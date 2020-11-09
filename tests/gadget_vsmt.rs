use std::collections::HashMap;
use rand::SeedableRng;
use rand::rngs::OsRng;
use rand_chacha::ChaChaRng;
use curve25519_dalek::scalar::Scalar;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs::r1cs::LinearCombination;

mod scalar_utils;
use scalar_utils::{ScalarBytes, TreeDepth, ScalarBits, get_bits};
mod utils;
use utils::AllocatedScalar;
mod mimc;
use mimc::{mimc, MIMC_ROUNDS};


type DBVal = (Scalar, Scalar);

pub struct VanillaSparseMerkleTree<'a> {
    pub depth: usize,
    empty_tree_hashes: Vec<Scalar>,
    db: HashMap<ScalarBytes, DBVal>,
    hash_constants: &'a [Scalar],
    pub root: Scalar
}

impl<'a> VanillaSparseMerkleTree<'a> {
    pub fn new(hash_constants: &'a [Scalar]) -> VanillaSparseMerkleTree<'a> {
        let depth = TreeDepth;
        let mut db = HashMap::new();
        let mut empty_tree_hashes: Vec<Scalar> = vec![];
        empty_tree_hashes.push(Scalar::zero());
        for i in 1..=depth {
            let prev = empty_tree_hashes[i-1];
            let new = mimc(&prev, &prev, hash_constants);
            let key = new.to_bytes();

            db.insert(key, (prev, prev));
            empty_tree_hashes.push(new);
        }

        let root = empty_tree_hashes[depth].clone();

        VanillaSparseMerkleTree {
            depth,
            empty_tree_hashes,
            db,
            hash_constants,
            root
        }
    }

    pub fn update(&mut self, idx: Scalar, val: Scalar) -> Scalar {
        let mut sidenodes: Vec<Scalar> = vec![];
        let mut cur_node = self.root.clone();
        //let mut cur_idx = get_bit_array(&idx);
        let mut cur_idx = ScalarBits::from_scalar(&idx);


        for i in 0..self.depth {
            let k = cur_node.to_bytes();
            let v = self.db.get(&k).unwrap();

            if cur_idx.is_msb_set() {
                sidenodes.push(v.0);
                cur_node = v.1;
            } else {
                sidenodes.push(v.1);
                cur_node = v.0;
            }

            cur_idx.shl();
        }

        //cur_idx = get_bit_array(&idx);
        let mut cur_idx = ScalarBits::from_scalar(&idx);
        let mut cur_val = val.clone();

        for i in 0..self.depth {
            let side_elem = sidenodes.pop().unwrap();
            let new_val = {
                if cur_idx.is_lsb_set() {
                    let nv =  mimc(&side_elem, &cur_val, self.hash_constants);
                    self.update_db_with_key_val(nv, (side_elem, cur_val));
                    nv
                } else {
                    let nv =  mimc(&cur_val, &side_elem, self.hash_constants);
                    self.update_db_with_key_val(nv, (cur_val, side_elem));
                    nv
                }
            };
            //println!("Root at level {} is {:?}", i, &cur_val);
            cur_idx.shr();
            cur_val = new_val;
        }

        self.root = cur_val;

        cur_val
    }

    pub fn get(&self, idx: Scalar, proof: &mut Option<Vec<Scalar>>) -> Scalar {
        let mut cur_idx = ScalarBits::from_scalar(&idx);
        let mut cur_node = self.root.clone();

        let need_proof = proof.is_some();
        let mut proof_vec = Vec::<Scalar>::new();

        for i in 0..self.depth {
            let k = cur_node.to_bytes();
            let v = self.db.get(&k).unwrap();
            if cur_idx.is_msb_set() {
                cur_node = v.1;
                if need_proof { proof_vec.push(v.0); }
            } else {
                cur_node = v.0;
                if need_proof { proof_vec.push(v.1); }
            }
            //cur_idx.shl(1);
            cur_idx.shl();
        }

        match proof {
            Some(v) => {
                v.extend_from_slice(&proof_vec);
            }
            None => ()
        }

        cur_node
    }

    pub fn verify_proof(&self, idx: Scalar, val: Scalar, proof: &[Scalar], root: Option<&Scalar>) -> bool {
        let mut cur_idx = ScalarBits::from_scalar(&idx);
        let mut cur_val = val.clone();

        for i in 0..self.depth {
            cur_val = {
                if cur_idx.is_lsb_set() {
                    mimc(&proof[self.depth-1-i], &cur_val, self.hash_constants)
                } else {
                    mimc(&cur_val, &proof[self.depth-1-i], self.hash_constants)
                }
            };

            cur_idx.shr();
        }

        // Check if root is equal to cur_val
        match root {
            Some(r) => {
                cur_val == *r
            }
            None => {
                cur_val == self.root
            }
        }
    }

    fn update_db_with_key_val(&mut self, key: Scalar, val: DBVal) {
        self.db.insert(key.to_bytes(), val);
    }
}


pub fn is_lsb_set(scalar: &Scalar) -> bool {
    (scalar.as_bytes()[0] & 1u8) == 1
}

// Check that bit 252 (0-indexing) is set or not
pub fn is_msb_set(scalar: &Scalar) -> bool {
    // 252 >> 3 = 31
    // 252 & 7 = 4
    ((scalar.as_bytes()[31] >> 4) & 1u8) == 1
}

pub fn mul2(scalar: &Scalar) -> Scalar {
    scalar * Scalar::from(2u8)
}

pub fn div2(scalar: &Scalar) -> Scalar {
    let inv_2 = Scalar::from_canonical_bytes(
        [247, 233, 122, 46, 141, 49, 9, 44, 107, 206, 123, 81, 239, 124, 111, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8]
    ).unwrap();
    scalar * inv_2
}


#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use curve25519_dalek::constants::BASEPOINT_ORDER;

    /*fn count_set_bits(bits: &[i8; 256]) -> u8 {
        let mut c = 0;
        for i in bits.iter() {
            if *i == 1i8 {
                c += 1;
            }
        }
        c
    }

    #[test]
    fn test_msb_lsb() {
        let two = Scalar::from(2u128);
        let _256 = Scalar::from(256u128);
        let _257 = Scalar::from(257u128);
        let _258 = Scalar::from(258u128);
        assert_eq!(is_lsb_set(&Scalar::zero()), false);
        assert_eq!(is_lsb_set(&Scalar::one()), true);
        assert_eq!(is_lsb_set(&two), false);
        assert_eq!(is_lsb_set(&_256), false);
        assert_eq!(is_lsb_set(&_257), true);
        assert_eq!(is_lsb_set(&_258), false);

        assert_eq!(is_msb_set(&Scalar::zero()), false);
        assert_eq!(is_msb_set(&Scalar::one()), false);
        assert_eq!(is_msb_set(&two), false);
        assert_eq!(is_msb_set(&_256), false);
        assert_eq!(is_msb_set(&_257), false);
        assert_eq!(is_msb_set(&_258), false);

        let l = BASEPOINT_ORDER;
        let l_minus_1 = l - Scalar::one();
        let t_252 = l - Scalar::from(27742317777372353535851937790883648493 as u128);
        let t_252_minus_1 = t_252 - Scalar::one();
        let t_252_plus_1 = t_252 + Scalar::one();
        assert_eq!(is_msb_set(&l), true);
        assert_eq!(is_msb_set(&l_minus_1), true);
        assert_eq!(is_msb_set(&t_252), true);
        assert_eq!(is_msb_set(&t_252_minus_1), false);
        assert_eq!(is_msb_set(&t_252_plus_1), true);
    }

    #[test]
    fn test_mul2_div2() {
        let x = Scalar::from(6 as u32);
        assert_eq!(Scalar::from(3 as u32), div2(&x));
        assert_eq!(Scalar::from(12 as u32), mul2(&x));
        let mut csprng: OsRng = OsRng::new().unwrap();

        for _ in 0..100 {
            let r: Scalar = Scalar::random(&mut csprng);
            let r2 = mul2(&r);
            assert_eq!(r, div2(&r2));
        }
    }*/

    #[test]
    fn test_vanilla_sparse_merkle_tree() {
        let mut test_rng: OsRng = OsRng::new().unwrap();;

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| Scalar::random(&mut test_rng)).collect::<Vec<_>>();
        let mut tree = VanillaSparseMerkleTree::new(&constants);

        for i in 1..10 {
            let s = Scalar::from(i as u32);
            tree.update(s, s);
        }

        for i in 1..10 {
            let s = Scalar::from(i as u32);
            assert_eq!(s, tree.get(s, &mut None));
            let mut proof_vec = Vec::<Scalar>::new();
            let mut proof = Some(proof_vec);
            assert_eq!(s, tree.get(s, &mut proof));
            proof_vec = proof.unwrap();
            assert!(tree.verify_proof(s, s, &proof_vec, None));
            assert!(tree.verify_proof(s, s, &proof_vec, Some(&tree.root)));
        }

        let kvs: Vec<(Scalar, Scalar)> = (0..100).map(|_| (Scalar::random(&mut test_rng), Scalar::random(&mut test_rng))).collect();
        for i in 0..kvs.len() {
            tree.update(kvs[i].0, kvs[i].1);
        }

        for i in 0..kvs.len() {
            assert_eq!(kvs[i].1, tree.get(kvs[i].0, &mut None));
        }
    }

    #[test]
    fn test_field_ops() {
        let one = Scalar::from(257u128);
        println!("one is {:?}", one);
        println!("one as bytes {:?}", one.as_bytes());
        //println!("one as bits {:?}", get_bits(&one).to_vec());

        let two = Scalar::from(2 as u32);
        let inv_2 = two.invert();
        println!("inv_2 is {:?}", inv_2);
        let x = Scalar::from(6 as u32);
        println!("x/2 {:?}", x*inv_2);


        let t = Scalar::from(256 as u32);
        let m = std::u128::MAX;
        let m1 = Scalar::from(m as u128) + Scalar::one();
        println!("m1 is {:?}", m1);
        let m2 = (m1 * t);
        println!("m2 is {:?}", m2);

        let mut r = Scalar::one();
        for i in 0..256 {
            r = r * two;
            /*println!("for i={} , r.is_canonical = {}", i, r.is_canonical());
            println!("For i={}, bit count={}", i, count_set_bits(&get_bits(&r)));
            println!("for i={} last byte={:?}", i, r.as_bytes()[31]);*/
        }

        let l = BASEPOINT_ORDER;
        println!("BASEPOINT_ORDER as bits {:?}", get_bits(&BASEPOINT_ORDER).to_vec());

        let y = Scalar::from(1u32);
        let mut b1 = vec![];
        let mut b2 = vec![];

        let mut z1 = y.clone();
        println!("z1 as bits {:?}", get_bits(&z1).to_vec());
        for i in 0..253 {
            if is_msb_set(&z1) {
                b1.push(1)
            } else {
                b1.push(0)
            }
            z1 = mul2(&z1);
        }

        let mut z2 = y.clone();
        println!("z2 as bits {:?}", get_bits(&z2).to_vec());
        for i in 0..253 {
            if is_lsb_set(&z2) {
                b2.insert(0, 1)
            } else {
                b2.insert(0, 0)
            }
            z2 = div2(&z2);
        }

        println!("b1 is {:?}", b1);
        println!("b2 is {:?}", b2);

        assert_eq!(b1, b2);
    }
}