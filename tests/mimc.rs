use rand::SeedableRng;
use rand_chacha::ChaChaRng;
use curve25519_dalek::scalar::Scalar;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs::r1cs::LinearCombination;


mod utils;
use utils::AllocatedQuantity;

//pub const MIMC_ROUNDS: usize = 322;
pub const MIMC_ROUNDS: usize = 10;


pub fn mimc(
    xl: &Scalar,
    xr: &Scalar,
    constants: &[Scalar]
) -> Scalar
{
    assert_eq!(constants.len(), MIMC_ROUNDS);

    let mut xl = xl.clone();
    let mut xr = xr.clone();

    for i in 0..MIMC_ROUNDS {
        let mut tmp1 = xl + constants[i];
        let mut tmp2 = (tmp1 * tmp1) * tmp1;
        tmp2 += xr;
        xr = xl;
        xl = tmp2;
    }

    xl
}

/*pub fn hash_2<CS: ConstraintSystem>(cs: &mut CS,
              mut left: AllocatedScalar,
              mut right: AllocatedScalar,
              mimc_rounds: usize,
              mimc_constants: &[Scalar]) -> Result<(Option<Scalar>, Variable), R1CSError> {
    for j in 0..mimc_rounds {
        // xL, xR := xR + (xL + Ci)^3, xL
        //let cs = &mut cs.namespace(|| format!("mimc round {}", j));
        let left_lc: LinearCombination = left.variable.into();
        let right_lc: LinearCombination = right.variable.into();
        let const_lc: LinearCombination = vec![(Variable::One(), mimc_constants[j])].iter().collect();

        let left_plus_const: LinearCombination = left_lc + const_lc;

        let (l, _, l_sqr) = cs.multiply(left_plus_const.clone(), left_plus_const);
        let (_, _, l_cube) = cs.multiply(l_sqr.into(), l.into());

        let new_l: LinearCombination = LinearCombination::from(l_cube) + right_lc;

        // tmp = (xL + Ci)^2
        /*let mut tmp_value = left_val.map(|mut e| {
            e.add_assign(&mimc_constants[j]);
            e.square();
            e
        });
        let mut tmp = cs.alloc(|| "tmp", || {
            tmp_value.ok_or(R1CSError::MissingAssignment)
        })?;

        cs.enforce(
            || "tmp = (xL + Ci)^2",
            |lc| lc + left + (mimc_constants[j], CS::one()),
            |lc| lc + left + (mimc_constants[j], CS::one()),
            |lc| lc + tmp
        );

        // new_xL = xR + (xL + Ci)^3
        // new_xL = xR + tmp * (xL + Ci)
        // new_xL - xR = tmp * (xL + Ci)
        let mut new_xl_value = left_val.map(|mut e| {
            e.add_assign(&mimc_constants[j]);
            e.mul_assign(&tmp_value.unwrap());
            e.add_assign(&right_val.unwrap());
            e
        });

        let mut new_xl = if j == (MIMC_ROUNDS-1) {
            // This is the last round, xL is our image and so
            // we allocate a public input.
            cs.alloc_input(|| "root", || {
                new_xl_value.ok_or(R1CSError::MissingAssignment)
            })?
        } else {
            cs.alloc(|| "new_xl", || {
                new_xl_value.ok_or(R1CSError::MissingAssignment)
            })?
        };

        cs.enforce(
            || "new_xL = xR + (xL + Ci)^3",
            |lc| lc + tmp,
            |lc| lc + left + (mimc_constants[j], CS::one()),
            |lc| lc + new_xl - right
        );

        // xR = xL
        right = left;
        right_val = left_val;

        // xL = new_xL
        left = new_xl;
        left_val = new_xl_value;*/
    }
    unimplemented!()
    //Ok((left_val, left))
}*/


#[cfg(test)]
mod tests {
    use super::*;
    // For benchmarking
    use std::time::{Duration, Instant};

    #[test]
    fn test_mimc() {
        let mut test_rng = ChaChaRng::from_seed([24u8; 32]);

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| Scalar::random(&mut test_rng)).collect::<Vec<_>>();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        const SAMPLES: u32 = 50;
        let mut total_proving = Duration::new(0, 0);
        let mut total_verifying = Duration::new(0, 0);

        for _ in 0..SAMPLES {
            // Generate a random preimage and compute the image
            let xl = Scalar::random(&mut test_rng);
            let xr = Scalar::random(&mut test_rng);
            let image = mimc(&xl, &xr, &constants);

            let (proof, commitments) = {
                let mut prover_transcript = Transcript::new(b"MiMC");
                let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

                let mut rng = rand::thread_rng();

                let (com_l, var_l) = prover.commit(xl, Scalar::random(&mut rng));
                let (com_r, var_r) = prover.commit(xr, Scalar::random(&mut rng));


                let proof = prover.prove(&bp_gens).unwrap();

                (proof, (com_l, com_r))
            };
        }
    }

}
