#![allow(non_snake_case)]
#![doc(include = "../../docs/range-proof-protocol.md")]

use core::iter;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};
use merlin::Transcript;

use crate::errors::ProofError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::transcript::TranscriptProtocol;
use crate::util;

use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};

// Modules for MPC protocol

use super::dealer::*;
use super::party::*;

#[derive(Clone, Debug)]
/// The zether proof generates a proof of a correct anonymous transaction making use
/// of Bulletproofs.
pub struct BatchZetherProof {
    /// Number of receipients
    pub nmbr: usize,
    /// Commitment to the bits of the value
    pub A: CompressedRistretto,
    /// Commitment to the blinding factors
    pub S: CompressedRistretto,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub T_1: CompressedRistretto,
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    pub T_2: CompressedRistretto,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    pub t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    pub e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    pub ipp_proof: InnerProductProof,
    /// Sigma protocol messages
    /// Commitment to the blinding factors
    pub ann_y: CompressedRistretto,
    /// Commitment to the blinding factors
    pub ann_D: CompressedRistretto,
    /// Commitment to the blinding factors
    pub ann_b: CompressedRistretto,
    /// Commitment to the blinding factors
    pub ann_y_: Vec<CompressedRistretto>,
    /// Commitment to the blinding factors
    pub ann_t: CompressedRistretto,
    /// Response to the challenge
    pub res_sk: Scalar,
    /// Response to the challenge
    pub res_r: Scalar,
    /// Response to the challenge
    pub res_b: Scalar,
}

impl BatchZetherProof {
    /// Generate for multiple in the zether scenario. Because of using ElGamal
    /// encryptions in Zether, we need to twist a bit the proof an verification
    /// given that the ElGamal bases does not satisfy the requirements of a
    /// Pedersen commitment base.
    /// The main difference with the bulletproof, except of the sigma protocol,
    /// is how we apply the challenge to the committed polynomial.
    /// In this scenario, we omit the first coefficient of the polynomial.
    #[allow(dead_code)]
    pub fn prove_multiple(
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[Scalar],
        n: usize,

        pk_sender: &RistrettoPoint,
        pks_receivers: &Vec<RistrettoPoint>,
        enc_balance_after_transfer: &(RistrettoPoint, RistrettoPoint),
        enc_amount_sender: Vec<(RistrettoPoint, RistrettoPoint)>,
        sk_sender: &Scalar,
        comm_rnd: &Scalar,
    ) -> Result<(BatchZetherProof, Vec<CompressedRistretto>), ProofError> {
        if values.len() != blindings.len() {
            return Err(ProofError::WrongNumBlindingFactors);
        }

        // We shouldn't need this for batch proofs
        // if values.len() != 2 {
        //     return Err(ProofError::WrongNumZetherProof); // todo: check this
        // }

        let dealer = Dealer::new(bp_gens, pc_gens, transcript, n, values.len())?;

        let parties: Vec<_> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, &v_blinding)| Party::new(bp_gens, pc_gens, v, v_blinding, n))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let (parties, bit_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| {
                p.assign_position(j)
                    .expect("We already checked the parameters, so this should never happen")
            })
            .unzip();

        let value_commitments: Vec<_> = bit_commitments.iter().map(|c| c.V_j).collect();

        let (dealer, bit_challenge) = dealer.receive_bit_commitments(bit_commitments)?;

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge(&bit_challenge))
            .unzip();

        let (dealer, poly_challenge) = dealer.receive_poly_commitments(poly_commitments)?;

        let proof_shares: Vec<_> = parties
            .into_iter()
            .map(|p| p.apply_challenge_zether(&poly_challenge))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let scalar_values: Vec<Scalar> = values.into_iter().map(|x| Scalar::from(*x)).collect();
        let proof = dealer.receive_shares_and_generate_batch_zether(
            &scalar_values[0..scalar_values.len() - 1].to_vec(),
            &Scalar::from(*values.last().unwrap()),
            &proof_shares,
            pk_sender,
            pks_receivers,
            enc_balance_after_transfer,
            enc_amount_sender,
            sk_sender,
            comm_rnd,
        )?;

        Ok((proof, value_commitments))
    }

    /// Verifies an aggregated rangeproof for the given value commitments together
    /// with the sigma protocol. Note that in the 'mega check' we omit the
    /// verification involving the pedersen commitments of the values within a range
    /// to include the ElGamal encryptions instead. A simple translation would
    /// not suffice, given that ElGamal encryptions cannot be seen as Pedersen
    /// commitments.
    #[allow(dead_code)]
    pub fn verify_multiple(
        &self,
        bp_gens: &BulletproofGens,
        pc_gens: &PedersenGens,
        transcript: &mut Transcript,
        value_commitments: &Vec<CompressedRistretto>,
        n: usize,

        pk_sender: &RistrettoPoint,
        pk_receiver: &Vec<RistrettoPoint>,
        enc_balance_after_transfer: &(RistrettoPoint, RistrettoPoint),
        enc_amount_sender: Vec<(RistrettoPoint, RistrettoPoint)>,
        enc_amount_receiver: Vec<(RistrettoPoint, RistrettoPoint)>,
    ) -> Result<(Scalar, Scalar, Scalar), ProofError> {
        let m = value_commitments.len();

        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(ProofError::InvalidBitsize);
        }
        if bp_gens.gens_capacity < n {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < m {
            return Err(ProofError::InvalidGeneratorsLength);
        }

        transcript.rangeproof_domain_sep(n as u64, m as u64);

        for V in value_commitments.iter() {
            // Allow the commitments to be zero (0 value, 0 blinding)
            // See https://github.com/dalek-cryptography/bulletproofs/pull/248#discussion_r255167177
            transcript.append_point(b"V", V);
        }

        transcript.validate_and_append_point(b"A", &self.A)?;
        transcript.validate_and_append_point(b"S", &self.S)?;

        let y = transcript.challenge_scalar(b"y");
        let z = transcript.challenge_scalar(b"z");
        let zz = z * z;
        let mut powers_of_z: Vec<Scalar> = util::exp_iter(z).take(self.nmbr + 2).collect(); // check. Make sure we remove the powers until zz
        powers_of_z.remove(0);
        powers_of_z.remove(0);
        let last_power_z = powers_of_z.last().unwrap() * z;
        assert_eq!(powers_of_z[0], zz);
        let minus_z = -z;

        transcript.validate_and_append_point(b"T_1", &self.T_1)?;
        transcript.validate_and_append_point(b"T_2", &self.T_2)?;

        let x = transcript.challenge_scalar(b"x");

        transcript.append_scalar(b"t_x", &self.t_x);
        transcript.append_scalar(b"t_x_blinding", &self.t_x_blinding);
        transcript.append_scalar(b"e_blinding", &self.e_blinding);

        let w = transcript.challenge_scalar(b"w");

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(n * m, transcript)?;
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        // Construct concat_z_and_2, an iterator of the values of
        // z^0 * \vec(2)^n || z^1 * \vec(2)^n || ... || z^(m-1) * \vec(2)^n
        let powers_of_2: Vec<Scalar> = util::exp_iter(Scalar::from(2u64)).take(n).collect();
        let concat_z_and_2: Vec<Scalar> = util::exp_iter(z)
            .take(m)
            .flat_map(|exp_z| powers_of_2.iter().map(move |exp_2| exp_2 * exp_z))
            .collect();

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter(y.invert()))
            .zip(concat_z_and_2.iter())
            .map(|((s_i_inv, exp_y_inv), z_and_2)| z + exp_y_inv * (zz * z_and_2 - b * s_i_inv));

        let challenge_sigma = transcript.challenge_scalar(b"challenge_sigma");

        let decompressed_announcements = self.ann_y_.iter().map(|x| x.decompress());
        let substracted_keys = pk_receiver.iter().map(|x| Some(pk_sender - x));
        let substracted_ciphertexts = enc_amount_receiver
            .iter()
            .zip(enc_amount_sender.iter())
            .map(|(x, y)| Some(y.0 - x.0));
        let hidden_decrypted_ciphertexts = enc_amount_sender
            .iter()
            .map(|x| Some(challenge_sigma * x.0 - self.res_sk * x.1));
        assert_eq!(powers_of_z.len(), hidden_decrypted_ciphertexts.len());
        let enc_amount_senders_1 = enc_amount_sender
            .iter()
            .map(|x| Some(x.1 - Scalar::zero() * x.1)); // CLEARLY NOT THE WAY TO DO THIS. Cant deal with the chain error

        let basepoint_scalar = w * (self.t_x - a * b);

        let check_sender_pk = RistrettoPoint::optional_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(challenge_sigma))
                .chain(iter::once(-self.res_sk)),
            iter::once(self.ann_y.decompress())
                .chain(iter::once(Some(*pk_sender)))
                .chain(iter::once(Some(pc_gens.B))),
        )
        .ok_or_else(|| ProofError::VerificationError)?;

        let check_D = enc_amount_senders_1
            .map(|enc_amount_sender_1| {
                RistrettoPoint::optional_multiscalar_mul(
                    iter::once(Scalar::one())
                        .chain(iter::once(challenge_sigma))
                        .chain(iter::once(-self.res_r)),
                    iter::once(self.ann_D.decompress())
                        .chain(iter::once(enc_amount_sender_1))
                        .chain(iter::once(Some(pc_gens.B))),
                )
            })
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| ProofError::VerificationError)?;

        let check_C_Cbar = decompressed_announcements
            .zip(substracted_ciphertexts)
            .zip(substracted_keys)
            .map(|((ann_y_, substracted_ciphertext), substracted_key)| {
                RistrettoPoint::optional_multiscalar_mul(
                    iter::once(Scalar::one())
                        .chain(iter::once(challenge_sigma))
                        .chain(iter::once(-self.res_r)),
                    iter::once(ann_y_)
                        .chain(iter::once(substracted_ciphertext))
                        .chain(iter::once(substracted_key)),
                )
            })
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| ProofError::VerificationError)?;

        let check_balance = RistrettoPoint::optional_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(powers_of_z.clone())
                .chain(iter::once(last_power_z))
                .chain(iter::once(-self.res_b)),
            iter::once(self.ann_b.decompress())
                .chain(hidden_decrypted_ciphertexts.clone())
                .chain(iter::once(Some(
                    challenge_sigma * enc_balance_after_transfer.0
                        - self.res_sk * enc_balance_after_transfer.1,
                )))
                .chain(iter::once(Some(pc_gens.B))),
        )
        .ok_or_else(|| ProofError::VerificationError)?;

        let check_t = RistrettoPoint::optional_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(-Scalar::one()))
                .chain(iter::once(self.res_b))
                .chain(iter::once(challenge_sigma))
                .chain(iter::once(challenge_sigma)),
            iter::once(self.ann_t.decompress())
                .chain(iter::once(self.ann_b.decompress()))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(iter::once(Some(
                    -(self.t_x - delta(n, m, &y, &z)) * pc_gens.B
                        - self.t_x_blinding * pc_gens.B_blinding,
                )))
                .chain(iter::once(Some(
                    x * self.T_1.decompress().unwrap() + (x * x) * self.T_2.decompress().unwrap(),
                ))),
        )
        .ok_or_else(|| ProofError::VerificationError)?;

        let check_ipp = RistrettoPoint::optional_multiscalar_mul(
            iter::once(Scalar::one())
                .chain(iter::once(x))
                .chain(x_sq.iter().cloned())
                .chain(x_inv_sq.iter().cloned())
                .chain(iter::once(-self.e_blinding))
                .chain(iter::once(basepoint_scalar))
                .chain(g)
                .chain(h),
            iter::once(self.A.decompress())
                .chain(iter::once(self.S.decompress()))
                .chain(self.ipp_proof.L_vec.iter().map(|L| L.decompress()))
                .chain(self.ipp_proof.R_vec.iter().map(|R| R.decompress()))
                .chain(iter::once(Some(pc_gens.B_blinding)))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(bp_gens.G(n, m).map(|&x| Some(x)))
                .chain(bp_gens.H(n, m).map(|&x| Some(x))),
        )
        .ok_or_else(|| ProofError::VerificationError)?;

        if check_sender_pk.is_identity()
            && check_D.iter().all(|x| x.is_identity())
            && check_C_Cbar.iter().all(|x| x.is_identity())
            && check_balance.is_identity()
            && check_t.is_identity()
            && check_ipp.is_identity()
        {
            Ok((x, y, z))
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// Serializes the proof into a byte array of \\(2 \lg n + 9\\)
    /// 32-byte elements, where \\(n\\) is the number of secret bits.
    ///
    /// # Layout
    ///
    /// The layout of the range proof encoding is:
    ///
    /// * 9 compressed Ristretto points \\(A,S,T_1,T_2\\),
    /// * 6 scalars \\(t_x, \tilde{t}_x, \tilde{e}\\),
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0,R_0\dots,L_{n-1},R_{n-1}\\),
    /// * two scalars \\(a, b\\).

    pub fn to_bytes(&self) -> Vec<u8> {
        // 15 elements: points A, S, T1, T2, ann_y, ann_D, ann_b, ann_y_ (multiple), ann_t, scalars tx, tx_bl, e_bl, res_sk, res_r, res_b.
        let mut buf =
            Vec::with_capacity((14 + self.nmbr) * 32 + self.ipp_proof.serialized_size() + 8);
        buf.extend_from_slice(&self.nmbr.to_ne_bytes());
        buf.extend_from_slice(self.A.as_bytes());
        buf.extend_from_slice(self.S.as_bytes());
        buf.extend_from_slice(self.T_1.as_bytes());
        buf.extend_from_slice(self.T_2.as_bytes());
        buf.extend_from_slice(self.t_x.as_bytes());
        buf.extend_from_slice(self.t_x_blinding.as_bytes());
        buf.extend_from_slice(self.e_blinding.as_bytes());
        buf.extend_from_slice(self.ann_y.as_bytes());
        buf.extend_from_slice(self.ann_D.as_bytes());
        buf.extend_from_slice(self.ann_b.as_bytes());
        for i in 0..self.nmbr {
            buf.extend_from_slice(self.ann_y_[i].as_bytes());
        }
        buf.extend_from_slice(self.ann_t.as_bytes());
        buf.extend_from_slice(self.res_sk.as_bytes());
        buf.extend_from_slice(self.res_r.as_bytes());
        buf.extend_from_slice(self.res_b.as_bytes());
        // XXX this costs an extra alloc
        buf.extend_from_slice(self.ipp_proof.to_bytes().as_slice());
        buf
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `RangeProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<BatchZetherProof, ProofError> {
        use std::convert::TryInto;
        if (slice.len() - 8) % 32 != 0 {
            return Err(ProofError::FormatError);
        }
        if slice.len() < 15 * 32 {
            return Err(ProofError::FormatError);
        }

        use util::read32;
        let nmbr_bytes: [u8; 8] = slice[0..8].try_into().expect("slice with incorrect length"); // should never get an error
        let nmbr = usize::from_ne_bytes(nmbr_bytes);
        let A = CompressedRistretto(read32(&slice[8 + 0 * 32..]));
        let S = CompressedRistretto(read32(&slice[8 + 1 * 32..]));
        let T_1 = CompressedRistretto(read32(&slice[8 + 2 * 32..]));
        let T_2 = CompressedRistretto(read32(&slice[8 + 3 * 32..]));

        let t_x = Scalar::from_canonical_bytes(read32(&slice[8 + 4 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let t_x_blinding = Scalar::from_canonical_bytes(read32(&slice[8 + 5 * 32..]))
            .ok_or(ProofError::FormatError)?;
        let e_blinding = Scalar::from_canonical_bytes(read32(&slice[8 + 6 * 32..]))
            .ok_or(ProofError::FormatError)?;

        let ann_y = CompressedRistretto(read32(&slice[8 + 7 * 32..]));
        let ann_D = CompressedRistretto(read32(&slice[8 + 8 * 32..]));
        let ann_b = CompressedRistretto(read32(&slice[8 + 9 * 32..]));
        let mut ann_y_: Vec<CompressedRistretto> = vec![];
        for i in 0..nmbr {
            ann_y_.push(CompressedRistretto(read32(&slice[8 + (10 + i) * 32..])));
        }
        let ann_t = CompressedRistretto(read32(&slice[8 + (10 + nmbr) * 32..]));

        let res_sk = Scalar::from_canonical_bytes(read32(&slice[8 + (11 + nmbr) * 32..]))
            .ok_or(ProofError::FormatError)?;
        let res_r = Scalar::from_canonical_bytes(read32(&slice[8 + (12 + nmbr) * 32..]))
            .ok_or(ProofError::FormatError)?;
        let res_b = Scalar::from_canonical_bytes(read32(&slice[8 + (13 + nmbr) * 32..]))
            .ok_or(ProofError::FormatError)?;

        let ipp_proof = InnerProductProof::from_bytes(&slice[8 + (14 + nmbr) * 32..])?;

        Ok(BatchZetherProof {
            nmbr,
            A,
            S,
            T_1,
            T_2,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
            ann_y,
            ann_D,
            ann_b,
            ann_y_,
            ann_t,
            res_sk,
            res_r,
            res_b,
        })
    }
}

impl Serialize for BatchZetherProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

impl<'de> Deserialize<'de> for BatchZetherProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct BatchZetherProofVisitor;

        impl<'de> Visitor<'de> for BatchZetherProofVisitor {
            type Value = BatchZetherProof;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a valid BatchZetherProof")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<BatchZetherProof, E>
            where
                E: serde::de::Error,
            {
                BatchZetherProof::from_bytes(v).map_err(serde::de::Error::custom)
            }
        }

        deserializer.deserialize_bytes(BatchZetherProofVisitor)
    }
}

/// Compute
/// \\[
/// \delta(y,z) = (z - z^{2}) \langle \mathbf{1}, {\mathbf{y}}^{n \cdot m} \rangle - \sum_{j=0}^{m-1} z^{j+3} \cdot \langle \mathbf{1}, {\mathbf{2}}^{n \cdot m} \rangle
/// \\]
fn delta(n: usize, m: usize, y: &Scalar, z: &Scalar) -> Scalar {
    let sum_y = util::sum_of_powers(y, n * m);
    let sum_2 = util::sum_of_powers(&Scalar::from(2u64), n);
    let sum_z = util::sum_of_powers(z, m);

    (z - z * z) * sum_y - z * z * z * sum_2 * sum_z
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::generators::PedersenGens;
    use rand::thread_rng;

    fn add_ciphertext(
        ctxt_1: &(RistrettoPoint, RistrettoPoint),
        ctxt_2: &(RistrettoPoint, RistrettoPoint),
    ) -> (RistrettoPoint, RistrettoPoint) {
        (ctxt_1.0 + ctxt_2.0, ctxt_1.1 + ctxt_2.1)
    }

    #[test]
    fn serialize_and_deserialize_batch_zether_proof() {
        let b_sent_1 = 1234u64;
        let b_sent_2 = 1222u64;
        let b_sent_3 = 111u64;
        let b_remaining = 123u64;
        let b_initial = &b_sent_1 + &b_sent_2 + &b_sent_3 + &b_remaining;

        // Bulletproof part
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 4);

        let blinding_1 = Scalar::random(&mut thread_rng());
        let blinding_2 = Scalar::random(&mut thread_rng());
        let blinding_3 = Scalar::random(&mut thread_rng());
        let blinding_4 = Scalar::random(&mut thread_rng());

        let mut prover_transcript = Transcript::new(b"doctest example");

        let sk = Scalar::random(&mut thread_rng());
        let g = pc_gens.B;

        let y = &sk * &g; // public key sender
        let y_1 = RistrettoPoint::random(&mut thread_rng()); // public key receiver 1
        let y_2 = RistrettoPoint::random(&mut thread_rng()); // public key receiver 2
        let y_3 = RistrettoPoint::random(&mut thread_rng()); // public key receiver 3

        let random_encryption = Scalar::random(&mut thread_rng());
        let (Cl, Cr) = (
            &Scalar::from(b_initial) * &g + &random_encryption * &y,
            &random_encryption * &g,
        );

        let blinding_factor = Scalar::random(&mut thread_rng());
        let enc_amount_sender_1 = (
            &Scalar::from(b_sent_1) * &g + &blinding_factor * &y,
            &blinding_factor * &g,
        );

        let enc_amount_sender_2 = (
            &Scalar::from(b_sent_2) * &g + &blinding_factor * &y,
            &blinding_factor * &g,
        );

        let enc_amount_sender_3 = (
            &Scalar::from(b_sent_3) * &g + &blinding_factor * &y,
            &blinding_factor * &g,
        );

        let enc_amounts_sender = vec![
            enc_amount_sender_1,
            enc_amount_sender_2,
            enc_amount_sender_3,
        ];

        let mut added_encrypted_amount = (Scalar::zero() * g, Scalar::zero() * g);
        for i in enc_amounts_sender.clone() {
            added_encrypted_amount = add_ciphertext(&added_encrypted_amount, &i);
        }

        let Cln = Cl - added_encrypted_amount.0; // encrypted balance after sending
        let Crn = Cr - added_encrypted_amount.1; // "

        let (zether_proof, _committed_value) = BatchZetherProof::prove_multiple(
            &bp_gens,
            &pc_gens,
            &mut prover_transcript,
            &[b_sent_1, b_sent_2, b_sent_3, b_remaining],
            &[blinding_1, blinding_2, blinding_3, blinding_4],
            64,
            &y,
            &vec![y_1, y_2, y_3],
            &(Cln, Crn),
            enc_amounts_sender.clone(),
            &sk,
            &blinding_factor,
        )
        .expect("A real program could handle errors");

        // Just making sure that the byte conversion works
        let bytes = zether_proof.to_bytes();
        let from_bytes = BatchZetherProof::from_bytes(&bytes).unwrap();
        assert_eq!(bytes, from_bytes.to_bytes());
    }

    #[test]
    fn create_and_verify_batch_zether_proof() {
        let b_sent_1 = 1234u64;
        let b_sent_2 = 1222u64;
        let b_sent_3 = 111u64;
        let b_remaining = 123u64;
        let b_initial = &b_sent_1 + &b_sent_2 + &b_sent_3 + &b_remaining;

        // Bulletproof part
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 4);

        let blinding_1 = Scalar::random(&mut thread_rng());
        let blinding_2 = Scalar::random(&mut thread_rng());
        let blinding_3 = Scalar::random(&mut thread_rng());
        let blinding_4 = Scalar::random(&mut thread_rng());

        let mut prover_transcript = Transcript::new(b"doctest example");

        let commitment_1 = pc_gens.commit(Scalar::from(b_sent_1), blinding_1);
        let commitment_2 = pc_gens.commit(Scalar::from(b_sent_2), blinding_2);
        let commitment_3 = pc_gens.commit(Scalar::from(b_sent_3), blinding_3);
        let commitment_4 = pc_gens.commit(Scalar::from(b_remaining), blinding_4);

        let sk = Scalar::random(&mut thread_rng());
        let g = pc_gens.B;

        let y = &sk * &g; // public key sender
        let y_1 = RistrettoPoint::random(&mut thread_rng()); // public key receiver 1
        let y_2 = RistrettoPoint::random(&mut thread_rng()); // public key receiver 2
        let y_3 = RistrettoPoint::random(&mut thread_rng()); // public key receiver 3

        let random_encryption = Scalar::random(&mut thread_rng());
        let (Cl, Cr) = (
            &Scalar::from(b_initial) * &g + &random_encryption * &y,
            &random_encryption * &g,
        );

        let blinding_factor = Scalar::random(&mut thread_rng());
        let enc_amount_sender_1 = (
            &Scalar::from(b_sent_1) * &g + &blinding_factor * &y,
            &blinding_factor * &g,
        );
        let enc_amount_receiver_1 = (
            &Scalar::from(b_sent_1) * &g + &blinding_factor * &y_1,
            &blinding_factor * &g,
        );

        let enc_amount_sender_2 = (
            &Scalar::from(b_sent_2) * &g + &blinding_factor * &y,
            &blinding_factor * &g,
        );
        let enc_amount_receiver_2 = (
            &Scalar::from(b_sent_2) * &g + &blinding_factor * &y_2,
            &blinding_factor * &g,
        );

        let enc_amount_sender_3 = (
            &Scalar::from(b_sent_3) * &g + &blinding_factor * &y,
            &blinding_factor * &g,
        );
        let enc_amount_receiver_3 = (
            &Scalar::from(b_sent_3) * &g + &blinding_factor * &y_3,
            &blinding_factor * &g,
        );

        let enc_amounts_sender = vec![
            enc_amount_sender_1,
            enc_amount_sender_2,
            enc_amount_sender_3,
        ];
        let enc_amounts_receiver = vec![
            enc_amount_receiver_1,
            enc_amount_receiver_2,
            enc_amount_receiver_3,
        ];

        let mut added_encrypted_amount = (Scalar::zero() * g, Scalar::zero() * g);
        for i in enc_amounts_sender.clone() {
            added_encrypted_amount = add_ciphertext(&added_encrypted_amount, &i);
        }

        let Cln = Cl - added_encrypted_amount.0; // encrypted balance after sending
        let Crn = Cr - added_encrypted_amount.1; // "

        let (zether_proof, _committed_value) = BatchZetherProof::prove_multiple(
            &bp_gens,
            &pc_gens,
            &mut prover_transcript,
            &[b_sent_1, b_sent_2, b_sent_3, b_remaining],
            &[blinding_1, blinding_2, blinding_3, blinding_4],
            64,
            &y,
            &vec![y_1, y_2, y_3],
            &(Cln, Crn),
            enc_amounts_sender.clone(),
            &sk,
            &blinding_factor,
        )
        .expect("A real program could handle errors");

        let mut verifier_transcript = Transcript::new(b"doctest example");

        assert!(zether_proof
            .verify_multiple(
                &bp_gens,
                &pc_gens,
                &mut verifier_transcript,
                &vec![
                    commitment_1.compress(),
                    commitment_2.compress(),
                    commitment_3.compress(),
                    commitment_4.compress()
                ],
                64,
                &y,
                &vec![y_1, y_2, y_3],
                &(Cln, Crn),
                enc_amounts_sender,
                enc_amounts_receiver,
            )
            .is_ok());
    }
}