use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs::r1cs::LinearCombination;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_factor_r1cs() {
        // Prove knowledge of `p` and `q` such that given an `r`, `p * q = r`

        // TODO: Prove that neither `p` or `q` is 1, this can be done range proof gadget or using the `not_equals_gadget`
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let (p, q, r) = (17u64, 19u64, 323u64);

        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"Factors");
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let mut rng = rand::thread_rng();

            let (com_p, var_p) = prover.commit(p.into(), Scalar::random(&mut rng));
            let (com_q, var_q) = prover.commit(q.into(), Scalar::random(&mut rng));

            let (_, _, o) =  prover.multiply(var_p.into(), var_q.into());
            let lc: LinearCombination = vec![(Variable::One(), r.into())].iter().collect();
            prover.constrain(o -  lc);

            let proof = prover.prove(&bp_gens).unwrap();

            (proof, (com_p, com_q))
        };

        let mut verifier_transcript = Transcript::new(b"Factors");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let var_p = verifier.commit(commitments.0);
        let var_q = verifier.commit(commitments.1);

        let (_, _, o) =  verifier.multiply(var_p.into(), var_q.into());
        let lc: LinearCombination = vec![(Variable::One(), r.into())].iter().collect();
        verifier.constrain(o -  lc);

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_factor_r1cs_2() {
        // Prove knowledge of `p`, `q` and `r` such that given an `s`, `p * q * r = s`

        // TODO: Prove that neither `p` or `q` or `r` is 1, this can be done range proof gadget.
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let (p, q, r, s) = (5u64, 7u64, 3u64, 105u64);

        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"Factors");
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let mut rng = rand::thread_rng();

            let (com_p, var_p) = prover.commit(p.into(), Scalar::random(&mut rng));
            let (com_q, var_q) = prover.commit(q.into(), Scalar::random(&mut rng));
            let (com_r, var_r) = prover.commit(r.into(), Scalar::random(&mut rng));

            let (_, _, o1) =  prover.multiply(var_p.into(), var_q.into());
            let (_, _, o2) =  prover.multiply(o1.into(), var_r.into());
            let lc: LinearCombination = vec![(Variable::One(), s.into())].iter().collect();
            prover.constrain(o2 -  lc);

            let proof = prover.prove(&bp_gens).unwrap();

            (proof, (com_p, com_q, com_r))
        };

        let mut verifier_transcript = Transcript::new(b"Factors");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let var_p = verifier.commit(commitments.0);
        let var_q = verifier.commit(commitments.1);
        let var_r = verifier.commit(commitments.2);

        let (_, _, o1) =  verifier.multiply(var_p.into(), var_q.into());
        let (_, _, o2) =  verifier.multiply(o1.into(), var_r.into());
        let lc: LinearCombination = vec![(Variable::One(), s.into())].iter().collect();
        verifier.constrain(o2 -  lc);

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}