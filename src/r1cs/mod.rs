#![doc(include = "../../docs/r1cs-docs-example.md")]

#[doc(include = "../../docs/cs-proof.md")]
mod notes {}

mod constraint_system;
mod linear_combination;
mod proof;
mod prover;
mod verifier;

pub use self::{
	constraint_system::{ConstraintSystem, RandomizableConstraintSystem, RandomizedConstraintSystem},
	linear_combination::{LinearCombination, Variable},
	proof::R1CSProof,
	prover::Prover,
	verifier::Verifier,
};

pub use crate::errors::R1CSError;
