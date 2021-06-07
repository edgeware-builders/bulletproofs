#![cfg_attr(not(feature = "std"), no_std)]
#![feature(external_doc)]
//#![deny(missing_docs)]
#![doc(include = "../README.md")]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]
#![doc(html_root_url = "https://docs.rs/bulletproofs/2.0.0")]

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

mod util;

#[doc(include = "../docs/notes-intro.md")]
mod notes {
	#[doc(include = "../docs/notes-ipp.md")]
	mod inner_product_proof {}
	#[doc(include = "../docs/notes-rp.md")]
	mod range_proof {}
	#[doc(include = "../docs/notes-r1cs.md")]
	mod r1cs_proof {}
}

mod errors;
mod generators;
mod inner_product_proof;
mod range_proof;
mod transcript;

pub use crate::{
	errors::ProofError,
	generators::{BulletproofGens, BulletproofGensShare, PedersenGens},
	range_proof::RangeProof,
};

#[doc(include = "../docs/aggregation-api.md")]
pub mod range_proof_mpc {
	pub use crate::{
		errors::MPCError,
		range_proof::{dealer, messages, party},
	};
}

#[cfg(feature = "yoloproofs")]
pub mod r1cs;
