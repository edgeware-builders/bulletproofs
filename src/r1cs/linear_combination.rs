//! Definition of linear combinations.

use alloc::vec::Vec;
use core::{
	cmp::Ord,
	iter::FromIterator,
	ops::{Add, Mul, Neg, Sub},
};
use curve25519_dalek::scalar::Scalar;
use sp_std::collections::btree_map::BTreeMap;

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Variable {
	/// Represents an external input specified by a commitment.
	Committed(usize),
	/// Represents the left input of a multiplication gate.
	MultiplierLeft(usize),
	/// Represents the right input of a multiplication gate.
	MultiplierRight(usize),
	/// Represents the output of a multiplication gate.
	MultiplierOutput(usize),
	/// Represents the constant 1.
	One(),
}

impl From<Variable> for LinearCombination {
	fn from(v: Variable) -> LinearCombination {
		LinearCombination {
			terms: vec![(v, Scalar::one())],
		}
	}
}

impl<S: Into<Scalar>> From<S> for LinearCombination {
	fn from(s: S) -> LinearCombination {
		LinearCombination {
			terms: vec![(Variable::One(), s.into())],
		}
	}
}

// Arithmetic on variables produces linear combinations

impl Neg for Variable {
	type Output = LinearCombination;

	fn neg(self) -> Self::Output {
		-LinearCombination::from(self)
	}
}

impl<L: Into<LinearCombination>> Add<L> for Variable {
	type Output = LinearCombination;

	fn add(self, other: L) -> Self::Output {
		LinearCombination::from(self) + other.into()
	}
}

impl<L: Into<LinearCombination>> Sub<L> for Variable {
	type Output = LinearCombination;

	fn sub(self, other: L) -> Self::Output {
		LinearCombination::from(self) - other.into()
	}
}

impl<S: Into<Scalar>> Mul<S> for Variable {
	type Output = LinearCombination;

	fn mul(self, other: S) -> Self::Output {
		LinearCombination {
			terms: vec![(self, other.into())],
		}
	}
}

// Arithmetic on scalars with variables produces linear combinations

impl Add<Variable> for Scalar {
	type Output = LinearCombination;

	fn add(self, other: Variable) -> Self::Output {
		LinearCombination {
			terms: vec![(Variable::One(), self), (other, Scalar::one())],
		}
	}
}

impl Sub<Variable> for Scalar {
	type Output = LinearCombination;

	fn sub(self, other: Variable) -> Self::Output {
		LinearCombination {
			terms: vec![(Variable::One(), self), (other, -Scalar::one())],
		}
	}
}

impl Mul<Variable> for Scalar {
	type Output = LinearCombination;

	fn mul(self, other: Variable) -> Self::Output {
		LinearCombination {
			terms: vec![(other, self)],
		}
	}
}

/// Represents a linear combination of
/// [`Variables`](::r1cs::Variable).  Each term is represented by a
/// `(Variable, Scalar)` pair.
#[derive(Clone, Debug, PartialEq)]
pub struct LinearCombination {
	pub(super) terms: Vec<(Variable, Scalar)>,
}

impl LinearCombination {
	pub fn get_terms(self) -> Vec<(Variable, Scalar)> {
		self.terms
	}

	/// Simplify linear combination by taking Variables common across terms and
	/// adding their corresponding scalars. Useful when linear combinations
	/// become large. Takes ownership of linear combination as this function is
	/// useful when memory is limited and the obvious action after this function
	/// call will be to free the memory held by the old linear combination
	pub fn simplify(self) -> Self {
		// Build hashmap to hold unique variables with their values.
		let mut vars: BTreeMap<Variable, Scalar> = BTreeMap::new();

		let terms = self.get_terms();
		for (var, val) in terms {
			*vars.entry(var).or_insert_with(Scalar::zero) += val;
		}

		let mut new_lc_terms = vec![];
		for (var, val) in vars {
			new_lc_terms.push((var, val));
		}
		new_lc_terms.iter().collect()
	}
}

impl Default for LinearCombination {
	fn default() -> Self {
		LinearCombination { terms: Vec::new() }
	}
}

impl FromIterator<(Variable, Scalar)> for LinearCombination {
	fn from_iter<T>(iter: T) -> Self
	where
		T: IntoIterator<Item = (Variable, Scalar)>,
	{
		LinearCombination {
			terms: iter.into_iter().collect(),
		}
	}
}

impl<'a> FromIterator<&'a (Variable, Scalar)> for LinearCombination {
	fn from_iter<T>(iter: T) -> Self
	where
		T: IntoIterator<Item = &'a (Variable, Scalar)>,
	{
		LinearCombination {
			terms: iter.into_iter().cloned().collect(),
		}
	}
}

// Arithmetic on linear combinations

impl<L: Into<LinearCombination>> Add<L> for LinearCombination {
	type Output = Self;

	fn add(mut self, rhs: L) -> Self::Output {
		self.terms.extend(rhs.into().terms.iter().cloned());
		LinearCombination { terms: self.terms }
	}
}

impl<L: Into<LinearCombination>> Sub<L> for LinearCombination {
	type Output = Self;

	fn sub(mut self, rhs: L) -> Self::Output {
		self.terms
			.extend(rhs.into().terms.iter().map(|(var, coeff)| (*var, -coeff)));
		LinearCombination { terms: self.terms }
	}
}

impl Mul<LinearCombination> for Scalar {
	type Output = LinearCombination;

	fn mul(self, other: LinearCombination) -> Self::Output {
		let out_terms = other
			.terms
			.into_iter()
			.map(|(var, scalar)| (var, scalar * self))
			.collect();
		LinearCombination { terms: out_terms }
	}
}

impl Neg for LinearCombination {
	type Output = Self;

	fn neg(mut self) -> Self::Output {
		for (_, s) in self.terms.iter_mut() {
			*s = -*s
		}
		self
	}
}

impl<S: Into<Scalar>> Mul<S> for LinearCombination {
	type Output = Self;

	fn mul(mut self, other: S) -> Self::Output {
		let other = other.into();
		for (_, s) in self.terms.iter_mut() {
			*s *= other
		}
		self
	}
}
