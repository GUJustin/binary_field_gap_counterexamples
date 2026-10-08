/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import ArkLib.Data.CodingTheory.Basic.Distance
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Rat.Floor

/-!
# Concrete semantics for the paper's main theorem statements

Definitions 3.1–3.5 in [Section 3, pp. 18–19](../../binary-field-counterexamples.pdf#page=18)
fix the paper's code, agreement, challenge, list, and gap quantities. These quantities count coordinates, use polynomial degree strictly
below the message bound, and maximize over actual polynomials. The predicates below
express upper bounds and attained lower bounds directly, avoiding a separate choice
of a maximizing polynomial. Equality means both bounds, including attainment.

Agreement counts use ArkLib's `Code.agree`. Common agreement compares pairs at the
same coordinates. Exceptional sets count distinct challenges for one fixed pair of
words; the nonzero set explicitly removes zero. Decoding lists contain distinct
polynomials, not representations or construction parameters.

Every definition here has a complete body. None assumes a counterexample, carries
an admitted mathematical assertion, or permits callers to substitute the meaning
of agreement. These definitions are included in the statement-drift baseline.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- Actual polynomial agreement on the finite coordinate subtype of `D`. -/
noncomputable def agreementCount {F : Type*} [Field F]
    (D : Finset F) (w : D → F) (p : F[X]) : ℕ := by
  classical
  exact Code.agree w (fun x ↦ p.eval x.val)

/-- At least `T` agreements with some strict-degree message polynomial. -/
def agreementGE {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (T : ℕ) : Prop :=
  ∃ p : F[X], p.degree < K ∧ T ≤ agreementCount D w p

/-- Every strict-degree message polynomial has at most `T` agreements. -/
def agreementLE {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (T : ℕ) : Prop :=
  ∀ p : F[X], p.degree < K → agreementCount D w p ≤ T

/-- The maximum agreement is exactly `T`, with an attaining polynomial. -/
def agreementEQ {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (T : ℕ) : Prop :=
  agreementGE D K w T ∧ agreementLE D K w T

/-- Both explaining polynomials must agree at the same coordinates. -/
noncomputable def commonAgreementCount {F : Type*} [Field F]
    (D : Finset F) (f g : D → F) (p r : F[X]) : ℕ := by
  classical
  exact Code.agree (fun x ↦ (f x, g x)) (fun x ↦ (p.eval x.val, r.eval x.val))

/-- A pair of strict-degree explaining polynomials attains at least `T` common coordinates. -/
def commonAgreementGE {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) : Prop :=
  ∃ p r : F[X], p.degree < K ∧ r.degree < K ∧ T ≤ commonAgreementCount D f g p r

/-- No pair of strict-degree explaining polynomials exceeds `T` common coordinates. -/
def commonAgreementLE {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) : Prop :=
  ∀ p r : F[X], p.degree < K → r.degree < K → commonAgreementCount D f g p r ≤ T

/-- Exact maximum common agreement, including attainment. -/
def commonAgreementEQ {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) : Prop :=
  commonAgreementGE D K f g T ∧ commonAgreementLE D K f g T

/-- All exceptional challenges for one pair fixed before the challenge is chosen. -/
noncomputable def badChallenges {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) : Finset F := by
  classical
  exact Finset.univ.filter fun z ↦ agreementGE D K (fun x ↦ f x + z * g x) T

/-- The same event restricted to nonzero challenges. -/
noncomputable def nonzeroBadChallenges {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) : Finset F := by
  classical
  exact (badChallenges D K f g T).erase 0

/-- A decoding list of at least `L` distinct strict-degree polynomials for one word. -/
def ordinaryList {F : Type*} [Field F]
    (D : Finset F) (K T L : ℕ) : Prop :=
  ∃ w : D → F, ∃ ps : Finset F[X], L ≤ ps.card ∧
    ∀ p ∈ ps, p.degree < K ∧ T ≤ agreementCount D w p

/-- The coordinates of a finite additive subgroup; in characteristic two these
are exactly binary linear domains. -/
noncomputable def additiveDomain {F : Type*} [Field F] [Fintype F]
    (D : AddSubgroup F) : Finset F := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ D

/-- Transport a domain through a chosen field embedding. -/
noncomputable def mappedDomain {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (D : Finset B) : Finset F := by
  classical
  exact D.image φ

/-- Translate an evaluation domain, keeping every coordinate. -/
noncomputable def affineDomain {F : Type*} [Field F]
    (D : Finset F) (shift : F) : Finset F := by
  classical
  exact D.image (fun x ↦ x + shift)

end BinaryFieldCounterexamples
