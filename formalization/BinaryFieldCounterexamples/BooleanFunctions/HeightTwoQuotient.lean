/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.BooleanFunctions.HeightTwo
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.FieldTheory.Finiteness

/-!
# Height two on spaces with unused coordinates

The first sentence in the height-two proof of Lemma 6.4 passes to a quotient
by translation periods. Degree preservation is proved in `DegreeQuotient`.
Here uniform quotient fibers also preserve balance. Consequently every balanced
function of essential dimension three has degree two, even when its ambient
space is larger than three-dimensional.
-/

@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

/-- Every point in the support of the induced function contributes exactly one
coset of `P` to the original support. -/
theorem periodQuotient_support_card_mul (f : U → ZMod 2) (P : Submodule (ZMod 2) U)
    (hP : P ≤ Trees.periodSubmodule f) :
    Nat.card {x : U // f x = 1} =
      Nat.card P * Nat.card {q : U ⧸ P // periodQuotientFunction f P q = 1} := by
  let r : U ⧸ P → U := Function.surjInv P.mkQ_surjective
  have hr (q : U ⧸ P) : P.mkQ (r q) = q := Function.surjInv_eq P.mkQ_surjective q
  have hdiff (x : U) : x - r (P.mkQ x) ∈ P :=
    (Submodule.Quotient.eq P).mp (hr (P.mkQ x)).symm
  have hk (p : P) : P.mkQ p = 0 := (Submodule.Quotient.mk_eq_zero P).mpr p.property
  let e : {x : U // f x = 1} ≃
      ({q : U ⧸ P // periodQuotientFunction f P q = 1} × P) :=
    { toFun := fun x =>
        (⟨P.mkQ x, by rw [periodQuotientFunction_mkQ f P hP]; exact x.property⟩,
          ⟨x - r (P.mkQ x), hdiff x⟩)
      invFun := fun y => ⟨r y.1 + y.2, by
        have hper : Trees.IsPeriod f (y.2 : U) := hP y.2.property
        rw [hper]
        exact y.1.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change r (P.mkQ x) + ((x : U) - r (P.mkQ x)) = x
        abel
      right_inv := by
        rintro ⟨q, p⟩
        apply Prod.ext
        · apply Subtype.ext
          change P.mkQ (r q + p) = q
          rw [map_add, hr, hk, add_zero]
        · apply Subtype.ext
          change r q + (p : U) - r (P.mkQ (r q + p)) = p
          rw [map_add, hr, hk, add_zero]
          abel }
  rw [Nat.card_congr e, Nat.card_prod, mul_comm]

/-- After quotienting by all translation periods, the induced Boolean
function has no nonzero period. -/
theorem periodQuotientFunction_period_free (f : U → ZMod 2) :
    ∀ q, Trees.IsPeriod (periodQuotientFunction f (Trees.periodSubmodule f)) q → q = 0 := by
  let P := Trees.periodSubmodule f
  intro q hq
  obtain ⟨u, rfl⟩ := P.mkQ_surjective q
  have hp : Trees.IsPeriod f u := by
    intro x
    rw [← periodQuotientFunction_mkQ f P le_rfl (x + u), map_add, hq,
      periodQuotientFunction_mkQ f P le_rfl x]
  exact (Submodule.Quotient.mk_eq_zero P).mpr hp

/-- Quotienting by period directions preserves balance when the quotient has
positive dimension. Both sides express balance by the cardinality of the support. -/
theorem periodQuotient_balanced_iff [FiniteDimensional (ZMod 2) U]
    (f : U → ZMod 2) (P : Submodule (ZMod 2) U) (hP : P ≤ Trees.periodSubmodule f)
    (hn : 0 < Module.finrank (ZMod 2) (U ⧸ P)) :
    Nat.card {x : U // f x = 1} = Nat.card U / 2 ↔
      Nat.card {q : U ⧸ P // periodQuotientFunction f P q = 1} = Nat.card (U ⧸ P) / 2 := by
  have hp : 0 < Nat.card P := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    positivity
  have heven : 2 ∣ Nat.card (U ⧸ P) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 hn.ne'
  rw [periodQuotient_support_card_mul f P hP, P.card_eq_card_quotient_mul_card,
    Nat.mul_div_assoc _ heven]
  constructor
  · exact Nat.eq_of_mul_eq_mul_left hp
  · intro h
    rw [h]

/-- A balanced Boolean function of essential dimension three has degree two
in every ambient finite-dimensional binary vector space. This justifies the
height-two quotient reduction in the proof of Lemma 6.4. -/
theorem vectorDegree_eq_two_of_balanced_essential_dimension_three
    [FiniteDimensional (ZMod 2) U] (f : U → ZMod 2)
    (hbal : Nat.card {x : U // f x = 1} = Nat.card U / 2)
    (hdim : Module.finrank (ZMod 2) (U ⧸ Trees.periodSubmodule f) = 3) :
    vectorDegree f = 2 := by
  let P := Trees.periodSubmodule f
  let g := periodQuotientFunction f P
  have hn : 0 < Module.finrank (ZMod 2) (U ⧸ P) := by
    rw [hdim]
    decide
  have hgcard := (periodQuotient_balanced_iff f P le_rfl hn).mp hbal
  have hqcard : Nat.card (U ⧸ P) = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    decide
  have hgfour : Nat.card {q : U ⧸ P // g q = 1} = 4 := by
    simpa [g, hqcard] using hgcard
  have hgper : ∀ q, Trees.IsPeriod g q → q = 0 := periodQuotientFunction_period_free f
  have hgdim : Module.finrank (ZMod 2) ((U ⧸ P) ⧸ Trees.periodSubmodule g) = 3 := by
    have he := finrank_periodQuotient_eq_iff_period_free g
    rw [hdim] at he
    exact he.mpr hgper
  have hgdegree := (balanced_vectorDegree_two_iff_essential_dimension_three g hdim hgfour).mpr hgdim
  rwa [vectorDegree_periodQuotientFunction f P le_rfl] at hgdegree

/-- The degree-two clause is redundant once balance and essential dimension
three are known, in any ambient finite-dimensional binary vector space. -/
theorem balanced_essential_dimension_three_iff_balanced_degree_two
    [FiniteDimensional (ZMod 2) U] (f : U → ZMod 2) :
    (Nat.card {x : U // f x = 1} = Nat.card U / 2 ∧
      Module.finrank (ZMod 2) (U ⧸ Trees.periodSubmodule f) = 3) ↔
    (Nat.card {x : U // f x = 1} = Nat.card U / 2 ∧ vectorDegree f = 2 ∧
      Module.finrank (ZMod 2) (U ⧸ Trees.periodSubmodule f) = 3) := by
  constructor
  · rintro ⟨hbal, hdim⟩
    exact ⟨hbal, vectorDegree_eq_two_of_balanced_essential_dimension_three f hbal hdim, hdim⟩
  · rintro ⟨hbal, _, hdim⟩
    exact ⟨hbal, hdim⟩

end BinaryFieldCounterexamples.BooleanFunctions
