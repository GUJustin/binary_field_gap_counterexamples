/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.BooleanFunctions.DegreeParity
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeCharacterization
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeQuotient

/-!
# The height-two Boolean classification

The height-two paragraph of the proof of Lemma 6.4 identifies the 56 balanced
quadratic functions on three coordinates with the four-point supports that are
not affine planes. The finite combinatorial lemmas here use kernel-checked
finite enumeration of the eight points and their 256 Boolean functions. Linear
coordinate equivalences transport the classification and exact count to every
three-dimensional binary space. Essential dimension is expressed directly as
the dimension of the quotient by `Trees.periodSubmodule`.
-/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace BinaryFieldCounterexamples.BooleanFunctions

/-- A literal affine combination on three Boolean coordinates. -/
def threeAffineCombination (a : Fin 3 → ZMod 2) (c : ZMod 2)
    (x : Fin 3 → ZMod 2) : ZMod 2 := c + ∑ i, a i * x i

/-- Being representable by a constant and a linear combination of coordinates. -/
abbrev IsThreeAffine (f : (Fin 3 → ZMod 2) → ZMod 2) : Prop :=
  ∃ a : Fin 3 → ZMod 2, ∃ c : ZMod 2, ∀ x, f x = threeAffineCombination a c x

/-- An affine plane is one fiber of a nonzero linear coordinate combination. -/
abbrev IsThreeAffinePlane (S : Finset (Fin 3 → ZMod 2)) : Prop :=
  ∃ a : Fin 3 → ZMod 2, a ≠ 0 ∧ ∃ c : ZMod 2,
    ∀ x, x ∈ S ↔ ∑ i, a i * x i = c

/-- Of the 70 four-point subsets of the binary three-space, exactly 56 are
not affine planes. -/
theorem nonplane_four_point_card :
    ((Finset.univ.powersetCard 4).filter (fun S => ¬ IsThreeAffinePlane S)).card = 56 := by
  decide

/-- For a four-point support, its indicator is affine exactly when the support
is an affine plane. -/
theorem three_affine_iff_support_plane :
    ∀ f : (Fin 3 → ZMod 2) → ZMod 2,
      (Finset.univ.filter (fun x => f x = 1)).card = 4 →
      (IsThreeAffine f ↔ IsThreeAffinePlane (Finset.univ.filter (fun x => f x = 1))) := by
  decide


/-- The ordinary three-bit index of a binary coordinate vector. -/
def threePointIndex (x : Fin 3 → ZMod 2) : Fin 8 :=
  ⟨(x 0).val + 2 * (x 1).val + 4 * (x 2).val, by
    have := (x 0).val_lt
    have := (x 1).val_lt
    have := (x 2).val_lt
    omega⟩

/-- The vector with the three bits of an index. -/
def threePoint (i : Fin 8) : Fin 3 → ZMod 2 :=
  ![(i.val % 2 : ℕ), (i.val / 2 % 2 : ℕ), (i.val / 4 % 2 : ℕ)]

/-- Indexing and then decoding recovers the point. -/
theorem threePoint_index : ∀ x, threePoint (threePointIndex x) = x := by decide

/-- A Boolean truth table indexed by the eight binary vectors. Explicit
indexing avoids transports across equal function-valued keys in finite checks. -/
def threeTruthTable (b : Fin 8 → ZMod 2) (x : Fin 3 → ZMod 2) : ZMod 2 :=
  b (threePointIndex x)

/-- Every Boolean function is represented by its eight-entry truth table. -/
theorem exists_threeTruthTable (f : (Fin 3 → ZMod 2) → ZMod 2) :
    ∃ b, f = threeTruthTable b := by
  refine ⟨fun i => f (threePoint i), ?_⟩
  funext x
  simp [threeTruthTable, threePoint_index]

/-- The period classification for eight-entry truth tables, checked by reduction
in Lean's kernel. -/
theorem balanced_truth_table_period_free_iff_not_affine :
    ∀ b : Fin 8 → ZMod 2,
      (Finset.univ.filter (fun x => threeTruthTable b x = 1)).card = 4 →
      ((∀ u, (∀ x, threeTruthTable b (x + u) = threeTruthTable b x) → u = 0) ↔
        ¬ IsThreeAffine (threeTruthTable b)) := by
  decide

/-- A balanced Boolean function on three coordinates has no nonzero period
exactly when it is not affine. This proves the period assertion for nonplanar
four-point supports in the height-two proof of Lemma 6.4. -/
theorem balanced_period_free_iff_not_affine
    (f : (Fin 3 → ZMod 2) → ZMod 2)
    (hf : (Finset.univ.filter (fun x => f x = 1)).card = 4) :
    (∀ u, Trees.IsPeriod f u → u = 0) ↔ ¬ IsThreeAffine f := by
  obtain ⟨b, rfl⟩ := exists_threeTruthTable f
  exact balanced_truth_table_period_free_iff_not_affine b hf

/-- Affine representability is exactly degree at most one. -/
theorem isThreeAffine_iff_degree_le_one (f : (Fin 3 → ZMod 2) → ZMod 2) :
    IsThreeAffine f ↔ degree f ≤ 1 := by
  rw [degree_le_one_iff_affine_combination]
  simp only [IsThreeAffine, threeAffineCombination, funext_iff]

/-- Balanced functions of degree two are exactly the indicators of nonplanar
four-point sets. -/
theorem degree_eq_two_iff_support_not_plane
    (f : (Fin 3 → ZMod 2) → ZMod 2)
    (hf : (Finset.univ.filter (fun x => f x = 1)).card = 4) :
    degree f = 2 ↔ ¬ IsThreeAffinePlane (Finset.univ.filter (fun x => f x = 1)) := by
  have hdeg := degree_lt_three_of_support_card_eq_four f hf
  rw [← three_affine_iff_support_plane f hf, isThreeAffine_iff_degree_le_one]
  omega

/-- Every balanced degree-two function on the binary three-space has no
nonzero translation period. -/
theorem period_eq_zero_of_balanced_degree_two
    (f : (Fin 3 → ZMod 2) → ZMod 2)
    (hf : (Finset.univ.filter (fun x => f x = 1)).card = 4)
    (hdeg : degree f = 2) (u : Fin 3 → ZMod 2) (hu : Trees.IsPeriod f u) : u = 0 := by
  apply (balanced_period_free_iff_not_affine f hf).mpr _ u hu
  rw [isThreeAffine_iff_degree_le_one, hdeg]
  omega

/-- The quotient by all periods has full dimension precisely when all periods
vanish. Thus quotient dimension gives the paper's essential dimension. -/
theorem finrank_periodQuotient_eq_iff_period_free {U : Type*}
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (f : U → ZMod 2) :
    Module.finrank (ZMod 2) (U ⧸ Trees.periodSubmodule f) = Module.finrank (ZMod 2) U ↔
      ∀ u, Trees.IsPeriod f u → u = 0 := by
  have hr := (Trees.periodSubmodule f).finrank_quotient_add_finrank
  constructor
  · intro h
    have hz : Module.finrank (ZMod 2) (Trees.periodSubmodule f) = 0 := by omega
    have hb := Submodule.finrank_eq_zero.mp hz
    intro u hu
    have hu' : u ∈ Trees.periodSubmodule f := hu
    simpa [hb] using hu'
  · intro h
    have hb : Trees.periodSubmodule f = ⊥ := by
      apply le_antisymm _ bot_le
      intro u hu
      exact h u hu
    have hz : Module.finrank (ZMod 2) (Trees.periodSubmodule f) = 0 := by
      rw [hb, finrank_bot]
    simpa [hz] using hr

/-- On the binary three-space, among balanced functions degree two and
essential dimension three are equivalent. -/
theorem balanced_degree_two_iff_essential_dimension_three
    (f : (Fin 3 → ZMod 2) → ZMod 2)
    (hf : (Finset.univ.filter (fun x => f x = 1)).card = 4) :
    degree f = 2 ↔
      Module.finrank (ZMod 2) ((Fin 3 → ZMod 2) ⧸ Trees.periodSubmodule f) = 3 := by
  have hdim : Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := by
    simp
  have he := finrank_periodQuotient_eq_iff_period_free f
  rw [hdim] at he
  rw [he, balanced_period_free_iff_not_affine f hf, isThreeAffine_iff_degree_le_one]
  have hdeg := degree_lt_three_of_support_card_eq_four f hf
  omega

/-- Exactly 56 of the 256 Boolean functions are balanced and non-affine. -/
theorem balanced_nonaffine_function_card :
    (Finset.univ.filter (fun f : (Fin 3 → ZMod 2) → ZMod 2 =>
      (Finset.univ.filter (fun x => f x = 1)).card = 4 ∧ ¬ IsThreeAffine f)).card = 56 := by
  decide

/-- Exactly 56 Boolean functions on three coordinates are balanced and have
degree two. This is the intrinsic count in part four of Lemma 6.4. -/
theorem balanced_degree_two_card :
    Nat.card {f : (Fin 3 → ZMod 2) → ZMod 2 //
      (Finset.univ.filter (fun x => f x = 1)).card = 4 ∧ degree f = 2} = 56 := by
  let e : {f : (Fin 3 → ZMod 2) → ZMod 2 //
        (Finset.univ.filter (fun x => f x = 1)).card = 4 ∧ degree f = 2} ≃
      {f : (Fin 3 → ZMod 2) → ZMod 2 //
        (Finset.univ.filter (fun x => f x = 1)).card = 4 ∧ ¬ IsThreeAffine f} :=
    Equiv.subtypeEquivRight fun f => by
      apply and_congr_right
      intro hf
      rw [isThreeAffine_iff_degree_le_one]
      have hdeg := degree_lt_three_of_support_card_eq_four f hf
      omega
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact balanced_nonaffine_function_card

noncomputable section

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

omit [FiniteDimensional (ZMod 2) U] in
/-- A choice of linear coordinates preserves the number of points at which a
Boolean function equals one. The source need not carry a chosen enumeration. -/
theorem support_card_eq_three_coordinates (f : U → ZMod 2)
    (e : U ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    Nat.card {x : U // f x = 1} =
      (Finset.univ.filter (fun x => f (e.symm x) = 1)).card := by
  let es : {x : U // f x = 1} ≃
      {x : Fin 3 → ZMod 2 // f (e.symm x) = 1} :=
    { toFun := fun x => ⟨e x, by simpa using x.property⟩
      invFun := fun x => ⟨e.symm x, x.property⟩
      left_inv := fun x => by ext; simp
      right_inv := fun x => by ext; simp }
  rw [Nat.card_congr es, Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [FiniteDimensional (ZMod 2) U] in
/-- Translation periods are transported by a linear coordinate equivalence. -/
theorem period_free_iff_three_coordinates (f : U → ZMod 2)
    (e : U ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    (∀ u, Trees.IsPeriod f u → u = 0) ↔
      ∀ u, Trees.IsPeriod (f ∘ e.symm) u → u = 0 := by
  constructor
  · intro h u hu
    have hp : Trees.IsPeriod f (e.symm u) := by
      intro x
      have hx := hu (e x)
      simpa using hx
    have hz := h (e.symm u) hp
    have := congrArg e hz
    simpa using this
  · intro h u hu
    have hp : Trees.IsPeriod (f ∘ e.symm) (e u) := by
      intro x
      simpa using hu (e.symm x)
    have hz := h (e u) hp
    exact e.injective (by simpa using hz)

/-- Every balanced degree-two function on an arbitrary three-dimensional
binary vector space has no nonzero translation period. -/
theorem period_eq_zero_of_balanced_vectorDegree_two (f : U → ZMod 2)
    (hdim : Module.finrank (ZMod 2) U = 3)
    (hf : Nat.card {x : U // f x = 1} = 4)
    (hdeg : vectorDegree f = 2) (u : U) (hu : Trees.IsPeriod f u) : u = 0 := by
  let e := (Module.finBasisOfFinrankEq (ZMod 2) U hdim).equivFun
  have hcoord : degree (f ∘ e.symm) = 2 := by
    rw [← vectorDegree_eq_coordinates f e]
    exact hdeg
  have hcard : (Finset.univ.filter (fun x => (f ∘ e.symm) x = 1)).card = 4 := by
    simpa only [Function.comp_apply] using (support_card_eq_three_coordinates f e).symm.trans hf
  have hper : ∀ v, Trees.IsPeriod (f ∘ e.symm) v → v = 0 :=
    period_eq_zero_of_balanced_degree_two (f ∘ e.symm) hcard hcoord
  exact (period_free_iff_three_coordinates f e).mpr hper u hu

/-- On any three-dimensional binary space, a balanced function has degree two
exactly when its essential dimension (the quotient dimension) is three. -/
theorem balanced_vectorDegree_two_iff_essential_dimension_three (f : U → ZMod 2)
    (hdim : Module.finrank (ZMod 2) U = 3)
    (hf : Nat.card {x : U // f x = 1} = 4) :
    vectorDegree f = 2 ↔
      Module.finrank (ZMod 2) (U ⧸ Trees.periodSubmodule f) = 3 := by
  let e := (Module.finBasisOfFinrankEq (ZMod 2) U hdim).equivFun
  have hcard : (Finset.univ.filter (fun x => (f ∘ e.symm) x = 1)).card = 4 := by
    simpa only [Function.comp_apply] using (support_card_eq_three_coordinates f e).symm.trans hf
  have he := finrank_periodQuotient_eq_iff_period_free f
  rw [hdim] at he
  rw [vectorDegree_eq_coordinates f e, he, period_free_iff_three_coordinates f e]
  have hc := balanced_degree_two_iff_essential_dimension_three (f ∘ e.symm) hcard
  have hec := finrank_periodQuotient_eq_iff_period_free (f ∘ e.symm)
  simp only [Module.finrank_pi, Fintype.card_fin] at hec
  rwa [hec] at hc

/-- The intrinsic height-two count is 56 on every three-dimensional binary
vector space, independently of the linear coordinate choice. -/
theorem balanced_vectorDegree_two_card (hdim : Module.finrank (ZMod 2) U = 3) :
    Nat.card {f : U → ZMod 2 //
      Nat.card {x : U // f x = 1} = 4 ∧ vectorDegree f = 2} = 56 := by
  let e := (Module.finBasisOfFinrankEq (ZMod 2) U hdim).equivFun
  let ef : (U → ZMod 2) ≃ ((Fin 3 → ZMod 2) → ZMod 2) :=
    Equiv.arrowCongr e.toEquiv (Equiv.refl (ZMod 2))
  let es := ef.subtypeEquiv (p := fun f =>
      Nat.card {x : U // f x = 1} = 4 ∧ vectorDegree f = 2)
    (q := fun g => (Finset.univ.filter (fun x => g x = 1)).card = 4 ∧ degree g = 2)
    (fun f => by
      change (Nat.card {x : U // f x = 1} = 4 ∧ vectorDegree f = 2) ↔
        ((Finset.univ.filter (fun x => f (e.symm x) = 1)).card = 4 ∧
          degree (f ∘ e.symm) = 2)
      rw [support_card_eq_three_coordinates f e, vectorDegree_eq_coordinates f e])
  rw [Nat.card_congr es]
  exact balanced_degree_two_card

end
end BinaryFieldCounterexamples.BooleanFunctions
