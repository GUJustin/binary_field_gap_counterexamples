/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.CollisionPairs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Pooling distinct affine functions giving the challenges

Distinct affine functions on a positive-dimensional finite vector space agree
on at most one affine hyperplane.  Summing this pairwise bound and applying
collision averaging produces a parameter where many challenge values are distinct.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Finset

attribute [local instance] Classical.decEq Classical.propDecidable

/-- The zero fiber of a nonzero linear functional on `Fin r → F` has
cardinality `|F|^(r-1)`. -/
theorem nonzeroLinearMap_zeroFiber_card
    {F : Type*} [Field F] [Fintype F]
    (r : ℕ) (L : (Fin r → F) →ₗ[F] F) (hL : L ≠ 0) :
    (Finset.univ.filter fun x ↦ L x = 0).card = (Fintype.card F) ^ (r - 1) := by
  classical
  letI : Fintype (LinearMap.ker L) := Fintype.ofFinite _
  have hr := Module.Dual.finrank_ker_add_one_of_ne_zero hL
  have hdim : Module.finrank F (Fin r → F) = r := by simp
  rw [hdim] at hr
  have hk : Module.finrank F (LinearMap.ker L) = r - 1 := by omega
  have hc := Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker L)
  rw [hk] at hc
  simp only [Nat.card_eq_fintype_card] at hc
  rw [← hc, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun x ↦ ⟨x.1, by simpa using (Finset.mem_filter.mp x.2).2⟩
      invFun := fun x ↦ ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [LinearMap.mem_ker] using x.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- Two distinct affine scalar-valued maps on `Fin r → F` agree at no more
than `|F|^(r-1)` parameters. -/
theorem affineMap_collision_fiber_card_le
    {F : Type*} [Field F] [Fintype F]
    (r : ℕ) (f g : (Fin r → F) →ᵃ[F] F) (hfg : f ≠ g) :
    (Finset.univ.filter fun x ↦ f x = g x).card ≤ (Fintype.card F) ^ (r - 1) := by
  classical
  let L : (Fin r → F) →ₗ[F] F := f.linear - g.linear
  have heq (x : Fin r → F) : f x = g x ↔ L x = g 0 - f 0 := by
    have hf := congrFun (AffineMap.decomp f) x
    have hg := congrFun (AffineMap.decomp g) x
    change f x = f.linear x + f 0 at hf
    change g x = g.linear x + g 0 at hg
    rw [hf, hg]
    change f.linear x + f 0 = g.linear x + g 0 ↔
      f.linear x - g.linear x = g 0 - f 0
    rw [sub_eq_sub_iff_add_eq_add]
    simp [add_comm]
  by_cases hL : L = 0
  · have hzero : f 0 ≠ g 0 := by
      intro h0
      apply hfg
      apply AffineMap.ext
      intro x
      rw [heq]
      simp [L, hL, h0]
    have hn : (0 : F) ≠ g 0 - f 0 := by
      intro h
      exact hzero (sub_eq_zero.mp h.symm).symm
    have hempty : (Finset.univ.filter fun x ↦ f x = g x) = ∅ := by
      ext x
      simp [heq, L, hL, hn]
    simp [hempty]
  · have hsurj := LinearMap.surjective hL
    obtain ⟨x, hx⟩ := hsurj (g 0 - f 0)
    have hfiber := AddMonoidHom.card_fiber_eq_of_mem_range L
      (show g 0 - f 0 ∈ Set.range L from ⟨x, hx⟩)
      (show 0 ∈ Set.range L from ⟨0, map_zero L⟩)
    have hker := nonzeroLinearMap_zeroFiber_card r L hL
    calc
      (Finset.univ.filter fun y ↦ f y = g y).card =
          (Finset.univ.filter fun y ↦ L y = g 0 - f 0).card := by
        congr 1
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact heq y
      _ = (Finset.univ.filter fun y ↦ L y = 0).card := hfiber
      _ = (Fintype.card F) ^ (r - 1) := hker
      _ ≤ (Fintype.card F) ^ (r - 1) := le_rfl

/-- A uniform pairwise collision bound gives a total unordered-collision
budget equal to the bound times the number of unordered index pairs. -/
theorem sum_unorderedCollisionCount_le_choose_two_mul
    {Index Parameter Label : Type*} [LinearOrder Index] [DecidableEq Label]
    (P : Finset Parameter) (S : Finset Index)
    (label : Parameter → Index → Label) (B : ℕ)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (P.filter fun p ↦ label p i = label p j).card ≤ B) :
    ∑ p ∈ P, unorderedCollisionCount S (label p) ≤ S.card.choose 2 * B := by
  classical
  let pairs := (S ×ˢ S).filter fun ij ↦ ij.1 < ij.2
  calc
    ∑ p ∈ P, unorderedCollisionCount S (label p) =
        ∑ p ∈ P, (pairs.filter fun ij ↦ label p ij.1 = label p ij.2).card := by
      apply Finset.sum_congr rfl
      intro p _
      rw [unorderedCollisionCount_eq_card_pairCollisions]
      congr 1
      ext ij
      simp only [pairs, Finset.mem_filter, Finset.mem_product]
      tauto
    _ = ∑ ij ∈ pairs, (P.filter fun p ↦ label p ij.1 = label p ij.2).card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _ij ∈ pairs, B := by
      apply Finset.sum_le_sum
      intro ij hij
      rcases Finset.mem_filter.mp hij with ⟨hijS, hijlt⟩
      rcases Finset.mem_product.mp hijS with ⟨hi, hj⟩
      exact hpair ij.1 hi ij.2 hj (ne_of_lt hijlt)
    _ = S.card.choose 2 * B := by
      simp [pairs, Finset.card_product_filter_lt]

/-- A finite family of pairwise distinct affine functions on a
positive-dimensional parameter space has one parameter whose image realizes
the exact collision-averaging lower bound `⌈q M / (q + M - 1)⌉`. -/
theorem exists_affineLabel_parameter_image_card_lower
    {Index F : Type*} [Field F] [Fintype F]
    (r : ℕ) (hr : 1 ≤ r) (S : Finset Index)
    (label : Index → ((Fin r → F) →ᵃ[F] F))
    (hinj : Set.InjOn label S) :
    ∃ x : Fin r → F,
      natCeilDiv (Fintype.card F * S.card)
          (Fintype.card F + S.card - 1) ≤
        (S.image fun i ↦ label i x).card := by
  classical
  by_cases hS : S.card = 0
  · refine ⟨0, ?_⟩
    simp [hS, natCeilDiv]
  let P : Finset (Fin r → F) := Finset.univ
  let SI : Finset S := Finset.univ
  let B := (Fintype.card F) ^ (r - 1)
  letI : LinearOrder S := (Finset.equivFin S).linearOrder
  have hpair : ∀ i ∈ SI, ∀ j ∈ SI, i ≠ j →
      (P.filter fun x ↦ label i x = label j x).card ≤ B := by
    intro i hi j hj hij
    apply (show (Finset.univ.filter fun x ↦ label i x = label j x).card ≤ B from ?_)
    exact affineMap_collision_fiber_card_le r (label i) (label j)
      (fun h ↦ hij (Subtype.ext (hinj i.2 j.2 h)))
  have htotal : ∑ x ∈ P, unorderedCollisionCount SI (fun i ↦ label i x) ≤
      SI.card.choose 2 * B := by
    exact sum_unorderedCollisionCount_le_choose_two_mul
      P SI (fun x i ↦ label i x) B hpair
  have hP : P.Nonempty := by simp [P]
  obtain ⟨x, _hxP, _hadd, hsecond⟩ :=
    exists_parameter_image_card_bounds P SI (fun x i ↦ label i x)
      (SI.card.choose 2 * B) hP htotal
  have hSIcard : SI.card = S.card := by simp [SI]
  have himage : (SI.image fun i : S ↦ label i x).card =
      (S.image fun i ↦ label i x).card := by
    congr 1
    ext z
    simp [SI]
  rw [hSIcard] at hsecond
  refine ⟨x, ?_⟩
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hlargeDen : 0 < P.card * S.card + 2 * (S.card.choose 2 * B) := by positivity
  have hsmallDen : 0 < Fintype.card F + S.card - 1 := by omega
  rw [natCeilDiv_eq_rat_ceil _ _ hsmallDen]
  rw [natCeilDiv_eq_rat_ceil _ _ hlargeDen] at hsecond
  have hPcard : P.card = (Fintype.card F) ^ r := by simp [P]
  have hpow : (Fintype.card F) ^ r = B * Fintype.card F := by
    calc
      (Fintype.card F) ^ r = (Fintype.card F) ^ ((r - 1) + 1) := by
        congr 1
        omega
      _ = B * Fintype.card F := by simp [B, pow_add]
  have hchoose : 2 * (S.card.choose 2 * B) = S.card * (S.card - 1) * B := by
    calc
      2 * (S.card.choose 2 * B) = (S.card.choose 2 * 2) * B := by ac_rfl
      _ = S.card * (S.card - 1) * B := by
        rw [Nat.choose_two_right,
          Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self S.card)]
  have hdenrewrite : Fintype.card F + S.card - 1 =
      Fintype.card F + (S.card - 1) := by omega
  have hrat :
      ((Fintype.card F * S.card : ℕ) : ℚ) /
          (Fintype.card F + S.card - 1 : ℕ) =
      ((P.card * S.card ^ 2 : ℕ) : ℚ) /
          (P.card * S.card + 2 * (S.card.choose 2 * B) : ℕ) := by
    rw [hPcard, hpow, hchoose, hdenrewrite]
    push_cast
    have hB : (B : ℚ) ≠ 0 := by
      exact_mod_cast (pow_pos hq (r - 1)).ne'
    field_simp [hB]
  rw [hrat, ← himage]
  exact hsecond

/-- Rational-ceiling form of `exists_affineLabel_parameter_image_card_lower`. -/
theorem exists_affineLabel_parameter_image_card_lower_ratCeil
    {Index F : Type*} [Field F] [Fintype F]
    (r : ℕ) (hr : 1 ≤ r) (S : Finset Index)
    (label : Index → ((Fin r → F) →ᵃ[F] F))
    (hinj : Set.InjOn label S) :
    ∃ x : Fin r → F,
      ⌈((Fintype.card F * S.card : ℕ) : ℚ) /
          (Fintype.card F + S.card - 1 : ℕ)⌉₊ ≤
        (S.image fun i ↦ label i x).card := by
  obtain ⟨x, hx⟩ := exists_affineLabel_parameter_image_card_lower r hr S label hinj
  refine ⟨x, ?_⟩
  have hden : 0 < Fintype.card F + S.card - 1 := by
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  rw [← natCeilDiv_eq_rat_ceil _ _ hden]
  exact hx

end BinaryFieldCounterexamples
