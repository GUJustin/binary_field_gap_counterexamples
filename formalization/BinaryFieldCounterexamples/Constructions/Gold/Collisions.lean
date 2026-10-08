/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.Distinctness
public import BinaryFieldCounterexamples.Constructions.Gold.Compression
public import BinaryFieldCounterexamples.Constructions.Gold.Family
public import BinaryFieldCounterexamples.Counting.CollisionPairs
public import Mathlib.Data.Fintype.EquivFin

/-!
# Exterior collisions in the Gold locator family
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold

open Polynomial

variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]

/-- A uniform pairwise collision bound gives the corresponding total
unordered-collision budget. -/
theorem sum_unorderedCollisionCount_le_mul_choose_two
    {Index Parameter Label : Type*} [LinearOrder Index] [DecidableEq Label]
    (P : Finset Parameter) (S : Finset Index) (label : Parameter → Index → Label)
    (δ : ℕ)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (P.filter fun p ↦ label p i = label p j).card ≤ δ) :
    ∑ p ∈ P, unorderedCollisionCount S (label p) ≤ δ * S.card.choose 2 := by
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
    _ ≤ ∑ _ij ∈ pairs, δ := by
      apply Finset.sum_le_sum
      intro ij hij
      change ij ∈ (S ×ˢ S).filter (fun ij ↦ ij.1 < ij.2) at hij
      rcases Finset.mem_filter.mp hij with ⟨hijS, hijlt⟩
      rcases Finset.mem_product.mp hijS with ⟨hi, hj⟩
      exact hpair ij.1 hi ij.2 hj (ne_of_lt hijlt)
    _ = δ * S.card.choose 2 := by
      simp [pairs, Finset.card_product_filter_lt, Nat.mul_comm]

/-- Two subsets of a finite type whose cardinalities sum to more than the
ambient cardinality have a common point. -/
theorem exists_common_of_card_add_gt {α : Type*} [Fintype α]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (h : Nat.card {x : α // p x} + Nat.card {x : α // q x} > Nat.card α) :
    ∃ x, p x ∧ q x := by
  classical
  by_contra hn
  push_neg at hn
  let S := Finset.univ.filter p
  let T := Finset.univ.filter q
  have hdis : Disjoint S T := Finset.disjoint_left.mpr fun x hxS hxT ↦
    hn x (Finset.mem_filter.mp hxS).2 (Finset.mem_filter.mp hxT).2
  have hle : (S ∪ T).card ≤ (Finset.univ : Finset α).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hdis] at hle
  have hS : S.card = Nat.card {x : α // p x} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hT : T.card = Nat.card {x : α // q x} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hS, hT, Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  omega

/-- Two Gold majority repairs always have a common zero in the prescribed
domain. -/
theorem exists_common_repairedPolynomial_root (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2 ^ (k + 1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A₁ A₂ : TensorCoordinates d)
    (l₁ l₂ : D →+ ZMod 2) (κ₁ κ₂ : ZMod 2) (t : ℕ)
    (hzeros₁ : Nat.card {x : D // tensorQuadraticFunction D v A₁ x + l₁ x + κ₁ = 0} =
      2 ^ k + 2 ^ (k - t))
    (hzeros₂ : Nat.card {x : D // tensorQuadraticFunction D v A₂ x + l₂ x + κ₂ = 0} =
      2 ^ k + 2 ^ (k - t)) :
    ∃ x : D, (repairedPolynomial D v A₁ l₁ κ₁).eval (x : B) = 0 ∧
      (repairedPolynomial D v A₂ l₂ κ₂).eval (x : B) = 0 := by
  let p : D → Prop := fun x ↦ tensorQuadraticFunction D v A₁ x + l₁ x + κ₁ = 0
  let q : D → Prop := fun x ↦ tensorQuadraticFunction D v A₂ x + l₂ x + κ₂ = 0
  have hsum : Nat.card {x : D // p x} + Nat.card {x : D // q x} > Nat.card D := by
    rw [show Nat.card {x : D // p x} = 2 ^ k + 2 ^ (k - t) from hzeros₁,
      show Nat.card {x : D // q x} = 2 ^ k + 2 ^ (k - t) from hzeros₂, hD,
      pow_succ]
    have hp : 0 < 2 ^ (k - t) := by positivity
    omega
  obtain ⟨x, hx₁, hx₂⟩ := exists_common_of_card_add_gt p q hsum
  refine ⟨x, ?_, ?_⟩
  · rw [repairedPolynomial_eval]
    exact map_eq_zero (algebraMap (ZMod 2) B) |>.mpr hx₁
  · rw [repairedPolynomial_eval]
    exact map_eq_zero (algebraMap (ZMod 2) B) |>.mpr hx₂

/-- Two discarded factors with the same Artin--Schreier right hand side and
one common root are equal. -/
theorem discardedFactor_eq_of_sq_add_eq_and_common_root
    (H₁ H₂ R : B[X])
    (h₁ : H₁ ^ 2 + H₁ = R) (h₂ : H₂ ^ 2 + H₂ = R)
    (x : B) (hx₁ : H₁.eval x = 0) (hx₂ : H₂.eval x = 0) : H₁ = H₂ := by
  have hs : (H₁ + H₂) ^ 2 + (H₁ + H₂) = 0 := by
    rw [CharTwo.add_sq]
    calc
      H₁ ^ 2 + H₂ ^ 2 + (H₁ + H₂) =
          (H₁ ^ 2 + H₁) + (H₂ ^ 2 + H₂) := by ring
      _ = R + R := by rw [h₁, h₂]
      _ = 0 := CharTwo.add_self_eq_zero R
  have hp : (H₁ + H₂) * (H₁ + H₂ + 1) = 0 := by
    calc
      (H₁ + H₂) * (H₁ + H₂ + 1) = (H₁ + H₂) ^ 2 + (H₁ + H₂) := by ring
      _ = 0 := hs
  rcases mul_eq_zero.mp hp with hz | ho
  · exact (eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq H₂)
  · have he := congrArg (fun P : B[X] ↦ P.eval x) ho
    have : (1 : B) = 0 := by simpa [hx₁, hx₂] using he
    exact (one_ne_zero this).elim

/-- Equality of two quotient-locator derivatives recovers their discarded
factor, provided those factors have a common root. -/
theorem quotientLocator_derivative_eq_imp_discarded_eq
    (η : B) (L U₁ H₁ U₂ H₂ : B[X])
    (hη : η ≠ 0) (hU₁ : U₁ ≠ 0) (hU₂ : U₂ ≠ 0)
    (hH₁ : H₁ ≠ 0) (hH₂ : H₂ ≠ 0) (hdiv₁ : H₁ ∣ L) (hdiv₂ : H₂ ∣ L)
    (hAS₁ : H₁ ^ 2 + H₁ = C (η ^ 2) * L * U₁ ^ 2)
    (hAS₂ : H₂ ^ 2 + H₂ = C (η ^ 2) * L * U₂ ^ 2)
    (hH₁' : H₁.derivative = U₁ ^ 2) (hH₂' : H₂.derivative = U₂ ^ 2)
    (hU₁' : U₁.derivative = 0) (hU₂' : U₂.derivative = 0)
    (x : B) (hx₁ : H₁.eval x = 0) (hx₂ : H₂.eval x = 0)
    (he : (quotientLocator η U₁ L H₁).derivative =
      (quotientLocator η U₂ L H₂).derivative) : H₁ = H₂ := by
  rw [quotientLocator_derivative η U₁ L H₁ hη hU₁ hH₁ hdiv₁ hAS₁ hH₁' hU₁',
    quotientLocator_derivative η U₂ L H₂ hη hU₂ hH₂ hdiv₂ hAS₂ hH₂' hU₂'] at he
  have hC : C (η⁻¹) ≠ (0 : B[X]) := C_ne_zero.mpr (inv_ne_zero hη)
  have hU : U₁ = U₂ := mul_left_cancel₀ hC he
  subst U₂
  exact discardedFactor_eq_of_sq_add_eq_and_common_root H₁ H₂
    (C (η ^ 2) * L * U₁ ^ 2) hAS₁ hAS₂ x hx₁ hx₂

/-- Distinct Gold locators obtained from majority repairs have distinct formal
derivatives. -/
theorem repairedLocator_derivative_ne (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2 ^ (k + 1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A₁ A₂ : TensorCoordinates d)
    (l₁ l₂ : D →+ ZMod 2) (κ₁ κ₂ : ZMod 2) (t : ℕ)
    (ht0 : 2 ≤ t) (ht : 2 * t ≤ k + 1)
    (hM₁ : ∀ r, 1 ≤ r → r < t → goldMoment D v A₁ r = 0)
    (hM₂ : ∀ r, 1 ≤ r → r < t → goldMoment D v A₂ r = 0)
    (hr₁ : tensorPolarRank D v A₁ = 2 * t)
    (hr₂ : tensorPolarRank D v A₂ = 2 * t)
    (hzeros₁ : Nat.card {x : D // tensorQuadraticFunction D v A₁ x + l₁ x + κ₁ = 0} =
      2 ^ k + 2 ^ (k - t))
    (hzeros₂ : Nat.card {x : D // tensorQuadraticFunction D v A₂ x + l₂ x + κ₂ = 0} =
      2 ^ k + 2 ^ (k - t))
    (hne : repairedLocator D v A₁ l₁ κ₁ t ≠ repairedLocator D v A₂ l₂ κ₂ t) :
    (repairedLocator D v A₁ l₁ κ₁ t).derivative ≠
      (repairedLocator D v A₂ l₂ κ₂ t).derivative := by
  let H₁ := repairedPolynomial D v A₁ l₁ κ₁
  let H₂ := repairedPolynomial D v A₂ l₂ κ₂
  let U₁ := repairedSquareRoot t H₁
  let U₂ := repairedSquareRoot t H₂
  let L := subspacePolynomial D
  let η := normalizingRoot D
  have hdegrees₁ := repairedPolynomial_natDegrees D k hD v A₁ l₁ κ₁ t ht0 ht hM₁ hr₁
  have hdegrees₂ := repairedPolynomial_natDegrees D k hD v A₂ l₂ κ₂ t ht0 ht hM₂ hr₂
  have hH₁ : H₁ ≠ 0 := by
    intro hz
    have hd := hdegrees₁.1
    rw [show repairedPolynomial D v A₁ l₁ κ₁ = H₁ from rfl, hz, natDegree_zero] at hd
    have hp : 0 < 2 ^ k + 2 ^ (k - t) := by positivity
    omega
  have hH₂ : H₂ ≠ 0 := by
    intro hz
    have hd := hdegrees₂.1
    rw [show repairedPolynomial D v A₂ l₂ κ₂ = H₂ from rfl, hz, natDegree_zero] at hd
    have hp : 0 < 2 ^ k + 2 ^ (k - t) := by positivity
    omega
  have hU₁ : U₁ ≠ 0 := by
    intro hz
    have hd := hdegrees₁.2
    rw [show repairedSquareRoot t (repairedPolynomial D v A₁ l₁ κ₁) = U₁ from rfl,
      hz, natDegree_zero] at hd
    have hp : 0 < 2 ^ (k - t) := by positivity
    omega
  have hU₂ : U₂ ≠ 0 := by
    intro hz
    have hd := hdegrees₂.2
    rw [show repairedSquareRoot t (repairedPolynomial D v A₂ l₂ κ₂) = U₂ from rfl,
      hz, natDegree_zero] at hd
    have hp : 0 < 2 ^ (k - t) := by positivity
    omega
  have hdiv₁ : H₁ ∣ L :=
    (repairedPolynomial_dvd_locator D k hD v A₁ l₁ κ₁ t ht0 ht hM₁ hr₁ hzeros₁).1
  have hdiv₂ : H₂ ∣ L :=
    (repairedPolynomial_dvd_locator D k hD v A₂ l₂ κ₂ t ht0 ht hM₂ hr₂ hzeros₂).1
  have hU₁' : U₁.derivative = 0 := repairedSquareRoot_derivative t ht0 H₁
  have hU₂' : U₂.derivative = 0 := repairedSquareRoot_derivative t ht0 H₂
  have hH₁' : H₁.derivative = U₁ ^ 2 :=
    (repairedSquareRoot_sq t (by omega) H₁
      (repairedPolynomial_derivative_support D k hD v A₁ l₁ κ₁ t hM₁)).symm
  have hH₂' : H₂.derivative = U₂ ^ 2 :=
    (repairedSquareRoot_sq t (by omega) H₂
      (repairedPolynomial_derivative_support D k hD v A₂ l₂ κ₂ t hM₂)).symm
  have hAS₁ : H₁ ^ 2 + H₁ = C (η ^ 2) * L * U₁ ^ 2 := by
    rw [show H₁ ^ 2 + H₁ = normalizedLocator D * H₁.derivative from
      repairedPolynomial_artinSchreier D v A₁ l₁ κ₁, hH₁', normalizedLocator,
      ← normalizingRoot_sq]
  have hAS₂ : H₂ ^ 2 + H₂ = C (η ^ 2) * L * U₂ ^ 2 := by
    rw [show H₂ ^ 2 + H₂ = normalizedLocator D * H₂.derivative from
      repairedPolynomial_artinSchreier D v A₂ l₂ κ₂, hH₂', normalizedLocator,
      ← normalizingRoot_sq]
  obtain ⟨x, hx₁, hx₂⟩ :=
    exists_common_repairedPolynomial_root D k hD v A₁ A₂ l₁ l₂ κ₁ κ₂ t hzeros₁ hzeros₂
  intro he
  have hHeq := quotientLocator_derivative_eq_imp_discarded_eq η L U₁ H₁ U₂ H₂
    (normalizingRoot_ne_zero D) hU₁ hU₂ hH₁ hH₂ hdiv₁ hdiv₂ hAS₁ hAS₂
    hH₁' hH₂' hU₁' hU₂' x hx₁ hx₂ he
  apply hne
  simp only [repairedLocator]
  rw [show repairedPolynomial D v A₁ l₁ κ₁ = H₁ from rfl,
    show repairedPolynomial D v A₂ l₂ κ₂ = H₂ from rfl, hHeq]

/-- A collision of two mapped locators outside the mapped domain forces a
collision of their mapped formal derivatives. -/
theorem mapped_recovery_collision_derivative {F : Type*} [Field F]
    (φ : B →+* F) (hφ : Function.Injective φ) (L P₁ P₂ : B[X]) (c : B)
    (hc : c ≠ 0)
    (hrec₁ : P₁.derivative * (P₁ ^ 2 + L) = C c * P₁)
    (hrec₂ : P₂.derivative * (P₂ ^ 2 + L) = C c * P₂)
    (β : F) (hβ : (L.map φ).eval β ≠ 0)
    (he : (P₁.map φ).eval β = (P₂.map φ).eval β) :
    (P₁.derivative.map φ).eval β = (P₂.derivative.map φ).eval β := by
  have hr₁ := congrArg (fun Q : B[X] ↦ (Q.map φ).eval β) hrec₁
  have hr₂ := congrArg (fun Q : B[X] ↦ (Q.map φ).eval β) hrec₂
  simp at hr₁ hr₂
  let z := (P₂.map φ).eval β
  have hden : z ^ 2 + (L.map φ).eval β ≠ 0 := by
    intro hz
    rw [he] at hr₁
    rw [hz, mul_zero] at hr₁
    have hφc : φ c ≠ 0 := fun h ↦ hc (hφ (h.trans (map_zero φ).symm))
    have hz0 : z = 0 := (mul_eq_zero.mp hr₁.symm).resolve_left hφc
    rw [hz0, zero_pow (by decide), zero_add] at hz
    exact hβ hz
  rw [he] at hr₁
  exact mul_right_cancel₀ hden (hr₁.trans hr₂.symm)

/-- The formal derivative of an actual repaired Gold locator is the scaled
Frobenius power appearing in its definition. -/
theorem repairedLocator_derivative_eq (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2 ^ (k + 1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (l : D →+ ZMod 2) (κ : ZMod 2) (t : ℕ)
    (ht0 : 2 ≤ t) (ht : 2 * t ≤ k + 1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2 * t)
    (hzeros : Nat.card {x : D // tensorQuadraticFunction D v A x + l x + κ = 0} =
      2 ^ k + 2 ^ (k - t)) :
    (repairedLocator D v A l κ t).derivative =
      C ((normalizingRoot D)⁻¹) * repairedSquareRoot t (repairedPolynomial D v A l κ) := by
  let H := repairedPolynomial D v A l κ
  let U := repairedSquareRoot t H
  let L := subspacePolynomial D
  let η := normalizingRoot D
  have hdegrees := repairedPolynomial_natDegrees D k hD v A l κ t ht0 ht hM hr
  have hH : H ≠ 0 := by
    intro hz
    have hd := hdegrees.1
    rw [show repairedPolynomial D v A l κ = H from rfl, hz, natDegree_zero] at hd
    have hp : 0 < 2 ^ k + 2 ^ (k - t) := by positivity
    omega
  have hU : U ≠ 0 := by
    intro hz
    have hd := hdegrees.2
    rw [show repairedSquareRoot t (repairedPolynomial D v A l κ) = U from rfl,
      hz, natDegree_zero] at hd
    have hp : 0 < 2 ^ (k - t) := by positivity
    omega
  have hdiv : H ∣ L :=
    (repairedPolynomial_dvd_locator D k hD v A l κ t ht0 ht hM hr hzeros).1
  have hU' : U.derivative = 0 := repairedSquareRoot_derivative t ht0 H
  have hH' : H.derivative = U ^ 2 :=
    (repairedSquareRoot_sq t (by omega) H
      (repairedPolynomial_derivative_support D k hD v A l κ t hM)).symm
  have hAS : H ^ 2 + H = C (η ^ 2) * L * U ^ 2 := by
    rw [show H ^ 2 + H = normalizedLocator D * H.derivative from
      repairedPolynomial_artinSchreier D v A l κ, hH', normalizedLocator,
      ← normalizingRoot_sq]
  exact quotientLocator_derivative η U L H (normalizingRoot_ne_zero D) hU hH hdiv
    hAS hH' hU'

/-- Recovery plus a Frobenius-power description of two distinct derivatives
bounds their mapped exterior collisions by the degree before that power. -/
theorem card_mapped_collisions_le_of_recovery_frobenius
    {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
    (φ : B →+* F) (hφ : Function.Injective φ)
    (L P₁ P₂ G₁ G₂ : B[X]) (c a : B) (n m : ℕ) (S : Finset F)
    (hc : c ≠ 0) (ha : a ≠ 0)
    (hrec₁ : P₁.derivative * (P₁ ^ 2 + L) = C c * P₁)
    (hrec₂ : P₂.derivative * (P₂ ^ 2 + L) = C c * P₂)
    (hder₁ : P₁.derivative = C a * G₁ ^ (2 ^ n))
    (hder₂ : P₂.derivative = C a * G₂ ^ (2 ^ n))
    (hderne : P₁.derivative ≠ P₂.derivative)
    (hdegree₁ : G₁.natDegree ≤ m) (hdegree₂ : G₂.natDegree ≤ m)
    (hexterior : ∀ β ∈ S, (L.map φ).eval β ≠ 0) :
    (S.filter fun β ↦ (P₁.map φ).eval β = (P₂.map φ).eval β).card ≤ m := by
  classical
  let G := G₁ + G₂
  have hG : G ≠ 0 := by
    intro hz
    have heq : G₁ = G₂ :=
      (eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq G₂)
    apply hderne
    rw [hder₁, hder₂, heq]
  have hGmap : G.map φ ≠ 0 := (Polynomial.map_ne_zero_iff (p := G) hφ).mpr hG
  have hdegree : (G.map φ).natDegree ≤ m := by
    exact (natDegree_map_le : (G.map φ).natDegree ≤ G.natDegree) |>.trans
      ((natDegree_add_le G₁ G₂).trans (max_le hdegree₁ hdegree₂))
  have hsubset : S.filter (fun β ↦ (P₁.map φ).eval β = (P₂.map φ).eval β) ⊆
      S.filter (fun β ↦ (G.map φ).eval β = 0) := by
    intro β hβ
    rw [Finset.mem_filter] at hβ ⊢
    refine ⟨hβ.1, ?_⟩
    have hde := mapped_recovery_collision_derivative φ hφ L P₁ P₂ c hc hrec₁ hrec₂
      β (hexterior β hβ.1) hβ.2
    rw [hder₁, hder₂] at hde
    have hφa : φ a ≠ 0 := fun h ↦ ha (hφ (h.trans (map_zero φ).symm))
    have hde' : φ a * ((G₁.map φ).eval β) ^ (2 ^ n) =
        φ a * ((G₂.map φ).eval β) ^ (2 ^ n) := by simpa using hde
    have hpows : ((G₁.map φ).eval β) ^ (2 ^ n) =
        ((G₂.map φ).eval β) ^ (2 ^ n) := mul_left_cancel₀ hφa hde'
    have hpowzero : (((G₁.map φ).eval β) + ((G₂.map φ).eval β)) ^ (2 ^ n) = 0 := by
      rw [add_pow_expChar_pow, hpows, CharTwo.add_self_eq_zero]
    have hsumzero := (pow_eq_zero_iff (by positivity : 2 ^ n ≠ 0)).mp hpowzero
    simpa [G] using hsumzero
  exact (Finset.card_le_card hsubset).trans
    ((card_filter_eval_eq_zero_le S _ hGmap).trans hdegree)

/-- Any two distinct actual Gold locators collide at no more than the polar
radical scale on a finite set outside the mapped additive domain. -/
theorem card_mapped_repairedLocator_collisions_le
    {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
    (φ : B →+* F) (hφ : Function.Injective φ)
    (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2 ^ (k + 1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A₁ A₂ : TensorCoordinates d)
    (l₁ l₂ : D →+ ZMod 2) (κ₁ κ₂ : ZMod 2) (t : ℕ)
    (ht0 : 2 ≤ t) (ht : 2 * t ≤ k + 1)
    (hM₁ : ∀ r, 1 ≤ r → r < t → goldMoment D v A₁ r = 0)
    (hM₂ : ∀ r, 1 ≤ r → r < t → goldMoment D v A₂ r = 0)
    (hr₁ : tensorPolarRank D v A₁ = 2 * t)
    (hr₂ : tensorPolarRank D v A₂ = 2 * t)
    (hzeros₁ : Nat.card {x : D // tensorQuadraticFunction D v A₁ x + l₁ x + κ₁ = 0} =
      2 ^ k + 2 ^ (k - t))
    (hzeros₂ : Nat.card {x : D // tensorQuadraticFunction D v A₂ x + l₂ x + κ₂ = 0} =
      2 ^ k + 2 ^ (k - t))
    (hne : repairedLocator D v A₁ l₁ κ₁ t ≠ repairedLocator D v A₂ l₂ κ₂ t)
    (S : Finset F)
    (hexterior : ∀ β ∈ S, ((subspacePolynomial D).map φ).eval β ≠ 0) :
    (S.filter fun β ↦ ((repairedLocator D v A₁ l₁ κ₁ t).map φ).eval β =
      ((repairedLocator D v A₂ l₂ κ₂ t).map φ).eval β).card ≤ 2 ^ (k + 1 - 2 * t) := by
  let H₁ := repairedPolynomial D v A₁ l₁ κ₁
  let H₂ := repairedPolynomial D v A₂ l₂ κ₂
  let G₁ := frobeniusRoot t H₁.derivative
  let G₂ := frobeniusRoot t H₂.derivative
  let P₁ := repairedLocator D v A₁ l₁ κ₁ t
  let P₂ := repairedLocator D v A₂ l₂ κ₂ t
  have hrec₁ : P₁.derivative * (P₁ ^ 2 + subspacePolynomial D) =
      C ((subspacePolynomial D).coeff 1) * P₁ :=
    (repairedLocator_properties D k hD v A₁ l₁ κ₁ t ht0 ht hM₁ hr₁ hzeros₁).2.2.2.2
  have hrec₂ : P₂.derivative * (P₂ ^ 2 + subspacePolynomial D) =
      C ((subspacePolynomial D).coeff 1) * P₂ :=
    (repairedLocator_properties D k hD v A₂ l₂ κ₂ t ht0 ht hM₂ hr₂ hzeros₂).2.2.2.2
  have hder₁ : P₁.derivative = C ((normalizingRoot D)⁻¹) * G₁ ^ (2 ^ (t - 1)) := by
    rw [show P₁.derivative = C ((normalizingRoot D)⁻¹) * repairedSquareRoot t H₁ from
      repairedLocator_derivative_eq D k hD v A₁ l₁ κ₁ t ht0 ht hM₁ hr₁ hzeros₁]
    rfl
  have hder₂ : P₂.derivative = C ((normalizingRoot D)⁻¹) * G₂ ^ (2 ^ (t - 1)) := by
    rw [show P₂.derivative = C ((normalizingRoot D)⁻¹) * repairedSquareRoot t H₂ from
      repairedLocator_derivative_eq D k hD v A₂ l₂ κ₂ t ht0 ht hM₂ hr₂ hzeros₂]
    rfl
  have hderne : P₁.derivative ≠ P₂.derivative :=
    repairedLocator_derivative_ne D k hD v A₁ A₂ l₁ l₂ κ₁ κ₂ t ht0 ht hM₁ hM₂
      hr₁ hr₂ hzeros₁ hzeros₂ hne
  have hdegree₁ : G₁.natDegree ≤ 2 ^ (k + 1 - 2 * t) := by
    apply frobeniusRoot_natDegree_le t H₁.derivative (2 ^ (k + 1 - 2 * t))
    have hd := repairedPolynomial_derivative_natDegree D k hD v A₁ l₁ κ₁ t
      (by omega) ht hM₁ hr₁
    have he : k + 1 - t = (k + 1 - 2 * t) + t := by omega
    rw [show H₁ = repairedPolynomial D v A₁ l₁ κ₁ from rfl, hd, he, pow_add]
  have hdegree₂ : G₂.natDegree ≤ 2 ^ (k + 1 - 2 * t) := by
    apply frobeniusRoot_natDegree_le t H₂.derivative (2 ^ (k + 1 - 2 * t))
    have hd := repairedPolynomial_derivative_natDegree D k hD v A₂ l₂ κ₂ t
      (by omega) ht hM₂ hr₂
    have he : k + 1 - t = (k + 1 - 2 * t) + t := by omega
    rw [show H₂ = repairedPolynomial D v A₂ l₂ κ₂ from rfl, hd, he, pow_add]
  exact card_mapped_collisions_le_of_recovery_frobenius φ hφ (subspacePolynomial D)
    P₁ P₂ G₁ G₂ ((subspacePolynomial D).coeff 1) ((normalizingRoot D)⁻¹) (t - 1)
    (2 ^ (k + 1 - 2 * t)) S (subspacePolynomial_coeff_one_ne_zero D)
    (inv_ne_zero (normalizingRoot_ne_zero D)) hrec₁ hrec₂ hder₁ hder₂ hderne
    hdegree₁ hdegree₂ hexterior


/-- Both collision bounds hold at the same exterior pole. -/
theorem exists_exterior_parameter_repairedLocator_image_bounds
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [DecidableEq F]
    (φ : B →+* F) (hφ : Function.Injective φ)
    (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2 ^ (k + 1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ)
    (ht0 : 2 ≤ t) (ht : 2 * t ≤ k + 1)
    (ps : Finset B[X])
    (hps : ∀ p ∈ ps, ∃ A ∈ momentTensors D v t, ∃ l : D →+ ZMod 2, ∃ κ : ZMod 2,
      p = repairedLocator D v A l κ t ∧
        Nat.card {y : D // tensorQuadraticFunction D v A y + l y + κ = 0} =
          2 ^ k + 2 ^ (k - t))
    (E : Finset F) (hE : E.Nonempty)
    (hexterior : ∀ β ∈ E, ((subspacePolynomial D).map φ).eval β ≠ 0) :
    ∃ β ∈ E,
      ps.card - (2 ^ (k + 1 - 2 * t) * ps.card.choose 2) / E.card ≤
        (ps.image fun p ↦ (p.map φ).eval β).card ∧
      natCeilDiv (ps.card * E.card)
          (E.card + 2 ^ (k + 1 - 2 * t) * (ps.card - 1)) ≤
        (ps.image fun p ↦ (p.map φ).eval β).card := by
  classical
  letI : LinearOrder ps := (Finset.equivFin ps).linearOrder
  let label : F → ps → F := fun β p ↦ (p.val.map φ).eval β
  have hpair : ∀ i ∈ (Finset.univ : Finset ps), ∀ j ∈ (Finset.univ : Finset ps), i ≠ j →
      (E.filter fun β ↦ label β i = label β j).card ≤ 2 ^ (k + 1 - 2 * t) := by
    intro i _ j _ hij
    obtain ⟨A₁, hA₁, l₁, κ₁, hi, hz₁⟩ := hps i.val i.property
    obtain ⟨A₂, hA₂, l₂, κ₂, hj, hz₂⟩ := hps j.val j.property
    obtain ⟨hr₁, hM₁⟩ := (mem_momentTensors D v t A₁).mp hA₁
    obtain ⟨hr₂, hM₂⟩ := (mem_momentTensors D v t A₂).mp hA₂
    have hpne : repairedLocator D v A₁ l₁ κ₁ t ≠ repairedLocator D v A₂ l₂ κ₂ t := by
      intro heq
      apply hij
      apply Subtype.ext
      exact hi.trans (heq.trans hj.symm)
    simpa only [label, hi, hj] using
      card_mapped_repairedLocator_collisions_le φ hφ D k hD v A₁ A₂ l₁ l₂ κ₁ κ₂ t
        ht0 ht hM₁ hM₂ hr₁ hr₂ hz₁ hz₂ hpne E hexterior
  have htotal : ∑ β ∈ E, unorderedCollisionCount (Finset.univ : Finset ps) (label β) ≤
      2 ^ (k + 1 - 2 * t) * ps.card.choose 2 := by
    simpa using sum_unorderedCollisionCount_le_mul_choose_two E
      (Finset.univ : Finset ps) label (2 ^ (k + 1 - 2 * t)) hpair
  obtain ⟨β, hβ, hfirst, hsecond⟩ := exists_parameter_image_card_bounds E
    (Finset.univ : Finset ps) label (2 ^ (k + 1 - 2 * t) * ps.card.choose 2) hE htotal
  have himage : ((Finset.univ : Finset ps).image (label β)).card =
      (ps.image fun p ↦ (p.map φ).eval β).card := by
    congr 1
    ext z
    simp [label]
  rw [Finset.card_univ, Fintype.card_coe, himage] at hfirst hsecond
  refine ⟨β, hβ, hfirst, ?_⟩
  by_cases hps0 : ps.card = 0
  · simp [hps0, natCeilDiv]
  have hpspos : 0 < ps.card := Nat.pos_of_ne_zero hps0
  have hdenraw : 0 < E.card * ps.card +
      2 * (2 ^ (k + 1 - 2 * t) * ps.card.choose 2) := by positivity
  have hraw := (natCeilDiv_le_iff_le_mul hdenraw).mp hsecond
  have hchoose : 2 * ps.card.choose 2 = ps.card * (ps.card - 1) := by
    rw [Nat.choose_two_right]
    simpa [Nat.mul_comm] using
      Nat.mul_div_cancel' ps.card.even_mul_pred_self.two_dvd
  apply (natCeilDiv_le_iff_le_mul (by positivity :
    0 < E.card + 2 ^ (k + 1 - 2 * t) * (ps.card - 1))).mpr
  apply Nat.le_of_mul_le_mul_left (c := ps.card) _ hpspos
  calc
    ps.card * (ps.card * E.card) = E.card * ps.card ^ 2 := by ring
    _ ≤ (ps.image fun p ↦ (p.map φ).eval β).card *
        (E.card * ps.card + 2 * (2 ^ (k + 1 - 2 * t) * ps.card.choose 2)) := hraw
    _ = ps.card * ((ps.image fun p ↦ (p.map φ).eval β).card *
        (E.card + 2 ^ (k + 1 - 2 * t) * (ps.card - 1))) := by
      rw [show 2 * (2 ^ (k + 1 - 2 * t) * ps.card.choose 2) =
        2 ^ (k + 1 - 2 * t) * (2 * ps.card.choose 2) by ring]
      rw [hchoose]
      ring

/-- Collision averaging over a literal finite Gold locator family produces
one exterior parameter with the paper's simplified energy lower bound. -/
theorem exists_exterior_parameter_repairedLocator_image_bound
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [DecidableEq F]
    (φ : B →+* F) (hφ : Function.Injective φ)
    (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2 ^ (k + 1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ)
    (ht0 : 2 ≤ t) (ht : 2 * t ≤ k + 1)
    (ps : Finset B[X])
    (hps : ∀ p ∈ ps, ∃ A ∈ momentTensors D v t, ∃ l : D →+ ZMod 2, ∃ κ : ZMod 2,
      p = repairedLocator D v A l κ t ∧
        Nat.card {y : D // tensorQuadraticFunction D v A y + l y + κ = 0} =
          2 ^ k + 2 ^ (k - t))
    (E : Finset F) (hE : E.Nonempty)
    (hexterior : ∀ β ∈ E, ((subspacePolynomial D).map φ).eval β ≠ 0) :
    ∃ β ∈ E,
      natCeilDiv (ps.card * E.card)
          (E.card + 2 ^ (k + 1 - 2 * t) * (ps.card - 1)) ≤
        (ps.image fun p ↦ (p.map φ).eval β).card := by
  obtain ⟨β,hβ,_,hsecond⟩ := exists_exterior_parameter_repairedLocator_image_bounds
    φ hφ D k hD v t ht0 ht ps hps E hE hexterior
  exact ⟨β,hβ,hsecond⟩

end BinaryFieldCounterexamples.Gold
