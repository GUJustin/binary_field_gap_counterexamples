/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Polynomial.LocatorRemainders
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.FinCases

/-!
# Canonical polynomial representatives of binary functionals

A binary functional on a prescribed additive domain is represented by a
polynomial of degree at most half the domain size. For a nonzero functional,
the representative is the normalized product locator of its kernel. The
Lagrange representative fixes the polynomial itself, not merely its values on
the domain, as required when the Gold construction later evaluates outside it.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold

open Polynomial BinaryLocator

/-- A binary scalar is either zero or one. -/
theorem binary_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A nonzero binary functional is surjective onto the two-element field. -/
theorem binaryFunctional_surjective
    {V : Type*} [AddGroup V] (l : V →+ ZMod 2) (hl : l ≠ 0) :
    Function.Surjective l := by
  have hex : ∃ x : V, l x ≠ 0 := by
    by_contra! h
    exact hl (AddMonoidHom.ext h)
  obtain ⟨y, hy⟩ := hex
  have hyone : l y = 1 := (binary_eq_zero_or_one (l y)).resolve_left hy
  intro z
  rcases binary_eq_zero_or_one z with rfl | rfl
  · exact ⟨0, map_zero l⟩
  · exact ⟨y, hyone⟩

/-- The ambient subgroup on which a binary functional vanishes. -/
def functionalKernel {B : Type*} [AddCommGroup B]
    (D : AddSubgroup B) (l : D →+ ZMod 2) : AddSubgroup B :=
  l.ker.map D.subtype

/-- Kernel membership agrees with vanishing of the original functional. -/
theorem mem_functionalKernel
    {B : Type*} [AddCommGroup B] (D : AddSubgroup B) (l : D →+ ZMod 2) (x : D) :
    (x : B) ∈ functionalKernel D l ↔ l x = 0 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have he : y = x := Subtype.ext hxy
    exact he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- A nonzero functional has a kernel containing precisely half the domain. -/
theorem card_functionalKernel_mul_two
    {B : Type*} [AddCommGroup B] [Finite B]
    (D : AddSubgroup B) (l : D →+ ZMod 2) (hl : l ≠ 0) :
    Nat.card (functionalKernel D l) * 2 = Nat.card D := by
  have he := QuotientAddGroup.quotientKerEquivOfSurjective l (binaryFunctional_surjective l hl)
  have hq : Nat.card (D ⧸ l.ker) = 2 := by
    rw [Nat.card_congr he.toEquiv]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup l.ker
  rw [hq] at hc
  rw [functionalKernel, AddSubgroup.card_map_of_injective D.subtype_injective]
  omega

/-- A binary functional has a binary-supported polynomial representative of
natural degree at most half the prescribed domain size. -/
theorem exists_functional_polynomial
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (l : D →+ ZMod 2) :
    ∃ P : B[X], IsBinaryLinearized P ∧ P.natDegree ≤ Nat.card D / 2 ∧
      ∀ x : D, P.eval (x : B) = algebraMap (ZMod 2) B (l x) := by
  classical
  by_cases hl : l = 0
  · refine ⟨0, ?_, by simp, ?_⟩
    · intro n hn
      simp at hn
    · intro x
      simp [hl]
  obtain ⟨y, hy⟩ := binaryFunctional_surjective l hl 1
  let W := functionalKernel D l
  let L := subspacePolynomial W
  have hLne : L.eval (y : B) ≠ 0 := by
    intro he
    have hz := (mem_functionalKernel D l y).mp
      ((subspacePolynomial_eval_eq_zero_iff W (y : B)).mp he)
    rw [hy] at hz
    exact one_ne_zero hz
  let P := C ((L.eval (y : B))⁻¹) * L
  have hs : IsBinaryLinearized P :=
    is_binary_linearized_c_mul _ _ (subspacePolynomial_support W)
  refine ⟨P, hs, ?_, ?_⟩
  · have hc := card_functionalKernel_mul_two D l hl
    change Nat.card W * 2 = Nat.card D at hc
    have hd : L.natDegree = Nat.card W := by
      rw [Nat.card_eq_fintype_card]
      exact subspacePolynomial_natDegree W
    exact (natDegree_C_mul_le _ L).trans (by rw [hd]; omega)
  · intro x
    rcases binary_eq_zero_or_one (l x) with hx | hx
    · have he : L.eval (x : B) = 0 :=
        (subspacePolynomial_eval_eq_zero_iff W (x : B)).mpr
          ((mem_functionalKernel D l x).mpr hx)
      simp [P, he, hx]
    · have hxy : ((x - y : D) : B) ∈ W := by
        apply (mem_functionalKernel D l (x - y)).mpr
        simp [hx, hy]
      have he := subspacePolynomial_eval_add_mem W (y : B) ⟨(x - y : D), hxy⟩
      have he' : L.eval (x : B) = L.eval (y : B) := by
        convert he using 1
        congr 1
        change (x : B) = (y : B) + ((x : B) - (y : B))
        ring
      simp [P, he', hx, hLne]

/-- The canonical polynomial representative is the Lagrange interpolant on
the original domain. Its definition is valid independently of the kernel
description used to prove the stronger degree and support bounds. -/
noncomputable def functionalPolynomial
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (l : D →+ ZMod 2) : B[X] := by
  classical
  exact Lagrange.interpolate Finset.univ (fun x : D ↦ (x : B))
    (fun x : D ↦ algebraMap (ZMod 2) B (l x))

/-- The canonical interpolant represents the given functional at each original
domain coordinate. -/
theorem functionalPolynomial_eval
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (l : D →+ ZMod 2) (x : D) :
    (functionalPolynomial D l).eval (x : B) = algebraMap (ZMod 2) B (l x) := by
  classical
  exact Lagrange.eval_interpolate_at_node _ Subtype.val_injective.injOn (Finset.mem_univ x)

/-- The canonical representative has the strict uniqueness degree bound. -/
theorem functionalPolynomial_degree_lt
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (l : D →+ ZMod 2) :
    (functionalPolynomial D l).degree < Nat.card D := by
  classical
  have h := Lagrange.degree_interpolate_lt
    (s := Finset.univ) (v := fun x : D ↦ (x : B))
    (fun x : D ↦ algebraMap (ZMod 2) B (l x)) Subtype.val_injective.injOn
  simpa only [functionalPolynomial, Finset.card_univ, Nat.card_eq_fintype_card] using h

/-- The interpolant is uniquely determined by its values and degree below the
domain size. This equality is polynomial equality, including outside the domain. -/
theorem eq_functionalPolynomial
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (l : D →+ ZMod 2) (P : B[X])
    (hdeg : P.degree < Nat.card D)
    (heval : ∀ x : D, P.eval (x : B) = algebraMap (ZMod 2) B (l x)) :
    P = functionalPolynomial D l := by
  classical
  apply eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset D)
    (v := fun x : D ↦ (x : B)) Subtype.val_injective.injOn
  · simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hdeg
  · simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using functionalPolynomial_degree_lt D l
  · intro x _
    rw [heval, functionalPolynomial_eval]

/-- Binary coefficient support and the half-domain degree bound hold for the
fixed canonical polynomial, not just for a functionally equivalent representative. -/
theorem functionalPolynomial_support_and_degree
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (l : D →+ ZMod 2) :
    IsBinaryLinearized (functionalPolynomial D l) ∧
      (functionalPolynomial D l).natDegree ≤ Nat.card D / 2 := by
  classical
  obtain ⟨P, hs, hd, he⟩ := exists_functional_polynomial D l
  have hpos : 0 < Nat.card D := by simp only [Nat.card_eq_fintype_card]; exact Fintype.card_pos
  have hlt : P.degree < Nat.card D := (degree_le_of_natDegree_le hd).trans_lt
    (by exact_mod_cast (Nat.div_lt_self hpos (by decide : 1 < 2)))
  rw [← eq_functionalPolynomial D l P hlt he]
  exact ⟨hs, hd⟩

/-- The canonical functional polynomial has no constant term. -/
theorem functionalPolynomial_coeff_zero
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (l : D →+ ZMod 2) :
    (functionalPolynomial D l).coeff 0 = 0 := by
  exact (functionalPolynomial_support_and_degree D l).1.coeff_zero

/-- The product locator divides every polynomial vanishing on its subgroup. -/
theorem subspacePolynomial_dvd_of_eval_zero
    {B : Type*} [Field B] (D : AddSubgroup B) [Fintype D] (P : B[X])
    (hP : ∀ x : D, P.eval (x : B) = 0) : subspacePolynomial D ∣ P := by
  classical
  unfold subspacePolynomial
  apply Finset.prod_dvd_of_coprime
    (fun x _ y _ hxy ↦ pairwise_coprime_X_sub_C Subtype.val_injective hxy)
  intro x _
  exact dvd_iff_isRoot.mpr (hP x)

/-- Binary coefficient support makes the formal derivative constant. -/
theorem derivative_eq_C_of_binarySupport
    {B : Type*} [Field B] [CharP B 2] (P : B[X]) (hP : IsBinaryLinearized P) :
    P.derivative = C (P.coeff 1) := by
  ext n
  cases n with
  | zero => simp [coeff_derivative]
  | succ n =>
    rw [coeff_derivative, coeff_C]
    simp only [Nat.succ_ne_zero, ite_false]
    by_cases hc : P.coeff (n + 1 + 1) = 0
    · simp [hc]
    obtain ⟨i, hi⟩ := hP (n + 1 + 1) (mem_support_iff.mpr hc)
    have hi0 : i ≠ 0 := by intro h; simp [h] at hi
    have hcast : ((n + 1 + 1 : ℕ) : B) = 0 := by
      rw [hi, Nat.cast_pow, Nat.cast_ofNat, (show (2 : B) = 0 from CharTwo.two_eq_zero), zero_pow hi0]
    simpa only [Nat.cast_add, Nat.cast_one, mul_zero] using
      congrArg (P.coeff (n + 1 + 1) * ·) hcast

/-- Squaring and adding a canonical binary functional polynomial gives a
scalar multiple of the domain locator. -/
theorem functionalPolynomial_artinSchreier_scalar
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) [Fintype D] (l : D →+ ZMod 2) :
    ∃ θ : B, (functionalPolynomial D l) ^ 2 + functionalPolynomial D l =
      C θ * subspacePolynomial D := by
  classical
  let P := functionalPolynomial D l
  let Q := P ^ 2 + P
  have hdiv : subspacePolynomial D ∣ Q := by
    apply subspacePolynomial_dvd_of_eval_zero D Q
    intro x
    rcases binary_eq_zero_or_one (l x) with hx | hx
    · simp [Q, P, functionalPolynomial_eval, hx]
    · simp [Q, P, functionalPolynomial_eval, hx, CharTwo.add_self_eq_zero]
  have hd := (functionalPolynomial_support_and_degree D l).2
  change P.natDegree ≤ Nat.card D / 2 at hd
  have hdeg : Q.natDegree ≤ (subspacePolynomial D).natDegree := by
    rw [subspacePolynomial_natDegree, ← Nat.card_eq_fintype_card]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact natDegree_pow_le.trans (by omega)
    · exact hd.trans (Nat.div_le_self _ _)
  exact ⟨Q.leadingCoeff,
    eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
      (subspacePolynomial_monic D) hdiv hdeg⟩

/-- The Artin--Schreier scalar is fixed by the linear coefficient. This is the
normalized identity used to parametrize Gold's canonical additive polynomials. -/
theorem functionalPolynomial_artinSchreier
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) [Fintype D] (l : D →+ ZMod 2) :
    (functionalPolynomial D l) ^ 2 + functionalPolynomial D l =
      C ((functionalPolynomial D l).coeff 1) *
        (C ((subspacePolynomial D).coeff 1)⁻¹ * subspacePolynomial D) := by
  obtain ⟨θ, hθ⟩ := functionalPolynomial_artinSchreier_scalar D l
  have hc := congrArg (fun P : B[X] ↦ P.coeff 1) hθ
  simp [pow_two, mul_coeff_one, functionalPolynomial_coeff_zero] at hc
  rw [hθ, ← mul_assoc, ← C_mul, hc]
  rw [mul_assoc, mul_inv_cancel₀ (subspacePolynomial_coeff_one_ne_zero D), mul_one]

/-- The zero functional has zero canonical representative. -/
theorem functionalPolynomial_zero
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) : functionalPolynomial D 0 = 0 := by
  symm
  apply eq_functionalPolynomial D 0 0 (by simp)
  intro x
  simp

/-- The fixed canonical polynomials depend additively on the functional. -/
theorem functionalPolynomial_add
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (l k : D →+ ZMod 2) :
    functionalPolynomial D (l + k) = functionalPolynomial D l + functionalPolynomial D k := by
  symm
  apply eq_functionalPolynomial
  · exact (degree_add_le _ _).trans_lt
      (max_lt (functionalPolynomial_degree_lt D l) (functionalPolynomial_degree_lt D k))
  · intro x
    simp [functionalPolynomial_eval]

/-- The canonical representatives remember the original binary functional. -/
theorem functionalPolynomial_injective
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) : Function.Injective (functionalPolynomial D) := by
  intro l k h
  ext x
  apply (algebraMap (ZMod 2) B).injective
  rw [← functionalPolynomial_eval D l x, h, functionalPolynomial_eval]

/-- Vanishing of the linear coefficient forces the canonical polynomial to
vanish, by its Artin--Schreier identity and zero constant term. -/
theorem functionalPolynomial_eq_zero_of_coeff_one_eq_zero
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (l : D →+ ZMod 2)
    (hl : (functionalPolynomial D l).coeff 1 = 0) : functionalPolynomial D l = 0 := by
  classical
  have h := functionalPolynomial_artinSchreier D l
  rw [hl, map_zero, zero_mul] at h
  have hf : functionalPolynomial D l * (functionalPolynomial D l + 1) = 0 := by
    simpa only [mul_add, mul_one, ← pow_two] using h
  rcases mul_eq_zero.mp hf with hz | hz
  · exact hz
  · have hc := congrArg (fun P : B[X] ↦ P.coeff 0) hz
    have hbad : (1 : B) = 0 := by
      simpa only [coeff_add, functionalPolynomial_coeff_zero, coeff_one_zero, zero_add,
        coeff_zero] using hc
    exact (one_ne_zero hbad).elim

end BinaryFieldCounterexamples.Gold
