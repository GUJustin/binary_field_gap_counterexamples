/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.AffineFlatLocators
public import Mathlib.Data.Set.Card.Arithmetic
/-!
# Variable-size products of affine-flat locators

The shared-coefficient step of Lemma 6.1 (p. 58), Section 6.1, allows different
flat sizes. A product loses at least `w` degrees whenever a nonleading term is
selected. Disjointness identifies the sum of flat sizes with the support size.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A common leading gap survives products with individually varying degrees. -/
theorem natDegree_prod_sub_power_sum_le
    {ι F : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (P : ι → F[X]) (L : ι → ℕ) (w : ℕ)
    (hw : ∀ i ∈ s, w ≤ L i)
    (hdeg : ∀ i ∈ s, (P i).natDegree ≤ L i)
    (htail : ∀ i ∈ s, (P i - X^(L i)).natDegree ≤ L i - w) :
    ((∏ i ∈ s, P i) - X^(∑ i ∈ s, L i)).natDegree ≤ (∑ i ∈ s, L i) - w := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    by_cases hs : s = ∅
    · subst s
      simpa using htail a (by simp)
    have hh := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
      (fun i hi => hdeg i (Finset.mem_insert_of_mem hi))
      (fun i hi => htail i (Finset.mem_insert_of_mem hi))
    have hp : (∏ i ∈ s, P i).natDegree ≤ ∑ i ∈ s, L i :=
      (natDegree_prod_le (s := s) (f := P)).trans
        (Finset.sum_le_sum (fun i hi => hdeg i (Finset.mem_insert_of_mem hi)))
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hwS : w ≤ ∑ i ∈ s, L i := (hw b (Finset.mem_insert_of_mem hb)).trans
      (Finset.single_le_sum (fun i hi => Nat.zero_le _) hb)
    have hwa := hw a (Finset.mem_insert_self a s)
    have hta := htail a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have he : P a * (∏ i ∈ s, P i) - X^(L a + ∑ i ∈ s, L i) =
        (P a - X^(L a)) * (∏ i ∈ s, P i) +
          X^(L a) * ((∏ i ∈ s, P i) - X^(∑ i ∈ s, L i)) := by
      rw [pow_add]
      ring
    rw [he]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by omega)
    · apply natDegree_mul_le.trans
      rw [natDegree_X_pow]
      omega

/-- Any nonempty binary affine flat of size at least `2w` has leading gap `w`.
The integer `w` need not be a power of two. -/
theorem affineFlatLocator_tail_of_two_mul_le
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (A : AffineSubspace (ZMod 2) F) (a : F) (ha : a ∈ A) (w : ℕ)
    (hw : 1 ≤ w) (hsize : 2*w ≤ Nat.card A) :
    (affineFlatLocator A a - X^(Nat.card A)).natDegree ≤ Nat.card A - w := by
  let r := Module.finrank (ZMod 2) A.direction
  have hc : Nat.card A = 2^r := by
    rw [Trees.affineSubspace_card_direction A ⟨a, ha⟩,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]
  have hr : 1 ≤ r := by
    by_contra! hn
    have hz : r = 0 := by omega
    rw [hc, hz] at hsize
    norm_num at hsize
    omega
  have he : r = (r-1)+1 := by omega
  have hd : Nat.card A.direction = 2^((r-1)+1) := by
    rw [←Trees.affineSubspace_card_direction A ⟨a, ha⟩, hc, ←he]
  have ht := affineFlatLocator_tail A a (r-1) hd
  have hp : Nat.card A = 2 * 2^(r-1) := by
    calc
      Nat.card A = 2^((r-1)+1) := by rw [hc, ←he]
      _ = 2 * 2^(r-1) := by rw [pow_succ, Nat.mul_comm]
  rw [←he, ←hc] at ht
  exact ht.trans (by omega)

/-- A disjoint union of nonempty affine flats of arbitrary sizes at least `2w`
has a monic locator of degree its cardinality, and a leading gap of `w`. -/
theorem exists_locator_of_variable_affine_flat_union
    {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (S : Finset F) (A : ι → AffineSubspace (ZMod 2) F) (w : ℕ)
    (hw : 1 ≤ w) (hS : (S : Set F) = ⋃ i, (A i : Set F))
    (hne : ∀ i, (A i : Set F).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (A i : Set F) (A j : Set F)))
    (hsize : ∀ i, 2*w ≤ Nat.card (A i)) :
    ∃ P : F[X], P.Monic ∧ P.natDegree = S.card ∧
      (∀ x, P.eval x = 0 ↔ x ∈ S) ∧
      (P - X^S.card).natDegree ≤ S.card - w := by
  choose a ha using hne
  have hc : S.card = ∑ i, Nat.card (A i) := by
    have he : S = Finset.univ.biUnion (fun i => (A i : Set F).toFinset) := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, Set.mem_toFinset, true_and]
      change x ∈ (S : Set F) ↔ _
      rw [hS, Set.mem_iUnion]
    rw [he, Finset.card_biUnion]
    · simp only [Set.toFinset_card, Nat.card_eq_fintype_card]
      exact Finset.sum_congr rfl (fun i hi => Fintype.card_congr (Equiv.refl _))
    · intro i hi j hj hij
      exact Finset.disjoint_left.mpr (fun x hx hy =>
        Set.disjoint_left.mp (hdis hij) (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy))
  refine ⟨affineFlatUnionLocator Finset.univ A a, ?_, ?_, ?_, ?_⟩
  · exact monic_prod_of_monic _ _ (fun i hi => affineFlatLocator_monic (A i) (a i))
  · rw [affineFlatUnionLocator, natDegree_prod_of_monic _ (f := fun i => affineFlatLocator (A i) (a i))
        (fun i hi => affineFlatLocator_monic (A i) (a i))]
    simp_rw [affineFlatLocator_natDegree,
      ←Trees.affineSubspace_card_direction _ ⟨a _, ha _⟩]
    exact hc.symm
  · intro x
    rw [affineFlatUnionLocator_eval_eq_zero_iff _ _ _ (fun i hi => ha i)]
    change (∃ i ∈ Finset.univ, x ∈ A i) ↔ x ∈ (S : Set F)
    rw [hS, Set.mem_iUnion]
    simp
  · rw [hc]
    apply natDegree_prod_sub_power_sum_le Finset.univ
      (fun i => affineFlatLocator (A i) (a i)) (fun i => Nat.card (A i)) w
    · intro i hi
      have := hsize i
      omega
    · intro i hi
      rw [affineFlatLocator_natDegree, ←Trees.affineSubspace_card_direction _ ⟨a i, ha i⟩]
    · intro i hi
      exact affineFlatLocator_tail_of_two_mul_le (A i) (a i) (ha i) w hw (hsize i)
end BinaryFieldCounterexamples
