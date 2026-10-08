/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.CollisionPairs
public import BinaryFieldCounterexamples.Agreement.Projection
/-!
# Exterior collision bounds from actual support incidence

Double counting unordered support pairs identifies the sum of intersection sizes
with the sum of binomial incidence counts. A polynomial difference must spend one
root at every known intersection point, leaving only the remaining degree for
collisions outside the evaluation domain. The final natural-number inequality
keeps the incidence correction without truncated rational arithmetic.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators

theorem sum_pair_intersection_card_eq_incidence_choose_two
    {ι X : Type*} [LinearOrder ι] [DecidableEq X]
    (I : Finset ι) (D : Finset X) (S : ι → Finset X) (hS : ∀ i ∈ I, S i ⊆ D) :
    (∑ ij ∈ (I ×ˢ I).filter (fun ij => ij.1 < ij.2), (S ij.1 ∩ S ij.2).card) =
      ∑ x ∈ D, ((I.filter fun i => x ∈ S i).card).choose 2 := by
  let pairs := (I ×ˢ I).filter (fun ij => ij.1 < ij.2)
  have he (ij : ι × ι) (hij : ij ∈ pairs) :
      S ij.1 ∩ S ij.2 = D.filter (fun x => x ∈ S ij.1 ∧ x ∈ S ij.2) := by
    have hi : ij.1 ∈ I := (Finset.mem_product.mp (Finset.mem_filter.mp hij).1).1
    ext x
    simp only [Finset.mem_inter,Finset.mem_filter]
    exact ⟨fun h => ⟨hS ij.1 hi h.1,h⟩,fun h => h.2⟩
  rw [show (∑ ij ∈ (I ×ˢ I).filter (fun ij => ij.1 < ij.2), (S ij.1 ∩ S ij.2).card) =
    ∑ ij ∈ pairs, (D.filter (fun x => x ∈ S ij.1 ∧ x ∈ S ij.2)).card from
      Finset.sum_congr rfl (fun ij hij => congrArg Finset.card (he ij hij))]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hp : pairs.filter (fun ij => x ∈ S ij.1 ∧ x ∈ S ij.2) =
      ((I.filter fun i => x ∈ S i) ×ˢ (I.filter fun i => x ∈ S i)).filter (fun ij => ij.1 < ij.2) := by
    ext ij
    simp only [pairs,Finset.mem_filter,Finset.mem_product]
    tauto
  rw [←Finset.card_filter,hp,Finset.card_product_filter_lt,Finset.card_filter]
theorem exterior_root_count_add_known_roots_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (D S : Finset F) (hSD : S ⊆ D)
    (P : Polynomial F) (hP : P ≠ 0) (hS : ∀ x ∈ S, P.eval x=0) :
    ((Finset.univ \ D).filter (fun x => P.eval x=0)).card+S.card≤P.natDegree := by
  let R := (Finset.univ \ D).filter (fun x => P.eval x=0)
  have hdis : Disjoint R S := by
    apply Finset.disjoint_left.mpr
    intro x hx hxs
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2 (hSD hxs)
  rw [←Finset.card_union_of_disjoint hdis]
  apply (Finset.card_le_card (show R ∪ S ⊆ Finset.univ.filter (fun x => P.eval x=0) from ?_)).trans
    (card_filter_eval_eq_zero_le Finset.univ P hP)
  intro x hx
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (Finset.mem_filter.mp hx).2
  · exact hS x hx
theorem sum_exterior_collisions_add_incidence_le
    {ι F : Type*} [LinearOrder ι] [Field F] [Fintype F] [DecidableEq F]
    (I : Finset ι) (D : Finset F) (S : ι → Finset F) (P : ι → Polynomial F) (K : ℕ)
    (hS : ∀ i ∈ I, S i ⊆ D) (hroot : ∀ i ∈ I, ∀ x ∈ S i, (P i).eval x=0)
    (hinj : Set.InjOn P I)
    (hdeg : ∀ i ∈ I, ∀ j ∈ I, i≠j → (P i-P j).natDegree≤K) :
    (∑ β ∈ Finset.univ \ D, unorderedCollisionCount I (fun i => (P i).eval β)) +
      (∑ x ∈ D, ((I.filter fun i => x ∈ S i).card).choose 2) ≤ K*I.card.choose 2 := by
  let pairs := (I ×ˢ I).filter (fun ij => ij.1 < ij.2)
  have htotal : (∑ β ∈ Finset.univ \ D, unorderedCollisionCount I (fun i => (P i).eval β)) =
      ∑ ij ∈ pairs, ((Finset.univ \ D).filter (fun β => (P ij.1).eval β=(P ij.2).eval β)).card := by
    calc
      _ = ∑ β ∈ Finset.univ \ D, (pairs.filter (fun ij => (P ij.1).eval β=(P ij.2).eval β)).card := by
        apply Finset.sum_congr rfl
        intro β hβ
        rw [unorderedCollisionCount_eq_card_pairCollisions]
        congr 1
        ext ij
        simp only [pairs,Finset.mem_filter]
        tauto
      _ = _ := by simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
  rw [htotal,←sum_pair_intersection_card_eq_incidence_choose_two I D S hS]
  have he : (∑ ij ∈ pairs, ((Finset.univ \ D).filter (fun β => (P ij.1).eval β=(P ij.2).eval β)).card) +
      (∑ ij ∈ pairs, (S ij.1 ∩ S ij.2).card) ≤ ∑ _ij ∈ pairs, K := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ij hij
    obtain ⟨hijI,hlt⟩ := Finset.mem_filter.mp hij
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hijI
    have hn : P ij.1-P ij.2≠0 := sub_ne_zero.mpr (fun h => (ne_of_lt hlt) (hinj hi hj h))
    have hb := exterior_root_count_add_known_roots_le D (S ij.1 ∩ S ij.2)
      (fun x hx => hS ij.1 hi (Finset.mem_inter.mp hx).1) (P ij.1-P ij.2) hn
      (fun x hx => by rw [Polynomial.eval_sub,hroot ij.1 hi x (Finset.mem_inter.mp hx).1,
        hroot ij.2 hj x (Finset.mem_inter.mp hx).2,sub_self])
    simp only [Polynomial.eval_sub,sub_eq_zero] at hb
    exact hb.trans (hdeg ij.1 hi ij.2 hj (ne_of_lt hlt))
  simpa only [pairs,Finset.sum_const,Finset.card_product_filter_lt,smul_eq_mul,mul_comm] using he
end BinaryFieldCounterexamples
