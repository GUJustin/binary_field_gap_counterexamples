/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.PaddedPoleAssembly
public import BinaryFieldCounterexamples.Counting.AffineLabelPooling

/-!
# Disjoint padding and exterior pole transfer

A finite polynomial family with a common high-degree head supplies one received
pair on an arbitrary larger evaluation domain. Disjoint nodal padding raises
the agreement threshold, while adjoining the zero correction to the collision
count ensures that every selected challenge is both distinct and nonzero.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Longfellow

open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A field larger than the domain plus the pairwise root budget has an exterior
point where all polynomial labels are distinct and nonzero. -/
theorem exists_exterior_polynomial_labels_injective
    {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (Q : Finset F[X]) (K : ℕ)
    (hzero : ∀ p ∈ Q, p ≠ 0)
    (hdegree : ∀ p ∈ Q, p.natDegree ≤ K)
    (hq : D.card + K * (Q.card.choose 2 + Q.card) < Fintype.card F) :
    ∃ β ∉ D, Set.InjOn (fun p : F[X] => p.eval β) Q ∧
      ∀ p ∈ Q, p.eval β ≠ 0 := by
  let J := insert (0 : F[X]) Q
  let I : Finset J := Finset.univ
  let E := Finset.univ \ D
  let : LinearOrder J := (Finset.equivFin J).linearOrder
  have hz : (0 : F[X]) ∉ Q := by
    intro h
    exact hzero 0 h rfl
  have hJcard : I.card = Q.card + 1 := by
    simp only [I, Finset.card_univ, Fintype.card_coe]
    exact Finset.card_insert_of_notMem hz
  have hEcard : E.card = Fintype.card F - D.card := by
    simp [E, Finset.card_sdiff]
  have hbudget : I.card.choose 2 * K < E.card := by
    rw [hJcard, show (Q.card + 1).choose 2 = Q.card + Q.card.choose 2 from
      by simpa using Nat.choose_succ_succ Q.card 1, Nat.add_comm Q.card]
    rw [hEcard]
    rw [Nat.mul_comm]
    omega
  have hE : E.Nonempty := Finset.card_pos.mp (by omega)
  have hd (p : J) : (p : F[X]).natDegree ≤ K := by
    rcases Finset.mem_insert.mp p.property with hp | hp
    · simp [hp]
    · exact hdegree p hp
  have hpair : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      (E.filter fun β => (i : F[X]).eval β = (j : F[X]).eval β).card ≤ K := by
    intro i hi j hj hij
    have hn : (i : F[X]) - (j : F[X]) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hij (Subtype.ext h))
    have hb := card_filter_eval_eq_zero_le E ((i : F[X]) - (j : F[X])) hn
    simp only [eval_sub, sub_eq_zero] at hb
    exact hb.trans (natDegree_sub_le _ _ |>.trans (max_le (hd i) (hd j)))
  have htotal := sum_unorderedCollisionCount_le_choose_two_mul E I
    (fun β p => (p : F[X]).eval β) K hpair
  obtain ⟨β, hβ, himage, _⟩ := exists_parameter_image_card_bounds E I
    (fun β p => (p : F[X]).eval β) (I.card.choose 2 * K) hE htotal
  have hdiv : I.card.choose 2 * K / E.card = 0 := Nat.div_eq_of_lt hbudget
  rw [hdiv, Nat.sub_zero] at himage
  have hinj : Set.InjOn (fun p : J => (p : F[X]).eval β) I :=
    Finset.card_image_iff.mp (Nat.le_antisymm (Finset.card_image_le) himage)
  have hi : Function.Injective (fun p : J => (p : F[X]).eval β) := by
    intro p q he
    exact hinj (Finset.mem_univ _) (Finset.mem_univ _) he
  refine ⟨β, (Finset.mem_sdiff.mp hβ).2, ?_, ?_⟩
  · intro p hp q hq he
    exact congrArg Subtype.val (hi (a₁ := ⟨p, Finset.mem_insert_of_mem hp⟩)
      (a₂ := ⟨q, Finset.mem_insert_of_mem hq⟩) he)
  · intro p hp he
    have hh := hi (a₁ := ⟨p, Finset.mem_insert_of_mem hp⟩)
      (a₂ := ⟨0, Finset.mem_insert_self _ _⟩) (by simpa using he)
    exact hzero p hp (congrArg Subtype.val hh)

/-- Select `L` locators, pad outside `U`, and choose one exterior pole. The same
pair has common agreement exactly `K` and at least `L` distinct nonzero
exceptional challenges at threshold `K-k0+T`. -/
theorem exists_padded_pole_pair_of_polynomial_family
    {F : Type*} [Field F] [Fintype F]
    (S U : Finset F) (ps : Finset F[X]) (R : F[X]) (k0 K T L : ℕ)
    (hUS : U ⊆ S) (hk0 : 0 < k0) (hk : k0 ≤ K) (hK : K ≤ S.card)
    (hpad : K-k0 ≤ (S \ U).card) (hL : L ≤ ps.card)
    (hdegree : ∀ p ∈ ps, (p-R).natDegree = k0)
    (hroots : ∀ p ∈ ps, T ≤ (U.filter fun x => p.eval x = 0).card)
    (hq : S.card + K * (L.choose 2 + L) < Fintype.card F) :
    ∃ f g : S → F, commonAgreementEQ S K f g K ∧
      agreementEQ S K g K ∧
      L ≤ (nonzeroBadChallenges S K f g (K-k0+T)).card := by
  obtain ⟨P, hPps, hPcard⟩ := Finset.exists_subset_card_eq hL
  obtain ⟨W, hW, hWcard⟩ := Finset.exists_subset_card_eq hpad
  let A : F[X] := Lagrange.nodal W id
  let Q := P.image (fun p => A*(p-R))
  have hA : A ≠ 0 := Lagrange.nodal_ne_zero
  have hAd : A.natDegree = K-k0 := by simp [A, Lagrange.natDegree_nodal, hWcard]
  have hnonzero (p) (hp : p ∈ P) : p-R ≠ 0 := by
    intro hz
    have hd := hdegree p (hPps hp)
    rw [hz, natDegree_zero] at hd
    omega
  have hinj : Set.InjOn (fun p : F[X] => A*(p-R)) P := by
    intro p hp q hq he
    have hh := mul_left_cancel₀ hA he
    exact sub_left_injective hh
  have hQcard : Q.card = L := by
    rw [Finset.card_image_of_injOn hinj, hPcard]
  have hQzero : ∀ C ∈ Q, C ≠ 0 := by
    intro C hC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    exact mul_ne_zero hA (hnonzero p hp)
  have hQdeg : ∀ C ∈ Q, C.natDegree ≤ K := by
    intro C hC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    rw [natDegree_mul hA (hnonzero p hp), hAd, hdegree p (hPps hp)]
    omega
  obtain ⟨β, hβ, hlabels, hlabels0⟩ := exists_exterior_polynomial_labels_injective
    S Q K hQzero hQdeg (by simpa only [hQcard] using hq)
  let f : S → F := fun x => (A*R).eval (x:F) * ((x:F)-β)⁻¹
  let g : S → F := fun x => ((x:F)-β)⁻¹
  refine ⟨f, g, commonAgreementEQ_reciprocal_right S β hβ K hK f,
    agreementEQ_reciprocal S β hβ K hK, ?_⟩
  have himage : (Q.image fun C => C.eval β).card = L := by
    rw [Finset.card_image_of_injOn hlabels, hQcard]
  rw [← himage]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
  apply Finset.mem_erase.mpr
  refine ⟨hlabels0 _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩), ?_⟩
  apply poleReduction_badChallenge S β hβ (A*R) (A*(p-R)) K (K-k0+T)
    (degree_le_of_natDegree_le (hQdeg _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
  have he : A*R + A*(p-R) = A*p := by ring
  rw [he]
  let V := U.filter fun x => p.eval x = 0
  have hdis : Disjoint W V := by
    apply Finset.disjoint_left.mpr
    intro x hx hv
    exact (Finset.mem_sdiff.mp (hW hx)).2 (Finset.mem_filter.mp hv).1
  have hsub : W ∪ V ⊆ S.filter fun x => (A*p).eval x = 0 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · refine Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hW hx)).1, ?_⟩
      have hz : A.eval x = 0 := (eval_nodal_id_eq_zero_iff W x).mpr hx
      simp [eval_mul, hz]
    · obtain ⟨hxU, hz⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hUS hxU, by simp [eval_mul, hz]⟩
  calc
    K-k0+T ≤ W.card+V.card := by
      rw [hWcard]
      exact Nat.add_le_add_left (hroots p (hPps hp)) _
    _ = (W ∪ V).card := (Finset.card_union_of_disjoint hdis).symm
    _ ≤ _ := Finset.card_le_card hsub

end BinaryFieldCounterexamples.Longfellow
