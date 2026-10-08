/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Agreement.Interpolation
public import BinaryFieldCounterexamples.Agreement.OrdinaryListTransfer
public import BinaryFieldCounterexamples.Constructions.PaddedPoleAssembly

/-!
# Arbitrary padding for the all-rate construction

The nodal polynomial of a disjoint padding set adds every padding point to each
witness's agreement set and raises the strict degree budget by its cardinality.
A polynomial direction of exactly the message degree gives exact common
agreement by root counting and interpolation. Every old challenge, including
zero, and the full decoding-list count are preserved by this construction.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq

theorem agreementGE_nodal_padding
    {F : Type*} [Field F] (D H W : Finset F)
    (hH : H ⊆ D) (hW : W ⊆ D) (hdis : Disjoint W H)
    (K T : ℕ) (f : F → F) (P : F[X])
    (hP : P.degree < K)
    (hagr : T ≤ agreementCount H (fun x => f x) P) :
    agreementGE D (W.card+K)
      (fun x => (Lagrange.nodal W id).eval (x:F)*f x) (W.card+T) := by
  let L : F[X] := Lagrange.nodal W id
  have hL : L.natDegree=W.card := by simp [L,Lagrange.nodal]
  refine ⟨L*P,?_,?_⟩
  · by_cases hz : P=0
    · simp [hz]
    · have hp := (natDegree_lt_iff_degree_lt hz).mpr hP
      exact (degree_le_of_natDegree_le (natDegree_mul_le.trans
        (Nat.add_le_add hL.le (le_refl _)))).trans_lt (by exact_mod_cast Nat.add_lt_add_left hp W.card)
  · change W.card+T ≤ agreementCount D (fun x => L.eval (x:F)*f x) (L*P)
    rw [agreementCount_eq_card_filter H f P] at hagr
    rw [agreementCount_eq_card_filter D (fun x => L.eval x*f x) (L*P)]
    let A := H.filter fun x => P.eval x=f x
    have hdA : Disjoint W A := hdis.mono_right (Finset.filter_subset _ _)
    have hsub : W ∪ A ⊆ D.filter
        (fun x => (L*P).eval x=L.eval x*f x) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · apply Finset.mem_filter.mpr ⟨hW hx,?_⟩
        have hz : L.eval x=0 := (eval_nodal_id_eq_zero_iff W x).2 hx
        simp only [eval_mul,hz,zero_mul]
      · obtain ⟨hxH,hxP⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hH hxH,by simp only [eval_mul,hxP]⟩
    calc
      W.card+T ≤ W.card+A.card := Nat.add_le_add_left hagr _
      _ = (W ∪ A).card := (Finset.card_union_of_disjoint hdA).symm
      _ ≤ _ := Finset.card_le_card hsub

theorem badChallenges_subset_nodal_padding
    {F : Type*} [Field F] [Fintype F] (D H W : Finset F)
    (hH : H ⊆ D) (hW : W ⊆ D) (hdis : Disjoint W H)
    (K T : ℕ) (f g : F → F) :
    badChallenges H K (fun x => f x) (fun x => g x) T ⊆
      badChallenges D (W.card+K)
        (fun x => (Lagrange.nodal W id).eval (x:F)*f x)
        (fun x => (Lagrange.nodal W id).eval (x:F)*g x) (W.card+T) := by
  intro z hz
  obtain ⟨P,hP,hagr⟩ := (mem_badChallenges H K _ _ T z).mp hz
  apply (mem_badChallenges D (W.card+K) _ _ (W.card+T) z).mpr
  have hp := agreementGE_nodal_padding D H W hH hW hdis K T
    (fun x => f x+z*g x) P hP hagr
  convert hp using 1
  funext x
  ring

theorem commonAgreementEQ_polynomial_right
    {F : Type*} [Field F] (D : Finset F) (K : ℕ) (hK : K ≤ D.card)
    (f : D → F) (G : F[X]) (hG : G≠0) (hd : G.natDegree=K) :
    commonAgreementEQ D K f (fun x => G.eval (x:F)) K := by
  refine ⟨commonAgreementGE_of_le_card D K f _ hK,?_⟩
  apply commonAgreementLE_of_right
  have hp := agreementLE_polynomial D K G (by rw [degree_eq_natDegree hG,hd])
  simpa only [hd] using hp

theorem nodal_padded_pair_guarantees
    {F : Type*} [Field F] [Fintype F] (D H W : Finset F)
    (hH : H ⊆ D) (hW : W ⊆ D) (hdis : Disjoint W H)
    (K T : ℕ) (hK : W.card+K ≤ D.card) (f : F → F)
    (G : F[X]) (hG : G.Monic) (hd : G.natDegree=K) :
    let L := Lagrange.nodal W id
    let f' : D → F := fun x => L.eval (x:F)*f x
    let g' : D → F := fun x => (L*G).eval (x:F)
    commonAgreementEQ D (W.card+K) f' g' (W.card+K) ∧
      (badChallenges H K (fun x => f x) (fun x => G.eval (x:F)) T).card ≤
        (badChallenges D (W.card+K) f' g' (W.card+T)).card ∧
      ordinaryList D (W.card+K+1) (W.card+T)
        (badChallenges D (W.card+K) f' g' (W.card+T)).card := by
  dsimp only
  have hm : ((Lagrange.nodal W id)*G).Monic := Lagrange.nodal_monic.mul hG
  have hdeg : ((Lagrange.nodal W id)*G).natDegree=W.card+K := by
    rw [natDegree_mul Lagrange.nodal_ne_zero hG.ne_zero,Lagrange.natDegree_nodal,hd]
  refine ⟨commonAgreementEQ_polynomial_right D _ hK _ _ hm.ne_zero hdeg,?_,?_⟩
  · apply Finset.card_le_card
    simpa only [eval_mul] using
      badChallenges_subset_nodal_padding D H W hH hW hdis K T f (fun x => G.eval x)
  · exact ordinaryList_of_badChallenges_polynomial_direction D _ _ _ _ hm hdeg

end BinaryFieldCounterexamples
