/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.AllRates.FiniteSeed
public import BinaryFieldCounterexamples.Constructions.AllRates.GraphPopulation
public import BinaryFieldCounterexamples.Constructions.AllRates.Padding
public import BinaryFieldCounterexamples.Constructions.AllRates.PinnedListTransfer
/-!
# Complete finite pairs for Theorem 4.5

The concrete graph population and affine-parameter pooling supply the seed pair.
An actual subset outside its prescribed seed domain pads this pair to the exact
requested message length. The theorem keeps the rational ceiling, every
challenge including zero, exact common agreement, and the full decoding list.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open AllRatesConstruction
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 4.5 parts 1–2 and closing list clause on a finite padded domain: exact second-input agreement and lists pinned to the first input. -/
theorem exists_all_rate_finite_padded_pair_full
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : Finset F) (H : AddSubgroup F) (m s J T : ℕ)
    (hs : 2≤s) (hm : s+1≤m) (hH : Nat.card H=2^(m+s))
    (hHD : additiveDomain H ⊆ D) (hJ : 2^(m-1)≤J) (hJD : J≤D.card)
    (hroom : J-2^(m-1)+1≤D.card-(additiveDomain H).card)
    (hT : T≤J+2^(m-1)) :
    ∃ f g : D → F, agreementEQ D J g J ∧ commonAgreementEQ D J f g J ∧
      ⌈((Fintype.card F*2^(m*s):ℕ):ℚ)/(Fintype.card F+2^(m*s)-1:ℕ)⌉₊ ≤
        (badChallenges D J f g T).card ∧
      (∃ ps : Finset F[X], (badChallenges D J f g T).card = ps.card ∧
        ∀ p ∈ ps, p.degree < J+1 ∧ T ≤ agreementCount D f p) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨I,hI,hsize⟩ := exists_binary_graph_subgroup_family H m s hH
  obtain ⟨θ,hθ⟩ := exists_finite_seed_parameter_direction_dimension H m s hs (by omega) hH I hsize
  rw [hI] at hθ
  let w := J-2^(m-1)+1
  have hw : w≤(D\additiveDomain H).card := by
    rw [Finset.card_sdiff_of_subset hHD]
    exact hroom
  obtain ⟨W,hW,hWcard⟩ := Finset.exists_subset_card_eq hw
  have hWD : W⊆D := hW.trans Finset.sdiff_subset
  have hdis : Disjoint W (additiveDomain H) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxH
    exact (Finset.mem_sdiff.mp (hW hx)).2 hxH
  let K := 2^(m-1)-1
  let src := cancellationSource m s (finiteCancellationParameterExtension s θ)
  let G : F[X] := X^K
  have hG : G.Monic := monic_X_pow _
  have hdeg : G.natDegree=K := natDegree_X_pow _
  have hdim : W.card+K=J := by
    rw [hWcard]
    have hpos : 0<(2:ℕ)^(m-1) := by positivity
    dsimp [w,K]
    omega
  have hpow : 2^m=2^(m-1)*2 := by rw [←pow_succ,show m-1+1=m by omega]
  have hthr : W.card+(2^m-1)=J+2^(m-1) := by
    rw [hWcard,hpow]
    dsimp [w]
    have hpos : 0<(2:ℕ)^(m-1) := by positivity
    omega
  have hp := nodal_padded_pair_guarantees D (additiveDomain H) W hHD hWD hdis K (2^m-1)
    (by rw [hdim]; exact hJD) (fun x => src.eval x) G hG hdeg
  dsimp only at hp
  rw [hdim,hthr] at hp
  have hGfull : (Lagrange.nodal W id * G).Monic := Lagrange.nodal_monic.mul hG
  have hGfulldeg : (Lagrange.nodal W id * G).natDegree = J := by
    rw [natDegree_mul Lagrange.nodal_ne_zero hG.ne_zero, Lagrange.natDegree_nodal, hdeg, hdim]
  refine ⟨_,_,⟨agreementGE_right_of_common D J _ _ J hp.1.1, ?_⟩,hp.1,?_,?_⟩
  · have hb := agreementLE_polynomial D J (Lagrange.nodal W id * G)
      (by rw [degree_eq_natDegree hGfull.ne_zero, hGfulldeg])
    simpa only [hGfulldeg] using hb
  · apply le_trans hθ
    have hc := hp.2.1
    simp only [G,eval_pow,eval_X,K,src] at hc
    apply hc.trans
    apply Finset.card_le_card
    intro z hz
    obtain ⟨P,hP,hagr⟩ := (mem_badChallenges D J _ _ (J+2^(m-1)) z).mp hz
    exact (mem_badChallenges D J _ _ T z).mpr ⟨P,hP,hT.trans hagr⟩
  · apply decodingList_of_badChallenges_polynomial_direction_at_input
    · exact Lagrange.nodal_monic.mul hG
    · rw [natDegree_mul Lagrange.nodal_ne_zero hG.ne_zero,Lagrange.natDegree_nodal,hdeg,hdim]
end BinaryFieldCounterexamples
