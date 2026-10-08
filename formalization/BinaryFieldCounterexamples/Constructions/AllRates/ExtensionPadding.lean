/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.AllRates.ExtensionSeed
public import BinaryFieldCounterexamples.Constructions.AllRates.GraphPopulation
public import BinaryFieldCounterexamples.Constructions.AllRates.Padding

/-!
# High-extension all-rate padding

Padding inside the mapped base field preserves the independent-frame
decomposition of the first input.  Projection onto the final frame coordinate
therefore proves exact individual agreement while all distinct nonzero seed
challenges remain exceptional on the prescribed mapped domain.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Finset Polynomial
open AllRatesConstruction
attribute [local instance] Classical.propDecidable Classical.decEq

namespace AllRatesConstruction

/-- Nodal evaluation commutes with an injective field embedding. -/
theorem eval_nodal_mappedDomain
    {B F : Type*} [Field B] [Field F] (φ : B →+* F)
    (W : Finset B) (x : B) :
    (Lagrange.nodal (mappedDomain φ W) id).eval (φ x) =
      φ ((Lagrange.nodal W id).eval x) := by
  rw [Lagrange.eval_nodal, Lagrange.eval_nodal, map_prod]
  simp only [mappedDomain, id_eq]
  rw [Finset.prod_image φ.injective.injOn]
  simp only [map_sub]

/-- The proper-extension finite all-rate pair, with both individual
bounds and all graph-subspace challenges kept after exact padding. -/
theorem exists_all_rate_highExtension_padded_pair
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2] [Algebra B F]
    (D H : AddSubgroup B) (m s J T : ℕ)
    (hs : 2 ≤ s) (hm : s + 1 ≤ m) (hH : Nat.card H = 2 ^ (m + s))
    (hHD : H ≤ D) (hJ : 2 ^ (m - 1) ≤ J) (hJD : J ≤ Nat.card D)
    (hroom : J - 2 ^ (m - 1) + 1 ≤ Nat.card D - Nat.card H)
    (hT : T ≤ J + 2 ^ (m - 1))
    (hcard : Fintype.card B ^ (s + 1) ≤ Fintype.card F) :
    let DF := D.map (algebraMap B F).toAddMonoidHom
    let S := additiveDomain DF
    ∃ f g : S → F,
      agreementEQ S J f J ∧ agreementEQ S J g J ∧
      commonAgreementEQ S J f g J ∧
      2 ^ (m * s) ≤ (nonzeroBadChallenges S J f g T).card := by
  classical
  dsimp only
  let φ : B →+* F := algebraMap B F
  let DF := D.map φ.toAddMonoidHom
  let HF := H.map φ.toAddMonoidHom
  let D0 := additiveDomain D
  let H0 := additiveDomain H
  let S := additiveDomain DF
  have hframecard : Fintype.card B ^ (s + 1) ≤ Fintype.card F := hcard
  obtain ⟨v, hv, hv0⟩ := exists_normalized_independent_frame (B := B) (F := F)
    (s + 1) (by omega) hframecard
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨I, hIcard, hIsize⟩ := exists_binary_graph_subgroup_family H m s hH
  let w := J - 2 ^ (m - 1) + 1
  have hH0D0 : H0 ⊆ D0 := by
    intro x hx
    exact (mem_additiveDomain D x).2 (hHD ((mem_additiveDomain H x).1 hx))
  have hw : w ≤ (D0 \ H0).card := by
    rw [Finset.card_sdiff_of_subset hH0D0, card_additiveDomain, card_additiveDomain]
    exact hroom
  obtain ⟨W, hW, hWcard⟩ := Finset.exists_subset_card_eq hw
  let WF := mappedDomain φ W
  have hWFcard : WF.card = w := by
    simp only [WF]
    rw [card_mappedDomain, hWcard]
  have hSF : mappedDomain φ D0 = S := by
    simp only [D0, S]
    rw [mappedDomain_additiveDomain]
  have hHF : mappedDomain φ H0 = additiveDomain HF := by
    simp only [H0]
    rw [mappedDomain_additiveDomain]
  have hWFS : WF ⊆ S := by
    rw [← hSF]
    exact Finset.image_mono φ (hW.trans Finset.sdiff_subset)
  have hHFS : additiveDomain HF ⊆ S := by
    rw [← hHF, ← hSF]
    exact Finset.image_mono φ hH0D0
  have hdisbase : Disjoint W H0 := by
    exact Finset.disjoint_left.mpr fun x hx hxH ↦ (Finset.mem_sdiff.mp (hW hx)).2 hxH
  have hdis : Disjoint WF (additiveDomain HF) := by
    rw [← hHF]
    exact (Finset.disjoint_image φ.injective).2 hdisbase
  let K := 2 ^ (m - 1) - 1
  let θ := extensionCancellationParameters s v
  let src : F[X] := cancellationSource m s (finiteCancellationParameterExtension s θ)
  let G : F[X] := X ^ K
  have hG : G.Monic := monic_X_pow _
  have hGdeg : G.natDegree = K := natDegree_X_pow _
  have hdim : WF.card + K = J := by
    rw [hWFcard]
    have hp : 0 < (2 : ℕ) ^ (m - 1) := by positivity
    dsimp [w, K]
    omega
  have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ, show m - 1 + 1 = m by omega]
  have hthr : WF.card + (2 ^ m - 1) = J + 2 ^ (m - 1) := by
    rw [hWFcard, hpow]
    dsimp [w]
    have hp : 0 < (2 : ℕ) ^ (m - 1) := by positivity
    omega
  let seedf : additiveDomain HF → F := fun x ↦ src.eval (x : F) +
    v (Fin.last s) * (x : F) ^ K
  let seedg : additiveDomain HF → F := fun x ↦ (x : F) ^ K
  have hseed : 2 ^ (m * s) ≤
      (nonzeroBadChallenges (additiveDomain HF) K seedf seedg (2 ^ m - 1)).card := by
    rw [← hIcard]
    exact highExtension_seed_badChallenges H m s hs hm hH I hIsize v hv hv0
  have hp := nodal_padded_pair_guarantees S (additiveDomain HF) WF hHFS hWFS hdis
    K (2 ^ m - 1) (by
      rw [hdim]
      rw [← hSF, card_mappedDomain]
      simpa only [D0, card_additiveDomain] using hJD)
    (fun x ↦ src.eval x + v (Fin.last s) * x ^ K)
    G hG hGdeg
  dsimp only at hp
  rw [hdim, hthr] at hp
  let Lf : F[X] := Lagrange.nodal WF id
  let f : S → F := fun x ↦ Lf.eval (x : F) *
    (src.eval (x : F) + v (Fin.last s) * (x : F) ^ K)
  let g : S → F := fun x ↦ (Lf * G).eval (x : F)
  have hcommon : commonAgreementEQ S J f g J := by
    simpa only [f, g, Lf, G, eval_mul] using hp.1
  have hfirstLE : agreementLE S J f J := by
    let Lb : B[X] := Lagrange.nodal W id
    let Gb : B[X] := Lb * X ^ K
    have hGbdeg : Gb.natDegree = J := by
      simp only [Gb]
      rw [natDegree_mul Lagrange.nodal_ne_zero (pow_ne_zero _ X_ne_zero),
        Lagrange.natDegree_nodal, natDegree_X_pow, hWcard, ← hWFcard, hdim]
    have hGbne : Gb ≠ 0 := by
      intro he
      rw [he] at hGbdeg
      simp at hGbdeg
      have hp : 0 < (2 : ℕ) ^ (m - 1) := by positivity
      omega
    have hGbdegree : (J : WithBot ℕ) ≤ Gb.degree := by
      rw [degree_eq_natDegree hGbne, hGbdeg]
    have hproj := agreementLE_extensionFrameWordOnMapped s (by omega) v hv hv0
      D0 J
      (fun x : B ↦ Lb.eval x * x ^ (2 ^ (m + s - 1) - 1))
      (fun j x ↦ Lb.eval x * x ^ (2 ^ (m + s - 2 - j.1) - 1))
      Gb hGbdegree
    rw [hSF] at hproj
    have hfun : f = fun x : S ↦ extensionFrameWordOnMapped s v
        (fun y : B ↦ Lb.eval y * y ^ (2 ^ (m + s - 1) - 1))
        (fun j y ↦ Lb.eval y * y ^ (2 ^ (m + s - 2 - j.1) - 1))
        (fun y ↦ Gb.eval y) (x : F) := by
      funext x
      obtain ⟨y, hyD, hy⟩ : ∃ y ∈ D0, φ y = (x : F) := by
        have hx : (x : F) ∈ mappedDomain φ D0 := by
          rw [hSF]
          exact x.property
        exact Finset.mem_image.mp hx
      simp only [f, Lf, src, θ, K, WF]
      rw [← hy]
      rw [extensionFrameWordOnMapped_apply]
      rw [eval_nodal_mappedDomain φ W y]
      rw [cancellationSource_extensionFrameWord m s hs v y]
      unfold extensionFrameWord
      simp only [Lb, Gb, eval_mul, eval_pow, eval_X, map_mul, map_pow,
        map_zero, zero_mul, K, φ]
      rw [mul_add, mul_add, mul_add, Finset.mul_sum]
      ring_nf
    rw [hfun]
    simpa only [hGbdeg] using hproj
  have hsecondLE : agreementLE S J g J := by
    have hnonzero : Lf * G ≠ 0 := mul_ne_zero Lagrange.nodal_ne_zero hG.ne_zero
    have hdeg : (Lf * G).natDegree = J := by
      rw [natDegree_mul Lagrange.nodal_ne_zero hG.ne_zero,
        Lagrange.natDegree_nodal, hGdeg, hdim]
    have hle : (J : WithBot ℕ) ≤ (Lf * G).degree := by
      rw [degree_eq_natDegree hnonzero, hdeg]
    have h := agreementLE_polynomial S J (Lf * G) hle
    simpa only [g, hdeg] using h
  have hfirst : agreementEQ S J f J :=
    ⟨agreementGE_left_of_common S J f g J hcommon.1, hfirstLE⟩
  have hsecond : agreementEQ S J g J :=
    ⟨agreementGE_right_of_common S J f g J hcommon.1, hsecondLE⟩
  refine ⟨f, g, hfirst, hsecond, hcommon, hseed.trans (Finset.card_le_card ?_)⟩
  intro z hz
  rw [nonzeroBadChallenges, Finset.mem_erase] at hz ⊢
  refine ⟨hz.1, ?_⟩
  have hzpad := badChallenges_subset_nodal_padding S (additiveDomain HF) WF
    hHFS hWFS hdis K (2 ^ m - 1)
    (fun x ↦ src.eval x + v (Fin.last s) * x ^ K) (fun x ↦ x ^ K) hz.2
  rw [hdim, hthr] at hzpad
  obtain ⟨P, hP, hagr⟩ := (mem_badChallenges S J _ _ (J + 2 ^ (m - 1)) z).mp hzpad
  apply (mem_badChallenges S J f g T z).mpr
  refine ⟨P, hP, hT.trans ?_⟩
  simpa only [f, g, Lf, G, eval_mul, eval_pow, eval_X] using hagr

end AllRatesConstruction
end BinaryFieldCounterexamples
