/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.GoldCounting
public import BinaryFieldCounterexamples.Constructions.Gold.FullSource
/-!
# Main theorem: Gold counting for the manuscript's full received word

This companion to Theorem 5.1, p. 36, fixes the decoding-list word explicitly
as the full square root of `L_D-lambda_0 X`, transported to each affine domain.
The previous list theorem uses only its top two terms. The explaining degree
is exactly half the root count for the full source too.

The received-pair proof already uses the full canonical numerator at the
selected exterior pole; its sharp count and individual/common agreement
contracts therefore require no change. The second theorem assembles that pair
with the explicitly fixed full-source list on the same prescribed domain.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
/-- Theorem 5.1's list for exactly the full word `R|_(D+a)` used by the paper,
with at least the printed Gaussian population of distinct strict-degree
explaining polynomials. -/
theorem gold_counting_list_fullSource
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) [Fintype D] (a : B) (m d t : ℕ)
    (hB : Fintype.card B=2^m) (hD : (additiveDomain D).card=2^d)
    (ht : 2≤t) (htd : t≤d/2)
    (hΔ : 1≤m-t*(m-d+if Even d then 1 else 0)) :
    let N : ℕ := 2^d
    let Δ : ℕ := m-t*(m-d+if Even d then 1 else 0)
    let L : ℕ := 2^(2*t)*(2^Δ-1)*gaussianBinomial 4 (d/2) t
    let T : ℕ := N/2-N/2^(t+1)
    let E := affineDomain (additiveDomain D) a
    ∃ ps : Finset B[X], L≤ps.card ∧
      ∀ p ∈ ps, p.degree<(N/4:ℕ) ∧
        T≤agreementCount E (fun x ↦ (Gold.goldFullSourcePolynomial D).eval ((x:B)-a)) p := by
  classical
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  dsimp only
  have hDN : Nat.card D=2^d := by rwa [card_additiveDomain] at hD
  obtain ⟨e⟩ := Gold.exists_gold_basis D d hDN
  have hdt : 2*t≤d := by omega
  have hd : d-1+1=d := by omega
  have hDN' : Nat.card D=2^(d-1+1) := by simpa only [hd] using hDN
  obtain ⟨ps,hcard,hps⟩ := Gold.exists_repairedLocator_family D (d-1) hDN' (Gold.basisParameter D e) e
    (Gold.basisParameter_eval D e) t ht (by omega)
  let p : ps → B[X] := fun z ↦ (z.val+Gold.goldFullSourcePolynomial D).comp (X-C a)
  have hp : Function.Injective p := by
    intro i j h
    have he := congrArg (fun Q : B[X] ↦ Q.comp (X+C a)) h
    simp only [p,comp_assoc] at he
    have hc : (X-C a).comp (X+C a)=(X : B[X]) := by simp
    rw [hc,comp_X,comp_X] at he
    exact Subtype.ext (add_right_cancel he)
  have hK : 2^d/4=2^(d-1-1) := by
    change 2^d/2^2=2^(d-1-1)
    rw [Nat.pow_div (by omega : 2≤d) (by decide : 0<2)]
    congr 1
  have hN : 2^d/2=2^(d-1) := by
    change 2^d/2^1=2^(d-1)
    rw [Nat.pow_div (by omega : 1≤d) (by decide : 0<2)]
  have hT : 2^d/2^(t+1)=2^(d-1-t) := by
    rw [Nat.pow_div (by omega : t+1≤d) (by decide : 0<2)]
    congr 1
    omega
  refine ⟨Finset.univ.image p,?_,?_⟩
  · rw [Finset.card_image_iff.mpr hp.injOn,Finset.card_univ,Fintype.card_coe,hcard]
    have hpopulation := Gold.card_momentTensors_lower_bound D m d t hB hDN e (by omega) hdt hΔ
    calc
      _ = ((2^(m-t*(m-d+if Even d then 1 else 0))-1)*gaussianBinomial 4 (d/2) t)*2^(2*t) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hpopulation
  · intro q hq
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨A,hA,l,κ,he,hzero⟩ := hps z.val z.property
    obtain ⟨hr,hM⟩ := (Gold.mem_momentTensors D (Gold.basisParameter D e) t A).mp hA
    have htail := Gold.repairedLocator_fullSource_natDegree D (d-1) hDN' (Gold.basisParameter D e)
      A l κ t ht (by omega) hM hr hzero
    have hroots := (Gold.repairedLocator_properties D (d-1) hDN' (Gold.basisParameter D e)
      A l κ t ht (by omega) hM hr hzero).2.2.2.1
    constructor
    · change ((z.val+Gold.goldFullSourcePolynomial D).comp (X-C a)).degree<(2^d/4:ℕ)
      rw [degree_comp (by simp),degree_X_sub_C,mul_one,hK]
      apply degree_le_natDegree.trans_lt
      rw [he,htail]
      exact_mod_cast Nat.sub_lt (by positivity : 0<(2:ℕ)^(d-1-1))
        (by positivity : 0<(2:ℕ)^(d-1-t-1))
    · rw [agreementCount_affineDomain (additiveDomain D) a
        (fun x : B ↦ (Gold.goldFullSourcePolynomial D).eval x)]
      have hc : (p z).comp (X+C a)=z.val+Gold.goldFullSourcePolynomial D := by simp [p,comp_assoc]
      rw [hc,Gold.agreementCount_add_source_eq_roots,he,hroots,hN,hT]
/-- The complete Theorem 5.1 for the explicit full-source word and the original
sharp received pair, with unchanged quantitative constants, strict witness
dimension, individual and common agreement, and every affine translate. -/
theorem gold_counting_sharp_fullSource
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B) (m d t : ℕ)
    (hB : Fintype.card B=2^m) (hD : (additiveDomain D).card=2^d)
    (ht : 2≤t) (htd : t≤d/2)
    (hΔ : 1≤m-t*(m-d+if Even d then 1 else 0)) (hq : 2^d<Fintype.card F) :
    let N : ℕ := 2^d
    let Δ : ℕ := m-t*(m-d+if Even d then 1 else 0)
    let L : ℕ := 2^(2*t)*(2^Δ-1)*gaussianBinomial 4 (d/2) t
    let T : ℕ := N/2-N/2^(t+1)
    let δ : ℕ := N/2^(2*t)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    let q : ℕ := Fintype.card F
    let Z : ℕ := max (L-(δ*L.choose 2)/(q-N))
      ⌈(L:ℚ)*((q:ℚ)-(N:ℚ))/((q:ℚ)-(N:ℚ)+(δ:ℚ)*((L:ℚ)-1))⌉₊
    (∃ ps : Finset B[X], L≤ps.card ∧ ∀ p ∈ ps, p.degree<(N/4:ℕ) ∧
      T≤agreementCount (affineDomain (additiveDomain D) a)
        (fun x ↦ (Gold.goldFullSourcePolynomial D).eval ((x:B)-a)) p) ∧
    ∃ f g : E → F, commonAgreementEQ E (N/4) f g (N/4) ∧
      agreementEQ E (N/4) g (N/4) ∧ agreementLE E (N/4) f (3*N/8-1) ∧
      Z≤(nonzeroBadChallenges E (N/4) f g T).card ∧
      Z≤(nonzeroBadChallenges E (T/2) f g T).card := by
  exact ⟨gold_counting_list_fullSource D a m d t hB hD ht htd hΔ,
    gold_counting_sharp φ D a m d t hB hD ht htd hΔ hq⟩
end BinaryFieldCounterexamples
