/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.GoldCounting
public import BinaryFieldCounterexamples.Constructions.Gold.FiniteExtensions
public import BinaryFieldCounterexamples.Constructions.Gold.DenseBounds
public import BinaryFieldCounterexamples.Constructions.Gold.EnergyLowerBound
/-!
# Finite assembly for the dense Gold regime
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A rounded extension degree realizes the Gold list and received-pair
construction with explicit count and normalized-count lower bounds. -/
theorem denseGold_finite
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) (c d t : ℕ)
    (hB : Fintype.card B=2^(d+c)) (hD : (additiveDomain D).card=2^d)
    (ht2 : 2≤t) (htd : t≤d/2)
    (hΔ : 1≤d+c-t*(c+if Even d then 1 else 0))
    (hell : d+c≤denseGoldExponent c d t)
    (hqexp : d+1≤denseGoldExponent c d t-(d+c))
    (h8exp : 3+(d-2*t)≤(d+c)*denseGoldExtensionDegree c d t) :
    let N : ℕ := 2^d
    let L : ℕ := 2^(2*t)*(2^(d+c-t*(c+if Even d then 1 else 0))-1)*
      gaussianBinomial 4 (d/2) t
    let T : ℕ := N/2-N/2^(t+1)
    let δ : ℕ := N/2^(2*t)
    ordinaryList (additiveDomain D) (N/4) T L ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
    letI := fieldF
    letI := finiteF
    ∃ φ : B →+* F,
      let D' := mappedDomain φ (additiveDomain D)
      let q : ℕ := Fintype.card F
      Fintype.card F=(2^(d+c))^(denseGoldExtensionDegree c d t) ∧
      ∃ f g : D' → F,
        commonAgreementEQ D' (N/4) f g (N/4) ∧
        ((q:ℚ)/(4*δ)-1 ≤ ((nonzeroBadChallenges D' (N/4) f g T).card:ℚ)) ∧
        ((1:ℚ)/(8*δ) ≤
          ((nonzeroBadChallenges D' (N/4) f g T).card:ℚ)/(q:ℚ)) := by
  classical
  dsimp only
  have hdt : 2*t≤d := by omega
  have hm : 0<d+c := by omega
  have her : 1≤denseGoldExtensionDegree c d t := by
    have hr := denseGold_rounding_lower c d t hm hell
    have hp : 0<(d+c)*denseGoldExtensionDegree c d t :=
      lt_of_lt_of_le (by omega : 0<denseGoldExponent c d t-(d+c)) hr.le
    exact (Nat.pos_of_mul_pos_left hp)
  have hΔ' : 1≤d+c-t*(d+c-d+if Even d then 1 else 0) := by
    have hcd : d+c-d=c := by omega
    rw [hcd]
    exact hΔ
  have hlist := gold_counting_list D 0 (d+c) d t hB hD ht2 htd hΔ'
  refine ⟨?_,?_⟩
  · simpa [affineDomain] using hlist
  obtain ⟨F,fieldF,finiteF,hF⟩ := exists_extension_of_degree B
    (denseGoldExtensionDegree c d t) her
  refine ⟨F,fieldF,finiteF,?_⟩
  letI := fieldF
  letI := finiteF
  obtain ⟨φ,hqcard⟩ := hF
  letI : CharP F 2 := charP_of_injective_ringHom φ.injective 2
  refine ⟨φ,?_,?_⟩
  · rw [hqcard,hB]
  let N := 2^d
  let L := 2^(2*t)*(2^(d+c-t*(c+if Even d then 1 else 0))-1)*
    gaussianBinomial 4 (d/2) t
  let T := N/2-N/2^(t+1)
  let δ := N/2^(2*t)
  let q := Fintype.card F
  have hq : q=2^((d+c)*denseGoldExtensionDegree c d t) := by
    dsimp [q]
    rw [hqcard,hB,←pow_mul]
  have hround := denseGold_rounding_lower c d t hm hell
  have hqexp' : d+1≤(d+c)*denseGoldExtensionDegree c d t := hqexp.trans hround.le
  have hNq : N<q := by
    rw [hq]
    dsimp [N]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have h2Nq : 2*N≤q := by
    rw [hq]
    dsimp [N]
    rw [←pow_succ']
    exact Nat.pow_le_pow_right (by decide) hqexp'
  have hδ : δ=2^(d-2*t) := by
    dsimp [δ,N]
    exact Nat.pow_div hdt (by decide)
  have hδpos : 0<δ := by rw [hδ]; positivity
  have hL : q≤L := by
    rw [hq]
    dsimp [L]
    exact (Nat.pow_le_pow_right (by decide)
      (Nat.mul_div_le (denseGoldExponent c d t) (d+c))).trans
        (denseGold_power_le_list c d t htd hΔ)
  have hqL : q≤δ*L := hL.trans (Nat.le_mul_of_pos_left L hδpos)
  have h8δ : 8*δ≤q := by
    rw [hq,hδ,show 8=2^3 by norm_num,←pow_add]
    exact Nat.pow_le_pow_right (by decide) h8exp
  have hgold := gold_counting φ D 0 (d+c) d t hB hD ht2 htd hΔ' hNq
  dsimp only at hgold
  have haffine : affineDomain (additiveDomain D) 0=additiveDomain D := by
    ext x
    simp [affineDomain]
  rw [haffine] at hgold
  obtain ⟨f,g,hcommon,hg,hf,hbad,hbadstrong⟩ := hgold
  have hZ : ⌈(L : ℚ)*((q : ℚ)-(N : ℚ))/
      ((q : ℚ)-(N : ℚ)+(δ : ℚ)*((L : ℚ)-1))⌉₊-1 ≤
      (nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g T).card := by
    simpa [N,L,T,δ,q] using hbad
  have hZQ : ((⌈(L : ℚ)*((q : ℚ)-(N : ℚ))/
      ((q : ℚ)-(N : ℚ)+(δ : ℚ)*((L : ℚ)-1))⌉₊-1 : ℕ) : ℚ) ≤
      ((nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g T).card : ℚ) := by
    exact_mod_cast hZ
  refine ⟨f,g,hcommon,?_,?_⟩
  · have henergy := gold_energy_count_lower_bound N δ L q (by dsimp [N]; positivity)
      h2Nq hδpos hqL
    exact henergy.trans hZQ
  · have hp := gold_energy_probability_lower_bound N δ L q (by dsimp [N]; positivity)
      h2Nq hδpos hqL h8δ
    exact hp.trans (div_le_div_of_nonneg_right hZQ (by positivity))

end BinaryFieldCounterexamples.Gold
