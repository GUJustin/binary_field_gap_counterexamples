/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.QuadraticNearJohnsonExact
public import BinaryFieldCounterexamples.MainTheorems.QuadraticNearJohnsonCompanions
public import BinaryFieldCounterexamples.MainTheorems.RateEighthProbability
/-!
# Main theorem companions: the front-matter probability certificates

This module assembles the four numerical consequences in the abstract,
Section 1, and Table 1. The probabilities concern actual exceptional challenge
sets on prescribed domains. Decimal comparisons use exact integer powers.
The statement in Section 1 at length `2^20` needs the challenge-field size
`2^128`; that field size is explicit here.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
set_option exponentiation.threshold 15000
set_option maxRecDepth 4000

/-- Section 1's `90.585` decimal follows from an exact positive-power certificate. -/
theorem frontmatter_90585_integer_certificate :
    (2 : ℕ)^7483 < 183251413675^200 := by norm_num

/-- Section 1's length-`2^20` exact count exceeds the printed probability threshold. -/
theorem frontmatter_90585_count_lower :
    (2 : ℝ)^(128 - 90.585 : ℝ) < 183251413675 := by
  apply (Real.rpow_lt_rpow_iff
    (x := (2 : ℝ)^(128 - 90.585 : ℝ)) (y := 183251413675) (z := (200 : ℝ))
    (Real.rpow_nonneg (by norm_num) _) (by norm_num) (by norm_num)).mp
  rw [← Real.rpow_mul (by norm_num), show (128 - 90.585 : ℝ)*200 = 7483 by norm_num]
  rw [show (7483 : ℝ) = (7483 : ℕ) by norm_num,
    show (200 : ℝ) = (200 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  exact_mod_cast frontmatter_90585_integer_certificate

/-- Table 1's `N=2^22` proper-subfield example: the exact exceptional probability
is strictly greater than `2^(-87)` in a 128-bit challenge field. -/
theorem quadratic_length22_probability
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B)
    (hB : Fintype.card B = 2^64) (hF : Fintype.card F = 2^128)
    (hD : (additiveDomain D).card = 2^22) :
    let E := mappedDomain φ (additiveDomain D)
    ∃ f g : E → F,
      commonAgreementEQ E (2^18) f g (2^19-1) ∧
      agreementLE E (2^18) f (2^19) ∧ agreementEQ E (2^18) g (2^19-1) ∧
      (badChallenges E (2^18) f g (2^20-1)).card = 2932028910251 ∧
      (2 : ℝ)^(-87 : ℝ) <
        ((badChallenges E (2^18) f g (2^20-1)).card : ℝ)/(Fintype.card F : ℝ) := by
  have hp : ¬Function.Surjective φ := by
    intro h
    have hc := Fintype.card_le_of_surjective φ h
    rw [hB, hF] at hc
    norm_num at hc
  obtain ⟨f,g,I,hc,hf,hg,hi,_,ht,_,_⟩ :=
    quadratic_near_johnson_exact φ hp D (2^18) (by norm_num) ⟨18,rfl⟩
      (by simpa using hD)
  have he : badChallenges _ (2^18) f g (2^20-1) = I :=
    ht _ (by norm_num) (by norm_num)
  norm_num at hi hc hf hg
  refine ⟨f,g,hc,hf,hg,?_,?_⟩
  · rw [he,hi]
  · rw [he,hi,hF]
    rw [Real.rpow_neg (by norm_num), show (87 : ℝ) = (87 : ℕ) by norm_num,
      Real.rpow_natCast]
    norm_num

/-- Section 1, length `2^20`: Corollary 4.2 in the explicitly required
128-bit field gives exceptional probability strictly above `2^(-90.585)`. -/
theorem quadratic_length20_probability
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (hF : Fintype.card F = 2^128)
    (hD : (additiveDomain D).card = 2^20) :
    let E := additiveDomain D
    ∃ f g : E → F,
      commonAgreementEQ E (2^16) f g (2^17-1) ∧
      183251413675 ≤ (badChallenges E (2^16) f g (2^18-1)).card ∧
      (2 : ℝ)^(-90.585 : ℝ) <
        ((badChallenges E (2^16) f g (2^18-1)).card : ℝ)/(Fintype.card F : ℝ) := by
  obtain ⟨θ,hc,hcount⟩ := quadratic_near_johnson_same_field D (2^16)
    (by norm_num) ⟨16,rfl⟩ (by simpa using hD)
  rw [hF] at hcount
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reducePow,
    Nat.reduceDiv] at hc hcount
  have hlo : 183251413675 ≤
      max (183251413675 - ⌊(Nat.choose 183251413675 2 : ℚ) / 2^128⌋₊)
        ⌈(2^128 : ℚ)*183251413675/(2^128+183251413675-1)⌉₊ := by
    apply le_trans ?_ (le_max_right _ _)
    have he : ⌈(2^128 : ℚ)*183251413675/(2^128+183251413675-1)⌉₊ =
        183251413675 := by
      rw [Nat.ceil_eq_iff (by decide)]
      norm_num
    rw [he]
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hlo
  have hcount' := hlo.trans hcount
  let E := additiveDomain D
  let f : E → F := fun x => (x : F)^(8*2^16-1)+θ*(x : F)^(4*2^16-1)
  let g : E → F := fun x => (x : F)^(2*2^16-1)
  change commonAgreementEQ E (2^16) f g (2^17-1) at hc
  change 183251413675 ≤ (badChallenges E (2^16) f g (2^18-1)).card at hcount'
  refine ⟨f,g,hc,hcount',?_⟩
  have hb : (2 : ℝ)^(128-90.585 : ℝ) <
      ((badChallenges E (2^16) f g (2^18-1)).card : ℝ) :=
    frontmatter_90585_count_lower.trans_le (Nat.cast_le.mpr hcount')
  have hp : (2 : ℝ)^(-90.585 : ℝ) <
      ((badChallenges E (2^16) f g (2^18-1)).card : ℝ)/(2 : ℝ)^128 := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^128)).mpr
    rw [show (128-90.585 : ℝ) = -90.585+128 by norm_num,
      Real.rpow_add (by norm_num), show (128 : ℝ) = (128 : ℕ) by norm_num,
      Real.rpow_natCast] at hb
    exact hb
  rw [hF]
  convert hp using 1 <;> norm_num [E]

/-- Section 4.2's two independent repetitions: one fixed rate-`1/8` pair has
joint exceptional probability above `2^(-57.17)`. The square is the uniform
product probability of two independent challenges for that same pair. -/
theorem rate_eighth_two_repetitions_probability
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (a : F)
    (hD : (additiveDomain D).card = 2^20) (hF : Fintype.card F = 2^64) :
    let E := affineDomain (additiveDomain D) a
    ∃ f g : E → F,
      commonAgreementEQ E (2^17) f g (2^17) ∧ agreementEQ E (2^17) g (2^17) ∧
      (2 : ℝ)^(-57.17 : ℝ) <
        (((badChallenges E (2^17) f g (3*2^16)).card : ℝ)/(Fintype.card F : ℝ))^2 := by
  obtain ⟨f,g,hc,hg,_,_,_,hp⟩ := rate_eighth_finite_probability D a hD hF
  refine ⟨f,g,hc,hg,?_⟩
  have hsq := pow_lt_pow_left₀ hp (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(-28.585 : ℝ))
    (by decide : (2 : ℕ) ≠ 0)
  have he : ((2 : ℝ)^(-28.585 : ℝ))^2 = (2 : ℝ)^(-57.17 : ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [he] at hsq
  exact hsq

/-- Section 4.2's two-repetition clause: the literal Cartesian product of the
exceptional challenge set occupies more than `2^(-57.17)` of the full space of
two independent challenges, for the same fixed pair of actual words. -/
theorem rate_eighth_two_repetitions_product_probability
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (a : F)
    (hD : (additiveDomain D).card = 2^20) (hF : Fintype.card F = 2^64) :
    let E := affineDomain (additiveDomain D) a
    ∃ f g : E → F,
      commonAgreementEQ E (2^17) f g (2^17) ∧ agreementEQ E (2^17) g (2^17) ∧
      let I := badChallenges E (2^17) f g (3*2^16)
      (2 : ℝ)^(-57.17 : ℝ) <
        ((I ×ˢ I).card : ℝ)/(Fintype.card (F × F) : ℝ) := by
  obtain ⟨f,g,hc,hg,hp⟩ := rate_eighth_two_repetitions_probability D a hD hF
  refine ⟨f,g,hc,hg,?_⟩
  convert hp using 1
  simp only [Finset.card_product, Fintype.card_prod, Nat.cast_mul]
  ring

/-- Abstract: on every proper-subfield binary domain larger than `2^20`,
Theorem 4.1's exact count has probability greater than `2^(-90)` over a
128-bit challenge field. The message length and threshold remain literal. -/
theorem quadratic_above_length20_probability
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hp : ¬Function.Surjective φ) (D : AddSubgroup B)
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K=2^k)
    (hD : (additiveDomain D).card=16*K) (hlarge : 2^20 < 16*K)
    (hF : Fintype.card F=2^128) :
    let E := mappedDomain φ (additiveDomain D)
    ∃ f g : E → F,
      commonAgreementEQ E K f g (2*K-1) ∧
      (2 : ℝ)^(-90 : ℝ) <
        ((badChallenges E K f g (4*K-1)).card : ℝ)/(Fintype.card F : ℝ) := by
  obtain ⟨k,hk⟩ := hpow
  have hk17 : 17 ≤ k := by
    by_contra h
    have hle := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show k ≤ 16 by omega)
    rw [hk] at hlarge
    norm_num at hle hlarge
    omega
  have hKbig : 2^17 ≤ K := by
    rw [hk]
    exact Nat.pow_le_pow_right (by decide) hk17
  obtain ⟨f,g,I,hc,_,_,hi,_,ht,_,_⟩ :=
    quadratic_near_johnson_exact φ hp D K hK ⟨k,hk⟩ hD
  have he := ht (4*K-1) (by omega) le_rfl
  have hprod : (2^21-1)*(2^21-2) ≤ (16*K-1)*(16*K-2) := by
    apply Nat.mul_le_mul <;> omega
  have hcount : 733006703275 ≤ I.card := by
    rw [hi]
    have hh := Nat.div_le_div_right hprod (c := 6)
    norm_num at hh
    exact hh
  refine ⟨f,g,hc,?_⟩
  have hh : (733006703275 : ℝ) ≤ I.card := by exact_mod_cast hcount
  have hl : (2 : ℝ)^(-90 : ℝ) < (733006703275 : ℝ)/(2 : ℝ)^128 := by
    rw [Real.rpow_neg (by norm_num), show (90 : ℝ) = (90 : ℕ) by norm_num,
      Real.rpow_natCast]
    norm_num
  apply hl.trans_le
  rw [he,hF]
  convert div_le_div_of_nonneg_right hh
    (show (0 : ℝ) ≤ (2 : ℝ)^128 by positivity) using 1 <;> norm_num
end BinaryFieldCounterexamples
