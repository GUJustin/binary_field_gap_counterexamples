/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FixedExtensionAsymptotic
public import BinaryFieldCounterexamples.Constructions.Gold.FullFieldExtensionParameters
/-!
# Full-field fixed-extension probability

At length `2^(2*n)`, the even-dimensional Gold parameters give limiting
exceptional probability at least `1/4^(e-1)` for each fixed extension exponent.
The cutoff precedes the fields and domain. All counts concern one fixed pair.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- The finite fixed-extension probability has the sharp leading coefficient,
with an explicit error `3/2^k` on the full field and every translate. -/
theorem gold_full_field_extension_probability_error
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (a : B) (n e k : ℕ)
    (he : 2≤e) (hn : e+2≤n) (hkn : k≤n)
    (hscale : 2*e^2+k+2≤n)
    (hB : Fintype.card B=2^(2*n))
    (hD : (additiveDomain D).card=2^(2*n))
    (hF : Fintype.card F=(2^(2*n))^e) :
    let N : ℕ := 2^(2*n)
    let T : ℕ := 2^(2*n-1)-2^(n+e-2)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F,
      commonAgreementEQ E (N/4) f g (N/4) ∧
      agreementEQ E (N/4) g (N/4) ∧
      agreementLE E (N/4) f (3*N/8-1) ∧
      ((1:ℚ)/(2:ℚ)^(2*(e-1))-3/(2:ℚ)^k)*(Fintype.card F:ℚ) ≤
        ((nonzeroBadChallenges E (N/4) f g T).card:ℚ) := by
  let N : ℕ := 2^(2*n)
  let q : ℕ := Fintype.card F
  let δ : ℕ := 2^(2*(e-1))
  let L : ℕ := 2^(2*(n-e+1))*(2^(n+e-1)-1)*gaussianBinomial 4 n (e-1)
  have hNpos : 0<N := by dsimp [N]; positivity
  have hδpos : 0<δ := by dsimp [δ]; positivity
  have hqform : q=2^(2*n*e) := by dsimp [q]; rw [hF,←pow_mul]
  have hNq : N<q := by
    rw [hqform]
    dsimp [N]
    apply Nat.pow_lt_pow_right (by decide)
    have hm := Nat.mul_le_mul_left (2*n) he
    omega
  have hMN : 2^k*N≤q := by
    dsimp [N]
    rw [←pow_add,hqform]
    apply Nat.pow_le_pow_right (by decide)
    have hm := Nat.mul_le_mul_left (2*n) he
    omega
  have hML : 2^k*q≤L := by
    dsimp [q,L]
    rw [hF]
    exact full_field_extension_list_ge_scaled_field n e k he hn hscale
  have heven : Even (2*n) := ⟨n,by omega⟩
  have hΔ : 1≤2*n-(n-e+1)*(2*n-2*n+if Even (2*n) then 1 else 0) := by
    rw [ite_eq_left heven]
    simp only [Nat.sub_self,zero_add,mul_one]
    omega
  obtain ⟨f,g,hcommon,hg,hf,hbad,_⟩ := gold_counting φ D a (2*n) (2*n) (n-e+1)
    hB hD (by omega) (by omega) hΔ hNq
  rw [full_field_extension_list_eq n e he hn,full_field_extension_delta_eq n e he hn,
    full_field_extension_threshold_eq n e he hn] at hbad
  dsimp only at hcommon hg hf hbad ⊢
  refine ⟨f,g,hcommon,hg,hf,?_⟩
  have hprob := gold_energy_probability_of_scaled_budgets N δ L q (2^k)
    hNpos hNq hδpos (by positivity) hMN hML
  have hqpos : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have hcount := (le_div_iff₀ hqpos).mp hprob
  have hZQ : ((⌈(L:ℚ)*((q:ℚ)-N)/((q:ℚ)-N+(δ:ℚ)*((L:ℚ)-1))⌉₊-1:ℕ):ℚ)≤
      ((nonzeroBadChallenges (mappedDomain φ (affineDomain (additiveDomain D) a))
        (N/4) f g (2^(2*n-1)-2^(n+e-2))).card:ℚ) := by exact_mod_cast hbad
  have hfinal := hcount.trans hZQ
  simpa only [q,δ,N,Nat.cast_pow,Nat.cast_ofNat] using hfinal

/-- For each fixed extension exponent the original probability coefficient is
attained up to every positive error, uniformly over all fields and prescribed
full-field domains after a cutoff depending only on that exponent and error. -/
theorem gold_full_field_extension_probability_asymptotic
    (e : ℕ) (he : 2≤e) (ε : ℝ) (hε : 0<ε) :
    ∃ n₀ : ℕ, e+2≤n₀ ∧ ∀ n : ℕ, n₀≤n →
    ∀ {B F : Type} [Field B] [Fintype B] [CharP B 2]
      [Field F] [Fintype F] [CharP F 2]
      (φ : B →+* F) (D : AddSubgroup B) (a : B),
      Fintype.card B=2^(2*n) → (additiveDomain D).card=2^(2*n) →
      Fintype.card F=(2^(2*n))^e →
    let N : ℕ := 2^(2*n)
    let T : ℕ := 2^(2*n-1)-2^(n+e-2)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F,
      commonAgreementEQ E (N/4) f g (N/4) ∧
      agreementEQ E (N/4) g (N/4) ∧
      agreementLE E (N/4) f (3*N/8-1) ∧
      ((1:ℝ)/(2:ℝ)^(2*(e-1))-ε)*(Fintype.card F:ℝ) ≤
        ((nonzeroBadChallenges E (N/4) f g T).card:ℝ) := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (3/ε) (by norm_num : (1:ℝ)<2)
  have hkε : (3:ℝ)/(2:ℝ)^k<ε := by
    have hp : (0:ℝ)<(2:ℝ)^k := by positivity
    apply (div_lt_iff₀ hp).mpr
    have hh := (div_lt_iff₀ hε).mp hk
    linarith
  let n₀ := max (e+2) (2*e^2+k+2)
  refine ⟨n₀,Nat.le_max_left _ _,?_⟩
  intro n hn₀ B F fieldB finiteB charB fieldF finiteF charF φ D a hB hD hF
  have hn : e+2≤n := (Nat.le_max_left _ _).trans hn₀
  have hlarge : 2*e^2+k+2≤n := (Nat.le_max_right _ _).trans hn₀
  obtain ⟨f,g,hcommon,hg,hf,hcount⟩ := gold_full_field_extension_probability_error φ D a n e k
    he hn (by omega) (by omega) hB hD hF
  refine ⟨f,g,hcommon,hg,hf,?_⟩
  have hcountR : ((1:ℝ)/(2:ℝ)^(2*(e-1))-3/(2:ℝ)^k)*(Fintype.card F:ℝ)≤
      ((nonzeroBadChallenges (mappedDomain φ (affineDomain (additiveDomain D) a))
        (2^(2*n)/4) f g (2^(2*n-1)-2^(n+e-2))).card:ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hcount
    push_cast at hh
    exact hh
  have hcoef : (1:ℝ)/(2:ℝ)^(2*(e-1))-ε≤(1:ℝ)/(2:ℝ)^(2*(e-1))-3/(2:ℝ)^k := by
    linarith
  exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans hcountR

end BinaryFieldCounterexamples.Gold
