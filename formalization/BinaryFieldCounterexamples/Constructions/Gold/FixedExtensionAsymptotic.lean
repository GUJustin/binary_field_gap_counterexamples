/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.GoldCounting
public import BinaryFieldCounterexamples.Constructions.Gold.FixedExtensionParameters
public import BinaryFieldCounterexamples.Constructions.Gold.FixedExtensionEnergy
/-!
# The sharp fixed-extension Gold probability coefficient

The explicit finite deficit yields the original coefficient `1/2^(2*e-1)`
from Corollary 5.3. Every positive error has a cutoff depending only on `e`
and that error, before choosing the fields, prescribed hyperplane or translate.
The integer threshold is identified with the manuscript's real radical formula.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- Scaling the field and locator budgets bounds all three probability deficits
by the reciprocal of the same positive integer. -/
theorem gold_energy_probability_of_scaled_budgets (N δ L q M : ℕ)
    (hN : 0<N) (hNq : N<q) (hδ : 0<δ) (hM : 0<M)
    (hMN : M*N≤q) (hML : M*q≤L) :
    let Z : ℕ := ⌈(L:ℚ)*((q:ℚ)-(N:ℚ)) /
      ((q:ℚ)-(N:ℚ)+(δ:ℚ)*((L:ℚ)-1))⌉₊-1
    (1:ℚ)/δ-3/(M:ℚ)≤(Z:ℚ)/(q:ℚ) := by
  have hq : 0<q := by omega
  have hL : 0<L := lt_of_lt_of_le (Nat.mul_pos hM hq) hML
  have hMq : M≤q := (Nat.le_mul_of_pos_right M hN).trans hMN
  have hδ1 : (1:ℚ)≤δ := by exact_mod_cast hδ
  have hqQ : (0:ℚ)<q := by exact_mod_cast hq
  have hLQ : (0:ℚ)<L := by exact_mod_cast hL
  have hMQ : (0:ℚ)<M := by exact_mod_cast hM
  have hδQ : (0:ℚ)<δ := by exact_mod_cast hδ
  have hMNQ : (M:ℚ)*N≤q := by exact_mod_cast hMN
  have hMLQ : (M:ℚ)*q≤L := by exact_mod_cast hML
  have h₁ : (N:ℚ)/((δ:ℚ)*q)≤1/(M:ℚ) := by
    rw [div_le_div_iff₀ (by positivity : (0:ℚ)<(δ:ℚ)*q) hMQ]
    nlinarith
  have h₂ : (q:ℚ)/((δ:ℚ)^2*L)≤1/(M:ℚ) := by
    rw [div_le_div_iff₀ (by positivity : (0:ℚ)<(δ:ℚ)^2*L) hMQ]
    have hs : (1:ℚ)≤(δ:ℚ)^2 := by nlinarith
    nlinarith
  have h₃ : (1:ℚ)/(q:ℚ)≤1/(M:ℚ) :=
    one_div_le_one_div_of_le hMQ (by exact_mod_cast hMq)
  have hbase := gold_energy_probability_deficit N δ L q hNq hδ hL
  dsimp only at hbase ⊢
  rw [show (3:ℚ)/(M:ℚ)=3*(1/(M:ℚ)) by ring]
  linarith

/-- The finite fixed-extension probability has the sharp leading coefficient,
with an explicit error `3/2^k` on every prescribed affine hyperplane. -/
theorem gold_fixed_extension_probability_error
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (a : B) (n e k : ℕ)
    (he : 2≤e) (hn : e+2≤n) (hkn : k≤n)
    (hscale : 2*e^2+k+1≤n+e)
    (hB : Fintype.card B=2^(2*n))
    (hD : (additiveDomain D).card=2^(2*n-1))
    (hF : Fintype.card F=(2^(2*n))^e) :
    let N : ℕ := 2^(2*n-1)
    let T : ℕ := 2^(2*n-2)-2^(n+e-2)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F,
      commonAgreementEQ E (N/4) f g (N/4) ∧
      agreementEQ E (N/4) g (N/4) ∧
      agreementLE E (N/4) f (3*N/8-1) ∧
      ((1:ℚ)/(2:ℚ)^(2*e-1)-3/(2:ℚ)^k)*(Fintype.card F:ℚ) ≤
        ((nonzeroBadChallenges E (N/4) f g T).card:ℚ) := by
  let N : ℕ := 2^(2*n-1)
  let q : ℕ := Fintype.card F
  let δ : ℕ := 2^(2*e-1)
  let L : ℕ := 2^(2*(n-e))*(2^(n+e)-1)*gaussianBinomial 4 (n-1) (e-1)
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
    exact fixed_extension_list_ge_scaled_field n e k he hn hscale
  have hodd : ¬Even (2*n-1) := by rintro ⟨r,hr⟩; omega
  have hΔ : 1≤2*n-(n-e)*(2*n-(2*n-1)+if Even (2*n-1) then 1 else 0) := by
    rw [ite_eq_right hodd,show 2*n-(2*n-1)+0=1 by omega,mul_one]
    omega
  obtain ⟨f,g,hcommon,hg,hf,hbad,_⟩ := gold_counting φ D a (2*n) (2*n-1) (n-e)
    hB hD (by omega) (by omega) hΔ hNq
  rw [fixed_extension_list_eq n e he hn,fixed_extension_delta_eq n e he hn,
    fixed_extension_threshold_eq n e he hn] at hbad
  dsimp only at hcommon hg hf hbad ⊢
  refine ⟨f,g,hcommon,hg,hf,?_⟩
  have hprob := gold_energy_probability_of_scaled_budgets N δ L q (2^k)
    hNpos hNq hδpos (by positivity) hMN hML
  have hqpos : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have hcount := (le_div_iff₀ hqpos).mp hprob
  have hZQ : ((⌈(L:ℚ)*((q:ℚ)-N)/((q:ℚ)-N+(δ:ℚ)*((L:ℚ)-1))⌉₊-1:ℕ):ℚ)≤
      ((nonzeroBadChallenges (mappedDomain φ (affineDomain (additiveDomain D) a))
        (N/4) f g (2^(2*n-2)-2^(n+e-2))).card:ℚ) := by exact_mod_cast hbad
  have hfinal := hcount.trans hZQ
  simpa only [q,δ,N,Nat.cast_pow,Nat.cast_ofNat] using hfinal

/-- The exact integer agreement threshold equals the radical expression in
Corollary 5.3; no rounding or change of threshold is needed. -/
theorem fixed_extension_threshold_eq_radical (n e : ℕ) (he : 2≤e) (hn : e+2≤n) :
    ((2^(2*n-2)-2^(n+e-2):ℕ):ℝ) =
      (2^(2*n-1):ℕ)/2 - (2:ℝ)^((e:ℝ)-3/2)*Real.sqrt (2^(2*n-1):ℕ) := by
  have hsub : (2:ℕ)^(n+e-2)≤2^(2*n-2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.cast_sub hsub,Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat]
  have hhalf : ((2^(2*n-1):ℕ):ℝ)/2=(2:ℝ)^(2*n-2) := by
    push_cast
    rw [show 2*n-1=(2*n-2)+1 by omega,pow_succ]
    ring
  rw [hhalf]
  congr 1
  rw [Real.sqrt_eq_rpow,Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast 2 (2*n-1),
    ←Real.rpow_mul (by norm_num : (0:ℝ)≤2),←Real.rpow_add (by norm_num : (0:ℝ)<2),
    ←Real.rpow_natCast]
  congr 1
  push_cast [Nat.cast_sub (by omega : 2≤n+e),Nat.cast_sub (by omega : 1≤2*n)]
  ring

/-- For each fixed extension exponent the original probability coefficient is
attained up to every positive error, uniformly over all fields and prescribed
affine hyperplanes after a cutoff depending only on that exponent and error. -/
theorem gold_fixed_extension_probability_asymptotic
    (e : ℕ) (he : 2≤e) (ε : ℝ) (hε : 0<ε) :
    ∃ n₀ : ℕ, e+2≤n₀ ∧ ∀ n : ℕ, n₀≤n →
    ∀ {B F : Type} [Field B] [Fintype B] [CharP B 2]
      [Field F] [Fintype F] [CharP F 2]
      (φ : B →+* F) (D : AddSubgroup B) (a : B),
      Fintype.card B=2^(2*n) → (additiveDomain D).card=2^(2*n-1) →
      Fintype.card F=(2^(2*n))^e →
    let N : ℕ := 2^(2*n-1)
    let T : ℕ := 2^(2*n-2)-2^(n+e-2)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F,
      commonAgreementEQ E (N/4) f g (N/4) ∧
      agreementEQ E (N/4) g (N/4) ∧
      agreementLE E (N/4) f (3*N/8-1) ∧
      ((1:ℝ)/(2:ℝ)^(2*e-1)-ε)*(Fintype.card F:ℝ) ≤
        ((nonzeroBadChallenges E (N/4) f g T).card:ℝ) := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (3/ε) (by norm_num : (1:ℝ)<2)
  have hkε : (3:ℝ)/(2:ℝ)^k<ε := by
    have hp : (0:ℝ)<(2:ℝ)^k := by positivity
    apply (div_lt_iff₀ hp).mpr
    have hh := (div_lt_iff₀ hε).mp hk
    linarith
  let n₀ := max (e+2) (2*e^2+k+1)
  refine ⟨n₀,Nat.le_max_left _ _,?_⟩
  intro n hn₀ B F fieldB finiteB charB fieldF finiteF charF φ D a hB hD hF
  have hn : e+2≤n := (Nat.le_max_left _ _).trans hn₀
  have hlarge : 2*e^2+k+1≤n := (Nat.le_max_right _ _).trans hn₀
  obtain ⟨f,g,hcommon,hg,hf,hcount⟩ := gold_fixed_extension_probability_error φ D a n e k
    he hn (by omega) (by omega) hB hD hF
  refine ⟨f,g,hcommon,hg,hf,?_⟩
  have hcountR : ((1:ℝ)/(2:ℝ)^(2*e-1)-3/(2:ℝ)^k)*(Fintype.card F:ℝ)≤
      ((nonzeroBadChallenges (mappedDomain φ (affineDomain (additiveDomain D) a))
        (2^(2*n-1)/4) f g (2^(2*n-2)-2^(n+e-2))).card:ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hcount
    push_cast at hh
    exact hh
  have hcoef : (1:ℝ)/(2:ℝ)^(2*e-1)-ε≤(1:ℝ)/(2:ℝ)^(2*e-1)-3/(2:ℝ)^k := by
    linarith
  exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans hcountR

end BinaryFieldCounterexamples.Gold
