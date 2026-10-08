/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.GoldCounting
public import BinaryFieldCounterexamples.Constructions.Gold.FixedExtensionParameters
public import BinaryFieldCounterexamples.Constructions.Gold.EnergyLowerBound
/-!
# Constant probability at fixed extension degree

The odd-dimensional hyperplane parameters give a fixed collision denominator
and a locator population larger than the challenge field. The resulting finite
bound is `q/(8*2^(2*e-1))`, hence a positive constant probability for each fixed
extension exponent. This is not the sharper leading coefficient of Corollary
4.3; that separate asymptotic assertion remains open.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- Every prescribed binary hyperplane and affine translate support one pair
with the individual/common bounds and a positive constant fraction of nonzero
exceptional challenges. The multiplier `8` is the existing coarse energy loss. -/
theorem gold_fixed_extension_constant_probability
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (a : B) (n e : ℕ)
    (he : 2≤e) (hn : e+2≤n) (hlarge : 2*e^2≤n)
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
      (Fintype.card F:ℚ)/(8*(2:ℚ)^(2*e-1)) ≤
        ((nonzeroBadChallenges E (N/4) f g T).card:ℚ) := by
  let N : ℕ := 2^(2*n-1)
  let q : ℕ := Fintype.card F
  let δ : ℕ := 2^(2*e-1)
  let L : ℕ := 2^(2*(n-e))*(2^(n+e)-1)*gaussianBinomial 4 (n-1) (e-1)
  have hNpos : 0<N := by dsimp [N]; positivity
  have hδpos : 0<δ := by dsimp [δ]; positivity
  have hqform : q=2^(2*n*e) := by dsimp [q]; rw [hF,←pow_mul]
  have h2N : 2*N≤q := by
    have hN2 : 2*N=2^(2*n) := by
      dsimp [N]
      rw [←pow_succ']
      congr 1
      omega
    rw [hN2,hqform]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith
  have hqL : q≤L := by
    dsimp [q,L]
    rw [hF]
    simpa using fixed_extension_list_ge_scaled_field n e 0 he hn (by omega)
  have hbudget : q≤δ*L := hqL.trans (Nat.le_mul_of_pos_left L hδpos)
  have h8δ : 8*δ≤q := by
    dsimp [δ]
    rw [show 8=2^3 by norm_num,←pow_add,hqform]
    apply Nat.pow_le_pow_right (by decide)
    have hm : 2*e≤n*e := Nat.mul_le_mul_right e (by omega : 2≤n)
    rw [Nat.mul_assoc]
    omega
  have hodd : ¬Even (2*n-1) := by rintro ⟨r,hr⟩; omega
  have hΔ : 1≤2*n-(n-e)*(2*n-(2*n-1)+if Even (2*n-1) then 1 else 0) := by
    rw [ite_eq_right hodd,show 2*n-(2*n-1)+0=1 by omega,mul_one]
    omega
  have hNq : 2^(2*n-1)<Fintype.card F := by change N<q; omega
  obtain ⟨f,g,hcommon,hg,hf,hbad,_⟩ := gold_counting φ D a (2*n) (2*n-1) (n-e)
    hB hD (by omega) (by omega) hΔ hNq
  rw [fixed_extension_list_eq n e he hn,fixed_extension_delta_eq n e he hn,
    fixed_extension_threshold_eq n e he hn] at hbad
  dsimp only at hcommon hg hf hbad ⊢
  refine ⟨f,g,hcommon,hg,hf,?_⟩
  have hprob := gold_energy_probability_lower_bound N δ L q hNpos h2N hδpos hbudget h8δ
  have hqpos : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have hcount := (le_div_iff₀ hqpos).mp hprob
  have hZ := (show (⌈(L:ℚ)*((q:ℚ)-N)/((q:ℚ)-N+(δ:ℚ)*((L:ℚ)-1))⌉₊-1:ℕ)≤
      (nonzeroBadChallenges (mappedDomain φ (affineDomain (additiveDomain D) a))
        (N/4) f g (2^(2*n-2)-2^(n+e-2))).card from hbad)
  have hZQ : ((⌈(L:ℚ)*((q:ℚ)-N)/((q:ℚ)-N+(δ:ℚ)*((L:ℚ)-1))⌉₊-1:ℕ):ℚ)≤
      ((nonzeroBadChallenges (mappedDomain φ (affineDomain (additiveDomain D) a))
        (N/4) f g (2^(2*n-2)-2^(n+e-2))).card:ℚ) := by exact_mod_cast hZ
  have hfinal := hcount.trans hZQ
  simpa only [q,δ,N,Nat.cast_pow,Nat.cast_ofNat,one_div,mul_comm,mul_assoc,div_eq_mul_inv,one_mul]
    using hfinal

end BinaryFieldCounterexamples.Gold
