/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.ExactHalfAgreement
public import BinaryFieldCounterexamples.Constructions.Gold.FiniteExtensions
public import BinaryFieldCounterexamples.Constructions.Gold.FixedPowerGrowth
/-! # Exponent-one fixed-threshold counterexample

The exact hyperplane construction handles every positive count exponent below
one. Its challenge field equals the native field in cardinality, and the
extension exponent is literally one. The same fixed pair and exact common
agreement are unchanged when lowering the threshold below one half.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
set_option autoImplicit false
set_option linter.style.haveILetI false
/-- For count exponent below one, the exact half-agreement construction has
extension exponent one, fixed before threshold, constant and length cutoff. -/
theorem optimal_fixed_threshold_of_lt_one
    (b : ℝ) (_hb : 0 < b) (hb1 : b < 1) :
    ∀ (a C₀ : ℝ), 1/4<a → a<1/2 → 0<C₀ →
    ∀ N₀ : ℕ, ∃ d : ℕ, N₀ ≤ 2 ^ d ∧
    ∃ (B : Type) (fieldB : Field B) (finiteB : Fintype B),
    letI := fieldB
    letI := finiteB
    ∃ (_ : CharP B 2), Fintype.card B = 2 ^ (d + 1) ∧
    ∃ D : AddSubgroup B, (additiveDomain D).card = 2 ^ d ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
    letI := fieldF
    letI := finiteF
    ∃ φ : B →+* F, Fintype.card F = (2 ^ (d + 1)) ^ 1 ∧
    let D' := mappedDomain φ (additiveDomain D)
    let N : ℕ := 2 ^ d
    ∃ f g : D' → F,
      commonAgreementEQ D' (N / 4) f g (N / 4) ∧
      C₀ * (N : ℝ) ^ b <
        (badChallenges D' (N / 4) f g ⌈a * N⌉₊).card := by
  classical
  intro a C₀ _ha ha' _hC₀ N₀
  obtain ⟨d,_,hd,hN₀,hgrowth⟩:=Gold.exists_even_binary_power_growth b 1 (by simpa using hb1) C₀ N₀ 3
  obtain ⟨B,fieldB,finiteB,hBdata⟩:=Gold.exists_hyperplane_with_extension d 1 (by omega)
  refine ⟨d,hN₀,B,fieldB,finiteB,?_⟩
  letI := fieldB
  letI := finiteB
  obtain ⟨charB,hB,D,hD,F,fieldF,finiteF,hFdata⟩:=hBdata
  refine ⟨charB,hB,D,hD,F,fieldF,finiteF,?_⟩
  letI := fieldF
  letI := finiteF
  obtain ⟨φ,hF⟩:=hFdata
  refine ⟨φ,hF,?_⟩
  letI : CharP F 2:=charP_of_injective_ringHom φ.injective 2
  let Dm:=D.map φ.toAddMonoidHom
  have hDm : (additiveDomain Dm).card=2^d := by
    rw [←mappedDomain_additiveDomain,card_mappedDomain,hD]
  have hproper : 2^d<Fintype.card F := by
    rw [hF,pow_one,pow_succ]
    have hp:0<2^d:=by positivity
    omega
  have hex:=exact_half_agreement Dm 0 d hd hDm hproper
  have haff : affineDomain (additiveDomain Dm) 0=additiveDomain Dm := by
    ext x
    simp [affineDomain]
  rw [haff] at hex
  dsimp only at hex ⊢
  change ∃ f g : mappedDomain φ (additiveDomain D) → F,
    commonAgreementEQ (mappedDomain φ (additiveDomain D)) (2^d/4) f g (2^d/4) ∧
    C₀*((2^d:ℕ):ℝ)^b < (badChallenges (mappedDomain φ (additiveDomain D))
      (2^d/4) f g ⌈a*((2^d:ℕ):ℝ)⌉₊).card
  rw [mappedDomain_additiveDomain]
  obtain ⟨f,g,hcommon,_,_,hbad,_,_⟩:=hex
  refine ⟨f,g,hcommon,?_⟩
  let N:=2^d
  have hthreshold : ⌈a*(N:ℝ)⌉₊≤N/2 := by
    apply Nat.ceil_le.mpr
    have hhalf : ((N/2:ℕ):ℝ)=(N:ℝ)/2 := by
      dsimp [N]
      rw [show 2^d/2=2^(d-1) by exact Nat.pow_div (x:=2) (m:=d) (n:=1) (by omega) (by decide)]
      rw [Nat.cast_pow,Nat.cast_pow]
      rw [show d=(d-1)+1 by omega,pow_succ]
      norm_num
    rw [hhalf]
    have hp:(0:ℝ)<N:=by dsimp [N];positivity
    nlinarith
  have hsubset : badChallenges (additiveDomain Dm) (N/4) f g (N/2) ⊆
      badChallenges (additiveDomain Dm) (N/4) f g ⌈a*(N:ℝ)⌉₊ := by
    intro z hz
    rw [mem_badChallenges] at hz ⊢
    obtain ⟨p,hp,hh⟩:=hz
    exact ⟨p,hp,hthreshold.trans hh⟩
  have hN2 : 2≤N := by
    dsimp [N]
    exact Nat.one_lt_pow (by omega) (by decide)
  have hcount : N≤(badChallenges (additiveDomain Dm) (N/4) f g ⌈a*(N:ℝ)⌉₊).card := by
    have hh:=Finset.card_le_card hsubset
    rw [hbad] at hh
    dsimp [N] at *
    omega
  have hform : (N:ℝ)^b=(2:ℝ)^((d:ℝ)*b) := by
    dsimp [N]
    rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  have hgrowth' : C₀*(N:ℝ)^b<(N:ℝ) := by
    rw [hform]
    simpa only [N,Nat.cast_one,mul_one,Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat] using hgrowth
  exact hgrowth'.trans_le (by exact_mod_cast hcount)
end BinaryFieldCounterexamples
