/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.HalfRateConstruction
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingProperty
public import BinaryFieldCounterexamples.Constructions.Gold.NativeCertificate
public import BinaryFieldCounterexamples.Constructions.Gold.Native128Certificate
/-!
# Native finite Gold construction

The actual Gold population is pooled before selecting an additive padding
locator. Its constant derivative preserves the sharp first-input bound; the
excluded pole preserves exact second-input and common agreement. All counts
and thresholds are exact on the original affine domain.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
/-- Native Gold padding preserves both individual bounds on every affine translate. -/
theorem native_pair_from_tensor_lower_bound
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B)
    (hD : Nat.card D=2^27) (e : Module.Basis (Fin 27) (ZMod 2) D)
    (hF : Fintype.card F=2^128)
    (hL : nativeGoldListSize≤(momentTensors D (basisParameter D e) 6).card*2^12) :
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F, commonAgreementEQ E (2^25) f g (2^25) ∧
      agreementEQ E (2^25) g (2^25) ∧ agreementLE E (2^25) f (193*2^27/512-1) ∧
      nativeGoldPaddedCount≤(nonzeroBadChallenges E (2^25) f g (16193*2^27/32768)).card := by
  classical
  dsimp only
  let D' := D.map φ.toAddMonoidHom
  let : Fintype D' := Fintype.ofFinite _
  let : Fintype (Module.Dual (ZMod 2) D) := Fintype.ofInjective
    (fun l : Module.Dual (ZMod 2) D => (l : D → ZMod 2)) DFunLike.coe_injective
  obtain ⟨β,hβ,Z,hZ,hdata⟩ := exists_gold_padding_pool φ D 27 6 hD e (by decide) (by decide)
    (by rw [hF]; norm_num) nativeGoldListSize hL
  have hZ' : nativeGoldPoleCount≤Z.card := by
    simpa only [nativeGoldPoleCount,Nat.cast_pow,Nat.cast_ofNat,hF,show 2^27/2^(2*6)=(2^15:ℕ) by norm_num] using hZ
  let E0 := additiveDomain D'
  let f0 : F → F := fun x => (binaryQuarterNumerator D' β).eval x*(x-β)⁻¹
  let g0 : F → F := fun x => (x-β)⁻¹
  have hd : Module.finrank (ZMod 2) D=27 := by simpa using Module.finrank_eq_card_basis e
  have hβE : β∉E0 := fun h => hβ ((mem_additiveDomain _ _).mp h)
  let j : D →+ F := φ.toAddMonoidHom.comp D.subtype
  have hj : Function.Injective j := fun x y h => Subtype.ext (φ.injective h)
  obtain ⟨A,hA,hAβ,hA',hbad⟩ := exists_polynomial_padding_with_property E0
    (mappedSubgroupDomainEquiv φ D) β hβE (fun x => f0 x) (fun x => g0 x) Z
    27 12 19 ((2^27/2-2^27/2^7)/2) (2^27/2-2^27/2^7) (16193*2^27/32768)
    hd (by decide) (by decide) (by decide) (by norm_num)
    (fun A => A.derivative.natDegree≤0)
    (exists_additive_padding_locator E0 (mappedSubgroupDomainEquiv φ D) β hβE j hj (fun _ => rfl)) (by
      intro z hz
      obtain ⟨hne,p,hp,H,hH,S,hS,hinv,hmatch⟩ := hdata z hz
      exact ⟨hne,p,hp,H,hH,S,hS,hinv,hmatch⟩)
  have hbad' : nativeGoldPaddedCount≤
      (nonzeroBadChallenges E0 (2^25) (fun x => A.eval (x:F)*f0 x)
        (fun x => A.eval (x:F)*g0 x) (16193*2^27/32768)).card := by
    have hk : (2^27/2-2^27/2^7)/2+2^19=(2^25:ℕ) := by norm_num
    rw [hk] at hbad
    apply le_trans (Nat.ceil_mono ?_) hbad
    apply mul_le_mul_of_nonneg_left (by exact_mod_cast hZ')
    norm_num
  rw [mappedDomain_affineDomain,mappedDomain_additiveDomain]
  let E := affineDomain E0 (φ a)
  let f1 : F → F := fun x => A.eval x*f0 x
  let g1 : F → F := fun x => A.eval x*g0 x
  have hcard : 2^25≤E.card := by
    rw [card_affineDomain,card_additiveDomain,natCard_map_addSubgroup,hD]
    norm_num
  have hg0 : agreementLE E0 (2^25) (fun x => g1 x) (2^25) := by
    simpa only [g1,g0,div_eq_mul_inv] using agreementLE_polynomialOverPole E0 β hβE A (2^25)
      (by rw [hA]; norm_num) hAβ
  have hg : agreementLE E (2^25) (fun x => g1 ((x:F)-φ a)) (2^25) :=
    agreementLE_affineDomain E0 (φ a) g1 _ _ hg0
  refine ⟨(fun x => f1 ((x:F)-φ a)),(fun x => g1 ((x:F)-φ a)),
    ⟨commonAgreementGE_of_le_card E _ _ _ hcard,commonAgreementLE_of_right E _ _ _ _ hg⟩,
    ⟨agreementGE_of_le_card E _ _ hcard,hg⟩,?_,?_⟩
  · apply agreementLE_affineDomain E0 (φ a) f1
    have hcD : Fintype.card D'=4*2^25 := by
      rw [←Nat.card_eq_fintype_card,natCard_map_addSubgroup,hD]
      norm_num
    have hf := agreementLE_padded_binaryQuarterSource D' β hβ (2^25) ⟨25,rfl⟩ hcD (2^19)
      (by norm_num) (by norm_num) (by decide) A hA.le hA' hAβ
    simpa only [f1,f0,mul_assoc,show 3*2^25/2+2^19/2-1=193*2^27/512-1 by norm_num] using hf
  · simp only [nonzeroBadChallenges]
    rw [badChallenges_affineDomain E0 (φ a) f1 g1]
    exact hbad'
/-- The sharp native finite count uses both collision bounds and exact padding while preserving both individual guarantees. -/
theorem native_pair_from_tensor_lower_bound_sharp
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B)
    (hD : Nat.card D=2^27) (e : Module.Basis (Fin 27) (ZMod 2) D)
    (hF : Fintype.card F=2^128)
    (hL : nativeGoldListSize≤(momentTensors D (basisParameter D e) 6).card*2^12) :
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F, commonAgreementEQ E (2^25) f g (2^25) ∧
      agreementEQ E (2^25) g (2^25) ∧ agreementLE E (2^25) f (193*2^27/512-1) ∧
      nativeGoldPaddedCountSharp≤(nonzeroBadChallenges E (2^25) f g (16193*2^27/32768)).card := by
  classical
  dsimp only
  let D' := D.map φ.toAddMonoidHom
  let : Fintype D' := Fintype.ofFinite _
  let : Fintype (Module.Dual (ZMod 2) D) := Fintype.ofInjective
    (fun l : Module.Dual (ZMod 2) D => (l : D → ZMod 2)) DFunLike.coe_injective
  obtain ⟨β,hβ,Z,hZ,hdata⟩ := exists_gold_padding_pool_sharp φ D 27 6 hD e (by decide) (by decide)
    (by rw [hF]; norm_num) nativeGoldListSize hL
  have hZ' : nativeGoldPoleCountSharp≤Z.card := by
    simpa only [nativeGoldPoleCountSharp,Nat.cast_pow,Nat.cast_ofNat,hF,show 2^27/2^(2*6)=(2^15:ℕ) by norm_num] using hZ
  let E0 := additiveDomain D'
  let f0 : F → F := fun x => (binaryQuarterNumerator D' β).eval x*(x-β)⁻¹
  let g0 : F → F := fun x => (x-β)⁻¹
  have hd : Module.finrank (ZMod 2) D=27 := by simpa using Module.finrank_eq_card_basis e
  have hβE : β∉E0 := fun h => hβ ((mem_additiveDomain _ _).mp h)
  let j : D →+ F := φ.toAddMonoidHom.comp D.subtype
  have hj : Function.Injective j := fun x y h => Subtype.ext (φ.injective h)
  obtain ⟨A,hA,hAβ,hA',hbad⟩ := exists_polynomial_padding_with_property_exact E0
    (mappedSubgroupDomainEquiv φ D) β hβE (fun x => f0 x) (fun x => g0 x) Z
    27 12 19 ((2^27/2-2^27/2^7)/2) (2^27/2-2^27/2^7) (16193*2^27/32768)
    hd (by decide) (by decide) (by norm_num)
    (fun A => A.derivative.natDegree≤0)
    (exists_additive_padding_locator E0 (mappedSubgroupDomainEquiv φ D) β hβE j hj (fun _ => rfl)) (by
      intro z hz
      obtain ⟨hne,p,hp,H,hH,S,hS,hinv,hmatch⟩ := hdata z hz
      exact ⟨hne,p,hp,H,hH,S,hS,hinv,hmatch⟩)
  have hbad' : nativeGoldPaddedCountSharp≤
      (nonzeroBadChallenges E0 (2^25) (fun x => A.eval (x:F)*f0 x)
        (fun x => A.eval (x:F)*g0 x) (16193*2^27/32768)).card := by
    have hk : (2^27/2-2^27/2^7)/2+2^19=(2^25:ℕ) := by norm_num
    rw [hk] at hbad
    unfold nativeGoldPaddedCountSharp
    apply le_trans (Nat.ceil_mono ?_) hbad
    apply mul_le_mul_of_nonneg_left (by exact_mod_cast hZ')
    unfold paddingRetentionProbability
    exact div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  rw [mappedDomain_affineDomain,mappedDomain_additiveDomain]
  let E := affineDomain E0 (φ a)
  let f1 : F → F := fun x => A.eval x*f0 x
  let g1 : F → F := fun x => A.eval x*g0 x
  have hcard : 2^25≤E.card := by
    rw [card_affineDomain,card_additiveDomain,natCard_map_addSubgroup,hD]
    norm_num
  have hg0 : agreementLE E0 (2^25) (fun x => g1 x) (2^25) := by
    simpa only [g1,g0,div_eq_mul_inv] using agreementLE_polynomialOverPole E0 β hβE A (2^25)
      (by rw [hA]; norm_num) hAβ
  have hg : agreementLE E (2^25) (fun x => g1 ((x:F)-φ a)) (2^25) :=
    agreementLE_affineDomain E0 (φ a) g1 _ _ hg0
  refine ⟨(fun x => f1 ((x:F)-φ a)),(fun x => g1 ((x:F)-φ a)),
    ⟨commonAgreementGE_of_le_card E _ _ _ hcard,commonAgreementLE_of_right E _ _ _ _ hg⟩,
    ⟨agreementGE_of_le_card E _ _ hcard,hg⟩,?_,?_⟩
  · apply agreementLE_affineDomain E0 (φ a) f1
    have hcD : Fintype.card D'=4*2^25 := by
      rw [←Nat.card_eq_fintype_card,natCard_map_addSubgroup,hD]
      norm_num
    have hf := agreementLE_padded_binaryQuarterSource D' β hβ (2^25) ⟨25,rfl⟩ hcD (2^19)
      (by norm_num) (by norm_num) (by decide) A hA.le hA' hAβ
    simpa only [f1,f0,mul_assoc,show 3*2^25/2+2^19/2-1=193*2^27/512-1 by norm_num] using hf
  · simp only [nonzeroBadChallenges]
    rw [badChallenges_affineDomain E0 (φ a) f1 g1]
    exact hbad'
end BinaryFieldCounterexamples.Gold
