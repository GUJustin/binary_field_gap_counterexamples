/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingAssembly
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingPool
/-!
# Half-rate Gold padding

The radical-invariant pooled witnesses are padded by one subspace locator.
Exact union counts give the stated threshold, and the excluded pole preserves
the common-agreement obstruction on every prescribed affine translate.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
/-- Coordinates identify a subgroup with its image domain. -/
noncomputable def mappedSubgroupDomainEquiv
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] (φ : B →+* F) (D : AddSubgroup B) :
    D ≃ additiveDomain (D.map φ.toAddMonoidHom) :=
  Equiv.ofBijective (fun x => ⟨φ (x:B),(mem_additiveDomain _ _).mpr ⟨x,x.property,rfl⟩⟩) (by
    constructor
    · intro x y h
      apply Subtype.ext
      exact φ.injective (congrArg Subtype.val h)
    · intro y
      obtain ⟨x,hx,he⟩ := (mem_additiveDomain _ _).mp y.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩)
/-- The coordinate equivalence is the specified field embedding on values. -/
theorem mappedSubgroupDomainEquiv_apply
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] (φ : B →+* F) (D : AddSubgroup B) (x:D) :
    ((mappedSubgroupDomainEquiv φ D x : additiveDomain (D.map φ.toAddMonoidHom)):F)=φ (x:B) := by
  rfl
/-- The half-rate padding threshold satisfies the exact union-count identity. -/
theorem halfRate_padding_count (d t : ℕ) (ht : 2≤t) (hpad : 2*t≤d-2) :
    (5*2^d/8-3*2^d/2^(t+3))*2^d=
      2^(d-2)*2^d+(2^d-2^(d-2))*(2^d/2-2^d/2^(t+1)) := by
  have hd : t+3≤d := by omega
  let a := 2^(d-(t+3))
  let b := 2^t
  have hN : 2^d=a*b*8 := by
    dsimp [a,b]
    change 2^d=2^(d-(t+3))*2^t*2^3
    rw [←pow_add,←pow_add]
    congr 1
    omega
  have hK : 2^(d-2)=a*b*2 := by
    dsimp [a,b]
    rw [←pow_add,←pow_succ]
    congr 1
    omega
  have hb : 4≤b := by
    exact Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) ht
  have ht1 : 2^(t+1)=b*2 := by simp [b,pow_succ]
  have ht3 : 2^(t+3)=b*8 := by simp [b,pow_add]
  have hbpos : 0<b := by dsimp [b]; positivity
  rw [hN,hK,ht1,ht3]
  have hdiv : 3*(a*b*8)/(b*8)=3*a := by
    rw [show 3*(a*b*8)=(3*a)*(b*8) by ring,Nat.mul_div_cancel _ (by positivity : 0<b*8)]
  have hdiv' : a*b*8/(b*2)=a*4 := by
    rw [show a*b*8=(a*4)*(b*2) by ring,Nat.mul_div_cancel _ (by positivity : 0<b*2)]
  rw [hdiv,hdiv']
  have hdiv5 : 5*(a*b*8)/8=5*(a*b) := by omega
  have hdiv2 : a*b*8/2=a*b*4 := by omega
  rw [hdiv5,hdiv2]
  have hab : 4*a≤a*b := by
    simpa only [Nat.mul_comm a 4] using Nat.mul_le_mul_left a hb
  have hs1 : 3*a≤5*(a*b) := by omega
  have hs2 : a*4≤a*b*4 := by omega
  have he1 := Nat.sub_add_cancel hs1
  have he2 := Nat.sub_add_cancel hs2
  have hdiff : a*b*8-a*b*2=a*b*6 := by omega
  apply Nat.add_right_cancel (m := 3*a*(a*b*8))
  calc
    (5*(a*b)-3*a)*(a*b*8)+3*a*(a*b*8) = 5*(a*b)*(a*b*8) := by
      rw [←Nat.add_mul,he1]
    _ = a*b*2*(a*b*8)+a*b*6*(a*b*4) := by ring
    _ = a*b*2*(a*b*8)+a*b*6*((a*b*4-a*4)+a*4) := by rw [he2]
    _ = a*b*2*(a*b*8)+(a*b*8-a*b*2)*(a*b*4-a*4)+3*a*(a*b*8) := by
      rw [hdiff]
      ring
/-- The retained half-rate fraction is nonnegative under the padding guard. -/
theorem halfRate_retention_nonneg (d t : ℕ) (ht : 2≤t) (hpad : 2*t≤d-2) :
    0≤1-3*((4:ℚ)^t-1)/((2:ℚ)^d-1) := by
  have h4 : (4:ℚ)^t=(2:ℚ)^(2*t) := by rw [pow_mul]; norm_num
  have hpow : (2:ℚ)^(2*t)≤(2:ℚ)^(d-2) := by gcongr; norm_num
  have hN : (2:ℚ)^d=(2:ℚ)^(d-2)*4 := by
    calc
      (2:ℚ)^d=2^((d-2)+2) := by congr 1; omega
      _=_ := by rw [pow_add]; norm_num
  have hp : 1≤(2:ℚ)^(d-2) := one_le_pow₀ (by norm_num)
  rw [h4]
  have hden : 0<(2:ℚ)^d-1 := by rw [hN]; linarith
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hden).mpr
  rw [hN]
  linarith
/-- Exact collision pooling and invariant-set padding give half-rate pairs on the prescribed affine domain. -/
theorem gold_half_rate_from_tensor_lower_bound
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B) (d t : ℕ)
    (hD : Nat.card D=2^d) (e : Module.Basis (Fin d) (ZMod 2) D)
    (ht : 2≤t) (hpad : 2*t≤d-2) (hq : 2^d<Fintype.card F)
    (L : ℕ) (hL : L≤(momentTensors D (basisParameter D e) t).card*2^(2*t)) :
    let N : ℕ := 2^d
    let δ : ℕ := N/2^(2*t)
    let Zbound := ⌈(L:ℚ)*((Fintype.card F:ℚ)-N)/
      ((Fintype.card F:ℚ)-N+δ*((L:ℚ)-1))⌉₊-1
    let ε : ℚ := 3*(4^t-1)/(N-1)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F, commonAgreementEQ E (N/2) f g (N/2) ∧
      ⌈(1-ε)*Zbound⌉₊≤(nonzeroBadChallenges E (N/2) f g (5*N/8-3*N/2^(t+3))).card := by
  classical
  dsimp only
  let D' := D.map φ.toAddMonoidHom
  let : Fintype D' := Fintype.ofFinite _
  let : Fintype (Module.Dual (ZMod 2) D) := Fintype.ofInjective (fun l : Module.Dual (ZMod 2) D => (l : D → ZMod 2)) DFunLike.coe_injective
  obtain ⟨β,hβ,Z,hZ,hdata⟩ := exists_gold_padding_pool φ D d t hD e ht (by omega) hq L hL
  let E0 := additiveDomain D'
  let f0 : F → F := fun x => (binaryQuarterNumerator D' β).eval x*(x-β)⁻¹
  let g0 : F → F := fun x => (x-β)⁻¹
  have hd : Module.finrank (ZMod 2) D=d := by simpa using Module.finrank_eq_card_basis e
  have hK : 2^d/2=2^(d-2)+2^(d-2) := by
    have he : d-2+1=d-1 := by omega
    rw [show 2^d/2=2^(d-1) by exact Nat.pow_div (by omega : 1≤d) (by decide : 0<(2:ℕ))]
    rw [←he,pow_succ]
    omega
  have hsmall : (2^d/2-2^d/2^(t+1))/2≤2^(d-2) := by
    apply (Nat.div_le_div_right (Nat.sub_le _ _)).trans
    rw [Nat.div_div_eq_div_mul]
    change 2^d/2^2≤2^(d-2)
    rw [Nat.pow_div (by omega) (by decide : 0<(2:ℕ))]
  have hβE : β∉E0 := fun h => hβ ((mem_additiveDomain _ _).mp h)
  obtain ⟨A,hA,hAβ,hbad⟩ := exists_polynomial_padding E0 (mappedSubgroupDomainEquiv φ D) β hβE
    (fun x => f0 x) (fun x => g0 x) Z d (2*t) (d-2) (2^(d-2))
    (2^d/2-2^d/2^(t+1)) (5*2^d/8-3*2^d/2^(t+3)) hd (by omega) (by omega) (by omega)
    (halfRate_padding_count d t ht hpad) (by
      intro z hz
      obtain ⟨hne,p,hp,H,hH,S,hS,hinv,hmatch⟩ := hdata z hz
      refine ⟨hne,p,hp.trans_le (by exact_mod_cast hsmall),H,hH,S,hS,hinv,?_⟩
      intro x
      exact hmatch x)
  have heps : ((2:ℚ)^(2*t)-1)*(2^(d-(d-2))-1)/(2^d-1)=3*((4:ℚ)^t-1)/(2^d-1) := by
    rw [show d-(d-2)=2 by omega,pow_mul]
    norm_num
    ring
  rw [heps,←hK] at hbad
  have hbad' : ⌈(1-3*((4:ℚ)^t-1)/(2^d-1))*
      (⌈(L:ℚ)*((Fintype.card F:ℚ)-(2^d:ℕ))/
        ((Fintype.card F:ℚ)-(2^d:ℕ)+(2^d/2^(2*t):ℕ)*((L:ℚ)-1))⌉₊-1 : ℕ)⌉₊≤
      (nonzeroBadChallenges E0 (2^d/2) (fun x => A.eval (x:F)*f0 x)
        (fun x => A.eval (x:F)*g0 x) (5*2^d/8-3*2^d/2^(t+3))).card := by
    apply le_trans (Nat.ceil_mono ?_) hbad
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hZ) (halfRate_retention_nonneg d t ht hpad)
  rw [mappedDomain_affineDomain,mappedDomain_additiveDomain]
  let E := affineDomain E0 (φ a)
  let f1 : F → F := fun x => A.eval x*f0 x
  let g1 : F → F := fun x => A.eval x*g0 x
  refine ⟨(fun x => f1 ((x:F)-φ a)),(fun x => g1 ((x:F)-φ a)),?_,?_⟩
  · have hcard : 2^d/2≤E.card := by
      rw [card_affineDomain,card_additiveDomain,natCard_map_addSubgroup,hD]
      exact Nat.div_le_self _ _
    refine ⟨commonAgreementGE_of_le_card E _ _ _ hcard,commonAgreementLE_of_right E _ _ _ _ ?_⟩
    apply agreementLE_affineDomain E0 (φ a) g1
    simpa only [g1,g0,div_eq_mul_inv] using agreementLE_polynomialOverPole E0 β hβE A (2^d/2)
      (by rw [hA,hK]; omega) hAβ
  · simp only [nonzeroBadChallenges]
    rw [badChallenges_affineDomain E0 (φ a) f1 g1]
    simpa only [nonzeroBadChallenges,Nat.cast_pow,Nat.cast_ofNat] using hbad'
/-- Both collision bounds followed by exact subspace retention give the strengthened half-rate theorem. -/
theorem gold_half_rate_from_tensor_lower_bound_sharp
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B) (d t : ℕ)
    (hD : Nat.card D=2^d) (e : Module.Basis (Fin d) (ZMod 2) D)
    (ht : 2≤t) (hpad : 2*t≤d-2) (hq : 2^d<Fintype.card F)
    (L : ℕ) (hL : L≤(momentTensors D (basisParameter D e) t).card*2^(2*t)) :
    let N : ℕ := 2^d
    let δ : ℕ := N/2^(2*t)
    let Zbound := max (L-(δ*L.choose 2)/(Fintype.card F-N)) ⌈(L:ℚ)*((Fintype.card F:ℚ)-N)/
      ((Fintype.card F:ℚ)-N+δ*((L:ℚ)-1))⌉₊
    let p := paddingRetentionProbability d (d-2) (2*t)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F, commonAgreementEQ E (N/2) f g (N/2) ∧
      ⌈p*Zbound⌉₊≤(nonzeroBadChallenges E (N/2) f g (5*N/8-3*N/2^(t+3))).card := by
  classical
  dsimp only
  let D' := D.map φ.toAddMonoidHom
  let : Fintype D' := Fintype.ofFinite _
  let : Fintype (Module.Dual (ZMod 2) D) := Fintype.ofInjective (fun l : Module.Dual (ZMod 2) D => (l : D → ZMod 2)) DFunLike.coe_injective
  obtain ⟨β,hβ,Z,hZ,hdata⟩ := exists_gold_padding_pool_sharp φ D d t hD e ht (by omega) hq L hL
  let E0 := additiveDomain D'
  let f0 : F → F := fun x => (binaryQuarterNumerator D' β).eval x*(x-β)⁻¹
  let g0 : F → F := fun x => (x-β)⁻¹
  have hd : Module.finrank (ZMod 2) D=d := by simpa using Module.finrank_eq_card_basis e
  have hK : 2^d/2=2^(d-2)+2^(d-2) := by
    have he : d-2+1=d-1 := by omega
    rw [show 2^d/2=2^(d-1) by exact Nat.pow_div (by omega : 1≤d) (by decide : 0<(2:ℕ))]
    rw [←he,pow_succ]
    omega
  have hsmall : (2^d/2-2^d/2^(t+1))/2≤2^(d-2) := by
    apply (Nat.div_le_div_right (Nat.sub_le _ _)).trans
    rw [Nat.div_div_eq_div_mul]
    change 2^d/2^2≤2^(d-2)
    rw [Nat.pow_div (by omega) (by decide : 0<(2:ℕ))]
  have hβE : β∉E0 := fun h => hβ ((mem_additiveDomain _ _).mp h)
  obtain ⟨A,hA,hAβ,hbad⟩ := exists_polynomial_padding_exact E0 (mappedSubgroupDomainEquiv φ D) β hβE
    (fun x => f0 x) (fun x => g0 x) Z d (2*t) (d-2) (2^(d-2))
    (2^d/2-2^d/2^(t+1)) (5*2^d/8-3*2^d/2^(t+3)) hd hpad (by omega)
    (halfRate_padding_count d t ht hpad) (by
      intro z hz
      obtain ⟨hne,p,hp,H,hH,S,hS,hinv,hmatch⟩ := hdata z hz
      refine ⟨hne,p,hp.trans_le (by exact_mod_cast hsmall),H,hH,S,hS,hinv,?_⟩
      intro x
      exact hmatch x)
  rw [←hK] at hbad
  have hbad' : ⌈paddingRetentionProbability d (d-2) (2*t)*
      (max (L-((2^d/2^(2*t))*L.choose 2)/(Fintype.card F-2^d)) ⌈(L:ℚ)*((Fintype.card F:ℚ)-(2^d:ℕ))/
        ((Fintype.card F:ℚ)-(2^d:ℕ)+(2^d/2^(2*t):ℕ)*((L:ℚ)-1))⌉₊ : ℕ)⌉₊≤
      (nonzeroBadChallenges E0 (2^d/2) (fun x => A.eval (x:F)*f0 x)
        (fun x => A.eval (x:F)*g0 x) (5*2^d/8-3*2^d/2^(t+3))).card := by
    apply le_trans (Nat.ceil_mono ?_) hbad
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hZ) (by unfold paddingRetentionProbability; positivity)
  rw [mappedDomain_affineDomain,mappedDomain_additiveDomain]
  let E := affineDomain E0 (φ a)
  let f1 : F → F := fun x => A.eval x*f0 x
  let g1 : F → F := fun x => A.eval x*g0 x
  refine ⟨(fun x => f1 ((x:F)-φ a)),(fun x => g1 ((x:F)-φ a)),?_,?_⟩
  · have hcard : 2^d/2≤E.card := by
      rw [card_affineDomain,card_additiveDomain,natCard_map_addSubgroup,hD]
      exact Nat.div_le_self _ _
    refine ⟨commonAgreementGE_of_le_card E _ _ _ hcard,commonAgreementLE_of_right E _ _ _ _ ?_⟩
    apply agreementLE_affineDomain E0 (φ a) g1
    simpa only [g1,g0,div_eq_mul_inv] using agreementLE_polynomialOverPole E0 β hβE A (2^d/2)
      (by rw [hA,hK]; omega) hAβ
  · simp only [nonzeroBadChallenges]
    rw [badChallenges_affineDomain E0 (φ a) f1 g1]
    simpa only [nonzeroBadChallenges,Nat.cast_pow,Nat.cast_ofNat] using hbad'
end BinaryFieldCounterexamples.Gold

