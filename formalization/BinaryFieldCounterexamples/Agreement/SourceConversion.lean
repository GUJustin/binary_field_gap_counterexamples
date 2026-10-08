/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Agreement.Projection
public import BinaryFieldCounterexamples.Agreement.Domains
/-!
# Proper-extension conversion to equal individual and common agreement

For an element theta outside the base field, the inputs f+theta*g and
f+(theta+1)*g each have agreement exactly equal to the original common
agreement. Base-linear coefficient projections give the upper bounds and
transported witnesses attain them. The fractional-linear challenge map is
injective and nonzero on every old challenge; scaled witnesses preserve agreement
and strict degree. In particular no old challenge, including zero, is lost.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq

theorem commonAgreementCount_eq_card_filter
    {B : Type*} [Field B] (D : Finset B) (f g : B → B) (p r : B[X]) :
    commonAgreementCount D (fun x => f x) (fun x => g x) p r =
      (D.filter fun x => p.eval x=f x ∧ r.eval x=g x).card := by
  unfold commonAgreementCount Code.agree
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Prod.mk.injEq] at hx
    exact Finset.mem_filter.mpr ⟨x.property,hx.1.symm,hx.2.symm⟩
  · intro x _ y _ he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hxD,hx⟩ := Finset.mem_filter.mp hx
    refine ⟨⟨x,hxD⟩,?_,rfl⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Prod.mk.injEq]
    exact ⟨hx.1.symm,hx.2.symm⟩

noncomputable def extensionLinearWord {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (θ : F) (f g : B → B) (x : F) : F :=
  φ (f (Function.invFun φ x))+θ*φ (g (Function.invFun φ x))

theorem extensionLinearWord_apply {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (θ : F) (f g : B → B) (x : B) :
    extensionLinearWord φ θ f g (φ x)=φ (f x)+θ*φ (g x) := by
  simp [extensionLinearWord,Function.leftInverse_invFun φ.injective x]

theorem agreementLE_extensionLinearWord
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (D : Finset B) (K C : ℕ) (f g : B → B)
    (hcommon : commonAgreementLE D K (fun x => f x) (fun x => g x) C)
    (θ : F) (hθ : θ∉Set.range (algebraMap B F)) :
    agreementLE (mappedDomain (algebraMap B F) D) K
      (fun x => extensionLinearWord (algebraMap B F) θ f g x) C := by
  intro p hp
  obtain ⟨l0,l1,h01,h0θ,h11,h1θ⟩ := exists_extension_coordinates θ hθ
  obtain ⟨p0,hp0,he0⟩ := exists_projected_polynomial l0 K p hp
  obtain ⟨p1,hp1,he1⟩ := exists_projected_polynomial l1 K p hp
  have hl (l : F →ₗ[B] B) (b : B) (v : F) : l (algebraMap B F b*v)=b*l v := by
    simpa [Algebra.smul_def] using l.map_smul b v
  have hm0 (b : B) : l0 (algebraMap B F b)=b := by
    simpa [h01] using hl l0 b 1
  have hm1 (b : B) : l1 (algebraMap B F b)=0 := by
    simpa [h11] using hl l1 b 1
  rw [agreementCount_mappedDomain]
  apply le_trans _ (hcommon p0 p1 hp0 hp1)
  rw [commonAgreementCount_eq_card_filter]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxD,hx⟩ := Finset.mem_filter.mp hx
  rw [extensionLinearWord_apply] at hx
  refine Finset.mem_filter.mpr ⟨hxD,?_,?_⟩
  · rw [he0,hx,map_add,hm0,mul_comm θ,hl,h0θ,mul_zero,add_zero]
  · rw [he1,hx,map_add,hm1,mul_comm θ,hl,h1θ,mul_one,zero_add]

noncomputable def extensionLinearPolynomial {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (θ : F) (p r : B[X]) : F[X] := p.map φ+θ • r.map φ

theorem extensionLinearPolynomial_degree_lt {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (θ : F) (p r : B[X]) (K : ℕ) (hp : p.degree<K) (hr : r.degree<K) :
    (extensionLinearPolynomial φ θ p r).degree<K := by
  apply (degree_add_le _ _).trans_lt
  apply max_lt
  · exact (degree_map_le).trans_lt hp
  · exact (degree_smul_le θ _).trans_lt ((degree_map_le).trans_lt hr)

theorem extensionLinearPolynomial_eval {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (θ : F) (p r : B[X]) (x : B) :
    (extensionLinearPolynomial φ θ p r).eval (φ x)=φ (p.eval x)+θ*φ (r.eval x) := by
  simp [extensionLinearPolynomial,eval_map,eval₂_at_apply]

theorem agreementGE_extensionLinearWord
    {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (D : Finset B) (K C : ℕ) (f g : B → B)
    (hcommon : commonAgreementGE D K (fun x => f x) (fun x => g x) C) (θ : F) :
    agreementGE (mappedDomain φ D) K (fun x => extensionLinearWord φ θ f g x) C := by
  obtain ⟨p,r,hp,hr,hcount⟩ := hcommon
  refine ⟨extensionLinearPolynomial φ θ p r,extensionLinearPolynomial_degree_lt φ θ p r K hp hr,?_⟩
  apply hcount.trans
  rw [commonAgreementCount_eq_card_filter,agreementCount_mappedDomain]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxD,hp,hr⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxD,?_⟩
  rw [extensionLinearPolynomial_eval,extensionLinearWord_apply,hp,hr]

theorem agreementEQ_extensionLinearWord
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (D : Finset B) (K C : ℕ) (f g : B → B)
    (hcommon : commonAgreementEQ D K (fun x => f x) (fun x => g x) C)
    (θ : F) (hθ : θ∉Set.range (algebraMap B F)) :
    agreementEQ (mappedDomain (algebraMap B F) D) K
      (fun x => extensionLinearWord (algebraMap B F) θ f g x) C := by
  exact ⟨agreementGE_extensionLinearWord _ D K C f g hcommon.1 θ,
    agreementLE_extensionLinearWord D K C f g hcommon.2 θ hθ⟩

theorem commonAgreementCount_mappedDomain
    {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (D : Finset B) (f g : F → F) (p r : F[X]) :
    commonAgreementCount (mappedDomain φ D) (fun x => f x) (fun x => g x) p r =
      (D.filter fun x => p.eval (φ x)=f (φ x) ∧ r.eval (φ x)=g (φ x)).card := by
  rw [commonAgreementCount_eq_card_filter]
  simp only [mappedDomain,Finset.filter_image]
  exact Finset.card_image_of_injective _ φ.injective

theorem commonAgreementGE_extensionLinearWords
    {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (D : Finset B) (K C : ℕ) (f g : B → B)
    (hcommon : commonAgreementGE D K (fun x => f x) (fun x => g x) C) (θ η : F) :
    commonAgreementGE (mappedDomain φ D) K
      (fun x => extensionLinearWord φ θ f g x) (fun x => extensionLinearWord φ η f g x) C := by
  obtain ⟨p,r,hp,hr,hcount⟩ := hcommon
  refine ⟨extensionLinearPolynomial φ θ p r,extensionLinearPolynomial φ η p r,
    extensionLinearPolynomial_degree_lt φ θ p r K hp hr,
    extensionLinearPolynomial_degree_lt φ η p r K hp hr,?_⟩
  apply hcount.trans
  rw [commonAgreementCount_eq_card_filter,commonAgreementCount_mappedDomain]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxD,hp,hr⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxD,?_,?_⟩ <;>
    rw [extensionLinearPolynomial_eval,extensionLinearWord_apply,hp,hr]

theorem extension_shift_outside_range
    {B F : Type*} [Field B] [Field F] (φ : B →+* F) (θ : F)
    (hθ : θ∉Set.range φ) : θ+1∉Set.range φ := by
  rintro ⟨b,hb⟩
  apply hθ
  refine ⟨b-1,?_⟩
  rw [map_sub,map_one,hb]
  ring

theorem source_conversion_agreements
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (D : Finset B) (K C : ℕ) (f g : B → B)
    (hcommon : commonAgreementEQ D K (fun x => f x) (fun x => g x) C)
    (θ : F) (hθ : θ∉Set.range (algebraMap B F)) :
    let A := mappedDomain (algebraMap B F) D
    let u := fun x : A => extensionLinearWord (algebraMap B F) θ f g x
    let v := fun x : A => extensionLinearWord (algebraMap B F) (θ+1) f g x
    agreementEQ A K u C ∧ agreementEQ A K v C ∧ commonAgreementEQ A K u v C := by
  have hu := agreementEQ_extensionLinearWord D K C f g hcommon θ hθ
  have hv := agreementEQ_extensionLinearWord D K C f g hcommon (θ+1)
    (extension_shift_outside_range _ θ hθ)
  exact ⟨hu,hv,commonAgreementGE_extensionLinearWords _ D K C f g hcommon.1 θ (θ+1),
    commonAgreementLE_of_right _ K _ _ C hv.2⟩

noncomputable def extensionChallenge {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (θ : F) (z : B) : F := (φ z-θ)/(θ+1-φ z)

theorem extensionChallenge_denominator_ne_zero
    {B F : Type*} [Field B] [Field F] (φ : B →+* F) (θ : F)
    (hθ : θ∉Set.range φ) (z : B) : θ+1-φ z≠0 := by
  intro hz
  exact extension_shift_outside_range φ θ hθ ⟨z,(sub_eq_zero.mp hz).symm⟩

theorem extensionChallenge_ne_zero
    {B F : Type*} [Field B] [Field F] (φ : B →+* F) (θ : F)
    (hθ : θ∉Set.range φ) (z : B) : extensionChallenge φ θ z≠0 := by
  apply div_ne_zero _ (extensionChallenge_denominator_ne_zero φ θ hθ z)
  intro hz
  exact hθ ⟨z,sub_eq_zero.mp hz⟩

theorem extensionChallenge_injective
    {B F : Type*} [Field B] [Field F] (φ : B →+* F) (θ : F)
    (hθ : θ∉Set.range φ) : Function.Injective (extensionChallenge φ θ) := by
  intro z w he
  apply φ.injective
  have hc := (div_eq_div_iff (extensionChallenge_denominator_ne_zero φ θ hθ z)
    (extensionChallenge_denominator_ne_zero φ θ hθ w)).mp he
  linear_combination hc

theorem extensionChallenge_word_identity
    {B F : Type*} [Field B] [Field F] (φ : B →+* F) (θ : F)
    (hθ : θ∉Set.range φ) (f g : B → B) (z x : B) :
    extensionLinearWord φ θ f g (φ x)+extensionChallenge φ θ z*
      extensionLinearWord φ (θ+1) f g (φ x)=
      (θ+1-φ z)⁻¹*φ (f x+z*g x) := by
  rw [extensionLinearWord_apply,extensionLinearWord_apply]
  dsimp only [extensionChallenge]
  rw [map_add,map_mul]
  field_simp [extensionChallenge_denominator_ne_zero φ θ hθ z]
  ring

theorem agreementGE_extensionChallenge
    {B F : Type*} [Field B] [Field F] (φ : B →+* F) (θ : F)
    (hθ : θ∉Set.range φ) (D : Finset B) (K T : ℕ) (f g : B → B) (z : B)
    (hz : agreementGE D K (fun x => f x+z*g x) T) :
    agreementGE (mappedDomain φ D) K
      (fun x => extensionLinearWord φ θ f g x+extensionChallenge φ θ z*
        extensionLinearWord φ (θ+1) f g x) T := by
  obtain ⟨p,hp,hcount⟩ := hz
  refine ⟨(θ+1-φ z)⁻¹ • p.map φ,?_,?_⟩
  · exact (degree_smul_le _ _).trans_lt (degree_map_le.trans_lt hp)
  · apply hcount.trans
    rw [agreementCount_eq_card_filter D (fun x : B => f x+z*g x) p,
      agreementCount_mappedDomain φ D (fun x : F => extensionLinearWord φ θ f g x+extensionChallenge φ θ z*
        extensionLinearWord φ (θ+1) f g x)]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxD,hx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxD,?_⟩
    rw [extensionChallenge_word_identity φ θ hθ]
    simp [eval_map,eval₂_at_apply,hx]

theorem card_badChallenges_le_converted_nonzeroBadChallenges
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F]
    (φ : B →+* F) (θ : F) (hθ : θ∉Set.range φ) (D : Finset B)
    (K T : ℕ) (f g : B → B) :
    (badChallenges D K (fun x => f x) (fun x => g x) T).card≤
      (nonzeroBadChallenges (mappedDomain φ D) K
        (fun x => extensionLinearWord φ θ f g x)
        (fun x => extensionLinearWord φ (θ+1) f g x) T).card := by
  rw [←Finset.card_image_of_injective _ (extensionChallenge_injective φ θ hθ)]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
  refine Finset.mem_erase.mpr ⟨extensionChallenge_ne_zero φ θ hθ w,?_⟩
  apply (mem_badChallenges _ _ _ _ _ _).mpr
  exact agreementGE_extensionChallenge φ θ hθ D K T f g w ((mem_badChallenges _ _ _ _ _ _).mp hw)
end BinaryFieldCounterexamples
