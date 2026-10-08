/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.DualRetention
public import BinaryFieldCounterexamples.Constructions.Gold.ExactRetention
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingIntersections
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingPolynomials
/-!
# Polynomial padding of a retained invariant family

Construct the actual monic locator of a selected subspace, transported through a
bijection to the evaluation domain. Its exact root set turns multiplication into
the set union counted by radical invariance. The selected nonzero challenges remain
distinct, all witness degrees are strict, and the retained count keeps the exact
rational fraction and natural ceiling. An excluded pole remains a nonroot.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial Module
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {F : Type*} [Field F]
theorem exists_padding_locator (E : Finset F) (e : V ≃ E) (β : F) (hβ : β ∉ E)
    (W : Submodule (ZMod 2) V) :
    ∃ A : F[X], A.natDegree=Fintype.card W ∧ A.eval β≠0 ∧
      ∀ x : V, A.eval (e x:F)=0 ↔ x ∈ W := by
  classical
  let A : F[X] := ∏ w : W, (X-C (e (w:V):F))
  refine ⟨A,?_,?_,?_⟩
  · simp [A]
  · intro hz
    have hz' : ∃ w : W, β=(e (w:V):F) := by
      simpa only [A,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_eq_zero_iff,
        Finset.mem_univ,true_and,sub_eq_zero] using hz
    obtain ⟨w,hw⟩ := hz'
    exact hβ (hw ▸ (e (w:V)).property)
  · intro x
    simp only [A,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_eq_zero_iff,
      Finset.mem_univ,true_and,sub_eq_zero]
    constructor
    · rintro ⟨w,hw⟩
      have he : e x=e (w:V) := Subtype.ext hw
      exact e.injective he ▸ w.property
    · intro hx
      exact ⟨⟨x,hx⟩,rfl⟩
theorem card_padding_union_transport (E : Finset F) (e : V ≃ E)
    (W : Submodule (ZMod 2) V) (S : Finset V) (A p : F[X]) (f g : E → F) (z : F)
    (hA : ∀ x : V, A.eval (e x:F)=0 ↔ x ∈ W)
    (hp : ∀ x : V, f (e x)+z*g (e x)=p.eval (e x:F) ↔ x ∈ S) :
    ((Finset.univ.filter fun x : E => A.eval (x:F)=0) ∪
      (Finset.univ.filter fun x : E => f x+z*g x=p.eval (x:F))).card =
      ((Finset.univ.filter fun x : V => x ∈ W) ∪ S).card := by
  classical
  have he : ((Finset.univ.filter fun x : V => x ∈ W) ∪ S).map e.toEmbedding =
      ((Finset.univ.filter fun x : E => A.eval (x:F)=0) ∪
        (Finset.univ.filter fun x : E => f x+z*g x=p.eval (x:F))) := by
    ext x
    obtain ⟨v,rfl⟩ := e.surjective x
    simp only [Finset.mem_map_equiv,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,
      true_and,hA,hp,Equiv.symm_apply_apply]
  rw [←he,Finset.card_map]
theorem exists_polynomial_padding [Fintype F] [Fintype (Dual (ZMod 2) V)]
    (E : Finset F) (e : V ≃ E) (β : F) (hβ : β ∉ E)
    (f g : E → F) (Z : Finset F) (d r w K T U : ℕ)
    (hd : finrank (ZMod 2) V=d) (hw : w≤d) (hr : r≤d) (hd0 : 0<d)
    (hcount : U*2^d=2^w*2^d+(2^d-2^w)*T)
    (hdata : ∀ z ∈ Z, z≠0 ∧ ∃ p : F[X], p.degree<K ∧
      ∃ H : Submodule (ZMod 2) V, finrank (ZMod 2) H=d-r ∧
        ∃ S : Finset V, S.card=T ∧
          (∀ x : V, ∀ h : H, x+(h:V) ∈ S ↔ x ∈ S) ∧
          ∀ x : V, f (e x)+z*g (e x)=p.eval (e x:F) ↔ x ∈ S) :
    ∃ A : F[X], A.natDegree=2^w ∧ A.eval β≠0 ∧
      ⌈(1-((2:ℚ)^r-1)*(2^(d-w)-1)/(2^d-1))*Z.card⌉₊ ≤
        (nonzeroBadChallenges E (K+2^w)
          (fun x => A.eval (x:F)*f x) (fun x => A.eval (x:F)*g x) U).card := by
  classical
  choose p hp H hH S hS hinv hag using (fun z : Z => (hdata z z.property).2)
  obtain ⟨W,hW,hret⟩ := exists_padding_subspace_retaining (Finset.univ : Finset Z)
    H d r w hd hw hr hd0 (fun z _ => hH z)
  have hcW : Fintype.card W=2^w := by
    rw [←Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K := ZMod 2),hW]
    simp [Nat.card_eq_fintype_card]
  have hcV : Fintype.card V=2^d := by
    rw [←Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K := ZMod 2),hd]
    simp [Nat.card_eq_fintype_card]
  obtain ⟨A,hA,hAβ,hroot⟩ := exists_padding_locator E e β hβ W
  refine ⟨A,hA.trans hcW,hAβ,?_⟩
  let G := (Finset.univ : Finset Z).filter (fun z => W ⊔ H z=⊤)
  let G' := G.map ⟨Subtype.val,Subtype.val_injective⟩
  have hbound : G'.card≤(nonzeroBadChallenges E (K+2^w)
      (fun x => A.eval (x:F)*f x) (fun x => A.eval (x:F)*g x) U).card := by
    apply nonzeroBadChallenges_padding E f g A K (2^w) U (by omega) G'
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
    refine ⟨(hdata i i.property).1,p i,hp i,?_⟩
    change U≤((Finset.univ.filter fun x : E => A.eval (x:F)=0) ∪
      (Finset.univ.filter fun x : E => f x+(i:F)*g x=(p i).eval (x:F))).card
    rw [card_padding_union_transport E e W (S i) A (p i) f g i hroot (hag i)]
    have hWH : W ⊔ H i=⊤ := (Finset.mem_filter.mp hi).2
    have hc := card_union_of_radical_invariance W (H i) hWH (S i) (hinv i)
    rw [hcW,hcV,hS i,←hcount] at hc
    have he : ((Finset.univ.filter fun x : V => x ∈ W) ∪ S i).card=U :=
      Nat.eq_of_mul_eq_mul_right (by positivity : 0<2^d) hc
    exact he.ge
  have hsmall : ⌈(1-((2:ℚ)^r-1)*(2^(d-w)-1)/(2^d-1))*Z.card⌉₊≤G'.card := by
    simpa only [G',Finset.card_map,Finset.card_univ,Fintype.card_coe] using hret
  exact hsmall.trans hbound
/-- Exact subspace counting retains the full Gaussian probability, including at the boundary `w=r`. -/
theorem exists_polynomial_padding_exact [Fintype F]
    (E : Finset F) (e : V ≃ E) (β : F) (hβ : β ∉ E)
    (f g : E → F) (Z : Finset F) (d r w K T U : ℕ)
    (hd : finrank (ZMod 2) V=d) (hrw : r≤w) (hw : w≤d)
    (hcount : U*2^d=2^w*2^d+(2^d-2^w)*T)
    (hdata : ∀ z ∈ Z, z≠0 ∧ ∃ p : F[X], p.degree<K ∧
      ∃ H : Submodule (ZMod 2) V, finrank (ZMod 2) H=d-r ∧
        ∃ S : Finset V, S.card=T ∧
          (∀ x : V, ∀ h : H, x+(h:V) ∈ S ↔ x ∈ S) ∧
          ∀ x : V, f (e x)+z*g (e x)=p.eval (e x:F) ↔ x ∈ S) :
    ∃ A : F[X], A.natDegree=2^w ∧ A.eval β≠0 ∧
      ⌈(paddingRetentionProbability d w r)*Z.card⌉₊ ≤
        (nonzeroBadChallenges E (K+2^w)
          (fun x => A.eval (x:F)*f x) (fun x => A.eval (x:F)*g x) U).card := by
  classical
  choose p hp H hH S hS hinv hag using (fun z : Z => (hdata z z.property).2)
  obtain ⟨W,hW,hret⟩ := exists_padding_subspace_retaining_exact (Finset.univ : Finset Z)
    H d r w hd hrw hw (fun z _ => hH z)
  have hcW : Fintype.card W=2^w := by
    rw [←Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K := ZMod 2),hW]
    simp [Nat.card_eq_fintype_card]
  have hcV : Fintype.card V=2^d := by
    rw [←Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K := ZMod 2),hd]
    simp [Nat.card_eq_fintype_card]
  obtain ⟨A,hA,hAβ,hroot⟩ := exists_padding_locator E e β hβ W
  refine ⟨A,hA.trans hcW,hAβ,?_⟩
  let G := (Finset.univ : Finset Z).filter (fun z => W ⊔ H z=⊤)
  let G' := G.map ⟨Subtype.val,Subtype.val_injective⟩
  have hbound : G'.card≤(nonzeroBadChallenges E (K+2^w)
      (fun x => A.eval (x:F)*f x) (fun x => A.eval (x:F)*g x) U).card := by
    apply nonzeroBadChallenges_padding E f g A K (2^w) U (by omega) G'
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
    refine ⟨(hdata i i.property).1,p i,hp i,?_⟩
    change U≤((Finset.univ.filter fun x : E => A.eval (x:F)=0) ∪
      (Finset.univ.filter fun x : E => f x+(i:F)*g x=(p i).eval (x:F))).card
    rw [card_padding_union_transport E e W (S i) A (p i) f g i hroot (hag i)]
    have hWH : W ⊔ H i=⊤ := (Finset.mem_filter.mp hi).2
    have hc := card_union_of_radical_invariance W (H i) hWH (S i) (hinv i)
    rw [hcW,hcV,hS i,←hcount] at hc
    have he : ((Finset.univ.filter fun x : V => x ∈ W) ∪ S i).card=U :=
      Nat.eq_of_mul_eq_mul_right (by positivity : 0<2^d) hc
    exact he.ge
  have hsmall : ⌈(paddingRetentionProbability d w r)*Z.card⌉₊≤G'.card := by
    simpa only [G',Finset.card_map,Finset.card_univ,Fintype.card_coe] using hret
  exact hsmall.trans hbound

/-- Exact subspace retention for a pole pair preserves exact common agreement at the padded dimension. -/
theorem exists_pole_padding_exact [Fintype F]
    (E : Finset F) (e : V ≃ E) (β : F) (hβ : β ∉ E)
    (f : E → F) (Z : Finset F) (d r w K T U : ℕ)
    (hd : finrank (ZMod 2) V=d) (hrw : r≤w) (hw : w≤d)
    (hK : K+2^w≤E.card)
    (hcount : U*2^d=2^w*2^d+(2^d-2^w)*T)
    (hdata : ∀ z ∈ Z, z≠0 ∧ ∃ p : F[X], p.degree<K ∧
      ∃ H : Submodule (ZMod 2) V, finrank (ZMod 2) H=d-r ∧
        ∃ S : Finset V, S.card=T ∧
          (∀ x : V, ∀ h : H, x+(h:V) ∈ S ↔ x ∈ S) ∧
          ∀ x : V, f (e x)+z*((e x:F)-β)⁻¹=p.eval (e x:F) ↔ x ∈ S) :
    ∃ A : F[X], A.natDegree=2^w ∧ A.eval β≠0 ∧
      commonAgreementEQ E (K+2^w)
        (fun x => A.eval (x:F)*f x) (fun x => A.eval (x:F)*((x:F)-β)⁻¹) (K+2^w) ∧
      ⌈(paddingRetentionProbability d w r)*Z.card⌉₊ ≤
        (nonzeroBadChallenges E (K+2^w)
          (fun x => A.eval (x:F)*f x) (fun x => A.eval (x:F)*((x:F)-β)⁻¹) U).card := by
  obtain ⟨A,hA,hAβ,hbad⟩ := exists_polynomial_padding_exact E e β hβ f
    (fun x => ((x:F)-β)⁻¹) Z d r w K T U hd hrw hw hcount hdata
  refine ⟨A,hA,hAβ,?_,hbad⟩
  refine ⟨commonAgreementGE_of_le_card E _ _ _ hK,commonAgreementLE_of_right E _ _ _ _ ?_⟩
  simpa only [div_eq_mul_inv] using agreementLE_polynomialOverPole E β hβ A (K+2^w)
    (by rw [hA]; omega) hAβ
end BinaryFieldCounterexamples.Gold
