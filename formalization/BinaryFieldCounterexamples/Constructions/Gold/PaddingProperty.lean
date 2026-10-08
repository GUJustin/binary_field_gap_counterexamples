/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingAssembly
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingSourceBound
/-!
# Padding with an additional proved locator property

The finite padding argument preserves any property of the actual chosen locator.
For additive embeddings, use the concrete image subgroup locator: its roots are
exactly the selected subspace and its formal derivative is constant. This supplies
the extra hypothesis for the first-input bound required by the native finite example.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial Module
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {F : Type*} [Field F]
theorem exists_polynomial_padding_with_property [Fintype F] [Fintype (Dual (ZMod 2) V)]
    (E : Finset F) (e : V ≃ E) (β : F) (hβ : β ∉ E)
    (f g : E → F) (Z : Finset F) (d r w K T U : ℕ)
    (hd : finrank (ZMod 2) V=d) (hw : w≤d) (hr : r≤d) (hd0 : 0<d)
    (hcount : U*2^d=2^w*2^d+(2^d-2^w)*T)
    (P : F[X] → Prop)
    (hlocator : ∀ W : Submodule (ZMod 2) V, ∃ A : F[X], A.natDegree=Fintype.card W ∧
      A.eval β≠0 ∧ (∀ x : V, A.eval (e x:F)=0 ↔ x ∈ W) ∧ P A)
    (hdata : ∀ z ∈ Z, z≠0 ∧ ∃ p : F[X], p.degree<K ∧
      ∃ H : Submodule (ZMod 2) V, finrank (ZMod 2) H=d-r ∧
        ∃ S : Finset V, S.card=T ∧
          (∀ x : V, ∀ h : H, x+(h:V) ∈ S ↔ x ∈ S) ∧
          ∀ x : V, f (e x)+z*g (e x)=p.eval (e x:F) ↔ x ∈ S) :
    ∃ A : F[X], A.natDegree=2^w ∧ A.eval β≠0 ∧ P A ∧
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
  obtain ⟨A,hA,hAβ,hroot,hPA⟩ := hlocator W
  refine ⟨A,hA.trans hcW,hAβ,hPA,?_⟩
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
/-- Exact subspace retention preserves any property of the chosen padding locator. -/
theorem exists_polynomial_padding_with_property_exact [Fintype F] [Fintype (Dual (ZMod 2) V)]
    (E : Finset F) (e : V ≃ E) (β : F) (hβ : β ∉ E)
    (f g : E → F) (Z : Finset F) (d r w K T U : ℕ)
    (hd : finrank (ZMod 2) V=d) (hrw : r≤w) (hw : w≤d)
    (hcount : U*2^d=2^w*2^d+(2^d-2^w)*T)
    (P : F[X] → Prop)
    (hlocator : ∀ W : Submodule (ZMod 2) V, ∃ A : F[X], A.natDegree=Fintype.card W ∧
      A.eval β≠0 ∧ (∀ x : V, A.eval (e x:F)=0 ↔ x ∈ W) ∧ P A)
    (hdata : ∀ z ∈ Z, z≠0 ∧ ∃ p : F[X], p.degree<K ∧
      ∃ H : Submodule (ZMod 2) V, finrank (ZMod 2) H=d-r ∧
        ∃ S : Finset V, S.card=T ∧
          (∀ x : V, ∀ h : H, x+(h:V) ∈ S ↔ x ∈ S) ∧
          ∀ x : V, f (e x)+z*g (e x)=p.eval (e x:F) ↔ x ∈ S) :
    ∃ A : F[X], A.natDegree=2^w ∧ A.eval β≠0 ∧ P A ∧
      ⌈paddingRetentionProbability d w r*Z.card⌉₊ ≤
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
  obtain ⟨A,hA,hAβ,hroot,hPA⟩ := hlocator W
  refine ⟨A,hA.trans hcW,hAβ,hPA,?_⟩
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
  have hsmall : ⌈paddingRetentionProbability d w r*Z.card⌉₊≤G'.card := by
    simpa only [G',Finset.card_map,Finset.card_univ,Fintype.card_coe] using hret
  exact hsmall.trans hbound
theorem exists_additive_padding_locator [Fintype F] [CharP F 2]
    (E : Finset F) (e : V ≃ E) (β : F) (hβ : β ∉ E)
    (j : V →+ F) (hj : Function.Injective j) (he : ∀ x : V, j x=(e x:F))
    (W : Submodule (ZMod 2) V) :
    ∃ A : F[X], A.natDegree=Fintype.card W ∧ A.eval β≠0 ∧
      (∀ x : V, A.eval (e x:F)=0 ↔ x ∈ W) ∧ A.derivative.natDegree≤0 := by
  classical
  let U := W.toAddSubgroup.map j
  letI : Fintype U := Fintype.ofFinite U
  refine ⟨subspacePolynomial U,?_,?_,?_,?_⟩
  · rw [subspacePolynomial_natDegree]
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card]
    exact AddSubgroup.card_map_of_injective hj
  · rw [ne_eq,subspacePolynomial_eval_eq_zero_iff]
    intro h
    obtain ⟨x,hx,hjx⟩ := h
    exact hβ (hjx ▸ (he x ▸ (e x).property))
  · intro x
    rw [subspacePolynomial_eval_eq_zero_iff,←he x]
    constructor
    · rintro ⟨y,hy,hyx⟩
      exact hj hyx ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  · rw [derivative_eq_C_of_binarySupport _ (subspacePolynomial_support U)]
    simp
end BinaryFieldCounterexamples.Gold
