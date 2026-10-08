/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Domains
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Exact fibers of additive polynomials

Evaluation of an additive polynomial is an additive homomorphism. Once the
polynomial splits with as many distinct roots as its degree, every nonempty
fiber has exactly that degree, so the inverse image of an embedded finite field
has the product cardinality claimed in the preimage construction.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.NearUnit
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Evaluation of a polynomial satisfying the literal addition identity is an
additive homomorphism. -/
noncomputable def additivePolynomialEval
    {F : Type*} [Field F] (P : F[X])
    (hadd : ∀x y : F,P.eval (x+y)=P.eval x+P.eval y) : F→+F :=
  { toFun := fun x => P.eval x
    map_zero' := by
      have h := hadd 0 0
      simp only [zero_add] at h
      have hz := congrArg (fun z : F => z-P.eval 0) h
      simpa only [sub_self,add_sub_cancel_right] using hz.symm
    map_add' := hadd }

/-- The additive evaluation kernel has the exact split-root cardinality. -/
theorem additivePolynomialEval_kernel_card
    {F : Type*} [Field F] [Fintype F]
    (P : F[X]) (hP : P≠0)
    (hadd : ∀x y : F,P.eval (x+y)=P.eval x+P.eval y) :
    (Finset.univ.filter fun x : F => additivePolynomialEval P hadd x=0).card=
      P.roots.toFinset.card := by
  apply congrArg Finset.card
  ext x
  rw [Finset.mem_filter,Multiset.mem_toFinset,mem_roots hP]
  simp only [Finset.mem_univ,true_and,additivePolynomialEval]
  rfl

/-- A monic separable additive polynomial with all its roots in the field pulls
an embedded finite field back to exactly `degree * field-size` points. -/
theorem additivePolynomial_preimage_card
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F]
    (ι : B→+*F) (P : F[X]) (hmonic : P.Monic) (_hsep : P.Separable)
    (hadd : ∀x y : F,P.eval (x+y)=P.eval x+P.eval y)
    (hsplit : P.roots.toFinset.card=P.natDegree)
    (himage : ∀b : B,∃x : F,P.eval x=ι b) :
    (Finset.univ.filter fun x : F => ∃b : B,P.eval x=ι b).card=
      P.natDegree*Fintype.card B := by
  let f := additivePolynomialEval P hadd
  let Y := mappedDomain ι (Finset.univ : Finset B)
  have hkernel : (Finset.univ.filter fun x : F => f x=0).card=P.natDegree := by
    rw [additivePolynomialEval_kernel_card P hmonic.ne_zero hadd,hsplit]
  have hY : Y.card=Fintype.card B := by
    change (mappedDomain ι (Finset.univ : Finset B)).card=Fintype.card B
    rw [card_mappedDomain,Finset.card_univ]
  have hfiber : ∀y∈Y,(Finset.univ.filter fun x : F => f x=y).card=P.natDegree := by
    intro y hy
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x,hx⟩ := himage b
    have hyrange : ι b∈Set.range f := ⟨x,hx⟩
    have hzerorange : (0:F)∈Set.range f := ⟨0,f.map_zero⟩
    rw [AddMonoidHom.card_fiber_eq_of_mem_range f hyrange hzerorange]
    exact hkernel
  have hsum := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset F) Y f
  have hpre : (Finset.univ.filter fun x : F => f x∈Y).card=
      P.natDegree*Fintype.card B := by
    rw [←hsum,Finset.sum_const_nat hfiber,hY,mul_comm]
  have heq : (Finset.univ.filter fun x : F => ∃b : B,P.eval x=ι b)=
      (Finset.univ.filter fun x : F => f x∈Y) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,f,Y,additivePolynomialEval,mappedDomain]
    constructor
    · rintro ⟨b,hb⟩
      exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,hb.symm⟩
    · intro hx
      obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hx
      exact ⟨b,he.symm⟩
  rw [heq]
  exact hpre

end BinaryFieldCounterexamples.NearUnit
