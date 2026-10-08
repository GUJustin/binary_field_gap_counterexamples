/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.SubspaceFrobeniusCommute
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import BinaryFieldCounterexamples.Polynomial.LocatorRemainders
/-!
# Quartic right factors of binary locators

For the exact quadratic-line classification, the literal identity
L_D=P^4+ηP^2+ξP and P(0)=0 force P to be additive. For each y the
polynomial P(X+y)+P(X)+P(y) has zero composition with a nonzero quartic,
so is constant; its value at zero is zero. This univariate argument avoids
multivariate total-degree machinery. If P is monic, divisibility and the
separable split locator show P is exactly the locator of a subgroup of D.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
/-- A normalized right factor of the displayed quartic locator composition is
additive. This supplies the root-subspace step of the exact quadratic-line
classification without a multivariate-polynomial total-degree argument. -/
theorem subspacePolynomial_quartic_factor_additive
    {B : Type*} [Field B] [CharP B 2]
    (D : AddSubgroup B) [Fintype D] (P : B[X]) (η ξ : B)
    (hP0 : P.eval 0=0)
    (hcomp : subspacePolynomial D=P^4+C η*P^2+C ξ*P) :
    ∀ x y : B, P.eval (x+y)=P.eval x+P.eval y := by
  intro x y
  let Q : B[X] := X^4+C η*X^2+C ξ*X
  have hQ : Q≠0 := by
    intro h
    have hh := congrArg (fun f:B[X]=>f.coeff 4) h
    norm_num [Q,coeff_add,coeff_C_mul,coeff_X_pow] at hh
  have hQP : Q.comp P=subspacePolynomial D := by
    simpa [Q] using hcomp.symm
  have hQadd (A B' : B[X]) : Q.comp (A+B')=Q.comp A+Q.comp B' := by
    simp only [Q,add_comp,mul_comp,pow_comp,X_comp,C_comp]
    have h4 : (A+B')^4=A^4+B'^4 := by
      simpa using add_pow_char_pow A B' 2 2
    rw [h4,CharTwo.add_sq]
    ring
  let R : B[X] := P.comp (X+C y)+P+C (P.eval y)
  have hQR : Q.comp R=0 := by
    dsimp [R]
    rw [hQadd,hQadd,←comp_assoc,hQP,←(comp_C (p:=P) (a:=y)),←comp_assoc,hQP,
      subspacePolynomial_comp_add,comp_X]
    ring_nf
    simp [CharTwo.two_eq_zero]
  have hR0 : R.eval 0=0 := by
    simp [R,eval_comp,hP0,CharTwo.add_self_eq_zero]
  have hR : R=0 := by
    have he := (comp_eq_zero_iff.mp hQR).resolve_left hQ
    rw [he.2]
    have hc : R.coeff 0=0 := by simpa only [coeff_zero_eq_eval_zero] using hR0
    simp [hc]
  have he := congrArg (fun f:B[X]=>f.eval x) hR
  simp only [R,eval_add,eval_comp,eval_X,eval_C,eval_zero] at he
  have hh : P.eval (x+y)+(P.eval x+P.eval y)=0 := by simpa only [add_assoc] using he
  exact CharTwo.add_eq_zero.mp hh
attribute [local instance] Classical.propDecidable Classical.decEq
/-- A monic normalized quartic right factor is exactly the locator of a
subgroup of the supplied domain, with cardinality equal to its degree. -/
theorem exists_subspacePolynomial_of_quartic_composition
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) (P : B[X]) (η ξ : B) (hP : P.Monic)
    (hP0 : P.eval 0=0)
    (hcomp : subspacePolynomial D=P^4+C η*P^2+C ξ*P) :
    ∃ W : AddSubgroup B, W≤D ∧ P=subspacePolynomial W ∧
      Fintype.card W=P.natDegree := by
  let f : B →+ B :=
    { toFun := P.eval
      map_zero' := hP0
      map_add' := subspacePolynomial_quartic_factor_additive D P η ξ hP0 hcomp }
  let W : AddSubgroup B := f.ker
  have hW (x:B) : x∈W ↔ P.eval x=0 := Iff.rfl
  have hWD : W≤D := by
    intro x hx
    apply (subspacePolynomial_eval_eq_zero_iff D x).mp
    rw [hcomp]
    simp only [eval_add,eval_pow,eval_mul,eval_C,(hW x).mp hx]
    ring
  have hdvd : P∣subspacePolynomial D := by
    refine ⟨P^3+C η*P+C ξ,?_⟩
    rw [hcomp]
    ring
  have hsplit : P.Splits := by
    have hDsplit : (subspacePolynomial D).Splits := by
      apply Splits.prod
      intro x hx
      exact Splits.X_sub_C _
    exact hDsplit.of_dvd (subspacePolynomial_monic D).ne_zero hdvd
  have hsep := (subspacePolynomial_separable D).of_dvd hdvd
  have hWsplit : (subspacePolynomial W).Splits := by
    apply Splits.prod
    intro x hx
    exact Splits.X_sub_C _
  have hroots : P.roots=(subspacePolynomial W).roots := by
    apply (Multiset.Nodup.ext (nodup_roots hsep)
      (nodup_roots (subspacePolynomial_separable W))).mpr
    intro x
    rw [mem_roots hP.ne_zero,mem_roots (subspacePolynomial_monic W).ne_zero]
    exact (hW x).symm.trans (subspacePolynomial_eval_eq_zero_iff W x).symm
  have heq : P=subspacePolynomial W := by
    rw [hsplit.eq_prod_roots_of_monic hP,
      hWsplit.eq_prod_roots_of_monic (subspacePolynomial_monic W),hroots]
  refine ⟨W,hWD,?_,?_⟩
  · convert heq using 1
    congr 1
    exact Subsingleton.elim _ _
  · rw [heq,subspacePolynomial_natDegree]
    simp only [←Nat.card_eq_fintype_card]
end BinaryFieldCounterexamples
