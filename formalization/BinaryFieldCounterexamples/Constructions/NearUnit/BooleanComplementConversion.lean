/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.NearUnit.ComplementConversion
@[expose] public section
namespace BinaryFieldCounterexamples.NearUnit
open Polynomial
set_option autoImplicit false
/-- A Boolean factor with a nonunit locator derivative still has an actual
complement square root. The locator itself is not rescaled. -/
theorem binaryComplement_exists_scaled_conversion
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (L H Q : B[X]) (lam : B) (hH : H≠0) (hfactor : L=H*Q)
    (hdifferential : H^2+H=C lam*L*H.derivative) :
    ∃ P : B[X], P^2=L+Q := by
  let a := (frobeniusEquiv B 2).symm lam
  have ha : a^2=lam := (frobeniusEquiv B 2).apply_symm_apply lam
  let A := C a*primePowerPolynomialRoot 2 1 H.derivative
  have hA : A^2=C lam*H.derivative := by
    dsimp only [A]
    rw [mul_pow,←map_pow,ha,binaryDerivative_square_root]
  have hcancel : H+1=Q*A^2 := by
    apply mul_left_cancel₀ hH
    rw [hA]
    rw [hfactor] at hdifferential
    linear_combination hdifferential
  refine ⟨A*Q,?_⟩
  calc
    (A*Q)^2=(Q*A^2)*Q := by ring
    _=(H+1)*Q := by rw [←hcancel]
    _=L+Q := by rw [hfactor];ring
/-- On a simple locator's roots, its complementary square vanishes precisely
where the discarded factor does not vanish. -/
theorem binaryComplement_eval_zero_iff_of_derivative
    {B : Type*} [Field B] [CharP B 2]
    (L H Q P : B[X]) (lam x : B) (hlam : lam≠0)
    (hderiv : L.derivative=C lam) (hfactor : L=H*Q)
    (hP : P^2=L+Q) (hx : L.eval x=0) :
    P.eval x=0 ↔ H.eval x≠0 := by
  have he := congrArg (fun G : B[X] => G.eval x) hfactor
  rw [hx,eval_mul] at he
  have hp := congrArg (fun G : B[X] => G.eval x) hP
  rw [eval_pow,eval_add,hx,zero_add] at hp
  constructor
  · intro hz hh
    have hq : Q.eval x=0 := by rw [hz,zero_pow (by decide)] at hp;exact hp.symm
    have hd := congrArg (fun G : B[X] => G.derivative.eval x) hfactor
    rw [hderiv,eval_C,derivative_mul,eval_add,eval_mul,eval_mul,hh,hq,
      mul_zero,zero_mul,add_zero] at hd
    exact hlam hd
  · intro hh
    have hq : Q.eval x=0 := (mul_eq_zero.mp he.symm).resolve_left hh
    rw [hq] at hp
    exact (pow_eq_zero_iff (by decide)).mp hp

/-- The fixed square-root first input and a complement give a low-degree correction,
whose exterior challenge squares to the literal reciprocal target value. -/
theorem binaryComplement_source_correction
    {B : Type*} [Field B] [CharP B 2]
    (L H Q P S : B[X]) (lam beta : B) (T : ℕ) (hT : 1≤T)
    (hfactor : L=H*Q) (hP : P^2=L+Q)
    (hS : S^2=L-C lam*(X-C beta)) (hQ : Q.natDegree≤T)
    (hLbeta : L.eval beta≠0) :
    (P+S).natDegree≤T/2 ∧ (P+S).eval beta≠0 ∧
      ((P+S).eval beta)^2=L.eval beta/H.eval beta := by
  have hsq : (P+S)^2=Q-C lam*(X-C beta) := by
    rw [CharTwo.add_sq,hP,hS]
    linear_combination (CharP.cast_eq_zero B[X] 2)*L
  have hdeg := congrArg Polynomial.natDegree hsq
  rw [natDegree_pow] at hdeg
  have hb : (Q-C lam*(X-C beta)).natDegree≤T := by
    apply (natDegree_sub_le _ _).trans
    apply max_le hQ
    exact natDegree_mul_le.trans (by simp only [natDegree_C,natDegree_X_sub_C];omega)
  have hval : ((P+S).eval beta)^2=Q.eval beta := by
    have hv := congrArg (fun G : B[X] => G.eval beta) hsq
    simpa only [eval_pow,eval_sub,eval_mul,eval_C,eval_X,sub_self,mul_zero,sub_zero] using hv
  have hfac := congrArg (fun G : B[X] => G.eval beta) hfactor
  rw [eval_mul] at hfac
  have hHbeta : H.eval beta≠0 := by intro hz;rw [hz,zero_mul] at hfac;exact hLbeta hfac
  have hQbeta : Q.eval beta≠0 := by intro hz;rw [hz,mul_zero] at hfac;exact hLbeta hfac
  refine ⟨by omega,?_,?_⟩
  · intro hz
    rw [hz,zero_pow (by decide)] at hval
    exact hQbeta hval.symm
  · rw [hval,hfac,mul_div_cancel_left₀ _ hHbeta]
end BinaryFieldCounterexamples.NearUnit
