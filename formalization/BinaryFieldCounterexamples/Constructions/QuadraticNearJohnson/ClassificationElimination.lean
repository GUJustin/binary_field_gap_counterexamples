/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.SourceBound
/-!
# Algebraic elimination for exact quadratic-line classification

More than `2K` projected agreement coordinates force a degree-`2K` residual
to vanish identically. Its top coefficient identifies the challenge, and
removing that top term leaves a square of degree at most `K`. A second
root-count elimination gives the literal quartic locator composition.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial

/-- The two projected coordinate equations force the quadratic relation,
its top coefficient, and the low-degree correction tail. -/
theorem quadratic_classification_elimination
    {F : Type*} [Field F] [CharP F 2]
    (S : Finset F) (K : ℕ) (hK : 0<K) (hlarge : 2*K<S.card)
    (A B : F[X]) (a z₀ : F) (hA : A.natDegree≤K) (hB : B.natDegree≤K)
    (hP : ∀ x ∈ S, (X^(4*K)+C a*X^(2*K)+A).eval x=0)
    (hQ : ∀ x ∈ S, (X^(8*K)+C z₀*X^(2*K)+B).eval x=0) :
    let P := X^(4*K)+C a*X^(2*K)+A
    let Q := X^(8*K)+C z₀*X^(2*K)+B
    let b := A.coeff K
    let V := A-C b*X^K
    Q=P^2+C (a^2)*P ∧ b^2=z₀+a^3 ∧
      V.natDegree≤K/2 ∧ B=V^2+C (a^2)*A ∧
      (A.coeff 0=0 → V.coeff 0=0) := by
  classical
  let P := X^(4*K)+C a*X^(2*K)+A
  let Q := X^(8*K)+C z₀*X^(2*K)+B
  let b := A.coeff K
  let V := A-C b*X^K
  let H := P^2+Q+C (a^2)*P
  have hHform : H=C (z₀+a^3)*X^(2*K)+A^2+C (a^2)*A+B := by
    dsimp [H,P,Q]
    simp only [CharTwo.add_sq,mul_pow,←map_pow,←pow_mul]
    rw [show 4*K*2=8*K by omega,show 2*K*2=4*K by omega]
    ring_nf
    simp [CharTwo.two_eq_zero]
    ring
  have hHdeg : H.natDegree≤2*K := by
    rw [hHform]
    apply (natDegree_add_le _ _).trans
    apply max_le _ (by omega)
    apply (natDegree_add_le _ _).trans
    apply max_le _ ((natDegree_C_mul_le _ _).trans (by omega))
    apply (natDegree_add_le _ _).trans
    exact max_le ((natDegree_C_mul_le _ _).trans (by simp))
      (natDegree_pow_le.trans (by omega))
  have hHzero : H=0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' H S _ (hHdeg.trans_lt hlarge)
    intro x hx
    have hp : P.eval x=0 := hP x hx
    have hq : Q.eval x=0 := hQ x hx
    simp [H,hp,hq]
  have hrelation : Q=P^2+C (a^2)*P := by
    have hh : Q+(P^2+C (a^2)*P)=0 := by
      calc
        _ = H := (add_assoc Q (P^2) (C (a^2)*P)).symm.trans
          (congrArg (fun R : F[X] => R+C (a^2)*P) (add_comm Q (P^2)))
        _ = 0 := hHzero
    exact CharTwo.add_eq_zero.mp hh
  have hb : b^2=z₀+a^3 := by
    have hh := congrArg (fun R : F[X] => R.coeff (2*K)) hHzero
    rw [hHform] at hh
    have hAc : A.coeff (2*K)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hBc : B.coeff (2*K)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [coeff_add,coeff_C_mul,coeff_X_pow_self,mul_one,
      coeff_pow_of_natDegree_le hA,hAc,hBc,mul_zero,add_zero,coeff_zero] at hh
    have hh' : b^2+(z₀+a^3)=0 := by simpa only [b,add_comm] using hh
    exact CharTwo.add_eq_zero.mp hh'
  have hVform : V^2=A^2+C (b^2)*X^(2*K) := by
    simp only [V,CharTwo.sub_eq_add,CharTwo.add_sq,mul_pow,←map_pow,←pow_mul]
    rw [show K*2=2*K by omega]
  have hBform : B=V^2+C (a^2)*A := by
    have hh : B+(V^2+C (a^2)*A)=0 := by
      rw [hVform,hb]
      simpa only [hHform,add_comm,add_left_comm,add_assoc] using hHzero
    exact CharTwo.add_eq_zero.mp hh
  have hVsquare : V^2=B+C (a^2)*A := by
    rw [hBform]
    simp [add_assoc,CharTwo.add_self_eq_zero]
  have hVdeg : V.natDegree≤K/2 := by
    have hh : (V^2).natDegree≤K := by
      rw [hVsquare]
      exact natDegree_add_le _ _ |>.trans (max_le hB ((natDegree_C_mul_le _ _).trans hA))
    rw [natDegree_pow] at hh
    omega
  refine ⟨hrelation,hb,hVdeg,hBform,?_⟩
  intro hA0
  simp [coeff_sub,coeff_X_pow,Ne.symm (Nat.ne_of_gt hK),hA0]

/-- The low-tail shape and more than `2K` shared roots force the literal
quartic composition with the domain locator. No additivity of `P` is assumed. -/
theorem quadratic_classification_locator_composition
    {F : Type*} [Field F] [CharP F 2]
    (S : Finset F) (K : ℕ) (hK : 0<K) (hlarge : 2*K<S.card)
    (L U V : F[X]) (a b d₈ d₄ : F)
    (hshape : L=X^(16*K)+C d₈*X^(8*K)+C d₄*X^(4*K)+U)
    (hU : U.natDegree≤2*K) (hV : V.natDegree≤K/2)
    (hL : ∀ x ∈ S, L.eval x=0)
    (hP : ∀ x ∈ S, (X^(4*K)+C a*X^(2*K)+C b*X^K+V).eval x=0) :
    let P := X^(4*K)+C a*X^(2*K)+C b*X^K+V
    let η := d₈+a^4
    let ξ := d₄+b^4+η*a^2
    L=P^4+C η*P^2+C ξ*P := by
  let P := X^(4*K)+C a*X^(2*K)+C b*X^K+V
  let η := d₈+a^4
  let ξ := d₄+b^4+η*a^2
  let R := L+P^4+C η*P^2+C ξ*P
  have hP2 : P^2=X^(8*K)+C (a^2)*X^(4*K)+C (b^2)*X^(2*K)+V^2 := by
    simp only [P,CharTwo.add_sq,mul_pow,←map_pow,←pow_mul]
    rw [show 4*K*2=8*K by omega,show 2*K*2=4*K by omega,show K*2=2*K by omega]
  have hP4 : P^4=X^(16*K)+C (a^4)*X^(8*K)+C (b^4)*X^(4*K)+V^4 := by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,hP2]
    simp only [CharTwo.add_sq,mul_pow,←map_pow,←pow_mul]
    rw [show 8*K*2=16*K by omega,show 4*K*2=8*K by omega,show 2*K*2=4*K by omega]
  have hRform : R=U+V^4+C η*(C (b^2)*X^(2*K)+V^2)+
      C ξ*(C a*X^(2*K)+C b*X^K+V) := by
    dsimp [R]
    rw [hshape,hP4,hP2]
    dsimp [P,η,ξ]
    simp only [map_add,map_mul,map_pow,mul_add]
    ring_nf
    simp [CharTwo.two_eq_zero]
  have hRdeg : R.natDegree≤2*K := by
    rw [hRform]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      apply max_le
      · exact (natDegree_add_le _ _).trans (max_le hU (natDegree_pow_le.trans (by omega)))
      · apply (natDegree_C_mul_le _ _).trans
        exact (natDegree_add_le _ _).trans (max_le
          ((natDegree_C_mul_le _ _).trans (by simp))
          (natDegree_pow_le.trans (by omega)))
    · apply (natDegree_C_mul_le _ _).trans
      apply (natDegree_add_le _ _).trans
      apply max_le _ (by omega)
      exact (natDegree_add_le _ _).trans (max_le
        ((natDegree_C_mul_le _ _).trans (by simp))
        ((natDegree_C_mul_le _ _).trans (by simp;omega)))
  have hRzero : R=0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R S _ (hRdeg.trans_lt hlarge)
    intro x hx
    have hp : P.eval x=0 := hP x hx
    simp [R,hL x hx,hp]
  have hh : L+(P^4+C η*P^2+C ξ*P)=0 := by simpa [R,add_assoc] using hRzero
  exact CharTwo.add_eq_zero.mp hh

end BinaryFieldCounterexamples
