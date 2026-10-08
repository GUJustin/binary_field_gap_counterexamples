/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.SourceBound
/-!
# The sharp first-input bound after binary locator padding

For the padded residual `P = A*S - (X-β)*p`, set `Q = P² + A²*L_D`
and `J = A*P' - A'*P`. The polynomial `J*Q + λ*A³*P` has zero derivative,
vanishes at every agreement coordinate, and is nonzero at the excluded pole.
Each agreement is therefore a double root. Constant derivatives of the padding
locator and normalized numerator give degree at most `w + 3*K - 2` under the
manuscript's guard `3*w ≤ K-2`.

The resulting first-input bound is exactly `3*K/2 + w/2 - 1`, preserving the
half-padding gain required by the native 128-bit example. The canonical numerator
corollary uses the committed concrete square-root polynomial.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
/-- In characteristic two every second formal derivative vanishes. -/
theorem second_derivative_eq_zero_charTwo {F : Type*} [Field F] [CharP F 2] (P : F[X]) :
    P.derivative.derivative=0 := by
  ext n
  simp only [coeff_derivative,coeff_zero]
  rcases Nat.even_or_odd n with ⟨k,hk⟩ | ⟨k,hk⟩
  · simp [hk,CharTwo.add_self_eq_zero]
  · simp [hk,Nat.cast_add,Nat.cast_mul,CharTwo.two_eq_zero,CharTwo.add_self_eq_zero]
/-- The padded Wronskian has identically zero derivative in characteristic two. -/
theorem paddingWronskian_derivative {F : Type*} [Field F] [CharP F 2]
    (A P Q : F[X]) (lam : F) (hQ : Q.derivative=C lam*A^2) :
    (((A*P.derivative-A.derivative*P)*Q)+C lam*A^3*P).derivative=0 := by
  rw [derivative_add,derivative_mul,derivative_sub,derivative_mul,derivative_mul,
    second_derivative_eq_zero_charTwo,second_derivative_eq_zero_charTwo,hQ]
  simp only [mul_zero,zero_mul,add_zero,zero_add,sub_self,derivative_mul,derivative_C,
    derivative_pow]
  have ht : (2:F[X])=0 := CharTwo.two_eq_zero
  ring_nf
  have hthree : (3:F)=1 := by
    calc (3:F)=2+1 := by ring
         _=1 := by rw [CharTwo.two_eq_zero,zero_add]
  simp [ht,hthree]
/-- The first input of Lemma 3.13 keeps the sharp half-padding degree gain. -/
theorem agreementLE_padded_binaryQuarterSource_of_square
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K w : ℕ) (hw : 2≤w) (hsmall : 3*w≤K-2) (hKeven : Even K) (hweven : Even w)
    (hKchar : (K:F)=0) (A S : F[X]) (hA : A.natDegree≤w)
    (hA' : A.derivative.natDegree≤0) (hAβ : A.eval β≠0)
    (hSsq : S^2=subspacePolynomial D-C ((subspacePolynomial D).coeff 1)*(X-C β))
    (hS : S.natDegree≤2*K) (hS' : S.derivative.natDegree≤0) :
    agreementLE (additiveDomain D) K
      (fun x => A.eval (x:F)*S.eval (x:F)*((x:F)-β)⁻¹) (3*K/2+w/2-1) := by
  classical
  let L := subspacePolynomial D
  let lam := L.coeff 1
  have hlam : lam≠0 := subspacePolynomial_coeff_one_ne_zero D
  intro p hp
  have hpdeg : p.natDegree≤K-1 := by
    by_cases hz : p=0
    · simp [hz]
    · have hh := (natDegree_lt_iff_degree_lt hz).mpr hp
      omega
  let B := (X-C β)*p
  let P := A*S-B
  let Q := P^2+A^2*L
  let J := A*P.derivative-A.derivative*P
  let Ω := J*Q+C lam*A^3*P
  let roots := (additiveDomain D).filter fun x => p.eval x=A.eval x*S.eval x*(x-β)⁻¹
  rw [agreementCount_eq_card_filter (additiveDomain D) (fun x => A.eval x*S.eval x*(x-β)⁻¹) p]
  have hB : B.natDegree≤K := by
    have hh : B.natDegree≤(X-C β).natDegree+p.natDegree := natDegree_mul_le
    rw [natDegree_X_sub_C] at hh
    omega
  have hB' : B.derivative.natDegree≤K-2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_derivative]
    by_cases he : n+1=K
    · have hh : (n:F)+1=0 := by simpa only [Nat.cast_add,Nat.cast_one] using (show ((n+1:ℕ):F)=0 by rw [he,hKchar])
      rw [hh,mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by omega)),zero_mul]
  have hP : P.natDegree≤2*K+w := by
    exact (natDegree_sub_le _ _).trans (max_le
      (natDegree_mul_le.trans (by omega)) (by omega))
  have hJform : J=A^2*S.derivative-A*B.derivative+A.derivative*B := by
    simp only [J,P,derivative_sub,derivative_mul]
    ring
  have hJ : J.natDegree≤w+K-2 := by
    rw [hJform]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_sub_le _ _).trans
      apply max_le
      · have hh : (A^2*S.derivative).natDegree≤(A^2).natDegree+S.derivative.natDegree := natDegree_mul_le
        have hpow : (A^2).natDegree≤2*A.natDegree := natDegree_pow_le
        omega
      · have hh : (A*B.derivative).natDegree≤A.natDegree+B.derivative.natDegree := natDegree_mul_le
        omega
    · have hh : (A.derivative*B).natDegree≤A.derivative.natDegree+B.natDegree := natDegree_mul_le
      omega
  have hQform : Q=B^2-C lam*A^2*(X-C β) := by
    simp only [Q,P,CharTwo.sub_eq_add,CharTwo.add_sq,mul_pow,hSsq,L,lam]
    have ht : (2:F[X])=0 := CharTwo.two_eq_zero
    ring_nf
    simp [ht]
  have hQdeg : Q.natDegree≤2*K := by
    rw [hQform]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_pow_le.trans (by omega)
    · have h1 : (C lam*A^2*(X-C β)).natDegree≤(C lam*A^2).natDegree+1 := by
        calc
          _ ≤ (C lam*A^2).natDegree+(X-C β : F[X]).natDegree := natDegree_mul_le
          _ = _ := by rw [natDegree_X_sub_C]
      have h2 : (C lam*A^2).natDegree≤(A^2).natDegree := by
        exact natDegree_C_mul_le _ _
      have h3 : (A^2).natDegree≤2*A.natDegree := natDegree_pow_le
      omega
  have hQ' : Q.derivative=C lam*A^2 := by
    rw [hQform]
    simp [derivative_pow,CharTwo.two_eq_zero,CharTwo.neg_eq]
  have hΩ' : Ω.derivative=0 := paddingWronskian_derivative A P Q lam hQ'
  have hQβ : Q.eval β=0 := by simp [hQform,B]
  have hSβ : S.eval β≠0 := by
    have hLβ : L.eval β≠0 := by
      intro he
      exact hβ ((subspacePolynomial_eval_eq_zero_iff D β).mp he)
    have he := congrArg (Polynomial.eval β) hSsq
    simp only [eval_pow,eval_sub,eval_mul,eval_C,eval_X,sub_self,mul_zero,sub_zero] at he
    intro hz
    exact hLβ (by simpa [hz,L] using he.symm)
  have hΩβ : Ω.eval β=lam*A.eval β^3*(A.eval β*S.eval β) := by
    simp [Ω,hQβ,P,B]
  have hΩ : Ω≠0 := by
    intro he
    rw [he,eval_zero] at hΩβ
    exact (mul_ne_zero (mul_ne_zero hlam (pow_ne_zero 3 hAβ)) (mul_ne_zero hAβ hSβ)) hΩβ.symm
  have hΩdeg : Ω.natDegree≤w+3*K-2 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · have hh : (J*Q).natDegree≤J.natDegree+Q.natDegree := natDegree_mul_le
      omega
    · have h1 : (C lam*A^3*P).natDegree≤(C lam*A^3).natDegree+P.natDegree := natDegree_mul_le
      have h2 : (C lam*A^3).natDegree≤(A^3).natDegree := natDegree_C_mul_le _ _
      have h3 : (A^3).natDegree≤3*A.natDegree := natDegree_pow_le
      omega
  have hroot (x : F) (hx : x ∈ roots) : Ω.eval x=0 := by
    obtain ⟨hxD,hxp⟩ := Finset.mem_filter.mp hx
    have hxD' : x ∈ D := by simpa [additiveDomain] using hxD
    have hxβ : x-β≠0 := sub_ne_zero.mpr (fun he => hβ (he ▸ hxD'))
    have hPzero : P.eval x=0 := by
      simp only [P,B,eval_sub,eval_mul,eval_X,eval_C]
      rw [hxp]
      field_simp
      ring
    have hQzero : Q.eval x=0 := by simp [Q,hPzero,L,(subspacePolynomial_eval_eq_zero_iff D x).mpr hxD']
    simp [Ω,hPzero,hQzero]
  have hdouble := (twice_card_le_natDegree_of_double_roots roots Ω hΩ hroot
    (fun x hx => by rw [hΩ',eval_zero])).trans hΩdeg
  change roots.card≤3*K/2+w/2-1
  obtain ⟨k,hk⟩ := hKeven
  obtain ⟨u,hu⟩ := hweven
  rw [hk,hu] at hdouble ⊢
  omega
/-- The canonical normalized numerator satisfies the manuscript's sharp padded first-input bound. -/
theorem agreementLE_padded_binaryQuarterSource
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K : ℕ) (hpow : ∃ k : ℕ, K=2^k) (hcard : Fintype.card D=4*K)
    (w : ℕ) (hw : 2≤w) (hsmall : 3*w≤K-2) (hweven : Even w)
    (A : F[X]) (hA : A.natDegree≤w) (hA' : A.derivative.natDegree≤0) (hAβ : A.eval β≠0) :
    agreementLE (additiveDomain D) K
      (fun x => A.eval (x:F)*(binaryQuarterNumerator D β).eval (x:F)*((x:F)-β)⁻¹)
      (3*K/2+w/2-1) := by
  have hK : 2≤K := by omega
  obtain ⟨k,hk⟩ := hpow
  cases k with
  | zero => simp at hk; omega
  | succ k =>
    have hKeven : Even K := by
      refine ⟨2^k,?_⟩
      rw [hk,pow_succ]
      omega
    have hKchar : (K:F)=0 := by simp [hk,pow_succ,CharTwo.two_eq_zero]
    apply agreementLE_padded_binaryQuarterSource_of_square D β hβ K w hw hsmall hKeven hweven hKchar
      A (binaryQuarterNumerator D β) hA hA' hAβ
    · exact binaryQuarterNumerator_sq D β
    · exact binaryQuarterNumerator_natDegree_le D β K hK hcard
    · rw [binaryQuarterNumerator_derivative]
      simp
end BinaryFieldCounterexamples.Gold
