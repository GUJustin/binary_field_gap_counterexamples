/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingSourceBound
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingPolynomials
public import BinaryFieldCounterexamples.Agreement.AffineTransport

/-!
# Arbitrary polynomial padding in characteristic two

The binary padding clause of Lemma 3.13 (p. 24) permits every multiplier,
including constant and odd-degree polynomials. The general bound uses the
natural floor `(3*K+w-1)/2`; the older constant-derivative specialization
keeps its existing bound independently.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial

/-- Arbitrary polynomial multipliers preserve the binary first-input bound under
`3*w ≤ K-1`; no parity or derivative restriction on the multiplier is needed. -/
theorem agreementLE_arbitrary_padded_binaryQuarterSource_of_square
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K w : ℕ) (hK : 2≤K) (hsmall : 3*w≤K-1) (A S : F[X]) (hA : A.natDegree≤w)
    (hAβ : A.eval β≠0)
    (hSsq : S^2=subspacePolynomial D-C ((subspacePolynomial D).coeff 1)*(X-C β))
    (hS : S.natDegree≤2*K) (hS' : S.derivative.natDegree≤0) :
    agreementLE (additiveDomain D) K
      (fun x => A.eval (x:F)*S.eval (x:F)*((x:F)-β)⁻¹) ((3*K+w-1)/2) := by
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
  have hB' : B.derivative.natDegree≤K-1 :=
    (natDegree_derivative_le B).trans (Nat.sub_le_sub_right hB 1)
  have hP : P.natDegree≤2*K+w := by
    exact (natDegree_sub_le _ _).trans (max_le
      (natDegree_mul_le.trans (by omega)) (by omega))
  have hJform : J=A^2*S.derivative-A*B.derivative+A.derivative*B := by
    simp only [J,P,derivative_sub,derivative_mul]
    ring
  have hJ : J.natDegree≤w+K-1 := by
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
    · by_cases hw : w=0
      · have hc : A=C (A.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
        have hder : A.derivative=0 := by rw [hc,derivative_C]
        simp [hder]
      · have hder := natDegree_derivative_le A
        have hh : (A.derivative*B).natDegree≤A.derivative.natDegree+B.natDegree := natDegree_mul_le
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
  have hΩdeg : Ω.natDegree≤w+3*K-1 := by
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
  change roots.card≤(3*K+w-1)/2
  omega

/-- The inputs of Lemma 3.13 keep the general first-input bound and
exact second-input/common agreement, with strict message degree below `K`. -/
theorem arbitrary_padded_binaryQuarterSources
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K w : ℕ) (hK : 2≤K) (hcard : Fintype.card D=4*K)
    (A : F[X]) (hA : A.natDegree≤w) (hAβ : A.eval β≠0)
    (hsmall : 3*w≤K-1) :
    let E := additiveDomain D
    let fA : E → F := fun x => A.eval (x:F)*
      (binaryQuarterNumerator D β).eval (x:F)*((x:F)-β)⁻¹
    let gA : E → F := fun x => A.eval (x:F)/((x:F)-β)
    agreementLE E K fA ((3*K+w-1)/2) ∧
      agreementEQ E K gA K ∧ commonAgreementEQ E K fA gA K := by
  dsimp only
  have hβE : β ∉ additiveDomain D := by simpa only [mem_additiveDomain] using hβ
  have hKcard : K≤(additiveDomain D).card := by
    rw [card_additiveDomain,Nat.card_eq_fintype_card,hcard]
    omega
  have hAK : A.natDegree≤K := by omega
  refine ⟨?_,agreementEQ_polynomialOverPole _ β hβE A K hAK hAβ hKcard,
    commonAgreementEQ_polynomialOverPole_right _ β hβE A K hAK hAβ hKcard _⟩
  apply agreementLE_arbitrary_padded_binaryQuarterSource_of_square D β hβ K w hK hsmall
    A (binaryQuarterNumerator D β) hA hAβ
  · exact binaryQuarterNumerator_sq D β
  · exact binaryQuarterNumerator_natDegree_le D β K hK hcard
  · rw [binaryQuarterNumerator_derivative]
    simp

/-- The translated canonical first input is literally the square root of the
reciprocal word with numerator `λ`, identifying the manuscript normalization. -/
theorem binaryQuarterSource_affine_sq
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (a β : F) (hβ : β ∉ D)
    (x : affineDomain (additiveDomain D) a) :
    ((binaryQuarterNumerator D β).eval ((x:F)-a)*((x:F)-a-β)⁻¹)^2 =
      (subspacePolynomial D).coeff 1 / ((x:F)-(β+a)) := by
  have hxD : (x:F)-a ∈ D := by
    have hx := x.property
    rwa [mem_affineDomain_iff,mem_additiveDomain] at hx
  have hne : (x:F)-a-β≠0 := sub_ne_zero.mpr (fun he => hβ (he ▸ hxD))
  have hs := congrArg (Polynomial.eval ((x:F)-a)) (binaryQuarterNumerator_sq D β)
  simp only [binaryQuarterRadicand,eval_pow,eval_sub,eval_mul,eval_C,eval_X] at hs
  rw [(subspacePolynomial_eval_eq_zero_iff D _).mpr hxD,zero_sub,CharTwo.neg_eq] at hs
  rw [mul_pow,hs,show (x:F)-(β+a)=(x:F)-a-β by ring]
  field_simp

/-- On every affine translate, every polynomial multiplier nonzero at the
exterior pole satisfies the binary padding clause of Lemma 3.13. -/
theorem arbitrary_padded_binaryQuarterSources_affine
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (a β : F) (hβ : β ∉ D)
    (K w : ℕ) (hK : 2≤K) (hcard : Fintype.card D=4*K)
    (A : F[X]) (hA : A.natDegree≤w)
    (hAβ : A.eval (β+a)≠0) (hsmall : 3*w≤K-1) :
    let E := affineDomain (additiveDomain D) a
    let fA : E → F := fun x => A.eval (x:F)*
      (binaryQuarterNumerator D β).eval ((x:F)-a)*((x:F)-a-β)⁻¹
    let gA : E → F := fun x => A.eval (x:F)/((x:F)-a-β)
    agreementLE E K fA ((3*K+w-1)/2) ∧
      agreementEQ E K gA K ∧ commonAgreementEQ E K fA gA K := by
  classical
  let E := affineDomain (additiveDomain D) a
  let A₀ := A.comp (X+C a)
  have hA₀ : A₀.natDegree≤w := by
    simpa [A₀,natDegree_comp] using hA
  have hA₀β : A₀.eval β≠0 := by simpa [A₀] using hAβ
  have hbase := (arbitrary_padded_binaryQuarterSources D β hβ K w hK hcard
    A₀ hA₀ hA₀β hsmall).1
  have hf := agreementLE_affineDomain (additiveDomain D) a
    (fun x => A₀.eval x*(binaryQuarterNumerator D β).eval x*(x-β)⁻¹)
    K ((3*K+w-1)/2) hbase
  have hβE : β+a ∉ E := by
    intro h
    rw [mem_affineDomain_iff,add_sub_cancel_right,mem_additiveDomain] at h
    exact hβ h
  have hKcard : K≤E.card := by
    dsimp [E]
    rw [card_affineDomain,card_additiveDomain,Nat.card_eq_fintype_card,hcard]
    omega
  have hAK : A.natDegree≤K := by omega
  dsimp only
  refine ⟨?_,?_,?_⟩
  · simpa [A₀] using hf
  · have hgform : (fun x : E => A.eval (x:F)/((x:F)-a-β)) =
        (fun x : E => A.eval (x:F)/((x:F)-(β+a))) := by
      funext x
      rw [show (x:F)-a-β=(x:F)-(β+a) by ring]
    rw [hgform]
    exact agreementEQ_polynomialOverPole E (β+a) hβE A K hAK hAβ hKcard
  · have hgform : (fun x : E => A.eval (x:F)/((x:F)-a-β)) =
        (fun x : E => A.eval (x:F)/((x:F)-(β+a))) := by
      funext x
      rw [show (x:F)-a-β=(x:F)-(β+a) by ring]
    rw [hgform]
    exact commonAgreementEQ_polynomialOverPole_right E (β+a) hβE A K hAK hAβ hKcard _

end BinaryFieldCounterexamples.Gold
