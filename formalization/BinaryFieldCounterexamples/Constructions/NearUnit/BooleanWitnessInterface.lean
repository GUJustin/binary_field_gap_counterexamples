/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.NearUnit.BooleanComplementConversion
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.SourceBound
public import BinaryFieldCounterexamples.Constructions.PoleReduction
public import BinaryFieldCounterexamples.Agreement.Domains
public import BinaryFieldCounterexamples.Agreement.Interpolation
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingWitnesses
/-!
# Exact Boolean complement and pole witness

This module keeps the concrete polynomials in Lemma 3.16: the derivative
square root, complementary locator, and pole correction. It proves exact
complementary root and retained-witness agreement counts, the sharp correction
degree, and normalized nonzero challenges for one pair independent of the Boolean
factor. The mapped-domain formulation is in `BooleanWitnessMapped`.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.NearUnit
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Saturation by distinct roots on the binary domain implies divisibility by its locator. -/
theorem saturated_boolean_factor_dvd
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (H : F[X]) (hH : H ≠ 0)
    (hroots : ((additiveDomain D).filter fun x ↦ H.eval x=0).card=H.natDegree) :
    H ∣ subspacePolynomial D := by
  let Z := (additiveDomain D).filter fun x ↦ H.eval x=0
  have hr : H.roots=Z.val := roots_eq_of_natDegree_le_card_of_ne_zero
    (fun x hx ↦ (Finset.mem_filter.mp hx).2) (by simpa [Z] using hroots.ge) hH
  have hs : H.Splits := splits_iff_card_roots.mpr (by rw [hr]; exact hroots)
  have hL : (subspacePolynomial D).roots=(additiveDomain D).val :=
    roots_eq_of_natDegree_le_card_of_ne_zero
      (fun x hx ↦ (subspacePolynomial_eval_eq_zero_iff D x).mpr
        ((mem_additiveDomain D x).mp hx))
      (by rw [subspacePolynomial_natDegree,card_additiveDomain,Nat.card_eq_fintype_card])
      (subspacePolynomial_monic D).ne_zero
  apply hs.dvd_of_roots_le_roots hH
  rw [hr,hL]
  exact Finset.val_le_iff.mpr (Finset.filter_subset _ _)

/-- A degree-at-least-two complementary quotient fixes the exact correction degree. -/
theorem boolean_complement_exact_degree
    {F : Type*} [Field F] [CharP F 2]
    (P S L Q : F[X]) (lam beta : F) (T : ℕ) (hT : 2 ≤ T)
    (hP : P^2=L+Q) (hS : S^2=L-C lam*(X-C beta)) (hQ : Q.natDegree=T) :
    (P+S).natDegree=T/2 := by
  have hsq : (P+S)^2=Q-C lam*(X-C beta) := by
    rw [CharTwo.add_sq,hP,hS]
    linear_combination (CharP.cast_eq_zero F[X] 2)*L
  have hdsmall : (C lam*(X-C beta)).natDegree<Q.natDegree := by
    apply natDegree_mul_le.trans_lt
    simp only [natDegree_C,natDegree_X_sub_C,zero_add,hQ]
    omega
  have hd := congrArg Polynomial.natDegree hsq
  rw [natDegree_pow,natDegree_sub_eq_left_of_natDegree_lt hdsmall,hQ] at hd
  omega

/-- The strengthened Boolean conversion keeps the literal complement and
pole witness, their exact root/agreement count and sharp correction degree. -/
theorem booleanFactor_exact_witness
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (beta : F) (hbeta : beta ∉ D)
    (K T : ℕ) (hK : 2 ≤ K) (hpow : ∃ j : ℕ, K=2^j)
    (hcard : Fintype.card D=4*K) (hT : 2 ≤ T) (hTK : T<2*K)
    (_heven : Even T) (H : F[X]) (hH : H≠0)
    (hdeg : H.natDegree=4*K-T)
    (hroots : ((additiveDomain D).filter fun x ↦ H.eval x=0).card=4*K-T)
    (hbool : H^2+H=C (((subspacePolynomial D).coeff 1)⁻¹)*
      subspacePolynomial D*H.derivative) :
    let L := subspacePolynomial D
    let lam := L.coeff 1
    let eta := (frobeniusEquiv F 2).symm (lam⁻¹)
    let A := C eta * primePowerPolynomialRoot 2 1 H.derivative
    let Q := L/H
    let P := A*Q
    let R := binaryQuarterNumerator D 0
    let S := binaryQuarterNumerator D beta
    let a := (P+S).eval beta
    let w := poleCorrection (P+S) beta
    let f : additiveDomain D → F := fun x ↦ S.eval (x:F)*((x:F)-beta)⁻¹
    let g : additiveDomain D → F := fun x ↦ ((x:F)-beta)⁻¹
    H∣L ∧ A^2=C (lam⁻¹)*H.derivative ∧ P^2=L+Q ∧
      R^2=L+C lam*X ∧
      (∀ x ∈ D, P.eval x=0 ↔ H.eval x≠0) ∧
      ((additiveDomain D).filter fun x ↦ P.eval x=0).card=T ∧
      (P+R).natDegree=T/2 ∧ (P+S).natDegree=T/2 ∧
      a=P.eval beta+(frobeniusEquiv F 2).symm (L.eval beta) ∧
      a≠0 ∧ a^2=L.eval beta/H.eval beta ∧
      w.degree<(T/2:ℕ) ∧ w.degree<K ∧
      (∀ x : additiveDomain D, f x+a*g x=w.eval (x:F) ↔ P.eval (x:F)=0) ∧
      agreementCount (additiveDomain D) (fun x ↦ f x+a*g x) w=T ∧
      agreementEQ (additiveDomain D) K g K ∧
      commonAgreementEQ (additiveDomain D) K f g K ∧
      agreementLE (additiveDomain D) K f (3*K/2-1) := by
  dsimp only
  let L := subspacePolynomial D
  let lam := L.coeff 1
  let eta := (frobeniusEquiv F 2).symm (lam⁻¹)
  let A := C eta * primePowerPolynomialRoot 2 1 H.derivative
  let Q := L/H
  let P := A*Q
  let R := binaryQuarterNumerator D 0
  let S := binaryQuarterNumerator D beta
  let a := (P+S).eval beta
  let w := poleCorrection (P+S) beta
  have hdiv : H∣L := saturated_boolean_factor_dvd D H hH (hroots.trans hdeg.symm)
  have hfactor : L=H*Q := (EuclideanDomain.mul_div_cancel' hH hdiv).symm
  have hA : A^2=C (lam⁻¹)*H.derivative := by
    dsimp only [A]
    rw [mul_pow,←map_pow,binaryDerivative_square_root]
    have he : eta^2=lam⁻¹ := (frobeniusEquiv F 2).apply_symm_apply (lam⁻¹)
    rw [he]
  have hP : P^2=L+Q := by
    have hc : H+1=Q*A^2 := by
      apply mul_left_cancel₀ hH
      rw [hA]
      have hb : H^2+H=C (lam⁻¹)*L*H.derivative := hbool
      rw [hfactor] at hb
      linear_combination hb
    calc
      (A*Q)^2=(Q*A^2)*Q := by ring
      _=(H+1)*Q := by rw [←hc]
      _=L+Q := by rw [hfactor]; ring
  have hQ0 : Q≠0 := by
    intro hz
    have hL := (subspacePolynomial_monic D).ne_zero
    apply hL
    simpa [hz] using hfactor
  have hQdeg : Q.natDegree=T := by
    have hd := congrArg Polynomial.natDegree hfactor
    rw [natDegree_mul hH hQ0,hdeg] at hd
    change (subspacePolynomial D).natDegree=_ at hd
    rw [subspacePolynomial_natDegree,hcard] at hd
    omega
  have hS : S^2=L-C lam*(X-C beta) := binaryQuarterNumerator_sq D beta
  have hR : R^2=L-C lam*(X-C 0) := binaryQuarterNumerator_sq D 0
  have hR' : R^2=L+C lam*X := by simpa [CharTwo.sub_eq_add] using hR
  have hLb : L.eval beta≠0 := fun h ↦ hbeta ((subspacePolynomial_eval_eq_zero_iff D beta).mp h)
  obtain ⟨_, hane, ha2⟩ := binaryComplement_source_correction L H Q P S lam beta T
    (by omega) hfactor hP hS hQdeg.le hLb
  have hroot (x : F) (hx : x∈D) : P.eval x=0 ↔ H.eval x≠0 :=
    binaryComplement_eval_zero_iff_of_derivative L H Q P lam x
      (subspacePolynomial_coeff_one_ne_zero D)
      (Gold.derivative_eq_C_of_binarySupport _ (subspacePolynomial_support D))
      hfactor hP ((subspacePolynomial_eval_eq_zero_iff D x).mpr hx)
  have hcount : ((additiveDomain D).filter fun x ↦ P.eval x=0).card=T := by
    have he : (additiveDomain D).filter (fun x ↦ P.eval x=0)=
        (additiveDomain D).filter (fun x ↦ H.eval x≠0) := by
      apply Finset.filter_congr
      intro x hx
      exact hroot x ((mem_additiveDomain D x).mp hx)
    rw [he]
    have hc := Finset.card_filter_add_card_filter_not (s:=additiveDomain D)
      (fun x ↦ H.eval x=0)
    rw [hroots,card_additiveDomain,Nat.card_eq_fintype_card,hcard] at hc
    change (4*K-T)+((additiveDomain D).filter fun x ↦ H.eval x≠0).card=4*K at hc
    omega
  have hdR := boolean_complement_exact_degree P R L Q lam 0 T hT hP hR hQdeg
  have hdS := boolean_complement_exact_degree P S L Q lam beta T hT hP hS hQdeg
  have hSb : S.eval beta=(frobeniusEquiv F 2).symm (L.eval beta) := by
    apply (frobeniusEquiv F 2).injective
    change (S.eval beta)^2= _
    rw [(frobeniusEquiv F 2).apply_symm_apply]
    have he := congrArg (fun Q : F[X] ↦ Q.eval beta) hS
    simpa using he
  have halabel : a=P.eval beta+(frobeniusEquiv F 2).symm (L.eval beta) := by
    change (P+S).eval beta=_
    rw [eval_add,hSb]
  have hw : w.degree<(T/2:ℕ) := poleCorrection_degree_lt (P+S) beta (T/2)
    (degree_le_of_natDegree_le hdS.le)
  have hhalf : T/2≤K := by omega
  have hwK : w.degree<K := hw.trans_le (by exact_mod_cast hhalf)
  have hagr (x : additiveDomain D) :
      S.eval (x:F)*((x:F)-beta)⁻¹+a*((x:F)-beta)⁻¹=w.eval (x:F) ↔ P.eval (x:F)=0 := by
    have hx : (x:F)≠beta := fun h ↦ hbeta (h ▸ (mem_additiveDomain D x).mp x.property)
    rw [Gold.poleCorrection_agreement_iff_root S (P+S) beta x hx]
    have hc : S+(P+S)=P := by rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
    rw [hc]
  have hacount : agreementCount (additiveDomain D)
      (fun x ↦ S.eval (x:F)*((x:F)-beta)⁻¹+a*((x:F)-beta)⁻¹) w=T := by
    rw [agreementCount_eq_card_filter (additiveDomain D)
      (fun x : F ↦ S.eval x*(x-beta)⁻¹+a*(x-beta)⁻¹) w]
    rw [←hcount]
    congr 1
    apply Finset.filter_congr
    intro x hx
    exact (eq_comm.trans (hagr ⟨x,hx⟩))
  have hb : beta∉additiveDomain D := by simpa only [mem_additiveDomain] using hbeta
  have hKd : K≤(additiveDomain D).card := by
    rw [card_additiveDomain,Nat.card_eq_fintype_card,hcard]; omega
  exact ⟨hdiv,hA,hP,hR',hroot,hcount,hdR,hdS,halabel,
    hane,ha2,hw,hwK,hagr,hacount,agreementEQ_reciprocal _ beta hb K hKd,
    commonAgreementEQ_reciprocal_right _ beta hb K hKd _,
    agreementLE_binaryQuarterSource D beta hbeta K hK hpow hcard⟩

/-- The canonical first-input numerator is literally the paper's square-root
polynomial plus the square root of the scaled pole. -/
theorem binaryQuarterNumerator_eq_zero_add_sqrt
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (beta : F) :
    binaryQuarterNumerator D beta=binaryQuarterNumerator D 0+
      C ((frobeniusEquiv F 2).symm ((subspacePolynomial D).coeff 1*beta)) := by
  apply CharTwo.sq_injective
  dsimp only
  rw [CharTwo.add_sq, binaryQuarterNumerator_sq, binaryQuarterNumerator_sq,
    ←map_pow]
  have hs : ((frobeniusEquiv F 2).symm ((subspacePolynomial D).coeff 1*beta))^2=
      (subspacePolynomial D).coeff 1*beta :=
    (frobeniusEquiv F 2).apply_symm_apply _
  rw [hs]
  simp only [binaryQuarterRadicand,map_zero,sub_zero,map_mul]
  ring

/-- The challenge attached to the literal Boolean complement, on one fixed pair. -/
noncomputable def booleanWitnessLabel
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (beta : F) (H : F[X]) : F :=
  (C ((frobeniusEquiv F 2).symm ((subspacePolynomial D).coeff 1)⁻¹)*
    primePowerPolynomialRoot 2 1 H.derivative*(subspacePolynomial D/H)+
      binaryQuarterNumerator D beta).eval beta

/-- Literal saturated Boolean factors at the same pole have the same normalized
challenge exactly when their values at that pole coincide. -/
theorem booleanWitnessLabel_eq_iff
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (beta : F) (hbeta : beta∉D)
    (K T : ℕ) (hK : 2≤K) (hpow : ∃ j : ℕ, K=2^j)
    (hcard : Fintype.card D=4*K) (hT : 2≤T) (hTK : T<2*K) (heven : Even T)
    (H J : F[X])
    (hdata : ∀ Q ∈ ({H,J} : Finset F[X]), Q≠0 ∧ Q.natDegree=4*K-T ∧
      ((additiveDomain D).filter fun x ↦ Q.eval x=0).card=4*K-T ∧
      Q^2+Q=C (((subspacePolynomial D).coeff 1)⁻¹)*subspacePolynomial D*Q.derivative) :
    booleanWitnessLabel D beta H=booleanWitnessLabel D beta J ↔ H.eval beta=J.eval beta := by
  have properties (Q : F[X]) (hQ : Q∈({H,J} : Finset F[X])) :
      booleanWitnessLabel D beta Q≠0 ∧
      (booleanWitnessLabel D beta Q)^2=(subspacePolynomial D).eval beta/Q.eval beta := by
    obtain ⟨hne,hd,hr,hb⟩ := hdata Q hQ
    have h := booleanFactor_exact_witness D beta hbeta K T hK hpow hcard hT hTK heven
      Q hne hd hr hb
    dsimp only at h
    exact ⟨h.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨ha,ha2⟩ := properties H (by simp)
  obtain ⟨hb,hb2⟩ := properties J (by simp)
  have hL : (subspacePolynomial D).eval beta≠0 :=
    fun h ↦ hbeta ((subspacePolynomial_eval_eq_zero_iff D beta).mp h)
  have hH : H.eval beta≠0 := by
    intro h
    rw [h,div_zero] at ha2
    exact ha (CharTwo.sq_injective (by simpa using ha2))
  have hJ : J.eval beta≠0 := by
    intro h
    rw [h,div_zero] at hb2
    exact hb (CharTwo.sq_injective (by simpa using hb2))
  constructor
  · intro h
    have he := congrArg (fun x : F ↦ x^2) h
    rw [ha2,hb2] at he
    exact (mul_left_cancel₀ hL ((div_eq_div_iff hH hJ).mp he)).symm
  · intro h
    apply CharTwo.sq_injective
    dsimp only
    rw [ha2,hb2,h]
end BinaryFieldCounterexamples.NearUnit
