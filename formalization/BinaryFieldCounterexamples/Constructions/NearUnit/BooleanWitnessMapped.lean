/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.NearUnit.BooleanWitnessInterface
public import BinaryFieldCounterexamples.Constructions.NearUnit.MappedBooleanFactor
/-!
# Boolean-to-witness conversion over a mapped binary domain

Lemma 3.16 is expressed over an arbitrary finite binary base field and a finite
extension, using literal coefficient maps of the base-field polynomials. For
N ≥ 8 and even 2 ≤ T < N/2, the saturated Boolean factor gives a nonzero challenge
and a concrete witness of degree < T/2 with exactly T agreements. The canonical
pair is independent of that factor, with exact second-input/common agreement N/4
and first-input agreement at most 3N/8 − 1. Exact witness agreement does not
assert a maximum agreement for the combined word.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.NearUnit
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The canonical polynomial square root of the derivative divided by the locator coefficient. -/
noncomputable def booleanDerivativeFactor
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) (H : B[X]) : B[X] :=
  C ((frobeniusEquiv B 2).symm ((subspacePolynomial D).coeff 1)⁻¹)*
    primePowerPolynomialRoot 2 1 H.derivative

/-- The literal derivative factor times the complementary locator quotient. -/
noncomputable def booleanComplementPolynomial
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) (H : B[X]) : B[X] :=
  booleanDerivativeFactor D H*(subspacePolynomial D/H)

/-- The derivative factor squares to the normalized derivative. -/
theorem booleanDerivativeFactor_sq
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) (H : B[X]) :
    (booleanDerivativeFactor D H)^2=
      C (((subspacePolynomial D).coeff 1)⁻¹)*H.derivative := by
  rw [booleanDerivativeFactor,mul_pow,←map_pow,binaryDerivative_square_root]
  rw [frobeniusEquiv_symm_pow_p]

/-- The canonical derivative square root commutes with a finite-field embedding. -/
theorem map_booleanDerivativeFactor
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (H : B[X]) :
    (booleanDerivativeFactor D H).map φ=
      booleanDerivativeFactor (D.map φ.toAddMonoidHom) (H.map φ) := by
  apply CharTwo.sq_injective
  dsimp only
  rw [←Polynomial.map_pow,booleanDerivativeFactor_sq,booleanDerivativeFactor_sq]
  simp only [Polynomial.map_mul,map_C,map_inv₀,derivative_map,coeff_subspacePolynomial_map]

/-- The concrete complementary polynomial commutes with coefficient mapping. -/
theorem map_booleanComplementPolynomial
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (H : B[X]) :
    (booleanComplementPolynomial D H).map φ=
      booleanComplementPolynomial (D.map φ.toAddMonoidHom) (H.map φ) := by
  simp only [booleanComplementPolynomial,Polynomial.map_mul,map_booleanDerivativeFactor,
    Polynomial.map_div,map_subspacePolynomial]

/-- The base-field canonical numerator maps to the canonical numerator at zero. -/
theorem map_binaryQuarterNumerator_zero
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) :
    (binaryQuarterNumerator D 0).map φ=binaryQuarterNumerator (D.map φ.toAddMonoidHom) 0 := by
  apply CharTwo.sq_injective
  dsimp only
  rw [←Polynomial.map_pow,binaryQuarterNumerator_sq,binaryQuarterNumerator_sq]
  simp only [binaryQuarterRadicand,Polynomial.map_sub,Polynomial.map_mul,map_C,map_X,
    map_zero,Polynomial.map_zero,map_subspacePolynomial,coeff_subspacePolynomial_map]

/-- A binary domain of size at least eight supplies the quarter-size power-of-two parameters. -/
theorem binary_quarter_parameters_of_card
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) (N : ℕ) (hN : Fintype.card D=N) (hN8 : 8≤N) :
    2≤N/4 ∧ (∃ j : ℕ, N/4=2^j) ∧ N=4*(N/4) := by
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  have hc := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=D)
  have htwo : Nat.card (ZMod 2)=2 := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
  rw [Nat.card_eq_fintype_card,hN,htwo] at hc
  have hd : 2≤Module.finrank (ZMod 2) D := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    rw [←hc]
    norm_num
    omega
  have hsplit : N=4*2^(Module.finrank (ZMod 2) D-2) := by
    rw [hc]
    conv_lhs => rw [←Nat.sub_add_cancel hd,pow_add]
    ring
  have hquarter : N/4=2^(Module.finrank (ZMod 2) D-2) := by
    rw [hsplit,Nat.mul_comm 4,Nat.mul_div_cancel _ (by decide : 0<4)]
  exact ⟨by omega,⟨_,hquarter⟩,by rw [hquarter]; exact hsplit⟩

/-- Saturated Boolean factors divide the locator and yield the exact complement square identity. -/
theorem booleanComplementPolynomial_properties
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) (H : B[X]) (hH : H≠0)
    (hroots : ((additiveDomain D).filter fun x ↦ H.eval x=0).card=H.natDegree)
    (hbool : H^2+H=C (((subspacePolynomial D).coeff 1)⁻¹)*subspacePolynomial D*H.derivative) :
    H∣subspacePolynomial D ∧ (booleanComplementPolynomial D H)^2=
      subspacePolynomial D+subspacePolynomial D/H := by
  have hdiv := saturated_boolean_factor_dvd D H hH hroots
  refine ⟨hdiv,?_⟩
  let A := booleanDerivativeFactor D H
  let Q := subspacePolynomial D/H
  have hfactor : subspacePolynomial D=H*Q := (EuclideanDomain.mul_div_cancel' hH hdiv).symm
  have hc : H+1=Q*A^2 := by
    apply mul_left_cancel₀ hH
    rw [booleanDerivativeFactor_sq]
    nth_rw 2 [hfactor] at hbool
    linear_combination hbool
  change (A*Q)^2=subspacePolynomial D+Q
  calc
    (A*Q)^2=(Q*A^2)*Q := by ring
    _=(H+1)*Q := by rw [←hc]
    _=subspacePolynomial D+Q := by rw [hfactor];ring

/-- Lemma 3.16 on a prescribed binary domain and any finite extension. The
polynomials are literal coefficient maps; the exact count concerns the displayed
witness, while the pair itself has the stated maximum-agreement bounds. -/
theorem boolean_to_witness_mapped
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (N T : ℕ)
    (hN : Fintype.card D=N) (hN8 : 8≤N)
    (beta : F) (hbeta : beta∉D.map φ.toAddMonoidHom)
    (hT : 2≤T) (hTN : T<N/2) (heven : Even T)
    (H : B[X]) (hH : H≠0) (hdeg : H.natDegree=N-T)
    (hroots : ((additiveDomain D).filter fun x ↦ H.eval x=0).card=N-T)
    (hbool : H^2+H=C (((subspacePolynomial D).coeff 1)⁻¹)*subspacePolynomial D*H.derivative) :
    let LB := subspacePolynomial D
    let lamB := LB.coeff 1
    let AB := booleanDerivativeFactor D H
    let PB := booleanComplementPolynomial D H
    let RB := binaryQuarterNumerator D 0
    let DF := D.map φ.toAddMonoidHom
    let HF := H.map φ
    let LF := LB.map φ
    let lamF := φ lamB
    let P := PB.map φ
    let R := RB.map φ
    let K := N/4
    let E := mappedDomain φ (additiveDomain D)
    let S := R+C ((frobeniusEquiv F 2).symm (lamF*beta))
    let a := P.eval beta+(frobeniusEquiv F 2).symm (LF.eval beta)
    let w := poleCorrection (P+S) beta
    let f : E → F := fun x ↦ S.eval (x:F)*((x:F)-beta)⁻¹
    let g : E → F := fun x ↦ ((x:F)-beta)⁻¹
    H∣LB ∧ AB^2=C (lamB⁻¹)*H.derivative ∧ PB^2=LB+LB/H ∧
      RB^2=LB+C lamB*X ∧ LF=subspacePolynomial DF ∧
      P^2=LF+LF/HF ∧ R^2=LF+C lamF*X ∧ S=binaryQuarterNumerator DF beta ∧
      (∀ x∈D, PB.eval x=0 ↔ H.eval x≠0) ∧
      ((additiveDomain D).filter fun x ↦ PB.eval x=0).card=T ∧
      (E.filter fun x ↦ P.eval x=0).card=T ∧
      (PB+RB).natDegree=T/2 ∧ (P+R).natDegree=T/2 ∧
      a=(P+S).eval beta ∧ a≠0 ∧ a^2=LF.eval beta/HF.eval beta ∧
      w.degree<(T/2:ℕ) ∧ w.degree<K ∧
      (∀ x : E, f x+a*g x=w.eval (x:F) ↔ P.eval (x:F)=0) ∧
      agreementCount E (fun x ↦ f x+a*g x) w=T ∧
      agreementEQ E K g K ∧ commonAgreementEQ E K f g K ∧
      agreementLE E K f (3*N/8-1) := by
  dsimp only
  let DF := D.map φ.toAddMonoidHom
  let HF := H.map φ
  let PB := booleanComplementPolynomial D H
  let RB := binaryQuarterNumerator D 0
  let P := PB.map φ
  let R := RB.map φ
  let K := N/4
  have hpars := binary_quarter_parameters_of_card D N hN hN8
  have hcard : Fintype.card DF=4*K := by
    rw [←Nat.card_eq_fintype_card,natCard_map_addSubgroup,Nat.card_eq_fintype_card,hN]
    exact hpars.2.2
  have hK : 2≤K := hpars.1
  have hpow : ∃ j : ℕ, K=2^j := hpars.2.1
  have hTK : T<2*K := by
    have hn : N=4*K := hpars.2.2
    omega
  obtain ⟨hdvd,hPB⟩ := booleanComplementPolynomial_properties D H hH
    (hroots.trans hdeg.symm) hbool
  obtain ⟨hHF,hdHF,hrHF,hdivHF,hboolHF⟩ := mapped_booleanFactor_data φ D H (N-T)
    hH hdeg hroots hdvd hbool
  have hN4 : N=4*K := hpars.2.2
  have core := booleanFactor_exact_witness DF beta hbeta K T hK hpow hcard hT hTK heven
    HF hHF (by simpa only [←hN4] using hdHF)
    (by simpa only [←hN4] using hrHF) hboolHF
  dsimp only at core
  simp only [←booleanDerivativeFactor.eq_def,←booleanComplementPolynomial.eq_def] at core
  have hPmap : P=booleanComplementPolynomial DF HF := map_booleanComplementPolynomial φ D H
  have hRmap : R=binaryQuarterNumerator DF 0 := map_binaryQuarterNumerator_zero φ D
  rcases core with ⟨_,_,hPc,hRc,hrootc,hcountc,hdRc,_,halabel,hane,ha2,hw,hwK,hagr,hacount,hg,hcommon,hf⟩
  have hS : R+C ((frobeniusEquiv F 2).symm (φ ((subspacePolynomial D).coeff 1)*beta))=
      binaryQuarterNumerator DF beta := by
    rw [hRmap]
    symm
    exact (binaryQuarterNumerator_eq_zero_add_sqrt DF beta).trans (by rw [coeff_subspacePolynomial_map])
  have hLF : (subspacePolynomial D).map φ=subspacePolynomial DF := map_subspacePolynomial φ D
  have hRb : RB^2=subspacePolynomial D+C ((subspacePolynomial D).coeff 1)*X := by
    simpa [RB,binaryQuarterRadicand,CharTwo.sub_eq_add] using binaryQuarterNumerator_sq D 0
  have hPm : P^2=(subspacePolynomial D).map φ+
      (subspacePolynomial D).map φ/HF := by
    simpa only [Polynomial.map_pow,Polynomial.map_add,Polynomial.map_div] using
      congrArg (Polynomial.map φ) hPB
  have hRm : R^2=(subspacePolynomial D).map φ+C (φ ((subspacePolynomial D).coeff 1))*X := by
    simpa only [Polynomial.map_pow,Polynomial.map_add,Polynomial.map_mul,map_C,map_X]
      using congrArg (Polynomial.map φ) hRb
  have hroot (x : B) (hx : x∈D) : PB.eval x=0 ↔ H.eval x≠0 := by
    have h := hrootc (φ x) (show φ x∈DF from ⟨x,hx,rfl⟩)
    rw [←hPmap] at h
    simpa only [P,HF,eval_map_apply,ne_eq,map_eq_zero] using h
  have hcountB : ((additiveDomain D).filter fun x ↦ PB.eval x=0).card=T := by
    have he : (additiveDomain D).filter (fun x ↦ PB.eval x=0)=
        (additiveDomain D).filter (fun x ↦ H.eval x≠0) := by
      apply Finset.filter_congr
      intro x hx
      exact hroot x ((mem_additiveDomain D x).mp hx)
    rw [he]
    have hc := Finset.card_filter_add_card_filter_not (s:=additiveDomain D) (fun x ↦ H.eval x=0)
    rw [hroots,card_additiveDomain,Nat.card_eq_fintype_card,hN] at hc
    change (N-T)+((additiveDomain D).filter fun x ↦ H.eval x≠0).card=N at hc
    omega
  have hdegree : (P+R).natDegree=T/2 := by rw [hPmap,hRmap]; exact hdRc
  have hdegreeB : (PB+RB).natDegree=T/2 := by
    have hd : (PB+RB).natDegree=(P+R).natDegree := by
      dsimp only [P,R]
      rw [←Polynomial.map_add,natDegree_map]
    exact hd.trans hdegree
  have hbound : 3*N/8-1=3*K/2-1 := by
    have hn : N=4*K := hpars.2.2
    omega
  have hE : mappedDomain φ (additiveDomain D)=additiveDomain DF := mappedDomain_additiveDomain φ D
  dsimp only [R,RB] at hS
  refine ⟨hdvd,booleanDerivativeFactor_sq D H,hPB,hRb,hLF,hPm,hRm,hS,hroot,hcountB,
    ?_,hdegreeB,hdegree,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hE,map_booleanComplementPolynomial]; exact hcountc
  · rw [hS,hLF,map_booleanComplementPolynomial]; exact halabel.symm
  · rw [hLF,map_booleanComplementPolynomial,←halabel]; exact hane
  · rw [hLF,map_booleanComplementPolynomial,←halabel]; exact ha2
  · rw [hS,map_booleanComplementPolynomial]; exact hw
  · rw [hS,map_booleanComplementPolynomial]; exact hwK
  · rw [hE,hS,hLF,map_booleanComplementPolynomial,←halabel]; exact hagr
  · rw [hE,hS,hLF,map_booleanComplementPolynomial,←halabel]; exact hacount
  · rw [hE]; exact hg
  · rw [hE,hS]; exact hcommon
  · rw [hE,hS,hbound]; exact hf

/-- The concrete challenge obtained from the mapped complement and the exterior locator square root. -/
noncomputable def mappedBooleanWitnessLabel
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (beta : F) (H : B[X]) : F :=
    ((booleanComplementPolynomial D H).map φ).eval beta+
      (frobeniusEquiv F 2).symm (((subspacePolynomial D).map φ).eval beta)

/-- The literal mapped challenge equals the canonical challenge on the image domain. -/
theorem mappedBooleanWitnessLabel_eq_canonical
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (beta : F) (H : B[X]) :
    mappedBooleanWitnessLabel φ D beta H=
      booleanWitnessLabel (D.map φ.toAddMonoidHom) beta (H.map φ) := by
  let DF := D.map φ.toAddMonoidHom
  have hs : (binaryQuarterNumerator DF beta).eval beta=
      (frobeniusEquiv F 2).symm ((subspacePolynomial DF).eval beta) := by
    apply (frobeniusEquiv F 2).injective
    change ((binaryQuarterNumerator DF beta).eval beta)^2=_
    rw [(frobeniusEquiv F 2).apply_symm_apply]
    have he := congrArg (fun Q : F[X] ↦ Q.eval beta) (binaryQuarterNumerator_sq DF beta)
    simpa [binaryQuarterRadicand] using he
  rw [mappedBooleanWitnessLabel,map_booleanComplementPolynomial,map_subspacePolynomial]
  change (booleanComplementPolynomial DF (H.map φ)).eval beta+_=
    (booleanComplementPolynomial DF (H.map φ)+binaryQuarterNumerator DF beta).eval beta
  rw [eval_add,hs]

/-- Two actual admissible Boolean factors yield the same concrete mapped challenge
exactly when their extension-field values at the prescribed pole coincide. -/
theorem mappedBooleanWitnessLabel_eq_iff
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (N T : ℕ)
    (hN : Fintype.card D=N) (hN8 : 8≤N)
    (beta : F) (hbeta : beta∉D.map φ.toAddMonoidHom)
    (hT : 2≤T) (hTN : T<N/2) (heven : Even T)
    (H J : B[X])
    (hdata : ∀ Q∈({H,J} : Finset B[X]), Q≠0 ∧ Q.natDegree=N-T ∧
      ((additiveDomain D).filter fun x ↦ Q.eval x=0).card=N-T ∧
      Q^2+Q=C (((subspacePolynomial D).coeff 1)⁻¹)*subspacePolynomial D*Q.derivative) :
    mappedBooleanWitnessLabel φ D beta H=mappedBooleanWitnessLabel φ D beta J ↔
      (H.map φ).eval beta=(J.map φ).eval beta := by
  have hpars := binary_quarter_parameters_of_card D N hN hN8
  have hc : Fintype.card (D.map φ.toAddMonoidHom)=4*(N/4) := by
    rw [←Nat.card_eq_fintype_card,natCard_map_addSubgroup,Nat.card_eq_fintype_card,hN]
    exact hpars.2.2
  have hTK : T<2*(N/4) := by omega
  have hm (Q : B[X]) (hQ : Q∈({H,J} : Finset B[X])) :
      Q.map φ≠0 ∧ (Q.map φ).natDegree=4*(N/4)-T ∧
      ((additiveDomain (D.map φ.toAddMonoidHom)).filter fun x ↦ (Q.map φ).eval x=0).card=4*(N/4)-T ∧
      (Q.map φ)^2+Q.map φ=C (((subspacePolynomial (D.map φ.toAddMonoidHom)).coeff 1)⁻¹)*
        subspacePolynomial (D.map φ.toAddMonoidHom)*(Q.map φ).derivative := by
    obtain ⟨hne,hd,hr,hb⟩ := hdata Q hQ
    have hv := saturated_boolean_factor_dvd D Q hne (hr.trans hd.symm)
    obtain ⟨hne',hd',hr',_,hb'⟩ := mapped_booleanFactor_data φ D Q (N-T) hne hd hr hv hb
    refine ⟨hne',?_,?_,hb'⟩
    · simpa only [←hpars.2.2] using hd'
    · simpa only [←hpars.2.2] using hr'
  rw [mappedBooleanWitnessLabel_eq_canonical,mappedBooleanWitnessLabel_eq_canonical]
  apply booleanWitnessLabel_eq_iff (D.map φ.toAddMonoidHom) beta hbeta (N/4) T
    hpars.1 hpars.2.1 hc hT hTK heven
  intro Q hQ
  have he : Q=H.map φ ∨ Q=J.map φ := by simpa using hQ
  rcases he with rfl | rfl
  · exact hm H (by simp)
  · exact hm J (by simp)
end BinaryFieldCounterexamples.NearUnit
