/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FullSource
public import BinaryFieldCounterexamples.Constructions.Gold.PairWitnesses
/-!
# The constant-derivative level locator in Lemma 5.12

The locator here is the literal product over the roots of `P` in the prescribed
domain, not a polynomial named as a locator by assumption. Normalizing the
complementary quotient shows that it equals `lc(H)(C^2+lambda_0 X)`.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
attribute [local instance] Classical.decEq
variable {B : Type*} [Field B] [Fintype B] [CharP B 2]
/-- The literal monic locator of the level set in the introduction to Section
5.3 and the proof of Lemma 5.12: all roots of `P` on the prescribed domain. -/
noncomputable def goldLevelLocator (D : AddSubgroup B) (P : B[X]) : B[X] :=
  ∏ x ∈ (additiveDomain D).filter (fun x ↦ P.eval x=0), (X-C x)
/-- The complementary quotient normalized to be monic is the actual product
locator of Lemma 5.12. This algebraic bridge assumes only the quotient-square
identity and saturation by the exhibited roots. -/
theorem goldLevelLocator_eq_scaled_quotient (D : AddSubgroup B) [Fintype D]
    (H P : B[X]) (hH : H≠0) (hdiv : H ∣ subspacePolynomial D)
    (hsq : P^2=subspacePolynomial D+subspacePolynomial D/H)
    (hcount : Nat.card {x : D // P.eval (x:B)=0}=(subspacePolynomial D/H).natDegree) :
    goldLevelLocator D P=C H.leadingCoeff*(subspacePolynomial D/H) := by
  classical
  let Q := subspacePolynomial D/H
  let E := (additiveDomain D).filter (fun x ↦ P.eval x=0)
  have hmul : H*Q=subspacePolynomial D := EuclideanDomain.mul_div_cancel' hH hdiv
  have hQ : Q≠0 := by
    intro hz
    rw [hz,mul_zero] at hmul
    exact (subspacePolynomial_monic D).ne_zero hmul.symm
  have hc : H.leadingCoeff*Q.leadingCoeff=1 := by
    have he := congrArg leadingCoeff hmul
    rw [leadingCoeff_mul,(subspacePolynomial_monic D).leadingCoeff] at he
    exact he
  have hE : E.card=Q.natDegree := by
    have he := agreementCount_add_source_eq_roots D (0 : B[X]) P
    rw [agreementCount_eq_card_filter (additiveDomain D) (fun x : B ↦ (0 : B[X]).eval x) (P+0)] at he
    simpa only [eval_zero,add_zero,E,Q] using he.trans hcount
  have hroot : ∀ x ∈ E, Q.eval x=0 := by
    intro x hx
    obtain ⟨hxD,hxP⟩ := Finset.mem_filter.mp hx
    have hL : (subspacePolynomial D).eval x=0 :=
      (subspacePolynomial_eval_eq_zero_iff D x).mpr ((mem_additiveDomain D x).mp hxD)
    have he := congrArg (fun R : B[X] ↦ R.eval x) hsq
    simpa only [eval_pow,hxP,zero_pow (by decide : 2≠0),eval_add,hL,zero_add,Q] using he.symm
  have hroots := roots_eq_of_natDegree_le_card_of_ne_zero hroot hE.ge hQ
  have hsplits : Q.Splits := splits_iff_card_roots.mpr (by rw [hroots]; exact hE)
  have he : Q=C Q.leadingCoeff*goldLevelLocator D P := by
    calc
      Q = C Q.leadingCoeff*(Q.roots.map fun x ↦ X-C x).prod := hsplits.eq_prod_roots
      _ = _ := by rw [hroots]; rfl
  change goldLevelLocator D P=C H.leadingCoeff*Q
  rw [he,← mul_assoc,← C_mul,hc,C_1,one_mul]
/-- Lemma 5.12, proof line 536, and Section 5.3's announced constant-derivative
form: the actual level-set locator is `lc(H)(C^2+lambda_0 X)` for `C=P+R`,
where `R` is the full manuscript square root. -/
theorem repairedLocator_levelLocator_eq [Algebra (ZMod 2) B]
    (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (ht0 : 2≤t) (ht : 2*t≤k+1)
    (hM : ∀ r, 1≤r → r<t → goldMoment D v A r=0) (hr : tensorPolarRank D v A=2*t)
    (hzeros : Nat.card {x : D // tensorQuadraticFunction D v A x+l x+κ=0}=2^k+2^(k-t)) :
    let P := repairedLocator D v A l κ t
    let H := repairedPolynomial D v A l κ
    goldLevelLocator D P=C H.leadingCoeff*((P+goldFullSourcePolynomial D)^2+
      C ((subspacePolynomial D).coeff 1)*X) := by
  dsimp only
  let H := repairedPolynomial D v A l κ
  let Q := subspacePolynomial D/H
  have hHdeg := (repairedPolynomial_natDegrees D k hD v A l κ t ht0 ht hM hr).1
  have hH : H≠0 := by
    intro hz
    rw [show repairedPolynomial D v A l κ=H from rfl,hz,natDegree_zero] at hHdeg
    have : 0<(2:ℕ)^k+2^(k-t) := by positivity
    omega
  have hdiv := (repairedPolynomial_dvd_locator D k hD v A l κ t ht0 ht hM hr hzeros).1
  have hmul : H*Q=subspacePolynomial D := EuclideanDomain.mul_div_cancel' hH hdiv
  have hQ : Q≠0 := by
    intro hz
    rw [hz,mul_zero] at hmul
    exact (subspacePolynomial_monic D).ne_zero hmul.symm
  have hdQ : Q.natDegree=2^k-2^(k-t) := by
    have he := congrArg natDegree hmul
    rw [natDegree_mul hH hQ,show H.natDegree=2^k+2^(k-t) from hHdeg,
      subspacePolynomial_natDegree,← Nat.card_eq_fintype_card,hD,pow_succ] at he
    omega
  have hs := repairedLocator_sq D k hD v A l κ t ht0 ht hM hr hzeros
  have hloc := goldLevelLocator_eq_scaled_quotient D H (repairedLocator D v A l κ t) hH hdiv hs
    (by rw [show (subspacePolynomial D/H).natDegree=2^k-2^(k-t) from hdQ];
        exact (repairedLocator_properties D k hD v A l κ t ht0 ht hM hr hzeros).2.2.2.1)
  rw [hloc]
  congr 1
  dsimp only [H]
  rw [CharTwo.add_sq,hs,goldFullSourcePolynomial_sq]
  linear_combination (norm := ring_nf)
    -(subspacePolynomial D+C ((subspacePolynomial D).coeff 1)*X)*(CharTwo.two_eq_zero (R := B[X]))
end BinaryFieldCounterexamples.Gold
