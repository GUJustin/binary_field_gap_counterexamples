/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.ClassificationCoordinates
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.ClassificationElimination
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.QuarticFactorAdditive
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.Labels
/-!
# Actual high-agreement explaining polynomials come from subspace-locator challenges

The concrete unshifted received line, evaluated on more than `2K` coordinates,
forces the challenge to come from a size-`4K` subgroup of the prescribed domain.
The original explaining polynomial is kept through an exact multiplied
identity, rather than replaced by an existential witness or a new definition.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Every strict-degree explaining polynomial on more than `2K` actual coordinates of
the unshifted quadratic line has the canonical subgroup challenge and the literal
locator residual identity for that same explaining polynomial. -/
theorem quadratic_classification_of_high_agreement
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [CharP F 2]
    (φ : B →+* F) (θ : F) (hθ : θ ∉ Set.range φ)
    (D : AddSubgroup B) (K : ℕ) (hK : 2≤K)
    (hpow : ∃ k : ℕ, K=2^k) (hD : (additiveDomain D).card=16*K)
    (S : Finset B) (hSD : S⊆additiveDomain D) (hS : 2*K<S.card)
    (p : F[X]) (hp : p.degree<K) (z : F)
    (heval : ∀ x ∈ S, p.eval (φ x) =
      (φ x)^(8*K-1)+θ*(φ x)^(4*K-1)+z*(φ x)^(2*K-1)) :
    ∃ W : AddSubgroup B, W≤D ∧ Fintype.card W=4*K ∧
      z=QuadraticConstruction.locatorLabel φ θ W K ∧
      X*p=(subspacePolynomial W).map φ^2+
        C (φ (QuadraticConstruction.locatorCoeffA W K^2)+θ)*(subspacePolynomial W).map φ+
        X^(8*K)+C θ*X^(4*K)+C z*X^(2*K) := by
  let _ : Algebra B F := φ.toAlgebra
  have halg : algebraMap B F=φ := RingHom.algebraMap_toAlgebra φ
  have hθ' : θ ∉ Set.range (algebraMap B F) := by rw [halg]; exact hθ
  have heval' : ∀ x ∈ S, p.eval (algebraMap B F x)=
      (algebraMap B F x)^(8*K-1)+θ*(algebraMap B F x)^(4*K-1)+
        z*(algebraMap B F x)^(2*K-1) := by simpa only [halg] using heval
  obtain ⟨z₀,a,h₀,h₁,hz,h₀deg,h₁deg,he₀,he₁⟩ :=
    quadratic_classification_coordinates θ hθ' K hK S hS p hp z heval'
  have hpform := quadratic_classification_reconstruct θ K hK S hS p hp z z₀ a h₀ h₁
    h₀deg h₁deg hz heval' he₀ he₁
  rw [halg] at hz hpform
  let A := X*h₁
  let B₀ := X*h₀
  let P := X^(4*K)+C a*X^(2*K)+A
  let Q := X^(8*K)+C z₀*X^(2*K)+B₀
  let b := A.coeff K
  let V := A-C b*X^K
  have hA : A.natDegree≤K := natDegree_X_mul_le_of_degree_lt h₁ K h₁deg
  have hB : B₀.natDegree≤K := natDegree_X_mul_le_of_degree_lt h₀ K h₀deg
  have pow_cancel (x : B) (j : ℕ) (hj : 0<j) : x*x^(j-1)=x^j := by
    rw [←pow_succ',Nat.sub_add_cancel hj]
  have hProot : ∀ x ∈ S, P.eval x=0 := by
    intro x hx
    simp only [P,A,eval_add,eval_mul,eval_pow,eval_X,eval_C,he₁ x hx,mul_add]
    rw [pow_cancel x (4*K) (by omega),←mul_assoc,mul_comm x a,mul_assoc,
      pow_cancel x (2*K) (by omega)]
    ring_nf
    simp [CharTwo.two_eq_zero]
  have hQroot : ∀ x ∈ S, Q.eval x=0 := by
    intro x hx
    simp only [Q,B₀,eval_add,eval_mul,eval_pow,eval_X,eval_C,he₀ x hx,mul_add]
    rw [pow_cancel x (8*K) (by omega),←mul_assoc,mul_comm x z₀,mul_assoc,
      pow_cancel x (2*K) (by omega)]
    ring_nf
    simp [CharTwo.two_eq_zero]
  obtain ⟨hrelation,hb,hV,hBform,hVzero⟩ :=
    quadratic_classification_elimination S K (by omega) hS A B₀ a z₀ hA hB hProot hQroot
  change Q=P^2+C (a^2)*P at hrelation
  change b^2=z₀+a^3 at hb
  change V.natDegree≤K/2 at hV
  have hPshape : P=X^(4*K)+C a*X^(2*K)+C b*X^K+V := by dsimp [P,V]; ring
  have hP0 : P.eval 0=0 := by simp [P,A,show 4*K≠0 by omega,show 2*K≠0 by omega]
  have htail : (C a*X^(2*K)+A).natDegree<4*K := by
    have hh : (C a*X^(2*K)+A).natDegree≤2*K := (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans
      (by simp : (X^(2*K):B[X]).natDegree≤2*K)) (by exact hA.trans (by omega : K≤2*K)))
    omega
  have hPmonic : P.Monic := by
    dsimp [P]
    rw [add_assoc]
    apply monic_X_pow_add
    exact degree_le_natDegree.trans_lt (by exact_mod_cast htail)
  have hPdegree : P.natDegree=4*K := by
    dsimp [P]
    rw [add_assoc,natDegree_add_eq_left_of_natDegree_lt (by simpa using htail),natDegree_X_pow]

  -- The actual domain locator supplies the quartic composition, not an assumed subspace.
  obtain ⟨k,hk⟩ := hpow
  have hcD : Fintype.card D=16*K := by
    simpa only [card_additiveDomain,Nat.card_eq_fintype_card] using hD
  have h16 : 2^(k+1+3)=16*K := by rw [hk]; simp [pow_add]; ring
  have h8 : 2^(k+1+2)=8*K := by rw [hk]; simp [pow_add]; ring
  have h4 : 2^(k+1+1)=4*K := by rw [hk]; simp [pow_add]; ring
  have h2 : 2^(k+1)=2*K := by rw [hk]; simp [pow_add]; ring
  obtain ⟨U,hU,_hU0,hLshape⟩ := subspacePolynomial_three_term_shape D (k+1) (hcD.trans h16.symm)
  rw [h16,h8,h4] at hLshape
  rw [h2] at hU
  let d₈ := (subspacePolynomial D).coeff (8*K)
  let d₄ := (subspacePolynomial D).coeff (4*K)
  let η := d₈+a^4
  let ξ := d₄+b^4+η*a^2
  have hLroots : ∀ x ∈ S, (subspacePolynomial D).eval x=0 := by
    intro x hx
    exact (subspacePolynomial_eval_eq_zero_iff D x).mpr ((mem_additiveDomain D x).mp (hSD hx))
  have hcomposition : subspacePolynomial D=P^4+C η*P^2+C ξ*P := by
    rw [hPshape]
    exact quadratic_classification_locator_composition S K (by omega) hS
      (subspacePolynomial D) U V a b d₈ d₄ hLshape hU hV hLroots
      (by simpa only [←hPshape] using hProot)
  obtain ⟨W,hWD,hPW,hWcard⟩ := exists_subspacePolynomial_of_quartic_composition
    D P η ξ hPmonic hP0 hcomposition
  have hWsize : Fintype.card W=4*K := hWcard.trans hPdegree
  have haW : QuadraticConstruction.locatorCoeffA W K=a := by
    change (subspacePolynomial W).coeff (2*K)=a
    rw [←hPW]
    have hAc : A.coeff (2*K)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [P,coeff_add,coeff_C_mul,coeff_X_pow,hAc,show 2*K≠4*K by omega]
  have hbW : QuadraticConstruction.locatorCoeffB W K=b := by
    change (subspacePolynomial W).coeff K=b
    rw [←hPW]
    simp [P,b,coeff_add,coeff_C_mul,coeff_X_pow,show K≠4*K by omega,show K≠2*K by omega]
  have hz₀ : z₀=a^3+b^2 := by rw [hb]; ring_nf; simp [CharTwo.two_eq_zero]
  have hlabel : z=QuadraticConstruction.locatorLabel φ θ W K := by
    simpa only [QuadraticConstruction.locatorLabel,haW,hbW,←hz₀] using hz
  refine ⟨W,hWD,hWsize,hlabel,?_⟩

  -- Recover the original explaining polynomial through its two coordinate polynomials.
  rw [haW,←hPW]
  have hmaprel := congrArg (Polynomial.map φ) hrelation
  simp only [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_C] at hmaprel
  have hPmap : P.map φ=X^(4*K)+C (φ a)*X^(2*K)+A.map φ := by
    simp [P]
  have hQmap : Q.map φ=X^(8*K)+C (φ z₀)*X^(2*K)+B₀.map φ := by
    simp [Q]
  have hAm : A.map φ=X*h₁.map φ := by simp [A]
  have hBm : B₀.map φ=X*h₀.map φ := by simp [B₀]
  have hpair : X*p=B₀.map φ+C θ*A.map φ := by rw [hpform,hAm,hBm]; ring
  calc
    X*p = B₀.map φ+C θ*A.map φ := hpair
    _ = (Q.map φ+C θ*P.map φ)+X^(8*K)+C θ*X^(4*K)+C z*X^(2*K) := by
      rw [hQmap,hPmap,hz]
      simp only [map_add,map_mul,mul_add]
      ring_nf
      simp [CharTwo.two_eq_zero]
    _ = (P.map φ)^2+C (φ (a^2)+θ)*P.map φ+X^(8*K)+C θ*X^(4*K)+C z*X^(2*K) := by
      rw [hmaprel,map_add]
      ring

end BinaryFieldCounterexamples
