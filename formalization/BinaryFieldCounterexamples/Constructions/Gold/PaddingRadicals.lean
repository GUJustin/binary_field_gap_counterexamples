/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Family
/-!
# Radical invariance of the actual Gold locator roots

A quadratic level with strictly more than half the points forces its linear
term to agree with the quadratic form on the polar radical: otherwise a radical
translation negates its Walsh sum, contradicting the strict majority. Thus the
existing majority-count witness contract already entails radical invariance.

The actual quotient locator vanishes precisely on the complementary quadratic
level. Its root set is consequently invariant under the polar radical, whose
cardinality is exactly the power required by the additive padding argument.
No radical-membership assumption is added to the locator family interface.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
open scoped BigOperators
open BinaryQuadraticData
/-- A repaired quadratic level is unchanged by its polar radical. -/
theorem quadraticRepair_add_radical {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (Q : BinaryQuadraticData V) (l : Module.Dual (ZMod 2) V) (κ : ZMod 2)
    (hl : l ∈ Q.repairs) (x : V) (r : Q.radical) :
    Q.toFun (x+(r:V))+l (x+(r:V))+κ=Q.toFun x+l x+κ := by
  have hr : Q.polarMap (r:V)=0 := r.property
  have hq := (Q.mem_repairs_iff l).mp hl r
  rw [Q.map_add_polar,map_add,hr]
  change Q.toFun x+Q.toFun r+0+(l x+l r)+κ=Q.toFun x+l x+κ
  linear_combination hq
/-- A strict-majority quadratic level forces its linear term to repair the polar radical. -/
theorem mem_quadraticRepairs_of_majority {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (Q : BinaryQuadraticData V) (l : Module.Dual (ZMod 2) V) (κ : ZMod 2)
    (hcount : Nat.card V<2*zeroCount (fun x => Q.toFun x+l x+κ)) : l ∈ Q.repairs := by
  apply (Q.mem_repairs_iff l).mpr
  intro r
  by_contra hn
  have hone : Q.toFun (r:V)+l r=1 := by
    rcases binary_eq_zero_or_one (Q.toFun (r:V)+l r) with hz | ho
    · exact (hn hz).elim
    · exact ho
  let g : V → ZMod 2 := fun x => Q.toFun x+l x+κ
  have hshift (x : V) : g (x+(r:V))=g x+1 := by
    have hr : Q.polarMap (r:V)=0 := r.property
    dsimp [g]
    rw [Q.map_add_polar,map_add,hr]
    change Q.toFun x+Q.toFun r+0+(l x+l r)+κ=Q.toFun x+l x+κ+1
    linear_combination hone
  have he : walshSum (fun x => g (x+(r:V)))=walshSum g := by
    exact Equiv.sum_comp (Equiv.addRight (r:V)) (fun x => binarySign (g x))
  have hg : walshSum g=0 := by
    simp_rw [hshift] at he
    rw [walshSum_add_one] at he
    omega
  have hc := walshSum_eq_two_mul_zeroCount_sub g
  rw [hg] at hc
  have hcount' : (Nat.card V:ℤ)<2*(zeroCount g:ℤ) := by exact_mod_cast hcount
  omega
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- The roots of the actual Gold locator are exactly the complementary repaired quadratic level. -/
theorem repairedLocator_eval_eq_zero_iff_level
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (ht0 : 2≤t) (ht : 2*t≤k+1)
    (hM : ∀ r, 1≤r → r<t → goldMoment D v A r=0) (hr : tensorPolarRank D v A=2*t)
    (hzeros : Nat.card {x : D // tensorQuadraticFunction D v A x+l x+κ=0}=2^k+2^(k-t))
    (x : D) :
    (repairedLocator D v A l κ t).eval (x:B)=0 ↔ tensorQuadraticFunction D v A x+l x+κ≠0 := by
  let H := repairedPolynomial D v A l κ
  let U := repairedSquareRoot t H
  have hdeg := (repairedPolynomial_natDegrees D k hD v A l κ t ht0 ht hM hr).1
  have hH : H≠0 := by
    intro he
    rw [show repairedPolynomial D v A l κ=0 from he,natDegree_zero] at hdeg
    have hp : 0<(2:ℕ)^k := by positivity
    have hp' : 0<(2:ℕ)^(k-t) := by positivity
    omega
  have hdiv : H ∣ subspacePolynomial D := (repairedPolynomial_dvd_locator D k hD v A l κ t ht0 ht hM hr hzeros).1
  have hder : H.derivative=U^2 := (repairedSquareRoot_sq t (by omega) H
    (repairedPolynomial_derivative_support D k hD v A l κ t hM)).symm
  have hAS : H^2+H=C ((normalizingRoot D)^2)*subspacePolynomial D*U^2 := by
    rw [show H^2+H=normalizedLocator D*H.derivative from repairedPolynomial_artinSchreier D v A l κ,
      hder,normalizedLocator,←normalizingRoot_sq]
  rw [repairedLocator,quotientLocator_eval_eq_zero_iff (normalizingRoot D) U (subspacePolynomial D) H
    hH hdiv hAS (x:B) ((subspacePolynomial_eval_eq_zero_iff D (x:B)).mpr x.property)]
  change H.eval (x:B)≠0 ↔ _
  rw [show H=repairedPolynomial D v A l κ from rfl,repairedPolynomial_eval,_root_.map_ne_zero]
/-- Every actual majority repair makes the Gold locator root set radical-invariant. -/
theorem repairedLocator_roots_add_radical
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (ht0 : 2≤t) (ht : 2*t≤k+1)
    (hM : ∀ r, 1≤r → r<t → goldMoment D v A r=0) (hr : tensorPolarRank D v A=2*t)
    (hzeros : Nat.card {x : D // tensorQuadraticFunction D v A x+l x+κ=0}=2^k+2^(k-t))
    (x : D) (r : (tensorQuadraticData D v A).radical) :
    (repairedLocator D v A l κ t).eval ((x+(r:D)):B)=0 ↔
      (repairedLocator D v A l κ t).eval (x:B)=0 := by
  have hcount : Nat.card D<2*zeroCount
      (fun x => (tensorQuadraticData D v A).toFun x+(l.toZModLinearMap 2) x+κ) := by
    change Nat.card D<2*Nat.card {x : D // tensorQuadraticFunction D v A x+l x+κ=0}
    rw [hD,hzeros,pow_succ]
    have hp : 0<(2:ℕ)^(k-t) := by positivity
    omega
  have hl := mem_quadraticRepairs_of_majority (tensorQuadraticData D v A) (l.toZModLinearMap 2) κ hcount
  have he := quadraticRepair_add_radical (tensorQuadraticData D v A) (l.toZModLinearMap 2) κ hl x r
  change tensorQuadraticFunction D v A (x+(r:D))+l (x+(r:D))+κ=tensorQuadraticFunction D v A x+l x+κ at he
  have hh := repairedLocator_eval_eq_zero_iff_level D k hD v A l κ t ht0 ht hM hr hzeros (x+(r:D))
  rw [he] at hh
  exact hh.trans (repairedLocator_eval_eq_zero_iff_level D k hD v A l κ t ht0 ht hM hr hzeros x).symm
/-- The actual invariant radical has precisely the codimension required by padding. -/
theorem cardinal_tensorQuadraticData_radical
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D=2^k) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (t : ℕ)
    (ht : 2*t≤k) (hr : tensorPolarRank D v A=2*t) :
    Nat.card (tensorQuadraticData D v A).radical=2^(k-2*t) := by
  rw [card_radical_of_polarRank (tensorQuadraticData D v A) (2*t) (by rw [tensorQuadraticData_rank,hr]),hD,
    Nat.pow_div ht (by decide : 0<2)]
end BinaryFieldCounterexamples.Gold
