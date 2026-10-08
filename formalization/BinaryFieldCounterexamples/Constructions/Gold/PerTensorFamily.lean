/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FullLocatorFamily
/-!
# Lemma 5.12: the exact family for each fixed matrix

The admissible labels for one matrix are its radical-compatible repairs.
Choosing the unique majority sign and using parameter injectivity gives exactly
`2^(2t)` distinct locators, now with the full manuscript correction polynomial.
The all-matrix companion is `exists_repairedLocator_family_full`.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- Lemma 5.12, exact per-matrix population: every rank-`2t` moment tensor
contributes exactly `2^(2t)` distinct monic full-source locators with the
majority level, exact correction degree, roots and recovery identity.
The same witnesses satisfy the coset and arbitrary-extension collision
clauses of `repairedLocator_properties_full`. -/
theorem exists_repairedLocator_family_per_tensor_full (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j)=if i=j then 1 else 0)
    (A : TensorCoordinates d) (t : ℕ) (ht0 : 2≤t) (ht : 2*t≤k+1)
    (hM : ∀ r, 1≤r → r<t → goldMoment D v A r=0) (hr : tensorPolarRank D v A=2*t) :
    ∃ ps : Finset B[X], ps.card=2^(2*t) ∧
      (∀ p ∈ ps, ∃ l : D →+ ZMod 2, ∃ κ : ZMod 2,
        p=repairedLocator D v A l κ t ∧
        Nat.card {y : D // tensorQuadraticFunction D v A y+l y+κ=0}=2^k+2^(k-t) ∧
        p.Monic ∧ p.natDegree=2^k ∧
        (p+goldFullSourcePolynomial D).natDegree=2^(k-1)-2^(k-t-1) ∧
        Nat.card {y : D // p.eval (y:B)=0}=2^k-2^(k-t) ∧
        (∀ y : D, p.eval (y:B)=0 ↔ tensorQuadraticFunction D v A y+l y+κ≠0) ∧
        p.derivative*(p^2+subspacePolynomial D)=C ((subspacePolynomial D).coeff 1)*p) ∧
      (∀ l : Module.Dual (ZMod 2) D, l ∈ (tensorQuadraticData D v A).repairs →
        ∃ κ : ZMod 2, repairedLocator D v A l.toAddMonoidHom κ t ∈ ps ∧
          Nat.card {y : D // tensorQuadraticFunction D v A y+l y+κ=0}=2^k+2^(k-t)) := by
  classical
  let Q := tensorQuadraticData D v A
  have hdim : Module.finrank (ZMod 2) D=k+1 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hD,Nat.card_eq_fintype_card,ZMod.card] at hc
    exact (Nat.pow_right_injective (by decide : 1<2)) hc.symm
  have hbit (l : Q.repairs) : ∃ κ : ZMod 2,
      Nat.card {y : D // tensorQuadraticFunction D v A y+l.val y+κ=0}=2^k+2^(k-t) := by
    obtain ⟨κ,hκ,_⟩ := BinaryQuadraticData.exists_bit_zeroCount_of_polarRank Q l.val l.property
      (k+1) t (by omega) hdim (by rw [tensorQuadraticData_rank]; exact hr)
    refine ⟨κ,?_⟩
    have heq : k+1-t-1=k-t := by omega
    simpa only [BinaryQuadraticData.zeroCount,Q,tensorQuadraticData,BinaryQuadraticData.toFun,
      BinaryQuadraticData.mk,Nat.add_sub_cancel,heq] using hκ
  choose κ hκ using hbit
  let P : Q.repairs → B[X] := fun l ↦ repairedLocator D v A l.val.toAddMonoidHom (κ l) t
  have hH (l : Q.repairs) : repairedPolynomial D v A l.val.toAddMonoidHom (κ l)≠0 := by
    intro hz
    have hd := (repairedPolynomial_natDegrees D k hD v A l.val.toAddMonoidHom (κ l)
      t ht0 ht hM hr).1
    rw [hz,natDegree_zero] at hd
    have : 0<(2:ℕ)^k+2^(k-t) := by positivity
    omega
  have hdiv (l : Q.repairs) := (repairedPolynomial_dvd_locator D k hD v A l.val.toAddMonoidHom (κ l)
    t ht0 ht hM hr (hκ l)).1
  have hP : Function.Injective P := by
    intro l l' he
    have hl := (repairedLocator_injective_parameters D k hD v x hdual A A
      l.val.toAddMonoidHom l'.val.toAddMonoidHom (κ l) (κ l') t (by omega) hM hM
      (hH l) (hH l') (hdiv l) (hdiv l') he).2.1
    apply Subtype.ext
    ext y
    exact congrArg (fun f : D →+ ZMod 2 ↦ f y) hl
  refine ⟨Finset.univ.image P,?_,?_,?_⟩
  · rw [Finset.card_image_iff.mpr hP.injOn,Finset.card_univ,Fintype.card_coe]
    exact BinaryQuadraticData.card_repairs_of_polarRank Q t (by rw [tensorQuadraticData_rank]; exact hr)
  · intro p hp
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
    have hf := repairedLocator_properties_full.{_,0} D k hD v A l.val.toAddMonoidHom (κ l) t
      ht0 ht hM hr (hκ l)
    exact ⟨l.val.toAddMonoidHom,κ l,rfl,hκ l,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,
      hf.2.2.2.2.1,hf.2.2.2.2.2.1⟩
  · intro l hl
    let z : Q.repairs := ⟨l,hl⟩
    exact ⟨κ z,Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩,hκ z⟩
end BinaryFieldCounterexamples.Gold
