/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.PerTensorFamily
public import BinaryFieldCounterexamples.Constructions.Gold.LevelLocator
/-!
# Lemma 5.12: the complete Gold locator contract

The exact per-matrix label families and the distinct all-matrix family are
assembled with every clause for the full square-root word. All root sets,
radicals, polynomial degrees and extension collisions are concrete.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
universe u w
open Polynomial
attribute [local instance] Classical.decEq
variable {B : Type u} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- Lemma 5.12 in one complete contract: the exact per-matrix repair count,
all-matrix distinct population, monicity, full-source correction degree,
quadratic level roots, recovery, radical dimension and cosets, and collisions
in arbitrary containing fields. The literal level-locator formula announced
in Section 5.3 is proved in `repairedLocator_levelLocator_eq`. -/
theorem gold_locators_full (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j)=if i=j then 1 else 0)
    (t : ℕ) (ht0 : 2≤t) (ht : 2*t≤k+1) :
    ∃ ps : Finset B[X], ps.card=(momentTensors D v t).card*2^(2*t) ∧
      (∀ p ∈ ps, ∃ A ∈ momentTensors D v t, ∃ l : D →+ ZMod 2, ∃ κ : ZMod 2,
        p=repairedLocator D v A l κ t ∧
        Nat.card {y : D // tensorQuadraticFunction D v A y+l y+κ=0}=2^k+2^(k-t) ∧
        p.Monic ∧ p.natDegree=2^k ∧
        (p+goldFullSourcePolynomial D).natDegree=2^(k-1)-2^(k-t-1) ∧
        Nat.card {y : D // p.eval (y:B)=0}=2^k-2^(k-t) ∧
        (∀ y : D, p.eval (y:B)=0 ↔ tensorQuadraticFunction D v A y+l y+κ≠0) ∧
        p.derivative*(p^2+subspacePolynomial D)=C ((subspacePolynomial D).coeff 1)*p ∧
        Nat.card (tensorQuadraticData D v A).radical=2^(k+1-2*t) ∧
        Module.finrank (ZMod 2) (tensorQuadraticData D v A).radical=k+1-2*t ∧
        (∀ (y : D) (r : (tensorQuadraticData D v A).radical),
          p.eval ((y+(r:D)):B)=0 ↔ p.eval (y:B)=0)) ∧
      (∀ {F : Type w} [Field F] [CharP F 2] (φ : B →+* F),
        ∀ p ∈ ps, ∀ q ∈ ps, p≠q → ∀ S : Finset F,
        (∀ β ∈ S, ((subspacePolynomial D).map φ).eval β≠0) →
        (S.filter fun β ↦ (p.map φ).eval β=(q.map φ).eval β).card ≤ 2^(k+1-2*t)) ∧
      (∀ A ∈ momentTensors D v t,
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
              Nat.card {y : D // tensorQuadraticFunction D v A y+l y+κ=0}=2^k+2^(k-t)) ) := by
  obtain ⟨ps,hcard,hprops,hcoll⟩ := exists_repairedLocator_family_full.{u,w}
    D k hD v x hdual t ht0 ht
  refine ⟨ps,hcard,hprops,hcoll,?_⟩
  intro A hA
  obtain ⟨hr,hM⟩ := (mem_momentTensors D v t A).mp hA
  exact exists_repairedLocator_family_per_tensor_full D k hD v x hdual A t ht0 ht hM hr
end BinaryFieldCounterexamples.Gold
