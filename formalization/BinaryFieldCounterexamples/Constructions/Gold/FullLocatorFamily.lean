/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FullSource
/-!
# Lemma 5.12: assembled locators for the full manuscript word

This companion keeps the existing locator construction and states its exact
full-source correction degree, roots, recovery identity, radical invariance,
and extension-field collision bound together for the same finite family.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
universe u w
open Polynomial
attribute [local instance] Classical.decEq
variable {B : Type u} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- Lemma 5.12(2): the actual polar radical has dimension `d-2t`,
not merely the equivalent cardinality. -/
theorem finrank_tensorQuadraticData_radical (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D=2^k) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (t : ℕ)
    (ht : 2*t≤k) (hr : tensorPolarRank D v A=2*t) :
    Module.finrank (ZMod 2) (tensorQuadraticData D v A).radical=k-2*t := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := (tensorQuadraticData D v A).radical)
  rw [cardinal_tensorQuadraticData_radical D k hD v A t ht hr,
    Nat.card_eq_fintype_card,ZMod.card] at hc
  exact (Nat.pow_right_injective (by decide : 1<2)) hc.symm
/-- Lemma 5.12, all per-member clauses for the manuscript's full `R`, with the
actual radical and collisions with every other admissible locator in every
containing field. The zero-count hypothesis is the majority level selected
by Lemma 5.10, rather than an assumption about any desired polynomial clause. -/
theorem repairedLocator_properties_full (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (ht0 : 2≤t) (ht : 2*t≤k+1)
    (hM : ∀ r, 1≤r → r<t → goldMoment D v A r=0) (hr : tensorPolarRank D v A=2*t)
    (hzeros : Nat.card {x : D // tensorQuadraticFunction D v A x+l x+κ=0}=2^k+2^(k-t)) :
    let P := repairedLocator D v A l κ t
    P.Monic ∧ P.natDegree=2^k ∧
    (P+goldFullSourcePolynomial D).natDegree=2^(k-1)-2^(k-t-1) ∧
    Nat.card {x : D // P.eval (x:B)=0}=2^k-2^(k-t) ∧
    (∀ x : D, P.eval (x:B)=0 ↔ tensorQuadraticFunction D v A x+l x+κ≠0) ∧
    P.derivative*(P^2+subspacePolynomial D)=C ((subspacePolynomial D).coeff 1)*P ∧
    Nat.card (tensorQuadraticData D v A).radical=2^(k+1-2*t) ∧
    Module.finrank (ZMod 2) (tensorQuadraticData D v A).radical=k+1-2*t ∧
    (∀ (x : D) (r : (tensorQuadraticData D v A).radical),
      P.eval ((x+(r:D)):B)=0 ↔ P.eval (x:B)=0) ∧
    (∀ {F : Type w} [Field F] [CharP F 2] (φ : B →+* F)
      (A' : TensorCoordinates d) (l' : D →+ ZMod 2) (κ' : ZMod 2),
      (∀ r, 1≤r → r<t → goldMoment D v A' r=0) → tensorPolarRank D v A'=2*t →
      Nat.card {x : D // tensorQuadraticFunction D v A' x+l' x+κ'=0}=2^k+2^(k-t) →
      P ≠ repairedLocator D v A' l' κ' t → ∀ S : Finset F,
      (∀ β ∈ S, ((subspacePolynomial D).map φ).eval β≠0) →
      (S.filter fun β ↦ (P.map φ).eval β=((repairedLocator D v A' l' κ' t).map φ).eval β).card ≤
        2^(k+1-2*t)) := by
  dsimp only
  have hp := repairedLocator_properties D k hD v A l κ t ht0 ht hM hr hzeros
  refine ⟨hp.1,hp.2.1,repairedLocator_fullSource_natDegree D k hD v A l κ t ht0 ht hM hr hzeros,
    hp.2.2.2.1,?_,hp.2.2.2.2,cardinal_tensorQuadraticData_radical D (k+1) hD v A t ht hr,
    finrank_tensorQuadraticData_radical D (k+1) hD v A t ht hr,?_,?_⟩
  · exact repairedLocator_eval_eq_zero_iff_level D k hD v A l κ t ht0 ht hM hr hzeros
  · exact repairedLocator_roots_add_radical D k hD v A l κ t ht0 ht hM hr hzeros
  · intro F _ _ φ A' l' κ' hM' hr' hzeros' hne S hext
    exact card_mapped_repairedLocator_collisions_le φ φ.injective D k hD v A A' l l' κ κ' t
      ht0 ht hM hM' hr hr' hzeros hzeros' hne S hext
/-- Lemma 5.12 assembled over all matrices: the same distinct finite family
has the exact repair population, full-source degree, exact roots, recovery,
and coset invariance. Extension collision clauses are supplied for each of
these same members by `repairedLocator_properties_full`. -/
theorem exists_repairedLocator_family_full (D : AddSubgroup B) [Fintype D]
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
        (S.filter fun β ↦ (p.map φ).eval β=(q.map φ).eval β).card ≤ 2^(k+1-2*t)) := by
  obtain ⟨ps,hcard,hps⟩ := exists_repairedLocator_family D k hD v x hdual t ht0 ht
  refine ⟨ps,hcard,?_,?_⟩
  · intro p hp
    obtain ⟨A,hA,l,κ,rfl,hzeros⟩ := hps p hp
    obtain ⟨hr,hM⟩ := (mem_momentTensors D v t A).mp hA
    have hf := repairedLocator_properties_full.{u,w} D k hD v A l κ t ht0 ht hM hr hzeros
    exact ⟨A,hA,l,κ,rfl,hzeros,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,
      hf.2.2.2.2.2.1,hf.2.2.2.2.2.2.1,hf.2.2.2.2.2.2.2.1,hf.2.2.2.2.2.2.2.2.1⟩
  · intro F _ _ φ p hp q hq hne S hext
    obtain ⟨A,hA,l,κ,rfl,hzeros⟩ := hps p hp
    obtain ⟨A',hA',l',κ',rfl,hzeros'⟩ := hps q hq
    obtain ⟨hr,hM⟩ := (mem_momentTensors D v t A).mp hA
    obtain ⟨hr',hM'⟩ := (mem_momentTensors D v t A').mp hA'
    exact card_mapped_repairedLocator_collisions_le φ φ.injective D k hD v A A' l l' κ κ' t
      ht0 ht hM hM' hr hr' hzeros hzeros' hne S hext
end BinaryFieldCounterexamples.Gold
