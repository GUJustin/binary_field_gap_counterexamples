/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.QuadraticCodePopulation
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceRadicalIncidence

/-!
# Minimum-rank population in the trace code

A choice of coordinates transports the concrete additive trace code to the
coordinate quadratic code used by the Fourier argument. Rank and cardinality
are preserved, yielding the literal Schmidt lower bound for `traceRankFamily`.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticFormTrace
open BinaryFieldCounterexamples.QuadraticCoordinates
open QuadraticGeometry
set_option warn.classDefReducibility false
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype

/-- Pullback along a linear equivalence gives an actual linear equivalence of quadratic-form spaces. -/
noncomputable def quadraticFormPullbackEquiv {k V W : Type*} [CommSemiring k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (e : W ≃ₗ[k] V) : QuadraticForm k V ≃ₗ[k] QuadraticForm k W := by
  exact
    { toFun := fun Q => Q.comp e.toLinearMap
      invFun := fun R => R.comp e.symm.toLinearMap
      left_inv := by
        intro Q
        ext x
        simp
      right_inv := by
        intro Q
        ext x
        simp
      map_add' := by
        intro Q R
        ext x
        simp
      map_smul' := by
        intro a Q
        ext x
        simp }

variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- The concrete trace code contains the Schmidt lower bound of minimum-rank forms. -/
theorem traceRankFamily_card_lower
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) :
    ((Fintype.card k)^t-1)*gaussianPascal ((Fintype.card k)^2) n t ≤
      (traceRankFamily n t ht htn hcard (2*t)).card := by
  have hdim : Module.finrank k B=2*n := by
    have hd := Module.natCard_eq_pow_finrank (K:=k) (V:=B)
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,hcard] at hd
    exact Nat.pow_right_injective Fintype.one_lt_card hd.symm
  let b := Module.finBasisOfFinrankEq k B hdim
  let e : (Fin (2*n)→k) ≃ₗ[k] B := b.equivFun.symm
  let : CharP k p := (algebraMap k B).charP (algebraMap k B).injective p
  let pull := quadraticFormPullbackEquiv e
  let C0 := traceQuadraticCode (k:=k) (B:=B) n t ht htn hcard
  let C := C0.map pull.toLinearMap
  let ec : C0 ≃ₗ[k] C := Submodule.equivMapOfInjective pull.toLinearMap pull.injective C0
  let : Fintype (QuadraticForm k B) := Fintype.ofInjective
    (fun Q : QuadraticForm k B => (Q : B → k)) DFunLike.coe_injective
  let : Fintype C0 := Fintype.ofFinite C0
  let : Fintype C := Fintype.ofEquiv C0 ec
  have hCcard : Fintype.card C=(Fintype.card k)^((2*n+1)*(n-t))*(Fintype.card k)^t := by
    rw [Fintype.card_congr ec.symm.toEquiv,←Nat.card_eq_fintype_card]
    exact traceQuadraticCode_natCard_eq_moment_scale n t ht htn hcard
  have hCrank (Q : C) : Module.finrank k ((Fin (2*n)→k) ⧸ Q.val.radical) =
      Module.finrank k (B ⧸ (ec.symm Q).val.radical) := by
    have hv : Q.val=pull (ec.symm Q).val := by
      have hh := congrArg Subtype.val (ec.apply_symm_apply Q)
      exact hh.symm.trans (Submodule.coe_equivMapOfInjective_apply
        pull.toLinearMap pull.injective C0 (ec.symm Q))
    rw [hv]
    change Module.finrank k ((Fin (2*n)→k) ⧸
      ((ec.symm Q).val.comp e.toLinearMap).radical) =
        Module.finrank k (B ⧸ (ec.symm Q).val.radical)
    rw [radical_quotient_finrank,radical_quotient_finrank]
    have heq : (ec.symm Q).val.Equivalent
        ((ec.symm Q).val.comp e.toLinearMap) := by
      exact ⟨(ec.symm Q).val.isometryEquivOfCompLinearEquiv e⟩
    rw [←heq.rank_radical_eq]
    simp [hdim]
  have hCmin : ∀ Q : C, Q≠0 → 2*t ≤ Module.finrank k ((Fin (2*n)→k) ⧸ Q.val.radical) := by
    intro Q hQ
    rw [hCrank]
    rw [radical_quotient_finrank]
    apply traceQuadraticCode_minimum_rank p r hq n t ht htn hcard (ec.symm Q).val
      (ec.symm Q).property
    intro hz
    apply hQ
    apply ec.symm.injective
    simpa using hz
  have hpop := quadraticCode_minimumRank_population_lower p n t (by omega) htn
    C.toAddSubgroup hCcard hCmin
  -- Transfer the coordinate rank filter back to the literal trace rank layer.
  have hfilters :
      (Finset.univ.filter (fun Q : C =>
        Module.finrank k ((Fin (2*n)→k) ⧸ Q.val.radical)=2*t)).card =
      (traceRankFamily n t ht htn hcard (2*t)).card := by
    apply Finset.card_bij (fun Q _ => (ec.symm Q).val)
    · intro Q hQ
      apply Finset.mem_filter.mpr
      refine ⟨(mem_traceQuadraticCode_iff n t ht htn hcard _).mp
        (ec.symm Q).property,?_⟩
      rw [←radical_quotient_finrank,←hCrank Q]
      exact (Finset.mem_filter.mp hQ).2
    · intro Q _ R _ he
      apply ec.symm.injective
      exact Subtype.ext he
    · intro R hR
      have hm := Finset.mem_filter.mp hR
      let R0 : C0 := ⟨R,(mem_traceQuadraticCode_iff n t ht htn hcard R).mpr hm.1⟩
      let Q : C := ec R0
      have hQ : Q∈Finset.univ.filter (fun Q : C =>
          Module.finrank k ((Fin (2*n)→k) ⧸ Q.val.radical)=2*t) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        have hback : (ec.symm Q).val=R := by simp [Q,R0]
        rw [hCrank Q,hback,radical_quotient_finrank]
        exact hm.2
      refine ⟨Q,hQ,?_⟩
      change (ec.symm (ec R0)).val=R
      simp [R0]
  exact hpop.trans_eq hfilters

end BinaryFieldCounterexamples.QuadraticFormTrace
