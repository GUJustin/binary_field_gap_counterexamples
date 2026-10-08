/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TranslationCount
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceCode
/-!
# Distinct translations of the actual trace family

The literal trace coefficients are recovered from the polar form, even in
characteristic two. The exact translated-function count therefore applies to
any actual constant-rank subfamily, without presuming its rank distribution.
-/
@[expose] public section
set_option warn.classDefReducibility false
namespace BinaryFieldCounterexamples.QuadraticFormTrace
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype

/-- Polar forms recover actual code elements in every characteristic. -/
theorem traceQuadraticCode_polar_injective (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) :
    Function.Injective (fun Q : traceQuadraticCode (k:=k) (B:=B) n t ht htn hcard =>
      Q.val.polarBilin) := by
  intro Q R h
  obtain ⟨u,hu⟩ := Q.property
  obtain ⟨v,hv⟩ := R.property
  apply Subtype.ext
  rw [←hu,←hv]
  have hp : u=v := by
    have h' : Q.val.polarBilin=R.val.polarBilin := h
    rw [←hu,←hv] at h'
    obtain ⟨ha,hc⟩ := traceFamily_parameters_eq_of_polarBilin_eq n t ht htn
      u.1 v.1 u.2.val v.2.val hcard _ _ h'
    exact Prod.ext ha (Subtype.ext hc)
  rw [hp]

/-- Exact translated-function count for an actual constant-rank subfamily of the trace family. -/
theorem traceQuadraticFamily_translated_natCard (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (T : Finset (QuadraticForm k B))
    (hT : T ⊆ traceQuadraticFamily n t ht htn hcard) (r : ℕ)
    (hr : ∀ Q∈T,Module.finrank k B-Module.finrank k Q.radical=r) :
    Nat.card (Set.range (fun z : T × B => fun x => z.1.val (x-z.2))) =
      T.card * (Fintype.card k)^r := by
  have hinj : Function.Injective (fun Q : T => Q.val.polarBilin) := by
    intro Q R h
    have hQ := (mem_traceQuadraticCode_iff n t ht htn hcard Q.val).mpr (hT Q.property)
    have hR := (mem_traceQuadraticCode_iff n t ht htn hcard R.val).mpr (hT R.property)
    have he := traceQuadraticCode_polar_injective n t ht htn hcard
      (a₁:=⟨Q.val,hQ⟩) (a₂:=⟨R.val,hR⟩) h
    apply Subtype.ext
    exact congrArg (fun S : traceQuadraticCode n t ht htn hcard => S.val) he
  simpa using QuadraticGeometry.translatedFamilyRange_natCard (fun Q : T => Q.val)
    hinj r (fun Q => hr Q.val Q.property)
end BinaryFieldCounterexamples.QuadraticFormTrace
