/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.QuotientIncidence
/-!
# Reduction along an actual quadratic radical line

The quadratic radical maps onto the radical of any quotient inside it.
Rank-nullity therefore preserves quadratic rank; a one-dimensional radical
kernel contributes exactly one scalar-field factor to the actual zero count.
These are the radical branch identities for singular-line flag counting.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
/-- Quotienting by a subspace of the actual quadratic radical maps that radical onto the quotient radical. -/
theorem radical_lift_eq_map (Q : QuadraticForm k V) (N : Submodule k V) (hN : N≤Q.radical) :
    (Q.lift N hN).radical=Q.radical.map N.mkQ := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    constructor
    · intro hz
      refine ⟨z,?_,rfl⟩
      change z ∈ Q.radical
      rw [QuadraticMap.mem_radical_iff'] at hz ⊢
      refine ⟨hz.1,?_⟩
      intro w
      exact hz.2 (N.mkQ w)
    · rintro ⟨w,hw,he⟩
      rw [←he]
      change w ∈ Q.radical at hw
      rw [QuadraticMap.mem_radical_iff'] at hw ⊢
      refine ⟨hw.1,?_⟩
      intro y
      induction y using Submodule.Quotient.induction_on with
      | _ y => exact hw.2 y
/-- The radical dimension drops by precisely the dimension of the radical-contained quotient kernel. -/
theorem radical_lift_finrank_add [FiniteDimensional k V]
    (Q : QuadraticForm k V) (N : Submodule k V) (hN : N≤Q.radical) :
    Module.finrank k (Q.lift N hN).radical+Module.finrank k N=Module.finrank k Q.radical := by
  rw [radical_lift_eq_map]
  exact quotientMap_finrank_add N Q.radical hN
/-- Quotienting inside the quadratic radical preserves the actual quadratic rank. -/
theorem radical_lift_rank [FiniteDimensional k V]
    (Q : QuadraticForm k V) (N : Submodule k V) (hN : N≤Q.radical) :
    Module.finrank k (V ⧸ N)-Module.finrank k (Q.lift N hN).radical=
      Module.finrank k V-Module.finrank k Q.radical := by
  have h := radical_lift_finrank_add Q N hN
  have hd := N.finrank_quotient_add_finrank
  omega
/-- An actual radical line contributes exactly a factor q to the zero count. -/
theorem radical_line_zero_natCard [Fintype k] [Fintype V]
    (Q : QuadraticForm k V) (N : Submodule k V) (hN : N≤Q.radical)
    (hdim : Module.finrank k N=1) :
    Nat.card {x : V // Q x=0}=Fintype.card k*Nat.card {y : V ⧸ N // Q.lift N hN y=0} := by
  rw [quadratic_zero_natCard_quotient Q N hN,
    Module.natCard_eq_pow_finrank (K:=k),Nat.card_eq_fintype_card,hdim,pow_one]
end BinaryFieldCounterexamples.QuadraticGeometry
