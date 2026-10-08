/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.PairWitnesses
/-!
# Boolean factor data under a field embedding

Mapping the same polynomial and additive domain preserves the saturated root
count, degree, divisibility and differential identity consumed by the canonical
input-pair construction. No new polynomial is selected during transport.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.NearUnit
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
/-- The literal mapped polynomial keeps every Boolean-factor input required
by the fixed-pair challenge construction. -/
theorem mapped_booleanFactor_data
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F]
    (phi : B →+* F) (D : AddSubgroup B) (H : B[X]) (m : ℕ)
    (hH : H≠0) (hdeg : H.natDegree=m)
    (hroots : ((additiveDomain D).filter fun x => H.eval x=0).card=m)
    (hdiv : H∣subspacePolynomial D)
    (hbool : H^2+H=C (((subspacePolynomial D).coeff 1)⁻¹)*subspacePolynomial D*H.derivative) :
    H.map phi≠0 ∧ (H.map phi).natDegree=m ∧
    ((additiveDomain (D.map phi.toAddMonoidHom)).filter fun x => (H.map phi).eval x=0).card=m ∧
    H.map phi ∣ subspacePolynomial (D.map phi.toAddMonoidHom) ∧
    (H.map phi)^2+H.map phi =
      C (((subspacePolynomial (D.map phi.toAddMonoidHom)).coeff 1)⁻¹)*
        subspacePolynomial (D.map phi.toAddMonoidHom)*(H.map phi).derivative := by
  refine ⟨Polynomial.map_ne_zero hH, by simpa using hdeg, ?_, ?_, ?_⟩
  · rw [Gold.card_mapped_locator_roots]
    have hc := Gold.agreementCount_add_source_eq_roots D 0 H
    rw [agreementCount_eq_card_filter (additiveDomain D)
      (fun x : B => (0:B[X]).eval x) (H+0)] at hc
    have hc' : ((additiveDomain D).filter fun x => H.eval x=0).card =
        Nat.card {x : D // H.eval (x:B)=0} := by
      simpa only [add_zero,eval_zero] using hc
    rw [←hc',hroots]
  · rw [←map_subspacePolynomial phi D]
    exact Polynomial.map_dvd phi hdiv
  · have he := congrArg (Polynomial.map phi) hbool
    simpa only [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_mul,map_C,
      map_inv₀,←coeff_subspacePolynomial_map, map_subspacePolynomial,←derivative_map] using he
end BinaryFieldCounterexamples.NearUnit
