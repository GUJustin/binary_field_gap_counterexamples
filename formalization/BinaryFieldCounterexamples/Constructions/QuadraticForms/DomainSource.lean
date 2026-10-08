/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SourceBound
public import BinaryFieldCounterexamples.Polynomial.PrimePowerSupport
public import BinaryFieldCounterexamples.Polynomial.LocatorRemainders
/-!
# The quarter-rate first input on an actual scalar subspace

The product locator's proved q-power support supplies the canonical numerator.
For a domain of size q^d with d at least three, the message length q^(d-2)
automatically has the required characteristic divisibility, and the first-input
bound keeps the paper's exact rational floor.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial

/-- The canonical numerator for an actual scalar-submodule locator satisfies the first-input bound. -/
theorem agreementLE_submodulePrimePowerQuarterNumerator
    {k F : Type*} [Field k] [Fintype k] [Field F] [Fintype F] [Algebra k F]
    (p r : ℕ) [Fact p.Prime] [CharP F p] (hr : 1 ≤ r)
    (hq : Fintype.card k = p^r) (D : Submodule k F) [Fintype D]
    (S : Finset F) (hS : ∀ x, x ∈ S ↔ x ∈ D)
    (β : F) (hβ : β ∉ D) (K : ℕ) (hK : 2 ≤ K) (hKchar : (K:F) = 0)
    (hcard : Fintype.card D = (p^r)^2*K) :
    agreementLE S K
      (fun x => (primePowerQuarterNumerator p r (subspacePolynomial D.toAddSubgroup) β).eval
        (x:F) * ((x:F)-β)⁻¹)
      (((p^r+1)*K-2)/2) := by
  apply agreementLE_primePowerQuarterNumerator p r hr S β
    (fun hx => hβ ((hS β).mp hx)) K hK hKchar
    (subspacePolynomial D.toAddSubgroup) (subspacePolynomial_coeff_one_ne_zero _)
  · intro x hx
    exact (subspacePolynomial_eval_eq_zero_iff _ x).mpr ((hS x).mp hx)
  · intro hz
    exact hβ ((subspacePolynomial_eval_eq_zero_iff _ β).mp hz)
  · intro n hn
    obtain ⟨i, hi⟩ := FiniteFieldLocator.subspacePolynomial_q_support D n hn
    exact ⟨i, by simpa only [hq] using hi⟩
  · rw [subspacePolynomial_natDegree]
    exact hcard.le

/-- A domain of size q^d supplies all numerical and characteristic hypotheses of the quarter-rate first-input bound. -/
theorem agreementLE_submoduleQuarterSource
    {k F : Type*} [Field k] [Fintype k] [Field F] [Fintype F] [Algebra k F]
    (p r : ℕ) [Fact p.Prime] [CharP F p] (hr : 1 ≤ r)
    (hq : Fintype.card k = p^r) (D : Submodule k F) [Fintype D]
    (S : Finset F) (hS : ∀ x, x ∈ S ↔ x ∈ D)
    (β : F) (hβ : β ∉ D) (d : ℕ) (hd : 3 ≤ d)
    (hcard : Fintype.card D = (Fintype.card k)^d) :
    agreementLE S ((Fintype.card k)^(d-2))
      (fun x => (primePowerQuarterNumerator p r (subspacePolynomial D.toAddSubgroup) β).eval
        (x:F) * ((x:F)-β)⁻¹)
      ⌊((Fintype.card k+1 : ℚ)*Fintype.card D/(2*(Fintype.card k)^2)-1)⌋₊ := by
  have hb : 2 ≤ Fintype.card k := Fintype.one_lt_card
  have hK : 2 ≤ (Fintype.card k)^(d-2) :=
    hb.trans (Nat.le_self_pow (by omega) _)
  have hKchar : (((Fintype.card k)^(d-2) : ℕ) : F) = 0 := by
    have hqzero : ((Fintype.card k : ℕ) : F) = 0 := by
      rw [← map_natCast (algebraMap k F), FiniteField.cast_card_eq_zero, map_zero]
    rw [Nat.cast_pow, hqzero, zero_pow (by omega : d-2 ≠ 0)]
  have hfactor : Fintype.card D = (Fintype.card k)^2*(Fintype.card k)^(d-2) := by
    rw [hcard, ← pow_add]
    congr 1
    omega
  rw [primePowerQuarterSource_floor (Fintype.card k) _ _ hb hK hfactor]
  simpa only [← hq] using agreementLE_submodulePrimePowerQuarterNumerator p r hr hq D S hS β hβ
    ((Fintype.card k)^(d-2)) hK hKchar (by simpa only [← hq] using hfactor)

end BinaryFieldCounterexamples
