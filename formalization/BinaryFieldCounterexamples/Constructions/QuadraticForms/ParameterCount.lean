/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceRadical
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Separable
/-!
# Cardinality of the actual quadratic trace family

The middle coefficient is counted by the split, separable polynomial
`X^(q^n)-X`, which divides the full-field polynomial. Coefficient recovery then
identifies the cardinality of the actual finite family of quadratic forms.
This counts the entire family; the distribution of its quadratic ranks and
types remains a separate theorem.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype

/-- There are exactly q^n actual coefficients fixed by the middle Frobenius. -/
theorem card_half_fixed_coefficients
    {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (n : ℕ) (hn : 1 ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) :
    (Finset.univ.filter fun c : B => c^((Fintype.card k)^n)=c).card = (Fintype.card k)^n := by
  let q := Fintype.card k
  let a := q^n
  let P : B[X] := X^a-X
  have hq : 1 < q := Fintype.one_lt_card
  have ha : 1 < a := Nat.one_lt_pow (by omega) hq
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero B ha
  have hd : P.natDegree = a := FiniteField.X_pow_card_sub_X_natDegree_eq B ha
  have hdiv : P ∣ X^(Fintype.card B)-X := by
    have hh := sub_dvd_pow_sub_pow (X^a : B[X]) X a
    have hh' : P ∣ (X^a)^a-X^a + P := dvd_add hh (dvd_refl P)
    have he : a*a = Fintype.card B := by
      rw [hcard]
      change q^n*q^n=q^(2*n)
      rw [← pow_add]
      congr 1
      omega
    simpa only [P, ← pow_mul, he, sub_add_sub_cancel] using hh'
  have hbig : (X^(Fintype.card B)-X : B[X]).Splits := by
    apply splits_iff_card_roots.mpr
    rw [FiniteField.roots_X_pow_card_sub_X, ← Finset.card_def, Finset.card_univ,
      FiniteField.X_pow_card_sub_X_natDegree_eq B Fintype.one_lt_card]
  have hs : P.Splits := hbig.of_dvd
    (FiniteField.X_pow_card_sub_X_ne_zero B Fintype.one_lt_card) hdiv
  have hq0 : (q:B)=0 := by
    rw [show q=Fintype.card k from rfl, ← map_natCast (algebraMap k B),
      FiniteField.cast_card_eq_zero, map_zero]
  have hpder : P.derivative = -1 := by
    simp [P, derivative_pow, a, Nat.cast_pow, hq0, show n ≠ 0 by omega]
  have hsep : P.Separable := by
    rw [separable_def, hpder]
    exact ⟨0, -1, by ring⟩
  have heq : (Finset.univ.filter fun c : B => c^((Fintype.card k)^n)=c) = P.roots.toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      mem_roots hP, IsRoot.def, P, eval_sub, eval_pow, eval_X, sub_eq_zero, a, q]
  rw [heq, Multiset.toFinset_card_of_nodup (nodup_roots hsep), ← hs.natDegree_eq_card_roots, hd]

theorem traceFamilyIndex_card (n t : ℕ) (htn : t ≤ n) :
    Fintype.card (TraceFamilyIndex n t) = n-t := by
  let e : TraceFamilyIndex n t ≃ Fin (n-t) :=
    { toFun := fun i => ⟨i.val.val-t, by have hi := i.val.isLt; have hi2 := i.property; omega⟩
      invFun := fun j => ⟨⟨j.val+t, by have hj := j.isLt; omega⟩, by change t ≤ j.val+t; omega⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        dsimp
        have hi := i.property
        omega
      right_inv := by
        intro j
        apply Fin.ext
        dsimp
        omega }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

/-- The literal coefficient parameter space has the required exact cardinality. -/
theorem trace_parameter_card
    {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (n t : ℕ) (hn : 1 ≤ n) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) :
    Fintype.card ((TraceFamilyIndex n t → B) × {c : B // c^((Fintype.card k)^n)=c}) =
      (Fintype.card k)^(2*n*(n-t)+n) := by
  rw [Fintype.card_prod, Fintype.card_fun, traceFamilyIndex_card n t htn,
    Fintype.card_subtype, card_half_fixed_coefficients n hn hcard, hcard,
    ← pow_mul, ← pow_add]

/-- The finite family of actual scalar-valued quadratic forms obtained from all allowed parameters. -/
noncomputable def traceQuadraticFamily
    {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) : Finset (QuadraticForm k B) :=
  Finset.univ.image fun u : (TraceFamilyIndex n t → B) × {c : B // c^((Fintype.card k)^n)=c} =>
    traceFamilyQuadraticForm n t ht htn u.1 u.2.val hcard u.2.property

/-- Parameter recovery gives the cardinality of the entire actual quadratic trace family. -/
theorem traceQuadraticFamily_card
    {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) :
    (traceQuadraticFamily (k:=k) (B:=B) n t ht htn hcard).card =
      (Fintype.card k)^(2*n*(n-t)+n) := by
  unfold traceQuadraticFamily
  have hi : Function.Injective (fun u : (TraceFamilyIndex n t → B) ×
      {c : B // c^((Fintype.card k)^n)=c} =>
      traceFamilyQuadraticForm n t ht htn u.1 u.2.val hcard u.2.property) := by
    intro u v huv
    obtain ⟨ha, hc⟩ := traceFamily_parameters_eq_of_quadraticForm_eq n t ht htn
      u.1 v.1 u.2.val v.2.val hcard u.2.property v.2.property huv
    exact Prod.ext ha (Subtype.ext hc)
  rw [Finset.card_image_of_injective _ hi, Finset.card_univ]
  exact trace_parameter_card n t (by omega) htn hcard

end BinaryFieldCounterexamples.QuadraticFormTrace
