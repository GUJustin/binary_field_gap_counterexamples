/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularFlags
/-!
# Grouping the actual singular-flag recurrence

Radical and nonradical singular lines have their actual cardinalities. Once
constant through-line fiber counts are established on each class, the proved
flag identity gives the exact two-branch recurrence. The fiber hypotheses
remain explicit; no rank/type enumeration is assumed here.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable singularLinesFintype totallySingularSubspacesFintype
variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]
/-- The actual singular lines inside the quadratic radical have the projective cardinality. -/
theorem singular_radical_lines_card (Q : QuadraticForm k V) :
    Nat.card {L : SingularLines Q // L.val≤Q.radical} =
      ((Fintype.card k)^(Module.finrank k Q.radical)-1)/(Fintype.card k-1) := by
  exact singularLinesInSubspace_card Q Q.radical (fun x hx => hx.1)
/-- Constant actual through-line fiber counts give the precise two-branch singular-flag recurrence. -/
theorem singular_flag_count_of_fiber_counts (Q : QuadraticForm k V) (e a b : ℕ)
    (ha : ∀ L : SingularLines Q, L.val≤Q.radical →
      Nat.card {S : TotallySingularSubspaces Q e // L.val≤S.val}=a)
    (hb : ∀ L : SingularLines Q, ¬L.val≤Q.radical →
      Nat.card {S : TotallySingularSubspaces Q e // L.val≤S.val}=b) :
    Nat.card (TotallySingularSubspaces Q e) * (((Fintype.card k)^e-1)/(Fintype.card k-1)) =
      (((Fintype.card k)^(Module.finrank k Q.radical)-1)/(Fintype.card k-1))*a +
        ((Nat.card {x : V // Q x=0}-1)/(Fintype.card k-1)-
          ((Fintype.card k)^(Module.finrank k Q.radical)-1)/(Fintype.card k-1))*b := by
  rw [←singular_flag_count]
  have hf (L : SingularLines Q) : Nat.card {S : TotallySingularSubspaces Q e // L.val≤S.val}=
      if L.val≤Q.radical then a else b := by
    split_ifs with h
    · exact ha L h
    · exact hb L h
  simp_rw [hf]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hr : (Finset.univ.filter (fun L : SingularLines Q => L.val≤Q.radical)).card =
      ((Fintype.card k)^(Module.finrank k Q.radical)-1)/(Fintype.card k-1) := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using singular_radical_lines_card Q
  have hc := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun L : SingularLines Q => L.val≤Q.radical)
  rw [Finset.card_univ,hr,←Nat.card_eq_fintype_card (α:=SingularLines Q),singularLines_card] at hc
  rw [hr]
  congr 1
  congr 1
  simp only [Nat.cast_id] at *
  omega
end BinaryFieldCounterexamples.QuadraticGeometry
