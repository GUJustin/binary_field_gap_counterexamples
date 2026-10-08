/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Templates
/-!
# Binary tree frame restrictions

Explicit binary frame relations used in the constrained height-two population.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- Binary two-vector span has its four explicit values. -/
theorem mem_binary_span_pair (a b c : V) :
    c ∈ Submodule.span (ZMod 2) ({a,b} : Set V) ↔ c=0 ∨ c=a ∨ c=b ∨ c=a+b := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨r,s,h⟩
    rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) r with rfl|rfl <;>
      rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) s with rfl|rfl <;>
      simp_all
  · rintro (rfl|rfl|rfl|rfl)
    · exact ⟨0,0,by simp⟩
    · exact ⟨1,0,by simp⟩
    · exact ⟨0,1,by simp⟩
    · exact ⟨1,1,by simp⟩
/-- Independence of a binary triple excludes the seven nonzero binary relations. -/
theorem binary_triple_independent_iff (a b c : V) :
    LinearIndependent (ZMod 2) ![a,b,c] ↔
      a≠0 ∧ b≠0 ∧ b≠a ∧ c≠0 ∧ c≠a ∧ c≠b ∧ c≠a+b := by
  have he : ![a,b,c] = Fin.snoc ![a,b] c := by ext i; fin_cases i <;> rfl
  rw [he,linearIndependent_finSnoc]
  have hr : Set.range ![a,b] = ({a,b} : Set V) := by ext x; simp [or_comm]
  rw [hr,mem_binary_span_pair]
  by_cases ha : a=0
  · subst a
    have hn : ¬LinearIndependent (ZMod 2) ![(0:V),b] := by
      intro h
      exact h.ne_zero 0 rfl
    simp [hn]
  · rw [LinearIndependent.pair_iff' ha]
    have hb : (∀ r : ZMod 2, r • a≠b) ↔ b≠0 ∧ b≠a := by
      constructor
      · intro h; exact ⟨by simpa [ne_comm] using h 0,by simpa [ne_comm] using h 1⟩
      · rintro ⟨h0,h1⟩ r
        rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) r with rfl|rfl <;> simp_all [ne_comm]
    rw [hb]
    tauto
/-- Adding the first vector to both remaining vectors preserves independence. -/
theorem binary_triple_shear_independent_iff (a b c : V) :
    LinearIndependent (ZMod 2) ![a,a+b,a+c] ↔ LinearIndependent (ZMod 2) ![a,b,c] := by
  have h := linearIndependent_add_smul_iff (R := ZMod 2) (v := ![a,b,c])
    (c := ![0,1,1]) (i := (0 : Fin 3)) (by rfl)
  have he : ![a,a+b,a+c] = ![a,b,c] + (fun x => (![0,1,1] x : ZMod 2) • ![a,b,c] 0) := by
    ext i
    fin_cases i <;> simp [add_comm]
  rw [he]
  exact h
/-- A vector outside a subspace is independent from a frame inside it. -/
theorem triple_independent_outside (U : Submodule (ZMod 2) V) (a b c : V)
    (ha : a ∉ U) (hb : b ∈ U) (hc : c ∈ U) :
    LinearIndependent (ZMod 2) ![a,b,c] ↔ LinearIndependent (ZMod 2) ![b,c] := by
  change LinearIndependent (ZMod 2) (Fin.cons a ![b,c]) ↔ _
  rw [linearIndependent_finCons]
  have hs : Submodule.span (ZMod 2) (Set.range ![b,c]) ≤ U := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    fin_cases i <;> assumption
  exact and_iff_left (fun h => ha (hs h))

end BinaryFieldCounterexamples.Trees
