/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalRoots

/-!
# Zero-count upper bound from radical multiplicities

Known roots on a radical-sized subset already force the elliptic-size upper
bound, by weighted root counting. No global splitting or quadratic type
classification is assumed; the actual radical and its multiplicities remain
explicit inputs to this algebraic step.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.decEq

/-- Extra multiplicity on a radical-sized root subset forces the smaller zero-count bound. -/
theorem zero_card_le_of_radical_multiplicities
    {F : Type*} [Field F] (q m t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) (htm : 2*t ≤ m)
    (G : F[X]) (hG : G ≠ 0) (S R : Finset F) (hRS : R ⊆ S)
    (hzero : ∀ x ∈ S, G.eval x = 0)
    (hmult : ∀ x ∈ R, q^t+1 ≤ rootMultiplicity x G)
    (hR : R.card = q^(m-2*t))
    (hdegree : G.natDegree ≤ q^(m-1)+q^(m-t-1)) :
    S.card ≤ q^(m-1)-(q-1)*q^(m-t-1) := by
  have hw := (weighted_root_card_le_natDegree G hG S R hRS (q^t) hzero hmult).trans hdegree
  rw [hR, ← pow_add] at hw
  have he : t+(m-2*t) = m-t := by omega
  rw [he] at hw
  have hp : q^(m-t) = q*q^(m-t-1) := by
    have he : m-t = (m-t-1)+1 := by omega
    calc
      q^(m-t) = q^((m-t-1)+1) := congrArg (q^·) he
      _ = q*q^(m-t-1) := pow_succ' _ _
  rw [hp] at hw
  apply Nat.le_sub_of_add_le
  have heq : q = (q-1)+1 := by omega
  nlinarith

end BinaryFieldCounterexamples
