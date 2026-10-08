/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Projecting explaining polynomials onto base-field coordinates

A base-linear functional on the extension coefficients preserves strict message
degree and commutes with evaluation at base-field points. In the proper-extension
construction this extracts the two equations belonging to `1` and `θ`, without
asserting that all other coefficient coordinates vanish.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- A coefficient projection produces a strict-degree polynomial with the
projected evaluations, also when the message bound is zero. -/
theorem exists_projected_polynomial
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (l : F →ₗ[B] B) (K : ℕ) (p : F[X]) (hp : p.degree < K) :
    ∃ q : B[X], q.degree < K ∧
      ∀ x : B, q.eval x = l (p.eval (algebraMap B F x)) := by
  classical
  let q : B[X] := ∑ i : Fin K, C (l (p.coeff i)) * X ^ (i : ℕ)
  refine ⟨q, degree_sum_fin_lt _, ?_⟩
  intro x
  have heval : p.eval (algebraMap B F x) =
      ∑ i : Fin K, p.coeff i * (algebraMap B F x) ^ (i : ℕ) := by
    rw [eval_eq_sum]
    exact (sum_fin (fun i a ↦ a * (algebraMap B F x) ^ i) (by simp) hp).symm
  rw [heval, map_sum]
  simp only [q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro i _
  have h := l.map_smul (x ^ (i : ℕ)) (p.coeff i)
  simpa [Algebra.smul_def, map_pow, mul_comm] using h.symm

/-- An exterior element supplies base-linear projections onto the independent
coordinates `1` and `θ`. No bound on the extension degree beyond properness is needed. -/
theorem exists_extension_coordinates
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (θ : F) (hθ : θ ∉ Set.range (algebraMap B F)) :
    ∃ l0 l1 : F →ₗ[B] B,
      l0 1 = 1 ∧ l0 θ = 0 ∧ l1 1 = 0 ∧ l1 θ = 1 := by
  have hnot : θ ∉ Submodule.span B ({1} : Set F) := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, ha⟩
    apply hθ
    exact ⟨a, by simpa [Algebra.smul_def] using ha⟩
  obtain ⟨l1, hl1, hlθ⟩ :=
    LinearMap.exists_extend_of_notMem
      (0 : Submodule.span B ({1} : Set F) →ₗ[B] B) hnot 1
  have hlone : l1 1 = 0 := by
    have h := congrArg (fun f : Submodule.span B ({1} : Set F) →ₗ[B] B ↦
      f ⟨1, Submodule.subset_span (Set.mem_singleton 1)⟩) hl1
    simpa using h
  obtain ⟨e, he⟩ := Module.Projective.exists_dual_eq_one B (one_ne_zero : (1 : F) ≠ 0)
  refine ⟨e - e θ • l1, l1, ?_, ?_, hlone, hlθ⟩
  · simp [hlone, he]
  · simp [hlθ]

end BinaryFieldCounterexamples
