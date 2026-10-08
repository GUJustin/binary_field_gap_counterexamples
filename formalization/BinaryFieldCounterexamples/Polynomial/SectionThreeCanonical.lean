/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.PaperSemantics
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Div

/-!
# Canonical representatives and distinct Reed–Solomon codewords

This module proves the existence, uniqueness and remainder clauses of Definition
3.6 in `sections/preliminaries.tex`, including the full finite-field modulus
`X ^ |F| - X`. It also proves the codeword-counting remark after Definition 3.4:
strict-degree message polynomials give distinct words on a sufficiently large
finite domain.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The canonical representative of Definition 3.6 on a finite domain, obtained
by interpolating the actual coordinate subtype. -/
noncomputable def canonicalRepresentative {F : Type*} [Field F]
    (D : Finset F) (u : D → F) : F[X] :=
  Lagrange.interpolate Finset.univ Subtype.val u

/-- Definition 3.6: the canonical representative has degree strictly below the
number of domain coordinates and represents the given function on every one. -/
theorem canonicalRepresentative_spec {F : Type*} [Field F]
    (D : Finset F) (u : D → F) :
    (canonicalRepresentative D u).degree < D.card ∧
      ∀ x : D, (canonicalRepresentative D u).eval (x : F) = u x := by
  classical
  refine ⟨?_, ?_⟩
  · simpa [canonicalRepresentative] using
      Lagrange.degree_interpolate_lt (s := Finset.univ) (v := Subtype.val) u
        Subtype.val_injective.injOn
  · intro x
    exact Lagrange.eval_interpolate_at_node u Subtype.val_injective.injOn
      (Finset.mem_univ x)

/-- Definition 3.6: any strict-degree representative is the canonical one;
the statement includes the empty domain, whose representative is zero. -/
theorem eq_canonicalRepresentative {F : Type*} [Field F]
    (D : Finset F) (u : D → F) (P : F[X]) (hP : P.degree < D.card)
    (heval : ∀ x : D, P.eval (x : F) = u x) :
    P = canonicalRepresentative D u := by
  classical
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset D)
    Subtype.val_injective.injOn
  · simpa using hP
  · simpa using (canonicalRepresentative_spec D u).1
  · intro x _
    exact (heval x).trans ((canonicalRepresentative_spec D u).2 x).symm

/-- Definition 3.6, assembled: every function on a finite domain has exactly
one representative of degree strictly below the domain cardinality. -/
theorem existsUnique_canonicalRepresentative {F : Type*} [Field F]
    (D : Finset F) (u : D → F) :
    ∃! P : F[X], P.degree < D.card ∧ ∀ x : D, P.eval (x : F) = u x := by
  refine ⟨canonicalRepresentative D u, canonicalRepresentative_spec D u, ?_⟩
  intro P hP
  exact eq_canonicalRepresentative D u P hP.1 hP.2

/-- Definition 3.6: the canonical representative is the monic-division
remainder modulo the domain's vanishing polynomial of any representative. -/
theorem canonicalRepresentative_eq_remainder {F : Type*} [Field F]
    (D : Finset F) (u : D → F) (P : F[X])
    (heval : ∀ x : D, P.eval (x : F) = u x) :
    canonicalRepresentative D u = P %ₘ Lagrange.nodal D id := by
  classical
  symm
  apply eq_canonicalRepresentative D u
  · simpa only [Lagrange.degree_nodal] using
      Polynomial.degree_modByMonic_lt P (Lagrange.nodal_monic (s := D) (v := id))
  · intro x
    have hroot : (Lagrange.nodal D id).eval (x : F) = 0 :=
      Lagrange.eval_nodal_at_node (v := id) x.property
    exact (Polynomial.eval₂_modByMonic_eq_self_of_root
      (f := RingHom.id F) hroot).trans (heval x)

/-- Definition 3.6: the vanishing polynomial of all elements of a finite field
is exactly `X ^ |F| - X`, as a polynomial rather than only a function. -/
theorem nodal_univ_eq_X_pow_card_sub_X {F : Type*} [Field F] [Fintype F] :
    Lagrange.nodal (Finset.univ : Finset F) id = X ^ Fintype.card F - X := by
  classical
  have hdeg : (X : F[X]).degree < (X ^ Fintype.card F : F[X]).degree := by
    simp only [degree_X, degree_X_pow]
    exact_mod_cast Fintype.one_lt_card (α := F)
  apply Polynomial.eq_of_degree_le_of_eval_finset_eq (Finset.univ : Finset F)
  · simp [Lagrange.degree_nodal]
  · simp only [Lagrange.degree_nodal, Finset.card_univ,
      degree_sub_eq_left_of_degree_lt hdeg, degree_X_pow]
  · rw [(Lagrange.nodal_monic (s := (Finset.univ : Finset F)) (v := id)).leadingCoeff,
      leadingCoeff_sub_of_degree_lt hdeg, (monic_X_pow _).leadingCoeff]
  · intro x hx
    have hn : (Lagrange.nodal Finset.univ id).eval x = 0 :=
      Lagrange.eval_nodal_at_node (v := id) hx
    rw [hn]
    simp only [eval_sub, eval_pow, eval_X, FiniteField.pow_card, sub_self]

/-- Definition 3.6 over a finite field: every polynomial representing a
function has remainder equal to its canonical representative modulo
`X ^ |F| - X`. -/
theorem canonicalRepresentative_univ_eq_remainder {F : Type*} [Field F] [Fintype F]
    (u : F → F) (P : F[X]) (heval : ∀ x : F, P.eval x = u x) :
    canonicalRepresentative Finset.univ (fun x => u x) =
      P %ₘ (X ^ Fintype.card F - X) := by
  rw [← nodal_univ_eq_X_pow_card_sub_X]
  exact canonicalRepresentative_eq_remainder _ _ P (fun x => heval x)

/-- The remark after Definition 3.4: evaluating strict-degree message
polynomials on a domain of size at least `K` is injective. Thus the paper's
stronger hypothesis `K < N` also guarantees distinct codewords. -/
theorem strictDegree_evaluation_injective {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (hK : K ≤ D.card) :
    Function.Injective (fun P : {P : F[X] // P.degree < K} =>
      (fun x : D => P.val.eval (x : F))) := by
  classical
  intro P Q heq
  apply Subtype.ext
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset D)
    Subtype.val_injective.injOn
  · simpa using P.property.trans_le (Nat.cast_le.mpr hK)
  · simpa using Q.property.trans_le (Nat.cast_le.mpr hK)
  · intro x _
    exact congrFun heq x

/-- The list-counting remark after Definition 3.4: a finite family of
strict-degree polynomials has exactly as many evaluation codewords as
polynomials whenever `K ≤ |D|`. -/
theorem strictDegree_codeword_image_card {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (hK : K ≤ D.card) (ps : Finset F[X])
    (hps : ∀ P ∈ ps, P.degree < K) :
    (ps.image (fun P => fun x : D => P.eval (x : F))).card = ps.card := by
  classical
  apply Finset.card_image_of_injOn
  intro P hP Q hQ heq
  exact congrArg Subtype.val
    (strictDegree_evaluation_injective D K hK
      (a₁ := ⟨P, hps P hP⟩) (a₂ := ⟨Q, hps Q hQ⟩) heq)

end BinaryFieldCounterexamples
