/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Basic

/-!
# Exact decoding lists for the quadratic construction

The paragraph following Theorem 4.1 converts each nonzero exceptional challenge
into a polynomial for the same first input. The coefficient at the degree of
the monic direction recovers the challenge. Thus the list has exactly the
exceptional cardinality, exact degree, and the same attained agreement.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial

/-- Theorem 4.1, decoding-list paragraph: nonzero challenges with exact agreement
produce an equally large list for the literal first input, with exact degree
that of the monic polynomial direction. -/
theorem exact_list_of_nonzero_polynomial_direction
    {F : Type*} [Field F] (D : Finset F) (K d T : ℕ) (f : D → F)
    (G : F[X]) (hG : G.Monic) (hdegG : G.degree = (d : WithBot ℕ))
    (hKd : K ≤ d) (I : Finset F) (hzero : 0 ∉ I)
    (hI : ∀ z ∈ I, agreementEQ D K (fun x => f x + z * G.eval (x : F)) T) :
    ∃ ps : Finset F[X], ps.card = I.card ∧
      ∀ p ∈ ps, p.degree = (d : WithBot ℕ) ∧
        p.degree < (d + 1 : ℕ) ∧ agreementCount D f p = T := by
  classical
  have hw (z : F) (hz : z ∈ I) : ∃ p : F[X], p.degree < K ∧
      T ≤ agreementCount D (fun x => f x + z * G.eval (x : F)) p := (hI z hz).1
  let P : F → F[X] := fun z => if hz : z ∈ I then (hw z hz).choose else 0
  have hP (z : F) (hz : z ∈ I) : (P z).degree < K ∧
      agreementCount D (fun x => f x + z * G.eval (x : F)) (P z) = T := by
    have hp : (P z).degree < K ∧
        T ≤ agreementCount D (fun x => f x + z * G.eval (x : F)) (P z) := by
      simpa only [P, dite_eq_left hz] using (hw z hz).choose_spec
    exact ⟨hp.1, le_antisymm ((hI z hz).2 (P z) hp.1) hp.2⟩
  let Q : F → F[X] := fun z => P z - C z * G
  have hc (z : F) (hz : z ∈ I) : (Q z).coeff d = -z := by
    have hp : (P z).coeff d = 0 := coeff_eq_zero_of_degree_lt
      ((hP z hz).1.trans_le (by exact_mod_cast hKd))
    have hg : G.coeff d = 1 := by
      have hd : G.natDegree = d := natDegree_eq_of_degree_eq_some hdegG
      rw [← hd]
      exact hG.coeff_natDegree
    simp [Q, coeff_sub, coeff_C_mul, hp, hg]
  have hi : Set.InjOn Q I := by
    intro z hz w hw he
    have h := congrArg (fun p : F[X] => p.coeff d) he
    rw [hc z hz, hc w hw] at h
    exact neg_injective h
  refine ⟨I.image Q, Finset.card_image_iff.mpr hi, ?_⟩
  intro p hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
  have hz0 : z ≠ 0 := fun h => hzero (h ▸ hz)
  have hdegree : (Q z).degree = (d : WithBot ℕ) := by
    have hmul : (C z * G).degree = (d : WithBot ℕ) := by
      rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hz0), hdegG]
    change (P z - C z * G).degree = (d : WithBot ℕ)
    rw [degree_sub_eq_right_of_degree_lt]
    · exact hmul
    · rw [hmul]
      exact (hP z hz).1.trans_le (by exact_mod_cast hKd)
  refine ⟨hdegree, ?_, ?_⟩
  · rw [hdegree]
    exact_mod_cast Nat.lt_succ_self d
  · have he : agreementCount D f (Q z) =
        agreementCount D (fun x => f x + z * G.eval (x : F)) (P z) := by
      simp only [agreementCount, Code.agree]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Q, eval_sub, eval_mul, eval_C]
      constructor <;> intro h <;> linear_combination h
    rw [he]
    exact (hP z hz).2

end BinaryFieldCounterexamples
