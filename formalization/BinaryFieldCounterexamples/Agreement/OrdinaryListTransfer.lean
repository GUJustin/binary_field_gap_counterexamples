/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Agreement.Basic
/-!
# Decoding lists from a polynomial challenge direction

When the direction is monic of degree K, subtracting its challenge multiple
from each strict-degree witness gives a decoding list at message length K+1. The
coefficient of degree K recovers the challenge, preserving every distinct challenge,
including zero. This is the list-transfer step used by the all-rate construction.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq

theorem ordinaryList_of_polynomial_direction_witnesses
    {F : Type*} [Field F] (D : Finset F) (K T : ℕ) (f : D → F)
    (G : F[X]) (hG : G.Monic) (hdegG : G.natDegree=K)
    (I : Finset F) (P : F → F[X])
    (hP : ∀ z∈I, (P z).degree<K ∧
      T≤agreementCount D (fun x => f x+z*G.eval (x:F)) (P z)) :
    ordinaryList D (K+1) T I.card := by
  let Q : F → F[X] := fun z => P z-C z*G
  have hc (z) (hz : z∈I) : (Q z).coeff K = -z := by
    have hp : (P z).coeff K=0 := coeff_eq_zero_of_degree_lt (hP z hz).1
    have hg : G.coeff K=1 := by rw [←hdegG]; exact hG.coeff_natDegree
    simp [Q,coeff_sub,coeff_C_mul,hp,hg]
  have hi : Set.InjOn Q I := by
    intro z hz w hw he
    have h := congrArg (fun p : F[X] => p.coeff K) he
    rw [hc z hz,hc w hw] at h
    exact neg_injective h
  refine ⟨f,I.image Q,?_,?_⟩
  · exact (Finset.card_image_iff.mpr hi).ge
  · intro p hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨?_,?_⟩
    · apply lt_of_le_of_lt (degree_sub_le _ _)
      apply max_lt
      · exact (hP z hz).1.trans (by exact_mod_cast Nat.lt_succ_self K)
      · have hd : (C z*G).natDegree≤K := by
          simpa [hdegG] using (natDegree_mul_le (p := C z) (q := G))
        exact (degree_le_of_natDegree_le hd).trans_lt (by exact_mod_cast Nat.lt_succ_self K)
    · have he : agreementCount D f (Q z)=
          agreementCount D (fun x => f x+z*G.eval (x:F)) (P z) := by
        simp only [agreementCount,Code.agree]
        congr 1
        ext x
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Q,eval_sub,eval_mul,eval_C]
        constructor <;> intro h <;> linear_combination h
      rw [he]
      exact (hP z hz).2

theorem ordinaryList_of_badChallenges_polynomial_direction
    {F : Type*} [Field F] [Fintype F] (D : Finset F) (K T : ℕ) (f : D → F)
    (G : F[X]) (hG : G.Monic) (hdegG : G.natDegree=K) :
    ordinaryList D (K+1) T (badChallenges D K f (fun x => G.eval (x:F)) T).card := by
  let I := badChallenges D K f (fun x => G.eval (x:F)) T
  have hw (z : F) (hz : z∈I) : ∃ p : F[X], p.degree<K ∧
      T≤agreementCount D (fun x => f x+z*G.eval (x:F)) p :=
    (mem_badChallenges D K f (fun x => G.eval (x:F)) T z).mp hz
  let P : F → F[X] := fun z => if hz : z∈I then (hw z hz).choose else 0
  apply ordinaryList_of_polynomial_direction_witnesses D K T f G hG hdegG I P
  intro z hz
  simpa only [P,dite_eq_left hz] using (hw z hz).choose_spec
end BinaryFieldCounterexamples
