/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Domains

/-!
# Agreement on translated domains

Translation preserves strict polynomial degree and every actual coordinate
agreement. In particular it preserves the entire exceptional set, allowing
additive-domain constructions to transfer to the prescribed affine domain.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
/-- Affine-domain membership is translation back into the original domain. -/
theorem mem_affineDomain_iff
    {F : Type*} [Field F] (D : Finset F) (a x : F) :
    x ∈ affineDomain D a ↔ x-a ∈ D := by
  classical
  simp only [affineDomain, Finset.mem_image]
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x-a,hx,sub_add_cancel x a⟩

/-- Translation preserves the number of actual coordinates. -/
theorem card_affineDomain
    {F : Type*} [Field F] (D : Finset F) (a : F) :
    (affineDomain D a).card=D.card := by
  classical
  exact Finset.card_image_of_injective _ (fun x y h => add_right_cancel h)

/-- Translation of coordinates transports the explaining polynomial by the
same literal shift, preserving every agreement. -/
theorem agreementCount_affineDomain
    {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (a : F)
    (w : F → F) (p : F[X]) :
    agreementCount (affineDomain D a) (fun x => w ((x : F)-a)) p =
      agreementCount D (fun x => w x) (p.comp (X+C a)) := by
  rw [agreementCount_eq_card_filter (affineDomain D a) (fun x => w (x-a)) p,
    agreementCount_eq_card_filter D w (p.comp (X+C a))]
  simp only [affineDomain, Finset.filter_image, add_sub_cancel_right,
    eval_comp, eval_add, eval_X, eval_C]
  have h := Finset.card_image_of_injective
    (D.filter (fun x => p.eval (x+a)=w x)) (fun x y h => add_right_cancel (b := a) h)
  convert h using 1
  congr 1
  ext x
  simp

/-- Affine translation preserves the strict-degree existential agreement event. -/
theorem agreementGE_affineDomain_iff
    {F : Type*} [Field F] (D : Finset F) (a : F)
    (w : F → F) (K T : ℕ) :
    agreementGE (affineDomain D a) K (fun x => w ((x : F)-a)) T ↔
      agreementGE D K (fun x => w x) T := by
  classical
  constructor
  · rintro ⟨p,hp,hcount⟩
    refine ⟨p.comp (X+C a),?_,?_⟩
    · rwa [degree_comp (by simp), degree_X_add_C, mul_one]
    · rwa [agreementCount_affineDomain] at hcount
  · rintro ⟨p,hp,hcount⟩
    refine ⟨p.comp (X-C a),?_,?_⟩
    · rwa [degree_comp (by simp), degree_X_sub_C, mul_one]
    · rw [agreementCount_affineDomain]
      have heq : (p.comp (X-C a)).comp (X+C a)=p := by
        rw [comp_assoc]
        simp
      rw [heq]
      exact hcount

/-- Translation preserves universal upper bounds on a word's agreement. -/
theorem agreementLE_affineDomain
    {F : Type*} [Field F] (D : Finset F) (a : F)
    (w : F → F) (K T : ℕ) (hw : agreementLE D K (fun x => w x) T) :
    agreementLE (affineDomain D a) K (fun x => w ((x : F)-a)) T := by
  classical
  intro p hp
  rw [agreementCount_affineDomain]
  apply hw
  rwa [degree_comp (by simp), degree_X_add_C, mul_one]

/-- Affine translation preserves the entire challenge set, not just its size. -/
theorem badChallenges_affineDomain
    {F : Type*} [Field F] [Fintype F] (D : Finset F) (a : F)
    (f g : F → F) (K T : ℕ) :
    badChallenges (affineDomain D a) K
      (fun x => f ((x : F)-a)) (fun x => g ((x : F)-a)) T =
      badChallenges D K (fun x => f x) (fun x => g x) T := by
  classical
  ext z
  rw [mem_badChallenges, mem_badChallenges]
  exact agreementGE_affineDomain_iff D a (fun x => f x+z*g x) K T
end BinaryFieldCounterexamples
