/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.Converse

/-!
# The two excluded exact-half challenges

The sharp first-input bound excludes zero. The other excluded challenge is the
nonzero exterior numerator value: a challenge at that value would force a
residual locator to vanish outside the prescribed domain.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
/-- The exterior numerator value squares to the nonzero exterior locator value. -/
theorem binaryQuarterNumerator_eval_pole_ne_zero
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D) :
    (binaryQuarterNumerator D β).eval β ≠ 0 := by
  have hsq : ((binaryQuarterNumerator D β).eval β)^2 =
      (subspacePolynomial D).eval β := by
    simpa [binaryQuarterRadicand] using
      congrArg (fun P : F[X] => P.eval β) (binaryQuarterNumerator_sq D β)
  intro h
  apply hβ
  apply (subspacePolynomial_eval_eq_zero_iff D β).mp
  simpa [h] using hsq.symm

/-- Zero is excluded by the sharp first-input bound, and the exterior
numerator value is excluded by the residual locator identity. -/
theorem binaryQuarterSource_excluded_challenges
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K=2^k)
    (hcard : Fintype.card D = 4*K) :
    let E := additiveDomain D
    let f : E → F := fun x => (binaryQuarterNumerator D β).eval (x : F)*((x : F)-β)⁻¹
    let g : E → F := fun x => ((x : F)-β)⁻¹
    0 ∉ badChallenges E K f g (2*K) ∧
      (binaryQuarterNumerator D β).eval β ∉ badChallenges E K f g (2*K) := by
  classical
  dsimp only
  constructor
  · intro hz
    obtain ⟨p,hp,hcount⟩ := (mem_badChallenges _ _ _ _ _ 0).mp hz
    simp only [zero_mul, add_zero] at hcount
    have hle := agreementLE_binaryQuarterSource D β hβ K hK hpow hcard p hp
    omega
  · intro hz
    obtain ⟨l,b,c,hl,hc,hm,hAS,he⟩ :=
      halfAgreement_bad_representation D β hβ K hK hcard _ hz
    let A := C c*(Gold.functionalPolynomial D l+C (algebraMap (ZMod 2) F b))
    have hAz : A.eval β=0 := by
      change (binaryQuarterNumerator D β).eval β=A.eval β-(binaryQuarterNumerator D β).eval β at he
      rw [CharTwo.sub_eq_add] at he
      have : A.eval β+(binaryQuarterNumerator D β).eval β =
          0+(binaryQuarterNumerator D β).eval β := by simpa using he.symm
      exact add_right_cancel this
    have hLeval := congrArg (fun P : F[X] => P.eval β) hAS
    change (A^2+C c*A).eval β=(subspacePolynomial D).eval β at hLeval
    have hLzero : (subspacePolynomial D).eval β=0 := by simpa [hAz] using hLeval.symm
    exact hβ ((subspacePolynomial_eval_eq_zero_iff D β).mp hLzero)
end BinaryFieldCounterexamples
