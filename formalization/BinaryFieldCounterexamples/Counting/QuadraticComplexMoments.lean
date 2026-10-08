/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.QuadraticCharacterDoubleSum
public import Mathlib.NumberTheory.LegendreSymbol.Complex
/-!
# Actual Fourier moments of finite additive codes

Unit-norm complex characters turn the squared Fourier mass into the literal
sum of the character kernel over the code. Nonnegative weights then give the
zero-character lower bound used in the quadratic population argument.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- Every complex additive character on a finite field has squared norm one. -/
theorem finiteField_complexChar_normSq {k : Type*} [Field k] [Finite k]
    (χ : AddChar k ℂ) (a : k) : Complex.normSq (χ a)=1 := by
  have hn : ‖χ a‖ = 1 := Complex.norm_eq_one_of_mem_rootsOfUnity
    (χ.val_mem_rootsOfUnity a (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite k)))
  rw [Complex.normSq_eq_norm_sq,hn,one_pow]

/-- The pinned canonical complex character is nontrivial. -/
theorem primitiveComplexChar_ne_one (k : Type*) [Field k] [Finite k] :
    AddChar.FiniteField.primitiveChar_to_Complex k ≠ 1 := by
  simpa using (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive k) (a:=1) one_ne_zero

/-- Translation converts the double correlation sum into code cardinality times its character sum. -/
theorem normSq_additiveCode_sum {V k : Type*} [AddCommGroup V] [Field k] [Finite k]
    (C : AddSubgroup V) [Fintype C] (χ : AddChar k ℂ) (p : V →+ k) :
    (Complex.normSq (∑ x : C, χ (p x)) : ℂ) =
      (Fintype.card C : ℂ) * ∑ x : C, χ (p x) := by
  classical
  have hd := normSq_character_sum_eq_double_sum (Finset.univ : Finset C) χ
    (fun x : C => p x) (finiteField_complexChar_normSq χ)
    (by intro x y; exact p.map_sub x y)
  rw [hd]
  have ht (y : C) : (∑ x : C, χ (p ((x-y : C) : V)))=∑ x : C, χ (p x) := by
    exact Fintype.sum_bijective (fun x : C => x-y) (by constructor; intro x z h; exact sub_left_injective h; intro z; exact ⟨z+y,by simp⟩) _ _ (fun _ => rfl)
  simp_rw [ht]
  simp

/-- The exact weighted Fourier mass is the literal code sum of its character kernel. -/
theorem weighted_code_fourier_sum {V S k : Type*} [AddCommGroup V]
    [Field k] [Finite k] [Fintype S]
    (C : AddSubgroup V) [Fintype C] (χ : AddChar k ℂ)
    (p : S → V →+ k) (w : S → ℝ) :
    (∑ s : S, (w s : ℂ) * (Complex.normSq (∑ x : C, χ (p s x)) : ℂ)) =
      (Fintype.card C : ℂ) * ∑ x : C, ∑ s : S, (w s : ℂ) * χ (p s x) := by
  simp_rw [normSq_additiveCode_sum C χ]
  calc
    _ = (Fintype.card C : ℂ) * ∑ s : S, ∑ x : C, (w s : ℂ) * χ (p s x) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by rw [Finset.sum_comm]

/-- Dividing the actual Fourier mass by code size leaves the literal kernel sum. -/
theorem normalized_code_fourier_sum {V S k : Type*} [AddCommGroup V]
    [Field k] [Finite k] [Fintype S]
    (C : AddSubgroup V) [Fintype C] (χ : AddChar k ℂ)
    (p : S → V →+ k) (w : S → ℝ) :
    (∑ s : S, (w s : ℂ) * (Complex.normSq (∑ x : C, χ (p s x)) : ℂ)) /
      (Fintype.card C : ℂ) = ∑ x : C, ∑ s : S, (w s : ℂ) * χ (p s x) := by
  rw [weighted_code_fourier_sum]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Fintype.card_ne_zero (α:=C))

/-- Nonnegative weights lower-bound the actual code kernel sum by its zero-character contribution. -/
theorem code_fourier_sum_lower_bound {V S k : Type*} [AddCommGroup V]
    [Field k] [Finite k] [Fintype S] [Zero S]
    (C : AddSubgroup V) [Fintype C] (χ : AddChar k ℂ)
    (p : S → V →+ k) (hp : p 0=0) (w : S → ℝ) (hw : ∀ s,0≤w s) :
    w 0 * Fintype.card C ≤
      (∑ x : C, ∑ s : S, (w s : ℂ) * χ (p s x)).re := by
  classical
  have he := congrArg Complex.re (normalized_code_fourier_sum C χ p w)
  have hc : (0 : ℝ)<Fintype.card C := by exact_mod_cast Fintype.card_pos (α:=C)
  have hmass : w 0 * (Fintype.card C : ℝ)^2 ≤
      ∑ s : S, w s * Complex.normSq (∑ x : C, χ (p s x)) := by
    have hz : Complex.normSq (∑ x : C, χ (p 0 x))=(Fintype.card C : ℝ)^2 := by
      simp [hp,Complex.normSq_natCast,pow_two]
    rw [←hz]
    exact Finset.single_le_sum (f:=fun s : S => w s * Complex.normSq (∑ x : C, χ (p s x)))
      (fun s _ => mul_nonneg (hw s) (Complex.normSq_nonneg _))
      (Finset.mem_univ (0 : S))
  have he' : (∑ s : S, w s * Complex.normSq (∑ x : C, χ (p s x))) /
      Fintype.card C = (∑ x : C, ∑ s : S, (w s : ℂ) * χ (p s x)).re := by
    convert he using 1
    simp [Complex.div_re,Complex.normSq_natCast]
    field_simp
  rw [←he']
  apply (le_div_iff₀ hc).mpr
  linarith [hmass]
end BinaryFieldCounterexamples
