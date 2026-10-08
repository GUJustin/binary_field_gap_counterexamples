/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.WeightedFourier
public import BinaryFieldCounterexamples.Constructions.Gold.AlternatingRankParity
/-!
# Minimum-rank population in a binary alternating code

The proved weighted Fourier identity and character orthogonality give the exact
Gaussian lower bound for the number of minimum-rank tensors in any actual
binary linear code.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The weighted alternating-character sum over a binary linear code is bounded
below by its trivial character contribution. -/
theorem alternatingCode_weighted_lower_bound (d s : ℕ)
    (C : Submodule (ZMod 2) (TensorIndex d → ZMod 2)) (hs : s≤d/2) :
    (Nat.card C : ℚ) * (gaussianBinomial 4 (d/2) s : ℚ) ≤
      (alternatingFourierParameter d)^s *
        ∑ A : C, (gaussianBinomial 4
          (d/2-(tensorAlternatingMatrix (A : TensorIndex d → ZMod 2)).rank/2) s : ℚ) := by
  let w : ℕ → ℕ := fun j => gaussianBinomial 4 (d/2-j) (s-j)
  have h := sum_weighted_alternating_characters_lower_bound d s w C
  have hq : (Nat.card C : ℚ) * (w 0 : ℚ) ≤
      ∑ A : C, ∑ j ∈ Finset.range (s+1),
        (w j : ℚ) * (alternatingRankCharacterSum d j A : ℚ) := by
    exact_mod_cast h
  have hw0 : w 0=gaussianBinomial 4 (d/2) s := by simp [w]
  rw [hw0] at hq
  calc
    _ ≤ ∑ A : C, ∑ j ∈ Finset.range (s+1),
        (w j : ℚ) * (alternatingRankCharacterSum d j A : ℚ) := hq
    _ = ∑ A : C, gaussianWeightedSum 4 (d/2) s
        (fun j => (alternatingRankCharacterSum d j A : ℚ)) := by rfl
    _ = ∑ A : C, (alternatingFourierParameter d)^s *
        (gaussianBinomial 4
          (d/2-(tensorAlternatingMatrix (A : TensorIndex d → ZMod 2)).rank/2) s : ℚ) := by
      apply Finset.sum_congr rfl
      intro A hA
      exact gaussianWeightedSum_alternatingTensor d s A hs
    _ = _ := by rw [Finset.mul_sum]

/-- A binary alternating code with minimum nonzero rank `2t` contains the
paper's quantitative number of rank-`2t` tensors. -/
theorem alternatingCode_minimumRank_count_lower_bound (d t : ℕ)
    (ht : 1≤t) (hdt : 2*t≤d)
    (C : Submodule (ZMod 2) (TensorIndex d → ZMod 2))
    (hmin : ∀ A : C, A ≠ 0 →
      2*t ≤ (tensorAlternatingMatrix (A : TensorIndex d → ZMod 2)).rank) :
    (gaussianBinomial 4 (d/2) t : ℚ) *
      ((Nat.card C : ℚ)/(alternatingFourierParameter d)^((d/2)-t)-1) ≤
      ((Finset.univ.filter fun A : C =>
        (tensorAlternatingMatrix (A : TensorIndex d → ZMod 2)).rank=2*t).card : ℚ) := by
  let n := d/2
  let s := n-t
  let γ := alternatingFourierParameter d
  let count := (Finset.univ.filter fun A : C =>
    (tensorAlternatingMatrix (A : TensorIndex d → ZMod 2)).rank=2*t).card
  have htle : t≤n := by dsimp [n]; omega
  have hs : s≤d/2 := by dsimp [s,n]; omega
  have hlow := alternatingCode_weighted_lower_bound d s C hs
  have hsym : gaussianBinomial 4 n s=gaussianBinomial 4 n t := by
    dsimp [s]
    rw [gaussianBinomial_symm 4 n (n-t) (by decide) (Nat.sub_le _ _), Nat.sub_sub_self htle]
  have hpoint (A : C) : (gaussianBinomial 4
      (n-(tensorAlternatingMatrix (A : TensorIndex d → ZMod 2)).rank/2) s : ℚ) =
      (if A=0 then (gaussianBinomial 4 n t : ℚ) else 0) +
      (if (tensorAlternatingMatrix (A : TensorIndex d → ZMod 2)).rank=2*t
        then 1 else 0) := by
    by_cases hA : A=0
    · subst A
      have hz : tensorAlternatingMatrix
          ((0 : C) : TensorIndex d → ZMod 2)=0 := by
        exact tensorAlternatingMatrix_zero d
      rw [hz, Matrix.rank_zero]
      have ht0 : (0:ℕ) ≠ 2*t := by omega
      simp only [Nat.zero_div, Nat.sub_zero, hsym, ite_true, ht0, ite_false,
        add_zero]
    · have hge := hmin A hA
      have heven := tensorAlternatingMatrix_rank_even d
        (A : TensorIndex d → ZMod 2)
      have hrle := (tensorAlternatingMatrix
        (A : TensorIndex d → ZMod 2)).rank_le_card_width
      simp only [Fintype.card_fin] at hrle
      by_cases hr : (tensorAlternatingMatrix
          (A : TensorIndex d → ZMod 2)).rank=2*t
      · have hhalf : (tensorAlternatingMatrix
            (A : TensorIndex d → ZMod 2)).rank/2=t := by omega
        rw [hhalf]
        simp only [hA, ite_false, hr, ite_true, zero_add]
        change (gaussianBinomial 4 (n-t) (n-t) : ℚ)=1
        rw [gaussianBinomial_eq_gaussianPascal _ _ _ (by decide), gaussianPascal_self]
        norm_num
      · rcases heven with ⟨r,hrtwo⟩
        have hgt : 2*t+2 ≤ (tensorAlternatingMatrix
            (A : TensorIndex d → ZMod 2)).rank := by omega
        have hhalfgt : t < (tensorAlternatingMatrix
            (A : TensorIndex d → ZMod 2)).rank/2 := by omega
        have hhalfle : (tensorAlternatingMatrix
            (A : TensorIndex d → ZMod 2)).rank/2 ≤ n := by
          dsimp [n]
          omega
        have hnot : ¬s ≤ n-(tensorAlternatingMatrix
            (A : TensorIndex d → ZMod 2)).rank/2 := by
          dsimp [s]
          omega
        simp [gaussianBinomial,hnot,hA,hr]
  have hsum : (∑ A : C, (gaussianBinomial 4
      (n-(tensorAlternatingMatrix (A : TensorIndex d → ZMod 2)).rank/2) s : ℚ)) =
      (gaussianBinomial 4 n t : ℚ)+(count:ℚ) := by
    rw [Finset.sum_congr rfl (fun A _ => hpoint A), Finset.sum_add_distrib]
    have hzsum : (∑ A : C,
        if A=0 then (gaussianBinomial 4 n t : ℚ) else 0) =
        (gaussianBinomial 4 n t : ℚ) := by
      calc
        _ = (if (0:C)=0 then (gaussianBinomial 4 n t : ℚ) else 0) := by
          apply Fintype.sum_eq_single (0 : C)
          intro A hA
          simp [hA]
        _ = _ := by simp
    rw [hzsum]
    apply congrArg (fun x : ℚ => (gaussianBinomial 4 n t : ℚ)+x)
    change (∑ A : C,
      if (tensorAlternatingMatrix (A : TensorIndex d → ZMod 2)).rank=2*t
      then (1:ℚ) else 0) = (count:ℚ)
    dsimp [count]
    rw [Finset.card_filter]
    norm_cast
  change (Nat.card C : ℚ) * (gaussianBinomial 4 n s : ℚ) ≤
    γ^s * ∑ A : C, (gaussianBinomial 4
      (n-(tensorAlternatingMatrix (A : TensorIndex d → ZMod 2)).rank/2) s : ℚ) at hlow
  rw [hsym,hsum] at hlow
  have hγ : 0 < γ^s := by
    dsimp [γ,alternatingFourierParameter]
    positivity
  change (gaussianBinomial 4 n t : ℚ) *
    ((Nat.card C : ℚ)/γ^s-1) ≤ (count:ℚ)
  calc
    (gaussianBinomial 4 n t : ℚ) * ((Nat.card C : ℚ)/γ^s-1) =
        ((Nat.card C : ℚ)*(gaussianBinomial 4 n t : ℚ)-
          γ^s*(gaussianBinomial 4 n t : ℚ))/γ^s := by field_simp
    _ ≤ count := by
      apply (div_le_iff₀ hγ).2
      linarith

end BinaryFieldCounterexamples.Gold
