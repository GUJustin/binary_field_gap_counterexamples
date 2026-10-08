/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianInversion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite Gaussian incidence reconstruction

The explicit Gaussian Möbius coefficients invert the upper-triangular
subspace-incidence transform on every finite sequence.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- Upper-triangular Gaussian incidence transform. -/
def gaussianIncidenceTransform (q d : ℕ) (c : ℕ → ℚ) (r : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (d - r + 1),
    (gaussianPascal q (d - r) a : ℚ) * c (r + a)

/-- Reindex the finite triangular double sum by its total degree. -/
theorem sum_range_triangle_swap (D : ℕ) (f : ℕ → ℕ → ℚ) :
    ∑ a ∈ Finset.range (D + 1), ∑ b ∈ Finset.range (D - a + 1), f a b =
      ∑ u ∈ Finset.range (D + 1), ∑ a ∈ Finset.range (u + 1), f a (u - a) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij
    (fun p hp => ⟨p.1 + p.2, p.1⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    omega
  · intro p hp q hq heq
    ext <;> simp_all <;> omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    refine ⟨⟨p.2, p.1 - p.2⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · ext <;> simp <;> omega
  · intro p hp
    simp only
    congr 1
    omega

/-- Applying the explicit Gaussian inverse coefficients to the incidence
transform reconstructs the original finite sequence. -/
theorem gaussianInverseCoefficient_incidenceTransform
    (q d e : ℕ) (hq : 1 < q) (c : ℕ → ℚ) (_hed : e ≤ d) :
    gaussianInverseCoefficient q d e (gaussianIncidenceTransform q d c) = c e := by
  let D := d - e
  have hsub (a : ℕ) (ha : a ≤ D) : d - (e + a) = D - a := by
    dsimp [D]
    omega
  have hreindex :
      (∑ a ∈ Finset.range (D + 1),
        gaussianMobius q a * (gaussianPascal q D a : ℚ) *
          (∑ b ∈ Finset.range (D - a + 1),
            (gaussianPascal q (D - a) b : ℚ) * c (e + a + b))) =
      ∑ u ∈ Finset.range (D + 1),
        (∑ a ∈ Finset.range (u + 1),
          gaussianMobius q a * (gaussianPascal q D a : ℚ) *
            gaussianPascal q (D - a) (u - a)) * c (e + u) := by
    calc
      _ = ∑ a ∈ Finset.range (D + 1),
          ∑ b ∈ Finset.range (D - a + 1),
            (gaussianMobius q a * (gaussianPascal q D a : ℚ) *
              gaussianPascal q (D - a) b) * c (e + a + b) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            ring
      _ = ∑ u ∈ Finset.range (D + 1),
          ∑ a ∈ Finset.range (u + 1),
            (gaussianMobius q a * (gaussianPascal q D a : ℚ) *
              gaussianPascal q (D - a) (u - a)) * c (e + a + (u - a)) := by
            exact sum_range_triangle_swap D _
      _ = ∑ u ∈ Finset.range (D + 1),
          (∑ a ∈ Finset.range (u + 1),
            gaussianMobius q a * (gaussianPascal q D a : ℚ) *
              gaussianPascal q (D - a) (u - a)) * c (e + u) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a ha
            have hau : a ≤ u := by
              have := Finset.mem_range.mp ha
              omega
            congr 2
            omega
  have horiginal :
      gaussianInverseCoefficient q d e (gaussianIncidenceTransform q d c) =
      ∑ a ∈ Finset.range (D + 1),
        gaussianMobius q a * (gaussianPascal q D a : ℚ) *
          (∑ b ∈ Finset.range (D - a + 1),
            (gaussianPascal q (D - a) b : ℚ) * c (e + a + b)) := by
    rw [gaussianInverseCoefficient]
    apply Finset.sum_congr
    · dsimp [D]
    · intro a ha
      have haD : a ≤ D := by
        have := Finset.mem_range.mp ha
        omega
      dsimp [gaussianIncidenceTransform]
      rw [hsub a haD]
  rw [horiginal, hreindex]
  calc
    ∑ u ∈ Finset.range (D + 1),
        (∑ a ∈ Finset.range (u + 1), gaussianMobius q a *
          (gaussianPascal q D a : ℚ) * gaussianPascal q (D - a) (u - a)) * c (e + u) =
      ∑ u ∈ Finset.range (D + 1), (if 0 = u then 1 else 0) * c (e + u) := by
        apply Finset.sum_congr rfl
        intro u hu
        have huD : u ≤ D := by
          have := Finset.mem_range.mp hu
          omega
        have hdelta := gaussianPascal_incidence_mobius q D 0 u hq (by omega) huD
        simp only [Nat.sub_zero] at hdelta
        rw [hdelta]
    _ = c e := by simp

/-- Full finite reconstruction: any sequence with the Gaussian incidence
expansion has the explicit Möbius coefficients. -/
theorem gaussian_triangular_reconstruction
    (q d : ℕ) (hq : 1 < q) (c w : ℕ → ℚ)
    (hw : ∀ r ≤ d, w r = gaussianIncidenceTransform q d c r) :
    ∀ e ≤ d, gaussianInverseCoefficient q d e w = c e := by
  intro e hed
  rw [gaussianInverseCoefficient]
  have heq :
      (∑ a ∈ Finset.range (d - e + 1), gaussianMobius q a *
        (gaussianPascal q (d - e) a : ℚ) * w (e + a)) =
      gaussianInverseCoefficient q d e (gaussianIncidenceTransform q d c) := by
    rw [gaussianInverseCoefficient]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hw (e + a) (by
      have := Finset.mem_range.mp ha
      omega)]
  rw [heq]
  exact gaussianInverseCoefficient_incidenceTransform q d e hq c hed

end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples

/-- The finite Gaussian inverse coefficients determine every entry through the cutoff. -/
theorem eq_on_of_gaussianInverseCoefficient_eq
    (q d : ℕ) (x y : ℕ → ℚ)
    (h : ∀ e ≤ d, gaussianInverseCoefficient q d e x =
      gaussianInverseCoefficient q d e y) :
    ∀ e ≤ d, x e = y e := by
  intro e hed
  induction hn : d - e using Nat.strong_induction_on generalizing e with
  | h n ih =>
    have hi := h e hed
    rw [gaussianInverseCoefficient, gaussianInverseCoefficient] at hi
    let S := (Finset.range (d - e + 1)).erase 0
    have hzero : 0 ∈ Finset.range (d - e + 1) := by simp
    have hxsplit :
        (∑ a ∈ Finset.range (d - e + 1), gaussianMobius q a *
          (gaussianPascal q (d - e) a : ℚ) * x (e + a)) =
        x e + ∑ a ∈ S, gaussianMobius q a *
          (gaussianPascal q (d - e) a : ℚ) * x (e + a) := by
      calc
        _ = gaussianMobius q 0 * (gaussianPascal q (d - e) 0 : ℚ) * x (e + 0) +
            ∑ a ∈ (Finset.range (d - e + 1)).erase 0, gaussianMobius q a *
              (gaussianPascal q (d - e) a : ℚ) * x (e + a) :=
          (Finset.add_sum_erase _ _ hzero).symm
        _ = _ := by simp [S, gaussianMobius, gaussianPascal_zero]
    have hysplit :
        (∑ a ∈ Finset.range (d - e + 1), gaussianMobius q a *
          (gaussianPascal q (d - e) a : ℚ) * y (e + a)) =
        y e + ∑ a ∈ S, gaussianMobius q a *
          (gaussianPascal q (d - e) a : ℚ) * y (e + a) := by
      calc
        _ = gaussianMobius q 0 * (gaussianPascal q (d - e) 0 : ℚ) * y (e + 0) +
            ∑ a ∈ (Finset.range (d - e + 1)).erase 0, gaussianMobius q a *
              (gaussianPascal q (d - e) a : ℚ) * y (e + a) :=
          (Finset.add_sum_erase _ _ hzero).symm
        _ = _ := by simp [S, gaussianMobius, gaussianPascal_zero]
    rw [hxsplit, hysplit] at hi
    have htail :
        (∑ a ∈ S, gaussianMobius q a *
          (gaussianPascal q (d - e) a : ℚ) * x (e + a)) =
        ∑ a ∈ S, gaussianMobius q a *
          (gaussianPascal q (d - e) a : ℚ) * y (e + a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have harange : a < d - e + 1 := Finset.mem_range.mp (Finset.mem_of_mem_erase ha)
      have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
      have hea : e + a ≤ d := by omega
      have hlt : d - (e + a) < n := by omega
      rw [ih (d - (e + a)) hlt (e + a) hea rfl]
    linarith

/-- Every finite rank-weight sequence has the Gaussian incidence expansion
with the explicit inverse coefficients. -/
theorem gaussianIncidenceTransform_inverseCoefficient
    (q d r : ℕ) (hq : 1 < q) (w : ℕ → ℚ) (hrd : r ≤ d) :
    gaussianIncidenceTransform q d
      (fun e => gaussianInverseCoefficient q d e w) r = w r := by
  apply eq_on_of_gaussianInverseCoefficient_eq q d
    (gaussianIncidenceTransform q d (fun e => gaussianInverseCoefficient q d e w)) w
    (fun e hed => ?_) r hrd
  rw [gaussianInverseCoefficient_incidenceTransform q d e hq
    (fun e => gaussianInverseCoefficient q d e w) hed]

end BinaryFieldCounterexamples
