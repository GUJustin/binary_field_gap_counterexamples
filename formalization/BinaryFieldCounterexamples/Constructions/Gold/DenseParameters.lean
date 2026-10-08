/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.PaperSemantics
public import BinaryFieldCounterexamples.Constructions.Gold.DimensionArithmetic
public import BinaryFieldCounterexamples.Constructions.Gold.DenseBounds

/-!
# Parameters for the dense Gold regime

This file chooses the growing tensor-rank parameter and controls the linear
rounding losses in the list and challenge-field exponents.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold

set_option maxHeartbeats 800000

noncomputable def denseTheta (c : ℕ) : ℝ := min ((1 : ℝ) / 4) (1 / ((c : ℝ) + 1))

def denseT (c d : ℕ) : ℕ := min (d / 4) ((d + c - 1) / (c + 1))

def denseDelta (c d : ℕ) : ℕ :=
  d + c - denseT c d * (c + if Even d then 1 else 0)

def denseEll (c d : ℕ) : ℕ :=
  denseGoldExponent c d (denseT c d)

def denseR (c d : ℕ) : ℕ := denseGoldExtensionDegree c d (denseT c d)

theorem denseTheta_pos (c : ℕ) : 0 < denseTheta c := by
  simp [denseTheta]
  positivity

theorem denseTheta_le_quarter (c : ℕ) : denseTheta c ≤ 1 / 4 := by
  exact min_le_left _ _

theorem denseT_le_quarter (c d : ℕ) : denseT c d ≤ d / 4 := by
  exact min_le_left _ _

theorem denseT_guards (c d : ℕ) (hd : 16 * (c + 1) ≤ d) :
    2 ≤ denseT c d ∧ denseT c d ≤ d / 2 ∧ 1 ≤ denseDelta c d := by
  have hc : 0 < c + 1 := by omega
  have hd8 : 8 ≤ d := by linarith
  have hfirst : 2 ≤ d / 4 := by omega
  have hnum : 2 * (c + 1) ≤ d + c - 1 := by omega
  have hsecond : 2 ≤ (d + c - 1) / (c + 1) :=
    (Nat.le_div_iff_mul_le hc).2 hnum
  have ht2 : 2 ≤ denseT c d := by simp [denseT, hfirst, hsecond]
  have ht4 := denseT_le_quarter c d
  have ht2d : denseT c d ≤ d / 2 := ht4.trans (by omega)
  have htsecond : denseT c d ≤ (d + c - 1) / (c + 1) := min_le_right _ _
  have htmul : denseT c d * (c + 1) ≤ d + c - 1 := by
    exact (Nat.le_div_iff_mul_le hc).mp htsecond
  have hi : (if Even d then 1 else 0) ≤ 1 := by split <;> omega
  have hfactor : c + (if Even d then 1 else 0) ≤ c + 1 := by omega
  have htmul' : denseT c d * (c + if Even d then 1 else 0) ≤ d + c - 1 :=
    (Nat.mul_le_mul_left _ hfactor).trans htmul
  have hdelta : 1 ≤ denseDelta c d := by
    dsimp [denseDelta]
    omega
  exact ⟨ht2, ht2d, hdelta⟩

theorem denseT_real_bounds (c d : ℕ) (hd : 1 ≤ d) :
    denseTheta c * (d : ℝ) - 2 ≤ denseT c d ∧
      (denseT c d : ℝ) ≤ denseTheta c * d + 1 := by
  -- Natural division is a floor, so each quotient has less than one unit of error.
  have hquot (m n : ℕ) :
      (m : ℝ) / n - 1 < ((m / n : ℕ) : ℝ) ∧
        ((m / n : ℕ) : ℝ) ≤ (m : ℝ) / n := by
    exact ⟨by simpa only [Nat.floor_div_eq_div] using
      Nat.sub_one_lt_floor ((m : ℝ) / n), Nat.cast_div_le⟩
  obtain ⟨haL, haU⟩ := hquot d 4
  obtain ⟨hbL, hbU⟩ := hquot (d + c - 1) (c + 1)
  simp only [Nat.cast_ofNat] at haL haU
  simp only [Nat.cast_add, Nat.cast_one] at hbL hbU
  have hnum : ((d + c - 1 : ℕ) : ℝ) = (d : ℝ) + c - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d + c), Nat.cast_add, Nat.cast_one]
  have hcpos : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have hshiftL : (d : ℝ) / ((c : ℝ) + 1) - 1 ≤
      ((d + c - 1 : ℕ) : ℝ) / ((c : ℝ) + 1) := by
    apply (le_div_iff₀ hcpos).2
    rw [sub_mul, div_mul_cancel₀ _ hcpos.ne', one_mul, hnum]
    linarith only [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
  have hshiftU : ((d + c - 1 : ℕ) : ℝ) / ((c : ℝ) + 1) ≤
      (d : ℝ) / ((c : ℝ) + 1) + 1 := by
    apply (div_le_iff₀ hcpos).2
    rw [add_mul, div_mul_cancel₀ _ hcpos.ne', one_mul, hnum]
    linarith only
  have haL' : (d : ℝ) / 4 - 2 ≤ ((d / 4 : ℕ) : ℝ) :=
    (sub_le_sub_left (by norm_num : (1 : ℝ) ≤ 2) _).trans haL.le
  have hbL' : (d : ℝ) / ((c : ℝ) + 1) - 2 ≤
      (((d + c - 1) / (c + 1) : ℕ) : ℝ) := by
    calc
      _ = ((d : ℝ) / ((c : ℝ) + 1) - 1) - 1 := by ring
      _ ≤ ((d + c - 1 : ℕ) : ℝ) / ((c : ℝ) + 1) - 1 :=
        sub_le_sub_right hshiftL 1
      _ ≤ _ := hbL.le
  have hminL := min_le_min haL' hbL'
  have hminU := min_le_min
    (haU.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
    (hbU.trans hshiftU)
  rw [min_sub_sub_right] at hminL
  rw [min_add_add_right] at hminU
  have hscale : min ((d : ℝ) / 4) ((d : ℝ) / ((c : ℝ) + 1)) =
      denseTheta c * (d : ℝ) := by
    rw [denseTheta, min_mul_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ d)]
    simp only [div_mul_eq_mul_div, one_mul]
  simpa only [denseT, Nat.cast_min, hscale] using And.intro hminL hminU

/-- The logarithmic size exponent before rounding to an extension degree has
only linear error from its quadratic leading term. -/
theorem denseEll_real_bounds (c d : ℕ) (hd : 16 * (c + 1) ≤ d) :
    let E := denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2
    E - 8 * ((c + 1 : ℕ) : ℝ) * (d : ℝ) ≤ (denseEll c d : ℝ) ∧
      (denseEll c d : ℝ) ≤ E + 8 * ((c + 1 : ℕ) : ℝ) * (d : ℝ) := by
  dsimp only
  -- First prove the rounding estimate with scalar variables, independently of the parameters.
  have hquadratic (D C X Y U S : ℝ) (hD1 : 1 ≤ D) (hC0 : 0 ≤ C)
      (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hX4 : X ≤ D / 4) (hY4 : Y ≤ D / 4)
      (hXYL : Y - 2 ≤ X) (hXYU : X ≤ Y + 1)
      (hUL : D / 2 - 1 ≤ U) (hUU : U ≤ D / 2)
      (hS0 : 0 ≤ S) (hSU : S ≤ D + C) :
      D * Y - 2 * Y ^ 2 - 8 * (C + 1) * D ≤ 2 * X + S + 2 * X * (U - X) ∧
        2 * X + S + 2 * X * (U - X) ≤ D * Y - 2 * Y ^ 2 + 8 * (C + 1) * D := by
    have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans hD1
    have hfactor0 : 0 ≤ D - 2 * X - 2 * Y := by linarith only [hX4, hY4]
    have hfactorU : D - 2 * X - 2 * Y ≤ D := by linarith only [hX0, hY0]
    have hdiffL : -2 ≤ X - Y := by linarith only [hXYL]
    have hdiffU : X - Y ≤ 1 := by linarith only [hXYU]
    have hprodL : -2 * D ≤ (X - Y) * (D - 2 * X - 2 * Y) := by
      have hmul := mul_le_mul_of_nonneg_right hdiffL hfactor0
      linarith only [hmul, hfactorU]
    have hprodU : (X - Y) * (D - 2 * X - 2 * Y) ≤ D := by
      have hmul := mul_le_mul_of_nonneg_right hdiffU hfactor0
      linarith only [hmul, hfactorU]
    have hroundL : -2 * X ≤ 2 * X * (U - X) - 2 * X * (D / 2 - X) := by
      linarith only [mul_le_mul_of_nonneg_left hUL hX0]
    have hroundU : 2 * X * (U - X) - 2 * X * (D / 2 - X) ≤ 0 := by
      linarith only [mul_le_mul_of_nonneg_left hUU hX0]
    have hmain : 2 * X * (D / 2 - X) - (D * Y - 2 * Y ^ 2) =
        (X - Y) * (D - 2 * X - 2 * Y) := by ring
    have hcoreL : D * Y - 2 * Y ^ 2 - 2 * D - 2 * X ≤ 2 * X * (U - X) := by
      linarith only [hmain, hprodL, hroundL]
    have hcoreU : 2 * X * (U - X) ≤ D * Y - 2 * Y ^ 2 + D := by
      linarith only [hmain, hprodU, hroundU]
    have hcMul : C ≤ C * D := by
      simpa using mul_le_mul_of_nonneg_left hD1 hC0
    have hCd : 2 * D ≤ 8 * (C + 1) * D := by
      linarith only [mul_nonneg hC0 hD0, hD0]
    constructor
    · have hlow : D * Y - 2 * Y ^ 2 - 2 * D ≤ 2 * X + S + 2 * X * (U - X) := by
        linarith only [hcoreL, hS0]
      exact (sub_le_sub_left hCd _).trans hlow
    · have hupp : 2 * X + S + 2 * X * (U - X) ≤ D * Y - 2 * Y ^ 2 + (5 / 2) * D + C := by
        linarith only [hcoreU, hSU, hX4]
      exact hupp.trans (by linarith only [hcMul, mul_nonneg hC0 hD0, hD0])

  -- Supply the floor and cast bounds once, then identify the scalar leading term.
  obtain ⟨ht2, htd2, hDelta⟩ := denseT_guards c d hd
  have hd1 : 1 ≤ d := by omega
  obtain ⟨htL, htU⟩ := denseT_real_bounds c d hd1
  have htheta4 := denseTheta_le_quarter c
  have hx4 : (denseT c d : ℝ) ≤ (d : ℝ) / 4 :=
    (Nat.cast_le.mpr (denseT_le_quarter c d)).trans Nat.cast_div_le
  have hy4 : denseTheta c * (d : ℝ) ≤ (d : ℝ) / 4 := by
    have h := mul_le_mul_of_nonneg_right htheta4 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    simpa only [div_mul_eq_mul_div, one_mul] using h
  have huU : ((d / 2 : ℕ) : ℝ) ≤ (d : ℝ) / 2 := Nat.cast_div_le
  have huL : (d : ℝ) / 2 - 1 ≤ ((d / 2 : ℕ) : ℝ) := by
    have hfloor := Nat.sub_one_lt_floor ((d : ℝ) / (2 : ℕ))
    rw [Nat.floor_div_eq_div] at hfloor
    simpa only [Nat.cast_ofNat] using hfloor.le
  have hDeltaR0 : 0 ≤ (denseDelta c d : ℝ) - 1 := by
    have hR : (1 : ℝ) ≤ denseDelta c d := by exact_mod_cast hDelta
    exact sub_nonneg.mpr hR
  have hDeltaRU : (denseDelta c d : ℝ) - 1 ≤ (d : ℝ) + c := by
    have hR : (denseDelta c d : ℝ) ≤ (d : ℝ) + c := by
      exact_mod_cast Nat.sub_le (d + c) (denseT c d * (c + if Even d then 1 else 0))
    exact (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans hR
  have hellNat : denseEll c d = 2 * denseT c d + (denseDelta c d - 1) +
      2 * (denseT c d * (d / 2 - denseT c d)) := rfl
  have hell : (denseEll c d : ℝ) = 2 * (denseT c d : ℝ) +
      ((denseDelta c d : ℝ) - 1) +
      2 * (denseT c d : ℝ) * (((d / 2 : ℕ) : ℝ) - denseT c d) := by
    rw [hellNat]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_sub hDelta, Nat.cast_sub htd2, mul_assoc]
  have hleading : (d : ℝ) * (denseTheta c * d) - 2 * (denseTheta c * d) ^ 2 =
      denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2 := by ring
  have hraw := hquadratic (d : ℝ) (c : ℝ) (denseT c d : ℝ) (denseTheta c * d)
    ((d / 2 : ℕ) : ℝ) ((denseDelta c d : ℝ) - 1)
    (by exact_mod_cast hd1) (Nat.cast_nonneg c) (Nat.cast_nonneg _)
    (mul_nonneg (denseTheta_pos c).le (Nat.cast_nonneg d)) hx4 hy4 htL htU
    huL huU hDeltaR0 hDeltaRU
  rw [hleading, ← hell] at hraw
  simpa only [Nat.cast_add, Nat.cast_one] using hraw

/-- Rounding `ell` down to a multiple of the base-field logarithm costs at
most one further linear term. -/
theorem denseRoundedExponent_bounds (c d : ℕ) (hd : 16 * (c + 1) ≤ d) :
    let E := denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2
    E - 10 * ((c + 1 : ℕ) : ℝ) * (d : ℝ) ≤
        (((d + c) * denseR c d : ℕ) : ℝ) ∧
      (((d + c) * denseR c d : ℕ) : ℝ) ≤
        E + 10 * ((c + 1 : ℕ) : ℝ) * (d : ℝ) := by
  dsimp only
  obtain ⟨hellL, hellU⟩ := denseEll_real_bounds c d hd
  have hd1 : 1 ≤ d := by linarith
  have hm : 0 < d + c := by omega
  have hfloor : (d + c) * denseR c d ≤ denseEll c d := by
    simpa [denseR, denseEll, denseGoldExtensionDegree, Nat.mul_comm] using
      Nat.div_mul_le_self (denseEll c d) (d + c)
  have hfloor' : denseEll c d < (d + c) * (denseR c d + 1) := by
    simpa [denseR, denseEll, denseGoldExtensionDegree] using
      (Nat.lt_mul_div_succ (denseEll c d) hm)
  have hfloorR : (((d + c) * denseR c d : ℕ) : ℝ) ≤ denseEll c d := by exact_mod_cast hfloor
  have hfloorR' : (denseEll c d : ℝ) - (d + c) <
      (((d + c) * denseR c d : ℕ) : ℝ) := by
    have hR : (denseEll c d : ℝ) <
        (d + c : ℕ) * ((denseR c d : ℝ) + 1) := by exact_mod_cast hfloor'
    push_cast at hR ⊢
    linarith
  have hmc : ((d + c : ℕ) : ℝ) ≤ ((c + 1 : ℕ) : ℝ) * (d : ℝ) := by
    push_cast
    have hc0 : (0 : ℝ) ≤ c := by positivity
    have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ d by exact_mod_cast hd1) hc0
    linarith
  constructor
  · calc
      _ ≤ (denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2 -
          8 * ((c + 1 : ℕ) : ℝ) * d) - (d + c : ℕ) := by linarith
      _ ≤ (denseEll c d : ℝ) - (d + c : ℕ) := by linarith
      _ ≤ (((d + c) * denseR c d : ℕ) : ℝ) := by
        simpa only [Nat.cast_add] using hfloorR'.le
  · calc
      (((d + c) * denseR c d : ℕ) : ℝ) ≤ denseEll c d := hfloorR
      _ ≤ _ := by linarith

theorem exists_denseGrowth_cutoff (c : ℕ) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d →
      16 * (c + 1) ≤ d ∧
      (4 : ℝ) * d <
        denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2 -
          10 * ((c + 1 : ℕ) : ℝ) * d := by
  let α := denseTheta c * (1 - 2 * denseTheta c)
  have hθ := denseTheta_pos c
  have hθ4 := denseTheta_le_quarter c
  have hhalf : 0 < 1 - 2 * denseTheta c := by linarith
  have hα : 0 < α := by dsimp [α]; exact mul_pos hθ hhalf
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (16 * ((c + 1 : ℕ) : ℝ))
      ((10 * ((c + 1 : ℕ) : ℝ) + 4) / α))
  refine ⟨n, fun d hnd ↦ ?_⟩
  have hndR : (n : ℝ) ≤ d := by exact_mod_cast hnd
  have hguardR : 16 * ((c + 1 : ℕ) : ℝ) < n :=
    (le_max_left _ _).trans_lt hn
  have hratio : (10 * ((c + 1 : ℕ) : ℝ) + 4) / α < n :=
    (le_max_right _ _).trans_lt hn
  have hguard : 16 * (c + 1) ≤ d := by
    exact_mod_cast (hguardR.le.trans hndR)
  refine ⟨hguard, ?_⟩
  have hdα : 10 * ((c + 1 : ℕ) : ℝ) + 4 < α * d := by
    have hnα := (div_lt_iff₀ hα).mp hratio
    exact hnα.trans_le (by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hndR hα.le)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by linarith)
  dsimp [α] at hdα ⊢
  linarith [mul_pos (sub_pos.mpr hdα) hdpos]

/-- The exact natural guards and the two rounded real exponent bounds consumed
by the finite dense Gold assembly. -/
theorem exists_denseParameter_bundle (c : ℕ) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d →
      let t := denseT c d
      let m := d + c
      let ell := denseGoldExponent c d t
      let r := denseGoldExtensionDegree c d t
      let E := denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2
      16 * (c + 1) ≤ d ∧ 2 ≤ t ∧ t ≤ d / 2 ∧
      1 ≤ d + c - t * (c + if Even d then 1 else 0) ∧
      m ≤ ell ∧ d + 1 ≤ ell - m ∧ 3 + (d - 2 * t) ≤ m * r ∧
      (2 : ℝ) ^ (E - 16 * ((c + 1 : ℕ) : ℝ) * d) ≤ (2 : ℝ) ^ (ell : ℝ) ∧
      (2 : ℝ) ^ (E - 16 * ((c + 1 : ℕ) : ℝ) * d) ≤ (2 : ℝ) ^ ((m * r : ℕ) : ℝ) ∧
      (2 : ℝ) ^ ((m * r : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (E + 16 * ((c + 1 : ℕ) : ℝ) * d) := by
  obtain ⟨d₀, hd₀⟩ := exists_denseGrowth_cutoff c
  refine ⟨d₀, fun d hd ↦ ?_⟩
  obtain ⟨hguard, hgrowth⟩ := hd₀ d hd
  obtain ⟨ht2, htd, hDelta⟩ := denseT_guards c d hguard
  obtain ⟨hellL, hellU⟩ := denseEll_real_bounds c d hguard
  obtain ⟨hrL, hrU⟩ := denseRoundedExponent_bounds c d hguard
  have hdpos : 0 < d := by linarith
  have hmle : d + c ≤ 2 * d := by linarith
  have hell4 : (4 : ℝ) * d < denseGoldExponent c d (denseT c d) := by
    have : denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2 -
        10 * ((c + 1 : ℕ) : ℝ) * d ≤ denseGoldExponent c d (denseT c d) := by
      simpa [denseEll] using (show
        denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2 -
          10 * ((c + 1 : ℕ) : ℝ) * d ≤ (denseEll c d : ℝ) by linarith [hellL])
    exact hgrowth.trans_le this
  have hr4 : (4 : ℝ) * d < (d + c) * denseGoldExtensionDegree c d (denseT c d) := by
    exact hgrowth.trans_le (by simpa [denseR] using hrL)
  have hell4N : 4 * d < denseGoldExponent c d (denseT c d) := by exact_mod_cast hell4
  have hr4N : 4 * d < (d + c) * denseGoldExtensionDegree c d (denseT c d) := by
    exact_mod_cast hr4
  have hmell : d + c ≤ denseGoldExponent c d (denseT c d) := by omega
  have hqexp : d + 1 ≤ denseGoldExponent c d (denseT c d) - (d + c) := by omega
  have h8 : 3 + (d - 2 * denseT c d) ≤
      (d + c) * denseGoldExtensionDegree c d (denseT c d) := by omega
  have hbase : (1 : ℝ) ≤ 2 := by norm_num
  dsimp only
  refine ⟨hguard, ht2, htd, hDelta, hmell, hqexp, h8, ?_, ?_, ?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hbase
    have this : denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2 -
        8 * ((c + 1 : ℕ) : ℝ) * d ≤ (denseGoldExponent c d (denseT c d) : ℝ) := by
      simpa [denseEll] using hellL
    norm_num only [Nat.cast_add, Nat.cast_one] at this ⊢
    linarith only [this,
      mul_nonneg (show (0 : ℝ) ≤ (c : ℝ) + 1 by positivity) (Nat.cast_nonneg d)]
  · apply Real.rpow_le_rpow_of_exponent_le hbase
    have this : denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2 -
        10 * ((c + 1 : ℕ) : ℝ) * d ≤
          (((d + c) * denseGoldExtensionDegree c d (denseT c d) : ℕ) : ℝ) := by
      simpa [denseR] using hrL
    norm_num only [Nat.cast_add, Nat.cast_one] at this ⊢
    linarith only [this,
      mul_nonneg (show (0 : ℝ) ≤ (c : ℝ) + 1 by positivity) (Nat.cast_nonneg d)]
  · apply Real.rpow_le_rpow_of_exponent_le hbase
    have this := (show (((d + c) * denseGoldExtensionDegree c d (denseT c d) : ℕ) : ℝ) ≤
        denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ) ^ 2 +
          10 * ((c + 1 : ℕ) : ℝ) * d by simpa [denseR] using hrU)
    norm_num only [Nat.cast_add, Nat.cast_one] at this ⊢
    linarith only [this,
      mul_nonneg (show (0 : ℝ) ≤ (c : ℝ) + 1 by positivity) (Nat.cast_nonneg d)]

theorem goldThreshold_deficit_eq (d t : ℕ) (ht : t + 1 ≤ d) :
    (1 : ℝ) / 2 -
        (((2 ^ d / 2 - 2 ^ d / 2 ^ (t + 1) : ℕ) : ℝ) / (2 ^ d : ℕ)) =
      1 / (2 : ℝ) ^ (t + 1) := by
  have hhalf : 2 ^ d / 2 = 2 ^ (d - 1) := by
    simpa using (Nat.pow_div (show 1 ≤ d by omega) (by decide : 0 < 2))
  have hsmall : 2 ^ d / 2 ^ (t + 1) = 2 ^ (d - (t + 1)) := by
    exact Nat.pow_div ht (by decide)
  have hsub : 2 ^ (d - (t + 1)) ≤ 2 ^ (d - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [hhalf, hsmall, Nat.cast_sub hsub, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have h1 : d - 1 + 1 = d := by omega
  have ht1 : d - (t + 1) + (t + 1) = d := by omega
  have hpow1 : (2 : ℝ) ^ (d - 1) * 2 = 2 ^ d := by
    calc
      _ = (2 : ℝ) ^ (d - 1) * 2 ^ 1 := by rw [pow_one]
      _ = _ := by rw [← pow_add, h1]
  have hpowt : (2 : ℝ) ^ (d - (t + 1)) * 2 ^ (t + 1) = 2 ^ d := by
    rw [← pow_add, ht1]
  have hN : (0 : ℝ) < 2 ^ d := by positivity
  have hT : (0 : ℝ) < 2 ^ (t + 1) := by positivity
  field_simp
  linarith only [congrArg (fun x : ℝ ↦ x * 2 ^ (t + 1)) hpow1, hpowt]

theorem denseThreshold_deficit_bounds (c d : ℕ) (hd : 16 * (c + 1) ≤ d) :
    let N : ℕ := 2 ^ d
    let T : ℕ := N / 2 - N / 2 ^ (denseT c d + 1)
    (1 / 4 : ℝ) * (N : ℝ) ^ (-denseTheta c) ≤ 1 / 2 - (T : ℝ) / N ∧
      1 / 2 - (T : ℝ) / N ≤ 2 * (N : ℝ) ^ (-denseTheta c) := by
  dsimp only
  obtain ⟨ht2, htd, hDelta⟩ := denseT_guards c d hd
  have hd1 : 1 ≤ d := by linarith
  obtain ⟨htL, htU⟩ := denseT_real_bounds c d hd1
  have ht1 : denseT c d + 1 ≤ d := by omega
  have hdef := goldThreshold_deficit_eq d (denseT c d) ht1
  have hNpow : (((2 ^ d : ℕ) : ℝ) ^ (-denseTheta c)) =
      (2 : ℝ) ^ (-denseTheta c * d) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hdefpow :
      (1 : ℝ) / 2 -
          (((2 ^ d / 2 - 2 ^ d / 2 ^ (denseT c d + 1) : ℕ) : ℝ) /
            (2 ^ d : ℕ)) =
        (2 : ℝ) ^ (-(denseT c d + 1 : ℕ) : ℝ) := by
    rw [hdef]
    rw [← Real.rpow_natCast]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [one_div]
  rw [hNpow, hdefpow]
  constructor
  · calc
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-denseTheta c * d) =
          (2 : ℝ) ^ (-2 : ℝ) * (2 : ℝ) ^ (-denseTheta c * d) := by
            norm_num [Real.rpow_neg]
      _ = (2 : ℝ) ^ ((-2 : ℝ) + (-denseTheta c * d)) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        norm_num only [Nat.cast_add, Nat.cast_one]
        linarith)
  · calc
      (2 : ℝ) ^ (-(denseT c d + 1 : ℕ) : ℝ) ≤
          (2 : ℝ) ^ ((1 : ℝ) + (-denseTheta c * d)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          norm_num only [Nat.cast_add, Nat.cast_one]
          linarith)
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-denseTheta c * d) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = 2 * (2 : ℝ) ^ (-denseTheta c * d) := by norm_num

end BinaryFieldCounterexamples.Gold
