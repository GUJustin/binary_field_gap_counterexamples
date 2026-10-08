/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.HigherRateLengthening.FieldBounds
/-!
# Exact rate parameters for higher-rate lengthening

The dyadic seed size divides four once the seed dimension is at least two.
Consequently the lower allowed rate is exactly the unpadded lengthened degree,
and taking the floor of the requested dimension never crosses below it.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.HigherRateLengthening

/-- Binary seed and ambient sizes have exactly the prescribed dyadic ratio. -/
theorem seed_size_ratio (r d : ℕ) (hrd : r ≤ d) :
    ((2^(d-r) : ℕ) : ℝ) / (2^d : ℕ) = 1 / (2^r : ℕ) := by
  have hp : (2^(d-r) : ℕ)*2^r=2^d := by rw [←pow_add,Nat.sub_add_cancel hrd]
  have hpr : (((2^(d-r) : ℕ) : ℝ))*((2^r : ℕ) : ℝ)=((2^d : ℕ) : ℝ) := by
    exact_mod_cast hp
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  simpa using hpr

/-- The seed size is divisible by four with no rounding loss. -/
theorem seed_quarter_cast (r d : ℕ) (hrd : r+2 ≤ d) :
    (((2^(d-r)/4 : ℕ) : ℝ)) = ((2^(d-r) : ℕ) : ℝ)/4 := by
  have hdiv : 4 ∣ (2^(d-r) : ℕ) := by
    change 2^2 ∣ 2^(d-r)
    exact Nat.pow_dvd_pow 2 (by omega)
  exact Nat.cast_div hdiv (by norm_num)

/-- Every rate in the stated interval supplies a legitimate padding size, and
the real padding-size identity has no hidden natural subtraction. -/
theorem rate_parameters (r d : ℕ) (hrd : r+2 ≤ d) (rho : ℝ)
    (hrho : 1-3*(1/(2^r : ℕ))/4 ≤ rho)
    (hrho' : rho < 1-(1/(2^r : ℕ))/4) :
    let N : ℕ := 2^d
    let M : ℕ := 2^(d-r)
    let K0 := N-M+M/4
    let J := ⌊rho*(N : ℝ)⌋₊
    let a := J-K0
    K0 ≤ J ∧ J ≤ N ∧ a ≤ M ∧ M ≤ N ∧
      (a : ℝ) = (J : ℝ)-(N : ℝ)+3*(M : ℝ)/4 := by
  dsimp only
  have hMN : (2^(d-r) : ℕ) ≤ 2^d :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hNpos : (0 : ℝ) < (2^d : ℕ) := by positivity
  have hratio := seed_size_ratio r d (by omega)
  have hquarter := seed_quarter_cast r d hrd
  have hKreal : ((2^d-2^(d-r)+2^(d-r)/4 : ℕ) : ℝ) =
      ((2^d : ℕ) : ℝ)-3*((2^(d-r) : ℕ) : ℝ)/4 := by
    rw [Nat.cast_add,Nat.cast_sub hMN,hquarter]
    ring
  have hKl : (((2^d-2^(d-r)+2^(d-r)/4 : ℕ) : ℝ)) ≤ rho*(2^d : ℕ) := by
    rw [hKreal]
    rw [←hratio] at hrho
    have hh := (div_le_iff₀ hNpos).mp (show
        (((2^d : ℕ) : ℝ)-3*((2^(d-r) : ℕ) : ℝ)/4)/((2^d : ℕ) : ℝ) ≤ rho by
      convert hrho using 1
      field_simp)
    exact hh
  have hK : 2^d-2^(d-r)+2^(d-r)/4 ≤ ⌊rho*(2^d : ℕ)⌋₊ :=
    (Nat.le_floor_iff (by linarith : 0 ≤ rho*(2^d : ℕ))).mpr hKl
  have hR : rho < 1 := by
    have hpos : (0 : ℝ) < 1/(2^r : ℕ) := by positivity
    linarith
  have hJ : ⌊rho*(2^d : ℕ)⌋₊ ≤ 2^d :=
    Nat.floor_le_of_le (by nlinarith : rho*(2^d : ℕ) ≤ ((2^d : ℕ) : ℝ))
  have ha := Nat.sub_le_sub_right hJ (2^d-2^(d-r)+2^(d-r)/4)
  refine ⟨hK,hJ,by
    exact ha.trans ((Nat.sub_le_sub_left (Nat.le_add_right (2^d-2^(d-r)) (2^(d-r)/4)) (2^d)).trans_eq (Nat.sub_sub_self hMN)),hMN,?_⟩
  rw [Nat.cast_sub hK,hKreal]
  ring

end BinaryFieldCounterexamples.HigherRateLengthening
