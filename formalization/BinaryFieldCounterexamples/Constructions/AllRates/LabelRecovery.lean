/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.AllRates.AffineLabels
public import Mathlib.Algebra.CharP.Reduced

/-!
# Triangular recovery for cancellation challenges

The coefficient of each cancellation parameter exposes one new locator
coefficient after the earlier coefficients are known. Consequently, distinct
locator prefixes define distinct affine functions giving the residual challenges.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
namespace AllRatesConstruction
open Finset
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The linear part of a finite sum of affine maps is evaluated termwise. -/
theorem affineMap_sum_linear_apply {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] {ι : Type*}
    (S : Finset ι) (f : ι → (V →ᵃ[F] F)) (x : V) :
    (∑ i ∈ S, f i).linear x = ∑ i ∈ S, (f i).linear x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, ih]

/-- Coefficient of the raw parameter `θ k` in a cancellation coefficient. -/
def cancellationSlope {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) (k j : ℕ) : F :=
  (cancellationCoeffAffine s a j).linear (Pi.single k 1)

@[simp]
theorem cancellationSlope_zero {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) (k : ℕ) : cancellationSlope s a k 0 = 0 := by
  rw [cancellationSlope, cancellationCoeffAffine.eq_1]
  rfl

@[simp]
theorem cancellationSlope_succ {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) (k j : ℕ) :
    cancellationSlope s a k (j + 1) = (if k = j + 1 then 1 else 0) +
      ∑ i ∈ Finset.range (j + 1), cancellationSlope s a k i *
        a (j + 1 - i) ^ (2 ^ (s - 1 - i)) := by
  rw [cancellationSlope, cancellationCoeffAffine.eq_2]
  simp only [AffineMap.add_linear, LinearMap.add_apply, LinearMap.toAffineMap_linear,
    LinearMap.proj_apply]
  simp only [affineMap_sum_linear_apply, AffineMap.smul_linear,
    LinearMap.smul_apply, smul_eq_mul]
  rw [← Finset.sum_subtype (s := Finset.range (j + 1))
    (fun i ↦ Iff.rfl)
    (fun i ↦ a (j + 1 - i) ^ (2 ^ (s - 1 - i)) *
      (cancellationCoeffAffine s a i).linear (Pi.single k 1))]
  simp only [cancellationSlope]
  simp [Pi.single_apply, eq_comm, mul_comm]


/-- A parameter cannot affect an earlier recursive coefficient. -/
theorem cancellationSlope_eq_zero_of_lt {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) {j k : ℕ} (hjk : j < k) :
    cancellationSlope s a k j = 0 := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero => exact cancellationSlope_zero s a k
      | succ j =>
          rw [cancellationSlope_succ]
          have hne : k ≠ j + 1 := by omega
          simp only [hne, ↓reduceIte, zero_add]
          apply Finset.sum_eq_zero
          intro i hi
          have hij : i < j + 1 := Finset.mem_range.mp hi
          rw [ih i hij (by omega), zero_mul]

/-- A genuine parameter enters its own recursive coefficient with slope one. -/
theorem cancellationSlope_self {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) {k : ℕ} (hk : 1 ≤ k) :
    cancellationSlope s a k k = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [cancellationSlope_succ]
  simp only [↓reduceIte, add_eq_left]
  apply Finset.sum_eq_zero
  intro i hi
  have hij : i < j + 1 := Finset.mem_range.mp hi
  rw [cancellationSlope_eq_zero_of_lt s a hij, zero_mul]

/-- Slopes through stage `j` depend only on the locator coefficients through
index `j-k`. -/
theorem cancellationSlope_congr_of_prefix {F : Type*} [Field F]
    (s : ℕ) (a a' : ℕ → F) {k j : ℕ} (hkj : k ≤ j)
    (ha : ∀ u, u ≤ j - k → a u = a' u) :
    cancellationSlope s a k j = cancellationSlope s a' k j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero => simp
      | succ j =>
          rw [cancellationSlope_succ, cancellationSlope_succ]
          apply congrArg (fun z ↦ (if k = j + 1 then 1 else 0) + z)
          apply Finset.sum_congr rfl
          intro i hi
          have hij : i < j + 1 := Finset.mem_range.mp hi
          by_cases hik : i < k
          · rw [cancellationSlope_eq_zero_of_lt s a hik,
              cancellationSlope_eq_zero_of_lt s a' hik, zero_mul, zero_mul]
          · have hki : k ≤ i := Nat.le_of_not_gt hik
            rw [ih i hij hki (fun u hu ↦ ha u (by omega))]
            rw [ha (j + 1 - i) (by omega)]


/-- Coefficient of `θ k` in the residual affine challenge. -/
def cancellationLabelSlope {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) (k : ℕ) : F :=
  (cancellationLabelAffine s a).linear (Pi.single k 1)

/-- The residual slope is the corresponding linear combination of recursive
coefficient slopes. -/
theorem cancellationLabelSlope_apply {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) (k : ℕ) :
    cancellationLabelSlope s a k =
      ∑ i ∈ Finset.range s, cancellationSlope s a k i *
        a (s - i) ^ (2 ^ (s - 1 - i)) := by
  rw [cancellationLabelSlope, cancellationLabelAffine,
    affineMap_sum_linear_apply]
  simp only [AffineMap.smul_linear, LinearMap.smul_apply, smul_eq_mul,
    cancellationSlope]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- The residual challenge slope is the slope of the next recursive coefficient. -/
theorem cancellationLabelSlope_eq_nextSlope {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) {k : ℕ} (hks : k < s) :
    cancellationLabelSlope s a k = cancellationSlope s a k s := by
  rw [cancellationLabelSlope_apply]
  cases s with
  | zero => omega
  | succ j =>
      rw [cancellationSlope_succ]
      have hne : k ≠ j + 1 := by omega
      simp [hne]

/-- Equality of affine residual challenges recovers the next locator coefficient
once all earlier coefficients are known. -/
theorem next_coefficient_eq_of_cancellationLabelAffine_eq
    {F : Type*} [Field F] [CharP F 2]
    (s m : ℕ) (hm1 : 1 ≤ m) (hms : m < s) (a a' : ℕ → F)
    (ha : ∀ u, u < m → a u = a' u)
    (hlabel : cancellationLabelAffine s a = cancellationLabelAffine s a') :
    a m = a' m := by
  let k := s - m
  have hk1 : 1 ≤ k := by omega
  have hks : k < s := by omega
  have hkadd : k + m = s := by omega
  have hlabelSlope : cancellationLabelSlope s a k = cancellationLabelSlope s a' k := by
    have hlinear := congrArg AffineMap.linear hlabel
    exact congrArg (fun L ↦ L (Pi.single k 1)) hlinear
  have hsum :
      (∑ i ∈ Finset.range s, cancellationSlope s a k i *
        a (s - i) ^ (2 ^ (s - 1 - i))) =
      ∑ i ∈ Finset.range s, cancellationSlope s a' k i *
        a' (s - i) ^ (2 ^ (s - 1 - i)) := by
    simpa [cancellationLabelSlope_apply] using hlabelSlope
  let T : ℕ → F := fun i ↦ cancellationSlope s a k i *
    a (s - i) ^ (2 ^ (s - 1 - i))
  let T' : ℕ → F := fun i ↦ cancellationSlope s a' k i *
    a' (s - i) ^ (2 ^ (s - 1 - i))
  have hkMem : k ∈ Finset.range s := Finset.mem_range.mpr hks
  have hother : ∀ i ∈ (Finset.range s).erase k, T i = T' i := by
    intro i hi
    have his : i < s := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    by_cases hiklt : i < k
    · simp only [T, T']
      rw [cancellationSlope_eq_zero_of_lt s a hiklt,
        cancellationSlope_eq_zero_of_lt s a' hiklt, zero_mul, zero_mul]
    · have hki : k ≤ i := Nat.le_of_not_gt hiklt
      have hki' : k < i := lt_of_le_of_ne hki hik.symm
      have hslope : cancellationSlope s a k i = cancellationSlope s a' k i := by
        apply cancellationSlope_congr_of_prefix s a a' hki
        intro u hu
        apply ha u
        omega
      have hacoeff : a (s - i) = a' (s - i) := ha _ (by omega)
      simp only [T, T', hslope, hacoeff]
  have hrem : ∑ i ∈ (Finset.range s).erase k, T i =
      ∑ i ∈ (Finset.range s).erase k, T' i := by
    exact Finset.sum_congr rfl hother
  have hdecomp := Finset.sum_erase_add (Finset.range s) T hkMem
  have hdecomp' := Finset.sum_erase_add (Finset.range s) T' hkMem
  have hTk : T k = a m ^ (2 ^ (m - 1)) := by
    simp only [T, cancellationSlope_self s a hk1, one_mul]
    congr 2 <;> omega
  have hTk' : T' k = a' m ^ (2 ^ (m - 1)) := by
    simp only [T', cancellationSlope_self s a' hk1, one_mul]
    congr 2 <;> omega
  have hpowers : a m ^ (2 ^ (m - 1)) = a' m ^ (2 ^ (m - 1)) := by
    rw [← hTk, ← hTk']
    apply add_left_cancel (a := ∑ i ∈ (Finset.range s).erase k, T i)
    calc
      (∑ i ∈ (Finset.range s).erase k, T i) + T k =
          ∑ i ∈ Finset.range s, T i := hdecomp
      _ = ∑ i ∈ Finset.range s, T' i := hsum
      _ = (∑ i ∈ (Finset.range s).erase k, T' i) + T' k := hdecomp'.symm
      _ = (∑ i ∈ (Finset.range s).erase k, T i) + T' k := by rw [hrem]
  apply iterateFrobenius_inj F 2 (m - 1)
  simpa [iterateFrobenius_def, iterate_frobenius] using hpowers


/-- At zero parameters, coefficient `j` depends only on the locator prefix
through `j`. -/
theorem cancellationCoeff_zero_congr_of_prefix {F : Type*} [Field F]
    (s : ℕ) (a a' : ℕ → F) {j : ℕ}
    (ha : ∀ u, u ≤ j → a u = a' u) :
    cancellationCoeff s a 0 j = cancellationCoeff s a' 0 j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero => simp
      | succ j =>
          rw [cancellationCoeff_succ, cancellationCoeff_succ]
          simp only [Pi.zero_apply, zero_add]
          apply Finset.sum_congr rfl
          intro i hi
          have hij : i < j + 1 := Finset.mem_range.mp hi
          rw [ih i hij (fun u hu ↦ ha u (by omega))]
          rw [ha (j + 1 - i) (by omega)]

/-- Once the coefficients below `s` agree, equality of residual affine challenges
recovers coefficient `s` from their constant terms. -/
theorem last_coefficient_eq_of_cancellationLabelAffine_eq
    {F : Type*} [Field F] [CharP F 2]
    (s : ℕ) (hs : 1 ≤ s) (a a' : ℕ → F)
    (ha : ∀ u, u < s → a u = a' u)
    (hlabel : cancellationLabelAffine s a = cancellationLabelAffine s a') :
    a s = a' s := by
  have hsum :
      (∑ i ∈ Finset.range s, cancellationCoeff s a 0 i *
        a (s - i) ^ (2 ^ (s - 1 - i))) =
      ∑ i ∈ Finset.range s, cancellationCoeff s a' 0 i *
        a' (s - i) ^ (2 ^ (s - 1 - i)) := by
    have heval := congrArg (fun A ↦ A (0 : ℕ → F)) hlabel
    change cancellationLabel s a 0 = cancellationLabel s a' 0 at heval
    simpa only [cancellationLabel_apply] using heval
  let T : ℕ → F := fun i ↦ cancellationCoeff s a 0 i *
    a (s - i) ^ (2 ^ (s - 1 - i))
  let T' : ℕ → F := fun i ↦ cancellationCoeff s a' 0 i *
    a' (s - i) ^ (2 ^ (s - 1 - i))
  have hzeroMem : 0 ∈ Finset.range s := Finset.mem_range.mpr hs
  have hother : ∀ i ∈ (Finset.range s).erase 0, T i = T' i := by
    intro i hi
    have his : i < s := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    have hcoeff : cancellationCoeff s a 0 i = cancellationCoeff s a' 0 i := by
      apply cancellationCoeff_zero_congr_of_prefix s a a'
      intro u hu
      apply ha u
      omega
    have hacoeff : a (s - i) = a' (s - i) := ha _ (by omega)
    simp only [T, T', hcoeff, hacoeff]
  have hrem : ∑ i ∈ (Finset.range s).erase 0, T i =
      ∑ i ∈ (Finset.range s).erase 0, T' i := Finset.sum_congr rfl hother
  have hdecomp := Finset.sum_erase_add (Finset.range s) T hzeroMem
  have hdecomp' := Finset.sum_erase_add (Finset.range s) T' hzeroMem
  have hT0 : T 0 = a s ^ (2 ^ (s - 1)) := by simp [T]
  have hT0' : T' 0 = a' s ^ (2 ^ (s - 1)) := by simp [T']
  have hpowers : a s ^ (2 ^ (s - 1)) = a' s ^ (2 ^ (s - 1)) := by
    rw [← hT0, ← hT0']
    apply add_left_cancel (a := ∑ i ∈ (Finset.range s).erase 0, T i)
    calc
      (∑ i ∈ (Finset.range s).erase 0, T i) + T 0 =
          ∑ i ∈ Finset.range s, T i := hdecomp
      _ = ∑ i ∈ Finset.range s, T' i := hsum
      _ = (∑ i ∈ (Finset.range s).erase 0, T' i) + T' 0 := hdecomp'.symm
      _ = (∑ i ∈ (Finset.range s).erase 0, T i) + T' 0 := by rw [hrem]
  apply iterateFrobenius_inj F 2 (s - 1)
  simpa [iterateFrobenius_def, iterate_frobenius] using hpowers

/-- Equality of the affine functions giving the cancellation challenges recovers the entire
locator prefix `a₀,…,a_s`. -/
theorem cancellationLabelAffine_prefix_injective
    {F : Type*} [Field F] [CharP F 2]
    (s : ℕ) (hs : 2 ≤ s) (a a' : ℕ → F) (ha0 : a 0 = a' 0)
    (hlabel : cancellationLabelAffine s a = cancellationLabelAffine s a') :
    ∀ u, u ≤ s → a u = a' u := by
  have hbelow : ∀ u, u < s → a u = a' u := by
    intro u hus
    induction u using Nat.strong_induction_on with
    | h u ih =>
        by_cases hu0 : u = 0
        · simpa [hu0] using ha0
        · apply next_coefficient_eq_of_cancellationLabelAffine_eq s u
            (by omega) hus a a' (fun v hv ↦ ih v hv (by omega)) hlabel
  intro u hus
  by_cases hu : u < s
  · exact hbelow u hu
  · have hueq : u = s := by omega
    subst u
    exact last_coefficient_eq_of_cancellationLabelAffine_eq s (by omega) a a' hbelow hlabel

/-- Recursive coefficients through stage `j` only inspect parameters numbered
`1,…,j`. -/
theorem cancellationCoeff_congr_of_parameters {F : Type*} [Field F]
    (s : ℕ) (a θ θ' : ℕ → F) {j : ℕ}
    (hθ : ∀ u, 1 ≤ u → u ≤ j → θ u = θ' u) :
    cancellationCoeff s a θ j = cancellationCoeff s a θ' j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero => simp
      | succ j =>
          rw [cancellationCoeff_succ, cancellationCoeff_succ,
            hθ (j + 1) (by omega) (by omega)]
          apply congrArg (fun z ↦ θ' (j + 1) + z)
          apply Finset.sum_congr rfl
          intro i hi
          have hij : i < j + 1 := Finset.mem_range.mp hi
          rw [ih i hij (fun u hu1 hui ↦ hθ u hu1 (by omega))]

/-- The residual challenge uses precisely parameters `1,…,s-1`. -/
theorem cancellationLabel_congr_of_parameters {F : Type*} [Field F]
    (s : ℕ) (a θ θ' : ℕ → F)
    (hθ : ∀ u, 1 ≤ u → u < s → θ u = θ' u) :
    cancellationLabel s a θ = cancellationLabel s a θ' := by
  rw [cancellationLabel_apply, cancellationLabel_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have his : i < s := Finset.mem_range.mp hi
  rw [cancellationCoeff_congr_of_parameters s a θ θ'
    (fun u hu1 hui ↦ hθ u hu1 (by omega))]

/-- The finite parameter wrapper keeps all information in the raw affine
cancellation challenge. -/
theorem cancellationLabelAffine_eq_of_finite_eq
    {F : Type*} [Field F] (s : ℕ) (a a' : ℕ → F)
    (hfinite : finiteCancellationLabelAffine s a =
      finiteCancellationLabelAffine s a') :
    cancellationLabelAffine s a = cancellationLabelAffine s a' := by
  apply AffineMap.ext
  intro θ
  let θfin : Fin (s - 1) → F := fun j ↦ θ (j + 1)
  have hext (u : ℕ) (hu1 : 1 ≤ u) (hus : u < s) :
      finiteCancellationParameterExtension s θfin u = θ u := by
    rw [finiteCancellationParameterExtension_apply_of_mem s θfin u hu1 hus]
    simp only [θfin]
    congr 1
    omega
  calc
    cancellationLabelAffine s a θ = cancellationLabel s a θ := rfl
    _ = cancellationLabel s a (finiteCancellationParameterExtension s θfin) := by
      apply cancellationLabel_congr_of_parameters
      intro u hu1 hus
      exact (hext u hu1 hus).symm
    _ = finiteCancellationLabelAffine s a θfin := rfl
    _ = finiteCancellationLabelAffine s a' θfin := by rw [hfinite]
    _ = cancellationLabel s a' (finiteCancellationParameterExtension s θfin) := rfl
    _ = cancellationLabel s a' θ := by
      apply cancellationLabel_congr_of_parameters
      exact hext
    _ = cancellationLabelAffine s a' θ := rfl

/-- Distinct locator prefixes produce distinct affine functions of the genuine
cancellation parameters. -/
theorem finiteCancellationLabelAffine_injective_of_prefix
    {F : Type*} [Field F] [CharP F 2]
    (s : ℕ) (hs : 2 ≤ s) {a a' : ℕ → F} (ha0 : a 0 = a' 0)
    (hpref : ∃ u ≤ s, a u ≠ a' u) :
    finiteCancellationLabelAffine s a ≠ finiteCancellationLabelAffine s a' := by
  intro hlabel
  have hraw := cancellationLabelAffine_eq_of_finite_eq s a a' hlabel
  have hall := cancellationLabelAffine_prefix_injective s hs a a' ha0 hraw
  obtain ⟨u, hus, hu⟩ := hpref
  exact hu (hall u hus)

end AllRatesConstruction
end BinaryFieldCounterexamples
