/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.OptimalFixedThreshold
public import BinaryFieldCounterexamples.Constructions.Gold.OptimalHyperplaneThreshold
/-!
# Main theorem: fixed-threshold counterexamples with exponent floor(b)+1

Paper statement: Theorem 5.4, p. 38. The paper chooses the sufficient exponent
`max(2, floor(b)+1)` so that the fixed-extension Gold corollary applies directly.
The theorem below preserves the stronger proved choice `floor(b)+1`.
For each proposed polynomial count exponent b>0, this exponent is determined before the
agreement threshold a, multiplicative constant C₀, and requested size cutoff.
For every 1/4<a<1/2 and C₀>0, arbitrarily large binary hyperplane domains of
size N have one pair with exact common agreement N/4 and more than C₀*N^b
distinct exceptional challenges at the natural ceiling of a*N. All code degrees are
strictly below N/4. The native field has size 2N; the challenge field has size
(2N)^(floor(b)+1), with the supplied embedding defining the same mapped domain.

For exponent at least two the proved fixed-extension Gold estimate supplies
order N^e challenges. The exponent-one branch uses the exact half-agreement
hyperplane theorem. The coarse positive probability suffices for this theorem;
this theorem does not assert a sharper leading coefficient.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
/-- The extension exponent is literally floor(b)+1 and cannot depend on any
later threshold, constant, or length choice. All field, domain and fixed-pair
conclusions are the original quantitative construction. -/
theorem no_fixed_polynomial_exceptional_bound_optimal_exponent
    (b : ℝ) (hb : 0<b) :
    ∀ (a C₀ : ℝ), 1/4<a → a<1/2 → 0<C₀ →
    ∀ N₀ : ℕ, ∃ d : ℕ, N₀ ≤ 2 ^ d ∧
    ∃ (B : Type) (fieldB : Field B) (finiteB : Fintype B),
    letI := fieldB
    letI := finiteB
    ∃ (_ : CharP B 2), Fintype.card B = 2 ^ (d + 1) ∧
    ∃ D : AddSubgroup B, (additiveDomain D).card = 2 ^ d ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
    letI := fieldF
    letI := finiteF
    ∃ φ : B →+* F, Fintype.card F = (2 ^ (d + 1)) ^ (⌊b⌋₊+1) ∧
    let D' := mappedDomain φ (additiveDomain D)
    let N : ℕ := 2 ^ d
    ∃ f g : D' → F,
      commonAgreementEQ D' (N / 4) f g (N / 4) ∧
      C₀ * (N : ℝ) ^ b <
        (badChallenges D' (N / 4) f g ⌈a * N⌉₊).card := by
  -- Exponent one is handled by the exact hyperplane construction.
  by_cases hb1 : b<1
  · have hfloor : ⌊b⌋₊=0:=Nat.floor_eq_zero.mpr hb1
    simpa only [hfloor,zero_add] using optimal_fixed_threshold_of_lt_one b hb hb1

  -- The fixed-extension Gold construction handles every larger exponent.
  · have he : 2≤⌊b⌋₊+1 := by
      have hfloor:= (Nat.one_le_floor_iff b).mpr (le_of_not_gt hb1)
      omega
    have hbe : b<((⌊b⌋₊+1:ℕ):ℝ) := by
      simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one b
    exact optimal_fixed_threshold_of_exponent (⌊b⌋₊+1) b he hb hbe
end BinaryFieldCounterexamples
