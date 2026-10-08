/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.Labels
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.Witnesses
public import BinaryFieldCounterexamples.Counting.CollisionPairs

/-!
# The quadratic construction over the base field

Distinct locator coefficient pairs have affine functions giving the challenges that collide at
at most one parameter.  Collision averaging therefore selects one coefficient
for which both image bounds in the paper hold simultaneously.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticConstruction

open Polynomial

/-- The affine locator challenge used when the construction stays in one field. -/
noncomputable def sameFieldLocatorLabel
    {F : Type*} [Field F] [Finite F]
    (K : ℕ) (θ : F) (W : AddSubgroup F) : F := by
  letI : Fintype W := Fintype.ofFinite W
  exact locatorCoeffA W K ^ 3 + locatorCoeffB W K ^ 2 +
    θ * locatorCoeffA W K

/-- Two distinct size-`4K` subgroups in the prescribed domain have affine
challenges that can agree for at most one parameter. -/
theorem sameFieldLocatorLabel_collision_unique
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D W₁ W₂ : AddSubgroup F)
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K = 2 ^ k)
    (hD : Nat.card D = 16 * K)
    (hW₁ : Nat.card W₁ = 4 * K) (hW₂ : Nat.card W₂ = 4 * K)
    (hle₁ : W₁ ≤ D) (hle₂ : W₂ ≤ D) (hne : W₁ ≠ W₂)
    {θ₁ θ₂ : F}
    (h₁ : sameFieldLocatorLabel K θ₁ W₁ = sameFieldLocatorLabel K θ₁ W₂)
    (h₂ : sameFieldLocatorLabel K θ₂ W₁ = sameFieldLocatorLabel K θ₂ W₂) :
    θ₁ = θ₂ := by
  classical
  let _ : Fintype W₁ := Fintype.ofFinite W₁
  let _ : Fintype W₂ := Fintype.ofFinite W₂
  have ha : locatorCoeffA W₁ K ≠ locatorCoeffA W₂ K := by
    intro ha
    have hbpow : locatorCoeffB W₁ K ^ 2 = locatorCoeffB W₂ K ^ 2 := by
      simpa only [sameFieldLocatorLabel, ha, add_left_inj, add_right_inj] using h₁
    have hb : locatorCoeffB W₁ K = locatorCoeffB W₂ K := CharTwo.sq_injective hbpow
    exact hne (eq_of_locatorCoeffA_eq_and_locatorCoeffB_eq D W₁ W₂ K hK hpow
      hD hW₁ hW₂ hle₁ hle₂ ha hb)
  have hprod : (θ₁ - θ₂) *
      (locatorCoeffA W₁ K - locatorCoeffA W₂ K) = 0 := by
    simp only [sameFieldLocatorLabel] at h₁ h₂
    linear_combination h₁ - h₂
  rcases mul_eq_zero.mp hprod with hθ | ha'
  · exact sub_eq_zero.mp hθ
  · exact (ha (sub_eq_zero.mp ha')).elim

/-- The total collision energy of any suitable subgroup family is bounded by
the number of its unordered pairs. -/
theorem sameFieldLocatorLabel_total_collisions
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [DecidableEq F]
    (D : AddSubgroup F) (S : Finset (AddSubgroup F))
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K = 2 ^ k)
    (hD : Nat.card D = 16 * K)
    (hcard : ∀ W ∈ S, Nat.card W = 4 * K)
    (hle : ∀ W ∈ S, W ≤ D) :
    ∑ θ ∈ (Finset.univ : Finset F),
        unorderedCollisionCount S (sameFieldLocatorLabel K θ) ≤ S.card.choose 2 := by
  classical
  let _ : LinearOrder (AddSubgroup F) := linearOrderOfSTO WellOrderingRel
  apply sum_unorderedCollisionCount_le_choose_two Finset.univ S
    (fun θ W ↦ sameFieldLocatorLabel K θ W)
  intro W₁ hW₁ W₂ hW₂ hne
  rw [Finset.card_le_one]
  intro θ₁ hθ₁ θ₂ hθ₂
  rw [Finset.mem_filter] at hθ₁ hθ₂
  exact sameFieldLocatorLabel_collision_unique D W₁ W₂ K hK hpow hD
    (hcard W₁ hW₁) (hcard W₂ hW₂) (hle W₁ hW₁) (hle W₂ hW₂) hne
    hθ₁.2 hθ₂.2

end BinaryFieldCounterexamples.QuadraticConstruction

namespace BinaryFieldCounterexamples

open Polynomial QuadraticConstruction

/-- Natural-number form of the same-field quadratic construction.  The two
bounds come from the same parameter chosen by collision averaging. -/
theorem quadratic_near_johnson_same_field_nat
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 16 * K) :
    let E := additiveDomain D
    let B₀ : ℕ := (16 * K - 1) * (16 * K - 2) / 6
    let q : ℕ := Fintype.card F
    ∃ θ : F,
      let f : E → F := fun x ↦ (x : F) ^ (8 * K - 1) + θ * (x : F) ^ (4 * K - 1)
      let g : E → F := fun x ↦ (x : F) ^ (2 * K - 1)
      commonAgreementEQ E K f g (2 * K - 1) ∧
      max (B₀ - Nat.choose B₀ 2 / q)
        (natCeilDiv (q * B₀ ^ 2) (q * B₀ + 2 * Nat.choose B₀ 2)) ≤
        (badChallenges E K f g (4 * K - 1)).card := by
  classical
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let E := additiveDomain D
  let B₀ : ℕ := (16 * K - 1) * (16 * K - 2) / 6
  let q : ℕ := Fintype.card F
  have hcD : Nat.card D = 16 * K := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hD
  have hfamily : B₀ ≤ (codimTwoBinarySubspaces D).card := by
    simpa only [B₀, hcD] using codimTwoBinarySubspaces_count_lower_bound D (by
      by_contra hrank
      have hrank' : Module.finrank (ZMod 2) D ≤ 1 := by omega
      have hcardpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
      have htwo : Nat.card (ZMod 2) = 2 := by
        rw [Nat.card_eq_fintype_card]
        exact ZMod.card 2
      rw [htwo, hcD] at hcardpow
      interval_cases Module.finrank (ZMod 2) D
      all_goals norm_num at hcardpow
      all_goals omega)
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hfamily
  have hScard4 : ∀ W ∈ S, Nat.card W = 4 * K := by
    intro W hW
    rw [natCard_codimTwoBinarySubspace D W (hSsub hW), hcD]
    omega
  have hSle : ∀ W ∈ S, W ≤ D := fun W hW ↦
    codimTwoBinarySubspaces_le D W (hSsub hW)
  have htotal : ∑ θ ∈ (Finset.univ : Finset F),
      unorderedCollisionCount S (sameFieldLocatorLabel K θ) ≤ Nat.choose B₀ 2 := by
    simpa only [hScard] using
      sameFieldLocatorLabel_total_collisions D S K hK hpow hcD hScard4 hSle
  obtain ⟨θ, _, hadd, hsecond⟩ := exists_parameter_image_card_bounds
    (Finset.univ : Finset F) S (fun θ W ↦ sameFieldLocatorLabel K θ W)
    (Nat.choose B₀ 2) Finset.univ_nonempty htotal
  let f : E → F := fun x ↦ firstWord K θ x
  let g : E → F := fun x ↦ secondWord K (x : F)
  have hg : agreementLE E K g (2 * K - 1) := by
    have hdeg : (K : WithBot ℕ) ≤ (X ^ (2 * K - 1) : F[X]).degree := by
      rw [degree_X_pow]
      exact_mod_cast (show K ≤ 2 * K - 1 by omega)
    simpa [g, secondWord] using agreementLE_polynomial E K
      (X ^ (2 * K - 1) : F[X]) hdeg
  have hpow2 : ∃ m : ℕ, 2 * K = 2 ^ m := by
    obtain ⟨k, hk⟩ := hpow
    exact ⟨k + 1, by rw [pow_succ, hk]; omega⟩
  obtain ⟨U, hUD, hUc⟩ := exists_binary_subspace_card_eq D (2 * K) hpow2 (by omega)
  have hUE : ∀ x ∈ U, x ∈ E := by
    intro x hx
    simpa only [E, additiveDomain, Finset.mem_filter, Finset.mem_univ, true_and] using hUD hx
  have hcommon : commonAgreementGE E K f g (2 * K - 1) :=
    by simpa [f, g] using commonAgreementGE_of_subgroup E U hUE K hpow hUc θ 0
  have hbad : S.image (sameFieldLocatorLabel K θ) ⊆
      badChallenges E K f g (4 * K - 1) := by
    intro z hz
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hz
    let _ : Fintype W := Fintype.ofFinite W
    have hw := bad_challenge_of_subgroup E W
      (fun x hx ↦ by simpa only [E, additiveDomain, Finset.mem_filter,
        Finset.mem_univ, true_and] using hSle W hW hx)
      K hK hpow (hScard4 W hW) θ 0
    simpa only [sameFieldLocatorLabel, locatorCoeffA, locatorCoeffB, zero_mul,
      add_zero, f, g, firstWord, secondWord] using hw
  refine ⟨θ, ⟨hcommon, commonAgreementLE_of_right E K f g _ hg⟩, ?_⟩
  have himage : (S.image (sameFieldLocatorLabel K θ)).card ≤
      (badChallenges E K f g (4 * K - 1)).card := Finset.card_le_card hbad
  have hadd' : B₀ - Nat.choose B₀ 2 / q ≤
      (S.image (sameFieldLocatorLabel K θ)).card := by
    simpa only [hScard, q, Finset.card_univ] using hadd
  have hsecond' : natCeilDiv (q * B₀ ^ 2)
      (q * B₀ + 2 * Nat.choose B₀ 2) ≤
      (S.image (sameFieldLocatorLabel K θ)).card := by
    simpa only [hScard, q, Finset.card_univ] using hsecond
  exact (max_le (hadd'.trans himage) (hsecond'.trans himage))

/-- Rational floor-and-ceiling form of the same-field construction, matching
the statement of Corollary 4.2. -/
theorem quadratic_near_johnson_same_field_proof
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 16 * K) :
    let E := additiveDomain D
    let B₀ : ℕ := (16 * K - 1) * (16 * K - 2) / 6
    let q : ℕ := Fintype.card F
    ∃ θ : F,
      let f : E → F := fun x ↦ (x : F) ^ (8 * K - 1) + θ * (x : F) ^ (4 * K - 1)
      let g : E → F := fun x ↦ (x : F) ^ (2 * K - 1)
      commonAgreementEQ E K f g (2 * K - 1) ∧
      max (B₀ - ⌊(Nat.choose B₀ 2 : ℚ) / q⌋₊)
        ⌈(q : ℚ) * B₀ / (q + B₀ - 1)⌉₊ ≤
        (badChallenges E K f g (4 * K - 1)).card := by
  classical
  let B₀ : ℕ := (16 * K - 1) * (16 * K - 2) / 6
  let q : ℕ := Fintype.card F
  have hB : 0 < B₀ := by
    dsimp only [B₀]
    have h₁ : 31 ≤ 16 * K - 1 := by omega
    have h₂ : 30 ≤ 16 * K - 2 := by omega
    apply Nat.div_pos
    · exact (by norm_num : 6 ≤ 31 * 30).trans (Nat.mul_le_mul h₁ h₂)
    · norm_num
  have hq : 0 < q := by
    exact Fintype.card_pos_iff.mpr ⟨0⟩
  have hfloor : ⌊(Nat.choose B₀ 2 : ℚ) / q⌋₊ = Nat.choose B₀ 2 / q := by
    rw [Nat.floor_div_natCast]
    norm_num
  have hchoose : 2 * Nat.choose B₀ 2 = B₀ * (B₀ - 1) := by
    rw [Nat.choose_two_right, mul_comm 2,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self B₀)]
  have hden : q * B₀ + 2 * Nat.choose B₀ 2 = B₀ * (q + B₀ - 1) := by
    rw [hchoose]
    calc
      q * B₀ + B₀ * (B₀ - 1) = B₀ * (q + (B₀ - 1)) := by ring
      _ = B₀ * (q + B₀ - 1) := by congr 1; omega
  have hdenpos : 0 < q * B₀ + 2 * Nat.choose B₀ 2 := by positivity
  have hceil :
      natCeilDiv (q * B₀ ^ 2) (q * B₀ + 2 * Nat.choose B₀ 2) =
        ⌈(q : ℚ) * B₀ / (q + B₀ - 1)⌉₊ := by
    rw [natCeilDiv_eq_rat_ceil _ _ hdenpos]
    congr 1
    rw [hden]
    simp only [Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub (show 1 ≤ q + B₀ by omega), Nat.cast_add, Nat.cast_one]
    field_simp
  simpa only [B₀, q, hfloor, ← hceil] using
    quadratic_near_johnson_same_field_nat D K hK hpow hD

/-- Full-field specialization of the collision bound. -/
theorem quadratic_near_johnson_full_field_proof
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K = 2 ^ k)
    (hF : Fintype.card F = 16 * K) :
    let E := additiveDomain (⊤ : AddSubgroup F)
    ∃ θ : F,
      let f : E → F := fun x ↦ (x : F) ^ (8 * K - 1) + θ * (x : F) ^ (4 * K - 1)
      let g : E → F := fun x ↦ (x : F) ^ (2 * K - 1)
      commonAgreementEQ E K f g (2 * K - 1) ∧
      16 * K - 5 ≤ (badChallenges E K f g (4 * K - 1)).card := by
  classical
  let N := 16 * K
  let B₀ := (N - 1) * (N - 2) / 6
  have hN : 32 ≤ N := by simp only [N]; omega
  have hdomain : (additiveDomain (⊤ : AddSubgroup F)).card = 16 * K := by
    simpa only [additiveDomain, AddSubgroup.mem_top, Finset.filter_true,
      Finset.card_univ] using hF
  obtain ⟨θ, hcommon, hbad⟩ :=
    quadratic_near_johnson_same_field_proof (⊤ : AddSubgroup F) K hK hpow hdomain
  refine ⟨θ, hcommon, ?_⟩
  let A := (N - 1) * (N - 2)
  have hmod : A % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hdiv : 6 * B₀ + A % 6 = A := by
    simpa only [A, B₀] using Nat.div_add_mod A 6
  have hsub₆ : N - 6 + 6 = N := by omega
  have hgap : (N - 6) * (N - 1) + 6 ≤ A := by
    calc
      (N - 6) * (N - 1) + 6 ≤ (N - 6) * (N - 1) + 4 * (N - 1) := by
        exact Nat.add_le_add_left (by omega) _
      _ = A := by
        rw [← Nat.add_mul, show N - 6 + 4 = N - 2 by omega, Nat.mul_comm]
  have hcross : (N - 6) * (N + B₀ - 1) < N * B₀ := by
    have hsmall : (N - 6) * (N - 1) < 6 * B₀ := by omega
    have hsum : N + B₀ - 1 = (N - 1) + B₀ := by omega
    calc
      (N - 6) * (N + B₀ - 1) = (N - 6) * (N - 1) + (N - 6) * B₀ := by
        rw [hsum, Nat.mul_add]
      _ < 6 * B₀ + (N - 6) * B₀ := Nat.add_lt_add_right hsmall _
      _ = N * B₀ := by rw [← Nat.add_mul, Nat.add_comm 6, hsub₆]
  have hdenpos : (0 : ℚ) < N + B₀ - 1 := by
    have hNQ : (1 : ℚ) < N := by exact_mod_cast (show 1 < N by omega)
    exact sub_pos.mpr (hNQ.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg B₀)))
  have hratio : (N - 6 : ℕ) <
      ⌈(N : ℚ) * B₀ / (N + B₀ - 1)⌉₊ := by
    rw [Nat.lt_ceil]
    rw [lt_div_iff₀ hdenpos]
    have hcrossQ : ((N - 6 : ℕ) : ℚ) * ((N + B₀ - 1 : ℕ) : ℚ) <
        (N * B₀ : ℕ) := by exact_mod_cast hcross
    simpa only [Nat.cast_mul,
      Nat.cast_sub (show 6 ≤ N by omega), Nat.cast_ofNat,
      Nat.cast_sub (show 1 ≤ N + B₀ by omega), Nat.cast_add, Nat.cast_one] using hcrossQ
  have hceil : N - 5 ≤ ⌈(N : ℚ) * B₀ / (N + B₀ - 1)⌉₊ := by omega
  have hmax : N - 5 ≤ max
      (B₀ - ⌊(Nat.choose B₀ 2 : ℚ) / N⌋₊)
      ⌈(N : ℚ) * B₀ / (N + B₀ - 1)⌉₊ := hceil.trans (le_max_right _ _)
  have hbad' : max
      (B₀ - ⌊(Nat.choose B₀ 2 : ℚ) / N⌋₊)
      ⌈(N : ℚ) * B₀ / (N + B₀ - 1)⌉₊ ≤
      (badChallenges (additiveDomain (⊤ : AddSubgroup F)) K
        (fun x ↦ (x : F) ^ (8 * K - 1) + θ * (x : F) ^ (4 * K - 1))
        (fun x ↦ (x : F) ^ (2 * K - 1)) (4 * K - 1)).card := by
    simpa only [N, B₀, hF] using hbad
  simpa only [N] using hmax.trans hbad'

end BinaryFieldCounterexamples
