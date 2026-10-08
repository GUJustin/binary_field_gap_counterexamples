/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.QuadraticNearJohnson
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.SharpSource
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.SameField

/-!
# Main theorem companions: sharper input bounds and every containing field

The proper-extension theorem is verified in `QuadraticNearJohnson.lean`.
This module proves three quantitative companions:
Theorem 4.1's sharper individual bound for extension degree at least three,
Corollary 4.2's simultaneous collision bounds over every containing field, and
its full-field specialization. They keep the original concrete semantics and
strict-degree hypotheses. All three proofs preserve these contracts.

For the sharper assertion choose a shift of the first input outside the span of `1,θ`.
Three independent coordinate projections bound individual agreement by `2K−1`;
the same remainder construction attains it.
-/

/-!
## Companion main result: every containing field

For [Corollary 4.2, p. 30](../../../binary-field-counterexamples.pdf#page=30), let `D ⊆ F` be any binary additive domain with
`N = 16 K`, `K ≥ 2` a power of two, and `F` finite of size `q`. Set
`B₀ = (N - 1)(N - 2)/6`. There exists `θ ∈ F` such that the unshifted pair
`f₀ = X^(8 K - 1) + θ X^(4 K - 1)`, `g = X^(2 K - 1)` has
`CA_K(f₀,g) = 2 K - 1` and at least

`max {B₀ - floor(choose(B₀,2)/q), ceil(q B₀/(q + B₀ - 1))}`

distinct exceptional challenges at threshold `4 K - 1`. The companion does not assert
the individual first-input bound above. Prove that two distinct locator challenges
collide for at most one value of `θ`; average unordered collisions and apply
both image-size estimates to the same minimizing `θ`. For `D = F`, the ceiling
gives at least `N - 5` exceptional challenges. This branch needs collision
averaging; the proper-extension construction uses injectivity directly.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial QuadraticConstruction

/-- Theorem 4.1, extension degree at least three: both inputs attain the sharp bound.
For a finite-field embedding, the cardinal inequality is equivalent to extension
 degree at least three. -/
theorem quadratic_near_johnson_both_far
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hext : Fintype.card B ^ 3 ≤ Fintype.card F)
    (D : AddSubgroup B) (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 16 * K) :
    let E := mappedDomain φ (additiveDomain D)
    ∃ f g : E → F,
      commonAgreementEQ E K f g (2 * K - 1) ∧
      agreementEQ E K f (2 * K - 1) ∧ agreementEQ E K g (2 * K - 1) ∧
      ((16 * K - 1) * (16 * K - 2) / 6) ≤
        (badChallenges E K f g (4 * K - 1)).card := by
  classical
  let : Algebra B F := φ.toAlgebra
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  obtain ⟨θ, s, hθ, l, hl1, hlθ, hls⟩ := exists_quadratic_sharp_coordinates (B := B) hext
  let E := mappedDomain φ (additiveDomain D)
  let f : E → F := fun x ↦ firstWord K θ x + s * secondWord K (x : F)
  let g : E → F := fun x ↦ secondWord K (x : F)
  have hf : agreementLE E K f (2 * K - 1) :=
    quadratic_source_agreementLE_of_projection (additiveDomain D) K (by omega) θ s l hl1 hlθ hls
  -- The second input bounds common agreement; remainders attain the bound.
  have hg : agreementLE E K g (2 * K - 1) := by
    have hdeg : (K : WithBot ℕ) ≤ (X ^ (2 * K - 1) : F[X]).degree := by
      rw [degree_X_pow]
      exact_mod_cast (show K ≤ 2 * K - 1 by omega)
    simpa [g, secondWord] using agreementLE_polynomial E K (X ^ (2 * K - 1) : F[X]) hdeg
  have hcD : Nat.card D = 16 * K := by simpa [card_additiveDomain] using hD
  have hpow2 : ∃ m : ℕ, 2 * K = 2 ^ m := by
    obtain ⟨k, hk⟩ := hpow
    exact ⟨k + 1, by rw [pow_succ, hk]; omega⟩
  obtain ⟨U, hUD, hUc⟩ := exists_binary_subspace_card_eq D (2 * K) hpow2 (by omega)
  let UF := U.map φ.toAddMonoidHom
  have hUFc : Nat.card UF = 2 * K := by
    exact (AddSubgroup.card_map_of_injective φ.injective).trans hUc
  have hUFE : ∀ x ∈ UF, x ∈ E := by
    rintro x ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, (mem_additiveDomain D y).mpr (hUD hy), rfl⟩
  have hcommon : commonAgreementGE E K f g (2 * K - 1) :=
    commonAgreementGE_of_subgroup E UF hUFE K hpow hUFc θ (s)
  refine ⟨f, g, ⟨hcommon, commonAgreementLE_of_right E K f g _ hg⟩,
    ⟨agreementGE_left_of_common E K f g _ hcommon, hf⟩, ⟨agreementGE_right_of_common E K f g _ hcommon, hg⟩, ?_⟩
  -- Count distinct challenges and transport every witness into the prescribed domain.
  let labels := (codimTwoBinarySubspaces D).image (finiteLocatorLabel φ θ K)
  have hlower : ((16 * K - 1) * (16 * K - 2) / 6) ≤ labels.card := by
    simpa only [hcD] using codimTwo_label_count_lower_bound φ θ hθ D K hK hpow hcD
  let shifted := labels.image (fun z ↦ z + s)
  have hshiftcard : shifted.card = labels.card :=
    Finset.card_image_of_injective labels (fun _ _ h ↦ add_right_cancel h)
  have hsubset : shifted ⊆ badChallenges E K f g (4 * K - 1) := by
    intro z hz
    obtain ⟨z0, hz0, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hz0
    let : Fintype W := Fintype.ofFinite W
    let WF := W.map φ.toAddMonoidHom
    have hWc : Nat.card W = 4 * K := by
      rw [natCard_codimTwoBinarySubspace D W hW, hcD]
      omega
    have hWFc : Nat.card WF = 4 * K := (natCard_map_addSubgroup φ W).trans hWc
    have hWFE : ∀ x ∈ WF, x ∈ E := by
      rintro x ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨y,
        (mem_additiveDomain D y).mpr (codimTwoBinarySubspaces_le D W hW hy), rfl⟩
    have hbad := bad_challenge_of_subgroup E WF hWFE K hK hpow hWFc θ (s)
    simpa only [WF, coeff_subspacePolynomial_map, finiteLocatorLabel, locatorLabel,
      locatorCoeffA, locatorCoeffB, map_add, map_pow] using hbad
  exact hlower.trans (hshiftcard ▸ Finset.card_le_card hsubset)

/-- Corollary 4.2: the same explicit monomial pair over every containing field. -/
theorem quadratic_near_johnson_same_field
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 16 * K) :
    let E := additiveDomain D
    let B₀ : ℕ := (16 * K - 1) * (16 * K - 2) / 6
    let q : ℕ := Fintype.card F
    ∃ θ : F,
      let f : E → F := fun x => (x : F) ^ (8 * K - 1) + θ * (x : F) ^ (4 * K - 1)
      let g : E → F := fun x => (x : F) ^ (2 * K - 1)
      commonAgreementEQ E K f g (2 * K - 1) ∧
      max (B₀ - ⌊(Nat.choose B₀ 2 : ℚ) / q⌋₊)
        ⌈(q : ℚ) * B₀ / (q + B₀ - 1)⌉₊ ≤
        (badChallenges E K f g (4 * K - 1)).card := by
  exact quadratic_near_johnson_same_field_proof D K hK hpow hD

/-- Corollary 4.2, full-field specialization: at least `N - 5` of all `N`
challenges qualify at threshold `N / 4 - 1`. -/
theorem quadratic_near_johnson_full_field
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K = 2 ^ k)
    (hF : Fintype.card F = 16 * K) :
    let E := additiveDomain (⊤ : AddSubgroup F)
    ∃ θ : F,
      let f : E → F := fun x => (x : F) ^ (8 * K - 1) + θ * (x : F) ^ (4 * K - 1)
      let g : E → F := fun x => (x : F) ^ (2 * K - 1)
      commonAgreementEQ E K f g (2 * K - 1) ∧
      16 * K - 5 ≤ (badChallenges E K f g (4 * K - 1)).card := by
  exact quadratic_near_johnson_full_field_proof K hK hpow hF

end BinaryFieldCounterexamples
