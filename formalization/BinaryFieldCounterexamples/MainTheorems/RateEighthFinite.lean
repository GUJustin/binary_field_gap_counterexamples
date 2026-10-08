/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.QuadraticNearJohnsonCompanions
public import BinaryFieldCounterexamples.Agreement.AffineTransport
public import BinaryFieldCounterexamples.Constructions.AllRates.FiniteSeed
public import BinaryFieldCounterexamples.Constructions.AllRates.Padding

@[expose] public section

/-!
# Main theorem: rate `1/8` at finite length

## Manuscript statement and status

Paper statement: [Corollary 4.6, p. 34](../../../binary-field-counterexamples.pdf#page=34).
Public theorems: `BinaryFieldCounterexamples.rate_eighth_finite` and
`BinaryFieldCounterexamples.rate_eighth_finite_count`.
**Proved.**

Let `D ⊆ F` be a binary additive domain of size `N = 32 K`, with `K ≥ 2` a power
of two, and let `a ∈ F`. Put `J = N/8 = 4 K`, `M = (N/2 - 1)(N/2 - 2)/6`, and
`q = |F|`. On the translate `D + a` there is one pair with `agr_J(g) = CA_J(f,g) = J` and at
least `ceil(q M/(q + M - 1))` distinct exceptional challenges at agreement
`3 N/16 = 6 K`. Zero may be among them. For `N = 2^20` and `q = 2^64` the count is
`45812722234`.

## Proof assembly

Apply Corollary 4.2 on a subspace `H ≤ D` of size `N/2 = 16 K`. Its second input
`X^(2 K - 1)` has degree `2 K - 1`, so its witnesses also count at that message
length. Multiply both inputs by the nodal polynomial of `2 K + 1` points of
`D \ H`. The padded second input is monic of degree `4 K`, which gives exact
common agreement, and every padding point is a new agreement, which raises the
threshold from `4 K - 1` to `6 K`. Translation by `a` preserves both statements.
-/

namespace BinaryFieldCounterexamples

open Polynomial AllRatesConstruction

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corollary 4.6: the padded quadratic count at rate `1/8` on every translate
of every binary additive domain of size `32 K`. -/
theorem rate_eighth_finite
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (a : F) (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 32 * K) :
    let E := affineDomain (additiveDomain D) a
    let M : ℕ := (16 * K - 1) * (16 * K - 2) / 6
    let q : ℕ := Fintype.card F
    ∃ f g : E → F,
      commonAgreementEQ E (4 * K) f g (4 * K) ∧ agreementEQ E (4 * K) g (4 * K) ∧
      ⌈(q : ℚ) * M / (q + M - 1)⌉₊ ≤ (badChallenges E (4 * K) f g (6 * K)).card := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hcD : Nat.card D = 32 * K := by simpa [card_additiveDomain] using hD
  obtain ⟨k, hk⟩ := hpow
  obtain ⟨H, hHD, hHc⟩ := exists_binary_subspace_card_eq D (16 * K)
    ⟨k + 4, by rw [hk, pow_add]; ring⟩ (by omega)
  have hH : (additiveDomain H).card = 16 * K := by rw [card_additiveDomain, hHc]
  have hseed := quadratic_near_johnson_same_field H K hK ⟨k, hk⟩ hH
  dsimp only at hseed
  obtain ⟨θ, -, hcount⟩ := hseed
  -- Choose the padding set outside the seed subspace.
  have hsub : additiveDomain H ⊆ additiveDomain D := by
    intro x hx
    exact (mem_additiveDomain D x).mpr (hHD ((mem_additiveDomain H x).mp hx))
  have hw : 2 * K + 1 ≤ (additiveDomain D \ additiveDomain H).card := by
    rw [Finset.card_sdiff_of_subset hsub, hD, hH]
    omega
  obtain ⟨W, hW, hWcard⟩ := Finset.exists_subset_card_eq hw
  have hWD : W ⊆ additiveDomain D := hW.trans Finset.sdiff_subset
  have hdis : Disjoint W (additiveDomain H) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxH
    exact (Finset.mem_sdiff.mp (hW hx)).2 hxH
  let src : F → F := fun x => x ^ (8 * K - 1) + θ * x ^ (4 * K - 1)
  let G : F[X] := X ^ (2 * K - 1)
  have hG : G.Monic := monic_X_pow _
  have hdeg : G.natDegree = 2 * K - 1 := natDegree_X_pow _
  have hdim : W.card + (2 * K - 1) = 4 * K := by rw [hWcard]; omega
  have hthr : W.card + (4 * K - 1) = 6 * K := by rw [hWcard]; omega
  have hp := nodal_padded_pair_guarantees (additiveDomain D) (additiveDomain H) W hsub hWD hdis
    (2 * K - 1) (4 * K - 1) (by rw [hdim, hD]; omega) src G hG hdeg
  dsimp only at hp
  rw [hdim, hthr] at hp
  -- The padded pair, as functions on the field, and its translate.
  let L : F[X] := Lagrange.nodal W id
  let f0 : F → F := fun x => L.eval x * src x
  let g0 : F → F := fun x => (L * G).eval x
  let P : F[X] := (L * G).comp (X - C a)
  have hPdeg : P.natDegree = 4 * K := by
    rw [natDegree_comp, natDegree_X_sub_C, mul_one,
      natDegree_mul Lagrange.nodal_ne_zero hG.ne_zero, Lagrange.natDegree_nodal, hdeg, hdim]
  have hPne : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hPdeg
    omega
  have hcardE : (affineDomain (additiveDomain D) a).card = 32 * K := by
    rw [card_affineDomain, hD]
  have hfun : (fun x : affineDomain (additiveDomain D) a => P.eval (x : F)) =
      fun x : affineDomain (additiveDomain D) a => g0 ((x : F) - a) := by
    funext x
    simp [P, g0]
  have hc := commonAgreementEQ_polynomial_right (affineDomain (additiveDomain D) a) (4 * K)
    (by rw [hcardE]; omega) (fun x => f0 ((x : F) - a)) P hPne hPdeg
  have hg := agreementLE_polynomial (affineDomain (additiveDomain D) a) (4 * K) P
    (by rw [degree_eq_natDegree hPne, hPdeg])
  rw [hPdeg] at hg
  rw [hfun] at hc hg
  refine ⟨fun x => f0 ((x : F) - a), fun x => g0 ((x : F) - a), hc,
    ⟨agreementGE_right_of_common _ _ _ _ _ hc.1, hg⟩, ?_⟩
  · rw [badChallenges_affineDomain (additiveDomain D) a f0 g0 (4 * K) (6 * K)]
    refine ((le_max_right _ _).trans hcount).trans (le_trans ?_ hp.2.1)
    apply Finset.card_le_card
    have hmono := badChallenges_dimension_mono (additiveDomain H) K (2 * K - 1) (4 * K - 1)
      (by omega) (fun x => src (x : F)) (fun x => G.eval (x : F))
    simpa [src, G] using hmono

/-- The count of Corollary 4.6 at `N = 2^20` and `q = 2^64`. -/
theorem rate_eighth_finite_count :
    let M : ℕ := (16 * 2 ^ 15 - 1) * (16 * 2 ^ 15 - 2) / 6
    let q : ℕ := 2 ^ 64
    ⌈(q : ℚ) * M / (q + M - 1)⌉₊ = 45812722234 := by
  dsimp only
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor <;> norm_num

end BinaryFieldCounterexamples
