/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.SourceBound
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.Witnesses
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.Labels
public import BinaryFieldCounterexamples.Polynomial.Map

/-!
# Main theorem: Quadratically many exceptions on every binary additive domain

## Manuscript statement and status

The September 21 paper revision strengthens Theorem 4.1 to an exact
classification above 2K agreements. This file proves the earlier lower-bound
contract only; the full exact classification and absence of further challenges are
proved in the companion `QuadraticNearJohnsonExact.lean`.

Paper statement: [Theorem 4.1, p. 28](../../../binary-field-counterexamples.pdf#page=28).
Public theorem: `BinaryFieldCounterexamples.quadratic_near_johnson`.
**Verified proper-extension theorem.** The theorem below has a complete proof with
no transitive admissions. The stronger individual bound and same-field companions
are proved in `QuadraticNearJohnsonCompanions.lean`.

Let `B ⊊ F` be finite fields of characteristic two, and let `D ⊆ B` be an
additive subspace of size `N = 16 K`, where `K ≥ 2` is a power of two.
There exist received words `f,g : D → F` such that

* `CA_K(f,g) = 2 K - 1`;
* `agr_K(f) ≤ 2 K` and `agr_K(g) = 2 K - 1`; and
* at least `(N - 1)(N - 2)/6` distinct challenges `z ∈ F` have a polynomial
  `H_z ∈ F[X]` of degree strictly below `K` agreeing with `f + z g` on
  at least `4 K - 1` coordinates.

Thus the same challenges qualify at `T = N/4 - 3`, within a constant number
of coordinates below the finite Johnson threshold `sqrt(N (K - 1))`.
The paper additionally asserts a sharper bound when `[F:B] ≥ 3`; that separate
companion is proved in that separate module. The verified statement needs only a proper extension.

Here `agr_K` maximizes ordinary agreement over degree-`< K` polynomials;
`CA_K` maximizes simultaneous agreement with two such polynomials on the
same coordinates. The shared `PaperSemantics` definitions give these manuscript conventions
concrete polynomial-agreement semantics.
The exceptional count concerns challenge values for one fixed pair, not locator objects.

## Formalization boundary

`PaperSemantics` specializes ArkLib's agreement sets to polynomial evaluation.
Do not replace the target by a proposition with an assumed counterexample, or
declare an abstract agreement predicate whose intended meaning is unverified.
The product locator, binary coefficient support, Frobenius remainders, coordinate
projection, distinct-challenge count, and final assembly are all proved below this
module's public import closure. Collision averaging is not a dependency.
-/

/-!
## Proof assembly: 1. Choose one pair

Choose `θ ∈ F \ B` and start with `f₀ = X^(8 K - 1) + θ X^(4 K - 1)` and
`g = X^(2 K - 1)`, restricted to `D`. The same `θ` must serve every subspace. The final first
input is a shift `f = f₀ + s g`, chosen in stage 3; translating all
challenges by `s` preserves their distinct count. Develop the extension-coordinate
argument separately for the stronger `[F:B] ≥ 3` conclusion; do not silently
strengthen the initial field hypothesis.
-/

/-!
## Proof assembly: 2. Turn each subspace into a strict-degree witness

For each codimension-two subspace `W ≤ D`, its linearized locator has shape
`L_W = X^(4 K) + a_W X^(2 K) + b_W X^K + V_W`, with `deg V_W ≤ K/2`.
Set `z_W = a_W^3 + b_W^2 + θ a_W` and expand
`L_W² + (a_W² + θ) L_W`. Its low-degree remainder is divisible by `X`.
After division, the witness degree is strictly below `K` and agreement holds
on `W \ {0}`, giving `4 K - 1` coordinates. Divisibility, the removed zero
coordinate, and the zero-polynomial degree convention are handled by the
supporting locator and `divX` lemmas.
-/

/-!
## Proof assembly: 3. Count challenges and establish the common-agreement gap

Recover `a_W` and `b_W` from `z_W` using linear independence of `1, θ` over `B`.
Prove that these coefficients determine `W` by comparing locator degree with
the number of common roots. Then count codimension-two binary subspaces.
The degree of `g` bounds its agreement, and hence common agreement, by `2 K - 1`.
For the matching lower bound choose `U ≤ D` of size `2 K`. The remainders
`R₁,R₂,R₃` of `X^(2 K),X^(4 K),X^(8 K)` modulo `L_U` are additive, have zero
constant coefficient, and have degree at most `K`. Thus `R₁/X` and
`(R₃ + θ R₂)/X` have degree strictly below `K` and match `g,f₀` on `U \ {0}`.
Generic interpolation alone would only supply `K` common coordinates.

For the first-input bound, let `d₄` be the coefficient of `X^(4 K)` in `L_D`
and choose `s ∈ B` with `s²=d₄`. Projecting a hypothetical explaining polynomial onto
`1,θ` gives `A=Xp₀`, `Q=Xp₁`. More than `2K` agreement points force the
polynomial identity `Q²+A+sX^(2K)=0`. Squaring it shows directly that
`L_D+(X^(4K)+Q)^4+d₈(X^(4K)+Q)^2` has degree at most `2K` and vanishes
on the same points. Its nonzero locator derivative contradicts its forced
vanishing. This avoids a separate coefficient-extraction lemma.

Common agreement is preserved by the first-input shift, and translating every challenge
by the same scalar preserves its cardinality. The counting proof uses ordered
independent pairs in the binary dual and at most six presentations per
codimension-two kernel. It therefore needs no general Gaussian-binomial formula.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial QuadraticConstruction

/-- Theorem 4.1: every prescribed binary additive domain in a proper extension.
The field embedding and its nonsurjectivity state the proper-extension hypothesis. -/
theorem quadratic_near_johnson
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hproper : ¬ Function.Surjective φ)
    (D : AddSubgroup B) (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 16 * K) :
    let E := mappedDomain φ (additiveDomain D)
    ∃ f g : E → F,
      commonAgreementEQ E K f g (2 * K - 1) ∧
      agreementLE E K f (2 * K) ∧ agreementEQ E K g (2 * K - 1) ∧
      ((16 * K - 1) * (16 * K - 2) / 6) ≤
        (badChallenges E K f g (4 * K - 1)).card := by
  classical
  let : Algebra B F := φ.toAlgebra
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  -- Choose one exterior coordinate and one first-input shift for the entire family.
  have hθex : ∃ θ : F, θ ∉ Set.range φ := by
    simpa only [Function.Surjective, not_forall, Set.mem_range] using hproper
  obtain ⟨θ, hθ⟩ := hθex
  have hθ' : θ ∉ Set.range (algebraMap B F) := hθ
  obtain ⟨s, hs⟩ := exists_quadratic_source_shift D K (by omega) hpow hD θ hθ'
  let E := mappedDomain φ (additiveDomain D)
  let f : E → F := fun x ↦ firstWord K θ x + φ s * secondWord K (x : F)
  let g : E → F := fun x ↦ secondWord K (x : F)
  have hf : agreementLE E K f (2 * K) := hs
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
    commonAgreementGE_of_subgroup E UF hUFE K hpow hUFc θ (φ s)
  refine ⟨f, g, ⟨hcommon, commonAgreementLE_of_right E K f g _ hg⟩,
    hf, ⟨agreementGE_right_of_common E K f g _ hcommon, hg⟩, ?_⟩
  -- Count distinct challenges and transport every witness into the prescribed domain.
  let labels := (codimTwoBinarySubspaces D).image (finiteLocatorLabel φ θ K)
  have hlower : ((16 * K - 1) * (16 * K - 2) / 6) ≤ labels.card := by
    simpa only [hcD] using codimTwo_label_count_lower_bound φ θ hθ D K hK hpow hcD
  let shifted := labels.image (fun z ↦ z + φ s)
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
    have hbad := bad_challenge_of_subgroup E WF hWFE K hK hpow hWFc θ (φ s)
    simpa only [WF, coeff_subspacePolynomial_map, finiteLocatorLabel, locatorLabel,
      locatorCoeffA, locatorCoeffB, map_add, map_pow] using hbad
  exact hlower.trans (hshiftcard ▸ Finset.card_le_card hsubset)

end BinaryFieldCounterexamples
