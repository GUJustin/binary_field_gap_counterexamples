/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.AffineTransport
public import BinaryFieldCounterexamples.Agreement.Interpolation
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.Exclusions
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.BadSet

/-!
# Main theorem: Exact half agreement with exactly 2N−2 exceptional challenges

## Manuscript statement and status

Paper statement: [Theorem 4.7, p. 35](../../../binary-field-counterexamples.pdf#page=35).
Public theorem: `BinaryFieldCounterexamples.exact_half_agreement`.
**Proved.** The original full statement is verified without transitive admissions.

Let `F` be a finite field of characteristic two and `D ⊊ F` an affine binary
space of size `N = 2^d`, with `d ≥ 3`. Put `K = N/4`. There is one pair over
the input/challenge field `F` with

`CA_K(f,g) = agr_K(g) = K`, `agr_K(f) ≤ 3 N/8 - 1`, and
`|Bad_(N/2)(f,g)| = 2 N - 2`.

All exceptional challenges are nonzero. If `|F| = 2 N`, then for some `s ≠ 0`,
`Bad_(N/2)(f,g) = F \ {0,s}`, so exceptional probability is exactly `1 - 1/N`.
This is an equality for the entire exceptional set, not just a lower bound from the
constructed hyperplanes. The domain is proper but need not be a hyperplane
unless the additional field-size equality holds. All code degrees are `< K`.

This elementary construction supplies an exact benchmark and the small-exponent
case of the fixed-threshold counterexample. Its proof uses locators, the
inputs of Lemma 3.13, and root bounds.
-/

/-!
## Proof assembly: 1. Normalize the input pair outside a pole

Choose `β ∈ F \ D`, put `L = L_D`, `λ = L'`,
`R = sqrt(L - λ X)`, and `S = R + sqrt(λ β)`.
Set `f(x) = S(x)/(x - β)` and `g(x) = 1/(x - β)`.
Prove the polynomial square roots exist in this binary finite-field setting.
Use [Lemma 3.13, p. 24](../../../binary-field-counterexamples.pdf#page=24), reciprocal agreement, and interpolation to obtain
the claimed individual and common agreements in the shared ArkLib interface.
-/

/-!
## Proof assembly: 2. Construct all affine-hyperplane challenges

For an affine hyperplane `H ⊆ D`, set `z_H = P_H(β) - S(β)` using its monic
locator. The polynomial `(S + z_H - P_H)/(X - β)` has degree at most `K - 1`
and agrees exactly on `H`. Prove divisibility before forming the quotient.
Parallel locators differ by a nonzero constant; nonparallel ones have `K`
common roots. Use these two cases to establish distinctness of all `2 N - 2`
challenges. Exclude zero using the first-input agreement bound.
-/

/-!
## Proof assembly: 3. Exclude any additional exceptional challenges

For an arbitrary strict-degree witness `h`, its residual numerator
`A = S + z - (X - β) h` is monic of degree `N/2`. At agreement `N/2` it
splits into distinct roots in `D`, hence divides `L`. Show `A² - L = c A`
by degree and divisibility, and `c ≠ 0` by differentiating. Coefficient
comparison then forces `A` to be affine binary linearized, so its roots form
an affine hyperplane and its challenge is already among the constructed challenges.
Only after this upper bound may the exceptional-set cardinality be stated as equality.
Set `s = S(β) = sqrt(L(β)) ≠ 0` and show it cannot be a hyperplane challenge,
since `P_H(β) ≠ 0`. When `|F| = 2 N`, counting identifies the whole complement
as `{0,s}` and gives the exact probability.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- Theorem 4.7: the entire exceptional set has exactly `2 N - 2` elements.
The final conditional identifies the set, rather than merely its cardinality. -/
theorem exact_half_agreement
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (a : F) (d : ℕ) (hd : 3 ≤ d)
    (hD : (additiveDomain D).card = 2 ^ d) (hproper : 2 ^ d < Fintype.card F) :
    let E := affineDomain (additiveDomain D) a
    let N : ℕ := 2 ^ d
    let K : ℕ := N / 4
    ∃ f g : E → F,
      commonAgreementEQ E K f g K ∧ agreementEQ E K g K ∧
      agreementLE E K f (3 * N / 8 - 1) ∧
      (badChallenges E K f g (N / 2)).card = 2 * N - 2 ∧
      0 ∉ badChallenges E K f g (N / 2) ∧
      (Fintype.card F = 2 * N → ∃ s : F, s ≠ 0 ∧
        ∀ z : F, z ∈ badChallenges E K f g (N / 2) ↔ z ≠ 0 ∧ z ≠ s) := by
  classical
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Fintype D := Fintype.ofFinite D
  -- Fix the quarter-rate parameters and one exterior pole before all challenges.
  let K := 2^(d-2)
  have hN : 2^d=4*K := by
    calc
      2^d=2^((d-2)+2) := by congr 1; omega
      _=4*K := by dsimp [K]; rw [pow_add]; ring
  have hK : 2 ≤ K := by
    have hh : 1 ≤ d-2 := by omega
    have := Nat.pow_le_pow_right (by decide : 0<2) hh
    simpa [K] using this
  have hpow : ∃k : ℕ, K=2^k := ⟨d-2,rfl⟩
  have hKdef : 2^d/4=K := by rw [hN]; omega
  have hhalf : 2^d/2=2*K := by rw [hN]; omega
  have hfthreshold : 3*2^d/8-1=3*K/2-1 := by rw [hN]; omega
  have hcD : Fintype.card D=4*K := by
    rw [card_additiveDomain, Nat.card_eq_fintype_card] at hD
    exact hD.trans hN
  obtain ⟨β,hβ⟩ : ∃β : F, β ∉ D := by
    by_contra h
    have hall : ∀β : F, β ∈ additiveDomain D := by
      intro β
      exact (mem_additiveDomain D β).mpr (by simpa using not_not.mp (fun hn => h ⟨β,hn⟩))
    have he : additiveDomain D=Finset.univ := Finset.eq_univ_of_forall hall
    rw [he, Finset.card_univ] at hD
    omega
  let E := affineDomain (additiveDomain D) a
  let f0 : F → F := fun x => (binaryQuarterNumerator D β).eval x*(x-β)⁻¹
  let g0 : F → F := fun x => (x-β)⁻¹
  let f : E → F := fun x => f0 ((x : F)-a)
  let g : E → F := fun x => g0 ((x : F)-a)
  have hβE : β+a ∉ E := by
    intro h
    rw [mem_affineDomain_iff, add_sub_cancel_right, mem_additiveDomain] at h
    exact hβ h
  have hgform : g = fun x : E => ((x : F)-(β+a))⁻¹ := by
    funext x
    dsimp [g,g0]
    congr 1
    ring
  have hKcard : K ≤ E.card := by
    dsimp [E]
    rw [card_affineDomain,hD,hN]
    omega
  -- The same translated pair keeps exact common and second-input agreement.
  have hcommon : commonAgreementEQ E K f g K := by
    rw [hgform]
    exact commonAgreementEQ_reciprocal_right E (β+a) hβE K hKcard f
  have hg : agreementEQ E K g K := by
    rw [hgform]
    exact agreementEQ_reciprocal E (β+a) hβE K hKcard
  have hf : agreementLE E K f (3*K/2-1) := by
    exact agreementLE_affineDomain (additiveDomain D) a f0 K _
      (agreementLE_binaryQuarterSource D β hβ K hK hpow hcD)
  have hbad : badChallenges E K f g (2*K) =
      badChallenges (additiveDomain D) K (fun x => f0 x) (fun x => g0 x) (2*K) :=
    badChallenges_affineDomain (additiveDomain D) a f0 g0 K (2*K)
  -- The hyperplane classification counts the entire exceptional set, in both directions.
  have hcount : (badChallenges E K f g (2*K)).card=2*2^d-2 := by
    rw [hbad]
    rw [ExactHalf.card_binaryQuarter_badChallenges D β hβ K hK hcD,
      Nat.card_eq_fintype_card, hcD, ← hN]
    omega
  obtain ⟨hzero,hsbad⟩ := binaryQuarterSource_excluded_challenges D β hβ K hK hpow hcD
  change 0 ∉ badChallenges (additiveDomain D) K (fun x => f0 x) (fun x => g0 x) (2*K) at hzero
  have hzeroE : 0 ∉ badChallenges E K f g (2*K) := by rwa [hbad]
  let s := (binaryQuarterNumerator D β).eval β
  have hs : s ≠ 0 := binaryQuarterNumerator_eval_pole_ne_zero D β hβ
  have hsE : s ∉ badChallenges E K f g (2*K) := by rw [hbad]; exact hsbad
  dsimp only
  rw [hKdef,hhalf,hfthreshold]
  refine ⟨f,g,hcommon,hg,hf,hcount,hzeroE,?_⟩
  -- At index two, the two excluded challenges exhaust the complement.
  intro hq
  refine ⟨s,hs,?_⟩
  let C := (Finset.univ : Finset F).erase 0 |>.erase s
  have hsub : badChallenges E K f g (2*K) ⊆ C := by
    intro z hz
    simp only [C, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun he => hsE (he ▸ hz), fun he => hzeroE (he ▸ hz)⟩
  have hC : C.card=Fintype.card F-2 := by
    simp [C, Finset.card_erase_of_mem, hs]
    omega
  have heq : badChallenges E K f g (2*K)=C := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hC,hcount,hq]
  intro z
  rw [heq]
  simp [C, and_comm]

end BinaryFieldCounterexamples
