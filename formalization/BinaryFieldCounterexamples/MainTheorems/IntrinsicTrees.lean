/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.HalfRateDecisionTrees
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.PaperCorollaries
/-!
# Main tree conclusions with intrinsic populations

Corollary 6.7 and Theorem 6.10 of
`sections/constructions/additive-support-trees.tex`, restated using the
intrinsic tree predicate from Definition 6.3. The population counts distinct
Boolean functions, equivalently distinct supports. The half-rate family
retains the paper's selected avoiding restriction.

On a domain of size `N = 2^d` in a larger challenge field of size `q`, the
whole family has population `B_h(d)`, agreement `N/2`, and message length
`N/2 - N/2^(h+1)`. The selected half-rate family has population `M_h(d)`,
message length `N/2`, and agreement `N/2 + N/2^(h+1)`. Both finite theorems
keep the maximum of the additive and second-moment image bounds, with their
respective rational collision energies. All five wrappers are proved.

For fixed height, the whole population grows as `N^(2^h-1)` and the selected
population as `N^(2^h-h-1)`. The asymptotic and probability wrappers choose
constants before the dimension, field, and prescribed domain; the selected
family restriction is retained in the actual-function count.
-/
@[expose] public section
attribute [local instance] Classical.decEq Classical.propDecidable
namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- The population in Corollary 6.7 is the number of intrinsic height-`h`
tree functions on the prescribed domain. -/
theorem half_agreement_trees_intrinsic
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (d h : ℕ) (hh : 2 ≤ h) (hd : 2^h-1 ≤ d)
    (hD : (additiveDomain D).card = 2^d) (hq : 2^d < Fintype.card F) :
    let N : ℕ := 2^d
    let T : ℕ := N/2
    let K : ℕ := N/2-N/2^(h+1)
    let M := Nat.card {φ : D → ZMod 2 // Trees.IsTreeFunction h φ}
    let E : ℚ := (K : ℚ)*M.choose 2-(N : ℚ)*(M/2).choose 2
    let A := additiveDomain D
    ∃ f g : A → F, commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
      agreementLE A K f (T-1) ∧
      max (M-⌊E/(Fintype.card F-N)⌋₊)
        ⌈(Fintype.card F-N : ℚ)*M^2/((Fintype.card F-N)*M+2*E)⌉₊ ≤
        (nonzeroBadChallenges A K f g T).card := by
  -- Recover the actual binary dimension from the prescribed domain size.
  have hDN : Nat.card D = 2^d := by rwa [card_additiveDomain] at hD
  have hdim : Module.finrank (ZMod 2) D = d := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hDN] at he
    simp only [Nat.card_eq_fintype_card, ZMod.card] at he
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) he.symm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hh
  have hcount := Trees.isTreeFunction_count (V := D) n (by rwa [hdim])
  rw [hdim] at hcount
  -- Substitute the intrinsic population into the unchanged finite formula.
  dsimp only
  rw [hcount]
  exact half_agreement_trees D d (n+2) (by omega) hd hD hq


/-- The canonical avoiding restriction, expressed as an intrinsic function
population, has the manuscript's exact half-rate support count. -/
theorem selectedIntrinsicTreeFunction_count_eq
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (h : ℕ) (hh : 2 ≤ h) (W : Submodule (ZMod 2) V)
    (hd : 2^h-1 ≤ Module.finrank (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) W+(h+1) = Module.finrank (ZMod 2) V) :
    Nat.card {φ : V → ZMod 2 // Trees.IsTreeFunction h φ ∧
      φ ∈ Trees.avoidingTreeFamily (h-2) W} =
        avoidingTreeSupportCount h (Module.finrank (ZMod 2) V) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hh
  rw [Nat.add_sub_cancel, Trees.selectedIntrinsicTreeFunction_count]
  exact Trees.avoidingTreeSupportFamily_card_eq n W hd (by simpa using hW)

/-- The population in Theorem 6.10 consists of intrinsic trees in the selected
canonical avoiding family; it is not the family of all trees vanishing on `W`. -/
theorem half_rate_decision_trees_intrinsic
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (d h : ℕ) (hh : 3 ≤ h) (hd : 2^h-1 ≤ d)
    (W : Submodule (ZMod 2) D)
    (hW : Module.finrank (ZMod 2) W+(h+1) = d)
    (hD : (additiveDomain D).card = 2^d) (hq : 2^d < Fintype.card F) :
    let N : ℕ := 2^d
    let K : ℕ := N/2
    let w : ℕ := N/2^(h+1)
    let M := Nat.card {φ : D → ZMod 2 // Trees.IsTreeFunction h φ ∧
      φ ∈ Trees.avoidingTreeFamily (h-2) W}
    let E : ℚ := (((K : ℚ)-w-(K : ℚ)^2/(N-w))*M^2+w*M)/2
    let A := additiveDomain D
    ∃ f g : A → F, commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
      agreementLE A K f (K+w-1) ∧
      max (M-⌊E/(Fintype.card F-N)⌋₊)
        ⌈(Fintype.card F-N : ℚ)*M^2/((Fintype.card F-N)*M+2*E)⌉₊ ≤
        (nonzeroBadChallenges A K f g (K+w)).card := by
  -- Recover the actual binary dimension from the prescribed domain size.
  have hDN : Nat.card D = 2^d := by rwa [card_additiveDomain] at hD
  have hdim : Module.finrank (ZMod 2) D = d := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hDN] at he
    simp only [Nat.card_eq_fintype_card, ZMod.card] at he
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) he.symm
  have hc := selectedIntrinsicTreeFunction_count_eq h (by omega) W
    (by rwa [hdim]) (by rwa [hdim])
  rw [hdim] at hc
  -- The selected intrinsic population is exactly the original counted family.
  dsimp only
  rw [hc]
  exact half_rate_decision_trees D d h (by omega) hd hD hq

/-- Theorem 6.10's support asymptotics, with its selected population counted
as distinct intrinsic functions on every binary space of dimension `d`. -/
theorem half_rate_support_count_asymptotic_intrinsic (h : ℕ) (hh : 3 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀ ≤ d → 2^h-1 ≤ d →
      ∀ (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V],
      Module.finrank (ZMod 2) V = d →
      ∀ W : Submodule (ZMod 2) V, Module.finrank (ZMod 2) W+(h+1) = d →
        let M := Nat.card {φ : V → ZMod 2 // Trees.IsTreeFunction h φ ∧
          φ ∈ Trees.avoidingTreeFamily (h-2) W}
        c * (2^d : ℝ)^(2^h-h-1) ≤ M ∧
        (M : ℝ) ≤ C * (2^d : ℝ)^(2^h-h-1) := by
  obtain ⟨c, C, hc, hC, d₀, hb⟩ := half_rate_support_count_asymptotic h hh
  refine ⟨c, C, hc, hC, d₀, ?_⟩
  intro d hd₀ hd V _ _ _ hdim W hW
  dsimp only
  rw [selectedIntrinsicTreeFunction_count_eq h (by omega) W
    (by rwa [hdim]) (by rwa [hdim]), hdim]
  exact hb d hd₀ hd

/-- Corollary 6.7's fixed-height count consequence, together with the exact
intrinsic population supplying its supports. The pair has the same common
and individual agreement guarantees as the existing main theorem. -/
theorem half_agreement_trees_asymptotic_intrinsic (h : ℕ) (hh : 2 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀ ≤ d → 2^h-1 ≤ d →
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (D : AddSubgroup F) [Fintype D],
        (additiveDomain D).card = 2^d → 2^d < Fintype.card F →
        let A := additiveDomain D
        let N : ℕ := 2^d
        let K : ℕ := N/2-N/2^(h+1)
        Nat.card {φ : D → ZMod 2 // Trees.IsTreeFunction h φ} = treeSupportCount h d ∧
        ∃ f g : A → F,
          commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
          agreementLE A K f (N/2-1) ∧
          c * min ((N : ℝ)^(2^h-1)) ((Fintype.card F : ℝ)/N) ≤
            ((nonzeroBadChallenges A K f g (N/2)).card : ℝ) := by
  obtain ⟨c, hc, d₀, hb⟩ := half_agreement_trees_asymptotic h hh
  refine ⟨c, hc, d₀, ?_⟩
  intro d hd₀ hd F _ _ _ _ D _ hD hq
  dsimp only
  constructor
  · have hDN : Nat.card D = 2^d := by rwa [card_additiveDomain] at hD
    have hdim : Module.finrank (ZMod 2) D = d := by
      have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
      rw [hDN] at he
      simp only [Nat.card_eq_fintype_card, ZMod.card] at he
      exact Nat.pow_right_injective (by decide : 2 ≤ 2) he.symm
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hh
    simpa only [hdim] using Trees.isTreeFunction_count (V := D) n (by rwa [hdim])
  · exact hb d hd₀ hd F D hD hq

/-- Theorem 6.10's uniform probability consequence, retaining an intrinsic
selected-population identity on every admissible padding subspace. -/
theorem half_rate_decision_trees_probability_intrinsic (h : ℕ) (hh : 3 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀ ≤ d → 2^h-1 ≤ d →
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (D : AddSubgroup F) [Fintype D],
        (additiveDomain D).card = 2^d → 2^d < Fintype.card F →
        let A := additiveDomain D
        let N : ℕ := 2^d
        let q : ℕ := Fintype.card F
        let K : ℕ := N/2
        ∃ f g : A → F,
          commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
          agreementLE A K f (K+N/2^(h+1)-1) ∧
          c * min ((N : ℝ)^(2^h-h-1)/q) (1/N) ≤
            ((nonzeroBadChallenges A K f g (K+N/2^(h+1))).card : ℝ)/q ∧
          ∀ W : Submodule (ZMod 2) D, Module.finrank (ZMod 2) W+(h+1) = d →
            let M := Nat.card {φ : D → ZMod 2 // Trees.IsTreeFunction h φ ∧
              φ ∈ Trees.avoidingTreeFamily (h-2) W}
            N*M ≤ q → c*M ≤
              ((nonzeroBadChallenges A K f g (K+N/2^(h+1))).card : ℝ) := by
  obtain ⟨c, hc, d₀, hb⟩ := half_rate_decision_trees_probability h (by omega)
  refine ⟨c, hc, d₀, ?_⟩
  intro d hd₀ hd F _ _ _ _ D _ hD hq
  obtain ⟨f, g, hcommon, hagree, hf, hp, hlarge⟩ := hb d hd₀ hd F D hD hq
  refine ⟨f, g, hcommon, hagree, hf, hp, ?_⟩
  intro W hW
  -- Recover the actual binary dimension from the prescribed domain size.
  have hDN : Nat.card D = 2^d := by rwa [card_additiveDomain] at hD
  have hdim : Module.finrank (ZMod 2) D = d := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hDN] at he
    simp only [Nat.card_eq_fintype_card, ZMod.card] at he
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) he.symm
  dsimp only
  rw [selectedIntrinsicTreeFunction_count_eq h (by omega) W
    (by rwa [hdim]) (by rwa [hdim]), hdim]
  exact hlarge

end BinaryFieldCounterexamples
