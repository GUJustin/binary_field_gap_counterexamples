/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Essential
public import BinaryFieldCounterexamples.BooleanFunctions.HeightTwoQuotient
/-!
# Intrinsic binary tree functions

This module follows Definition 6.3 (tree functions) in the paper's Section 6.2,
`sections/constructions/additive-support-trees.tex`. At heights at least three,
the root functional, its two affine slices, and the disjoint essential dual
spaces of the children are literal data in the predicate.

At height two the definition literally requires balance, degree two, and
essential dimension three. The equivalent degree-free form remains available
as `isHeightTwoTree_iff_balanced_essentialDimension`.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees

/-- Exact balance: both binary values occur on half the finite domain. -/
def IsBalanced {U : Type*} (φ : U → ZMod 2) : Prop :=
  ∀ b : ZMod 2, 2 * Nat.card {x : U // φ x = b} = Nat.card U

/-- Over the binary alphabet, exact balance is equivalent to having ones on
half the domain, expressed without natural division. -/
theorem isBalanced_iff_twice_support {U : Type*} [Finite U] (φ : U → ZMod 2) :
    IsBalanced φ ↔ 2*Nat.card {x : U // φ x=1}=Nat.card U := by
  classical
  letI : Fintype U := Fintype.ofFinite _
  have hp := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : U => φ x=1)
  have hz : ∀ b : ZMod 2, b≠1 ↔ b=0 := by decide
  simp only [hz, Finset.card_univ] at hp
  constructor
  · intro h
    exact h 1
  · intro h b
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h ⊢
    rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) b with rfl | rfl
    · omega
    · exact h

/-- The height-two clause of Definition 6.3: balance, degree two, and
essential dimension three, with degree computed from the reduced ANF. -/
def IsHeightTwoTree {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Finite U] (φ : U → ZMod 2) : Prop :=
  IsBalanced φ ∧ BooleanFunctions.vectorDegree φ = 2 ∧ essentialDimension φ = 3

/-- Definition 6.3 at height two, exposed without unfolding the predicate. -/
theorem isHeightTwoTree_iff_balanced_degree_essentialDimension {U : Type*}
    [AddCommGroup U] [Module (ZMod 2) U] [Finite U] (φ : U → ZMod 2) :
    IsHeightTwoTree φ ↔ IsBalanced φ ∧ BooleanFunctions.vectorDegree φ=2 ∧
      essentialDimension φ=3 := by rfl

/-- The old degree-free height-two form is equivalent to the paper definition.
The essential quotient has dimension three; balance eliminates its cubic term. -/
theorem isHeightTwoTree_iff_balanced_essentialDimension {U : Type*}
    [AddCommGroup U] [Module (ZMod 2) U] [Finite U] (φ : U → ZMod 2) :
    IsHeightTwoTree φ ↔ IsBalanced φ ∧ essentialDimension φ = 3 := by
  constructor
  · rintro ⟨hb, _, hd⟩
    exact ⟨hb, hd⟩
  · rintro ⟨hb, hd⟩
    refine ⟨hb, ?_, hd⟩
    apply BooleanFunctions.vectorDegree_eq_two_of_balanced_essential_dimension_three φ
    · have h := hb 1
      omega
    · rwa [← essentialDimension_eq_finrank_quotient_periodSubmodule]

/-- The paper's intrinsic recursive tree predicate, indexed by the actual
height. Heights below two have no tree functions. For height `h+3`, the children
have height `h+2`; their prescribed essential spaces have dimension
`2^(h+2)-1` and intersect trivially in the dual of the root kernel. -/
def IsTreeFunction : (h : ℕ) → {U : Type*} → [AddCommGroup U] →
    [Module (ZMod 2) U] → [Finite U] → (U → ZMod 2) → Prop
  | 0, _, _, _, _, _ => False
  | 1, _, _, _, _, _ => False
  | 2, _, _, _, _, φ => IsHeightTwoTree φ
  | h + 3, U, _, _, _, φ =>
      ∃ (s : Module.Dual (ZMod 2) U), s ≠ 0 ∧
      ∃ p : U, s p = 1 ∧
      ∃ L₀ L₁ : Submodule (ZMod 2) (Module.Dual (ZMod 2) s.ker),
        Module.finrank (ZMod 2) L₀ = 2^(h+2)-1 ∧
        Module.finrank (ZMod 2) L₁ = 2^(h+2)-1 ∧
        L₀ ⊓ L₁ = ⊥ ∧
        IsTreeFunction (h+2) (fun x : s.ker => φ x) ∧
        essentialDualSpace (fun x : s.ker => φ x) = L₀ ∧
        IsTreeFunction (h+2) (fun x : s.ker => φ (p + x)) ∧
        essentialDualSpace (fun x : s.ker => φ (p + x)) = L₁

@[simp] theorem isTreeFunction_zero {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (φ : U → ZMod 2) : ¬ IsTreeFunction 0 φ := by simp [IsTreeFunction]

@[simp] theorem isTreeFunction_one {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (φ : U → ZMod 2) : ¬ IsTreeFunction 1 φ := by simp [IsTreeFunction]

/-- The actual-height recursion starts with the isolated height-two predicate. -/
@[simp] theorem isTreeFunction_two {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (φ : U → ZMod 2) : IsTreeFunction 2 φ ↔ IsHeightTwoTree φ := by rfl

/-- No intrinsic tree is indexed by a height below two. -/
theorem IsTreeFunction.two_le {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    {h : ℕ} {φ : U → ZMod 2} (hφ : IsTreeFunction h φ) : 2 ≤ h := by
  cases h with
  | zero => exact False.elim hφ
  | succ h => cases h with
    | zero => exact False.elim hφ
    | succ h => omega

end BinaryFieldCounterexamples.Trees
