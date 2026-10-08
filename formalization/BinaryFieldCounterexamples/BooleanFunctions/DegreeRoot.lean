/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.BooleanFunctions.DegreeBlocks
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeSelector
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeCharacterization

/-!
# Root separation for arbitrary independent Boolean children

This is the degree characterization in Lemma 6.5 (Section 6.2), proved by the
paper's leading-monomial argument. In coordinates `s,x,y,z`, the branch is
`(1+s) f(x) + s g(y)` and a linear form is `a s + u(x) + v(y) + c(z)`.
For arbitrary children of exact degree `k ≥ 2`, a product of degree at most
`k+1` forces `u=v=c=0`. No tree predicate or period-count argument is assumed.
-/

@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions

open MvPolynomial BigOperators
variable {σ τ ζ : Type*} [Fintype σ] [Fintype τ] [Fintype ζ]

/-- The ANF of a genuine linear scalar map is homogeneous of degree one,
including the zero map. -/
theorem anf_linear_isHomogeneous (u : (σ → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    (anf u).IsHomogeneous 1 := by
  classical
  have hp := polynomial_eq_affine_of_totalDegree_le_one (anf u) (degree_affine_le u.toAffineMap)
  have hz : (anf u).coeff 0 = 0 := by
    simpa only [eval_zero, constantCoeff_eq, map_zero] using anf_eval u 0
  rw [hz, C_0, zero_add] at hp
  rw [hp]
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

/-- Polynomial version of the root-degree implication, retaining lower-degree
child terms and performing Boolean reduction before measuring degree. -/
theorem root_polynomial_separation
    (p₀ u : MvPolynomial σ (ZMod 2)) (p₁ v : MvPolynomial τ (ZMod 2))
    (c : MvPolynomial ζ (ZMod 2)) (a : ZMod 2) {k : ℕ} (hk : 2 ≤ k)
    (h₀ : p₀.totalDegree = k) (h₁ : p₁.totalDegree = k)
    (hu : u.IsHomogeneous 1) (hv : v.IsHomogeneous 1) (hc : c.IsHomogeneous 1)
    (hr₀ : p₀ ∈ restrictDegree σ (ZMod 2) 1) (hr₁ : p₁ ∈ restrictDegree τ (ZMod 2) 1)
    (hprod : (reduction
      (selectorLinearPolynomial a (rename blockX u + rename blockY v + rename blockZ c) *
        selectorBranchPolynomial (rename blockX p₀) (rename blockY p₁))).totalDegree ≤ k + 1) :
    u = 0 ∧ v = 0 ∧ c = 0 := by
  have hr : (rename (blockX : σ → BlockVariables σ τ ζ) u +
      rename blockY v + rename blockZ c).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      exact max_le ((totalDegree_rename_le _ _).trans hu.totalDegree_le)
        ((totalDegree_rename_le _ _).trans hv.totalDegree_le)
    · exact (totalDegree_rename_le _ _).trans hc.totalDegree_le
  have hz := homogeneousComponent_selector_product_eq_zero a _ _ _ (by omega) hr
    ((totalDegree_rename_le _ p₀).trans h₀.le)
    ((totalDegree_rename_le _ p₁).trans h₁.le) hprod
  rw [map_add, ← rename_homogeneousComponent, ← rename_homogeneousComponent] at hz
  exact root_top_block_separation (homogeneousComponent k p₀) u
    (homogeneousComponent k p₁) v c hk
    (homogeneousComponent_isHomogeneous _ _) (homogeneousComponent_isHomogeneous _ _)
    (homogeneousComponent_top_ne_zero p₀ (by omega) h₀)
    (homogeneousComponent_top_ne_zero p₁ (by omega) h₁) hu hv hc
    (homogeneousComponent_mem_restrictDegree _ _ _ hr₀)
    (homogeneousComponent_mem_restrictDegree _ _ _ hr₁) hz

/-- Branch in independent `s,x,y,z` coordinates; the unused block is explicit. -/
def blockBranchFunction (f : (σ → ZMod 2) → ZMod 2) (g : (τ → ZMod 2) → ZMod 2)
    (w : Option (BlockVariables σ τ ζ) → ZMod 2) : ZMod 2 :=
  (1 + w none) * f (fun i => w (some (blockX i))) +
    w none * g (fun i => w (some (blockY i)))

/-- A genuine linear form split into its selector and three coordinate blocks. -/
def blockLinearFunction (a : ZMod 2)
    (u : (σ → ZMod 2) →ₗ[ZMod 2] ZMod 2) (v : (τ → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (c : (ζ → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w : Option (BlockVariables σ τ ζ) → ZMod 2) : ZMod 2 :=
  a * w none + u (fun i => w (some (blockX i))) +
    v (fun i => w (some (blockY i))) + c (fun i => w (some (blockZ i)))

/-- The `z` coordinates can be adjoined to a child without changing its ANF. -/
theorem anf_ignore_unused_block (g : (τ → ZMod 2) → ZMod 2) :
    anf (fun y : (τ ⊕ ζ) → ZMod 2 => g (fun i => y (Sum.inl i))) =
      rename Sum.inl (anf g) := by
  apply anf_unique
  · exact rename_mem_restrictDegree _ Sum.inl_injective _ (anf_mem_restrictDegree g)
  · intro y
    simp [eval_rename, Function.comp_def]

/-- Adjoining unused coordinates preserves the child's degree. -/
theorem degree_ignore_unused_block (g : (τ → ZMod 2) → ZMod 2) :
    degree (fun y : (τ ⊕ ζ) → ZMod 2 => g (fun i => y (Sum.inl i))) = degree g := by
  rw [degree, anf_ignore_unused_block]
  exact totalDegree_rename_injective _ Sum.inl_injective _

/-- Equation `eq:tree-coordinates` has degree `k+1` even with an explicit unused
`z` block. The first child has exact degree `k>0`; the second has degree at most `k`. -/
theorem degree_blockBranchFunction (f : (σ → ZMod 2) → ZMod 2)
    (g : (τ → ZMod 2) → ZMod 2) {k : ℕ} (hk : 0 < k)
    (hf : degree f = k) (hg : degree g ≤ k) :
    degree (blockBranchFunction (ζ := ζ) f g) = k + 1 := by
  have he : blockBranchFunction (ζ := ζ) f g = branchFunction f
      (fun y : (τ ⊕ ζ) → ZMod 2 => g (fun i => y (Sum.inl i))) := rfl
  rw [he]
  apply degree_branchFunction f _ hk hf
  rw [degree_ignore_unused_block]
  exact hg

/-- The leading part in `s,x,y,z` is `s(Ω₀+Ω₁)`, with no unused-block terms. -/
theorem topPart_blockBranchFunction (f : (σ → ZMod 2) → ZMod 2)
    (g : (τ → ZMod 2) → ZMod 2) {k : ℕ} (hf : degree f ≤ k) :
    homogeneousComponent (k + 1) (anf (blockBranchFunction (ζ := ζ) f g)) =
      X none * (rename (some ∘ blockX) (homogeneousComponent k (anf f)) +
        rename (some ∘ blockY) (homogeneousComponent k (anf g))) := by
  change homogeneousComponent (k + 1) (anf (branchFunction f
    (fun y : (τ ⊕ ζ) → ZMod 2 => g (fun i => y (Sum.inl i))))) = _
  rw [topPart_branchFunction f _ hf, anf_ignore_unused_block, ← rename_homogeneousComponent,
    rename_rename]
  rfl

/-- Multiplication by the selector retains only the selected child; its degree
is at most `k+1`, including in the presence of arbitrary unused coordinates. -/
theorem degree_selector_mul_blockBranchFunction (f : (σ → ZMod 2) → ZMod 2)
    (g : (τ → ZMod 2) → ZMod 2) {k : ℕ} (hg : degree g ≤ k) :
    degree ((fun w : Option (BlockVariables σ τ ζ) → ZMod 2 => w none) *
      blockBranchFunction f g) ≤ k + 1 := by
  change degree ((fun w : Option (σ ⊕ (τ ⊕ ζ)) → ZMod 2 => w none) * branchFunction f
    (fun y : (τ ⊕ ζ) → ZMod 2 => g (fun i => y (Sum.inl i)))) ≤ k + 1
  apply degree_selector_mul_branchFunction
  rw [degree_ignore_unused_block]
  exact hg

/-- The function-level product is represented by the reduced selector polynomial
product, including all lower-degree child terms. -/
theorem anf_blockLinear_mul_blockBranch
    (f : (σ → ZMod 2) → ZMod 2) (g : (τ → ZMod 2) → ZMod 2) (a : ZMod 2)
    (u : (σ → ZMod 2) →ₗ[ZMod 2] ZMod 2) (v : (τ → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (c : (ζ → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    anf (blockLinearFunction a u v c * blockBranchFunction f g) =
      reduction (selectorLinearPolynomial a
        (rename blockX (anf u) + rename blockY (anf v) + rename blockZ (anf c)) *
        selectorBranchPolynomial (rename blockX (anf f)) (rename blockY (anf g))) := by
  unfold reduction
  congr 1
  funext w
  simp only [Pi.mul_apply, selectorLinearPolynomial, selectorBranchPolynomial,
    eval_mul, eval_add, eval_C, eval_X, eval_rename, anf_eval, Function.comp_def,
    blockLinearFunction, blockBranchFunction]
  ring

/-- The monomial-type argument of Lemma 6.5 for arbitrary exact-degree children.
For `k≥2`, the only surviving linear form is a multiple of the selector. -/
theorem root_degree_forces_blocks_zero
    (f : (σ → ZMod 2) → ZMod 2) (g : (τ → ZMod 2) → ZMod 2) (a : ZMod 2)
    (u : (σ → ZMod 2) →ₗ[ZMod 2] ZMod 2) (v : (τ → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (c : (ζ → ZMod 2) →ₗ[ZMod 2] ZMod 2) {k : ℕ} (hk : 2 ≤ k)
    (hf : degree f = k) (hg : degree g = k)
    (hprod : degree (blockLinearFunction a u v c * blockBranchFunction f g) ≤ k + 1) :
    u = 0 ∧ v = 0 ∧ c = 0 := by
  rw [degree, anf_blockLinear_mul_blockBranch] at hprod
  obtain ⟨hu, hv, hc⟩ := root_polynomial_separation (anf f) (anf u) (anf g) (anf v) (anf c) a hk
    hf hg (anf_linear_isHomogeneous u) (anf_linear_isHomogeneous v) (anf_linear_isHomogeneous c)
    (anf_mem_restrictDegree f) (anf_mem_restrictDegree g) hprod
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simpa using congrArg (eval x) hu
  · ext x
    simpa using congrArg (eval x) hv
  · ext x
    simpa using congrArg (eval x) hc

/-- Among nonzero linear forms, the root selector is exactly the one whose
product with this branch has degree at most `k+1`. This packages both directions
of the degree characterization used in Lemma 6.5, for arbitrary children. -/
theorem root_degree_characterization
    (f : (σ → ZMod 2) → ZMod 2) (g : (τ → ZMod 2) → ZMod 2) (a : ZMod 2)
    (u : (σ → ZMod 2) →ₗ[ZMod 2] ZMod 2) (v : (τ → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (c : (ζ → ZMod 2) →ₗ[ZMod 2] ZMod 2) {k : ℕ} (hk : 2 ≤ k)
    (hf : degree f = k) (hg : degree g = k)
    (hlinear : blockLinearFunction a u v c ≠ 0) :
    degree (blockLinearFunction a u v c * blockBranchFunction f g) ≤ k + 1 ↔
      blockLinearFunction a u v c = fun w => w none := by
  constructor
  · intro hprod
    obtain ⟨rfl, rfl, rfl⟩ := root_degree_forces_blocks_zero f g a u v c hk hf hg hprod
    have ha : a = 0 ∨ a = 1 := (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) a
    rcases ha with rfl | rfl
    · exfalso
      apply hlinear
      funext w
      simp [blockLinearFunction]
    · funext w
      simp [blockLinearFunction]
  · intro hroot
    rw [hroot]
    exact degree_selector_mul_blockBranchFunction f g hg.le

end BinaryFieldCounterexamples.BooleanFunctions
