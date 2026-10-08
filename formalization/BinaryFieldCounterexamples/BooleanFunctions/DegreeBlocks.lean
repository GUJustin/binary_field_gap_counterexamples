/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeBlockSupport

/-!
# Monomial types in independent Boolean coordinate blocks

The blockwise polynomial separation argument of Lemma 6.5 (unique root),
`lem:tree-root-unique` in the paper. The variables are split into `x`, `y`, `z`;
monomial types record the three respective variable counts.
-/

@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions
open MvPolynomial
variable {σ τ ζ Γ : Type*}

/-- Variables in the three independent child and unused coordinate blocks. -/
abbrev BlockVariables (σ τ ζ : Type*) := σ ⊕ (τ ⊕ ζ)

/-- The three-coordinate weight counts variables from each block. -/
def blockWeight : BlockVariables σ τ ζ → ℕ × ℕ × ℕ
  | Sum.inl _ => (1, 0, 0)
  | Sum.inr (Sum.inl _) => (0, 1, 0)
  | Sum.inr (Sum.inr _) => (0, 0, 1)

/-- The `x`-block embedding. -/
def blockX : σ → BlockVariables σ τ ζ := Sum.inl
/-- The `y`-block embedding. -/
def blockY : τ → BlockVariables σ τ ζ := Sum.inr ∘ Sum.inl
/-- The unused `z`-block embedding. -/
def blockZ : ζ → BlockVariables σ τ ζ := Sum.inr ∘ Sum.inr

/-- Distinct embedding ranges make products of multilinear polynomials multilinear. -/
theorem rename_mul_mem_restrictDegree_of_disjoint {α β : Type*}
    (j : α → Γ) (l : β → Γ) (hj : Function.Injective j) (hl : Function.Injective l)
    (hd : Disjoint (Set.range j) (Set.range l))
    (p : MvPolynomial α (ZMod 2)) (q : MvPolynomial β (ZMod 2))
    (hp : p ∈ restrictDegree α (ZMod 2) 1) (hq : q ∈ restrictDegree β (ZMod 2) 1) :
    rename j p * rename l q ∈ restrictDegree Γ (ZMod 2) 1 := by
  apply mul_mem_restrictDegree_of_disjoint _ _ (rename_mem_restrictDegree j hj p hp)
    (rename_mem_restrictDegree l hl q hq)
  intro i
  by_cases hi : i ∈ Set.range j
  · right
    apply degreeOf_rename_of_not_mem_range l hl q i
    exact fun hi' => Set.disjoint_left.mp hd hi hi'
  · left
    exact degreeOf_rename_of_not_mem_range j hj p i hi

/-- Homogeneous `x`-polynomials have monomial type `(k,0,0)`. -/
theorem isWeightedHomogeneous_blockX (p : MvPolynomial σ (ZMod 2)) {k : ℕ}
    (hp : p.IsHomogeneous k) :
    (rename (blockX : σ → BlockVariables σ τ ζ) p).IsWeightedHomogeneous blockWeight (k, 0, 0) := by
  apply isWeightedHomogeneous_rename
  simpa [blockWeight, blockX, Function.comp_def, nsmul_eq_mul] using
    isWeightedHomogeneous_const_weight p hp ((1, 0, 0) : ℕ × ℕ × ℕ)

/-- Homogeneous `y`-polynomials have monomial type `(0,k,0)`. -/
theorem isWeightedHomogeneous_blockY (p : MvPolynomial τ (ZMod 2)) {k : ℕ}
    (hp : p.IsHomogeneous k) :
    (rename (blockY : τ → BlockVariables σ τ ζ) p).IsWeightedHomogeneous blockWeight (0, k, 0) := by
  apply isWeightedHomogeneous_rename
  simpa [blockWeight, blockY, Function.comp_def, nsmul_eq_mul] using
    isWeightedHomogeneous_const_weight p hp ((0, 1, 0) : ℕ × ℕ × ℕ)

/-- Homogeneous `z`-polynomials have monomial type `(0,0,k)`. -/
theorem isWeightedHomogeneous_blockZ (p : MvPolynomial ζ (ZMod 2)) {k : ℕ}
    (hp : p.IsHomogeneous k) :
    (rename (blockZ : ζ → BlockVariables σ τ ζ) p).IsWeightedHomogeneous blockWeight (0, 0, k) := by
  apply isWeightedHomogeneous_rename
  simpa [blockWeight, blockZ, Function.comp_def, nsmul_eq_mul] using
    isWeightedHomogeneous_const_weight p hp ((0, 0, 1) : ℕ × ℕ × ℕ)

section Reduction
variable [Fintype σ] [Fintype τ] [Fintype ζ] [Fintype Γ]

/-- Cross-block products are already reduced, so Boolean multiplication does
not alter their coefficients. -/
theorem reduction_rename_mul_of_disjoint {α β : Type*}
    (j : α → Γ) (l : β → Γ) (hj : Function.Injective j) (hl : Function.Injective l)
    (hd : Disjoint (Set.range j) (Set.range l))
    (p : MvPolynomial α (ZMod 2)) (q : MvPolynomial β (ZMod 2))
    (hp : p ∈ restrictDegree α (ZMod 2) 1) (hq : q ∈ restrictDegree β (ZMod 2) 1) :
    reduction (rename j p * rename l q) = rename j p * rename l q := by
  exact anf_eval_eq_of_reduced _ (rename_mul_mem_restrictDegree_of_disjoint j l hj hl hd p q hp hq)

omit [Fintype σ] in
/-- A homogeneous linear polynomial is multilinear, including the zero form. -/
theorem homogeneous_one_mem_restrictDegree (p : MvPolynomial σ (ZMod 2))
    (hp : p.IsHomogeneous 1) : p ∈ restrictDegree σ (ZMod 2) 1 := by
  rw [mem_restrictDegree]
  intro d hd i
  exact (monomial_le_degreeOf i hd).trans ((degreeOf_le_totalDegree p i).trans hp.totalDegree_le)

/-- The four mixed products in the root proof survive reduction unchanged;
the two pure products remain confined to their own blocks. -/
theorem homogeneousComponent_reduction_block_product
    (p₀ u : MvPolynomial σ (ZMod 2)) (p₁ v : MvPolynomial τ (ZMod 2))
    (c : MvPolynomial ζ (ZMod 2)) {k : ℕ}
    (hp₀ : p₀.IsHomogeneous k) (hp₁ : p₁.IsHomogeneous k)
    (hu : u.IsHomogeneous 1) (hv : v.IsHomogeneous 1) (hc : c.IsHomogeneous 1)
    (hr₀ : p₀ ∈ restrictDegree σ (ZMod 2) 1) (hr₁ : p₁ ∈ restrictDegree τ (ZMod 2) 1) :
    homogeneousComponent (k + 1) (reduction
      ((rename blockX u + rename blockY v + rename blockZ c) *
        (rename blockX p₀ + rename blockY p₁))) =
      rename blockX (homogeneousComponent (k + 1) (reduction (u * p₀))) +
      rename blockY (homogeneousComponent (k + 1) (reduction (v * p₁))) +
      rename blockX u * rename blockY p₁ + rename blockY v * rename blockX p₀ +
      rename blockZ c * rename blockX p₀ + rename blockZ c * rename blockY p₁ := by
  have hx : Function.Injective (blockX : σ → BlockVariables σ τ ζ) := Sum.inl_injective
  have hy : Function.Injective (blockY : τ → BlockVariables σ τ ζ) := Sum.inr_injective.comp Sum.inl_injective
  have hz : Function.Injective (blockZ : ζ → BlockVariables σ τ ζ) := Sum.inr_injective.comp Sum.inr_injective
  have hxy : Disjoint (Set.range (blockX : σ → BlockVariables σ τ ζ)) (Set.range blockY) := by
    simp [Set.disjoint_left, blockX, blockY, Function.comp_def]
  have hxz : Disjoint (Set.range (blockX : σ → BlockVariables σ τ ζ)) (Set.range blockZ) := by
    simp [Set.disjoint_left, blockX, blockZ, Function.comp_def]
  have hyz : Disjoint (Set.range (blockY : τ → BlockVariables σ τ ζ)) (Set.range blockZ) := by
    simp [Set.disjoint_left, blockY, blockZ, Function.comp_def]
  have he : (rename blockX u + rename blockY v + rename blockZ c) *
      (rename blockX p₀ + rename blockY p₁) =
      rename blockX (u * p₀) + rename blockY (v * p₁) +
      rename blockX u * rename blockY p₁ + rename blockY v * rename blockX p₀ +
      rename blockZ c * rename blockX p₀ + rename blockZ c * rename blockY p₁ := by
    simp only [map_mul]
    ring
  rw [he]
  simp only [reduction_add, map_add]
  rw [reduction_rename _ hx, reduction_rename _ hy,
    reduction_rename_mul_of_disjoint _ _ hx hy hxy _ _ (homogeneous_one_mem_restrictDegree u hu) hr₁,
    reduction_rename_mul_of_disjoint _ _ hy hx hxy.symm _ _ (homogeneous_one_mem_restrictDegree v hv) hr₀,
    reduction_rename_mul_of_disjoint _ _ hz hx hxz.symm _ _ (homogeneous_one_mem_restrictDegree c hc) hr₀,
    reduction_rename_mul_of_disjoint _ _ hz hy hyz.symm _ _ (homogeneous_one_mem_restrictDegree c hc) hr₁]
  rw [← rename_homogeneousComponent, ← rename_homogeneousComponent]
  congr 4
  · exact homogeneousComponent_eq_self (by simpa [Nat.add_comm] using (hu.rename_isHomogeneous).mul (hp₁.rename_isHomogeneous))
  · exact homogeneousComponent_eq_self (by simpa [Nat.add_comm] using (hv.rename_isHomogeneous).mul (hp₀.rename_isHomogeneous))
  · exact homogeneousComponent_eq_self (by simpa [Nat.add_comm] using (hc.rename_isHomogeneous).mul (hp₀.rename_isHomogeneous))
  · exact homogeneousComponent_eq_self (by simpa [Nat.add_comm] using (hc.rename_isHomogeneous).mul (hp₁.rename_isHomogeneous))

/-- The six monomial types in the paper's root proof are distinct for `k≥2`.
Consequently a linear form supported in the `x`, `y`, and unused `z` blocks can
have no nonzero part if its product with the two child leading forms has no
component of degree `k+1`. The children may be arbitrary nonzero multilinear
homogeneous forms, rather than tree templates. -/
theorem root_top_block_separation
    (p₀ u : MvPolynomial σ (ZMod 2)) (p₁ v : MvPolynomial τ (ZMod 2))
    (c : MvPolynomial ζ (ZMod 2)) {k : ℕ} (hk : 2 ≤ k)
    (hp₀ : p₀.IsHomogeneous k) (hp₁ : p₁.IsHomogeneous k)
    (hne₀ : p₀ ≠ 0) (hne₁ : p₁ ≠ 0)
    (hu : u.IsHomogeneous 1) (hv : v.IsHomogeneous 1) (hc : c.IsHomogeneous 1)
    (hr₀ : p₀ ∈ restrictDegree σ (ZMod 2) 1) (hr₁ : p₁ ∈ restrictDegree τ (ZMod 2) 1)
    (hprod : homogeneousComponent (k + 1) (reduction
      ((rename blockX u + rename blockY v + rename blockZ c) *
        (rename blockX p₀ + rename blockY p₁))) = 0) :
    u = 0 ∧ v = 0 ∧ c = 0 := by
  classical
  let polys : Fin 6 → MvPolynomial (BlockVariables σ τ ζ) (ZMod 2) :=
    ![rename blockX (homogeneousComponent (k + 1) (reduction (u * p₀))),
      rename blockY (homogeneousComponent (k + 1) (reduction (v * p₁))),
      rename blockX u * rename blockY p₁,
      rename blockY v * rename blockX p₀,
      rename blockZ c * rename blockX p₀,
      rename blockZ c * rename blockY p₁]
  let types : Fin 6 → ℕ × ℕ × ℕ :=
    ![(k + 1, 0, 0), (0, k + 1, 0), (1, k, 0), (k, 1, 0), (k, 0, 1), (0, k, 1)]

  -- The positive child degree makes all six block-count vectors different.
  have ht : Function.Injective types := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [types, Prod.mk.injEq] at hij ⊢ <;> omega
  have hp : ∀ i, (polys i).IsWeightedHomogeneous blockWeight (types i) := by
    intro i
    fin_cases i <;> dsimp [polys, types]
    · exact isWeightedHomogeneous_blockX _ (homogeneousComponent_isHomogeneous _ _)
    · exact isWeightedHomogeneous_blockY _ (homogeneousComponent_isHomogeneous _ _)
    · simpa using (isWeightedHomogeneous_blockX u hu).mul (isWeightedHomogeneous_blockY p₁ hp₁)
    · simpa using (isWeightedHomogeneous_blockY v hv).mul (isWeightedHomogeneous_blockX p₀ hp₀)
    · simpa using (isWeightedHomogeneous_blockZ c hc).mul (isWeightedHomogeneous_blockX p₀ hp₀)
    · simpa using (isWeightedHomogeneous_blockZ c hc).mul (isWeightedHomogeneous_blockY p₁ hp₁)
  have hsum : ∑ i, polys i = 0 := by
    rw [homogeneousComponent_reduction_block_product _ _ _ _ _ hp₀ hp₁ hu hv hc hr₀ hr₁] at hprod
    simpa [polys, Fin.sum_univ_succ, add_assoc] using hprod
  have hz := weighted_types_separate blockWeight types ht polys hp hsum

  -- The mixed products are ordinary products of nonzero polynomials. Since the
  -- child leading forms are nonzero, each corresponding linear form vanishes.
  have h₂ := hz 2
  have h₃ := hz 3
  have h₄ := hz 4
  dsimp [polys] at h₂ h₃ h₄
  have hx : Function.Injective (blockX : σ → BlockVariables σ τ ζ) := Sum.inl_injective
  have hy : Function.Injective (blockY : τ → BlockVariables σ τ ζ) := Sum.inr_injective.comp Sum.inl_injective
  have hz' : Function.Injective (blockZ : ζ → BlockVariables σ τ ζ) := Sum.inr_injective.comp Sum.inr_injective
  have hpx : rename (blockX : σ → BlockVariables σ τ ζ) p₀ ≠ 0 := by
    exact fun hh => hne₀ (rename_injective _ hx (by simpa using hh))
  have hpy : rename (blockY : τ → BlockVariables σ τ ζ) p₁ ≠ 0 := by
    exact fun hh => hne₁ (rename_injective _ hy (by simpa using hh))
  refine ⟨?_, ?_, ?_⟩
  · exact rename_injective _ hx (by simpa using (mul_eq_zero.mp h₂).resolve_right hpy)
  · exact rename_injective _ hy (by simpa using (mul_eq_zero.mp h₃).resolve_right hpx)
  · exact rename_injective _ hz' (by simpa using (mul_eq_zero.mp h₄).resolve_right hpx)

end Reduction

end BinaryFieldCounterexamples.BooleanFunctions
