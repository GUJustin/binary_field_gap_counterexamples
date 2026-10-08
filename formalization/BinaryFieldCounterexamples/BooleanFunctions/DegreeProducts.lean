/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeLeading

/-!
# Independent blocks and the leading part of a Boolean branch

The polynomial ingredients of the degree argument following equation
`eq:tree-coordinates` in `sections/constructions/additive-support-trees.tex`.
The selector is `none`; the independent child blocks are indexed by a sum.
Polynomial statements are connected to the canonical Boolean normal forms by
`anf_branchFunction`, `degree_branchFunction`, and `topPart_branchFunction`.
The selector product also gives the upper degree bound in Lemma 6.5.
-/

@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions
open MvPolynomial

variable {R σ τ : Type*} [CommSemiring R]

/-- Injective renaming preserves total degree. -/
theorem totalDegree_rename_injective (f : σ → τ) (hf : Function.Injective f)
    (p : MvPolynomial σ R) : (rename f p).totalDegree = p.totalDegree := by
  classical
  apply le_antisymm (totalDegree_rename_le f p)
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro d hd
  have hd' : d.mapDomain f ∈ (rename f p).support := by
    simpa only [mem_support_iff, coeff_rename_mapDomain f hf] using hd
  have he : (d.mapDomain f).sum (fun _ e => e) = d.sum (fun _ e => e) := by
    exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
  rw [← he]
  exact MvPolynomial.le_totalDegree hd'

/-- Disjoint child blocks cannot cancel any term of positive degree. -/
theorem totalDegree_independent_add (p : MvPolynomial σ R) (q : MvPolynomial τ R)
    {k : ℕ} (hk : 0 < k) (hp : p.totalDegree = k) (hq : q.totalDegree ≤ k) :
    (rename Sum.inl p + rename Sum.inr q).totalDegree = k := by
  classical
  apply le_antisymm
  · exact (totalDegree_add _ _).trans (max_le
      (by rw [totalDegree_rename_injective _ Sum.inl_injective, hp])
      ((totalDegree_rename_le _ _).trans hq))
  obtain ⟨d, hd, hdeg⟩ := Finset.exists_mem_eq_sup p.support
    (by rw [MvPolynomial.support_nonempty]; intro he; simp [he] at hp; omega)
    (fun d => d.sum fun _ e => e)
  have hdne : d ≠ 0 := by
    intro he
    have := hp
    rw [MvPolynomial.totalDegree, hdeg, he] at this
    simp at this
    omega
  have hqzero : (rename Sum.inr q).coeff (d.mapDomain Sum.inl) = 0 := by
    apply coeff_rename_eq_zero
    intro e he
    have hde : d = 0 := by
      ext i
      have hi := congrArg (fun m => m (Sum.inl i)) he
      simpa [Finsupp.mapDomain_apply, Sum.inl_injective, Sum.inr_injective] using hi.symm
    exact (hdne hde).elim
  have hadd : d.mapDomain Sum.inl ∈ (rename Sum.inl p + rename Sum.inr q).support := by
    rw [MvPolynomial.mem_support_iff]
    simpa [coeff_rename_mapDomain _ Sum.inl_injective, hqzero] using (MvPolynomial.mem_support_iff.mp hd)
  have he : (d.mapDomain (Sum.inl : σ → σ ⊕ τ)).sum (fun _ e => e) = d.sum (fun _ e => e) :=
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
  have hdk : d.sum (fun _ e => e) = k := hdeg.symm.trans hp
  rw [← hdk, ← he]
  exact MvPolynomial.le_totalDegree hadd

/-- Polynomial form of `(1+s) p(x) + s q(y)`. -/
def branchPolynomial (p : MvPolynomial σ R) (q : MvPolynomial τ R) :
    MvPolynomial (Option (σ ⊕ τ)) R :=
  rename (Option.some ∘ Sum.inl) p + X none *
    (rename (Option.some ∘ Sum.inl) p + rename (Option.some ∘ Sum.inr) q)

/-- A branch with independent children of common positive degree `k` has degree `k+1`.
Only the first child needs exact degree; the second may have smaller degree. -/
theorem totalDegree_branchPolynomial [Nontrivial R] [NoZeroDivisors R]
    (p : MvPolynomial σ R) (q : MvPolynomial τ R) {k : ℕ}
    (hk : 0 < k) (hp : p.totalDegree = k) (hq : q.totalDegree ≤ k) :
    (branchPolynomial p q).totalDegree = k + 1 := by
  have hd := totalDegree_independent_add p q hk hp hq
  have hrename : (rename Option.some (rename Sum.inl p + rename Sum.inr q)).totalDegree = k := by
    rw [totalDegree_rename_injective _ (Option.some_injective _), hd]
  have hn : rename Option.some (rename Sum.inl p + rename Sum.inr q) ≠ 0 := by
    intro he
    simp [he] at hrename
    omega
  have hm : (X none * rename Option.some (rename Sum.inl p + rename Sum.inr q)).totalDegree = k + 1 := by
    rw [totalDegree_mul_of_isDomain (X_ne_zero none) hn, totalDegree_X, hrename]
    omega
  unfold branchPolynomial
  have he : rename (Option.some ∘ Sum.inl) p + rename (Option.some ∘ Sum.inr) q =
      rename Option.some (rename Sum.inl p + rename Sum.inr q) := by
    simp [map_add, rename_rename]
  rw [he]
  rw [totalDegree_add_eq_right_of_totalDegree_lt]
  · exact hm
  · rw [hm, totalDegree_rename_injective _ ((Option.some_injective _).comp Sum.inl_injective), hp]
    omega

/-- Multiplication by a variable shifts each homogeneous component by one. -/
theorem homogeneousComponent_X_mul (s : σ) (p : MvPolynomial σ R) (k : ℕ) :
    homogeneousComponent (k + 1) (X s * p) = X s * homogeneousComponent k p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
  | monomial d r =>
    rw [X, monomial_mul_monomial, one_mul]
    rw [homogeneousComponent_of_mem (isHomogeneous_monomial r rfl),
      homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
    have he : (Finsupp.single s 1 + d).degree = 1 + d.degree := by
      simp [map_add, Finsupp.degree_single]
    simp only [he]
    by_cases hd : k = d.degree
    · simp [hd, monomial_mul_monomial, Nat.add_comm]
    · have hne : k + 1 ≠ 1 + d.degree := by omega
      simp [hd, hne]

/-- The leading part of the branch is precisely `s (Ω₀ + Ω₁)`, as in the
paragraph after equation `eq:tree-coordinates` in the paper. -/
theorem homogeneousComponent_branchPolynomial
    (p : MvPolynomial σ R) (q : MvPolynomial τ R) {k : ℕ}
    (hp : p.totalDegree ≤ k) :
    homogeneousComponent (k + 1) (branchPolynomial p q) =
      X none * (rename (Option.some ∘ Sum.inl) (homogeneousComponent k p) +
        rename (Option.some ∘ Sum.inr) (homogeneousComponent k q)) := by
  unfold branchPolynomial
  rw [map_add, homogeneousComponent_eq_zero, zero_add, homogeneousComponent_X_mul, map_add]
  · rw [← rename_homogeneousComponent, ← rename_homogeneousComponent]
  · exact lt_of_le_of_lt (totalDegree_rename_le _ p |>.trans hp) (Nat.lt_succ_self k)

/-- Distinct monomial types separate in a vanishing sum. This packages the
six-type argument in the proof of `lem:tree-root-unique`: a type may record the
number of variables in each of the `x`, `y`, and `z` blocks. -/
theorem weighted_types_separate {M ι : Type*} [AddCommMonoid M]
    [Fintype ι] (w : σ → M) (t : ι → M) (ht : Function.Injective t)
    (p : ι → MvPolynomial σ R) (hp : ∀ i, (p i).IsWeightedHomogeneous w (t i))
    (hsum : ∑ i, p i = 0) : ∀ i, p i = 0 := by
  classical
  intro i
  have h := congrArg (weightedHomogeneousComponent w (t i)) hsum
  rw [map_sum, map_zero] at h
  simpa only [weightedHomogeneousComponent_of_mem (hp _), ht.eq_iff,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h

/-- A polynomial of exact positive degree has a nonzero leading homogeneous part. -/
theorem homogeneousComponent_top_ne_zero (p : MvPolynomial σ (ZMod 2))
    {k : ℕ} (hk : 0 < k) (hp : p.totalDegree = k) : homogeneousComponent k p ≠ 0 := by
  intro hz
  have hlt := totalDegree_sub_homogeneousComponent_lt p hk hp.le
  simp [hz, hp] at hlt

section BlockTypes
variable {M : Type*} [AddCommMonoid M]

/-- Renaming transports a polynomial's monomial type along the coordinate map. -/
theorem isWeightedHomogeneous_rename {m : M} (w : τ → M) (j : σ → τ)
    (p : MvPolynomial σ R) (hp : p.IsWeightedHomogeneous (w ∘ j) m) :
    (rename j p).IsWeightedHomogeneous w m := by
  intro d hd
  obtain ⟨e, rfl, he⟩ := coeff_rename_ne_zero j p d hd
  have hh := hp he
  rw [Finsupp.weight_apply] at hh ⊢
  rw [Finsupp.sum_mapDomain_index (h := fun i c => c • w i)
    (fun _ => zero_nsmul _) (fun _ _ _ => add_nsmul _ _ _)]
  exact hh

/-- Giving every variable the same vector weight records ordinary homogeneous degree. -/
theorem isWeightedHomogeneous_const_weight {k : ℕ} (p : MvPolynomial σ R)
    (hp : p.IsHomogeneous k) (e : M) : p.IsWeightedHomogeneous (fun _ => e) (k • e) := by
  intro d hd
  have hh := hp hd
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_nsmul_assoc]
  congr 1
  simpa [Finsupp.weight_apply, Finsupp.sum] using hh

end BlockTypes

section BooleanBranch
variable [Fintype σ] [Fintype τ]

/-- The branch function in the paper's independent selector and child coordinates. -/
def branchFunction (f : (σ → ZMod 2) → ZMod 2) (g : (τ → ZMod 2) → ZMod 2)
    (w : Option (σ ⊕ τ) → ZMod 2) : ZMod 2 :=
  (1 + w none) * f (fun i => w (some (Sum.inl i))) +
    w none * g (fun i => w (some (Sum.inr i)))

/-- The algebraic normal form of an independent branch is exactly the paper's
coordinate polynomial; multiplication by the fresh selector needs no reduction. -/
theorem anf_branchFunction (f : (σ → ZMod 2) → ZMod 2)
    (g : (τ → ZMod 2) → ZMod 2) :
    anf (branchFunction f g) = branchPolynomial (anf f) (anf g) := by
  apply anf_unique
  · unfold branchPolynomial
    have hp : rename (Option.some ∘ Sum.inl) (anf f) ∈
      restrictDegree (Option (σ ⊕ τ)) (ZMod 2) 1 := rename_mem_restrictDegree (Option.some ∘ Sum.inl)
      ((Option.some_injective _).comp Sum.inl_injective) (anf f) (anf_mem_restrictDegree f)
    have hq : rename (Option.some ∘ Sum.inr) (anf g) ∈
      restrictDegree (Option (σ ⊕ τ)) (ZMod 2) 1 := rename_mem_restrictDegree (Option.some ∘ Sum.inr)
      ((Option.some_injective _).comp Sum.inr_injective) (anf g) (anf_mem_restrictDegree g)
    apply (restrictDegree _ _ 1).add_mem hp
    apply X_mul_mem_restrictDegree _ _ ((restrictDegree _ _ 1).add_mem hp hq)
    apply Nat.eq_zero_of_le_zero
    apply (degreeOf_add_le _ _ _).trans
    apply max_le
    · rw [degreeOf_rename_of_not_mem_range (Option.some ∘ Sum.inl)
        ((Option.some_injective _).comp Sum.inl_injective) (anf f) none (by simp)]
    · rw [degreeOf_rename_of_not_mem_range (Option.some ∘ Sum.inr)
        ((Option.some_injective _).comp Sum.inr_injective) (anf g) none (by simp)]
  · intro w
    simp only [branchPolynomial, eval_add, eval_mul, eval_X, eval_rename, anf_eval,
      Function.comp_def, branchFunction]
    ring

/-- Independent Boolean children of positive degree `k` give a branch of exact
 degree `k+1` (Lemma 6.4, the recursive degree clause). -/
theorem degree_branchFunction (f : (σ → ZMod 2) → ZMod 2)
    (g : (τ → ZMod 2) → ZMod 2) {k : ℕ} (hk : 0 < k)
    (hf : degree f = k) (hg : degree g ≤ k) : degree (branchFunction f g) = k + 1 := by
  rw [degree, anf_branchFunction]
  exact totalDegree_branchPolynomial _ _ hk hf hg

/-- Leading algebraic normal form in the independent coordinates of
`eq:tree-coordinates`: its homogeneous part is `s (Ω₀ + Ω₁)`. -/
theorem topPart_branchFunction (f : (σ → ZMod 2) → ZMod 2)
    (g : (τ → ZMod 2) → ZMod 2) {k : ℕ} (hf : degree f ≤ k) :
    homogeneousComponent (k + 1) (anf (branchFunction f g)) =
      X none * (rename (Option.some ∘ Sum.inl) (homogeneousComponent k (anf f)) +
        rename (Option.some ∘ Sum.inr) (homogeneousComponent k (anf g))) := by
  rw [anf_branchFunction]
  exact homogeneousComponent_branchPolynomial _ _ hf

/-- Multiplying a branch by its selector simply retains the `s=1` child.
This is the first step in the proof of Lemma 6.5 (unique root). -/
theorem anf_selector_mul_branchFunction (f : (σ → ZMod 2) → ZMod 2)
    (g : (τ → ZMod 2) → ZMod 2) :
    anf ((fun w : Option (σ ⊕ τ) → ZMod 2 => w none) * branchFunction f g) =
      X none * rename (Option.some ∘ Sum.inr) (anf g) := by
  apply anf_unique
  · apply X_mul_mem_restrictDegree
    · exact rename_mem_restrictDegree _
        ((Option.some_injective _).comp Sum.inr_injective) _ (anf_mem_restrictDegree g)
    · exact degreeOf_rename_of_not_mem_range _
        ((Option.some_injective _).comp Sum.inr_injective) _ _ (by simp)
  · intro w
    simp only [eval_mul, eval_X, eval_rename, anf_eval, Function.comp_def, Pi.mul_apply,
      branchFunction]
    have hw : w none = 0 ∨ w none = 1 := by
      have hh := (w none).val_lt
      interval_cases hv : (w none).val <;> [left; right] <;>
        apply ZMod.val_injective <;> simp [hv, ZMod.val_one_eq_one_mod]
    rcases hw with hw | hw <;> simp [hw, show (1 : ZMod 2) + 1 = 0 by decide]

/-- The root selector times the branch has degree at most `k+1`, with no
hypothesis on the first child (Lemma 6.5, first sentence of the proof). -/
theorem degree_selector_mul_branchFunction (f : (σ → ZMod 2) → ZMod 2)
    (g : (τ → ZMod 2) → ZMod 2) {k : ℕ} (hg : degree g ≤ k) :
    degree ((fun w : Option (σ ⊕ τ) → ZMod 2 => w none) * branchFunction f g) ≤ k + 1 := by
  rw [degree, anf_selector_mul_branchFunction]
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_X]
    have := (totalDegree_rename_le (Option.some ∘ (Sum.inr : τ → σ ⊕ τ)) (anf g)).trans hg
    omega)

end BooleanBranch

end BinaryFieldCounterexamples.BooleanFunctions
