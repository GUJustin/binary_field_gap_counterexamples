/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.BooleanFunctions.Degree
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeParity
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Module.Projective

/-!
# Affine invariance of Boolean degree

Section 6.2 defines degree using linear coordinates and asserts affine invariance.
Lemma 6.4 additionally uses invariance under passing to a quotient by periods.
The underlying fact is that substitution of affine polynomials, followed by
Boolean reduction, cannot raise total degree. Surjective affine maps have affine
sections, so pullback along them preserves degree exactly.
-/

@[expose] public section
noncomputable section

namespace BinaryFieldCounterexamples.BooleanFunctions

open MvPolynomial BigOperators Module

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

omit [Fintype σ] [Fintype τ] in
/-- Substituting polynomials of degree at most one cannot raise total degree. -/
theorem totalDegree_bind_le (p : MvPolynomial σ (ZMod 2))
    (q : σ → MvPolynomial τ (ZMod 2)) (hq : ∀ i, (q i).totalDegree ≤ 1) :
    (bind₁ q p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff p, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [bind₁_monomial]
  calc
    _ ≤ (C (p.coeff d)).totalDegree + (∏ i ∈ d.support, q i ^ d i).totalDegree :=
      totalDegree_mul _ _
    _ ≤ 0 + ∑ i ∈ d.support, (q i ^ d i).totalDegree := by
      simp only [totalDegree_C]
      gcongr
      exact totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      simp only [zero_add]
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hq i))
    _ ≤ p.totalDegree := le_totalDegree hd

/-- Pullback by a map with affine coordinate functions cannot raise Boolean degree. -/
theorem degree_comp_le_of_coordinates (f : (σ → ZMod 2) → ZMod 2)
    (g : (τ → ZMod 2) → (σ → ZMod 2))
    (hg : ∀ i, degree (fun x => g x i) ≤ 1) : degree (f ∘ g) ≤ degree f := by
  let q : σ → MvPolynomial τ (ZMod 2) := fun i => anf (fun x => g x i)
  have heval : (fun x => eval x (bind₁ q (anf f))) = f ∘ g := by
    funext x
    rw [show eval x (bind₁ q (anf f)) = eval (fun i => eval x (q i)) (anf f) from
      eval₂Hom_bind₁ _ _ _ _]
    simp [q, anf_eval]
  rw [degree, ← heval]
  exact (reduction_totalDegree_le _).trans (totalDegree_bind_le _ q hg)

/-- A literal affine combination of coordinates has degree at most one. -/
theorem degree_affine_combination_le (a : σ → ZMod 2) (c : ZMod 2) :
    degree (fun x => c + ∑ i, a i * x i) ≤ 1 := by
  let p : MvPolynomial σ (ZMod 2) := C c + ∑ i, C (a i) * X i
  have heval : (fun x => eval x p) = (fun x => c + ∑ i, a i * x i) := by
    simp [p]
  rw [← heval, degree]
  apply (reduction_totalDegree_le p).trans
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by simp)

/-- Affine scalar maps on coordinate spaces have Boolean degree at most one. -/
theorem degree_affine_le (a : (σ → ZMod 2) →ᵃ[ZMod 2] ZMod 2) : degree a ≤ 1 := by
  classical
  have h : (a : (σ → ZMod 2) → ZMod 2) =
      fun x => a 0 + ∑ i, a.linear (Pi.single i 1) * x i := by
    funext x
    rw [a.decomp]
    simp only [Pi.add_apply]
    conv_lhs => arg 1; rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul, smul_eq_mul]
    simp [mul_comm, add_comm]
  rw [h]
  exact degree_affine_combination_le _ _

/-- An affine Boolean function has degree one exactly when it is nonconstant. -/
theorem degree_affine_eq_one_iff (a : (σ → ZMod 2) →ᵃ[ZMod 2] ZMod 2) :
    degree a = 1 ↔ ¬ ∃ c, (a : (σ → ZMod 2) → ZMod 2) = fun _ => c := by
  rw [← degree_eq_zero_iff]
  have := degree_affine_le a
  omega

/-- Restriction through any affine parametrization cannot raise degree. -/
theorem degree_comp_affine_le (f : (σ → ZMod 2) → ZMod 2)
    (a : (τ → ZMod 2) →ᵃ[ZMod 2] (σ → ZMod 2)) : degree (f ∘ a) ≤ degree f := by
  apply degree_comp_le_of_coordinates
  intro i
  exact degree_affine_le ((AffineMap.proj i).comp a)

/-- Invertible affine changes of linear coordinates preserve Boolean degree. -/
theorem degree_comp_affineEquiv (f : (σ → ZMod 2) → ZMod 2)
    (e : (τ → ZMod 2) ≃ᵃ[ZMod 2] (σ → ZMod 2)) : degree (f ∘ e) = degree f := by
  apply le_antisymm (degree_comp_affine_le f e.toAffineMap)
  have h := degree_comp_affine_le (f ∘ e) e.symm.toAffineMap
  simpa [Function.comp_def] using h

/-- Pullback by a surjective affine map preserves degree; in particular this
applies to the projection onto a quotient by a subspace of periods. -/
theorem degree_comp_affine_of_surjective (f : (σ → ZMod 2) → ZMod 2)
    (a : (τ → ZMod 2) →ᵃ[ZMod 2] (σ → ZMod 2)) (ha : Function.Surjective a) :
    degree (f ∘ a) = degree f := by
  obtain ⟨L, hL⟩ := a.linear.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (a.linear_surjective_iff.mpr ha))
  let b : (σ → ZMod 2) →ᵃ[ZMod 2] (τ → ZMod 2) :=
    L.toAffineMap + AffineMap.const (ZMod 2) _ (-L (a 0))
  have hb : ∀ x, a (b x) = x := by
    intro x
    have h := LinearMap.congr_fun hL (x - a 0)
    rw [a.decomp]
    simpa [b, map_sub, sub_eq_add_neg] using congrArg (fun y => y + a 0) h
  apply le_antisymm (degree_comp_affine_le f a)
  have h := degree_comp_affine_le (f ∘ a) b
  simpa [Function.comp_def, hb] using h

section VectorSpace

variable {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- Degree on an abstract finite-dimensional binary vector space, computed in
the chosen finite basis. `vectorDegree_eq_coordinates` proves independence of
this choice and permits any linear coordinate equivalence. -/
def vectorDegree (f : U → ZMod 2) : ℕ :=
  degree (f ∘ (Module.finBasis (ZMod 2) U).equivFun.symm)

/-- The abstract degree agrees with the coordinate API on a coordinate space. -/
theorem vectorDegree_eq_degree (f : (σ → ZMod 2) → ZMod 2) :
    vectorDegree f = degree f := by
  let b := (Module.finBasis (ZMod 2) (σ → ZMod 2)).equivFun
  have h := degree_comp_affineEquiv f b.symm.toAffineEquiv
  exact h

/-- Constants on an abstract binary space have degree zero. -/
@[simp] theorem vectorDegree_const (c : ZMod 2) : vectorDegree (fun _ : U => c) = 0 := by
  exact degree_const c

/-- Addition bound on abstract binary spaces. -/
theorem vectorDegree_add_le (f g : U → ZMod 2) :
    vectorDegree (f + g) ≤ max (vectorDegree f) (vectorDegree g) := by
  exact degree_add_le _ _

/-- Multiplication bound on abstract binary spaces. -/
theorem vectorDegree_mul_le (f g : U → ZMod 2) :
    vectorDegree (f * g) ≤ vectorDegree f + vectorDegree g := by
  exact degree_mul_le _ _

/-- No Boolean function has degree greater than the dimension of its domain. -/
theorem vectorDegree_le_finrank (f : U → ZMod 2) :
    vectorDegree f ≤ Module.finrank (ZMod 2) U := by
  simpa [vectorDegree] using degree_le_card (f ∘ (Module.finBasis (ZMod 2) U).equivFun.symm)

/-- On a positive-dimensional abstract binary space, degree is below the
dimension exactly when the number of points at which the function is one is even. -/
theorem vectorDegree_lt_finrank_iff_even_support [Fintype U]
    (hd : 0 < Module.finrank (ZMod 2) U) (f : U → ZMod 2) :
    vectorDegree f < Module.finrank (ZMod 2) U ↔
      Even (Finset.univ.filter (fun x => f x = 1)).card := by
  classical
  let b := (Module.finBasis (ZMod 2) U).equivFun
  have : Nonempty (Fin (Module.finrank (ZMod 2) U)) := ⟨⟨0, hd⟩⟩
  have hsum : (∑ x, f (b.symm x)) = ∑ x, f x := b.symm.toEquiv.sum_comp f
  have hc : (Finset.univ.filter (fun x => f (b.symm x) = 1)).card % 2 =
      (Finset.univ.filter (fun x => f x = 1)).card % 2 := by
    rw [sum_values_eq_support_card, sum_values_eq_support_card] at hsum
    have hv := congrArg ZMod.val hsum
    simpa using hv
  have h := degree_lt_card_iff_even_support (f ∘ b.symm)
  simpa only [vectorDegree, b, Fintype.card_fin, Function.comp_apply,
    Nat.even_iff, hc] using h

/-- Degree zero on an abstract space detects precisely the constants. -/
theorem vectorDegree_eq_zero_iff (f : U → ZMod 2) :
    vectorDegree f = 0 ↔ ∃ c, f = fun _ => c := by
  rw [vectorDegree, degree_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    funext x
    simpa using congrFun hc ((Module.finBasis (ZMod 2) U).equivFun x)
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

/-- Complementation preserves the degree of every nonconstant abstract function. -/
theorem vectorDegree_complement (f : U → ZMod 2) (h : 1 ≤ vectorDegree f) :
    vectorDegree (f + fun _ => 1) = vectorDegree f := by
  exact degree_complement _ h

/-- Affine scalar maps on abstract spaces have degree at most one. -/
theorem vectorDegree_affine_le (a : U →ᵃ[ZMod 2] ZMod 2) : vectorDegree a ≤ 1 := by
  let b := (Module.finBasis (ZMod 2) U).equivFun
  exact degree_affine_le (a.comp b.symm.toAffineEquiv.toAffineMap)

/-- Nonconstant affine scalar maps have degree exactly one. -/
theorem vectorDegree_affine_eq_one_iff (a : U →ᵃ[ZMod 2] ZMod 2) :
    vectorDegree a = 1 ↔ ¬ ∃ c, (a : U → ZMod 2) = fun _ => c := by
  rw [← vectorDegree_eq_zero_iff]
  have := vectorDegree_affine_le a
  omega

/-- Every linear coordinate system computes the same degree. -/
theorem vectorDegree_eq_coordinates (f : U → ZMod 2)
    (e : U ≃ₗ[ZMod 2] (σ → ZMod 2)) : vectorDegree f = degree (f ∘ e.symm) := by
  let b := (Module.finBasis (ZMod 2) U).equivFun
  have h := degree_comp_affineEquiv (f ∘ e.symm) (b.symm.trans e).toAffineEquiv
  simpa [vectorDegree, b, Function.comp_def] using h

/-- Arbitrary choices of linear basis give the same algebraic-normal-form degree. -/
theorem degree_basis_independent (f : U → ZMod 2)
    (b : Basis σ (ZMod 2) U) (c : Basis τ (ZMod 2) U) :
    degree (f ∘ b.equivFun.symm) = degree (f ∘ c.equivFun.symm) := by
  rw [← vectorDegree_eq_coordinates f b.equivFun,
    ← vectorDegree_eq_coordinates f c.equivFun]

/-- Affine restriction on abstract spaces does not raise degree. -/
theorem vectorDegree_comp_affine_le (f : U → ZMod 2) (a : V →ᵃ[ZMod 2] U) :
    vectorDegree (f ∘ a) ≤ vectorDegree f := by
  let b := (Module.finBasis (ZMod 2) U).equivFun
  let c := (Module.finBasis (ZMod 2) V).equivFun
  have h := degree_comp_affine_le (f ∘ b.symm)
    (b.toAffineEquiv.toAffineMap.comp (a.comp c.symm.toAffineEquiv.toAffineMap))
  simpa [vectorDegree, b, c, Function.comp_def] using h

/-- Restriction to a translate of a subspace cannot raise degree. Every affine
subspace with a chosen point has this parametrization by its direction space. -/
theorem vectorDegree_restrict_translate_le (f : U → ZMod 2)
    (P : Submodule (ZMod 2) U) (p : U) :
    vectorDegree (fun v : P => f (p + v)) ≤ vectorDegree f := by
  have h := vectorDegree_comp_affine_le f
    (P.subtype.toAffineMap + AffineMap.const (ZMod 2) P p)
  simpa [Function.comp_def, add_comm] using h

/-- Invariance under invertible affine changes on abstract binary vector spaces. -/
theorem vectorDegree_comp_affineEquiv (f : U → ZMod 2) (e : V ≃ᵃ[ZMod 2] U) :
    vectorDegree (f ∘ e) = vectorDegree f := by
  apply le_antisymm (vectorDegree_comp_affine_le f e.toAffineMap)
  have h := vectorDegree_comp_affine_le (f ∘ e) e.symm.toAffineMap
  simpa [Function.comp_def] using h

/-- A surjective affine parametrization preserves degree on abstract spaces. -/
theorem vectorDegree_comp_affine_of_surjective (f : U → ZMod 2)
    (a : V →ᵃ[ZMod 2] U) (ha : Function.Surjective a) :
    vectorDegree (f ∘ a) = vectorDegree f := by
  let b := (Module.finBasis (ZMod 2) U).equivFun
  let c := (Module.finBasis (ZMod 2) V).equivFun
  let A := b.toAffineEquiv.toAffineMap.comp (a.comp c.symm.toAffineEquiv.toAffineMap)
  have hA : Function.Surjective A := b.surjective.comp (ha.comp c.symm.surjective)
  have h := degree_comp_affine_of_surjective (f ∘ b.symm) A hA
  simpa [vectorDegree, b, c, A, Function.comp_def] using h

end VectorSpace

end BinaryFieldCounterexamples.BooleanFunctions
