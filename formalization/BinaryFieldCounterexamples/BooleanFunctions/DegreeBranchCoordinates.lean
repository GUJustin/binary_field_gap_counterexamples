/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.BooleanFunctions.DegreeBranch
public import Mathlib.Algebra.Module.Projective
/-!
# Transport of the top-degree root argument

The degree characterization in Lemma 6.5 (`lem:tree-root-unique`) is independent
of the chosen linear coordinates. We transport the leading-monomial separation
from `DegreeRoot` along surjective affine branch coordinates, retaining all
unused directions as an explicit third block.
-/
@[expose] public section
noncomputable section
namespace BinaryFieldCounterexamples.BooleanFunctions

variable {σ τ ζ : Type*} [Fintype σ] [Fintype τ] [Fintype ζ]

/-- Literal selector, child, and unused coordinates. -/
def blockCoordinateEquiv :
    (Option (BlockVariables σ τ ζ) → ZMod 2) ≃ₗ[ZMod 2]
      (ZMod 2 × (σ → ZMod 2) × (τ → ZMod 2) × (ζ → ZMod 2)) :=
  (LinearEquiv.piOptionEquivProd (ZMod 2)).trans
    ((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr
      ((LinearEquiv.sumArrowLequivProdArrow σ (τ ⊕ ζ) (ZMod 2) (ZMod 2)).trans
        ((LinearEquiv.refl (ZMod 2) (σ → ZMod 2)).prodCongr
          (LinearEquiv.sumArrowLequivProdArrow τ ζ (ZMod 2) (ZMod 2)))))

/-- Every linear form splits into its four independent coordinate blocks. -/
theorem exists_blockLinearFunction
    (L : (Option (BlockVariables σ τ ζ) → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ (a : ZMod 2) (u : (σ → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (v : (τ → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (c : (ζ → ZMod 2) →ₗ[ZMod 2] ZMod 2),
      (L : _ → ZMod 2) = blockLinearFunction a u v c := by
  let E := blockCoordinateEquiv (σ := σ) (τ := τ) (ζ := ζ)
  let M := L.comp E.symm.toLinearMap
  let U : (σ → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    M.comp ((LinearMap.inr (ZMod 2) (ZMod 2) _).comp
      (LinearMap.inl (ZMod 2) _ _))
  let V : (τ → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    M.comp ((LinearMap.inr (ZMod 2) (ZMod 2) _).comp
      ((LinearMap.inr (ZMod 2) _ _).comp (LinearMap.inl (ZMod 2) _ _)))
  let C : (ζ → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    M.comp ((LinearMap.inr (ZMod 2) (ZMod 2) _).comp
      ((LinearMap.inr (ZMod 2) _ _).comp (LinearMap.inr (ZMod 2) _ _)))
  refine ⟨M (1, 0, 0, 0), U, V, C, ?_⟩
  funext w
  have h : M (E w) = L w := by simp [M]
  rw [← h]
  have he : E w =
      w none • (1, 0, 0, 0) +
        (0, (fun i => w (some (blockX i))), 0, 0) +
        (0, 0, (fun i => w (some (blockY i))), 0) +
        (0, 0, 0, (fun i => w (some (blockZ i)))) := by
    change (w none, (fun i => w (some (blockX i))),
      (fun i => w (some (blockY i))), (fun i => w (some (blockZ i)))) = _
    ext <;> simp
  rw [he, map_add, map_add, map_add, map_smul]
  simp [U, V, C, blockLinearFunction, mul_comm]
  rfl

section Abstract
variable {V W U : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

/-- A surjective branch-coordinate map admits coordinates containing the full
kernel as an independent, unused block. -/
theorem exists_surjective_blockChart
    (L : U →ₗ[ZMod 2] (ZMod 2 × V × W)) (hL : Function.Surjective L) :
    ∃ C : (Option (BlockVariables (Fin (Module.finrank (ZMod 2) V))
        (Fin (Module.finrank (ZMod 2) W))
        (Fin (Module.finrank (ZMod 2) L.ker))) → ZMod 2) →ₗ[ZMod 2] U,
      Function.Surjective C ∧ ∀ w, L (C w) =
        (w none, (Module.finBasis (ZMod 2) V).equivFun.symm
          (fun i => w (some (blockX i))),
        (Module.finBasis (ZMod 2) W).equivFun.symm
          (fun i => w (some (blockY i)))) := by
  classical
  obtain ⟨S, hS⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hL)
  let bV := (Module.finBasis (ZMod 2) V).equivFun
  let bW := (Module.finBasis (ZMod 2) W).equivFun
  let bK := (Module.finBasis (ZMod 2) L.ker).equivFun
  let E := blockCoordinateEquiv (σ := Fin (Module.finrank (ZMod 2) V))
    (τ := Fin (Module.finrank (ZMod 2) W)) (ζ := Fin (Module.finrank (ZMod 2) L.ker))
  let D : (ZMod 2 × (Fin (Module.finrank (ZMod 2) V) → ZMod 2) ×
      (Fin (Module.finrank (ZMod 2) W) → ZMod 2) ×
      (Fin (Module.finrank (ZMod 2) L.ker) → ZMod 2)) →ₗ[ZMod 2] U := {
    toFun := fun p => S (p.1, bV.symm p.2.1, bW.symm p.2.2.1) + (bK.symm p.2.2.2 : U)
    map_add' := by
      intro x y
      simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]
      rw [show (x.1 + y.1, bV.symm x.2.1 + bV.symm y.2.1,
        bW.symm x.2.2.1 + bW.symm y.2.2.1) =
        (x.1, bV.symm x.2.1, bW.symm x.2.2.1) +
          (y.1, bV.symm y.2.1, bW.symm y.2.2.1) from rfl, map_add]
      abel
    map_smul' := by
      intro c x
      rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) c with rfl | rfl <;> simp
      change S 0=0
      exact map_zero S }
  refine ⟨D.comp E.toLinearMap, ?_, ?_⟩
  · intro x
    let k : L.ker := ⟨x - S (L x), by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun hS (L x)).symm⟩
    refine ⟨E.symm ((L x).1, bV (L x).2.1, bW (L x).2.2, bK k), ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E.apply_symm_apply]
    change S ((L x).1, bV.symm (bV (L x).2.1), bW.symm (bW (L x).2.2)) +
      (bK.symm (bK k) : U) = x
    simp only [LinearEquiv.symm_apply_apply]
    change S (L x) + (x - S (L x)) = x
    abel
  · intro w
    change L (S (w none, bV.symm (fun i => w (some (blockX i))),
      bW.symm (fun i => w (some (blockY i)))) +
      (bK.symm (fun i => w (some (blockZ i))) : U)) = _
    rw [map_add, show L (bK.symm (fun i => w (some (blockZ i))) : U) = 0 from
      (bK.symm _).property, add_zero]
    exact LinearMap.congr_fun hS _

/-- The degree test singles out the root functional of a surjective linear
pullback of two independent exact-degree children. The proof uses only the
leading-monomial argument of `root_degree_characterization`. -/
theorem root_degree_characterization_linearPullback
    (f : V → ZMod 2) (g : W → ZMod 2)
    (L : U →ₗ[ZMod 2] (ZMod 2 × V × W)) (hL : Function.Surjective L)
    (s : U →ₗ[ZMod 2] ZMod 2) (hsel : ∀ x, (L x).1 = s x)
    (ℓ : U →ₗ[ZMod 2] ZMod 2) (hℓ : ℓ ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) (hf : vectorDegree f = k) (hg : vectorDegree g = k) :
    vectorDegree (fun x => ℓ x * Trees.branch f g (L x)) ≤ k + 1 ↔ ℓ = s := by
  classical
  obtain ⟨C, hC, hcoord⟩ := exists_surjective_blockChart L hL
  obtain ⟨a, u, v, c, he⟩ := exists_blockLinearFunction (ℓ.comp C)
  let f₀ := f ∘ (Module.finBasis (ZMod 2) V).equivFun.symm
  let g₀ := g ∘ (Module.finBasis (ZMod 2) W).equivFun.symm
  have hb : (fun w => Trees.branch f g (L (C w))) =
      blockBranchFunction (ζ := Fin (Module.finrank (ZMod 2) L.ker)) f₀ g₀ := by
    funext w
    rw [hcoord]
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) (w none) with h | h <;>
      simp [Trees.branch, blockBranchFunction, h, f₀, g₀,
        show (1 : ZMod 2) + 1 = 0 by decide, Function.comp_def]
  have hd : vectorDegree (fun x => ℓ x * Trees.branch f g (L x)) =
      degree (blockLinearFunction a u v c * blockBranchFunction f₀ g₀) := by
    have h := vectorDegree_comp_affine_of_surjective
      (fun x => ℓ x * Trees.branch f g (L x)) C.toAffineMap hC
    rw [vectorDegree_eq_degree] at h
    have he' : (fun w => ℓ (C w)) = blockLinearFunction a u v c := he
    have hh : (fun x => ℓ x * Trees.branch f g (L x)) ∘ C.toAffineMap =
        blockLinearFunction a u v c * blockBranchFunction f₀ g₀ := by
      funext w
      exact congrArg₂ (· * ·) (congrFun he' w) (congrFun hb w)
    rw [hh] at h
    exact h.symm
  have hn : blockLinearFunction a u v c ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    obtain ⟨w, rfl⟩ := hC x
    have hw := congrFun he w
    simpa [hz] using hw
  have hr : blockLinearFunction a u v c = (fun w => w none) ↔ ℓ = s := by
    constructor
    · intro h
      ext x
      obtain ⟨w, rfl⟩ := hC x
      have hw := congrFun he w
      have hs := hsel (C w)
      rw [hcoord] at hs
      rw [h] at hw
      exact hw.trans hs
    · intro h
      funext w
      have hw := congrFun he w
      have hs := hsel (C w)
      rw [hcoord] at hs
      rw [h] at hw
      exact hw.symm.trans hs.symm
  rw [hd, root_degree_characterization f₀ g₀ a u v c hk hf hg hn, hr]

end Abstract
end BinaryFieldCounterexamples.BooleanFunctions
