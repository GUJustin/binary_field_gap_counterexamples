/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.BaseCount
public import BinaryFieldCounterexamples.Constructions.Trees.TemplateCounts
public import BinaryFieldCounterexamples.Constructions.Trees.PullbackProperties
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Definition
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Quotient
/-!
# Intrinsic height-two tree functions

The height-two predicate from Definition `def:tree-functions` is
balance, degree two, and essential dimension three. On the three-dimensional
essential quotient these are precisely the 56 affine images of `baseTemplate`.
This proves the height-two case of the degree-free clauses of
Lemma `lem:tree-structure`; the Boolean-degree identification is supplied by
`isHeightTwoTree_iff_balanced_essentialDimension`.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees

attribute [local instance] binaryFintype

/-- One affine coordinate datum for each nonplanar four-point support. -/
def heightTwoAffineList : List ((Fin 3 → ZMod 2) × (Fin 3 → (Fin 3 → ZMod 2))) :=
  [baseDatum 3 5 6 7,
   baseDatum 3 5 2 6,
   baseDatum 3 1 6 5,
   baseDatum 0 3 5 4,
   baseDatum 3 5 6 2,
   baseDatum 3 5 2 3,
   baseDatum 3 1 6 4,
   baseDatum 0 3 5 7,
   baseDatum 3 1 5 6,
   baseDatum 0 3 4 5,
   baseDatum 3 1 4 6,
   baseDatum 0 3 7 5,
   baseDatum 3 5 6 1,
   baseDatum 3 5 2 4,
   baseDatum 3 1 6 3,
   baseDatum 0 3 5 1,
   baseDatum 3 5 1 6,
   baseDatum 0 4 3 5,
   baseDatum 3 4 1 6,
   baseDatum 0 1 5 3,
   baseDatum 3 5 4 2,
   baseDatum 3 4 5 2,
   baseDatum 0 4 1 2,
   baseDatum 0 1 4 2,
   baseDatum 3 1 2 7,
   baseDatum 0 3 1 5,
   baseDatum 0 1 3 5,
   baseDatum 0 1 2 4,
   baseDatum 3 5 6 4,
   baseDatum 3 5 2 1,
   baseDatum 3 1 6 2,
   baseDatum 0 3 5 2,
   baseDatum 3 5 4 6,
   baseDatum 3 4 5 6,
   baseDatum 0 4 1 3,
   baseDatum 0 1 4 3,
   baseDatum 3 5 1 2,
   baseDatum 0 4 3 1,
   baseDatum 3 4 1 2,
   baseDatum 0 1 5 2,
   baseDatum 3 1 2 6,
   baseDatum 0 3 1 6,
   baseDatum 0 1 3 4,
   baseDatum 0 1 2 5,
   baseDatum 3 1 5 2,
   baseDatum 0 3 4 1,
   baseDatum 3 1 4 2,
   baseDatum 0 3 7 1,
   baseDatum 3 1 2 5,
   baseDatum 0 3 1 4,
   baseDatum 0 1 3 6,
   baseDatum 0 1 2 6,
   baseDatum 3 1 2 4,
   baseDatum 0 3 1 7,
   baseDatum 0 1 3 7,
   baseDatum 0 1 2 7]

/-- Every representative has invertible linear columns. -/
theorem heightTwoAffineList_bijective : ∀ p ∈ heightTwoAffineList,
    ∀ x, binaryImage (0, p.2) x = 0 → x = 0 := by
  have h : heightTwoAffineList.all (fun p =>
      decide (∀ x, binaryImage (0, p.2) x = 0 → x = 0)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

/-- The index of a three-bit vector in the explicit cube enumeration. -/
def binaryCubeIndex (x : Fin 3 → ZMod 2) : Fin 8 :=
  ⟨(x 0).val + 2*(x 1).val + 4*(x 2).val, by
    have h0 := ZMod.val_lt (x 0)
    have h1 := ZMod.val_lt (x 1)
    have h2 := ZMod.val_lt (x 2)
    omega⟩

/-- Eight values interpreted as a Boolean function on three coordinates. -/
def heightTwoTruthTable (v : Fin 8 → ZMod 2) (x : Fin 3 → ZMod 2) : ZMod 2 :=
  v (binaryCubeIndex x)

/-- A kernel-checked classification of all 256 Boolean functions on three bits. -/
theorem heightTwo_coordinate_classification : ∀ v : Fin 8 → ZMod 2,
    (∀ b, (Finset.univ.filter (fun x => heightTwoTruthTable v x = b)).card = 4) →
    (∀ u, (∀ x, heightTwoTruthTable v (binaryImage (u, ![binaryVec 1, binaryVec 2, binaryVec 4]) x) = heightTwoTruthTable v x) → u = 0) →
    heightTwoAffineList.any (fun p => decide (∀ x, heightTwoTruthTable v x = binaryTemplate (binaryImage p x))) = true := by
  decide +kernel

/-- The explicit cube enumeration is inverse to the coordinate index. -/
theorem binaryVec_cubeIndex : ∀ x : Fin 3 → ZMod 2,
    binaryVec (binaryCubeIndex x).val = x := by decide +kernel

/-- The coordinate columns encode translation by `u`. -/
theorem binaryImage_coordinate_translation : ∀ u x : Fin 3 → ZMod 2,
    binaryImage (u, ![binaryVec 1, binaryVec 2, binaryVec 4]) x = x + u := by
  decide +kernel

/-- On the minimal three-dimensional space, balance and essential dimension three
characterize exactly the affine orbit of the height-two template. -/
theorem isHeightTwoTree_coordinate_representation
    (f : (Fin 3 → ZMod 2) → ZMod 2) (hf : IsHeightTwoTree f) :
    ∃ e : (Fin 3 → ZMod 2) ≃ᵃ[ZMod 2] (Fin 3 → ZMod 2),
      ∀ x, baseTemplate (e x) = f x := by
  classical
  rw [isHeightTwoTree_iff_balanced_essentialDimension] at hf
  have hdim : Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := by simp
  have hpdim : Module.finrank (ZMod 2) (periodSubmodule f) = 0 := by
    have hd := essentialDimension_add_finrank_periodSubmodule f
    rw [hf.2, hdim] at hd
    omega
  have hper : periodSubmodule f = ⊥ := Submodule.finrank_eq_zero.mp hpdim
  let v : Fin 8 → ZMod 2 := fun i => f (binaryVec i.val)
  have hv (x : Fin 3 → ZMod 2) : heightTwoTruthTable v x = f x := by
    change f (binaryVec (binaryCubeIndex x).val) = f x
    rw [binaryVec_cubeIndex]
  have hc := heightTwo_coordinate_classification v
  have hb : ∀ b, (Finset.univ.filter (fun x => heightTwoTruthTable v x = b)).card = 4 := by
    intro b
    have h := hf.1 b
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fun] at h
    simpa only [hv, Fintype.card_subtype] using (show Fintype.card {x // f x = b} = 4 by omega)
  have hperiod : ∀ u, (∀ x, heightTwoTruthTable v
      (binaryImage (u, ![binaryVec 1, binaryVec 2, binaryVec 4]) x) = heightTwoTruthTable v x) → u = 0 := by
    intro u hu
    have hp : u ∈ periodSubmodule f := by
      intro x
      simpa only [hv, binaryImage_coordinate_translation] using hu x
    simpa only [hper, Submodule.mem_bot] using hp
  obtain ⟨p, hp, heq⟩ := List.any_eq_true.mp (hc hb hperiod)
  have hcol (x : Fin 3 → ZMod 2) : binaryImage (0, p.2) x = baseLinear p.2 x := by
    funext j
    simp [binaryImage, binaryAdd_eq, binaryMul_eq, baseLinear, Fin.sum_univ_three]
  have hinj : Function.Injective (baseLinearMap p.2) :=
    (injective_iff_map_eq_zero (baseLinearMap p.2)).2 fun x hx =>
      heightTwoAffineList_bijective p hp x (by simpa [hcol] using hx)
  let L := LinearEquiv.ofBijective (baseLinearMap p.2) (Finite.injective_iff_bijective.mp hinj)
  let e : (Fin 3 → ZMod 2) ≃ᵃ[ZMod 2] (Fin 3 → ZMod 2) :=
    affineEquivCoordinates.symm (p.1, L)
  refine ⟨e, ?_⟩
  intro x
  have hex (x : Fin 3 → ZMod 2) : e x = baseLinear p.2 x + p.1 := by
    simp [e, affineEquivCoordinates, L, add_comm]
  have hbim : binaryImage p x = baseLinear p.2 x + p.1 := by
    funext j
    simp [binaryImage, binaryAdd_eq, binaryMul_eq, baseLinear, Fin.sum_univ_three]
  have hh := (of_decide_eq_true heq) x
  simpa only [hv, binaryTemplate, binaryAdd_eq, binaryMul_eq, baseTemplate, hbim, hex] using hh.symm

/-- Every surjective affine image of the base template satisfies the intrinsic
height-two predicate. -/
theorem isHeightTwoTree_affinePullback {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (a : V →ᵃ[ZMod 2] (Fin 3 → ZMod 2)) (ha : Function.Surjective a) :
    IsHeightTwoTree (fun x => baseTemplate (a x)) := by
  classical
  letI := Fintype.ofFinite V
  rw [isHeightTwoTree_iff_balanced_essentialDimension]
  constructor
  · intro b
    have hc := affine_preimage_fiber_count a ha baseTemplate b
    rw [baseTemplate_fiber_card] at hc
    norm_num [Fintype.card_fun] at hc
    simp only [Nat.card_eq_fintype_card] at hc ⊢
    change 2 * Fintype.card {x : V // baseTemplate (a x) = b} = Fintype.card V
    omega
  · rw [essentialDimension_affineMap_precompose_periodFree baseTemplate baseTemplate_period_iff a ha]
    simp

/-- Surjective affine pullback preserves and reflects the height-two
predicate. The reverse balance implication follows from uniform finite fibers. -/
theorem isHeightTwoTree_affineMap_precompose_iff {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (f : W → ZMod 2) (a : V →ᵃ[ZMod 2] W) (ha : Function.Surjective a) :
    IsHeightTwoTree (fun x => f (a x)) ↔ IsHeightTwoTree f := by
  classical
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite W
  have hc := affine_preimage_fiber_count a ha f
  have hv : 0 < Fintype.card V := Fintype.card_pos
  have hw : 0 < Fintype.card W := Fintype.card_pos
  rw [isHeightTwoTree_iff_balanced_essentialDimension,
    isHeightTwoTree_iff_balanced_essentialDimension, essentialDimension_affineMap_precompose f a ha]
  constructor
  · rintro ⟨hb, hd⟩
    refine ⟨?_, hd⟩
    intro b
    have h := hc b
    have hb' := hb b
    simp only [Nat.card_eq_fintype_card] at h hb' ⊢
    nlinarith
  · rintro ⟨hb, hd⟩
    refine ⟨?_, hd⟩
    intro b
    have h := hc b
    have hb' := hb b
    simp only [Nat.card_eq_fintype_card] at h hb' ⊢
    nlinarith

/-- The intrinsic height-two definition is precisely the existing
surjective affine pullback family. This is the base API for the recursive bridge. -/
theorem isHeightTwoTree_iff_mem_affinePullbackFamily {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (f : V → ZMod 2) :
    IsHeightTwoTree f ↔ f ∈ affinePullbackFamily V baseTemplate := by
  classical
  constructor
  · intro hf
    let P := periodSubmodule f
    letI : Finite (V ⧸ P) := Finite.of_surjective P.mkQ P.mkQ_surjective
    let q := quotientFunction f P le_rfl
    have hq : IsHeightTwoTree q :=
      (isHeightTwoTree_affineMap_precompose_iff q P.mkQ.toAffineMap P.mkQ_surjective).mp hf
    have hdim : Module.finrank (ZMod 2) (V ⧸ P) = Module.finrank (ZMod 2) (Fin 3 → ZMod 2) := by
      rw [← essentialDimension_eq_finrank_quotient_periodSubmodule f]
      simp [hf.2.2]
    let e : (V ⧸ P) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) := LinearEquiv.ofFinrankEq _ _ hdim
    let g := fun x => q (e.symm x)
    have hg : IsHeightTwoTree g :=
      (isHeightTwoTree_affineMap_precompose_iff q e.symm.toAffineEquiv.toAffineMap e.symm.surjective).mpr hq
    obtain ⟨b, hb⟩ := isHeightTwoTree_coordinate_representation g hg
    let a := b.toAffineMap.comp (e.toAffineEquiv.toAffineMap.comp P.mkQ.toAffineMap)
    refine ⟨⟨a, b.surjective.comp (e.surjective.comp P.mkQ_surjective)⟩, ?_⟩
    funext x
    change baseTemplate (b (e (P.mkQ x))) = f x
    rw [hb]
    change q (e.symm (e (P.mkQ x))) = f x
    rw [e.symm_apply_apply]
    exact quotientFunction_mkQ f P le_rfl x
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact isHeightTwoTree_affinePullback a ha

attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype

/-- Lemma `lem:tree-structure`, part 4: exactly 56 intrinsic height-two
functions exist on every three-dimensional finite binary vector space. -/
theorem isHeightTwoTree_card_dimension_three {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (hd : Module.finrank (ZMod 2) V = 3) :
    Nat.card {f : V → ZMod 2 // IsHeightTwoTree f} = 56 := by
  classical
  have hc : Nat.card V=8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    norm_num
  have he (f : V → ZMod 2) : IsHeightTwoTree f ↔
      Nat.card {x : V // f x=1}=4 ∧ BooleanFunctions.vectorDegree f=2 := by
    constructor
    · intro hf
      have hb := hf.1 1
      exact ⟨by omega,hf.2.1⟩
    · rintro ⟨hb,hdeg⟩
      refine ⟨(isBalanced_iff_twice_support f).mpr (by omega),hdeg,?_⟩
      rw [essentialDimension_eq_finrank_quotient_periodSubmodule]
      exact (BooleanFunctions.balanced_vectorDegree_two_iff_essential_dimension_three
        f hd hb).mp hdeg
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact BooleanFunctions.balanced_vectorDegree_two_card hd

end BinaryFieldCounterexamples.Trees
