/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.DegreeStructure
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.PrescribedSpace
public import BinaryFieldCounterexamples.Counting.ComplementCount
public import BinaryFieldCounterexamples.Counting.SubspaceGaussianCount
/-!
# Counting intrinsic trees through their unique roots

The recursive step in Lemma 6.6 of Section 6.2 counts a root and its ordered
children. The fixed-root equivalence below is literal restriction to the two
slices and gluing along the root projection. The global equivalence uses
`IsTreeRoot.unique`, whose proof is the degree argument of Lemma 6.5, to ensure
that each parent occurs exactly once.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] Classical.propDecidable Classical.decEq
open Module
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U]

/-- Glue two Boolean children on the two slices of a fixed linear root. -/
def glueRootChildren (s : Dual (ZMod 2) U) (p : U) (hp : s p=1)
    (f g : s.ker → ZMod 2) : U → ZMod 2 :=
  fun x => if s x=0 then f (treeRootProjection s p hp x)
    else g (treeRootProjection s p hp x)

@[simp] theorem glueRootChildren_zeroSlice (s : Dual (ZMod 2) U)
    (p : U) (hp : s p=1) (f g : s.ker → ZMod 2) (x : s.ker) :
    glueRootChildren s p hp f g x=f x := by
  simp [glueRootChildren,show s x=0 from x.property]

@[simp] theorem glueRootChildren_oneSlice (s : Dual (ZMod 2) U)
    (p : U) (hp : s p=1) (f g : s.ker → ZMod 2) (x : s.ker) :
    glueRootChildren s p hp f g (p+x)=g x := by
  have hpj : treeRootProjection s p hp (p+x)=x := by
    simpa using treeRootProjection_apply_add s p hp x (1 : ZMod 2)
  simp [glueRootChildren,map_add,hp,show s x=0 from x.property,hpj]

/-- The ordered children permitted by Definition 6.3 at a fixed root. -/
def RootChildPairs (n : ℕ) (s : Dual (ZMod 2) U) :=
  {fg : (s.ker → ZMod 2) × (s.ker → ZMod 2) //
    IsTreeFunction (n+2) fg.1 ∧ IsTreeFunction (n+2) fg.2 ∧
      essentialDualSpace fg.1 ⊓ essentialDualSpace fg.2=⊥}

/-- Child pairs form a finite family on a finite binary space. -/
noncomputable def rootChildPairsFintype (n : ℕ) (s : Dual (ZMod 2) U) :
    Fintype (RootChildPairs n s) := by
  classical
  letI : Fintype s.ker := Fintype.ofFinite _
  unfold RootChildPairs
  exact Fintype.ofFinite _
attribute [local instance] rootChildPairsFintype

/-- Gluing admissible children supplies literal intrinsic root data. -/
theorem glueRootChildren_isTreeRoot (n : ℕ) (s : Dual (ZMod 2) U)
    (p : U) (hp : s p=1) (fg : RootChildPairs n s) :
    IsTreeRoot (n+3) (glueRootChildren s p hp fg.1.1 fg.1.2) s := by
  classical
  letI : Fintype s.ker := Fintype.ofFinite _
  have hs : s≠0 := by intro he; simpa [he] using hp
  have h₀ : (fun x : s.ker => glueRootChildren s p hp fg.1.1 fg.1.2 x)=fg.1.1 :=
    funext (glueRootChildren_zeroSlice s p hp _ _)
  have h₁ : (fun x : s.ker => glueRootChildren s p hp fg.1.1 fg.1.2 (p+x))=fg.1.2 :=
    funext (glueRootChildren_oneSlice s p hp _ _)
  refine ⟨by omega,hs,p,hp,essentialDualSpace fg.1.1,essentialDualSpace fg.1.2,
    fg.2.1.essentialDimension,fg.2.2.1.essentialDimension,fg.2.2.2,?_,?_,?_,?_⟩
  · simpa only [show n+3-1=n+2 by omega,h₀] using fg.2.1
  · exact congrArg essentialDualSpace h₀
  · simpa only [show n+3-1=n+2 by omega,h₁] using fg.2.2.1
  · exact congrArg essentialDualSpace h₁

/-- A fixed-root parent is exactly its ordered pair of literal slice functions.
The point on the one-slice is chosen once, not counted as additional data. -/
noncomputable def fixedRootTreeFunctionsEquivChildren (n : ℕ)
    (s : Dual (ZMod 2) U) (p : U) (hp : s p=1) :
    {φ : U → ZMod 2 // IsTreeRoot (n+3) φ s} ≃ RootChildPairs n s := by
  classical
  refine {
    toFun := fun φ => ⟨(fun x => φ.1 x,fun x => φ.1 (p+x)),φ.2.children_at p hp⟩
    invFun := fun fg => ⟨glueRootChildren s p hp fg.1.1 fg.1.2,
      glueRootChildren_isTreeRoot n s p hp fg⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro φ
    apply Subtype.ext
    funext x
    change (if s x=0 then φ.1 (treeRootProjection s p hp x)
      else φ.1 (p+treeRootProjection s p hp x))=φ.1 x
    rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) (s x) with hx | hx
    · simp [hx,treeRootProjection]
    · simp [hx,treeRootProjection]
  · intro fg
    apply Subtype.ext
    apply Prod.ext <;> funext x
    · exact glueRootChildren_zeroSlice s p hp _ _ x
    · exact glueRootChildren_oneSlice s p hp _ _ x

/-- Nonzero binary linear functionals are the possible intrinsic roots. -/
def TreeRootFunctionals (U : Type*) [AddCommGroup U] [Module (ZMod 2) U] :=
  {s : Dual (ZMod 2) U // s≠0}

/-- The nonzero dual population is finite. -/
noncomputable def treeRootFunctionalsFintype : Fintype (TreeRootFunctionals U) := by
  classical
  letI : Fintype (Dual (ZMod 2) U) := Fintype.ofInjective
    (fun f : Dual (ZMod 2) U => (f : U → ZMod 2)) DFunLike.coe_injective
  unfold TreeRootFunctionals
  exact Fintype.ofFinite _
attribute [local instance] treeRootFunctionalsFintype

/-- In dimension `d` the root factor is exactly `2^d-1`. -/
theorem treeRootFunctionals_card :
    Nat.card (TreeRootFunctionals U)=2^(finrank (ZMod 2) U)-1 := by
  classical
  letI : Fintype (Dual (ZMod 2) U) := Fintype.ofInjective
    (fun f : Dual (ZMod 2) U => (f : U → ZMod 2)) DFunLike.coe_injective
  change Nat.card {s : Dual (ZMod 2) U // s≠0}=_
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_subtype_eq,
    Module.card_eq_pow_finrank (K := ZMod 2),Subspace.dual_finrank_eq]
  norm_num

/-- Every nonzero binary functional has a nonempty one-slice. -/
theorem exists_treeRootPoint (s : TreeRootFunctionals U) : ∃ p : U, s.1 p=1 := by
  classical
  by_contra hn
  apply s.2
  ext x
  rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) (s.1 x) with hx | hx
  · exact hx
  · exact False.elim (hn ⟨x,hx⟩)

/-- Fix a point in each root's one-slice, without introducing multiplicity. -/
noncomputable def treeRootPoint (s : TreeRootFunctionals U) : U :=
  (exists_treeRootPoint s).choose

/-- The chosen point lies on the one-slice. -/
theorem treeRootPoint_spec (s : TreeRootFunctionals U) : s.1 (treeRootPoint s)=1 := by
  exact (exists_treeRootPoint s).choose_spec

/-- A nonzero intrinsic root cuts the ambient dimension by one. -/
theorem treeRootKernel_finrank (s : TreeRootFunctionals U) :
    finrank (ZMod 2) s.1.ker+1=finrank (ZMod 2) U := by
  have hsurj : Function.Surjective s.1 := by
    intro c
    rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) c with rfl | rfl
    · exact ⟨0,map_zero _⟩
    · exact ⟨treeRootPoint s,treeRootPoint_spec s⟩
  have he := s.1.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,Module.finrank_self] at he
  omega

/-- Under root uniqueness, every intrinsic tree corresponds to exactly one
nonzero root and one ordered pair of children on its two slices. -/
noncomputable def treeFunctionsEquivRootChildrenOfUnique (n : ℕ)
    (hunique : ∀ (φ : U → ZMod 2) (s t : Dual (ZMod 2) U),
      IsTreeRoot (n+3) φ s → IsTreeRoot (n+3) φ t → s=t) :
    {φ : U → ZMod 2 // IsTreeFunction (n+3) φ} ≃
      Σ s : TreeRootFunctionals U, RootChildPairs n s.1 := by
  classical
  let F : (Σ s : TreeRootFunctionals U, RootChildPairs n s.1) →
      {φ : U → ZMod 2 // IsTreeFunction (n+3) φ} := fun z =>
    ⟨glueRootChildren z.1.1 (treeRootPoint z.1) (treeRootPoint_spec z.1)
      z.2.1.1 z.2.1.2,
      (glueRootChildren_isTreeRoot n z.1.1 (treeRootPoint z.1)
        (treeRootPoint_spec z.1) z.2).isTreeFunction⟩
  refine (Equiv.ofBijective F ⟨?_,?_⟩).symm
  · rintro ⟨s,fg⟩ ⟨t,ij⟩ he
    have he' := congrArg Subtype.val he
    have hs := glueRootChildren_isTreeRoot n s.1 (treeRootPoint s) (treeRootPoint_spec s) fg
    have ht := glueRootChildren_isTreeRoot n t.1 (treeRootPoint t) (treeRootPoint_spec t) ij
    change glueRootChildren s.1 (treeRootPoint s) (treeRootPoint_spec s) fg.1.1 fg.1.2=
      glueRootChildren t.1 (treeRootPoint t) (treeRootPoint_spec t) ij.1.1 ij.1.2 at he'
    rw [←he'] at ht
    have hst : s=t := Subtype.ext (hunique _ s.1 t.1 hs ht)
    subst t
    have hfg : fg=ij :=
      (fixedRootTreeFunctionsEquivChildren n s.1 (treeRootPoint s)
        (treeRootPoint_spec s)).symm.injective (Subtype.ext he')
    exact congrArg (Sigma.mk s) hfg
  · intro φ
    obtain ⟨s,hs⟩ := (isTreeFunction_succ_iff_exists_root n φ.1).mp φ.2
    let z : TreeRootFunctionals U := ⟨s,hs.nonzero⟩
    let E := fixedRootTreeFunctionsEquivChildren n z.1 (treeRootPoint z) (treeRootPoint_spec z)
    refine ⟨⟨z,E ⟨φ.1,hs⟩⟩,?_⟩
    apply Subtype.ext
    exact congrArg (fun f : {ψ : U → ZMod 2 // IsTreeRoot (n+3) ψ z.1} => f.1)
      (E.left_inv ⟨φ.1,hs⟩)

/-- Ordered independent essential-coordinate spaces of equal dimension. -/
def IndependentChildSpaces (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    (r : ℕ) :=
  {E : Submodule (ZMod 2) (Dual (ZMod 2) W) ×
      Submodule (ZMod 2) (Dual (ZMod 2) W) //
    finrank (ZMod 2) E.1=r ∧ finrank (ZMod 2) E.2=r ∧ E.1 ⊓ E.2=⊥}

/-- The possible essential-space pairs form a literal finite family. -/
noncomputable def independentChildSpacesFintype (r : ℕ) :
    Fintype (IndependentChildSpaces U r) := by
  classical
  letI : Fintype (Dual (ZMod 2) U) := Fintype.ofInjective
    (fun f : Dual (ZMod 2) U => (f : U → ZMod 2)) DFunLike.coe_injective
  unfold IndependentChildSpaces
  exact Fintype.ofFinite _
attribute [local instance] independentChildSpacesFintype

/-- In dimension `2r`, an ordered independent pair is a first `r`-space
followed by a complement; no coordinate bases are counted. -/
noncomputable def independentChildSpacesEquivComplements (r : ℕ)
    (hd : finrank (ZMod 2) U=2*r) :
    IndependentChildSpaces U r ≃
      Σ E : subspacesOfFinrank (ZMod 2) (Dual (ZMod 2) U) r,
        {F : Submodule (ZMod 2) (Dual (ZMod 2) U) // IsCompl E.1 F} := by
  classical
  have hdual : finrank (ZMod 2) (Dual (ZMod 2) U)=2*r := by
    rw [Subspace.dual_finrank_eq,hd]
  refine {
    toFun := fun E => ⟨⟨E.1.1,E.2.1⟩,⟨E.1.2,?_⟩⟩
    invFun := fun E => ⟨(E.1.1,E.2.1),E.1.2,?_,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (Submodule.isCompl_iff_disjoint _ _ (by rw [hdual,E.2.1,E.2.2.1]; omega)).mpr
      (disjoint_iff.mpr E.2.2.2)
  · change finrank (ZMod 2) E.2.1=r
    have he := Submodule.finrank_add_eq_of_isCompl E.2.2
    rw [hdual,E.1.2] at he
    omega
  · exact disjoint_iff.mp E.2.2.disjoint
  · intro E; rfl
  · intro E; rfl

/-- The paper's Gaussian and complementary-space factor counts literal
ordered essential spaces, rather than representations of those spaces. -/
theorem independentChildSpaces_card (r : ℕ) (hd : finrank (ZMod 2) U=2*r) :
    Nat.card (IndependentChildSpaces U r)=
      gaussianBinomial 2 (2*r) r*2^(r^2) := by
  classical
  letI : Fintype (Dual (ZMod 2) U) := Fintype.ofInjective
    (fun f : Dual (ZMod 2) U => (f : U → ZMod 2)) DFunLike.coe_injective
  letI : Fintype (subspacesOfFinrank (ZMod 2) (Dual (ZMod 2) U) r) := Fintype.ofFinite _
  rw [Nat.card_congr (independentChildSpacesEquivComplements r hd),Nat.card_sigma]
  have hc (E : subspacesOfFinrank (ZMod 2) (Dual (ZMod 2) U) r) :
      Nat.card {F : Submodule (ZMod 2) (Dual (ZMod 2) U) // IsCompl E.1 F}=2^(r^2) := by
    rw [complements_natCard_eq_pow,Subspace.dual_finrank_eq,hd,E.2]
    norm_num [show 2*r-r=r by omega,pow_two]
  simp_rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,subspacesOfFinrank_card_eq_gaussianBinomial r
    (by rw [Subspace.dual_finrank_eq,hd]; omega),Subspace.dual_finrank_eq,hd]
  norm_num

/-- Extract the actual essential spaces of the two children. -/
noncomputable def rootChildEssentialPair (n : ℕ) (s : Dual (ZMod 2) U)
    (fg : RootChildPairs n s) : IndependentChildSpaces s.ker (2^(n+2)-1) := by
  classical
  letI : Fintype s.ker := Fintype.ofFinite _
  exact ⟨(essentialDualSpace fg.1.1,essentialDualSpace fg.1.2),
    fg.2.1.essentialDimension,fg.2.2.1.essentialDimension,fg.2.2.2⟩

/-- At prescribed essential spaces, the children are chosen independently. -/
noncomputable def rootChildEssentialFiberEquiv (n : ℕ) (s : Dual (ZMod 2) U)
    (E : IndependentChildSpaces s.ker (2^(n+2)-1)) :
    {fg : RootChildPairs n s // rootChildEssentialPair n s fg=E} ≃
      {f : s.ker → ZMod 2 // IsTreeFunction (n+2) f ∧ essentialDualSpace f=E.1.1} ×
      {g : s.ker → ZMod 2 // IsTreeFunction (n+2) g ∧ essentialDualSpace g=E.1.2} := by
  classical
  refine {
    toFun := fun fg => (⟨fg.1.1.1,fg.1.2.1,?_⟩,⟨fg.1.1.2,fg.1.2.2.1,?_⟩)
    invFun := fun fg => ⟨⟨(fg.1.1,fg.2.1),fg.1.2.1,fg.2.2.1,?_⟩,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact congrArg (fun E => E.1.1) fg.2
  · exact congrArg (fun E => E.1.2) fg.2
  · rw [fg.1.2.2,fg.2.2.2]
    exact E.2.2.2
  · apply Subtype.ext
    exact Prod.ext fg.1.2.2 fg.2.2.2
  · intro fg; rfl
  · intro fg; rfl

/-- Count the child pair by its two literal essential spaces and then the two
prescribed-space tree populations, exactly as in Lemma 6.6. -/
theorem rootChildPairs_card (n : ℕ) (s : Dual (ZMod 2) U)
    (hd : finrank (ZMod 2) s.ker=2*(2^(n+2)-1)) :
    Nat.card (RootChildPairs n s)=
      gaussianBinomial 2 (2*(2^(n+2)-1)) (2^(n+2)-1)*
        2^((2^(n+2)-1)^2)*intrinsicTreeMinimalCount (n+2)^2 := by
  classical
  letI : Fintype s.ker := Fintype.ofFinite _
  letI : Fintype (IndependentChildSpaces s.ker (2^(n+2)-1)) := Fintype.ofFinite _
  rw [←Nat.card_congr (Equiv.sigmaFiberEquiv (rootChildEssentialPair n s)),Nat.card_sigma]
  have hc (E : IndependentChildSpaces s.ker (2^(n+2)-1)) :
      Nat.card {fg : RootChildPairs n s // rootChildEssentialPair n s fg=E}=
        intrinsicTreeMinimalCount (n+2)^2 := by
    rw [Nat.card_congr (rootChildEssentialFiberEquiv n s E),Nat.card_prod,
      isTreeFunction_prescribed_essentialDualSpace_count n E.1.1 E.2.1,
      isTreeFunction_prescribed_essentialDualSpace_count n E.1.2 E.2.2.1]
    simp [intrinsicTreeMinimalCount,pow_two]
  simp_rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,independentChildSpaces_card _ hd]

/-- Literal recursive counting on a minimal domain. The only uniqueness
premise used is uniqueness of the intrinsic root; the degree proof supplies it
in `isTreeFunction_count_succ_by_root` below. -/
theorem isTreeFunction_count_succ_of_unique (n : ℕ)
    (hd : finrank (ZMod 2) U=2^(n+3)-1)
    (hunique : ∀ (φ : U → ZMod 2) (s t : Dual (ZMod 2) U),
      IsTreeRoot (n+3) φ s → IsTreeRoot (n+3) φ t → s=t) :
    Nat.card {φ : U → ZMod 2 // IsTreeFunction (n+3) φ}=
      (2^(2^(n+3)-1)-1)*gaussianBinomial 2 (2*(2^(n+2)-1)) (2^(n+2)-1)*
        2^((2^(n+2)-1)^2)*intrinsicTreeMinimalCount (n+2)^2 := by
  classical
  rw [Nat.card_congr (treeFunctionsEquivRootChildrenOfUnique n hunique),Nat.card_sigma]
  have hk (s : TreeRootFunctionals U) :
      finrank (ZMod 2) s.1.ker=2*(2^(n+2)-1) := by
    have he := treeRootKernel_finrank s
    have hp : 1≤(2:ℕ)^(n+2) := Nat.one_le_pow _ _ (by decide)
    rw [hd,show n+3=n+2+1 by omega,pow_succ] at he
    omega
  simp_rw [rootChildPairs_card n _ (hk _)]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,treeRootFunctionals_card,hd]
  ring

/-- The actual essential space assigns each tree to one Grassmannian fiber. -/
noncomputable def intrinsicTreeEssentialSpace (h : ℕ)
    (φ : {φ : U → ZMod 2 // IsTreeFunction h φ}) :
    subspacesOfFinrank (ZMod 2) (Dual (ZMod 2) U) (2^h-1) :=
  ⟨essentialDualSpace φ.1,φ.2.essentialDimension⟩

/-- The fiber over an essential space is the literal prescribed-space family. -/
noncomputable def intrinsicTreeEssentialFiberEquiv (h : ℕ)
    (E : subspacesOfFinrank (ZMod 2) (Dual (ZMod 2) U) (2^h-1)) :
    {φ : {φ : U → ZMod 2 // IsTreeFunction h φ} // intrinsicTreeEssentialSpace h φ=E} ≃
      {φ : U → ZMod 2 // IsTreeFunction h φ ∧ essentialDualSpace φ=E.1} := by
  refine {
    toFun := fun φ => ⟨φ.1.1,φ.1.2,congrArg Subtype.val φ.2⟩
    invFun := fun φ => ⟨⟨φ.1,φ.2.1⟩,Subtype.ext φ.2.2⟩
    left_inv := by intro φ; rfl
    right_inv := by intro φ; rfl }

/-- Lemma 6.6's factorization `B_h(d)=[d choose t_h]_2 C_h`, proved by
partitioning intrinsic functions according to their actual essential space. -/
theorem isTreeFunction_count_gaussian_by_essentialSpace (n : ℕ)
    (hd : 2^(n+2)-1≤finrank (ZMod 2) U) :
    Nat.card {φ : U → ZMod 2 // IsTreeFunction (n+2) φ}=
      gaussianBinomial 2 (finrank (ZMod 2) U) (2^(n+2)-1)*
        intrinsicTreeMinimalCount (n+2) := by
  classical
  letI : Fintype (Dual (ZMod 2) U) := Fintype.ofInjective
    (fun f : Dual (ZMod 2) U => (f : U → ZMod 2)) DFunLike.coe_injective
  letI : Fintype (subspacesOfFinrank (ZMod 2) (Dual (ZMod 2) U) (2^(n+2)-1)) :=
    Fintype.ofFinite _
  rw [←Nat.card_congr (Equiv.sigmaFiberEquiv (intrinsicTreeEssentialSpace (n+2))),
    Nat.card_sigma]
  have hc (E : subspacesOfFinrank (ZMod 2) (Dual (ZMod 2) U) (2^(n+2)-1)) :
      Nat.card {φ : {φ : U → ZMod 2 // IsTreeFunction (n+2) φ} //
        intrinsicTreeEssentialSpace (n+2) φ=E}=intrinsicTreeMinimalCount (n+2) := by
    rw [Nat.card_congr (intrinsicTreeEssentialFiberEquiv (n+2) E),
      isTreeFunction_prescribed_essentialDualSpace_count n E.1 E.2]
    rfl
  simp_rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,subspacesOfFinrank_card_eq_gaussianBinomial _
    (by rwa [Subspace.dual_finrank_eq]),Subspace.dual_finrank_eq]
  norm_num

/-- Literal intrinsic supports are closed under complementation. -/
theorem intrinsicTreeSupportFamily_complement_by_tree_complement (h : ℕ) (S : Finset U)
    (hS : S ∈ intrinsicTreeSupportFamily U h) :
    Finset.univ \ S ∈ intrinsicTreeSupportFamily U h := by
  classical
  obtain ⟨φ,hφ,rfl⟩ := (mem_intrinsicTreeSupportFamily h S).mp hS
  refine (mem_intrinsicTreeSupportFamily h _).mpr ⟨_,hφ.complement,?_⟩
  ext x
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,binarySupport,
    Finset.mem_filter,Finset.mem_univ,true_and]
  rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) (φ x) with hx | hx <;>
    simp [hx,show (1 : ZMod 2)+1=0 by decide]

/-- The incidence clause of Lemma 6.6 by the paper's complementation pairing:
a point belongs to exactly one support in each complementary pair. -/
theorem intrinsicTreeSupportFamily_point_incidence_by_complement (h : ℕ) (x : U) :
    2*((intrinsicTreeSupportFamily U h).filter (fun S => x ∈ S)).card=
      (intrinsicTreeSupportFamily U h).card := by
  classical
  let F := intrinsicTreeSupportFamily U h
  have he : (F.filter fun S => x ∈ S).card=(F.filter fun S => x ∉ S).card := by
    apply Finset.card_bij (fun S _ => Finset.univ \ S)
    · intro S hS
      obtain ⟨hSF,hx⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr ⟨intrinsicTreeSupportFamily_complement_by_tree_complement h S hSF,
        by simp [hx]⟩
    · intro S hS T hT hST
      have hh := congrArg (fun S : Finset U => Finset.univ \ S) hST
      simpa using hh
    · intro S hS
      obtain ⟨hSF,hx⟩ := Finset.mem_filter.mp hS
      refine ⟨Finset.univ \ S,Finset.mem_filter.mpr
        ⟨intrinsicTreeSupportFamily_complement_by_tree_complement h S hSF,by simp [hx]⟩,?_⟩
      simp
  have ht := Finset.card_filter_add_card_filter_not (s := F) (p := fun S => x ∈ S)
  change 2*(F.filter (fun S => x ∈ S)).card=F.card
  omega

/-- Lemma 6.6's root-and-children parametrization, with uniqueness discharged
by the top-degree monomial proof of Lemma 6.5. -/
noncomputable def treeFunctionsEquivRootChildren (n : ℕ) :
    {φ : U → ZMod 2 // IsTreeFunction (n+3) φ} ≃
      Σ s : TreeRootFunctionals U, RootChildPairs n s.1 :=
  treeFunctionsEquivRootChildrenOfUnique n (fun _ _ _ hs ht => hs.unique ht)

/-- Lemma 6.6's minimal-domain recursion, proved by counting unique roots,
ordered complementary essential spaces, and independent prescribed-space
children. The injectivity step uses the paper's degree proof of root uniqueness. -/
theorem isTreeFunction_count_succ_by_root (n : ℕ)
    (hd : finrank (ZMod 2) U=2^(n+3)-1) :
    Nat.card {φ : U → ZMod 2 // IsTreeFunction (n+3) φ}=
      (2^(2^(n+3)-1)-1)*gaussianBinomial 2 (2*(2^(n+2)-1)) (2^(n+2)-1)*
        2^((2^(n+2)-1)^2)*intrinsicTreeMinimalCount (n+2)^2 := by
  exact isTreeFunction_count_succ_of_unique n hd (fun _ _ _ hs ht => hs.unique ht)

/-- The numerical `C_h` recurrence is a consequence of the literal intrinsic
root count, not merely an identity between frame products. Together with
`isTreeFunction_two_count`, this is the paper's recursive counting argument. -/
theorem intrinsicTreeMinimalCount_succ_by_root (n : ℕ) :
    let r := 2^(n+2)-1
    intrinsicTreeMinimalCount (n+3)=
      (2^(2^(n+3)-1)-1)*gaussianBinomial 2 (2*r) r*2^(r^2)*
        intrinsicTreeMinimalCount (n+2)^2 := by
  letI := templateSpaceAddCommGroup (n+1)
  letI := templateSpaceModule (n+1)
  letI := templateSpaceFintype (n+1)
  have hd : finrank (ZMod 2) (TemplateSpace (n+1))=2^(n+3)-1 := by
    simpa only [show n+1+2=n+3 by omega] using templateSpace_finrank (n+1)
  have h := isTreeFunction_count_succ_by_root (U := TemplateSpace (n+1)) n hd
  have hc : Nat.card {φ : TemplateSpace (n+1) → ZMod 2 // IsTreeFunction (n+3) φ}=
      intrinsicTreeMinimalCount (n+3) := by
    have hcount := isTreeFunction_count (V := TemplateSpace (n+1)) (n+1)
      (by rw [hd])
    simpa only [show n+1+2=n+3 by omega,hd,intrinsicTreeMinimalCount] using hcount
  exact hc.symm.trans h

end BinaryFieldCounterexamples.Trees
