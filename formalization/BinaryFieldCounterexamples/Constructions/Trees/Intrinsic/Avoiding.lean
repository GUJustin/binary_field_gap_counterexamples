/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.DegreeStructure
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingCounts
public import BinaryFieldCounterexamples.Counting.TreeAsymptotics
/-!
# Intrinsic trees avoiding a subspace

Definition 6.8 selects the zero child recursively, rather than merely asking
that a tree vanish on the subspace. The bridge to the canonical coordinate
family identifies exactly the functions counted in Lemma 6.9.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Trees
set_option backward.isDefEq.respectTransparency false
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype

/-- Definition 6.8: height-two trees vanish on `W`; at larger heights the
intrinsic root annihilates `W` and its literal zero-slice child recursively
avoids the copy of `W` in the root kernel. Heights below two are excluded.
The definition makes sense for every subspace; the count theorem supplies the
paper's codimension hypothesis. -/
def IsAvoidingTree : (h : ℕ) → {U : Type*} → [AddCommGroup U] →
    [Module (ZMod 2) U] → [Finite U] → Submodule (ZMod 2) U → (U → ZMod 2) → Prop
  | 0, _, _, _, _, _, _ => False
  | 1, _, _, _, _, _, _ => False
  | 2, _, _, _, _, W, φ => IsTreeFunction 2 φ ∧ ∀ x : W, φ x = 0
  | n+3, _, _, _, _, W, φ =>
      ∃ s, IsTreeRoot (n+3) φ s ∧ W ≤ s.ker ∧
        IsAvoidingTree (n+2) (W.comap s.ker.subtype) (fun x : s.ker => φ x)

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

/-- Definition 6.8's recursive avoiding condition includes the actual
Definition 6.3 tree predicate. -/
theorem IsAvoidingTree.isTreeFunction {h : ℕ} {W : Submodule (ZMod 2) U}
    {φ : U → ZMod 2} (hφ : IsAvoidingTree h W φ) : IsTreeFunction h φ := by
  cases h with
  | zero => exact False.elim hφ
  | succ h => cases h with
    | zero => exact False.elim hφ
    | succ h => cases h with
      | zero => exact hφ.1
      | succ n => exact hφ.choose_spec.1.isTreeFunction

/-- The sentence after Definition 6.8: an intrinsic avoiding tree vanishes
on the prescribed subspace, so its support is disjoint from that subspace. -/
theorem IsAvoidingTree.vanishes {h : ℕ} {W : Submodule (ZMod 2) U}
    {φ : U → ZMod 2} (hφ : IsAvoidingTree h W φ) (x : W) : φ x = 0 := by
  induction h using Nat.twoStepInduction generalizing U with
  | zero => exact False.elim hφ
  | one => exact False.elim hφ
  | more n ih ih' =>
    cases n with
    | zero => exact hφ.2 x
    | succ n =>
      obtain ⟨s,hs,hW,hchild⟩ := hφ
      exact ih' hchild ⟨⟨x,hW x.property⟩,x.property⟩

/-- The height-two case of Definition 6.8 admits linear template coordinates:
a vanishing origin is normalized using the zero-fiber stabilizer, preserving
all values of the literal function. -/
theorem exists_linear_pullback_of_tree_origin_zero (n : ℕ) (φ : U → ZMod 2)
    (hφ : IsTreeFunction (n+2) φ) (hzero : φ 0=0) :
    ∃ L : U →ₗ[ZMod 2] TemplateSpace n, Function.Surjective L ∧
      (fun x => template n (L x))=φ := by
  obtain ⟨⟨a,ha⟩,hfun⟩ := (isTreeFunction_iff_affinePullbackFamily n φ).mp hφ
  have hbase : template n (a 0)=0 := (congrFun hfun 0).trans hzero
  obtain ⟨e,he⟩ := template_stabilizer_zero_image n (a 0) hbase
  let b : U →ᵃ[ZMod 2] TemplateSpace n := e.1.symm.toAffineMap.comp a
  have hb0 : b 0=0 := by
    change e.1.symm (a 0)=0
    rw [←he]
    exact e.1.symm_apply_apply 0
  have hb (x : U) : b.linear x=b x := by
    have h := b.map_vadd (0:U) x
    simpa [hb0] using h.symm
  refine ⟨b.linear,b.linear_surjective_iff.mpr (e.1.symm.surjective.comp ha),?_⟩
  funext x
  rw [hb]
  have hstab := (mem_affineFunctionStabilizer (template n) e.1).mp e.2 (e.1.symm (a x))
  simp only [AffineEquiv.apply_symm_apply] at hstab
  exact hstab.symm.trans (congrFun hfun x)

/-- Definition 6.8 at height two is exactly the literal vanishing base family
used to prove the first formula in Lemma 6.9. -/
theorem isAvoidingTree_two_iff (W : Submodule (ZMod 2) U) (φ : U → ZMod 2) :
    IsAvoidingTree 2 W φ ↔ φ ∈ avoidingTreeFamily 0 W := by
  constructor
  · rintro ⟨hφ,hW⟩
    obtain ⟨L,hL,hfun⟩ := exists_linear_pullback_of_tree_origin_zero 0 φ hφ (hW 0)
    apply (mem_avoidingTreeFamily_iff 0 W φ).mpr
    refine ⟨L,hL,?_,hfun⟩
    intro x
    exact (congrFun hfun x).trans (hW x)
  · intro hφ
    obtain ⟨L,hL,hcore,hfun⟩ := (mem_avoidingTreeFamily_iff 0 W φ).mp hφ
    refine ⟨(isTreeFunction_iff_affinePullbackFamily 0 φ).mpr
      ⟨⟨L.toAffineMap,hL⟩,hfun⟩,?_⟩
    intro x
    exact (congrFun hfun x).symm.trans (hcore x)

/-- Definition 6.8's recursive assembly uses linear coordinates for the
avoiding zero child and affine coordinates for the unrestricted one child.
Its affine offset is multiplied by the root bit, giving a linear parent map. -/
def avoidingRootLinearMap {T : Type*} [AddCommGroup T] [Module (ZMod 2) T]
    (s : Module.Dual (ZMod 2) U) (p : U) (hp : s p=1)
    (a : s.ker →ₗ[ZMod 2] T) (b : s.ker →ᵃ[ZMod 2] T) :
    U →ₗ[ZMod 2] (ZMod 2 × T × T) :=
  s.prod ((a.comp (treeRootProjection s p hp)).prod
    (b.linear.comp (treeRootProjection s p hp) + s.smulRight (b 0)))

omit [Finite U] in
/-- The recursive coordinates in Definition 6.8 are surjective when the child
essential spaces are disjoint, as used in Lemma 6.9's recurrence. -/
theorem avoidingRootLinearMap_surjective {T : Type*} [AddCommGroup T]
    [Module (ZMod 2) T] (s : Module.Dual (ZMod 2) U) (p : U) (hp : s p=1)
    (a : s.ker →ₗ[ZMod 2] T) (b : s.ker →ᵃ[ZMod 2] T)
    (hab : Function.Surjective (a.prod b.linear)) :
    Function.Surjective (avoidingRootLinearMap s p hp a b) := by
  rintro ⟨c,u,v⟩
  obtain ⟨x,hx⟩ := hab (u,v-c • b 0)
  refine ⟨c • p+x,?_⟩
  have hsel : s (c • p+x)=c := by simp [hp,show s x=0 from x.property]
  apply Prod.ext
  · exact hsel
  · apply Prod.ext
    · simpa [avoidingRootLinearMap] using congrArg Prod.fst hx
    · change b.linear (treeRootProjection s p hp (c • p+x)) +
        s (c • p+x) • b 0=v
      rw [treeRootProjection_apply_add,hsel,show b.linear x=v-c • b 0 from congrArg Prod.snd hx]
      abel

omit [Finite U] in
/-- The recursive linear parent coordinates recover the literal function of
Definition 6.8 on both root slices. -/
theorem avoidingRootLinearMap_template (n : ℕ) (φ : U → ZMod 2)
    (s : Module.Dual (ZMod 2) U) (p : U) (hp : s p=1)
    (a : s.ker →ₗ[ZMod 2] TemplateSpace n)
    (b : s.ker →ᵃ[ZMod 2] TemplateSpace n)
    (ha : (fun x => template n (a x))=(fun x : s.ker => φ x))
    (hb : (fun x => template n (b x))=(fun x : s.ker => φ (p+x))) :
    (fun x => template (n+1) (avoidingRootLinearMap s p hp a b x))=φ := by
  funext x
  rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) (s x) with hx | hx
  · change (if s x=0 then template n (a (treeRootProjection s p hp x)) else _) = φ x
    rw [hx,ite_eq_left rfl]
    exact (congrFun ha (treeRootProjection s p hp x)).trans
      (by change φ (x-s x • p)=φ x; simp [hx])
  · change (if s x=0 then _ else template n
      (b.linear (treeRootProjection s p hp x)+s x • b 0))=φ x
    rw [hx,ite_eq_right one_ne_zero,one_smul]
    have hbx : b.linear (treeRootProjection s p hp x)+b 0 =
        b (treeRootProjection s p hp x) := by
      simpa using (b.map_vadd (0:s.ker) (treeRootProjection s p hp x)).symm
    rw [hbx]
    exact (congrFun hb (treeRootProjection s p hp x)).trans
      (by change φ (p+(x-s x • p))=φ x; rw [hx,one_smul]; congr 1; abel)

theorem frame_first_isTreeRoot (n : ℕ) (L : U →ₗ[ZMod 2] TemplateSpace (n+1))
    (hL : Function.Surjective L) :
    IsTreeRoot (n+3) (fun x => template (n+1) (L x))
      ((LinearMap.fst (ZMod 2) (ZMod 2) (TemplateSpace n × TemplateSpace n)).comp L) := by
  let : Fintype U := Fintype.ofFinite _
  let s : Module.Dual (ZMod 2) U :=
    (LinearMap.fst (ZMod 2) (ZMod 2) (TemplateSpace n × TemplateSpace n)).comp L
  have hs : s≠0 := by
    obtain ⟨x,hx⟩ := hL (1,0,0)
    intro he
    have hh : s x=1 := congrArg Prod.fst hx
    simpa [he] using hh
  have htree : IsTreeFunction (n+3) (fun x => template (n+1) (L x)) :=
    (isTreeFunction_iff_affinePullbackFamily (n+1) _).mpr ⟨⟨L.toAffineMap,hL⟩,rfl⟩
  apply (isTreeRoot_iff_degree htree (by omega) s).mpr
  refine ⟨hs,?_⟩
  exact (BooleanFunctions.root_degree_characterization_affinePullback
    (V := TemplateSpace n) (W := TemplateSpace n) (template n) (template n)
    L.toAffineMap hL s (fun _ => rfl) s hs (by omega : 2≤n+2)
    (template_vectorDegree n) (template_vectorDegree n)).mpr rfl

/-- Definition 6.8's intrinsic avoiding functions are precisely the canonical
surjective linear pullbacks used in Lemma 6.9. The equality holds for every
subspace, without assuming its codimension in advance. -/
theorem isAvoidingTree_iff_avoidingTreeFamily (n : ℕ)
    (W : Submodule (ZMod 2) U) (φ : U → ZMod 2) :
    IsAvoidingTree (n+2) W φ ↔ φ ∈ avoidingTreeFamily n W := by
  induction n generalizing U with
  | zero => exact isAvoidingTree_two_iff W φ
  | succ n ih =>
    constructor
    · rintro ⟨s,hs,hW,hchild⟩
      obtain ⟨L₀,hL₀,hcore,hfun₀⟩ := (mem_avoidingTreeFamily_iff n _ _).mp
        ((ih _ _).mp hchild)
      obtain ⟨_,_,p,hp,L₀',L₁',hd₀,hd₁,hdisj,h₀,hE₀,h₁,hE₁⟩ := hs
      simp only [show n+3-1=n+2 by omega] at h₀ h₁
      obtain ⟨⟨b,hb⟩,hfun₁⟩ := (isTreeFunction_iff_affinePullbackFamily n _).mp h₁
      have hea := essentialDualSpace_affineMap_precompose_periodFree
        (template n) (template_period_iff n) L₀.toAffineMap hL₀
      have heb := essentialDualSpace_affineMap_precompose_periodFree
        (template n) (template_period_iff n) b hb
      change essentialDualSpace (fun x => template n (L₀ x))=L₀.ker.dualAnnihilator at hea
      change (fun x => template n (b x))=(fun x : s.ker => φ (p+x)) at hfun₁
      rw [hfun₀,hE₀] at hea
      rw [hfun₁,hE₁] at heb
      rw [hea,heb] at hdisj
      have hab := (jointSurjective_iff_disjoint_dualAnnihilator L₀ b.linear hL₀
        (b.linear_surjective_iff.mpr hb)).mpr hdisj
      apply (mem_avoidingTreeFamily_iff (n+1) W φ).mpr
      refine ⟨avoidingRootLinearMap s p hp L₀ b,
        avoidingRootLinearMap_surjective s p hp L₀ b hab,?_,
        avoidingRootLinearMap_template n φ s p hp L₀ b hfun₀ hfun₁⟩
      intro x
      have hx : s x=0 := hW x.property
      refine ⟨hx,?_⟩
      have he : treeRootProjection s p hp x=⟨x,hx⟩ := by
        apply Subtype.ext
        simp [treeRootProjection,hx]
      change templateAvoidingCore n (L₀ (treeRootProjection s p hp x))
      rw [he]
      exact hcore ⟨⟨x,hx⟩,x.property⟩
    · intro hφ
      obtain ⟨L,hL,hcore,rfl⟩ := (mem_avoidingTreeFamily_iff (n+1) W φ).mp hφ
      let s : Module.Dual (ZMod 2) U :=
        (LinearMap.fst (ZMod 2) (ZMod 2) (TemplateSpace n × TemplateSpace n)).comp L
      let A : s.ker →ₗ[ZMod 2] TemplateSpace n :=
        ((LinearMap.fst (ZMod 2) (TemplateSpace n) (TemplateSpace n)).comp
          (LinearMap.snd (ZMod 2) (ZMod 2) (TemplateSpace n × TemplateSpace n))).comp
          (L.comp s.ker.subtype)
      have hA : Function.Surjective A := by
        intro u
        obtain ⟨x,hx⟩ := hL (0,u,0)
        exact ⟨⟨x,congrArg Prod.fst hx⟩,congrArg (fun z => z.2.1) hx⟩
      refine ⟨s,frame_first_isTreeRoot n L hL,?_,(ih _ _).mpr ?_⟩
      · intro x hx
        exact (hcore ⟨x,hx⟩).1
      · apply (mem_avoidingTreeFamily_iff n _ _).mpr
        refine ⟨A,hA,?_,?_⟩
        · intro x
          exact (hcore ⟨x,x.property⟩).2
        · funext x
          have hx : (L x).1=0 := x.property
          change template n (L x).2.1=template (n+1) (L x)
          simp [template,branch,hx]

/-- Lemma 6.9: the number of intrinsic Definition 6.8 functions equals the
paper's exact recurrence for the prescribed codimension-`h+1` subspace. -/
theorem isAvoidingTree_count (n : ℕ) (W : Submodule (ZMod 2) U)
    (hd : 2^(n+2)-1≤Module.finrank (ZMod 2) U)
    (hW : Module.finrank (ZMod 2) W+(n+3)=Module.finrank (ZMod 2) U) :
    Nat.card {φ : U → ZMod 2 // IsAvoidingTree (n+2) W φ}=
      avoidingTreeSupportCount (n+2) (Module.finrank (ZMod 2) U) := by
  classical
  let : Fintype U := Fintype.ofFinite _
  let e := (Equiv.refl (U → ZMod 2)).subtypeEquiv
    (fun φ => isAvoidingTree_iff_avoidingTreeFamily n W φ)
  exact (Nat.card_congr e).trans (avoidingTreeFamily_card n W hd hW)

/-- Lemma 6.9's fixed-height growth estimate, counted intrinsically as in
Definition 6.8, uniformly over all spaces and subspaces of the stated dimensions. -/
theorem isAvoidingTree_count_growth (h : ℕ) (hh : 2≤h) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀≤d → 2^h-1≤d →
      ∀ (U : Type*) [AddCommGroup U] [Module (ZMod 2) U] [Finite U],
      Module.finrank (ZMod 2) U=d →
      ∀ W : Submodule (ZMod 2) U, Module.finrank (ZMod 2) W+(h+1)=d →
        let M := Nat.card {φ : U → ZMod 2 // IsAvoidingTree h W φ}
        c*(2^d : ℝ)^(2^h-h-1)≤M ∧ (M : ℝ)≤C*(2^d : ℝ)^(2^h-h-1) := by
  obtain ⟨c,C,hc,hC,d₀,hbound⟩ := avoidingTreeSupportCount_growth h hh
  refine ⟨c,C,hc,hC,d₀,?_⟩
  intro d hd₀ hd U _ _ _ hdim W hW
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hh
  dsimp only
  rw [isAvoidingTree_count n W (by rwa [hdim]) (by simpa [hdim] using hW),hdim]
  exact hbound d hd₀

/-- Definition 6.8 may use the unique intrinsic root directly: its existential
presentation chooses no additional root and is independent of root witnesses. -/
theorem isAvoidingTree_succ_iff_at_root (n : ℕ) (W : Submodule (ZMod 2) U)
    (φ : U → ZMod 2) (s : Module.Dual (ZMod 2) U)
    (hs : IsTreeRoot (n+3) φ s) :
    IsAvoidingTree (n+3) W φ ↔ W≤s.ker ∧
      IsAvoidingTree (n+2) (W.comap s.ker.subtype) (fun x : s.ker => φ x) := by
  let : Fintype U := Fintype.ofFinite _
  constructor
  · rintro ⟨t,ht,hW,hchild⟩
    have he : t=s := ht.unique hs
    subst t
    exact ⟨hW,hchild⟩
  · rintro ⟨hW,hchild⟩
    exact ⟨s,hs,hW,hchild⟩

/-- Lemma 6.9 assembled: the intrinsic count equals the exact initial-value
and recurrence formula, has the stated fixed-height exponent, and every
counted support avoids `W`. -/
theorem isAvoidingTree_count_full (n : ℕ) (W : Submodule (ZMod 2) U)
    (hd : 2^(n+2)-1≤Module.finrank (ZMod 2) U)
    (hW : Module.finrank (ZMod 2) W+(n+3)=Module.finrank (ZMod 2) U) :
    Nat.card {φ : U → ZMod 2 // IsAvoidingTree (n+2) W φ}=
      avoidingTreeSupportCount (n+2) (Module.finrank (ZMod 2) U) ∧
    (∀ d : ℕ, avoidingTreeSupportCount 2 d=28*(6*2^(d-3)-5)) ∧
    (∀ j d : ℕ, let r := 2^(j+2)-1
      avoidingTreeSupportCount (j+3) d=
        (2^(j+4)-1)*avoidingTreeSupportCount (j+2) (d-1)*2^(r^2)*
          gaussianBinomial 2 (d-1-r) r*treeSupportCount (j+2) r) ∧
    HasBinaryPowerGrowth (avoidingTreeSupportCount (n+2)) (2^(n+2)-(n+2)-1) ∧
    (∀ φ : U → ZMod 2, IsAvoidingTree (n+2) W φ → ∀ x : W, φ x=0) := by
  exact ⟨isAvoidingTree_count n W hd hW,fun _ => rfl,fun _ _ => rfl,
    avoidingTreeSupportCount_growth (n+2) (by omega),fun _ hφ => hφ.vanishes⟩

end BinaryFieldCounterexamples.Trees
