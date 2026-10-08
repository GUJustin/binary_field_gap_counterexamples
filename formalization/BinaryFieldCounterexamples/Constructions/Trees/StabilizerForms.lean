/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AffineOrbits
/-!
# Exact affine stabilizer normal forms for independent branches

A stabilizer preserving the root coordinate cannot mix the two child blocks:
any cross block would produce a nonzero child translation period. Its remaining
parameters are exactly two child affine stabilizers and two unused translations.
A slice swap adds the two possible root orientations. The resulting literal
bijection gives the exact cardinal recurrence once root recovery is supplied.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] affineFunctionMulAction affineEquivFintype
/-- Two independent shears from the branch coordinate into child coordinates. -/
def branchShear {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (a b : V) :
    (ZMod 2 × V × V) ≃ₗ[ZMod 2] (ZMod 2 × V × V) :=
  { toFun := fun x => (x.1,x.2.1+x.1 • a,x.2.2+x.1 • b)
    invFun := fun x => (x.1,x.2.1-x.1 • a,x.2.2-x.1 • b)
    left_inv := by intro x; simp
    right_inv := by intro x; simp
    map_add' := by intro x y; ext <;> simp [add_smul] <;> abel
    map_smul' := by intro c x; ext <;> simp [smul_add,mul_smul] }
/-- The complete root-preserving affine form from two child maps and two unused translations. -/
def branchPreservingForm {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e0 e1 : V ≃ᵃ[ZMod 2] V) (a b : V) :
    (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V) :=
  ((AffineEquiv.prodCongr (AffineEquiv.refl (ZMod 2) (ZMod 2))
    (AffineEquiv.prodCongr e0 e1)).trans (branchShear a b).toAffineEquiv).trans
      (AffineEquiv.constVAdd (ZMod 2) (ZMod 2 × V × V) (0,0,b))
/-- The normal form is given by its literal coordinate formula. -/
theorem branchPreservingForm_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e0 e1 : V ≃ᵃ[ZMod 2] V) (a b : V) (x : ZMod 2 × V × V) :
    branchPreservingForm e0 e1 a b x=(x.1,e0 x.2.1+x.1 • a,e1 x.2.2+(x.1+1) • b) := by
  change (0+x.1,0+(e0 x.2.1+x.1 • a),b+(e1 x.2.2+x.1 • b))=_
  simp only [zero_add,add_smul,one_smul]
  abel_nf
/-- Normal forms formed from child stabilizers preserve the actual parent function. -/
theorem branchPreservingForm_stabilizes {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V → ZMod 2) (e0 e1 : V ≃ᵃ[ZMod 2] V)
    (h0 : e0 ∈ affineFunctionStabilizer f) (h1 : e1 ∈ affineFunctionStabilizer f) (a b : V) :
    branchPreservingForm e0 e1 a b ∈ affineFunctionStabilizer (branch f f) := by
  rw [mem_affineFunctionStabilizer]
  intro x
  rw [branchPreservingForm_apply]
  have hz := (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) x.1
  rcases hz with hz|hz
  · simpa [branch,hz] using (mem_affineFunctionStabilizer f e0).mp h0 x.2.1
  · simpa [branch,hz,show (1:ZMod 2)+1=0 by decide] using (mem_affineFunctionStabilizer f e1).mp h1 x.2.2
/-- Distinct child maps or unused translations yield distinct affine normal forms. -/
theorem branchPreservingForm_injective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    Function.Injective (fun p : (V ≃ᵃ[ZMod 2] V) × (V ≃ᵃ[ZMod 2] V) × V × V =>
      branchPreservingForm p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  intro p q h
  have h0 : p.1=q.1 := by
    ext x
    have he := congrArg (fun e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V) => (e (0,x,0)).2.1) h
    simpa only [branchPreservingForm_apply,zero_smul,add_zero] using he
  have h1 : p.2.1=q.2.1 := by
    ext x
    have he := congrArg (fun e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V) => (e (1,0,x)).2.2) h
    simpa only [branchPreservingForm_apply,show (1:ZMod 2)+1=0 by decide,zero_smul,add_zero] using he
  have ha : p.2.2.1=q.2.2.1 := by
    have he := congrArg (fun e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V) => (e (1,0,0)).2.1) h
    simpa only [branchPreservingForm_apply,one_smul,h0,add_right_inj] using he
  have hb : p.2.2.2=q.2.2.2 := by
    have he := congrArg (fun e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V) => (e (0,0,0)).2.2) h
    simpa only [branchPreservingForm_apply,zero_add,one_smul,h1,add_right_inj] using he
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext ha hb))
/-- Root-preserving stabilizers cannot mix the two independent child-coordinate spaces. -/
theorem branch_stabilizer_cross_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V → ZMod 2) (hf : ∀ u, IsPeriod f u → u=0)
    (e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V))
    (he : e ∈ affineFunctionStabilizer (branch f f))
    (hz : ∀ x, (e x).1=x.1) (v : V) :
    (e.linear (0,0,v)).2.1=0 ∧ (e.linear (0,v,0)).2.2=0 := by
  have heq := (mem_affineFunctionStabilizer (branch f f) e).mp he
  constructor
  · apply hf
    intro w
    let p := e.symm (0,w,0)
    have hep : e p=(0,w,0) := e.apply_symm_apply _
    have hp : p.1=0 := (hz p).symm.trans (congrArg Prod.fst hep)
    have htranslate : (e (p+(0,0,v))).2.1=w+(e.linear (0,0,v)).2.1 := by
      have h := congrArg (fun y : ZMod 2 × V × V => y.2.1) (e.map_vadd p (0,0,v))
      simpa [hep,add_comm] using h
    have hsame : branch f f (e (p+(0,0,v)))=branch f f (e p) := by
      rw [heq,heq]
      simp [branch,hp]
    simpa only [branch,hz,hp,Prod.fst_add,add_zero,ite_true,hep,htranslate] using hsame
  · apply hf
    intro w
    let p := e.symm (1,0,w)
    have hep : e p=(1,0,w) := e.apply_symm_apply _
    have hp : p.1=1 := (hz p).symm.trans (congrArg Prod.fst hep)
    have htranslate : (e (p+(0,v,0))).2.2=w+(e.linear (0,v,0)).2.2 := by
      have h := congrArg (fun y : ZMod 2 × V × V => y.2.2) (e.map_vadd p (0,v,0))
      simpa [hep,add_comm] using h
    have hsame : branch f f (e (p+(0,v,0)))=branch f f (e p) := by
      rw [heq,heq]
      simp [branch,hp]
    simpa only [branch,hz,hp,Prod.fst_add,add_zero,ite_eq_right (by decide : (1:ZMod 2)≠0),hep,htranslate] using hsame
/-- The first child block of an affine map's linear part. -/
def branchLeftLinear {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V)) : V →ₗ[ZMod 2] V :=
  { toFun := fun x => (e.linear (0,x,0)).2.1
    map_add' := by intro x y; simpa using congrArg (fun x : ZMod 2 × V × V => x.2.1) (e.linear.map_add (0,x,0) (0,y,0))
    map_smul' := by intro c x; simpa using congrArg (fun x : ZMod 2 × V × V => x.2.1) (e.linear.map_smul c (0,x,0)) }
/-- The second child block of an affine map's linear part. -/
def branchRightLinear {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V)) : V →ₗ[ZMod 2] V :=
  { toFun := fun x => (e.linear (0,0,x)).2.2
    map_add' := by intro x y; simpa using congrArg (fun x : ZMod 2 × V × V => x.2.2) (e.linear.map_add (0,0,x) (0,0,y))
    map_smul' := by intro c x; simpa using congrArg (fun x : ZMod 2 × V × V => x.2.2) (e.linear.map_smul c (0,0,x)) }
/-- Vanishing cross blocks give the literal child-coordinate formula on either root slice. -/
theorem branch_cross_zero_eval {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V))
    (hc : ∀ v, (e.linear (0,0,v)).2.1=0 ∧ (e.linear (0,v,0)).2.2=0)
    (z : ZMod 2) (x y : V) :
    (e (z,x,y)).2=(branchLeftLinear e x+(e (z,0,0)).2.1,
      branchRightLinear e y+(e (z,0,0)).2.2) := by
  have he := congrArg (fun p : ZMod 2 × V × V => p.2) (e.map_vadd (z,0,0) ((0,x,0)+(0,0,y)))
  rw [map_add] at he
  have he' : (e (z,x,y)).2=(e.linear (0,x,0)).2+(e.linear (0,0,y)).2+(e (z,0,0)).2 := by simpa using he
  rw [he']
  apply Prod.ext <;> simp [(hc x).2,(hc y).1,branchLeftLinear,branchRightLinear]
/-- The child blocks of a root-preserving affine stabilizer are injective. -/
theorem branch_childLinear_injective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V))
    (hz : ∀ x, (e x).1=x.1)
    (hc : ∀ v, (e.linear (0,0,v)).2.1=0 ∧ (e.linear (0,v,0)).2.2=0) :
    Function.Injective (branchLeftLinear e) ∧ Function.Injective (branchRightLinear e) := by
  have hl (x : ZMod 2 × V × V) : (e.linear x).1=x.1 := by
    have he := congrArg Prod.fst (e.map_vadd 0 x)
    simpa [hz] using he.symm
  constructor
  · intro x y h
    have he : e.linear (0,x,0)=e.linear (0,y,0) :=
      Prod.ext (by rw [hl,hl]) (Prod.ext h (by rw [(hc x).2,(hc y).2]))
    exact congrArg (fun p : ZMod 2 × V × V => p.2.1) (e.linear.injective he)
  · intro x y h
    have he : e.linear (0,0,x)=e.linear (0,0,y) :=
      Prod.ext (by rw [hl,hl]) (Prod.ext (by rw [(hc x).1,(hc y).1]) h)
    exact congrArg (fun p : ZMod 2 × V × V => p.2.2) (e.linear.injective he)
/-- Every root-preserving stabilizer has the proved two-child normal form. -/
theorem branch_stabilizer_normal_form {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (f : V → ZMod 2) (hf : ∀ u, IsPeriod f u → u=0)
    (e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V))
    (he : e ∈ affineFunctionStabilizer (branch f f))
    (hz : ∀ x, (e x).1=x.1) :
    ∃ e0 e1 : V ≃ᵃ[ZMod 2] V, e0 ∈ affineFunctionStabilizer f ∧ e1 ∈ affineFunctionStabilizer f ∧
      ∃ a b : V, e=branchPreservingForm e0 e1 a b := by
  have hc := branch_stabilizer_cross_zero f hf e he hz
  obtain ⟨hinj0,hinj1⟩ := branch_childLinear_injective e hz hc
  let L0 : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (branchLeftLinear e)
    ⟨hinj0,(Finite.injective_iff_surjective).mp hinj0⟩
  let L1 : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (branchRightLinear e)
    ⟨hinj1,(Finite.injective_iff_surjective).mp hinj1⟩
  let e0 := AffineEquiv.ofLinearEquiv L0 (0:V) (e (0,0,0)).2.1
  let e1 := AffineEquiv.ofLinearEquiv L1 (0:V) (e (1,0,0)).2.2
  have he0 (x : V) : e0 x=(e (0,x,0)).2.1 := by
    have hx := congrArg Prod.fst (branch_cross_zero_eval e hc 0 x 0)
    simp only [e0,AffineEquiv.ofLinearEquiv_apply,vsub_eq_sub,sub_zero,vadd_eq_add]
    change branchLeftLinear e x+(e (0,0,0)).2.1=(e (0,x,0)).2.1
    exact hx.symm
  have he1 (y : V) : e1 y=(e (1,0,y)).2.2 := by
    have hy := congrArg Prod.snd (branch_cross_zero_eval e hc 1 0 y)
    simp only [e1,AffineEquiv.ofLinearEquiv_apply,vsub_eq_sub,sub_zero,vadd_eq_add]
    change branchRightLinear e y+(e (1,0,0)).2.2=(e (1,0,y)).2.2
    exact hy.symm
  have hstab := (mem_affineFunctionStabilizer (branch f f) e).mp he
  refine ⟨e0,e1,?_,?_,(e (1,0,0)).2.1-(e (0,0,0)).2.1,
    (e (0,0,0)).2.2-(e (1,0,0)).2.2,?_⟩
  · rw [mem_affineFunctionStabilizer]
    intro x
    have hh := hstab (0,x,0)
    simpa [branch,hz,←he0] using hh
  · rw [mem_affineFunctionStabilizer]
    intro y
    have hh := hstab (1,0,y)
    simpa [branch,hz,←he1] using hh
  · apply AffineEquiv.ext
    intro p
    rw [branchPreservingForm_apply]
    apply Prod.ext
    · exact hz p
    ·
      have hev := branch_cross_zero_eval e hc p.1 p.2.1 p.2.2
      rw [show (p.1,p.2.1,p.2.2)=p by rfl] at hev
      rw [hev]
      dsimp [e0,e1,AffineEquiv.ofLinearEquiv_apply]
      have hL0 (x : V) : L0 x=branchLeftLinear e x := rfl
      have hL1 (x : V) : L1 x=branchRightLinear e x := rfl
      simp only [hL0,hL1]
      have hp := (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) p.1
      rcases hp with hp|hp
      · simp only [hp,zero_smul,zero_add,one_smul,sub_zero ]
        apply Prod.ext <;> abel_nf
      · simp only [hp,one_smul,show (1:ZMod 2)+1=0 by decide,zero_smul,add_zero,sub_zero ]
        apply Prod.ext <;> abel_nf
/-- Swap the two root slices together with the independent child coordinates. -/
def branchSwap {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V) :=
  (AffineEquiv.prodCongr (AffineEquiv.refl (ZMod 2) (ZMod 2))
    (LinearEquiv.prodComm (ZMod 2) V V).toAffineEquiv).trans
      (AffineEquiv.constVAdd (ZMod 2) (ZMod 2 × V × V) (1,0,0))
/-- Literal coordinate formula for the slice swap. -/
theorem branchSwap_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : ZMod 2 × V × V) :
    branchSwap x=(x.1+1,x.2.2,x.2.1) := by
  change (1+x.1,0+x.2.2,0+x.2.1)=_
  simp [add_comm]
/-- The root swap is an involution. -/
theorem branchSwap_apply_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : ZMod 2 × V × V) :
    branchSwap (branchSwap x)=x := by
  rw [branchSwap_apply,branchSwap_apply]
  simp only [add_assoc,show (1:ZMod 2)+1=0 by decide,add_zero]
/-- Swapping independent identical child templates preserves their branch function. -/
theorem branchSwap_stabilizes {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (f : V → ZMod 2) :
    branchSwap ∈ affineFunctionStabilizer (branch f f) := by
  rw [mem_affineFunctionStabilizer]
  intro x
  rw [branchSwap_apply]
  rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) x.1 with h|h <;>
    simp [branch,h,show (1:ZMod 2)+1=0 by decide]
/-- The two possible root orientations of a child normal form. -/
def branchForm {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ε : ZMod 2) (e0 e1 : V ≃ᵃ[ZMod 2] V) (a b : V) :
    (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V) :=
  if ε=0 then branchPreservingForm e0 e1 a b else
    (branchPreservingForm e0 e1 a b).trans branchSwap
/-- Every oriented normal form preserves the parent function. -/
theorem branchForm_stabilizes {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V → ZMod 2) (ε : ZMod 2) (e0 e1 : V ≃ᵃ[ZMod 2] V)
    (h0 : e0 ∈ affineFunctionStabilizer f) (h1 : e1 ∈ affineFunctionStabilizer f) (a b : V) :
    branchForm ε e0 e1 a b ∈ affineFunctionStabilizer (branch f f) := by
  dsimp only [branchForm]
  split_ifs
  · exact branchPreservingForm_stabilizes f e0 e1 h0 h1 a b
  · exact (affineFunctionStabilizer (branch f f)).mul_mem (branchSwap_stabilizes f)
      (branchPreservingForm_stabilizes f e0 e1 h0 h1 a b)
/-- The root orientation is recovered by evaluation at the origin. -/
theorem branchForm_origin_first {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ε : ZMod 2) (e0 e1 : V ≃ᵃ[ZMod 2] V) (a b : V) :
    (branchForm ε e0 e1 a b (0,0,0)).1=ε := by
  rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) ε with h|h <;>
    simp [branchForm,h,AffineEquiv.trans_apply,branchSwap_apply,branchPreservingForm_apply]
/-- An oriented affine normal form determines every one of its parameters. -/
theorem branchForm_injective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    Function.Injective (fun p : ZMod 2 × (V ≃ᵃ[ZMod 2] V) × (V ≃ᵃ[ZMod 2] V) × V × V =>
      branchForm p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  intro p q he
  have hε : p.1=q.1 := by
    simpa only [branchForm_origin_first] using
      congrArg (fun e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V) => (e (0,0,0)).1) he
  apply Prod.ext hε
  apply branchPreservingForm_injective
  by_cases hz : p.1=0
  · simpa only [branchForm,hz,←hε,ite_true] using he
  · simp only [branchForm,hz,←hε,ite_false] at he
    apply AffineEquiv.ext
    intro x
    exact (branchSwap (V := V)).injective (congrArg (fun e => e x) he)
/-- Root-linear recovery implies the exhaustive oriented stabilizer classification. -/
theorem branch_stabilizer_full_normal_form {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (f : V → ZMod 2) (hf : ∀ u, IsPeriod f u → u=0)
    (e : (ZMod 2 × V × V) ≃ᵃ[ZMod 2] (ZMod 2 × V × V))
    (he : e ∈ affineFunctionStabilizer (branch f f))
    (hroot : ∀ x, (e.linear x).1=x.1) :
    ∃ ε : ZMod 2, ∃ e0 e1 : V ≃ᵃ[ZMod 2] V,
      e0 ∈ affineFunctionStabilizer f ∧ e1 ∈ affineFunctionStabilizer f ∧
      ∃ a b : V, e=branchForm ε e0 e1 a b := by
  have hfirst (x : ZMod 2 × V × V) : (e x).1=x.1+(e 0).1 := by
    have hx := congrArg Prod.fst (e.map_vadd 0 x)
    simpa only [vadd_eq_add,add_zero,Prod.fst_add,hroot] using hx
  rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (e 0).1 with hε|hε
  · obtain ⟨e0,e1,h0,h1,a,b,heq⟩ := branch_stabilizer_normal_form f hf e he
      (fun x => by rw [hfirst,hε,add_zero])
    exact ⟨0,e0,e1,h0,h1,a,b,by simpa [branchForm] using heq⟩
  · let e' := e.trans (branchSwap (V := V))
    have he'stab : e' ∈ affineFunctionStabilizer (branch f f) :=
      (affineFunctionStabilizer (branch f f)).mul_mem (branchSwap_stabilizes f) he
    have he'root (x : ZMod 2 × V × V) : (e' x).1=x.1 := by
      change (branchSwap (e x)).1=x.1
      rw [branchSwap_apply]
      change (e x).1+1=x.1
      rw [hfirst x,hε,add_assoc,show (1:ZMod 2)+1=0 by decide,add_zero]
    obtain ⟨e0,e1,h0,h1,a,b,heq⟩ := branch_stabilizer_normal_form f hf e' he'stab he'root
    refine ⟨1,e0,e1,h0,h1,a,b,?_⟩
    apply AffineEquiv.ext
    intro x
    have hx := congrArg (fun e => branchSwap (e x)) heq
    simpa only [e',AffineEquiv.trans_apply,branchSwap_apply_apply,branchForm,
      ite_eq_right (by decide : (1:ZMod 2)≠0)] using hx
/-- Exhaustive normal forms give the exact actual affine stabilizer recurrence. -/
theorem branch_stabilizer_card {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (f : V → ZMod 2) (hf : ∀ u, IsPeriod f u → u=0)
    (hroot : ∀ e ∈ affineFunctionStabilizer (branch f f), ∀ x, (e.linear x).1=x.1) :
    Nat.card (affineFunctionStabilizer (branch f f))=
      2*(Nat.card V)^2*(Nat.card (affineFunctionStabilizer f))^2 := by
  classical
  let g : ZMod 2 × affineFunctionStabilizer f × affineFunctionStabilizer f × V × V →
      affineFunctionStabilizer (branch f f) := fun p =>
    ⟨branchForm p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2,
      branchForm_stabilizes f p.1 p.2.1 p.2.2.1 p.2.1.property p.2.2.1.property p.2.2.2.1 p.2.2.2.2⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨ε,e0,e1,a,b⟩ ⟨ε',e0',e1',a',b'⟩ h
      have heq : branchForm ε e0 e1 a b=branchForm ε' e0' e1' a' b' := congrArg Subtype.val h
      have hh := branchForm_injective (a₁ := (ε,(e0:V ≃ᵃ[ZMod 2] V),(e1:V ≃ᵃ[ZMod 2] V),a,b))
        (a₂ := (ε',(e0':V ≃ᵃ[ZMod 2] V),(e1':V ≃ᵃ[ZMod 2] V),a',b')) heq
      change (ε,(e0:V ≃ᵃ[ZMod 2] V),(e1:V ≃ᵃ[ZMod 2] V),a,b)=
        (ε',(e0':V ≃ᵃ[ZMod 2] V),(e1':V ≃ᵃ[ZMod 2] V),a',b') at hh
      simp only [Prod.mk.injEq] at hh
      exact Prod.ext hh.1 (Prod.ext (Subtype.ext hh.2.1)
        (Prod.ext (Subtype.ext hh.2.2.1) (Prod.ext hh.2.2.2.1 hh.2.2.2.2)))
    · intro e
      obtain ⟨ε,e0,e1,h0,h1,a,b,he⟩ := branch_stabilizer_full_normal_form f hf e e.property
        (hroot e e.property)
      exact ⟨(ε,⟨e0,h0⟩,⟨e1,h1⟩,a,b),Subtype.ext he.symm⟩
  rw [←Nat.card_congr (Equiv.ofBijective g hg)]
  simp only [Nat.card_prod]
  rw [show Nat.card (ZMod 2)=2 by rw [Nat.card_eq_fintype_card,ZMod.card]]
  ring
end BinaryFieldCounterexamples.Trees
