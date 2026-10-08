/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.BorderedRank
/-!
# Splitting off a binary hyperbolic plane

A nonzero symmetric alternating form has a pair with pairing one. The explicit
orthogonal projection gives a linear equivalence with its codimension-two
orthogonal complement and a hyperbolic plane. The pairing splits literally;
the kernel is unchanged and the polar rank drops by exactly two. These are the
one-step linear-algebra facts needed for a canonical form in the Fourier proof.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- The vectors orthogonal to both chosen hyperbolic vectors. -/
def hyperbolicComplement (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V) :
    Submodule (ZMod 2) V := LinearMap.ker (C x) ⊓ LinearMap.ker (C y)

/-- Subtract the two hyperbolic coordinates (addition in characteristic two). -/
def hyperbolicProjection (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V) :
    V →ₗ[ZMod 2] V := LinearMap.id + (C y).smulRight x + (C x).smulRight y

/-- The explicit projection lands in the orthogonal complement. -/
theorem hyperbolicProjection_mem
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1) (z : V) :
    hyperbolicProjection C x y z ∈ hyperbolicComplement C x y := by
  have hyx : C y x=1 := (hs _ _).trans hxy
  constructor
  · change C x (z+(C y z) • x+(C x z) • y)=0
    simp [ha,hxy,CharTwo.add_self_eq_zero]
  · change C y (z+(C y z) • x+(C x z) • y)=0
    simp [ha,hyx,CharTwo.add_self_eq_zero]

/-- The actual linear splitting, with explicit inverse h+a x+b y. -/
noncomputable def hyperbolicSplitEquiv
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1) :
    V ≃ₗ[ZMod 2] hyperbolicComplement C x y × (ZMod 2 × ZMod 2) := by
  let p : V →ₗ[ZMod 2] hyperbolicComplement C x y :=
    (hyperbolicProjection C x y).codRestrict _ (hyperbolicProjection_mem C x y hs ha hxy)
  let f : V →ₗ[ZMod 2] hyperbolicComplement C x y × (ZMod 2 × ZMod 2) :=
    p.prod ((C y).prod (C x))
  have htwo (a : V) : a+a=0 := by
    have hz : (2 : ZMod 2)=0 := by decide
    have he := two_smul (ZMod 2) a
    rw [hz, zero_smul] at he
    exact he.symm
  have hcancel (z a b : V) : z+a+b+a+b=z := by
    calc
      _ = z+(a+a)+(b+b) := by abel
      _ = z := by rw [htwo,htwo]; simp
  refine { f with
    invFun := fun w => (w.1 : V)+w.2.1 • x+w.2.2 • y
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    change (z+(C y z) • x+(C x z) • y)+(C y z) • x+(C x z) • y=z
    exact hcancel _ _ _
  · intro w
    have hxw : C x (w.1 : V)=0 := w.1.property.1
    have hyw : C y (w.1 : V)=0 := w.1.property.2
    have hyx : C y x=1 := (hs _ _).trans hxy
    apply Prod.ext
    · apply Subtype.ext
      change hyperbolicProjection C x y ((w.1 : V)+w.2.1 • x+w.2.2 • y)=(w.1 : V)
      simp only [hyperbolicProjection, LinearMap.add_apply,LinearMap.id_apply,
        LinearMap.smulRight_apply, map_add,map_smul,hxw,hyw,ha,hxy,hyx]
      simp [htwo]
    · apply Prod.ext <;> simp [f,ha,hxy,hyx,hxw,hyw]
/-- The form splits as the restricted form plus a hyperbolic plane. -/
theorem hyperbolic_pairing_decomposition
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1)
    (h k : hyperbolicComplement C x y) (a b c e : ZMod 2) :
    C ((h : V)+a • x+b • y) ((k : V)+c • x+e • y) =
      C (h : V) (k : V)+a*e+b*c := by
  have hyx : C y x=1 := (hs _ _).trans hxy
  have hxk : C x (k : V)=0 := k.property.1
  have hyk : C y (k : V)=0 := k.property.2
  have hhx : C (h : V) x=0 := (hs _ _).trans h.property.1
  have hhy : C (h : V) y=0 := (hs _ _).trans h.property.2
  simp [map_add,map_smul,ha,hxy,hyx,hxk,hyk,hhx,hhy,smul_eq_mul]
  ring

/-- The complement loses exactly two dimensions. -/
theorem hyperbolicComplement_finrank [Finite V]
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1) :
    Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (hyperbolicComplement C x y)+2 := by
  have h := (hyperbolicSplitEquiv C x y hs ha hxy).finrank_eq
  simpa [Module.finrank_prod] using h
/-- A nonzero binary bilinear form has a pair with pairing one. -/
theorem exists_hyperbolic_pair
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (hC : C≠0) :
    ∃ x y, C x y=1 := by
  by_contra h
  push Not at h
  apply hC
  ext x y
  rcases binary_eq_zero_or_one (C x y) with hz | ho
  · exact hz
  · exact (h x y ho).elim

/-- The literal restriction of the form to its orthogonal complement. -/
def hyperbolicRestrictedMap
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V) :
    hyperbolicComplement C x y →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (hyperbolicComplement C x y) :=
  (hyperbolicComplement C x y).dualRestrict.comp
    (C.comp (hyperbolicComplement C x y).subtype)

/-- Restriction keeps the original pairing values. -/
theorem hyperbolicRestrictedMap_apply
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (a b : hyperbolicComplement C x y) :
    hyperbolicRestrictedMap C x y a b = C (a : V) (b : V) := by
  rfl

/-- Symmetry is preserved by restriction. -/
theorem hyperbolicRestrictedMap_symmetric
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (a b : hyperbolicComplement C x y) :
    hyperbolicRestrictedMap C x y a b=hyperbolicRestrictedMap C x y b a := by
  exact hs a b

/-- Alternation is preserved by restriction. -/
theorem hyperbolicRestrictedMap_alternating
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (ha : ∀ a, C a a=0) (a : hyperbolicComplement C x y) :
    hyperbolicRestrictedMap C x y a a=0 := by
  exact ha a
/-- The orthogonal splitting identifies the original and restricted kernels. -/
noncomputable def hyperbolicKernelEquiv
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1) :
    LinearMap.ker C ≃ₗ[ZMod 2] LinearMap.ker (hyperbolicRestrictedMap C x y) := by
  let f : LinearMap.ker C → LinearMap.ker (hyperbolicRestrictedMap C x y) := fun z =>
    ⟨⟨z.val, by
      constructor
      · change C x z.val=0
        rw [hs, show C z.val=0 from z.property]
        rfl
      · change C y z.val=0
        rw [hs, show C z.val=0 from z.property]
        rfl⟩, by
      ext w
      change C z.val (w : V)=0
      rw [show C z.val=0 from z.property]
      rfl⟩
  let g : LinearMap.ker (hyperbolicRestrictedMap C x y) → LinearMap.ker C := fun z =>
    ⟨z.val.val, by
      ext w
      let e := hyperbolicSplitEquiv C x y hs ha hxy
      have hw := e.symm_apply_apply w
      rw [← hw]
      change C z.val.val (((e w).1 : V)+(e w).2.1 • x+(e w).2.2 • y)=0
      have hz : C z.val.val ((e w).1 : V)=0 := LinearMap.congr_fun z.property (e w).1
      have hzx : C z.val.val x=0 := (hs _ _).trans z.val.property.1
      have hzy : C z.val.val y=0 := (hs _ _).trans z.val.property.2
      simp [hz,hzx,hzy]⟩
  exact {
    toFun := f
    invFun := g
    left_inv := fun z => rfl
    right_inv := fun z => rfl
    map_add' := fun z w => rfl
    map_smul' := fun c z => rfl }

/-- The restricted form has rank exactly two less than the original. -/
theorem hyperbolicRestrictedMap_rank [Finite V]
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1) :
    Module.finrank (ZMod 2) (LinearMap.range C) =
      Module.finrank (ZMod 2) (LinearMap.range (hyperbolicRestrictedMap C x y))+2 := by
  have hk := (hyperbolicKernelEquiv C x y hs ha hxy).finrank_eq
  have hd := hyperbolicComplement_finrank C x y hs ha hxy
  have h1 := C.finrank_range_add_finrank_ker
  have h2 := (hyperbolicRestrictedMap C x y).finrank_range_add_finrank_ker
  omega
end BinaryFieldCounterexamples.Gold
