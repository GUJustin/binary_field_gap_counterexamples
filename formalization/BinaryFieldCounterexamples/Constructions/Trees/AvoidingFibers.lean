/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingRoots
public import BinaryFieldCounterexamples.Constructions.Trees.RootFrameCounts
public import BinaryFieldCounterexamples.Counting.GaussianEstimates
public import BinaryFieldCounterexamples.Constructions.Trees.Leaves
/-!
# Exact canonical avoiding-frame fibers

Actual parent frames split by their nonzero annihilator root. The literal
root fiber is identified with the proved fixed-root parameter type; summing
its exact cardinal gives the child-frame, complement, and translation factors.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- Actual surjective frames satisfying the canonical prescribed-subspace constraint. -/
def AvoidingFrames (n : ℕ) (W : Submodule (ZMod 2) V) :=
  {L : V →ₗ[ZMod 2] TemplateSpace n // Function.Surjective L ∧ avoidingTreeFrameProperty n W L}
/-- Equality of extracted roots is equality of the actual first-coordinate functionals. -/
theorem avoidingFrameRoot_eq_iff (n : ℕ) (W : Submodule (ZMod 2) V)
    (L : AvoidingFrames (n+1) W) (z : AvoidingRoots W) :
    avoidingFrameRoot n W L=z ↔ rootFirst L.1=z.1.1 := by
  constructor
  · intro h
    exact congrArg (fun z : AvoidingRoots W => z.1.1) h
  · intro h
    exact Subtype.ext (Subtype.ext h)
/-- At an admissible fixed root, the concrete core condition is exactly the previous core condition inside its kernel. -/
theorem avoidingFrameProperty_at_root (n : ℕ) (W : Submodule (ZMod 2) V)
    (z : AvoidingRoots W) (L : V →ₗ[ZMod 2] TemplateSpace (n+1)) (hroot : rootFirst L=z.1.1) :
    avoidingTreeFrameProperty (n+1) W L ↔
      avoidingTreeFrameProperty n (avoidingRootSubspace W z) (rootRestrictedLeft z.1.1 L) := by
  constructor
  · intro h x
    exact (h ⟨x.1.1,x.2⟩).2
  · intro h x
    refine ⟨?_,h ⟨⟨x.1,avoidingRoot_le_ker W z x.2⟩,x.2⟩⟩
    change rootFirst L x.1=0
    rw [hroot]
    exact avoidingRoot_le_ker W z x.2
/-- A literal root fiber is exactly the fixed-root frame type used by the linear parameter count. -/
def avoidingFrameRootFiberEquiv (n : ℕ) (W : Submodule (ZMod 2) V) (z : AvoidingRoots W) :
    {L : AvoidingFrames (n+1) W // avoidingFrameRoot n W L=z} ≃
      RootAdmissibleFrames z.1.1 (avoidingTreeFrameProperty n (avoidingRootSubspace W z)) :=
  { toFun := fun L =>
      ⟨L.1.1,L.1.2.1,(avoidingFrameRoot_eq_iff n W L.1 z).mp L.2,
        (avoidingFrameProperty_at_root n W z L.1.1
          ((avoidingFrameRoot_eq_iff n W L.1 z).mp L.2)).mp L.1.2.2⟩
    invFun := fun L =>
      ⟨⟨L.1,L.2.1,(avoidingFrameProperty_at_root n W z L.1 L.2.2.1).mpr L.2.2.2⟩,
        (avoidingFrameRoot_eq_iff n W _ z).mpr L.2.2.1⟩
    left_inv := by intro L; rfl
    right_inv := by intro L; rfl }
/-- Uniform actual root fibers multiply by the exact nonzero annihilator population. -/
theorem avoidingFrames_card_of_uniform_root_fibers [Fintype V] (n : ℕ)
    (W : Submodule (ZMod 2) V) (M : ℕ)
    (hM : ∀ z : AvoidingRoots W, Nat.card
      (RootAdmissibleFrames z.1.1 (avoidingTreeFrameProperty n (avoidingRootSubspace W z)))=M) :
    Nat.card (AvoidingFrames (n+1) W)=
      (2^(Module.finrank (ZMod 2) V-Module.finrank (ZMod 2) W)-1)*M := by
  classical
  let : Fintype (Module.Dual (ZMod 2) V) := Fintype.ofInjective
    (fun f : Module.Dual (ZMod 2) V => (f : V → ZMod 2)) DFunLike.coe_injective
  let : Finite (AvoidingRoots W) := Finite.of_injective
    (fun z : AvoidingRoots W => z.1.1) (by intro a b h; exact Subtype.ext (Subtype.ext h))
  let : Fintype (AvoidingRoots W) := Fintype.ofFinite _
  let : Finite (V →ₗ[ZMod 2] TemplateSpace (n+1)) := Finite.of_injective
    (fun L : V →ₗ[ZMod 2] TemplateSpace (n+1) => (L : V → TemplateSpace (n+1))) DFunLike.coe_injective
  let : Finite (AvoidingFrames (n+1) W) := Finite.of_injective
    (fun L : AvoidingFrames (n+1) W => L.1) (by intro a b h; exact Subtype.ext h)
  have hf (z : AvoidingRoots W) : Nat.card
      {L : AvoidingFrames (n+1) W // avoidingFrameRoot n W L=z}=M :=
    (Nat.card_congr (avoidingFrameRootFiberEquiv n W z)).trans (hM z)
  rw [←Nat.card_congr (Equiv.sigmaFiberEquiv (fun L : AvoidingFrames (n+1) W => avoidingFrameRoot n W L)),
    Nat.card_sigma]
  simp_rw [hf]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,avoidingRoots_card]
  simp
/-- The actual constrained parent-frame count is the exact root, child, complement, and translation product. -/
theorem avoidingFrames_card_step [Fintype V] (n : ℕ) (W : Submodule (ZMod 2) V) (M : ℕ)
    (hd : 2*(2^(n+2)-1)≤Module.finrank (ZMod 2) V-1)
    (hchild : ∀ z : AvoidingRoots W, Nat.card (AvoidingFrames n (avoidingRootSubspace W z))=M) :
    Nat.card (AvoidingFrames (n+1) W)=
      (2^(Module.finrank (ZMod 2) V-Module.finrank (ZMod 2) W)-1)*
        (M*(2^(2^(n+2)-1))^2*2^((2^(n+2)-1)^2)*
          binaryFrameProduct (Module.finrank (ZMod 2) V-1-(2^(n+2)-1)) (2^(n+2)-1)) := by
  apply avoidingFrames_card_of_uniform_root_fibers n W
  intro z
  have hker : Module.finrank (ZMod 2) (LinearMap.ker z.1.1)=Module.finrank (ZMod 2) V-1 := by
    have h := binaryFunctional_ker_finrank z.1.1 (avoidingRoot_ne_zero W z)
    omega
  have ht : Nat.card (TemplateSpace n)=2^(2^(n+2)-1) := by
    rw [Nat.card_eq_fintype_card,templateSpace_card]
  have hdim : 2*Module.finrank (ZMod 2) (TemplateSpace n)≤
      Module.finrank (ZMod 2) (LinearMap.ker z.1.1) := by
    rw [templateSpace_finrank,hker]
    exact hd
  rw [rootAdmissibleFrames_card z.1.1 (binaryFunctional_surjective z.1.1 (avoidingRoot_ne_zero W z))
    (avoidingTreeFrameProperty n (avoidingRootSubspace W z)) hdim]
  change Nat.card (AvoidingFrames n (avoidingRootSubspace W z))*_*_*_= _
  rw [hchild,ht,templateSpace_finrank,hker]
  have hp : (∏ i : Fin (2^(n+2)-1),
      (2^(Module.finrank (ZMod 2) V-1-(2^(n+2)-1))-2^(i:ℕ)))=
      binaryFrameProduct (Module.finrank (ZMod 2) V-1-(2^(n+2)-1)) (2^(n+2)-1) :=
    Fin.prod_univ_eq_prod_range (fun i => 2^(Module.finrank (ZMod 2) V-1-(2^(n+2)-1))-2^i) (2^(n+2)-1)
  rw [hp]
end BinaryFieldCounterexamples.Trees
