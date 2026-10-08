/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingFamily
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingFibers
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingSupports
public import BinaryFieldCounterexamples.Constructions.Trees.BaseAvoidingFamily
public import BinaryFieldCounterexamples.Constructions.Trees.TemplateZeroOrbit
public import BinaryFieldCounterexamples.Constructions.Trees.FrameArithmetic
/-!
# Exact prescribed-subspace avoiding tree counts

The actual height-two vanishing family supplies the base. Actual root fibers,
canonical-core invariance, and the proved origin stabilizer supply every
recursive factor. Height induction therefore identifies the literal finite
support population with the original manuscript recurrence on every prescribed
subspace of the stated codimension. No population formula is assumed.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- The canonical height-two family is exactly the actual vanishing base family. -/
theorem avoidingTreeFamily_zero (W : Submodule (ZMod 2) V) :
    avoidingTreeFamily 0 W=baseAvoidingFamily W := by
  ext f
  constructor
  · intro hf
    obtain ⟨L,hL,hcore,rfl⟩ := (mem_avoidingTreeFamily_iff 0 W f).mp hf
    exact ⟨⟨L,hL,hcore⟩,rfl⟩
  · rintro ⟨L,rfl⟩
    exact (mem_avoidingTreeFamily_iff 0 W _).mpr ⟨L.1,L.2.1,L.2.2,rfl⟩
/-- The exact canonical avoiding-family recurrence starts from the original base count. -/
theorem avoidingTreeFamily_card_zero [Fintype V] (W : Submodule (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) W+3=Module.finrank (ZMod 2) V) :
    Nat.card (avoidingTreeFamily 0 W)=avoidingTreeSupportCount 2 (Module.finrank (ZMod 2) V) := by
  rw [avoidingTreeFamily_zero]
  exact baseAvoidingFamily_card W hW
/-- Exact cancellation of actual root-frame factors yields the original manuscript recurrence. -/
theorem avoiding_count_step_algebra (n d C M : ℕ)
    (hd : 2*(2^(n+2)-1)≤d-1)
    (h : C*(2*treeDenominator (n+3))=
      (2^(n+4)-1)*(M*(2*treeDenominator (n+2)))*(2^(2^(n+2)-1))^2*
        2^((2^(n+2)-1)^2)*binaryFrameProduct (d-1-(2^(n+2)-1)) (2^(n+2)-1)) :
    C=(2^(n+4)-1)*M*2^((2^(n+2)-1)^2)*
      gaussianBinomial 2 (d-1-(2^(n+2)-1)) (2^(n+2)-1)*
      treeSupportCount (n+2) (2^(n+2)-1) := by
  have hr : 2^(n+2)-1≤d-1-(2^(n+2)-1) := by omega
  rw [binaryFrameProduct_eq_gaussian_mul _ _ hr,
    ←treeSupportCount_mul_denominator n (2^(n+2)-1) le_rfl] at h
  have hp : (2:ℕ)^(2*(2^(n+2)-1))=(2^(2^(n+2)-1))^2 := by rw [mul_comm,pow_mul]
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by decide : 0<(2:ℕ)) (treeDenominator_pos (n+3)))
  calc
    _=_ := h
    _=_ := by rw [treeDenominator,hp]; ring
/-- The actual canonical avoiding family has exactly the original manuscript recurrence count. -/
theorem avoidingTreeFamily_card [Fintype V] (n : ℕ) (W : Submodule (ZMod 2) V)
    (hd : 2^(n+2)-1≤Module.finrank (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) W+(n+3)=Module.finrank (ZMod 2) V) :
    Nat.card (avoidingTreeFamily n W)=avoidingTreeSupportCount (n+2) (Module.finrank (ZMod 2) V) := by
  induction n generalizing V with
  | zero => exact avoidingTreeFamily_card_zero W hW
  | succ n ih =>
    have hp : 1≤(2:ℕ)^(n+2) := Nat.one_le_pow _ _ (by decide)
    have htau : 2^(n+1+2)-1=2*(2^(n+2)-1)+1 := by
      rw [show n+1+2=n+2+1 by omega,pow_succ]
      omega
    have hdim : 2*(2^(n+2)-1)≤Module.finrank (ZMod 2) V-1 := by rw [htau] at hd; omega
    have hchild (z : AvoidingRoots W) : Nat.card (AvoidingFrames n (avoidingRootSubspace W z))=
        avoidingTreeSupportCount (n+2) (Module.finrank (ZMod 2) V-1)*(2*treeDenominator (n+2)) := by
      let : Fintype (LinearMap.ker z.1.1) := Fintype.ofFinite _
      have hker : Module.finrank (ZMod 2) (LinearMap.ker z.1.1)=Module.finrank (ZMod 2) V-1 := by
        have h := binaryFunctional_ker_finrank z.1.1 (avoidingRoot_ne_zero W z)
        omega
      have hdimchild : 2^(n+2)-1≤Module.finrank (ZMod 2) (LinearMap.ker z.1.1) := by rw [hker]; omega
      have hWchild : Module.finrank (ZMod 2) (avoidingRootSubspace W z)+(n+3)=
          Module.finrank (ZMod 2) (LinearMap.ker z.1.1) := by
        rw [avoidingRootSubspace_finrank,hker]
        omega
      have hfamily := ih (avoidingRootSubspace W z) hdimchild hWchild
      have h := avoidingTreeFamily_card_mul_stabilizer n (avoidingRootSubspace W z)
      rw [template_origin_stabilizer_card,hfamily,hker] at h
      exact h.symm
    have hraw := avoidingFrames_card_step n W _ hdim hchild
    have hroot : Module.finrank (ZMod 2) V-Module.finrank (ZMod 2) W=n+4 := by omega
    rw [hroot] at hraw
    have hfactor := avoidingTreeFamily_card_mul_stabilizer (n+1) W
    rw [template_origin_stabilizer_card] at hfactor
    change Nat.card (avoidingTreeFamily (n+1) W)*(2*treeDenominator (n+1+2))=
      Nat.card (AvoidingFrames (n+1) W) at hfactor
    have hidentity : Nat.card (avoidingTreeFamily (n+1) W)*(2*treeDenominator (n+3))=
        (2^(n+4)-1)*(avoidingTreeSupportCount (n+2) (Module.finrank (ZMod 2) V-1)*
          (2*treeDenominator (n+2)))*(2^(2^(n+2)-1))^2*
          2^((2^(n+2)-1)^2)*binaryFrameProduct
            (Module.finrank (ZMod 2) V-1-(2^(n+2)-1)) (2^(n+2)-1) := by
      calc
        _=Nat.card (AvoidingFrames (n+1) W) := by simpa only [show n+1+2=n+3 by omega] using hfactor
        _=_ := hraw.trans (by ring)
    exact avoiding_count_step_algebra n (Module.finrank (ZMod 2) V) _ _ hdim hidentity
/-- The literal finite avoiding support family has exactly the original count on every prescribed subspace. -/
theorem avoidingTreeSupportFamily_card_eq [Fintype V] (n : ℕ) (W : Submodule (ZMod 2) V)
    (hd : 2^(n+2)-1≤Module.finrank (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) W+(n+3)=Module.finrank (ZMod 2) V) :
    (avoidingTreeSupportFamily n W).card=avoidingTreeSupportCount (n+2) (Module.finrank (ZMod 2) V) := by
  rw [avoidingTreeSupportFamily_card]
  exact avoidingTreeFamily_card n W hd hW
end BinaryFieldCounterexamples.Trees
