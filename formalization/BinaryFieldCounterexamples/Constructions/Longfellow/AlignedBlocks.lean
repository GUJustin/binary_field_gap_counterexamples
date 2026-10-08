/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Longfellow.DomainCoordinates
/-!
# Longfellow's aligned binary blocks

Section 5.8, `sections/applications.tex` lines 109–110, states that an aligned
block of `2^k` integer indices maps to an affine space of dimension `k`.
For `k ≤ 16` and a block contained in the sixteen-bit index range, we identify
that space as the translate of the binary span of the first `k` basis vectors.
Both its dimension and its exact number of points are proved below.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Longfellow
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {B : Type*} [Field B] [Algebra (ZMod 2) B]

/-- Section 5.8's aligned-block claim: extend the first `k` binary coordinates
by zero, then apply the actual Longfellow basis encoding. -/
noncomputable def alignedLowMap (b : Module.Basis (Fin 16) (ZMod 2) B) (k : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] B :=
  b.equivFun.symm.toLinearMap.comp
    ({ toFun := fun v i => if h : (i : ℕ) < k then v ⟨i,h⟩ else 0,
       map_add' := by intro v w; funext i; by_cases hi : (i : ℕ) < k <;> simp [hi]
       map_smul' := by intro c v; funext i; by_cases hi : (i : ℕ) < k <;> simp [hi] } :
      (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin 16 → ZMod 2))

/-- Section 5.8's aligned-block claim: the direction space is a genuine
`F₂`-submodule, defined as the range of the low-coordinate linear map. -/
noncomputable def alignedLowSpace (b : Module.Basis (Fin 16) (ZMod 2) B) (k : ℕ) :
    Submodule (ZMod 2) B := (alignedLowMap b k).range

/-- Section 5.8's aligned-block claim: the first `k ≤ 16` coordinates remain
independent under the actual basis encoding. -/
theorem alignedLowMap_injective (b : Module.Basis (Fin 16) (ZMod 2) B)
    (k : ℕ) (hk : k ≤ 16) : Function.Injective (alignedLowMap b k) := by
  intro v w h
  have hv := congrArg b.equivFun h
  simp only [alignedLowMap,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,LinearMap.coe_mk,AddHom.coe_mk] at hv
  funext i
  have hh := congrFun hv ⟨i,lt_of_lt_of_le i.isLt hk⟩
  simpa only [dite_eq_left i.isLt] using hh

/-- Section 5.8's aligned-block claim: the low-coordinate map sends each
standard coordinate vector to the corresponding Longfellow basis vector. -/
theorem alignedLowMap_basis (b : Module.Basis (Fin 16) (ZMod 2) B)
    (k : ℕ) (hk : k ≤ 16) (i : Fin k) :
    alignedLowMap b k (Pi.basisFun (ZMod 2) (Fin k) i) =
      b ⟨i,lt_of_lt_of_le i.isLt hk⟩ := by
  apply b.equivFun.injective
  simp only [alignedLowMap,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,LinearMap.coe_mk,AddHom.coe_mk]
  funext j
  rw [b.equivFun_self,Pi.basisFun_apply]
  by_cases hj : (j : ℕ) < k
  · simp [hj,Pi.single_apply,Fin.ext_iff,eq_comm]
  · have hne : (i : ℕ) ≠ j := by omega
    simp [hj,Fin.ext_iff,hne]

/-- Section 5.8's aligned-block claim: the direction submodule is precisely
the binary span of the first `k` prescribed basis vectors. -/
theorem alignedLowSpace_eq_span (b : Module.Basis (Fin 16) (ZMod 2) B)
    (k : ℕ) (hk : k ≤ 16) :
    alignedLowSpace b k = Submodule.span (ZMod 2)
      (Set.range fun i : Fin k => b ⟨i,lt_of_lt_of_le i.isLt hk⟩) := by
  rw [alignedLowSpace,LinearMap.range_eq_map,←(Pi.basisFun (ZMod 2) (Fin k)).span_eq,
    Submodule.map_span]
  have he : alignedLowMap b k '' Set.range (Pi.basisFun (ZMod 2) (Fin k)) =
      Set.range (fun i : Fin k => b ⟨i,lt_of_lt_of_le i.isLt hk⟩) := by
    ext x
    constructor
    · rintro ⟨v,⟨i,rfl⟩,rfl⟩
      exact ⟨i,(alignedLowMap_basis b k hk i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨i,rfl⟩,alignedLowMap_basis b k hk i⟩
  rw [he]

/-- Section 5.8's aligned-block claim: its direction space has binary
dimension exactly `k`, including `k = 0` and `k = 16`. -/
theorem alignedLowSpace_finrank (b : Module.Basis (Fin 16) (ZMod 2) B)
    (k : ℕ) (hk : k ≤ 16) : Module.finrank (ZMod 2) (alignedLowSpace b k) = k := by
  rw [alignedLowSpace,LinearMap.finrank_range_of_inj (alignedLowMap_injective b k hk)]
  simp

/-- Section 5.8's aligned-block claim: the direction space has exactly `2^k`
points, also when viewed as the additive subgroup used by `additiveDomain`. -/
theorem alignedLowSpace_card (b : Module.Basis (Fin 16) (ZMod 2) B)
    (k : ℕ) (hk : k ≤ 16) : Nat.card (alignedLowSpace b k).toAddSubgroup = 2^k := by
  have he := (LinearEquiv.ofInjective (alignedLowMap b k)
    (alignedLowMap_injective b k hk)).toEquiv
  rw [show Nat.card (alignedLowSpace b k).toAddSubgroup =
      Nat.card (alignedLowMap b k).range from rfl,←Nat.card_congr he]
  simp [Nat.card_eq_fintype_card,ZMod.card]

/-- Section 5.8's aligned-block claim: varying the low `k` bits adds exactly
the low-coordinate vector to the encoding of the block's first index. -/
theorem inj_aligned_offset (b : Module.Basis (Fin 16) (ZMod 2) B)
    (k c r : ℕ) (hr : r < 2^k) :
    inj b (c*2^k+r) = inj b (c*2^k) +
      alignedLowMap b k (fun i => if r.testBit i then 1 else 0) := by
  apply b.equivFun.injective
  rw [map_add]
  simp only [inj,alignedLowMap,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,LinearMap.coe_mk,AddHom.coe_mk]
  funext i
  rw [Nat.mul_comm c (2^k),Nat.testBit_two_pow_mul_add c hr]
  simp only [Pi.add_apply,Nat.testBit_two_pow_mul]
  by_cases hi : (i : ℕ) < k
  · simp [hi,Nat.not_le_of_lt hi]
  · simp [hi,Nat.le_of_not_gt hi]

variable [Fintype B] [CharP B 2]

/-- Section 5.8's aligned-block claim: every aligned block contained in the
sixteen-bit index range maps onto the affine translate of the first `k`
basis-vector span, with translation equal to the encoding of its first index. -/
theorem aligned_interval_eq (b : Module.Basis (Fin 16) (ZMod 2) B)
    (k c : ℕ) (hk : k ≤ 16) (hc : (c+1)*2^k ≤ 2^16) :
    (Finset.Ico (c*2^k) ((c+1)*2^k)).image (inj b) =
      affineDomain (additiveDomain (alignedLowSpace b k).toAddSubgroup)
        (inj b (c*2^k)) := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hj
    have hr : j-c*2^k < 2^k := by rw [Nat.add_mul] at hhi; omega
    have hj_eq : j = c*2^k+(j-c*2^k) := by omega
    rw [hj_eq,inj_aligned_offset b k c _ hr,mem_affineDomain_iff,
      add_sub_cancel_left,mem_additiveDomain]
    exact ⟨_,rfl⟩
  · rw [card_affineDomain,card_additiveDomain,alignedLowSpace_card b k hk,
      Finset.card_image_iff.mpr (by
        intro j hj l hl he
        exact inj_injective_below b ((Finset.mem_Ico.mp hj).2.trans_le hc)
          ((Finset.mem_Ico.mp hl).2.trans_le hc) he),Nat.card_Ico]
    rw [Nat.add_mul]
    simp

/-- Section 5.8's aligned-block claim: the actual image of the aligned
integer interval has exactly `2^k` distinct field points. -/
theorem aligned_interval_card (b : Module.Basis (Fin 16) (ZMod 2) B)
    (k c : ℕ) (hk : k ≤ 16) (hc : (c+1)*2^k ≤ 2^16) :
    ((Finset.Ico (c*2^k) ((c+1)*2^k)).image (inj b)).card = 2^k := by
  rw [aligned_interval_eq b k c hk hc,card_affineDomain,card_additiveDomain,
    alignedLowSpace_card b k hk]

end BinaryFieldCounterexamples.Longfellow
