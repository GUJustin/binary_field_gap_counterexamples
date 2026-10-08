/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.Longfellow
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic
/-!
# Longfellow's literal binary index domain

Section 5.8 defines `inj(j)` by the sixteen bits of `j` in the prescribed
power basis. The definitions below use an actual binary basis, so no domain
inclusion or domain cardinality is assumed. The specification's power basis
is obtained by taking `b i = g^i`.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Longfellow
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]

/-- Section 5.8's map `inj`: use the sixteen literal binary digits as basis coordinates. -/
noncomputable def inj (b : Module.Basis (Fin 16) (ZMod 2) B) (j : ℕ) : B :=
  b.equivFun.symm (fun i => if j.testBit i then 1 else 0)

/-- Section 5.8's bit injection is the sum printed in the paper. -/
theorem inj_eq_sum (b : Module.Basis (Fin 16) (ZMod 2) B) (j : ℕ) :
    inj b j = ∑ i : Fin 16, (if j.testBit i then (1 : ZMod 2) else 0) • b i := by
  exact b.equivFun_symm_apply _

/-- Section 5.8: the binary encoding is injective on the prescribed sixteen-bit range. -/
theorem inj_injective_below (b : Module.Basis (Fin 16) (ZMod 2) B)
    {j k : ℕ} (hj : j < 2^16) (hk : k < 2^16) (he : inj b j = inj b k) : j=k := by
  have hv := congrArg b.equivFun he
  simp only [inj,LinearEquiv.apply_symm_apply] at hv
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 16
  · have h := congrFun hv ⟨i,hi⟩
    cases hji : j.testBit i <;> cases hki : k.testBit i <;> simp_all
  · rw [Nat.testBit_eq_false_of_lt (hj.trans_le (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_eq_false_of_lt (hk.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]

/-- Section 5.8's queried domain, the literal image of `[2K-1,e)`. -/
noncomputable def domain (b : Module.Basis (Fin 16) (ZMod 2) B) (e K : ℕ) : Finset B :=
  (Finset.Ico (2*K-1) e).image (inj b)

/-- Section 5.8: the actual queried-domain cardinality is `e-2K+1`. -/
theorem domain_card (b : Module.Basis (Fin 16) (ZMod 2) B)
    (e K : ℕ) (he : e < 2^16) (hK : 1 ≤ K) (hlo : 2*K ≤ e) :
    (domain b e K).card = e-2*K+1 := by
  rw [domain,Finset.card_image_iff.mpr]
  · rw [Nat.card_Ico]
    omega
  · intro j hj k hk heq
    exact inj_injective_below b ((Finset.mem_Ico.mp hj).2.trans he)
      ((Finset.mem_Ico.mp hk).2.trans he) heq

/-- Section 5.8's eleven freely varying low coordinates, mapped into the actual basis. -/
noncomputable def lowMap (b : Module.Basis (Fin 16) (ZMod 2) B) :
    (Fin 11 → ZMod 2) →ₗ[ZMod 2] B :=
  b.equivFun.symm.toLinearMap.comp
    ({
      toFun := fun v i => if h : (i : ℕ) < 11 then v ⟨i,h⟩ else 0,
      map_add' := by intro v w; funext i; by_cases hi : (i : ℕ) < 11 <;> simp [hi]
      map_smul' := by intro c v; funext i; by_cases hi : (i : ℕ) < 11 <;> simp [hi] } : (Fin 11 → ZMod 2) →ₗ[ZMod 2] (Fin 16 → ZMod 2))

/-- Section 5.8's low-coordinate map is injective, since the basis is independent. -/
theorem lowMap_injective (b : Module.Basis (Fin 16) (ZMod 2) B) :
    Function.Injective (lowMap b) := by
  intro v w h
  have hv := congrArg b.equivFun h
  simp only [lowMap,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,LinearMap.coe_mk,AddHom.coe_mk] at hv
  funext i
  have hh := congrFun hv ⟨i,by omega⟩
  simpa only [dif_pos i.isLt] using hh

/-- Section 5.8's actual additive eleven-space. -/
noncomputable def lowSpace (b : Module.Basis (Fin 16) (ZMod 2) B) : AddSubgroup B :=
  (lowMap b).range.toAddSubgroup

/-- Section 5.8: the low-coordinate subspace has exactly `2048` elements. -/
theorem lowSpace_card (b : Module.Basis (Fin 16) (ZMod 2) B) :
    Nat.card (lowSpace b) = 2^11 := by
  have he := (LinearEquiv.ofInjective (lowMap b) (lowMap_injective b)).toEquiv
  rw [show Nat.card (lowSpace b) = Nat.card (lowMap b).range from rfl,
    ←Nat.card_congr he]
  simp [Nat.card_eq_fintype_card,ZMod.card]

/-- Section 5.8: every index in `[2048,4096)` belongs to the affine low eleven-space. -/
theorem central_index_mem (b : Module.Basis (Fin 16) (ZMod 2) B)
    {j : ℕ} (hj : 2048 ≤ j) (hj' : j < 4096) :
    inj b j ∈ affineDomain (additiveDomain (lowSpace b)) (b ⟨11,by decide⟩) := by
  let r := j-2048
  have hr : r < 2^11 := by dsimp [r]; norm_num; omega
  have he : j=2^11+r := by dsimp [r]; norm_num; omega
  have heq : inj b j = b ⟨11,by decide⟩ + lowMap b
      (fun i => if r.testBit i then 1 else 0) := by
    apply b.equivFun.injective
    rw [map_add]
    simp only [inj,lowMap,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply,LinearMap.coe_mk,AddHom.coe_mk]
    funext i
    simp only [Pi.add_apply,b.equivFun_self,Fin.ext_iff,Fin.val_mk]
    by_cases hi : (i : ℕ) < 11
    · have hn : ¬ (11 : ℕ) = i := by omega
      simp only [he,Nat.testBit_two_pow_add_gt hi,hn,ite_false,zero_add,dite_eq_left hi]
    · by_cases hi' : (i : ℕ)=11
      · have hifin : i=(⟨11,by decide⟩ : Fin 16) := Fin.ext hi'
        subst i
        simp only [Fin.val_mk,he,Nat.testBit_two_pow_add_eq,
          Nat.testBit_eq_false_of_lt hr,Bool.not_false,ite_true,Nat.lt_irrefl,dite_false,
          add_zero]
      · have hbig : 12 ≤ (i : ℕ) := by omega
        have hlt : j < 2^(i : ℕ) := hj'.trans_le (by
          calc 4096=2^12 := by norm_num
               _ ≤ _ := Nat.pow_le_pow_right (by decide) hbig)
        have hn : ¬ (11 : ℕ) = i := by omega
        simp only [Nat.testBit_eq_false_of_lt hlt,hi,hn,ite_false,dite_false,
          Bool.false_eq_true,add_zero]
  rw [heq, mem_affineDomain_iff,add_sub_cancel_left,mem_additiveDomain]
  exact ⟨_,rfl⟩

/-- Section 5.8: `[2048,4096)` maps onto the specified affine eleven-space,
not merely a subset of some space of unknown dimension. -/
theorem central_interval_eq (b : Module.Basis (Fin 16) (ZMod 2) B) :
    (Finset.Ico 2048 4096).image (inj b) =
      affineDomain (additiveDomain (lowSpace b)) (b ⟨11,by decide⟩) := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    exact central_index_mem b (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
  · rw [card_affineDomain,card_additiveDomain,lowSpace_card,
      Finset.card_image_iff.mpr (by
        intro j hj k hk he
        exact inj_injective_below b (by have := (Finset.mem_Ico.mp hj).2; norm_num; omega)
          (by have := (Finset.mem_Ico.mp hk).2; norm_num; omega) he),Nat.card_Ico]
    norm_num

/-- Corollary 5.19's domain prerequisite is proved for the actual index interval. -/
theorem central_space_subset_domain (b : Module.Basis (Fin 16) (ZMod 2) B)
    (e K : ℕ) (hlo : 2*K-1 ≤ 2048) (hhi : 4096 ≤ e) :
    affineDomain (additiveDomain (lowSpace b)) (b ⟨11,by decide⟩) ⊆ domain b e K := by
  rw [←central_interval_eq,domain]
  apply Finset.image_subset_image
  intro j hj
  have hh := Finset.mem_Ico.mp hj
  exact Finset.mem_Ico.mpr ⟨hlo.trans hh.1,hh.2.trans_le hhi⟩
end BinaryFieldCounterexamples.Longfellow
