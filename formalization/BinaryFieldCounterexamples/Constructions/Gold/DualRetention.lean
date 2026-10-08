/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.SubspaceIncidence
public import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Choosing a padding subspace with exact retention

Apply uniform subspace incidence in the actual dual space. Avoiding the nonzero
annihilator of a radical is equivalent to the padding subspace and radical
spanning the whole space. The dual dimension identity supplies the requested
padding dimension, and the exact retained fraction includes its natural ceiling.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Module
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [Fintype (Dual (ZMod 2) V)]
attribute [local instance] Classical.propDecidable Classical.decEq

theorem dualCoannihilator_sup_eq_top_iff (U : Submodule (ZMod 2) (Dual (ZMod 2) V))
    (H : Submodule (ZMod 2) V) :
    U.dualCoannihilator ⊔ H = ⊤ ↔
      ¬ ∃ x ∈ (Finset.univ.filter (fun x : Dual (ZMod 2) V => x ∈ H.dualAnnihilator)).erase 0,
        x ∈ U := by
  classical
  rw [← Submodule.dualAnnihilator_eq_bot_iff, Submodule.dualAnnihilator_sup_eq,
    Subspace.dualCoannihilator_dualAnnihilator_eq]
  constructor
  · rintro he ⟨x,hx,hU⟩
    have hz : x ∈ (⊥ : Submodule (ZMod 2) (Dual (ZMod 2) V)) := by
      rw [← he]
      exact ⟨hU,(Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2⟩
    exact (Finset.mem_erase.mp hx).1 hz
  · intro hn
    apply eq_bot_iff.mpr
    intro x hx
    by_contra hzero
    apply hn
    exact ⟨x,Finset.mem_erase.mpr ⟨hzero,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx.2⟩⟩,hx.1⟩

theorem card_nonzero_dualAnnihilator (H : Submodule (ZMod 2) V) :
    ((Finset.univ.filter (fun x : Dual (ZMod 2) V => x ∈ H.dualAnnihilator)).erase 0).card =
      2^(finrank (ZMod 2) V-finrank (ZMod 2) H)-1 := by
  classical
  rw [Finset.card_erase_of_mem (by simp)]
  have hc : (Finset.univ.filter (fun x : Dual (ZMod 2) V => x ∈ H.dualAnnihilator)).card =
      Nat.card H.dualAnnihilator := by rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hc,Module.natCard_eq_pow_finrank (K := ZMod 2)]
  have hdim := Subspace.finrank_add_finrank_dualAnnihilator_eq H
  have he : finrank (ZMod 2) H.dualAnnihilator = finrank (ZMod 2) V-finrank (ZMod 2) H := by omega
  rw [he]
  simp [Nat.card_eq_fintype_card]
theorem exists_padding_subspace_retaining {ι : Type*} (I : Finset ι)
    (H : ι → Submodule (ZMod 2) V) (d r w : ℕ)
    (hd : finrank (ZMod 2) V=d) (hw : w≤d) (hr : r≤d) (hd0 : 0<d)
    (hH : ∀ i ∈ I, finrank (ZMod 2) (H i)=d-r) :
    ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W=w ∧
      ⌈(1-((2:ℚ)^r-1)*(2^(d-w)-1)/(2^d-1))*I.card⌉₊ ≤
        (I.filter (fun i => W ⊔ H i=⊤)).card := by
  classical
  let B (i : ι) := (Finset.univ.filter (fun x : Dual (ZMod 2) V => x ∈ (H i).dualAnnihilator)).erase 0
  have hcV : Fintype.card (Dual (ZMod 2) V)=2^d := by
    rw [← Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Subspace.dual_finrank_eq,hd]
    simp [Nat.card_eq_fintype_card]
  have hk : d-w≤finrank (ZMod 2) (Dual (ZMod 2) V) := by rw [Subspace.dual_finrank_eq,hd]; omega
  have hB : ∀ i ∈ I, ∀ x ∈ B i, x≠0 := by
    intro i hi x hx
    exact (Finset.mem_erase.mp hx).1
  have hR : ∀ i ∈ I, (B i).card≤2^r-1 := by
    intro i hi
    dsimp [B]
    rw [card_nonzero_dualAnnihilator,hd,hH i hi,Nat.sub_sub_self hr]
  have hcpos : 1<Fintype.card (Dual (ZMod 2) V) := by rw [hcV]; exact Nat.one_lt_two_pow hd0.ne'
  obtain ⟨U,hU,hret⟩ := binarySubspacesOfCard_retained_ceiling I B (2^r-1) (d-w) hk hcpos hB hR
  refine ⟨U.dualCoannihilator,?_,?_⟩
  · have hcard : Nat.card U=2^(d-w) := (Finset.mem_filter.mp hU).2
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] at hcard
    have hdimU : finrank (ZMod 2) U=d-w := by
      have hp : 2^finrank (ZMod 2) U=2^(d-w) := by simpa [Nat.card_eq_fintype_card] using hcard
      exact (Nat.pow_right_injective (by decide : 1<2)) hp
    have hs := Subspace.finrank_add_finrank_dualCoannihilator_eq U
    rw [hd,hdimU] at hs
    omega
  · have he : I.filter (fun i => U.dualCoannihilator ⊔ H i=⊤) =
        I.filter (fun i => ¬ ∃ x ∈ B i, x ∈ U) := by
      ext i
      simp only [Finset.mem_filter,dualCoannihilator_sup_eq_top_iff,B]
    rw [he]
    simpa only [hcV,Nat.cast_sub (show 1≤2^r from Nat.one_le_two_pow),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hret
end BinaryFieldCounterexamples
