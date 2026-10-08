/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.MomentPopulation
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
/-!
# Uniform binary subspace incidence and retained challenges

Linear automorphisms make every nonzero vector occur in equally many subspaces
of a fixed size. Double counting yields the exact incidence identity. A union
bound and finite averaging then choose one subspace avoiding the forbidden
vectors for the stated ceiling number of challenges. All subspaces and incidences
are concrete finite sets; no distributional or population assumption is used.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
theorem exists_binary_linearEquiv_apply_eq {x y : V} (hx : x≠0) (hy : y≠0) :
    ∃ g : V ≃ₗ[ZMod 2] V, g x=y := by
  let fx := LinearMap.toSpanSingleton (ZMod 2) V x
  let fy := LinearMap.toSpanSingleton (ZMod 2) V y
  let ex := LinearEquiv.ofInjective fx (smul_left_injective (ZMod 2) hx)
  let ey := LinearEquiv.ofInjective fy (smul_left_injective (ZMod 2) hy)
  obtain ⟨g,hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨g,?_⟩
  have he := hg (ex 1)
  simp only [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] at he
  have hex : ((ex 1 : LinearMap.range fx) : V)=x := by
    change (1 : ZMod 2) • x=x
    exact one_smul _ _
  have hey : ((ey 1 : LinearMap.range fy) : V)=y := by
    change (1 : ZMod 2) • y=y
    exact one_smul _ _
  rw [hex,hey] at he
  exact he.symm
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
theorem binary_subspace_incidence_uniform (k : ℕ) {x y : V} (hx : x≠0) (hy : y≠0) :
    Nat.card {W : Submodule (ZMod 2) V // Nat.card W=2^k ∧ x∈W} =
      Nat.card {W : Submodule (ZMod 2) V // Nat.card W=2^k ∧ y∈W} := by
  classical
  obtain ⟨g,hg⟩ := exists_binary_linearEquiv_apply_eq hx hy
  let e := (Submodule.orderIsoMapComap g).toEquiv
  apply Nat.card_congr (Equiv.subtypeEquiv e ?_)
  intro W
  have hc : Nat.card (e W)=Nat.card W := (Nat.card_congr (g.submoduleMap W).toEquiv).symm
  have hm : y∈e W ↔ x∈W := by
    change y∈W.map g.toLinearMap ↔ x∈W
    rw [← hg,Submodule.mem_map]
    constructor
    · rintro ⟨z,hz,he⟩
      exact g.injective he ▸ hz
    · intro h
      exact ⟨x,h,rfl⟩
  rw [hc,hm]
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
noncomputable def binarySubspacesOfCard (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (k : ℕ) : Finset (Submodule (ZMod 2) V) := by
  classical
  exact Finset.univ.filter fun W => Nat.card W=2^k

theorem binarySubspacesOfCard_incidence_uniform (k : ℕ) {x y : V} (hx : x≠0) (hy : y≠0) :
    ((binarySubspacesOfCard V k).filter (fun W => x∈W)).card =
      ((binarySubspacesOfCard V k).filter (fun W => y∈W)).card := by
  classical
  have h := binary_subspace_incidence_uniform k hx hy
  simpa [binarySubspacesOfCard,Nat.card_eq_fintype_card,Fintype.card_subtype,
    Finset.filter_filter] using h
theorem binarySubspacesOfCard_incidence_count (k : ℕ) {x : V} (hx : x≠0) :
    (binarySubspacesOfCard V k).card*(2^k-1) =
      (Fintype.card V-1)*((binarySubspacesOfCard V k).filter (fun W => x∈W)).card := by
  classical
  have hcW (W : Submodule (ZMod 2) V) :
      ((Finset.univ.erase (0:V)).filter (fun z => z∈W)).card=Nat.card W-1 := by
    have he : (Finset.univ.erase (0:V)).filter (fun z => z∈W) =
        (Finset.univ.filter (fun z : V => z∈W)).erase 0 := by ext z; simp
    rw [he,Finset.card_erase_of_mem (by simp)]
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (W : Submodule (ZMod 2) V) (z : V) => z∈W)
    (s := binarySubspacesOfCard V k) (t := Finset.univ.erase (0:V))
  have hleft : (∑ W ∈ binarySubspacesOfCard V k,
      ((Finset.univ.erase (0:V)).bipartiteAbove (fun W z => z∈W) W).card) =
      (binarySubspacesOfCard V k).card*(2^k-1) := by
    have he : ∀ W ∈ binarySubspacesOfCard V k,
        ((Finset.univ.erase (0:V)).bipartiteAbove (fun W z => z∈W) W).card=2^k-1 := by
      intro W hW
      rw [Finset.bipartiteAbove,hcW]
      have hcard : Nat.card W=2^k := (Finset.mem_filter.mp hW).2
      rw [hcard]
    simp_rw [Finset.sum_congr rfl he]
    simp
  have hright : (∑ z ∈ Finset.univ.erase (0:V),
      ((binarySubspacesOfCard V k).bipartiteBelow (fun W z => z∈W) z).card) =
      (Fintype.card V-1)*((binarySubspacesOfCard V k).filter (fun W => x∈W)).card := by
    have he : ∀ z ∈ Finset.univ.erase (0:V),
        ((binarySubspacesOfCard V k).bipartiteBelow (fun W z => z∈W) z).card =
          ((binarySubspacesOfCard V k).filter (fun W => x∈W)).card := by
      intro z hz
      exact binarySubspacesOfCard_incidence_uniform k (Finset.mem_erase.mp hz).1 hx
    rw [Finset.sum_congr rfl he]
    simp
  rw [hleft,hright] at h
  exact h
theorem binarySubspacesOfCard_nonempty (k : ℕ) (hk : k≤Module.finrank (ZMod 2) V) :
    (binarySubspacesOfCard V k).Nonempty := by
  classical
  let e := Module.finBasis (ZMod 2) V
  let f : Fin k → Fin (Module.finrank (ZMod 2) V) := Fin.castLE hk
  have hf : Function.Injective f := Fin.castLE_injective hk
  have hi : LinearIndependent (ZMod 2) (fun i : Fin k => e (f i)) := e.linearIndependent.comp f hf
  let W := Submodule.span (ZMod 2) (Set.range (fun i : Fin k => e (f i)))
  refine ⟨W,?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  change Nat.card (ZMod 2)^Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun i : Fin k => e (f i))))=2^k
  rw [finrank_span_eq_card hi]
  simp [Nat.card_eq_fintype_card]
theorem binarySubspacesOfCard_hits_bound (k : ℕ) (B : Finset V)
    (hB : ∀ x ∈ B, x ≠ 0) :
    (Fintype.card V-1)*((binarySubspacesOfCard V k).filter
      (fun W => ∃ x ∈ B, x ∈ W)).card ≤
      (binarySubspacesOfCard V k).card * B.card * (2^k-1) := by
  classical
  let G := binarySubspacesOfCard V k
  have he : G.filter (fun W => ∃ x ∈ B, x ∈ W) =
      B.biUnion (fun x => G.filter (fun W => x ∈ W)) := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [he]
  calc
    (Fintype.card V-1)*(B.biUnion (fun x => G.filter (fun W => x ∈ W))).card
        ≤ (Fintype.card V-1)*∑ x ∈ B, (G.filter (fun W => x ∈ W)).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ x ∈ B, (Fintype.card V-1)*(G.filter (fun W => x ∈ W)).card := by
      rw [Finset.mul_sum]
    _ = ∑ _x ∈ B, G.card*(2^k-1) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (binarySubspacesOfCard_incidence_count k (hB x hx)).symm
    _ = G.card*B.card*(2^k-1) := by simp; ring
theorem binarySubspacesOfCard_retention {ι : Type*} (I : Finset ι)
    (B : ι → Finset V) (R k : ℕ) (hk : k ≤ Module.finrank (ZMod 2) V)
    (hB : ∀ i ∈ I, ∀ x ∈ B i, x ≠ 0) (hR : ∀ i ∈ I, (B i).card ≤ R) :
    ∃ W ∈ binarySubspacesOfCard V k,
      (Fintype.card V-1)*(I.filter (fun i => ∃ x ∈ B i, x ∈ W)).card ≤
        I.card*R*(2^k-1) := by
  classical
  let G := binarySubspacesOfCard V k
  let hit (i : ι) (W : Submodule (ZMod 2) V) := ∃ x ∈ B i, x ∈ W
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    hit (s := I) (t := G)
  have htotal : (∑ W ∈ G, (Fintype.card V-1)*(I.filter (fun i => hit i W)).card) ≤
      ∑ _W ∈ G, I.card*R*(2^k-1) := by
    rw [← Finset.mul_sum]
    have he : (∑ W ∈ G, (I.filter (fun i => hit i W)).card) =
        ∑ i ∈ I, (G.filter (hit i)).card := hcount.symm
    rw [he, Finset.mul_sum]
    calc
      (∑ i ∈ I, (Fintype.card V-1)*(G.filter (hit i)).card)
          ≤ ∑ i ∈ I, G.card*R*(2^k-1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (binarySubspacesOfCard_hits_bound k (B i) (hB i hi)).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hR i hi)))
      _ = ∑ _W ∈ G, I.card*R*(2^k-1) := by simp; ring
  exact Finset.exists_le_of_sum_le (binarySubspacesOfCard_nonempty k hk) htotal
theorem binarySubspacesOfCard_retained_ceiling {ι : Type*} (I : Finset ι)
    (B : ι → Finset V) (R k : ℕ) (hk : k ≤ Module.finrank (ZMod 2) V)
    (hV : 1 < Fintype.card V)
    (hB : ∀ i ∈ I, ∀ x ∈ B i, x ≠ 0) (hR : ∀ i ∈ I, (B i).card ≤ R) :
    ∃ W ∈ binarySubspacesOfCard V k,
      ⌈(1-(R : ℚ)*(2^k-1)/(Fintype.card V-1))*I.card⌉₊ ≤
        (I.filter (fun i => ¬ ∃ x ∈ B i, x ∈ W)).card := by
  classical
  obtain ⟨W,hW,h⟩ := binarySubspacesOfCard_retention I B R k hk hB hR
  refine ⟨W,hW,?_⟩
  apply Nat.ceil_le.mpr
  have htwo : 1 ≤ 2^k := Nat.one_le_two_pow
  have hh : ((Fintype.card V : ℚ)-1)*
      ((I.filter (fun i => ∃ x ∈ B i, x ∈ W)).card : ℚ) ≤
        (I.card : ℚ)*R*(2^k-1) := by
    have hh := (show ((Fintype.card V-1 : ℕ) : ℚ)*
      ((I.filter (fun i => ∃ x ∈ B i, x ∈ W)).card : ℚ) ≤
      (I.card : ℚ)*R*((2^k-1 : ℕ) : ℚ) by exact_mod_cast h)
    simpa only [Nat.cast_sub hV.le, Nat.cast_sub htwo, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hh
  have hc := Finset.card_filter_add_card_filter_not
    (s := I) (p := fun i => ∃ x ∈ B i, x ∈ W)
  have hcq : ((I.filter (fun i => ∃ x ∈ B i, x ∈ W)).card : ℚ) +
      (I.filter (fun i => ¬ ∃ x ∈ B i, x ∈ W)).card = I.card := by exact_mod_cast hc
  have hp : (0 : ℚ) < Fintype.card V-1 := by
    have hp : (1 : ℚ) < Fintype.card V := by exact_mod_cast hV
    linarith
  apply (mul_le_mul_iff_of_pos_right hp).mp
  field_simp
  nlinarith
end BinaryFieldCounterexamples
