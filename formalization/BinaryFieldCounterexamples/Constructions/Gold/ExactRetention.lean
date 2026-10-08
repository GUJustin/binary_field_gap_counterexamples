/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.SubspaceIncidence
public import BinaryFieldCounterexamples.Counting.SpanningSubspaceCount
/-!
# Exact probability and retention for subspace padding

Uniformly choosing an actual `w`-dimensional subspace spans with each fixed
codimension-`r` radical with the exact Gaussian ratio below. Double counting
therefore keeps the ceiling of that fraction of any indexed family.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Exact success probability for uniform subspace padding, in Gaussian form. -/
def paddingRetentionProbability (d w r : ℕ) : ℚ :=
  (2:ℚ)^(r*(d-w)) * gaussianBinomial 2 (d-r) (w-r) / gaussianBinomial 2 d w

/-- Binary cardinality and dimension give equivalent indexing of the subspaces. -/
theorem binarySubmodule_card_eq_pow_iff (W : Submodule (ZMod 2) V) (w : ℕ) :
    Nat.card W = 2^w ↔ finrank (ZMod 2) W = w := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  exact (Nat.pow_right_injective (by decide : 1<2)).eq_iff

/-- The denominator of the exact padding probability counts the actual choices. -/
theorem binarySubspacesOfCard_card_gaussian (d w : ℕ)
    (hd : finrank (ZMod 2) V = d) (hw : w ≤ d) :
    (binarySubspacesOfCard V w).card = gaussianBinomial 2 d w := by
  have h := subspacesOfFinrank_card_eq_gaussianBinomial (k := ZMod 2) (V := V) w (by omega)
  simpa [binarySubspacesOfCard,subspacesOfFinrank,Nat.card_eq_fintype_card,
    Fintype.card_subtype,←binarySubmodule_card_eq_pow_iff,hd] using h

/-- The numerator counts exactly the padding subspaces that span with a fixed radical. -/
theorem binarySubspacesOfCard_spanning_count (H : Submodule (ZMod 2) V) (d w r : ℕ)
    (hd : finrank (ZMod 2) V = d) (hH : finrank (ZMod 2) H = d-r)
    (hrw : r ≤ w) (hwd : w ≤ d) :
    ((binarySubspacesOfCard V w).filter (fun W => W ⊔ H = ⊤)).card =
      2^(r*(d-w)) * gaussianBinomial 2 (d-r) (w-r) := by
  have h := spanningSubspaces_natCard H d r w hd hH hrw hwd
  simpa [binarySubspacesOfCard,Nat.card_eq_fintype_card,Fintype.card_subtype,
    Finset.filter_filter,←binarySubmodule_card_eq_pow_iff,sup_comm] using h

/-- The stated rational probability is the successful fraction of the literal finite choice set. -/
theorem binarySubspacesOfCard_spanning_probability (H : Submodule (ZMod 2) V) (d w r : ℕ)
    (hd : finrank (ZMod 2) V = d) (hH : finrank (ZMod 2) H = d-r)
    (hrw : r ≤ w) (hwd : w ≤ d) :
    (((binarySubspacesOfCard V w).filter (fun W => W ⊔ H = ⊤)).card:ℚ) /
      (binarySubspacesOfCard V w).card = paddingRetentionProbability d w r := by
  rw [binarySubspacesOfCard_spanning_count H d w r hd hH hrw hwd,
    binarySubspacesOfCard_card_gaussian d w hd hwd]
  simp [paddingRetentionProbability]

/-- A single padding subspace keeps the ceiling of the exact uniform success fraction. -/
theorem exists_padding_subspace_retaining_exact {ι : Type*} (I : Finset ι)
    (H : ι → Submodule (ZMod 2) V) (d r w : ℕ)
    (hd : finrank (ZMod 2) V = d) (hrw : r ≤ w) (hwd : w ≤ d)
    (hH : ∀ i ∈ I, finrank (ZMod 2) (H i) = d-r) :
    ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = w ∧
      ⌈paddingRetentionProbability d w r * I.card⌉₊ ≤
        (I.filter (fun i => W ⊔ H i = ⊤)).card := by
  classical
  let G := binarySubspacesOfCard V w
  let M := 2^(r*(d-w)) * gaussianBinomial 2 (d-r) (w-r)
  have hG : G.Nonempty := binarySubspacesOfCard_nonempty w (by omega)
  have hsum : (∑ W ∈ G, (I.filter (fun i => W ⊔ H i = ⊤)).card) = I.card*M := by
    have hc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun (i : ι) (W : Submodule (ZMod 2) V) => W ⊔ H i = ⊤) (s := I) (t := G)
    change (∑ i ∈ I, (G.filter (fun W => W ⊔ H i = ⊤)).card) =
      ∑ W ∈ G, (I.filter (fun i => W ⊔ H i = ⊤)).card at hc
    rw [←hc]
    have hf : ∀ i ∈ I, (G.filter (fun W => W ⊔ H i = ⊤)).card = M := by
      intro i hi
      exact binarySubspacesOfCard_spanning_count (H i) d w r hd (hH i hi) hrw hwd
    rw [Finset.sum_congr rfl hf]
    simp
  have havg : (∑ _W ∈ G, I.card*M) ≤
      ∑ W ∈ G, G.card*(I.filter (fun i => W ⊔ H i = ⊤)).card := by
    conv_rhs => rw [←Finset.mul_sum,hsum]
    simp
  obtain ⟨W,hW,hret⟩ := Finset.exists_le_of_sum_le hG havg
  refine ⟨W,(binarySubmodule_card_eq_pow_iff W w).mp (Finset.mem_filter.mp hW).2,?_⟩
  apply Nat.ceil_le.mpr
  have hgpos : (0:ℚ) < G.card := by exact_mod_cast Finset.card_pos.mpr hG
  have hretq : (I.card:ℚ)*M ≤ G.card*(I.filter (fun i => W ⊔ H i = ⊤)).card := by
    exact_mod_cast hret
  have hgc : G.card = gaussianBinomial 2 d w := binarySubspacesOfCard_card_gaussian d w hd hwd
  have he : paddingRetentionProbability d w r = (M:ℚ)/G.card := by
    simp [paddingRetentionProbability,M,hgc]
  rw [he,div_mul_eq_mul_div]
  apply (div_le_iff₀ hgpos).mpr
  linarith
end BinaryFieldCounterexamples
