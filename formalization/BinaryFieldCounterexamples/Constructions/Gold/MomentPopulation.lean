/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Family
public import BinaryFieldCounterexamples.Constructions.Gold.MomentKernel
public import BinaryFieldCounterexamples.Constructions.Gold.MinimumRank
public import BinaryFieldCounterexamples.Constructions.Gold.MinimumRankPopulation
public import BinaryFieldCounterexamples.Constructions.Gold.DimensionArithmetic
/-!
# Quantitative population of the actual Gold moment tensors

The concrete kernel satisfies the proved alternating-code minimum rank bound.
Its exact dimension lower bound and the positive `Delta` arithmetic turn the
universal Fourier population inequality into the manuscript's original
`(2^Delta-1) [floor(d/2) choose t]_4` count, without rounding loss.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- Every nonzero tensor in the actual moment kernel has the required matrix rank. -/
theorem goldMomentKernel_matrix_minimum_rank
    (D : AddSubgroup B) [Fintype D] (d t : ℕ) (hD : Nat.card D=2^d)
    (e : Module.Basis (Fin d) (ZMod 2) D) (ht : 1≤t) (hdt : 2*t≤d)
    (A : goldMomentKernel D (basisParameter D e) t) (hA : A≠0) :
    2*t ≤ (tensorAlternatingMatrix A.val).rank := by
  rw [← tensorPolarRank_basis_eq_matrix_rank D e A.val]
  have hd : d-1+1=d := by omega
  have hD' : Nat.card D=2^(d-1+1) := by simpa only [hd] using hD
  exact tensorPolarRank_lower_bound_of_moments D (d-1) hD' (basisParameter D e) e
    (basisParameter_eval D e) A.val (fun hz => hA (Subtype.ext hz)) t (by omega)
    ((mem_goldMomentKernel D (basisParameter D e) t A.val).mp A.property)

/-- The locator parameter set is exactly the minimum-rank level of the actual kernel. -/
theorem card_momentTensors_eq_rank_kernel
    (D : AddSubgroup B) [Fintype D] (d t : ℕ)
    (e : Module.Basis (Fin d) (ZMod 2) D) :
    (momentTensors D (basisParameter D e) t).card =
      Nat.card {A : goldMomentKernel D (basisParameter D e) t //
        (tensorAlternatingMatrix A.val).rank=2*t} := by
  classical
  letI : Fintype (TensorCoordinates d) := inferInstanceAs (Fintype (TensorIndex d → ZMod 2))
  let G := {A : TensorCoordinates d // A ∈ momentTensors D (basisParameter D e) t}
  let K := goldMomentKernel D (basisParameter D e) t
  let R := {A : K // (tensorAlternatingMatrix A.val).rank=2*t}
  let equiv : G ≃ R := {
    toFun := fun A => ⟨⟨A.val, (mem_goldMomentKernel D (basisParameter D e) t A.val).mpr
      ((mem_momentTensors D (basisParameter D e) t A.val).mp A.property).2⟩, by
        rw [← tensorPolarRank_basis_eq_matrix_rank D e A.val]
        exact ((mem_momentTensors D (basisParameter D e) t A.val).mp A.property).1⟩
    invFun := fun A => ⟨A.val.val, (mem_momentTensors D (basisParameter D e) t A.val.val).mpr
      ⟨by rw [tensorPolarRank_basis_eq_matrix_rank D e A.val.val]; exact A.property,
        (mem_goldMomentKernel D (basisParameter D e) t A.val.val).mp A.val.property⟩⟩
    left_inv := fun A => rfl
    right_inv := fun A => rfl }
  calc
    _ = Nat.card G := by simp [G,Nat.card_eq_fintype_card]
    _ = Nat.card R := Nat.card_congr equiv
/-- The prescribed domain cardinality supplies a binary basis of the stated dimension. -/
theorem exists_gold_basis
    (D : AddSubgroup B) [Fintype D] (d : ℕ) (hD : Nat.card D=2^d) :
    Nonempty (Module.Basis (Fin d) (ZMod 2) D) := by
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
  rw [hD] at he
  simp only [Nat.card_eq_fintype_card,ZMod.card] at he
  have hd : Module.finrank (ZMod 2) D=d := by
    apply Nat.le_antisymm
    · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp he.ge
    · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp he.le
  exact ⟨Module.finBasisOfFinrankEq (ZMod 2) D hd⟩

/-- A prescribed additive subspace cannot exceed the ambient binary dimension. -/
theorem gold_dimension_le_field_dimension
    (D : AddSubgroup B) [Fintype D] (m d : ℕ)
    (hB : Fintype.card B=2^m) (hD : Nat.card D=2^d) : d≤m := by
  have hc : Nat.card D≤Nat.card B :=
    Nat.card_le_card_of_injective (fun x : D => (x : B)) Subtype.coe_injective
  rw [hD,Nat.card_eq_fintype_card,hB] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hc
/-- The actual moment tensors satisfy the exact quantitative Gold population bound. -/
theorem card_momentTensors_lower_bound
    (D : AddSubgroup B) [Fintype D] (m d t : ℕ)
    (hB : Fintype.card B=2^m) (hD : Nat.card D=2^d)
    (e : Module.Basis (Fin d) (ZMod 2) D) (ht : 1≤t) (hdt : 2*t≤d)
    (hΔ : 1≤m-t*(m-d+if Even d then 1 else 0)) :
    (2^(m-t*(m-d+if Even d then 1 else 0))-1)*gaussianBinomial 4 (d/2) t ≤
      (momentTensors D (basisParameter D e) t).card := by
  classical
  let K := goldMomentKernel D (basisParameter D e) t
  let Δ := m-t*(m-d+if Even d then 1 else 0)
  have hpop := alternatingCode_minimumRank_count_lower_bound d t ht hdt K
    (goldMomentKernel_matrix_minimum_rank D d t hD e ht hdt)
  have hc : (Finset.univ.filter (fun A : K => (tensorAlternatingMatrix A.val).rank=2*t)).card =
      (momentTensors D (basisParameter D e) t).card := by
    rw [card_momentTensors_eq_rank_kernel]
    simp [Nat.card_eq_fintype_card,Fintype.card_subtype,K]
  rw [hc] at hpop
  have hdim := gold_dimension_le_field_dimension D m d hB hD
  have hsize := goldMomentKernel_card_lower_bound_delta D (basisParameter D e) t m hB hdim
    (by omega) ht hΔ
  have hpar : (if d%2=0 then 1 else 0)=(if Even d then 1 else 0) := by
    simp [Nat.even_iff]
  have hg : (alternatingFourierParameter d)^(d/2-t) =
      (2:ℚ)^((d-if Even d then 1 else 0)*(d/2-t)) := by
    rw [alternatingFourierParameter,hpar,←pow_mul]
  have hgpos : 0<(alternatingFourierParameter d)^(d/2-t) := by rw [hg]; positivity
  have hratio : (2:ℚ)^Δ ≤ (Nat.card K : ℚ)/(alternatingFourierParameter d)^(d/2-t) := by
    apply (le_div_iff₀ hgpos).mpr
    rw [hg,mul_comm]
    exact_mod_cast hsize
  have hpow : 1≤2^Δ := Nat.one_le_pow _ _ (by decide)
  have hcast : (((2^Δ-1)*gaussianBinomial 4 (d/2) t : ℕ):ℚ) =
      (gaussianBinomial 4 (d/2) t : ℚ)*((2:ℚ)^Δ-1) := by
    rw [Nat.cast_mul,Nat.cast_sub hpow]
    push_cast
    ring
  have hfinal : (((2^Δ-1)*gaussianBinomial 4 (d/2) t : ℕ):ℚ) ≤
      ((momentTensors D (basisParameter D e) t).card : ℚ) := by
    rw [hcast]
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hratio 1) (Nat.cast_nonneg _)).trans hpop
  exact_mod_cast hfinal
end BinaryFieldCounterexamples.Gold
