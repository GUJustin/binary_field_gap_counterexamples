/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.TemplateCounts
public import BinaryFieldCounterexamples.Counting.GaussianIdentities
public import BinaryFieldCounterexamples.Counting.GaussianEstimates
/-!
# Exact tree-frame arithmetic

The proved Gaussian frame product and actual tree orbit establish exact
denominator divisibility and the original Gaussian-times-minimal-count factor.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
/-- Exact natural Gaussian factorization of the ordered binary-frame product. -/
theorem binaryFrameProduct_eq_gaussian_mul (d r : ℕ) (hr : r≤d) :
    binaryFrameProduct d r=gaussianBinomial 2 d r*binaryFrameProduct r r := by
  rw [gaussianBinomial_eq_gaussianPascal 2 d r (by decide)]
  apply Nat.cast_injective (R := ℚ)
  change ((∏ i ∈ Finset.range r, (2^d-2^i) : ℕ):ℚ)=_
  rw [Nat.cast_mul,cast_gaussianFrameProduct 2 d r (by decide) hr]
  change _=(gaussianPascal 2 d r:ℚ)*((∏ i ∈ Finset.range r, (2^r-2^i) : ℕ):ℚ)
  rw [cast_gaussianFrameProduct 2 r r (by decide) le_rfl]
  exact (gaussianPascal_frame_product 2 d r (by decide) hr).symm
/-- The literal tree orbit proves exact divisibility by the manuscript denominator. -/
theorem treeSupportCount_mul_denominator (n d : ℕ) (hd : 2^(n+2)-1≤d) :
    treeSupportCount (n+2) d*treeDenominator (n+2)=binaryFrameProduct d (2^(n+2)-1) := by
  let V := Fin d → ZMod 2
  have hv : Module.finrank (ZMod 2) V=d := by simp [V]
  have hfamily : Nat.card (affinePullbackFamily V (template n))=treeSupportCount (n+2) d := by
    rw [←treeSupportFamily_card,treeSupportFamily_card_eq n (by simpa [hv] using hd),hv]
  have hT : Nat.card (TemplateSpace n)=2^(2^(n+2)-1) := by
    rw [Nat.card_eq_fintype_card,templateSpace_card]
  have h := affinePullbackFamily_card_mul_stabilizer (V := V) (template n) (template_period_iff n)
  rw [template_stabilizer_card,surjectiveAffineMaps_card,
    surjectiveLinearMaps_card (by simpa [templateSpace_finrank,hv] using hd),
    hfamily,hT,templateSpace_finrank,hv] at h
  have hp : (∏ i : Fin (2^(n+2)-1), (2^d-2^(i:ℕ)))=binaryFrameProduct d (2^(n+2)-1) :=
    Fin.prod_univ_eq_prod_range (fun i => 2^d-2^i) (2^(n+2)-1)
  rw [hp] at h
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0<(2:ℕ)) (2^(n+2)-1))
  calc
    _=treeSupportCount (n+2) d*(2^(2^(n+2)-1)*treeDenominator (n+2)) := by ring
    _=_ := h
/-- The manuscript Gaussian times minimal-domain count is the exact extended-domain count. -/
theorem treeSupportCount_eq_gaussian_mul (n d : ℕ) (hd : 2^(n+2)-1≤d) :
    treeSupportCount (n+2) d=gaussianBinomial 2 d (2^(n+2)-1)*
      treeSupportCount (n+2) (2^(n+2)-1) := by
  apply Nat.eq_of_mul_eq_mul_right (treeDenominator_pos (n+2))
  rw [treeSupportCount_mul_denominator n d hd,mul_assoc,
    treeSupportCount_mul_denominator n (2^(n+2)-1) le_rfl]
  exact binaryFrameProduct_eq_gaussian_mul d (2^(n+2)-1) hd
end BinaryFieldCounterexamples.Trees
