/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.QuadraticNearJohnsonCompanions
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.ThresholdArithmetic
/-!
# Main theorem companion: retaining more than half the quadratic population

Section 1's consequence of Corollary 4.2 says `q≥M` gives more than `M/2`
exceptional challenges. This follows from its literal rounded second-moment
bound, and is assembled here for the actual received pair.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
/-- Section 1's unassembled Corollary 4.2 consequence: on every prescribed
binary domain, `q≥M` gives one fixed pair with strictly more than `M/2`
distinct exceptional challenges and the exact printed common agreement. -/
theorem quadratic_near_johnson_more_than_half_population
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (K : ℕ) (hK : 2≤K) (hpow : ∃ k : ℕ,K=2^k)
    (hD : (additiveDomain D).card=16*K)
    (hq : (16*K-1)*(16*K-2)/6≤Fintype.card F) :
    let E := additiveDomain D
    let M := (16*K-1)*(16*K-2)/6
    ∃ f g : E → F, commonAgreementEQ E K f g (2*K-1) ∧
      (M : ℚ)/2 < (badChallenges E K f g (4*K-1)).card := by
  obtain ⟨θ,hc,hcount⟩ := quadratic_near_johnson_same_field D K hK hpow hD
  let E := additiveDomain D
  let f : E → F := fun x => (x : F)^(8*K-1)+θ*(x : F)^(4*K-1)
  let g : E → F := fun x => (x : F)^(2*K-1)
  let M := (16*K-1)*(16*K-2)/6
  have hprod : 31*30≤(16*K-1)*(16*K-2) := Nat.mul_le_mul (by omega) (by omega)
  have hdiv := Nat.div_le_div_right hprod (c:=6)
  have hM : 0<M := by dsimp [M]; norm_num at hdiv; omega
  refine ⟨f,g,hc,?_⟩
  apply (quadratic_collision_ceiling_gt_half M (Fintype.card F) hM hq).trans_le
  exact Nat.cast_le.mpr ((le_max_right _ _).trans hcount)
end BinaryFieldCounterexamples
