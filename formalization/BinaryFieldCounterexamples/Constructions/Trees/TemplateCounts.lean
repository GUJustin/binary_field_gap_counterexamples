/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.StabilizerForms
public import BinaryFieldCounterexamples.Constructions.Trees.BranchRecovery
public import BinaryFieldCounterexamples.Counting.TreeSupportCounts
public import BinaryFieldCounterexamples.Constructions.Trees.SurjectivePullbacks
public import BinaryFieldCounterexamples.Constructions.Trees.BaseCount
public import BinaryFieldCounterexamples.Constructions.Trees.SurjectiveLinearCount
public import BinaryFieldCounterexamples.Constructions.Trees.SupportFamily
public import BinaryFieldCounterexamples.Counting.TreePositivity
/-!
# Exact minimal-template stabilizer counts

The actual affine branch-recovery theorem and exhaustive stabilizer normal
forms give the recurrence. The explicit height-two count then identifies its
closed value with the manuscript denominator. A separate exact cancellation
lemma connects affine-surjection populations to literal pullback families.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
  affineFunctionMulAction affineEquivFintype
/-- The actual affine stabilizer of a minimal template obeys the exact recursive count. -/
theorem template_stabilizer_card_succ (n : ℕ) :
    Nat.card (affineFunctionStabilizer (template (n+1)))=
      2*(2^(2^(n+2)-1))^2*(Nat.card (affineFunctionStabilizer (template n)))^2 := by
  change Nat.card (affineFunctionStabilizer (branch (template n) (template n)))=_
  have hf : ∃ x y, template n x≠template n y := by
    obtain ⟨x,hx⟩ := template_surjective n 0
    obtain ⟨y,hy⟩ := template_surjective n 1
    exact ⟨x,y,by rw [hx,hy]; decide⟩
  have hfp : ∀ u, IsPeriod (template n) u → u=0 := fun u => (template_period_iff n u).mp
  have hV : 2<Nat.card (TemplateSpace n) := by
    rw [Nat.card_eq_fintype_card,templateSpace_card]
    have hp : 4≤(2:ℕ)^(n+2) := by
      exact Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : 2≤n+2)
    calc
      2<2^3 := by decide
      _≤_ := Nat.pow_le_pow_right (by decide) (by omega)
  have hc := branch_stabilizer_card (template n) hfp (fun e he =>
    affine_branch_stabilizer_first_linear (template n) (template n) hf hf hfp hfp hV e
      ((mem_affineFunctionStabilizer _ _).mp he))
  simpa only [Nat.card_eq_fintype_card,templateSpace_card] using hc
/-- The actual template stabilizer recurrence gives the manuscript denominator from its finite base count. -/
theorem template_stabilizer_card_of_base
    (hbase : Nat.card (affineFunctionStabilizer baseTemplate)=24) (n : ℕ) :
    Nat.card (affineFunctionStabilizer (template n))=2^(2^(n+2)-1)*treeDenominator (n+2) := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
    rw [template_stabilizer_card_succ,ih]
    have hp : 1≤(2:ℕ)^(n+2) := Nat.one_le_pow _ _ (by decide)
    have hr : 2^(n+1+2)-1=2*(2^(n+2)-1)+1 := by
      rw [show n+1+2=n+2+1 by omega,pow_succ]
      omega
    rw [hr,show n+1+2=n+3 by omega,treeDenominator]
    have h2 : (2:ℕ)^(2*(2^(n+2)-1))=(2^(2^(n+2)-1))^2 := by rw [mul_comm,pow_mul]
    rw [pow_succ (2:ℕ) (2*(2^(n+2)-1)),h2]
    ring
/-- The actual minimal-template stabilizer has the exact manuscript denominator. -/
theorem template_stabilizer_card (n : ℕ) :
    Nat.card (affineFunctionStabilizer (template n))=2^(2^(n+2)-1)*treeDenominator (n+2) := by
  exact template_stabilizer_card_of_base baseTemplate_stabilizer_card n
/-- The exact actual pullback family count follows by cancelling the positive minimal-space translation factor. -/
theorem affinePullbackFamily_card_of_population {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (n : ℕ) (δ P : ℕ) (hδ : 0<δ)
    (hstab : Nat.card (affineFunctionStabilizer (template n))=Nat.card (TemplateSpace n)*δ)
    (hpop : Nat.card {L : V →ₗ[ZMod 2] TemplateSpace n // Function.Surjective L}=P) :
    Nat.card (affinePullbackFamily V (template n))=P/δ := by
  have hc := affinePullbackFamily_card_mul_stabilizer (V := V) (template n) (template_period_iff n)
  rw [hstab,surjectiveAffineMaps_card,hpop] at hc
  have hp : 0<Nat.card (TemplateSpace n) := Nat.card_pos
  have he : Nat.card (affinePullbackFamily V (template n))*δ=P := by
    apply Nat.eq_of_mul_eq_mul_left hp
    calc
      Nat.card (TemplateSpace n)*(Nat.card (affinePullbackFamily V (template n))*δ)=
          Nat.card (affinePullbackFamily V (template n))*(Nat.card (TemplateSpace n)*δ) := by ring
      _=_ := hc
  rw [←he,Nat.mul_div_cancel _ hδ]
/-- The literal prescribed-domain tree family has exactly the manuscript product count. -/
theorem treeSupportFamily_card_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (n : ℕ) (hdim : 2^(n+2)-1 ≤ Module.finrank (ZMod 2) V) :
    (treeSupportFamily V n).card=treeSupportCount (n+2) (Module.finrank (ZMod 2) V) := by
  rw [treeSupportFamily_card]
  apply affinePullbackFamily_card_of_population n (treeDenominator (n+2))
    (∏ i ∈ Finset.range (2^(n+2)-1), (2^Module.finrank (ZMod 2) V-2^i))
    (treeDenominator_pos _)
  · simpa only [Nat.card_eq_fintype_card,templateSpace_card] using template_stabilizer_card n
  · have h := surjectiveLinearMaps_card (V := V) (W := TemplateSpace n)
      (by simpa only [templateSpace_finrank] using hdim)
    rw [templateSpace_finrank] at h
    rw [← Fin.prod_univ_eq_prod_range]
    exact h

end BinaryFieldCounterexamples.Trees
