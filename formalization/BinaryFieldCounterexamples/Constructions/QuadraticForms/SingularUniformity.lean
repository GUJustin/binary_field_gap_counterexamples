/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ThroughLineCounts
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalLineQuotient
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.FlagRecurrence
/-!
# Uniformity of actual totally singular subspace counts

Induction on the subspace dimension compares the actual radical and nonradical
line fibers. Their dimensions, quadratic radicals, and zero counts agree.
The exact flag identity then shows that these three invariants determine every
singular-subspace count, without invoking an orbit classification.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
universe u v
variable {k : Type u} [Field k] [Fintype k]
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.decEq Classical.propDecidable
attribute [local instance] singularLinesFintype totallySingularSubspacesFintype
/-- The zero-dimensional totally singular subspace is uniquely the bottom subspace. -/
theorem totallySingularSubspaces_zero_card {V : Type v} [AddCommGroup V] [Module k V]
    [Fintype V] (Q : QuadraticForm k V) : Nat.card (TotallySingularSubspaces Q 0)=1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨⊥,by simp,by intro z hz; simpa using (show Q z=0 by rw [show z=0 from hz,Q.map_zero])⟩,?_⟩
  intro S
  apply Subtype.ext
  exact (Submodule.finrank_eq_zero.mp S.property.1)
/-- Equal lower-dimensional singular counts compare actual fibers in each line branch. -/
theorem through_line_card_eq_of_lower_uniformity (e : ℕ)
    (ih : ∀ {V W : Type v} [AddCommGroup V] [Module k V] [Fintype V]
      [AddCommGroup W] [Module k W] [Fintype W]
      (Q : QuadraticForm k V) (R : QuadraticForm k W),
      Module.finrank k V=Module.finrank k W → Module.finrank k Q.radical=Module.finrank k R.radical →
      Nat.card {x : V // Q x=0}=Nat.card {y : W // R y=0} →
      Nat.card (TotallySingularSubspaces Q e)=Nat.card (TotallySingularSubspaces R e))
    {V W : Type v} [AddCommGroup V] [Module k V] [Fintype V]
    [AddCommGroup W] [Module k W] [Fintype W]
    (Q : QuadraticForm k V) (R : QuadraticForm k W)
    (hd : Module.finrank k V=Module.finrank k W)
    (hr : Module.finrank k Q.radical=Module.finrank k R.radical)
    (hz : Nat.card {x : V // Q x=0}=Nat.card {y : W // R y=0})
    (L : SingularLines Q) (M : SingularLines R)
    (hbranch : L.val≤Q.radical ↔ M.val≤R.radical) :
    Nat.card {S : TotallySingularSubspaces Q (e+1) // L.val≤S.val}=
      Nat.card {S : TotallySingularSubspaces R (e+1) // M.val≤S.val} := by
  classical
  by_cases hL : L.val≤Q.radical
  · have hM := hbranch.mp hL
    rw [through_radical_line_card Q L hL,through_radical_line_card R M hM]
    let : Fintype (V ⧸ L.val) := Fintype.ofFinite _
    let : Fintype (W ⧸ M.val) := Fintype.ofFinite _
    apply ih
    · have ha := L.val.finrank_quotient_add_finrank
      have hb := M.val.finrank_quotient_add_finrank
      rw [L.property.1] at ha
      rw [M.property.1] at hb
      omega
    · have ha := radical_lift_finrank_add Q L.val hL
      have hb := radical_lift_finrank_add R M.val hM
      rw [L.property.1] at ha
      rw [M.property.1] at hb
      omega
    · have ha := radical_line_zero_natCard Q L.val hL L.property.1
      have hb := radical_line_zero_natCard R M.val hM M.property.1
      rw [ha,hb] at hz
      exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos hz
  · have hM : ¬M.val≤R.radical := fun h => hL (hbranch.mpr h)
    obtain ⟨x,y,hxne,hx,hy,hxy,hspan⟩ := nonradical_line_hyperbolic Q L hL
    obtain ⟨z,w,hzne,hz0,hw,hzw,hspan'⟩ := nonradical_line_hyperbolic R M hM
    rw [through_singular_line_card Q L x hx hxne hspan,
      through_singular_line_card R M z hz0 hzne hspan']
    let : Fintype ((Q.polarBilin x).ker ⧸ singularPerpLine Q x hx) := Fintype.ofFinite _
    let : Fintype ((R.polarBilin z).ker ⧸ singularPerpLine R z hz0) := Fintype.ofFinite _
    apply ih
    · rw [singularLineQuotient_finrank Q x y hx hy hxy,
        singularLineQuotient_finrank R z w hz0 hw hzw,hd]
    · rw [singularLineQuotient_radical_finrank Q x y hx hy hxy,
        singularLineQuotient_radical_finrank R z w hz0 hw hzw,hr]
    · have ha := singularLineQuotient_zero_count Q x y hx hy hxy
      have hb := singularLineQuotient_zero_count R z w hz0 hw hzw
      rw [ha,hb,hd] at hz
      exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos (Nat.add_left_cancel hz)
/-- The number of actual totally singular subspaces depends only on ambient dimension, quadratic radical dimension, and the actual zero count. -/
theorem totallySingularSubspaces_card_eq (e : ℕ) :
    ∀ {V W : Type v} [AddCommGroup V] [Module k V] [Fintype V]
      [AddCommGroup W] [Module k W] [Fintype W]
      (Q : QuadraticForm k V) (R : QuadraticForm k W),
      Module.finrank k V=Module.finrank k W → Module.finrank k Q.radical=Module.finrank k R.radical →
      Nat.card {x : V // Q x=0}=Nat.card {y : W // R y=0} →
      Nat.card (TotallySingularSubspaces Q e)=Nat.card (TotallySingularSubspaces R e) := by
  induction e with
  | zero =>
    intro V W _ _ _ _ _ _ Q R hd hr hz
    rw [totallySingularSubspaces_zero_card,totallySingularSubspaces_zero_card]
  | succ e ih =>
    intro V W _ _ _ _ _ _ Q R hd hr hz
    have hf := through_line_card_eq_of_lower_uniformity e ih Q R hd hr hz
    have hcard : Fintype.card (SingularLines Q)=Fintype.card (SingularLines R) := by
      rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,singularLines_card,singularLines_card,hz]
    have hrCard : Fintype.card {L : SingularLines Q // L.val≤Q.radical}=
        Fintype.card {M : SingularLines R // M.val≤R.radical} := by
      rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,
        singular_radical_lines_card,singular_radical_lines_card,hr]
    have hnCard : Fintype.card {L : SingularLines Q // ¬L.val≤Q.radical}=
        Fintype.card {M : SingularLines R // ¬M.val≤R.radical} := by
      rw [Fintype.card_subtype_compl,Fintype.card_subtype_compl,hcard,hrCard]
    let er := Fintype.equivOfCardEq hrCard
    let en := Fintype.equivOfCardEq hnCard
    have hsum : (∑ L : SingularLines Q,
        Nat.card {S : TotallySingularSubspaces Q (e+1) // L.val≤S.val}) =
        ∑ M : SingularLines R,
          Nat.card {S : TotallySingularSubspaces R (e+1) // M.val≤S.val} := by
      rw [←Fintype.sum_subtype_add_sum_subtype (fun L : SingularLines Q => L.val≤Q.radical),
        ←Fintype.sum_subtype_add_sum_subtype (fun M : SingularLines R => M.val≤R.radical)]
      congr 1
      · apply Fintype.sum_equiv er
        intro L
        exact hf L.val (er L).val (by simp only [L.property,(er L).property])
      · apply Fintype.sum_equiv en
        intro L
        exact hf L.val (en L).val (by simp only [L.property,(en L).property])
    rw [singular_flag_count,singular_flag_count] at hsum
    have hq : 1 < Fintype.card k := Fintype.one_lt_card
    have hp : Fintype.card k ≤ (Fintype.card k)^(e+1) := by
      simpa using Nat.pow_le_pow_right (by omega : 1≤Fintype.card k) (by omega : 1≤e+1)
    have hg : 0 < ((Fintype.card k)^(e+1)-1)/(Fintype.card k-1) :=
      Nat.div_pos (by omega) (by omega)
    exact Nat.eq_of_mul_eq_mul_right hg hsum
end BinaryFieldCounterexamples.QuadraticGeometry
