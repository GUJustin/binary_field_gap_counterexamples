/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperbolicIncidenceRecurrence
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RankCharacterKernel
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
/-- The rank-zero starting sequence and a literal hyperbolic plane satisfy the same scalar recurrence. -/
theorem polarGaussianCount_hyperbolic_zero (q e : ℕ) :
    polarGaussianCount q 1 0 (e+1)=
      (q:ℚ)^(e+1)*(if e+1=0 then 1 else 0)+
        ((q:ℚ)^(0-e)+1)*(if e=0 then 1 else 0) := by
  cases e with
  | zero => simp [polarGaussianCount,polarPlusProduct,gaussianPascal_self]
  | succ e => simp [polarGaussianCount,gaussianPascal_eq_zero]
variable {k V W : Type*} [Field k] [Fintype k]
  [AddCommGroup V] [Module k V] [Fintype V]
  [AddCommGroup W] [Module k W] [Fintype W]
/-- The zero-dimensional actual singular-count sequence is the delta at zero. -/
theorem singular_count_of_finrank_zero (Q : QuadraticForm k V) (hd : Module.finrank k V=0) (e : ℕ) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=if e=0 then 1 else 0 := by
  by_cases he : e=0
  · subst e
    rw [totallySingularSubspaces_zero_card]
    simp
  · rw [totallySingularSubspaces_card_zero_of_finrank Q e (by omega)]
    simp [he]
/-- The odd actual closed count is its common polar Gaussian model. -/
theorem singular_model_odd (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (s : ℕ) (hd : Module.finrank k V=2*s+1)
    (hz : Nat.card {x : V // Q x=0}=(Fintype.card k)^(2*s)) (e : ℕ) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=polarGaussianCount (Fintype.card k) s s e := by
  simpa only [polarGaussianCount,polarPlusProduct,gaussianBinomial_eq_gaussianPascal _ _ _ Fintype.one_lt_card]
    using totallySingularSubspaces_closed_odd_all Q hQ s e hd hz
/-- The positive even actual closed count is its common polar Gaussian model. -/
theorem singular_model_positive (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (s : ℕ) (hd : Module.finrank k V=2*(s+1))
    (hz : Nat.card {x : V // Q x=0}=evenQuadraticZeroCount (Fintype.card k) (s+1) true) (e : ℕ) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=polarGaussianCount (Fintype.card k) (s+1) s e := by
  have heq (i : ℕ) : s+1-i-1=s-i := by omega
  simpa only [polarGaussianCount,polarPlusProduct,gaussianBinomial_eq_gaussianPascal _ _ _ Fintype.one_lt_card,heq]
    using totallySingularSubspaces_closed_positive_all Q hQ (s+1) e hd hz
/-- The negative even actual closed count is its common polar Gaussian model. -/
theorem singular_model_negative (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (s : ℕ) (hd : Module.finrank k V=2*(s+1))
    (hz : Nat.card {x : V // Q x=0}=evenQuadraticZeroCount (Fintype.card k) (s+1) false) (e : ℕ) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=polarGaussianCount (Fintype.card k) s (s+1) e := by
  simpa only [polarGaussianCount,polarPlusProduct,gaussianBinomial_eq_gaussianPascal _ _ _ Fintype.one_lt_card,
    Nat.add_sub_cancel]
    using totallySingularSubspaces_closed_negative_all Q hQ (s+1) e (by omega) hd hz
/-- Two actual radical-free forms with hyperbolically related dimension and zero count satisfy the exact singular-incidence recurrence. -/
theorem radicalFree_singular_hyperbolic (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (R : QuadraticForm k W) (hQ : Q.radical=⊥) (hR : R.radical=⊥)
    (hd : Module.finrank k W=Module.finrank k V+2)
    (hz : Nat.card {x : W // R x=0}=(Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V)+
      Fintype.card k*Nat.card {x : V // Q x=0}) (e : ℕ) :
    (Nat.card (TotallySingularSubspaces R (e+1)):ℚ)=
      (Fintype.card k:ℚ)^(e+1)*(Nat.card (TotallySingularSubspaces Q (e+1)):ℚ)+
        ((Fintype.card k:ℚ)^(Module.finrank k V-e)+1)*(Nat.card (TotallySingularSubspaces Q e):ℚ) := by
  classical
  have hp := zeroCountPattern_of_radical_bot p Q hQ
  rw [← Nat.card_eq_fintype_card (α := {x : V // Q x = 0})] at hp
  have hq : 1≤Fintype.card k := Fintype.card_pos
  rcases hp with ⟨hd0,hz0⟩ | ⟨s,hds,hzs⟩ | ⟨s,hds,hzs⟩
  · have hdR : Module.finrank k W=2*(0+1) := by omega
    have hzR : Nat.card {x : W // R x=0}=evenQuadraticZeroCount (Fintype.card k) (0+1) true := by
      rw [hd0,hz0] at hz
      simp only [evenQuadraticZeroCount,↓reduceIte,zero_add,Nat.reduceSub,pow_one,pow_zero,mul_one] at *
      omega
    rw [singular_model_positive R hR 0 hdR hzR,singular_count_of_finrank_zero Q hd0,
      singular_count_of_finrank_zero Q hd0,hd0]
    exact polarGaussianCount_hyperbolic_zero _ e
  · have hdR : Module.finrank k W=2*(s+1)+1 := by omega
    have hzR : Nat.card {x : W // R x=0}=(Fintype.card k)^(2*(s+1)) := by
      rw [hds,hzs] at hz
      have hqm : Fintype.card k-1+1=Fintype.card k := by omega
      rw [show 2*(s+1)=2*s+2 by omega,pow_add,pow_two]
      rw [pow_succ] at hz
      linarith [congrArg (fun u => u*((Fintype.card k)*(Fintype.card k)^(2*s))) hqm]
    rw [singular_model_odd R hR (s+1) hdR hzR,singular_model_odd Q hQ s hds hzs,
      singular_model_odd Q hQ s hds hzs,hds]
    simpa only [show s+s=2*s by omega] using polarGaussianCount_hyperbolic_all (Fintype.card k) s s e (Fintype.one_lt_card (α := k)) (by omega)
  · have hdQ : Module.finrank k V=2*(s+1) := by omega
    have hdR : Module.finrank k W=2*((s+1)+1) := by omega
    have hex1 : 2*(s+1)-1=2*s+1 := by omega
    have hex2 : s+1-1=s := by omega
    rcases hzs with hzplus | hzminus
    · have hzQ : Nat.card {x : V // Q x=0}=evenQuadraticZeroCount (Fintype.card k) (s+1) true := by
        simpa only [evenQuadraticZeroCount,↓reduceIte,hex1,hex2] using hzplus
      have hzR : Nat.card {x : W // R x=0}=evenQuadraticZeroCount (Fintype.card k) ((s+1)+1) true := by
        rw [evenQuadraticZeroCount_succ _ _ hq (by omega),←hzQ,←hdQ]
        exact hz
      rw [singular_model_positive R hR (s+1) hdR hzR,singular_model_positive Q hQ s hdQ hzQ,
        singular_model_positive Q hQ s hdQ hzQ,hdQ]
      have hh := polarGaussianCount_hyperbolic_all (Fintype.card k) (s+1) s e Fintype.one_lt_card (by omega)
      simpa only [show s+1+s+1=2*(s+1) by omega] using hh
    · have hzQ : Nat.card {x : V // Q x=0}=evenQuadraticZeroCount (Fintype.card k) (s+1) false := by
        simpa only [evenQuadraticZeroCount,Bool.false_eq_true,↓reduceIte,hex1,hex2] using hzminus
      have hzR : Nat.card {x : W // R x=0}=evenQuadraticZeroCount (Fintype.card k) ((s+1)+1) false := by
        rw [evenQuadraticZeroCount_succ _ _ hq (by omega),←hzQ,←hdQ]
        exact hz
      rw [singular_model_negative R hR (s+1) hdR hzR,singular_model_negative Q hQ s hdQ hzQ,
        singular_model_negative Q hQ s hdQ hzQ,hdQ]
      have hh := polarGaussianCount_hyperbolic_all (Fintype.card k) s (s+1) e Fintype.one_lt_card (by omega)
      simpa only [show s+(s+1)+1=2*(s+1) by omega] using hh
/-- Actual degenerate forms inherit the hyperbolic singular-incidence recurrence through their radical quotients. -/
theorem singular_hyperbolic (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (R : QuadraticForm k W)
    (hd : Module.finrank k W=Module.finrank k V+2)
    (hh : Module.finrank k R.radical=Module.finrank k Q.radical)
    (hz : Nat.card {x : W // R x=0}=(Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V)+
      Fintype.card k*Nat.card {x : V // Q x=0}) (e : ℕ) :
    (Nat.card (TotallySingularSubspaces R (e+1)):ℚ)=
      (Fintype.card k:ℚ)^(e+1)*(Nat.card (TotallySingularSubspaces Q (e+1)):ℚ)+
        ((Fintype.card k:ℚ)^(Module.finrank k V-e)+1)*(Nat.card (TotallySingularSubspaces Q e):ℚ) := by
  classical
  let : Fintype (V ⧸ Q.radical) := Fintype.ofFinite _
  let : Fintype (W ⧸ R.radical) := Fintype.ofFinite _
  have hdimQ := Q.radical.finrank_quotient_add_finrank
  have hdimR := R.radical.finrank_quotient_add_finrank
  have hdbar : Module.finrank k (W ⧸ R.radical)=Module.finrank k (V ⧸ Q.radical)+2 := by omega
  have hzbar : Nat.card {x : W ⧸ R.radical // R.lift R.radical le_rfl x=0}=
      (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k (V ⧸ Q.radical))+
        Fintype.card k*Nat.card {x : V ⧸ Q.radical // Q.lift Q.radical le_rfl x=0} := by
    rw [quadratic_zero_natCard_radical R,quadratic_zero_natCard_radical Q,hh,←hdimQ,pow_add] at hz
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (Fintype.card_pos (α := k)) _)
    calc
      _ = _ := hz
      _ = _ := by ring
  have hstep := radicalFree_singular_hyperbolic p (Q.lift Q.radical le_rfl)
    (R.lift R.radical le_rfl) (radical_lift_radical_eq_bot Q) (radical_lift_radical_eq_bot R)
    hdbar hzbar
  have hr := rationalRadicalConvolution_hyperbolic (Fintype.card k)
    (Module.finrank k (V ⧸ Q.radical)) (Module.finrank k Q.radical)
    (fun i => (Nat.card (TotallySingularSubspaces (Q.lift Q.radical le_rfl) i):ℚ))
    (fun i => (Nat.card (TotallySingularSubspaces (R.lift R.radical le_rfl) i):ℚ))
    (fun i hi => by rw [totallySingularSubspaces_card_zero_of_finrank _ i hi]; simp)
    (by rw [totallySingularSubspaces_zero_card,totallySingularSubspaces_zero_card]) hstep e
  rw [actual_singular_count_eq_rationalRadicalConvolution R,
    actual_singular_count_eq_rationalRadicalConvolution Q,
    actual_singular_count_eq_rationalRadicalConvolution Q,hh]
  simpa only [hdimQ] using hr
/-- Removing an actual hyperbolic plane gives the exact singular-subspace recurrence, in all characteristics and with arbitrary radical. -/
theorem hyperbolicComplement_singular_recurrence (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (x y : V) (hx : Q x=0) (hy : Q y=0)
    (hxy : Q.polarBilin x y=1) (e : ℕ) :
    (Nat.card (TotallySingularSubspaces Q (e+1)):ℚ)=
      (Fintype.card k:ℚ)^(e+1)*
        (Nat.card (TotallySingularSubspaces (Q.comp (hyperbolicComplement Q x y).subtype) (e+1)):ℚ)+
      ((Fintype.card k:ℚ)^(Module.finrank k (hyperbolicComplement Q x y)-e)+1)*
        (Nat.card (TotallySingularSubspaces (Q.comp (hyperbolicComplement Q x y).subtype) e):ℚ) := by
  classical
  apply singular_hyperbolic p (Q.comp (hyperbolicComplement Q x y).subtype) Q
    (hyperbolicComplement_finrank Q x y hx hy hxy)
    (hyperbolicComplementRadicalEquiv Q x y hx hy hxy).finrank_eq.symm
  have hh := hyperbolicSplit_zero_count Q x y hx hy hxy
  have hc := Module.natCard_eq_pow_finrank (K:=k) (V:=hyperbolicComplement Q x y)
  simp only [Nat.card_eq_fintype_card] at hc ⊢
  rw [←hc]
  exact hh
/-- Every actual incidence sequence starts at one. -/
theorem quadraticIncidenceSequence_zero (Q : QuadraticForm k V) : quadraticIncidenceSequence Q 0=1 := by
  simp [quadraticIncidenceSequence,totallySingularSubspaces_zero_card]
/-- The weighted actual incidence sequence has the exact two-term hyperbolic step used by Möbius inversion. -/
theorem quadraticIncidenceSequence_hyperbolic (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (R : QuadraticForm k W)
    (hd : Module.finrank k W=Module.finrank k V+2)
    (hh : Module.finrank k R.radical=Module.finrank k Q.radical)
    (hz : Nat.card {x : W // R x=0}=(Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V)+
      Fintype.card k*Nat.card {x : V // Q x=0}) (e : ℕ) :
    quadraticIncidenceSequence R (e+1)=
      (Fintype.card k:ℚ)^(e+1)*quadraticIncidenceSequence Q (e+1)+
        ((Fintype.card k:ℚ)^(Module.finrank k V+1)+(Fintype.card k:ℚ)^(e+1))*quadraticIncidenceSequence Q e := by
  unfold quadraticIncidenceSequence
  rw [singular_hyperbolic p Q R hd hh hz]
  by_cases he : e≤Module.finrank k V
  · have ht : (e+1)*(e+1+1)/2=e*(e+1)/2+(e+1) := by
      rw [show (e+1)*(e+1+1)=e*(e+1)+(e+1)*2 by ring,Nat.add_mul_div_right]; norm_num
    have hp : (Fintype.card k:ℚ)^(e+1)*(Fintype.card k:ℚ)^(Module.finrank k V-e)=
        (Fintype.card k:ℚ)^(Module.finrank k V+1) := by rw [←pow_add]; congr 1; omega
    rw [ht,pow_add]
    rw [←hp]
    ring
  · rw [totallySingularSubspaces_card_zero_of_finrank Q e (by omega),
      totallySingularSubspaces_card_zero_of_finrank Q (e+1) (by omega)]
    simp
end BinaryFieldCounterexamples.QuadraticGeometry
