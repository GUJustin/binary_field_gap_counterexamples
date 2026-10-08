/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.DegenerateZeroCount
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TracePopulation
/-!
# Elliptic type as actual orthogonal splitting

The elliptic type in Proposition 5.21 is defined through actual hyperbolic
splittings, ending in an anisotropic plane. On the quadratic-radical quotient,
this is precisely the paper's orthogonal sum of hyperbolic planes and one
anisotropic plane. Zero counts are consequences of this definition, not its
meaning. The converse zero-count criterion is proved by actual splitting.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open Module
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
variable {k : Type*} [Field k]

/-- Proposition 5.21's orthogonal decomposition: `s` hyperbolic planes and one
anisotropic plane, using the actual orthogonal-complement splitting. -/
def HasEllipticSplitting (s : ℕ) {V : Type*} [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) : Prop :=
  match s with
  | 0 => Module.finrank k V = 2 ∧ Q.Anisotropic
  | s + 1 => ∃ x y : V, Q x = 0 ∧ Q y = 0 ∧ Q.polarBilin x y = 1 ∧
      HasEllipticSplitting s (Q.comp (hyperbolicComplement Q x y).subtype)

/-- Proposition 5.21: elliptic type means that the actual quadratic-radical
quotient is an orthogonal sum of hyperbolic planes and one anisotropic plane. -/
def IsElliptic {V : Type*} [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) : Prop :=
  ∃ s : ℕ, HasEllipticSplitting s (Q.lift Q.radical le_rfl)

theorem minus_recurrence (q s : ℕ) (hq : 1 ≤ q) :
    (q-1)*q^(2*s+2)+q*(q^(2*s+1)-(q-1)*q^s) =
      q^(2*(s+1)+1)-(q-1)*q^(s+1) := by
  have hqm : q-1+1=q := by omega
  have hp2 : q^(2*s+2)=q*q^(2*s+1) := by rw [show 2*s+2=(2*s+1)+1 by omega,pow_succ']
  have hp3 : q^(2*(s+1)+1)=q*q*q^(2*s+1) := by
    rw [show 2*(s+1)+1=(2*s+1)+2 by omega,pow_add,pow_two]
    ring
  rw [hp2,hp3,pow_succ' q s]
  have hbase : (q-1)*(q*q^(2*s+1))+q*q^(2*s+1)=q*q*q^(2*s+1) := by
    linarith [congrArg (fun u => u*(q*q^(2*s+1))) hqm]
  have hsub := Nat.sub_add_cancel (even_correction_le q s hq)
  have hnew : (q-1)*(q*q^s) ≤ q*q*q^(2*s+1) := by
    have hh := even_correction_le q (s+1) hq
    rw [hp3,pow_succ' q s] at hh
    exact hh
  have hsubnew := Nat.sub_add_cancel hnew
  linarith [congrArg (fun u => q*u) hsub]

/-- Proposition 5.21(2): an actual elliptic orthogonal splitting has rank
`2(s+1)` and the exact smaller zero count. -/
theorem HasEllipticSplitting.dimension_zero_count [Fintype k]
    {V : Type*} [AddCommGroup V] [Module k V] [Fintype V]
    {s : ℕ} {Q : QuadraticForm k V} (h : HasEllipticSplitting s Q) :
    Module.finrank k V = 2*s+2 ∧
      Fintype.card {x : V // Q x=0} =
        (Fintype.card k)^(2*s+1)-(Fintype.card k-1)*(Fintype.card k)^s := by
  induction s generalizing V with
  | zero =>
      obtain ⟨hd,ha⟩ := h
      refine ⟨by simpa using hd,?_⟩
      rw [anisotropic_zero_card Q ha]
      simp only [Nat.mul_zero,Nat.zero_add,pow_one,pow_zero,Nat.mul_one]
      have := Fintype.card_pos (α:=k)
      omega
  | succ s ih =>
      obtain ⟨x,y,hx,hy,hxy,hh⟩ := h
      obtain ⟨hd,hz⟩ := ih hh
      simp only [QuadraticMap.comp_apply,Submodule.subtype_apply] at hz
      refine ⟨?_,?_⟩
      · rw [hyperbolicComplement_finrank Q x y hx hy hxy,hd]
        omega
      · have hcH : Fintype.card (hyperbolicComplement Q x y) =
            (Fintype.card k)^(Module.finrank k (hyperbolicComplement Q x y)) :=
          Module.card_eq_pow_finrank (K:=k)
        rw [hyperbolicSplit_zero_count Q x y hx hy hxy,hz,hcH,hd]
        exact minus_recurrence _ _ Fintype.card_pos

theorem plus_recurrence (q s : ℕ) (hq : 1 ≤ q) :
    (q-1)*q^(2*s+2)+q*(q^(2*s+1)+(q-1)*q^s) =
      q^(2*(s+1)+1)+(q-1)*q^(s+1) := by
  have hqm : q-1+1=q := by omega
  have hp2 : q^(2*s+2)=q*q^(2*s+1) := by rw [show 2*s+2=(2*s+1)+1 by omega,pow_succ']
  have hp3 : q^(2*(s+1)+1)=q*q*q^(2*s+1) := by
    rw [show 2*(s+1)+1=(2*s+1)+2 by omega,pow_add,pow_two]
    ring
  rw [hp2,hp3,pow_succ' q s]
  linarith [congrArg (fun u => u*(q*q^(2*s+1))) hqm]

/-- Proposition 5.21(1): the smaller even-dimensional zero count forces the
paper's actual elliptic orthogonal decomposition, over every finite field. -/
theorem hasEllipticSplitting_of_zero_count [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    {V : Type*} [AddCommGroup V] [Module k V] [Fintype V]
    (s : ℕ) (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (hd : Module.finrank k V=2*s+2)
    (hz : Fintype.card {x : V // Q x=0} =
      (Fintype.card k)^(2*s+1)-(Fintype.card k-1)*(Fintype.card k)^s) :
    HasEllipticSplitting s Q := by
  induction s generalizing V with
  | zero =>
      refine ⟨by simpa using hd,?_⟩
      have hc : Fintype.card {x : V // Q x=0}=1 := by
        simp only [Nat.mul_zero,Nat.zero_add,pow_one,pow_zero,Nat.mul_one] at hz
        have := Fintype.card_pos (α:=k)
        omega
      obtain ⟨u,hu⟩ := Fintype.card_eq_one_iff.mp hc
      intro x hx
      have hx0 : (⟨x,hx⟩ : {x : V // Q x=0})=⟨0,Q.map_zero⟩ :=
        (hu ⟨x,hx⟩).trans (hu ⟨0,Q.map_zero⟩).symm
      exact congrArg Subtype.val hx0
  | succ s ih =>
      have ha : ¬Q.Anisotropic := by
        intro ha
        have := QuadraticCoordinates.anisotropic_finrank_le_two p Q ha
        omega
      change ¬ ∀ x, Q x=0 → x=0 at ha
      push Not at ha
      obtain ⟨x,hx,hne⟩ := ha
      obtain ⟨y,hy,hxy⟩ := exists_hyperbolic_partner Q x hx
        (singular_not_mem_polar_ker_of_radical_bot Q hQ x hx hne)
      let H := hyperbolicComplement Q x y
      let QH := Q.comp H.subtype
      have hH : QH.radical=⊥ := hyperbolicComplement_radical_bot Q hQ x y hx hy hxy
      have hdH : Module.finrank k H=2*s+2 := by
        have := hyperbolicComplement_finrank Q x y hx hy hxy
        change Module.finrank k V=Module.finrank k H+2 at this
        omega
      have hcounts := zero_card_of_radical_bot_even p QH hH (s+1) (by omega)
        (by rw [hdH]; omega)
      have hdimexp : 2*(s+1)-1=2*s+1 := by omega
      simp only [hdimexp,Nat.add_sub_cancel] at hcounts
      have hrec := hyperbolicSplit_zero_count Q x y hx hy hxy
      change Fintype.card {z : V // Q z=0} =
        (Fintype.card k-1)*Fintype.card H+Fintype.card k*Fintype.card {z : H // QH z=0} at hrec
      have hcH : Fintype.card H=(Fintype.card k)^(Module.finrank k H) :=
        Module.card_eq_pow_finrank (K:=k)
      rw [hcH,hdH] at hrec
      refine ⟨x,y,hx,hy,hxy,?_⟩
      apply ih QH hH hdH
      rcases hcounts with hplus | hminus
      · rw [hplus,plus_recurrence _ _ Fintype.card_pos,hz] at hrec
        have hpos : 0 < (Fintype.card k-1)*(Fintype.card k)^(s+1) :=
          Nat.mul_pos (by have := Fintype.one_lt_card (α:=k); omega)
            (pow_pos Fintype.card_pos _)
        omega
      · exact hminus

theorem radical_minus_factor (q d r t : ℕ) (ht : 0 < t) (hd : d=2*t+r) :
    q^r*(q^(2*t-1)-(q-1)*q^(t-1)) = q^(d-1)-(q-1)*q^(d-t-1) := by
  have hpow : q^r*q^(2*t-1)=q^(d-1) := by
    rw [←pow_add]; congr 1; omega
  have hcorr : q^r*((q-1)*q^(t-1))=(q-1)*q^(d-t-1) := by
    rw [←mul_assoc,mul_comm (q^r),mul_assoc,←pow_add]
    congr 2
    omega
  rw [Nat.mul_sub_left_distrib,hpow,hcorr]

/-- Proposition 5.21(2), for every elliptic form on the paper's actual vector
space: the zero count is `b^(d-1) - (b-1)b^(d-t-1)` at rank `2t`. -/
theorem IsElliptic.zero_natCard [Fintype k]
    {V : Type*} [AddCommGroup V] [Module k V] [Fintype V]
    {Q : QuadraticForm k V} (hQ : IsElliptic Q) (t : ℕ)
    (hrank : Module.finrank k V-Module.finrank k Q.radical=2*t) :
    Nat.card {x : V // Q x=0} = (Fintype.card k)^(Module.finrank k V-1)-
      (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V-t-1) := by
  obtain ⟨s,hs⟩ := hQ
  obtain ⟨hd,hz⟩ := hs.dimension_zero_count
  have hrq := radical_quotient_finrank Q
  have hst : t=s+1 := by omega
  have ht : 0<t := by omega
  have hdim := Q.radical.finrank_quotient_add_finrank
  have hdim' : Module.finrank k V=2*t+Module.finrank k Q.radical := by omega
  rw [quadratic_zero_natCard_radical,Nat.card_eq_fintype_card,hz]
  have he1 : 2*s+1=2*t-1 := by omega
  have he2 : s=t-1 := by omega
  rw [he1,he2]
  exact radical_minus_factor _ _ _ _ ht hdim'

/-- Proposition 5.21(1): for positive even rank over a finite field, the exact
smaller zero count characterizes the actual elliptic orthogonal decomposition. -/
theorem isElliptic_iff_zero_natCard [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    {V : Type*} [AddCommGroup V] [Module k V] [Fintype V]
    (Q : QuadraticForm k V) (t : ℕ) (ht : 0<t)
    (hrank : Module.finrank k V-Module.finrank k Q.radical=2*t) :
    IsElliptic Q ↔ Nat.card {x : V // Q x=0} =
      (Fintype.card k)^(Module.finrank k V-1)-
        (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V-t-1) := by
  constructor
  · exact fun h => h.zero_natCard t hrank
  · intro hz
    have hdq : Module.finrank k (V ⧸ Q.radical)=2*t := by
      rw [radical_quotient_finrank,hrank]
    have hdim := Q.radical.finrank_quotient_add_finrank
    have hdim' : Module.finrank k V=2*t+Module.finrank k Q.radical := by omega
    have hquot : Fintype.card {x : V ⧸ Q.radical // Q.lift Q.radical le_rfl x=0} =
        (Fintype.card k)^(2*t-1)-(Fintype.card k-1)*(Fintype.card k)^(t-1) := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos (Fintype.card_pos (α:=k))
        (Module.finrank k Q.radical))
      have hprod := quadratic_zero_natCard_radical Q
      have hqc : Nat.card {x : V ⧸ Q.radical // Q.lift Q.radical le_rfl x=0} =
          Fintype.card {x : V ⧸ Q.radical // Q.lift Q.radical le_rfl x=0} :=
        Nat.card_eq_fintype_card
      rw [hqc] at hprod
      rw [←hprod,hz,radical_minus_factor _ _ _ _ ht hdim']
    refine ⟨t-1,hasEllipticSplitting_of_zero_count p (t-1)
      (Q.lift Q.radical le_rfl) (radical_lift_radical_eq_bot Q) ?_ ?_⟩
    · rw [hdq]; omega
    · have he : 2*(t-1)+1=2*t-1 := by omega
      simpa only [he] using hquot

/-- Proposition 5.21(5): every invertible linear substitution preserves the
paper's elliptic type, including forms with a nonzero quadratic radical. -/
theorem isElliptic_comp_linearEquiv_iff [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    {V W : Type*} [AddCommGroup V] [Module k V] [Fintype V]
    [AddCommGroup W] [Module k W] [Fintype W]
    (Q : QuadraticForm k V) (e : W ≃ₗ[k] V) :
    IsElliptic (Q.comp e.toLinearMap) ↔ IsElliptic Q := by
  let R := Q.comp e.toLinearMap
  have heq : Q.Equivalent R := ⟨Q.isometryEquivOfCompLinearEquiv e⟩
  have hd : Module.finrank k W=Module.finrank k V := e.finrank_eq
  have hr : Module.finrank k R.radical=Module.finrank k Q.radical :=
    heq.rank_radical_eq.symm
  have hz : Nat.card {x : W // R x=0}=Nat.card {x : V // Q x=0} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv e.toEquiv (fun x => Iff.rfl)
  constructor
  · intro hR
    change IsElliptic R at hR
    obtain ⟨s,hs⟩ := hR
    have hds := hs.dimension_zero_count
    have hquot := radical_quotient_finrank R
    have hRankR : Module.finrank k W-Module.finrank k R.radical=2*(s+1) := by omega
    have hRankQ : Module.finrank k V-Module.finrank k Q.radical=2*(s+1) := by
      simpa only [hd,hr] using hRankR
    apply (isElliptic_iff_zero_natCard p Q (s+1) (by omega) hRankQ).mpr
    rw [←hz]
    have hzero := (show IsElliptic R from ⟨s,hs⟩).zero_natCard (s+1) hRankR
    simpa only [hd] using hzero
  · intro hQ
    obtain ⟨s,hs⟩ := hQ
    have hds := hs.dimension_zero_count
    have hquot := radical_quotient_finrank Q
    have hRankQ : Module.finrank k V-Module.finrank k Q.radical=2*(s+1) := by omega
    have hRankR : Module.finrank k W-Module.finrank k R.radical=2*(s+1) := by
      simpa only [hd,hr] using hRankQ
    apply (isElliptic_iff_zero_natCard p R (s+1) (by omega) hRankR).mpr
    rw [hz]
    have hzero := (show IsElliptic Q from ⟨s,hs⟩).zero_natCard (s+1) hRankQ
    simpa only [hd] using hzero

end BinaryFieldCounterexamples.QuadraticGeometry

namespace BinaryFieldCounterexamples.QuadraticFormTrace
set_option warn.classDefReducibility false
open Module QuadraticGeometry
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Proposition 5.21(1): every actual trace form of minimum positive rank has
elliptic type in the paper's orthogonal-decomposition sense. -/
theorem traceFamilyQuadraticForm_isElliptic
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    IsElliptic (traceFamilyQuadraticForm n t ht htn a c hcard hc) := by
  let : CharP k p := (algebraMap k B).charP (algebraMap k B).injective p
  apply (isElliptic_iff_zero_natCard p _ t (by omega) hrank).mpr
  have hz := traceFamilyQuadraticForm_zero_natCard_of_exact_rank p r hr hq n t ht htn
    a c hcard hc hne hrank
  rwa [finrank_eq_of_card (k:=k) (2*n) hcard]

/-- Proposition 5.21(1): membership in the minimum-rank trace layer entails the
paper's elliptic type, with no additional hypothesis on the form's parameters. -/
theorem traceRankFamily_mem_isElliptic
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (Q : QuadraticForm k B) (hQ : Q∈traceRankFamily n t ht htn hcard (2*t)) :
    IsElliptic Q := by
  obtain ⟨hQ,hrank⟩ := Finset.mem_filter.mp hQ
  have hQnonzero : Q≠0 := by
    intro hz
    have hrad : (0 : QuadraticForm k B).radical=⊤ := by
      ext x
      simp [QuadraticMap.mem_radical_iff']
    rw [hz,hrad,finrank_top] at hrank
    omega
  obtain ⟨u,hu⟩ := (mem_traceQuadraticCode_iff n t ht htn hcard Q).mpr hQ
  have hne : u.1≠0 ∨ u.2.val≠0 := by
    by_contra h
    push Not at h
    have hu0 : u=0 := Prod.ext h.1 (Subtype.ext h.2)
    rw [hu0,map_zero] at hu
    exact hQnonzero hu.symm
  rw [←hu] at hrank ⊢
  exact traceFamilyQuadraticForm_isElliptic p r hr hq n t ht htn u.1 u.2.val
    hcard ((mem_halfCoefficientSpace n u.2.val).mp u.2.property) hne hrank

/-- Proposition 5.21(1) in full: at least `(b^t-1)[n,t]_(b²)` actual trace
forms have rank `2t` and the paper's elliptic orthogonal type. -/
theorem traceRankFamily_elliptic_card_lower
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) :
    ((Fintype.card k)^t-1)*gaussianPascal ((Fintype.card k)^2) n t ≤
      ((traceRankFamily n t ht htn hcard (2*t)).filter IsElliptic).card := by
  have he : (traceRankFamily n t ht htn hcard (2*t)).filter IsElliptic =
      traceRankFamily n t ht htn hcard (2*t) := by
    apply Finset.filter_eq_self.mpr
    intro Q hQ
    exact traceRankFamily_mem_isElliptic p r hr hq n t ht htn hcard Q hQ
  rw [he]
  exact traceRankFamily_card_lower p r hq n t ht htn hcard

/-- Proposition 5.21(5): every nonzero input dilation preserves elliptic type
for actual quadratic forms over the trace family's ambient field. -/
theorem isElliptic_comp_mul_iff (p : ℕ) [Fact p.Prime] [CharP B p]
    (Q : QuadraticForm k B) (z : B) (hz : z≠0) :
    IsElliptic (Q.comp (LinearMap.mulLeft k z)) ↔ IsElliptic Q := by
  let : CharP k p := (algebraMap k B).charP (algebraMap k B).injective p
  exact isElliptic_comp_linearEquiv_iff p Q
    (Units.mulLeftLinearEquiv k B (Units.mk0 z hz))

/-- Proposition 5.21(5) in full: nonzero dilation preserves actual trace-family
membership, quadratic rank and the paper's elliptic type simultaneously. -/
theorem traceQuadraticFamily_dilation_full
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (Q : QuadraticForm k B) (z : B) (hz : z≠0) :
    (Q.comp (LinearMap.mulLeft k z)∈traceQuadraticFamily n t ht htn hcard ↔
      Q∈traceQuadraticFamily n t ht htn hcard) ∧
    (Module.finrank k B-Module.finrank k (Q.comp (LinearMap.mulLeft k z)).radical =
      Module.finrank k B-Module.finrank k Q.radical) ∧
    (IsElliptic (Q.comp (LinearMap.mulLeft k z)) ↔ IsElliptic Q) := by
  refine ⟨?_,?_,isElliptic_comp_mul_iff p Q z hz⟩
  · rw [←mem_traceQuadraticCode_iff,←mem_traceQuadraticCode_iff]
    exact traceQuadraticCode_comp_mul_mem_iff n t ht htn hcard z hz Q
  · rw [radical_finrank_comp_mul Q z hz]
end BinaryFieldCounterexamples.QuadraticFormTrace
