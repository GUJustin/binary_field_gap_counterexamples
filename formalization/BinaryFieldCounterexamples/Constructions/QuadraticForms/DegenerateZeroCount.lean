/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ZeroClassification
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalQuotient
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ExactRank
/-!
# Degenerate quadratic zero counts and minimum-rank trace type

Passing to the actual quadratic radical reduces zero counting to the radical-free
classification. The independently proved trace-family upper bound then selects
the elliptic alternative at minimum rank. No assertion about the number of
minimum-rank parameters is used here.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open Module
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]

/-- Odd actual quadratic rank gives the exact usual finite-field zero count, including degenerate forms. -/
theorem zero_card_of_odd_rank (p : ℕ) [Fact p.Prime] [CharP k p] (Q : QuadraticForm k V)
    (hodd : Odd (Module.finrank k V-Module.finrank k Q.radical)) :
    Nat.card {x : V // Q x=0}=(Fintype.card k)^(Module.finrank k V-1) := by
  have hqodd : Odd (Module.finrank k (V ⧸ Q.radical)) := by
    rw [radical_quotient_finrank]; exact hodd
  have hz := zero_card_of_radical_bot_odd p (Q.lift Q.radical le_rfl)
    (radical_lift_radical_eq_bot Q) hqodd
  rw [quadratic_zero_natCard_radical,Nat.card_eq_fintype_card,hz,← pow_add]
  congr 1
  have hdim := Q.radical.finrank_quotient_add_finrank
  obtain ⟨r,hr⟩ := hqodd
  omega

/-- Positive even actual quadratic rank gives the two exact finite-field zero counts. -/
theorem zero_card_of_even_rank (p : ℕ) [Fact p.Prime] [CharP k p] (Q : QuadraticForm k V)
    (s : ℕ) (hs : 0 < s)
    (hrank : Module.finrank k V-Module.finrank k Q.radical=2*s) :
    Nat.card {x : V // Q x=0}=(Fintype.card k)^(Module.finrank k V-1)+
        (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V-s-1) ∨
      Nat.card {x : V // Q x=0}=(Fintype.card k)^(Module.finrank k V-1)-
        (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V-s-1) := by
  have hqdim : Module.finrank k (V ⧸ Q.radical)=2*s := by
    rw [radical_quotient_finrank,hrank]
  have hz := zero_card_of_radical_bot_even p (Q.lift Q.radical le_rfl)
    (radical_lift_radical_eq_bot Q) s hs hqdim
  have hdim := Q.radical.finrank_quotient_add_finrank
  rw [hqdim] at hdim
  have hpow : (Fintype.card k)^(Module.finrank k Q.radical)*(Fintype.card k)^(2*s-1)=
      (Fintype.card k)^(Module.finrank k V-1) := by
    rw [← pow_add]; congr 1; omega
  have hcorr : (Fintype.card k)^(Module.finrank k Q.radical)*
        ((Fintype.card k-1)*(Fintype.card k)^(s-1))=
      (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V-s-1) := by
    rw [← mul_assoc,mul_comm ((Fintype.card k)^(Module.finrank k Q.radical)),mul_assoc,← pow_add]
    congr 2
    omega
  rw [quadratic_zero_natCard_radical,Nat.card_eq_fintype_card]
  rcases hz with hz | hz
  · left
    rw [hz,Nat.mul_add,hpow,hcorr]
  · right
    rw [hz,Nat.mul_sub_left_distrib,hpow,hcorr]

/-- Rank zero means every actual vector is a quadratic zero. -/
theorem zero_card_of_rank_zero (p : ℕ) [Fact p.Prime] [CharP k p] (Q : QuadraticForm k V)
    (hrank : Module.finrank k V-Module.finrank k Q.radical=0) :
    Nat.card {x : V // Q x=0}=(Fintype.card k)^(Module.finrank k V) := by
  have hqdim : Module.finrank k (V ⧸ Q.radical)=0 := by rw [radical_quotient_finrank,hrank]
  have hp := zeroCountPattern_of_radical_bot p (Q.lift Q.radical le_rfl)
    (radical_lift_radical_eq_bot Q)
  have hz : Fintype.card {x : V ⧸ Q.radical // Q.lift Q.radical le_rfl x=0}=1 := by
    rcases hp with h0 | ⟨r,hr,hz⟩ | ⟨r,hr,hz⟩
    · exact h0.2
    · omega
    · omega
  have hdim := Q.radical.finrank_quotient_add_finrank
  rw [hqdim,zero_add] at hdim
  rw [quadratic_zero_natCard_radical,Nat.card_eq_fintype_card,hz,mul_one,hdim]
end BinaryFieldCounterexamples.QuadraticGeometry

namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Module
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Every actual minimum-rank trace form has exactly the smaller, elliptic zero count. -/
theorem traceFamilyQuadraticForm_zero_natCard_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    Nat.card {x : B // traceFamilyQuadraticForm n t ht htn a c hcard hc x=0}=
      (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
  let : CharP k p := (algebraMap k B).charP (algebraMap k B).injective p
  have hd := finrank_eq_of_card (k:=k) (2*n) hcard
  have hz := QuadraticGeometry.zero_card_of_even_rank p
    (traceFamilyQuadraticForm n t ht htn a c hcard hc) t (by omega) hrank
  rw [hd] at hz
  have hb := traceFamilyQuadraticForm_zero_card_le_of_exact_rank p r hr hq n t ht htn
    a c hcard hc hne hrank
  have he : Nat.card {x : B // traceFamilyQuadraticForm n t ht htn a c hcard hc x=0}=
      (Finset.univ.filter (fun x : B => traceFamilyQuadraticForm n t ht htn a c hcard hc x=0)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype _ (by intro x; simp)
  rw [← he] at hb
  rcases hz with hz | hz
  · have hpos : 0 < (Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
      apply Nat.mul_pos
      · have := Fintype.one_lt_card (α:=k); omega
      · exact pow_pos Fintype.card_pos _
    omega
  · exact hz

/-- The exact smaller count also holds for the literal finite zero set used in family counting. -/
theorem traceFamilyQuadraticForm_zero_card_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    (Finset.univ.filter (fun x : B => traceFamilyQuadraticForm n t ht htn a c hcard hc x=0)).card=
      (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
  have he := traceFamilyQuadraticForm_zero_natCard_of_exact_rank p r hr hq n t ht htn a c hcard hc hne hrank
  rw [Nat.card_eq_fintype_card,Fintype.card_of_subtype
    (Finset.univ.filter (fun x : B => traceFamilyQuadraticForm n t ht htn a c hcard hc x=0))
    (by intro x; simp)] at he
  exact he

/-- The actual minimum-rank trace family contains no form with the hyperbolic zero count. -/
theorem traceFamilyQuadraticForm_not_hyperbolic_zero_count
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    Nat.card {x : B // traceFamilyQuadraticForm n t ht htn a c hcard hc x=0}≠
      (Fintype.card k)^(2*n-1)+(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
  rw [traceFamilyQuadraticForm_zero_natCard_of_exact_rank p r hr hq n t ht htn a c hcard hc hne hrank]
  have hpos : 0 < (Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
    apply Nat.mul_pos
    · have := Fintype.one_lt_card (α:=k); omega
    · exact pow_pos Fintype.card_pos _
  omega
end BinaryFieldCounterexamples.QuadraticFormTrace
