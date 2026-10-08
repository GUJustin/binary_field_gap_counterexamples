/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularUniformity
/-!
# Cleared products for radical-free singular-subspace counts

Actual flag counting gives a product along any valid hyperbolic zero-count
chain. The odd and both even numerical types instantiate that chain, retaining
natural-number subtraction and the full admissible dimension range.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
universe u v
variable {k : Type u} [Field k] [Fintype k]
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.decEq Classical.propDecidable
attribute [local instance] singularLinesFintype totallySingularSubspacesFintype
/-- A radical-free form has the cleared singular-subspace product for any literal chain of successive hyperbolic zero counts. -/
theorem totallySingularSubspaces_product_of_zero_chain (e : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module k V] [Fintype V]
      (Q : QuadraticForm k V) (_hQ : Q.radical=⊥) (d : ℕ)
      (_hd : Module.finrank k V=d) (_hde : 2*e≤d) (z : ℕ→ℕ),
      z 0=Nat.card {x : V // Q x=0} →
      (∀ i, i+1<e → z i=(Fintype.card k-1)*(Fintype.card k)^(d-2*i-2)+Fintype.card k*z (i+1)) →
      Nat.card (TotallySingularSubspaces Q e)*
        (∏ i ∈ Finset.range e, ((Fintype.card k)^(i+1)-1)) =
        ∏ i ∈ Finset.range e, (z i-1) := by
  induction e with
  | zero =>
    intro V _ _ _ Q hQ d hd hde z hz hc
    simp only [Finset.range_zero,Finset.prod_empty,mul_one]
    exact totallySingularSubspaces_zero_card Q
  | succ e ih =>
    intro V _ _ _ Q hQ d hd hde z hz hc
    by_cases he : e=0
    · subst e
      simpa only [Finset.prod_range_one,zero_add,pow_one,hz,TotallySingularSubspaces,SingularLines] using (singularLines_card_mul Q).symm
    have hfi (L : SingularLines Q) :
        Nat.card {S : TotallySingularSubspaces Q (e+1) // L.val≤S.val}*
          (∏ i ∈ Finset.range e, ((Fintype.card k)^(i+1)-1)) =
            ∏ i ∈ Finset.range e, (z (i+1)-1) := by
      have hL : ¬L.val≤Q.radical := by
        rw [hQ]
        intro h
        have hb := le_antisymm h bot_le
        have hh := L.property.1
        rw [hb,finrank_bot] at hh
        omega
      obtain ⟨x,y,hxne,hx,hy,hxy,hspan⟩ := nonradical_line_hyperbolic Q L hL
      rw [through_singular_line_card Q L x hx hxne hspan]
      let Q' := (Q.comp (Q.polarBilin x).ker.subtype).lift (singularPerpLine Q x hx)
        (singularPerpLine_le_radical Q x hx)
      let : Fintype ((Q.polarBilin x).ker ⧸ singularPerpLine Q x hx) := Fintype.ofFinite _
      have hr' : Q'.radical=⊥ := by
        apply Submodule.finrank_eq_zero.mp
        rw [singularLineQuotient_radical_finrank Q x y hx hy hxy,hQ,finrank_bot]
      apply ih Q' hr' (d-2) (by rw [singularLineQuotient_finrank Q x y hx hy hxy,hd])
        (by omega) (fun i => z (i+1))
      · have hrec := singularLineQuotient_zero_count Q x y hx hy hxy
        have hzc := hc 0 (by omega)
        simp only [mul_zero,Nat.sub_zero,zero_add] at hzc
        rw [hd,←hz,hzc] at hrec
        exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos (Nat.add_left_cancel hrec)
      · intro i hi
        have h := hc (i+1) (by omega)
        have hex : d-2*(i+1)-2=d-2-2*i-2 := by omega
        simpa only [hex] using h
    have hs := singular_flag_count Q (e+1)
    have hsum : (∑ L : SingularLines Q,
        Nat.card {S : TotallySingularSubspaces Q (e+1) // L.val≤S.val})*
          (∏ i ∈ Finset.range e, ((Fintype.card k)^(i+1)-1)) =
        Nat.card (SingularLines Q)*(∏ i ∈ Finset.range e,(z (i+1)-1)) := by
      rw [Finset.sum_mul]
      rw [Finset.sum_congr rfl (fun L _ => hfi L)]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
    rw [hs] at hsum
    have hm := congrArg (fun a : ℕ => a*(Fintype.card k-1)) hsum
    have hdiv : (((Fintype.card k)^(e+1)-1)/(Fintype.card k-1))*(Fintype.card k-1)=
        (Fintype.card k)^(e+1)-1 := Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one _ _)
    have hl : Nat.card (SingularLines Q)*(Fintype.card k-1)=z 0-1 := by
      rw [hz]; exact (singularLines_card_mul Q).symm
    rw [Finset.prod_range_succ,Finset.prod_range_succ']
    calc
      _ = ((Nat.card (TotallySingularSubspaces Q (e+1)) *
          (((Fintype.card k)^(e+1)-1)/(Fintype.card k-1))) *
          (∏ i ∈ Finset.range e,((Fintype.card k)^(i+1)-1)))*(Fintype.card k-1) := by
        nth_rw 1 [←hdiv]
        ring
      _ = _ := hm
      _ = _ := by rw [mul_right_comm,hl]; exact mul_comm _ _
/-- The two numerical zero counts for a positive even-dimensional radical-free form. -/
def evenQuadraticZeroCount (q s : ℕ) (positive : Bool) : ℕ :=
  if positive then q^(2*s-1)+(q-1)*q^(s-1) else q^(2*s-1)-(q-1)*q^(s-1)
/-- Both even numerical types satisfy the literal hyperbolic zero-count recurrence away from dimension zero. -/
theorem evenQuadraticZeroCount_succ (q s : ℕ) (hq : 1≤q) (hs : 1≤s) (positive : Bool) :
    evenQuadraticZeroCount q (s+1) positive=
      (q-1)*q^(2*s)+q*evenQuadraticZeroCount q s positive := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hs
  have hqm : q-1+1=q := by omega
  have hp2 : q^(2*a+2)=q*q^(2*a+1) := by rw [show 2*a+2=(2*a+1)+1 by omega,pow_succ']
  have hp3 : q^(2*a+3)=q*q*q^(2*a+1) := by
    rw [show 2*a+3=(2*a+1)+2 by omega,pow_add,pow_two]; ring
  have he1 : 2*(1+a+1)-1=2*a+3 := by omega
  have he2 : 1+a+1-1=a+1 := by omega
  have he3 : 2*(1+a)=2*a+2 := by omega
  have he5 : 1+a-1=a := by omega
  have he6 : 2*a+2-1=2*a+1 := by omega
  have hbase : (q-1)*(q*q^(2*a+1))+q*q^(2*a+1)=q*q*q^(2*a+1) := by
    rw [← add_one_mul, hqm, ← mul_assoc]
  cases positive
  · simp only [evenQuadraticZeroCount,Bool.false_eq_true,↓reduceIte,he1,he2,he3,he6,he5,hp2,hp3,pow_succ' q a]
    -- Distribute multiplication over natural subtraction using its exact bound.
    rw [Nat.mul_sub_left_distrib,
      ← Nat.add_sub_assoc (Nat.mul_le_mul_left q (even_correction_le q a hq)), hbase]
    congr 1
    ac_rfl
  · simp only [evenQuadraticZeroCount,↓reduceIte,he1,he2,he3,he6,he5,hp2,hp3,pow_succ' q a]
    rw [Nat.mul_add, ← add_assoc, hbase]
    congr 1
    ac_rfl
/-- The cleared even-type product follows for either literal zero-count sign. -/
theorem totallySingularSubspaces_product_even {V : Type v}
    [AddCommGroup V] [Module k V] [Fintype V]
    (Q : QuadraticForm k V) (hQ : Q.radical=⊥) (s e : ℕ) (he : e≤s)
    (hd : Module.finrank k V=2*s) (positive : Bool)
    (hz : Nat.card {x : V // Q x=0}=evenQuadraticZeroCount (Fintype.card k) s positive) :
    Nat.card (TotallySingularSubspaces Q e)*
      (∏ i ∈ Finset.range e,((Fintype.card k)^(i+1)-1)) =
      ∏ i ∈ Finset.range e,(evenQuadraticZeroCount (Fintype.card k) (s-i) positive-1) := by
  apply totallySingularSubspaces_product_of_zero_chain e Q hQ (2*s) hd (by omega)
    (fun i => evenQuadraticZeroCount (Fintype.card k) (s-i) positive)
  · simpa using hz.symm
  · intro i hi
    have hs : 1≤s-(i+1) := by omega
    have hh := evenQuadraticZeroCount_succ (Fintype.card k) (s-(i+1)) Fintype.card_pos hs positive
    have ha : s-(i+1)+1=s-i := by omega
    have hb : 2*(s-(i+1))=2*s-2*i-2 := by omega
    simpa only [ha,hb] using hh
/-- The cleared odd-dimensional product uses the actual odd zero count. -/
theorem totallySingularSubspaces_product_odd {V : Type v}
    [AddCommGroup V] [Module k V] [Fintype V]
    (Q : QuadraticForm k V) (hQ : Q.radical=⊥) (s e : ℕ) (he : e≤s)
    (hd : Module.finrank k V=2*s+1)
    (hz : Nat.card {x : V // Q x=0}=(Fintype.card k)^(2*s)) :
    Nat.card (TotallySingularSubspaces Q e)*
      (∏ i ∈ Finset.range e,((Fintype.card k)^(i+1)-1)) =
      ∏ i ∈ Finset.range e,((Fintype.card k)^(2*(s-i))-1) := by
  apply totallySingularSubspaces_product_of_zero_chain e Q hQ (2*s+1) hd (by omega)
    (fun i => (Fintype.card k)^(2*(s-i)))
  · simpa using hz.symm
  · intro i hi
    let q := Fintype.card k
    have hq : q-1+1=q := by have := Fintype.card_pos (α:=k); dsimp [q]; omega
    have ha : 2*(s-i)=2*(s-(i+1))+2 := by omega
    have hb : 2*s+1-2*i-2=2*(s-(i+1))+1 := by omega
    change q^(2*(s-i))=(q-1)*q^(2*s+1-2*i-2)+q*q^(2*(s-(i+1)))
    rw [ha,hb,pow_add,pow_two,pow_succ']
    rw [← add_one_mul, hq]
    ac_rfl
end BinaryFieldCounterexamples.QuadraticGeometry
