/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularDimension
public import BinaryFieldCounterexamples.Counting.GaussianIdentities
import Mathlib.Tactic.Linarith
/-!
# Normalized closed singular-subspace counts

Factoring the literal nonzero zero counts and cancelling the proved Gaussian
factorials normalizes the cleared products. Odd, hyperbolic, and elliptic
formulas retain the actual zero-count hypotheses. The all-dimension variants
use the proved geometric vanishing ranges, including the elliptic boundary.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
/-- The Gaussian coefficient cancels the descending q-factorial exactly in its valid range. -/
theorem gaussianBinomial_mul_factorial (q n e : ℕ) (hq : 1<q) (he : e≤n) :
    (gaussianBinomial q n e : ℚ)*gaussianFactorial q e=
      ∏ i ∈ Finset.range e,((q:ℚ)^(n-i)-1) := by
  apply mul_right_cancel₀ (gaussianFactorial_ne_zero q (n-e) hq)
  rw [gaussianBinomial_eq_gaussianPascal q n e hq,gaussianPascal_factorial q n e he,
    gaussianFactorial_descending q n e he]
/-- Casting a natural product of q-powers minus one preserves all subtractions. -/
theorem cast_prod_pow_sub_one (q e : ℕ) (hq : 1≤q) (f : ℕ→ℕ) :
    ((∏ i ∈ Finset.range e,(q^(f i)-1) : ℕ):ℚ)=
      ∏ i ∈ Finset.range e,((q:ℚ)^(f i)-1) := by
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Nat.cast_sub (one_le_pow₀ hq),Nat.cast_pow,Nat.cast_one]
/-- A cleared descending product gives the normalized rational Gaussian formula. -/
theorem normalized_gaussian_product (q n e c : ℕ) (hq : 1<q) (he : e≤n) (f : ℕ→ℕ)
    (hc : c*(∏ i ∈ Finset.range e,(q^(i+1)-1))=
      (∏ i ∈ Finset.range e,(q^(n-i)-1))*(∏ i ∈ Finset.range e,f i)) :
    (c:ℚ)=(gaussianBinomial q n e:ℚ)*(∏ i ∈ Finset.range e,(f i:ℚ)) := by
  have h := congrArg (fun a : ℕ => (a:ℚ)) hc
  simp only [Nat.cast_mul] at h
  rw [cast_prod_pow_sub_one q e (by omega),cast_prod_pow_sub_one q e (by omega),Nat.cast_prod] at h
  change (c:ℚ)*gaussianFactorial q e=_ at h
  apply mul_right_cancel₀ (gaussianFactorial_ne_zero q e hq)
  rw [mul_right_comm,gaussianBinomial_mul_factorial q n e hq he]
  exact h
/-- The odd-dimensional nonzero-zero count factors without subtraction artifacts. -/
theorem odd_zero_sub_one_factor (q s : ℕ) (hq : 1≤q) :
    q^(2*s)-1=(q^s-1)*(q^s+1) := by
  have h := Nat.sub_add_cancel (one_le_pow₀ hq : 1≤q^s)
  have he : (q^s-1)*(q^s+1)+1=q^(2*s) := by
    rw [Nat.mul_comm 2 s,pow_mul,pow_two]
    nlinarith
  omega
/-- The hyperbolic nonzero-zero count factors into its two Gaussian factors. -/
theorem even_positive_sub_one_factor (q s : ℕ) (hq : 1≤q) (hs : 1≤s) :
    evenQuadraticZeroCount q s true-1=(q^s-1)*(q^(s-1)+1) := by
  have hp : q^(2*s-1)=q^(s-1)*q^s := by rw [←pow_add]; congr 1; omega
  have hqpow : q^s=q*q^(s-1) := by rw [←pow_succ']; congr 1; omega
  have hqm : q-1+1=q := by omega
  have hsub := Nat.sub_add_cancel (one_le_pow₀ hq : 1≤q^s)
  simp only [evenQuadraticZeroCount,↓reduceIte,hp]
  have he : q^(s-1)*q^s+(q-1)*q^(s-1)=(q^s-1)*(q^(s-1)+1)+1 := by
    nlinarith [congrArg (fun u => u*q^(s-1)) hqm]
  omega
/-- The elliptic nonzero-zero count factors into its two Gaussian factors. -/
theorem even_negative_sub_one_factor (q s : ℕ) (hq : 1≤q) (hs : 1≤s) :
    evenQuadraticZeroCount q s false-1=(q^(s-1)-1)*(q^s+1) := by
  have hp : q^(2*s-1)=q^(s-1)*q^s := by rw [←pow_add]; congr 1; omega
  have hqpow : q^s=q*q^(s-1) := by rw [←pow_succ']; congr 1; omega
  have hqm : q-1+1=q := by omega
  have hsub := Nat.sub_add_cancel (one_le_pow₀ hq : 1≤q^(s-1))
  have hle : (q-1)*q^(s-1)≤q^(2*s-1) := by
    have h := even_correction_le q (s-1) hq
    simpa only [show 2*(s-1)+1=2*s-1 by omega] using h
  have hdiff := Nat.sub_add_cancel hle
  simp only [evenQuadraticZeroCount,Bool.false_eq_true,↓reduceIte]
  rw [hp] at hdiff ⊢
  have he : q^(s-1)*q^s-(q-1)*q^(s-1)=(q^(s-1)-1)*(q^s+1)+1 := by
    linarith [congrArg (fun u => u*q^(s-1)) hqm,congrArg (fun u => u*q^s) hsub]
  omega
variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]
/-- The normalized odd-dimensional radical-free singular-subspace count. -/
theorem totallySingularSubspaces_closed_odd (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (s e : ℕ) (he : e≤s) (hd : Module.finrank k V=2*s+1)
    (hz : Nat.card {x : V // Q x=0}=(Fintype.card k)^(2*s)) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=
      (gaussianBinomial (Fintype.card k) s e:ℚ)*
        ∏ i ∈ Finset.range e,((Fintype.card k:ℚ)^(s-i)+1) := by
  have hp := totallySingularSubspaces_product_odd Q hQ s e he hd hz
  simp_rw [odd_zero_sub_one_factor (Fintype.card k) _ Fintype.card_pos] at hp
  rw [Finset.prod_mul_distrib] at hp
  have hn := normalized_gaussian_product (Fintype.card k) s e _ Fintype.one_lt_card he
    (fun i => (Fintype.card k)^(s-i)+1) hp
  simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hn
/-- The normalized hyperbolic even-dimensional radical-free singular-subspace count. -/
theorem totallySingularSubspaces_closed_positive (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (s e : ℕ) (he : e≤s) (hd : Module.finrank k V=2*s)
    (hz : Nat.card {x : V // Q x=0}=evenQuadraticZeroCount (Fintype.card k) s true) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=
      (gaussianBinomial (Fintype.card k) s e:ℚ)*
        ∏ i ∈ Finset.range e,((Fintype.card k:ℚ)^(s-i-1)+1) := by
  have hp := totallySingularSubspaces_product_even Q hQ s e he hd true hz
  have hf : (∏ i ∈ Finset.range e,(evenQuadraticZeroCount (Fintype.card k) (s-i) true-1))=
      ∏ i ∈ Finset.range e,(((Fintype.card k)^(s-i)-1)*((Fintype.card k)^(s-i-1)+1)) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact even_positive_sub_one_factor _ _ Fintype.card_pos (by have := Finset.mem_range.mp hi; omega)
  rw [hf,Finset.prod_mul_distrib] at hp
  have hn := normalized_gaussian_product (Fintype.card k) s e _ Fintype.one_lt_card he
    (fun i => (Fintype.card k)^(s-i-1)+1) hp
  simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hn
/-- The normalized elliptic even-dimensional radical-free singular-subspace count. -/
theorem totallySingularSubspaces_closed_negative (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (s e : ℕ) (hs : 1≤s) (he : e≤s-1) (hd : Module.finrank k V=2*s)
    (hz : Nat.card {x : V // Q x=0}=evenQuadraticZeroCount (Fintype.card k) s false) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=
      (gaussianBinomial (Fintype.card k) (s-1) e:ℚ)*
        ∏ i ∈ Finset.range e,((Fintype.card k:ℚ)^(s-i)+1) := by
  have hp := totallySingularSubspaces_product_even Q hQ s e (by omega) hd false hz
  have hf : (∏ i ∈ Finset.range e,(evenQuadraticZeroCount (Fintype.card k) (s-i) false-1))=
      ∏ i ∈ Finset.range e,(((Fintype.card k)^(s-1-i)-1)*((Fintype.card k)^(s-i)+1)) := by
    apply Finset.prod_congr rfl
    intro i hi
    have h := even_negative_sub_one_factor (Fintype.card k) (s-i) Fintype.card_pos
      (by have := Finset.mem_range.mp hi; omega)
    simpa only [show s-i-1=s-1-i by omega] using h
  rw [hf,Finset.prod_mul_distrib] at hp
  have hn := normalized_gaussian_product (Fintype.card k) (s-1) e _ Fintype.one_lt_card he
    (fun i => (Fintype.card k)^(s-i)+1) hp
  simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hn
/-- The odd normalized formula extends by zero through all subspace dimensions. -/
theorem totallySingularSubspaces_closed_odd_all (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (s e : ℕ) (hd : Module.finrank k V=2*s+1)
    (hz : Nat.card {x : V // Q x=0}=(Fintype.card k)^(2*s)) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=
      (gaussianBinomial (Fintype.card k) s e:ℚ)*
        ∏ i ∈ Finset.range e,((Fintype.card k:ℚ)^(s-i)+1) := by
  by_cases he : e≤s
  · exact totallySingularSubspaces_closed_odd Q hQ s e he hd hz
  · rw [totallySingularSubspaces_card_eq_zero_of_large Q hQ e (by omega),
      gaussianBinomial_eq_gaussianPascal _ _ _ Fintype.one_lt_card,
      gaussianPascal_eq_zero _ _ _ (by omega)]
    simp
/-- The hyperbolic normalized formula extends by zero through all subspace dimensions. -/
theorem totallySingularSubspaces_closed_positive_all (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (s e : ℕ) (hd : Module.finrank k V=2*s)
    (hz : Nat.card {x : V // Q x=0}=evenQuadraticZeroCount (Fintype.card k) s true) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=
      (gaussianBinomial (Fintype.card k) s e:ℚ)*
        ∏ i ∈ Finset.range e,((Fintype.card k:ℚ)^(s-i-1)+1) := by
  by_cases he : e≤s
  · exact totallySingularSubspaces_closed_positive Q hQ s e he hd hz
  · rw [totallySingularSubspaces_card_eq_zero_of_large Q hQ e (by omega),
      gaussianBinomial_eq_gaussianPascal _ _ _ Fintype.one_lt_card,
      gaussianPascal_eq_zero _ _ _ (by omega)]
    simp
/-- The elliptic normalized formula extends by zero, including the excluded half-dimensional boundary. -/
theorem totallySingularSubspaces_closed_negative_all (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (s e : ℕ) (hs : 1≤s) (hd : Module.finrank k V=2*s)
    (hz : Nat.card {x : V // Q x=0}=evenQuadraticZeroCount (Fintype.card k) s false) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=
      (gaussianBinomial (Fintype.card k) (s-1) e:ℚ)*
        ∏ i ∈ Finset.range e,((Fintype.card k:ℚ)^(s-i)+1) := by
  by_cases he : e≤s-1
  · exact totallySingularSubspaces_closed_negative Q hQ s e hs he hd hz
  · have hz0 : Nat.card (TotallySingularSubspaces Q e)=0 := by
      by_cases heq : e=s
      · subst e
        exact totallySingularSubspaces_card_eq_zero_elliptic Q hQ s hs hd hz
      · exact totallySingularSubspaces_card_eq_zero_of_large Q hQ e (by omega)
    rw [hz0,gaussianBinomial_eq_gaussianPascal _ _ _ Fintype.one_lt_card,
      gaussianPascal_eq_zero _ _ _ (by omega)]
    simp
end BinaryFieldCounterexamples.QuadraticGeometry
