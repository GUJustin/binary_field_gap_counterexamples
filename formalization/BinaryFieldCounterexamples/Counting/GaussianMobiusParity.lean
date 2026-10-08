/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianInversion
public import BinaryFieldCounterexamples.Counting.AlternatingRankFormula
public import BinaryFieldCounterexamples.Counting.GaussianPascalAlternate
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Gaussian Möbius parity and the rank-one kernel

The alternating Gaussian Möbius sum controlling the rank-one quadratic
character kernel vanishes in odd rank.  In even rank it is an explicit odd
factor product.  A reciprocal Rogers--Szegő recurrence proves this parity
statement, and an exact adjacent-rank argument identifies the resulting even
block with the Gaussian Newton block used by the weighted moment calculation.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators Polynomial
noncomputable def reciprocalGaussian (q n k : ℕ) : ℚ :=
  (gaussianPascal q n k:ℚ)/(q:ℚ)^(k*(n-k))
noncomputable def reciprocalRogers (q n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n+1), Polynomial.monomial k (reciprocalGaussian q n k)
theorem coeff_reciprocalRogers (q n k:ℕ) :
 (reciprocalRogers q n).coeff k = if k≤n then reciprocalGaussian q n k else 0 := by
  simp [reciprocalRogers, Polynomial.coeff_monomial, reciprocalGaussian]
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples
theorem gp_one_mul_rat (q m:ℕ) : (gaussianPascal q m 1:ℚ)*((q:ℚ)-1)=(q:ℚ)^m-1 := by
  induction m with
  | zero => simp [gaussianPascal]
  | succ m ih =>
    rw [gaussianPascal_succ]
    push_cast
    simp only [gaussianPascal_zero,Nat.cast_one,pow_zero,mul_one,pow_succ']
    calc
      (1+(q:ℚ)*(gaussianPascal q m 1:ℚ))*((q:ℚ)-1) =
          ((q:ℚ)-1)+(q:ℚ)*((gaussianPascal q m 1:ℚ)*((q:ℚ)-1)) := by ring
      _ = _ := by rw [ih]; ring
theorem gp_ratio_sub_rat (q n k:ℕ) (hq:1<q) (hk0:0<k) (hk:k≤n) :
   (gaussianPascal q n k:ℚ)*((q:ℚ)^k-1)=
     (gaussianPascal q (n-1) (k-1):ℚ)*((q:ℚ)^n-1) := by
  have hf := gaussianPascal_flag q n k 1 hq hk (by omega)
  have hfc := congrArg (fun z : ℕ => (z:ℚ)) hf
  push_cast at hfc
  have h1:=gp_one_mul_rat q k
  have h2:=gp_one_mul_rat q n
  calc
   _ = (gaussianPascal q n k:ℚ)*((gaussianPascal q k 1:ℚ)*((q:ℚ)-1)) := by rw [h1]
   _ = ((gaussianPascal q n k:ℚ)*(gaussianPascal q k 1:ℚ))*((q:ℚ)-1) := by ring
   _ = ((gaussianPascal q n 1:ℚ)*(gaussianPascal q (n-1) (k-1):ℚ))*((q:ℚ)-1) := by rw [hfc]
   _ = (gaussianPascal q (n-1) (k-1):ℚ)*((gaussianPascal q n 1:ℚ)*((q:ℚ)-1)) := by ring
   _ = _ := by rw [h2]
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples
theorem reciprocalGaussian_ratio (q n k:ℕ) (hq:1<q) (hk0:0<k) (hk:k≤n) :
   (((1:ℚ)/(q:ℚ))^k-1)*reciprocalGaussian q n k =
    (((1:ℚ)/(q:ℚ))^n-1)*reciprocalGaussian q (n-1) (k-1) := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hk
  have hqn : (q:ℚ)≠0 := by positivity
  have hr:=gp_ratio_sub_rat q (k+a) k hq hk0 (by omega)
  have hkrep : k=(k-1)+1 := by omega
  have he : (k-1)*a+(k+a)=k*a+k := by
    calc
      _ = (k-1)*a+(((k-1)+1)+a) := by rw [←hkrep]
      _ = ((k-1)+1)*a+((k-1)+1) := by ring
      _ = _ := by rw [←hkrep]
  unfold reciprocalGaussian
  rw [show k+a-k=a by omega,show k+a-1-(k-1)=a by omega]
  calc
    (((1:ℚ)/(q:ℚ))^k-1)*((gaussianPascal q (k+a) k:ℚ)/(q:ℚ)^(k*a)) =
      -((gaussianPascal q (k+a) k:ℚ)*((q:ℚ)^k-1))/(q:ℚ)^(k*a+k) := by
        rw [div_pow]
        field_simp
        ring
    _ = -((gaussianPascal q (k+a-1) (k-1):ℚ)*((q:ℚ)^(k+a)-1))/(q:ℚ)^(k*a+k) := by rw [hr]
    _ = (((1:ℚ)/(q:ℚ))^(k+a)-1)*
        ((gaussianPascal q (k+a-1) (k-1):ℚ)/(q:ℚ)^((k-1)*a)) := by
          rw [div_pow]
          field_simp
          have hp : (q:ℚ)^(k+a)*(q:ℚ)^((k-1)*a)=(q:ℚ)^(k*a+k) := by
            rw [←pow_add,show k+a+(k-1)*a=(k-1)*a+(k+a) by omega,he]
          calc
            -((gaussianPascal q (k+a-1) (k-1):ℚ)*(q:ℚ)^(k+a)*
                ((q:ℚ)^(k+a)-1)*(q:ℚ)^((k-1)*a)) =
              -((gaussianPascal q (k+a-1) (k-1):ℚ)*((q:ℚ)^(k+a)-1)*
                ((q:ℚ)^(k+a)*(q:ℚ)^((k-1)*a))) := by ring
            _ = _ := by rw [hp]; ring
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples
theorem reciprocalGaussian_succ (q n k:ℕ) (hq:1<q) (hk:k≤n) :
   reciprocalGaussian q (n+1) (k+1)=reciprocalGaussian q n k+
      ((1:ℚ)/(q:ℚ))^(k+1)*reciprocalGaussian q n (k+1) := by
  have hqn:(q:ℚ)≠0:=by positivity
  have hp := gaussianPascal_succ_alt q n k hq hk
  unfold reciprocalGaussian
  by_cases he:k=n
  · subst k
    rw [gaussianPascal_eq_zero q n (n+1) (by omega)]
    simp [gaussianPascal_self]
  · have hkn:k<n:=by omega
    obtain ⟨b,hnb⟩ : ∃ b, n=k+1+b := by use n-k-1; omega
    subst n
    have hiD : k+1+b+1-(k+1)=b+1 := by omega
    have hiA : k+1+b-k=b+1 := by omega
    have hiC : k+1+b-(k+1)=b := by omega
    rw [hiD,hiA,hiC]
    have hpc := congrArg (fun z : ℕ => (z:ℚ)) hp
    push_cast at hpc
    rw [hiA] at hpc
    rw [hpc, add_div]
    apply congrArg₂ (· + ·)
    · have he1 : k*(b+1)+(b+1)=(k+1)*(b+1) := by ring
      field_simp
      calc
        _ = (gaussianPascal q (k+1+b) k:ℚ)*
            ((q:ℚ)^(k*(b+1))*(q:ℚ)^(b+1)) := by ring
        _ = _ := by rw [←pow_add,he1]
    · rw [div_pow]
      have he2 : (k+1)*b+(k+1)=(k+1)*(b+1) := by ring
      field_simp
      simp only [one_pow,mul_one]
      calc
        _ = (gaussianPascal q (k+1+b) (k+1):ℚ)*
            ((q:ℚ)^((k+1)*b)*(q:ℚ)^(k+1)) := by ring
        _ = _ := by rw [←pow_add,he2]
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples
theorem reciprocalRogers_recurrence (q n:ℕ) (hq:1<q) :
   reciprocalRogers q (n+2)=
    reciprocalRogers q (n+1)+Polynomial.X*reciprocalRogers q (n+1)-
      Polynomial.C (1-((1:ℚ)/(q:ℚ))^(n+1))*
        (Polynomial.X*reciprocalRogers q n) := by
  ext k
  rw [Polynomial.coeff_sub,Polynomial.coeff_add,Polynomial.coeff_C_mul]
  by_cases hk0:k=0
  · subst k
    simp [coeff_reciprocalRogers,reciprocalGaussian,gaussianPascal_zero]
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hk0
  rw [Polynomial.coeff_X_mul,Polynomial.coeff_X_mul]
  rw [coeff_reciprocalRogers,coeff_reciprocalRogers]
  simp only [Nat.succ_eq_add_one]
  by_cases hak : a≤n
  · rw [ite_eq_left (by omega : a+1≤n+2),
      ite_eq_left (by omega : a+1≤n+1)]
    rw [coeff_reciprocalRogers,coeff_reciprocalRogers]
    rw [ite_eq_left (by omega : a≤n+1),ite_eq_left hak]
    have hs:=reciprocalGaussian_succ q (n+1) a hq (by omega)
    have hr:=reciprocalGaussian_ratio q (n+1) (a+1) hq (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hr
    rw [hs]
    linear_combination hr
  · have han:a>n:=by omega
    by_cases he:a=n+1
    · subst a
      rw [ite_eq_left (by omega : n+1+1≤n+2),
        ite_eq_right (by omega : ¬n+1+1≤n+1)]
      rw [coeff_reciprocalRogers,ite_eq_left le_rfl,
        coeff_reciprocalRogers,ite_eq_right (by omega)]
      simp [reciprocalGaussian,gaussianPascal_self]
    · have ha2:n+1<a:=by omega
      rw [ite_eq_right (by omega : ¬a+1≤n+2),
        ite_eq_right (by omega : ¬a+1≤n+1)]
      rw [coeff_reciprocalRogers,ite_eq_right (by omega),
        coeff_reciprocalRogers,ite_eq_right (by omega)]
      ring
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples
noncomputable def reciprocalAlternatingSum (q n:ℕ) : ℚ :=
  Polynomial.eval (-1) (reciprocalRogers q n)
theorem reciprocalAlternatingSum_eq (q n:ℕ) : reciprocalAlternatingSum q n=
   ∑ k ∈ Finset.range (n+1), reciprocalGaussian q n k*(-1:ℚ)^k := by
  unfold reciprocalAlternatingSum reciprocalRogers
  change (Polynomial.evalRingHom (-1))
    (∑ k ∈ Finset.range (n+1), Polynomial.monomial k (reciprocalGaussian q n k))=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp
theorem reciprocalAlternatingSum_recurrence (q n:ℕ) (hq:1<q) :
   reciprocalAlternatingSum q (n+2)=
     (1-((1:ℚ)/(q:ℚ))^(n+1))*reciprocalAlternatingSum q n := by
  have h:=congrArg (Polynomial.eval (-1)) (reciprocalRogers_recurrence q n hq)
  simp only [reciprocalAlternatingSum,Polynomial.eval_sub,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C] at h ⊢
  linear_combination h
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples
def natTriangle (n:ℕ):ℕ:=n*(n-1)/2
theorem natTriangle_add (a b:ℕ) : natTriangle (a+b)=natTriangle a+natTriangle b+a*b := by
  unfold natTriangle
  rw [←Finset.sum_range_id,←Finset.sum_range_id,←Finset.sum_range_id]
  rw [Finset.sum_range_add,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  simp only [Nat.cast_id, Nat.mul_comm, add_left_comm, add_comm]
theorem parity_exponent (r e:ℕ) (he:e≤r) :
   (r-e)*(r-e-1)/2+(r-e)+e*(e+1)/2+e*(r-e)=r*(r+1)/2 := by
  let a:=r-e
  have hr:r=e+a:=by dsimp [a]; omega
  rw [hr]
  have hsub:e+a-e=a:=by omega
  rw [hsub]
  have h:=natTriangle_add (e+1) a
  unfold natTriangle at h
  have h1:e+1-1=e:=by omega
  have h2:e+1+a-1=e+a:=by omega
  rw [h1,h2] at h
  have hR:(e+a)*(e+a+1)/2=(e+1+a)*(e+a)/2 := by
    congr 1
    ring
  rw [hR,h]
  ring
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- The cleared Möbius sum arising from the upper term of the codimension-one
Gaussian Pascal split. -/
def gaussianMobiusParitySum (q r : ℕ) : ℚ :=
  ∑ e ∈ Finset.range (r+1), gaussianMobius q (r-e) * (q:ℚ)^(r-e) *
    (q:ℚ)^(e*(e+1)/2) * gaussianPascal q r e

/-- The companion lower term in the same codimension-one split. -/
def gaussianMobiusParityLowerSum (q r : ℕ) : ℚ :=
  ∑ e ∈ Finset.range r, gaussianMobius q (r-e) *
    (q:ℚ)^(e*(e+1)/2) * gaussianPascal q (r-1) e

@[simp] theorem gaussianMobiusParitySum_zero (q : ℕ) :
    gaussianMobiusParitySum q 0=1 := by
  simp [gaussianMobiusParitySum,gaussianMobius,pow_zero]
  rfl

@[simp] theorem gaussianMobiusParitySum_one (q : ℕ) :
    gaussianMobiusParitySum q 1=0 := by
  norm_num [gaussianMobiusParitySum,gaussianMobius,gaussianPascal,
    Finset.sum_range_succ]

/-- The lower Pascal contribution is exactly the negative preceding parity sum. -/
theorem gaussianMobiusParityLowerSum_succ (q r : ℕ) :
    gaussianMobiusParityLowerSum q (r+1) = -gaussianMobiusParitySum q r := by
  unfold gaussianMobiusParityLowerSum gaussianMobiusParitySum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have her : e≤r := by have := Finset.mem_range.mp he; omega
  have ha : r+1-e=(r-e)+1 := by omega
  rw [ha,gaussianMobius]
  have hpow : ((-1:ℚ)^((r-e)+1))=-(-1:ℚ)^(r-e) := by rw [pow_succ]; ring
  have htri : ((r-e)+1)*((r-e)+1-1)/2=(r-e)*(r-e-1)/2+(r-e) := by
    calc
      _ = ∑ i ∈ Finset.range ((r-e)+1), i := (Finset.sum_range_id _).symm
      _ = (∑ i ∈ Finset.range (r-e), i)+(r-e) := by rw [Finset.sum_range_succ]
      _ = _ := by rw [Finset.sum_range_id]
  rw [hpow,htri,pow_add]
  rw [gaussianMobius]
  rw [show r+1-1=r by omega]
  ring


theorem gaussianMobiusParitySum_eq_reciprocal (q r : ℕ) (hq : 1 < q) :
    gaussianMobiusParitySum q r =
      (-1 : ℚ)^r * (q : ℚ)^(r*(r+1)/2) * reciprocalAlternatingSum q r := by
  rw [reciprocalAlternatingSum_eq]
  unfold gaussianMobiusParitySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have her : e ≤ r := by simpa using Finset.mem_range.mp he
  rw [gaussianMobius, reciprocalGaussian]
  have hqn : (q : ℚ) ≠ 0 := by positivity
  have hsign : (-1 : ℚ)^(r-e) = (-1 : ℚ)^r * (-1 : ℚ)^e := by
    calc
      (-1 : ℚ)^(r-e) = (-1 : ℚ)^(r-e) * ((-1 : ℚ)^e)^2 := by
        rw [← pow_mul]
        norm_num
      _ = _ := by
        have hex : r - e + e * 2 = r + e := by omega
        rw [← pow_mul, ← pow_add, hex, pow_add]
  have hexp := parity_exponent r e her
  rw [show r - e - 1 = (r-e)-1 by rfl]
  rw [div_eq_mul_inv]
  field_simp
  have hpow :
      (q : ℚ)^((r-e)*(r-e-1)/2) * (q : ℚ)^(r-e) *
          (q : ℚ)^(e*(e+1)/2) * (q : ℚ)^(e*(r-e)) =
        (q : ℚ)^(r*(r+1)/2) := by
    rw [← pow_add, ← pow_add, ← pow_add, hexp]
  calc
    _ = (gaussianPascal q r e : ℚ) *
        ((-1 : ℚ)^r * (-1 : ℚ)^e) * (q : ℚ)^(r*(r+1)/2) := by
          rw [← hpow, hsign]
          ring
    _ = _ := by ring
end BinaryFieldCounterexamples

namespace BinaryFieldCounterexamples
theorem upperTriangle_add_two (r : ℕ) :
    (r+2)*(r+2+1)/2 = r*(r+1)/2 + (2*r+3) := by
  calc
    (r+2)*(r+2+1)/2 = (r+2+1)*((r+2+1)-1)/2 := by
      rw [show r+2+1-1=r+2 by omega, Nat.mul_comm]
    _ = ∑ i ∈ Finset.range (r+2+1), i := (Finset.sum_range_id _).symm
    _ = (∑ i ∈ Finset.range (r+1), i) + (r+1) + (r+2) := by
      rw [show r+2+1=(r+1)+2 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
    _ = _ := by
      rw [Finset.sum_range_id, show r+1-1=r by omega]
      ring

theorem gaussianMobiusParitySum_recurrence (q r : ℕ) (hq : 1 < q) :
    gaussianMobiusParitySum q (r+2) =
      (q : ℚ)^(r+2) * ((q : ℚ)^(r+1)-1) * gaussianMobiusParitySum q r := by
  rw [gaussianMobiusParitySum_eq_reciprocal q (r+2) hq,
    reciprocalAlternatingSum_recurrence q r hq,
    gaussianMobiusParitySum_eq_reciprocal q r hq]
  have hqn : (q : ℚ) ≠ 0 := by positivity
  have htri := upperTriangle_add_two r
  rw [htri, pow_add]
  norm_num
  field_simp
  rw [show 2*r+3=(r+2)+(r+1) by omega, pow_add]
  ring
end BinaryFieldCounterexamples

namespace BinaryFieldCounterexamples
noncomputable def mobiusParityProduct (q u : ℕ) : ℚ :=
  (q : ℚ)^(u*(u+1)) * ∏ i ∈ Finset.range u, ((q : ℚ)^(2*i+1)-1)

theorem mobiusParityProduct_succ (q u : ℕ) :
    mobiusParityProduct q (u+1) =
      (q : ℚ)^(2*u+2) * ((q : ℚ)^(2*u+1)-1) * mobiusParityProduct q u := by
  unfold mobiusParityProduct
  rw [Finset.prod_range_succ]
  have he : (u+1)*(u+1+1)=u*(u+1)+(2*u+2) := by ring
  rw [he, pow_add]
  ring

theorem gaussianMobiusParitySum_even (q u : ℕ) (hq : 1 < q) :
    gaussianMobiusParitySum q (2*u) = mobiusParityProduct q u := by
  induction u with
  | zero => simp [mobiusParityProduct]
  | succ u ih =>
      rw [show 2*(u+1)=2*u+2 by ring,
        gaussianMobiusParitySum_recurrence q (2*u) hq, ih,
        mobiusParityProduct_succ]

theorem gaussianMobiusParitySum_odd (q u : ℕ) (hq : 1 < q) :
    gaussianMobiusParitySum q (2*u+1) = 0 := by
  induction u with
  | zero => simp
  | succ u ih =>
      rw [show 2*(u+1)+1=(2*u+1)+2 by ring,
        gaussianMobiusParitySum_recurrence q (2*u+1) hq, ih]
      ring
end BinaryFieldCounterexamples

namespace BinaryFieldCounterexamples
noncomputable def rankOneMobiusBlock (q n u : ℕ) : ℚ :=
  (gaussianPascal q (2*n-1) (2*u) : ℚ) * mobiusParityProduct q u

noncomputable def rankOneNewtonBlock (q n u : ℕ) : ℚ :=
  (q : ℚ)^(2*u) * (gaussianPascal (q^2) (n-1) u : ℚ) *
    gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u

theorem rankOneMobiusBlock_cross_succ (q n u : ℕ) (hq : 1 < q)
    (hu : u+1 ≤ n-1) :
    rankOneMobiusBlock q n (u+1) * ((q : ℚ)^(2*u+2)-1) =
      (q : ℚ)^(2*u+2) * ((q : ℚ)^(2*n-1-2*u)-1) *
        ((q : ℚ)^(2*n-1-(2*u+1))-1) * rankOneMobiusBlock q n u := by
  have hr1 := gaussianPascal_ratio q (2*n-1) (2*u) hq (by omega)
  have hr2 := gaussianPascal_ratio q (2*n-1) (2*u+1) hq (by omega)
  rw [show 2*u+1+1=2*u+2 by omega] at hr2
  unfold rankOneMobiusBlock
  rw [mobiusParityProduct_succ]
  calc
    _ = ((gaussianPascal q (2*n-1) (2*u+2) : ℚ) *
          ((q : ℚ)^(2*u+2)-1)) *
        ((q : ℚ)^(2*u+2) * ((q : ℚ)^(2*u+1)-1) *
          mobiusParityProduct q u) := by ring
    _ = ((gaussianPascal q (2*n-1) (2*u+1) : ℚ) *
          ((q : ℚ)^(2*n-1-(2*u+1))-1)) *
        ((q : ℚ)^(2*u+2) * ((q : ℚ)^(2*u+1)-1) *
          mobiusParityProduct q u) := by rw [hr2]
    _ = (q : ℚ)^(2*u+2) * ((q : ℚ)^(2*n-1-(2*u+1))-1) *
        ((gaussianPascal q (2*n-1) (2*u+1) : ℚ) *
          ((q : ℚ)^(2*u+1)-1)) * mobiusParityProduct q u := by ring
    _ = _ := by rw [hr1]; ring

theorem rankOneNewtonBlock_cross_succ (q n u : ℕ) (hq : 1 < q)
    (hu : u+1 ≤ n-1) :
    rankOneNewtonBlock q n (u+1) * ((q : ℚ)^(2*u+2)-1) =
      (q : ℚ)^(2*u+2) * ((q : ℚ)^(2*n-1-2*u)-1) *
        ((q : ℚ)^(2*n-1-(2*u+1))-1) * rankOneNewtonBlock q n u := by
  have hq2 : 1 < q^2 := Nat.one_lt_pow (by omega) hq
  have hr := gaussianPascal_ratio (q^2) (n-1) u hq2 (by omega)
  have hexp : 2*n-1 = 2*u + (2*n-1-2*u) := by omega
  have hqpow : ((q^2 : ℕ) : ℚ)^u = (q : ℚ)^(2*u) := by
    push_cast
    rw [← pow_mul]
  have hqpow2 : ((q : ℚ)^2)^u = (q : ℚ)^(2*u) := by
    rw [← pow_mul]
  have hgamma : (q : ℚ)^(2*n-1) - ((q^2 : ℕ)^u : ℚ) =
      (q : ℚ)^(2*u) * ((q : ℚ)^(2*n-1-2*u)-1) := by
    norm_num only [Nat.cast_pow]
    have hp : (q : ℚ)^(2*n-1) =
        (q : ℚ)^(2*u) * (q : ℚ)^(2*n-1-2*u) := by
      conv_lhs => rw [hexp]
      rw [pow_add]
    rw [hqpow2, hp]
    ring
  unfold rankOneNewtonBlock
  have hn : gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) (u+1) =
      gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u *
        ((q : ℚ)^(2*n-1) - ((q^2 : ℕ)^u : ℚ)) := by
    exact Finset.prod_range_succ _ _
  rw [hn, hgamma]
  norm_num only [Nat.cast_pow] at hr
  rw [show ((q : ℚ)^2)^(u+1) = (q : ℚ)^(2*u+2) by
    rw [← pow_mul, show 2*(u+1)=2*u+2 by ring]] at hr
  calc
    _ = (q : ℚ)^(2*(u+1)) *
        ((gaussianPascal (q^2) (n-1) (u+1) : ℚ) *
          ((q : ℚ)^(2*u+2)-1)) *
        (gaussianNewtonProduct (q^2) ((q : ℚ)^(2*n-1)) u *
          ((q : ℚ)^(2*u) * ((q : ℚ)^(2*n-1-2*u)-1))) := by ring
    _ = _ := by
      rw [hr]
      rw [show ((q : ℚ)^2)^(n-1-u) =
        (q : ℚ)^(2*n-1-(2*u+1)) by rw [← pow_mul]; congr 1; omega]
      ring
end BinaryFieldCounterexamples

namespace BinaryFieldCounterexamples
theorem rankOneMobiusBlock_eq_newton (q n u : ℕ) (hq : 1 < q)
    (hu : u ≤ n-1) : rankOneMobiusBlock q n u = rankOneNewtonBlock q n u := by
  induction u with
  | zero =>
      simp [rankOneMobiusBlock, rankOneNewtonBlock, mobiusParityProduct,
        gaussianPascal_zero, gaussianNewtonProduct]
  | succ u ih =>
      have hu' : u ≤ n-1 := by omega
      have hL := rankOneMobiusBlock_cross_succ q n u hq hu
      have hR := rankOneNewtonBlock_cross_succ q n u hq hu
      have hden : (q : ℚ)^(2*u+2)-1 ≠ 0 := by
        exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by exact_mod_cast hq) (by omega)))
      apply mul_right_cancel₀ hden
      rw [hL, hR, ih hu']
end BinaryFieldCounterexamples

namespace BinaryFieldCounterexamples
/-- The inverse-incidence kernel for a rank-one quadratic form in dimension `2n`. -/
noncomputable def rankOneIncidenceKernel (q n r : ℕ) : ℚ :=
  (gaussianPascal q (2*n-1) r : ℚ) * gaussianMobiusParitySum q r +
    (gaussianPascal q (2*n-1) (r-1) : ℚ) * gaussianMobiusParityLowerSum q r

theorem rankOneIncidenceKernel_even (q n u : ℕ) (hq : 1 < q)
    (hu : u ≤ n-1) :
    rankOneIncidenceKernel q n (2*u) = rankOneNewtonBlock q n u := by
  cases u with
  | zero =>
      simp [rankOneIncidenceKernel, rankOneNewtonBlock,
        gaussianMobiusParityLowerSum, gaussianNewtonProduct, gaussianPascal_zero]
  | succ u =>
      rw [rankOneIncidenceKernel, gaussianMobiusParitySum_even q (u+1) hq]
      rw [show 2*(u+1)=(2*u+1)+1 by omega,
        gaussianMobiusParityLowerSum_succ q (2*u+1),
        gaussianMobiusParitySum_odd q u hq]
      simp only [neg_zero, mul_zero, add_zero]
      exact rankOneMobiusBlock_eq_newton q n (u+1) hq hu

theorem rankOneIncidenceKernel_odd (q n u : ℕ) (hq : 1 < q)
    (hu : u ≤ n-1) :
    rankOneIncidenceKernel q n (2*u+1) = -rankOneNewtonBlock q n u := by
  rw [rankOneIncidenceKernel, gaussianMobiusParitySum_odd q u hq,
    gaussianMobiusParityLowerSum_succ q (2*u),
    gaussianMobiusParitySum_even q u hq]
  simp only [mul_zero, zero_add]
  rw [show 2*u+1-1=2*u by omega]
  rw [show (gaussianPascal q (2*n-1) (2*u) : ℚ) * -mobiusParityProduct q u =
    -(rankOneMobiusBlock q n u) by unfold rankOneMobiusBlock; ring]
  rw [rankOneMobiusBlock_eq_newton q n u hq hu]
end BinaryFieldCounterexamples
