/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.LocatorElimination
public import BinaryFieldCounterexamples.Constructions.AllRates.AffineLabels
public import BinaryFieldCounterexamples.Polynomial.DivX

/-!
# Exact recursive locator cancellation

The triangular scalar recursion cancels every prescribed leading coefficient
of a concrete Frobenius combination. Its next coefficient is the affine challenge.
The remaining numerator has degree at most `2^(m-2)` and zero constant term;
removing `X` therefore gives a strict-degree witness on every nonzero root.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.AllRatesConstruction
open Polynomial BinaryLocator
variable {F : Type*} [Field F] [CharP F 2]
set_option linter.unusedSectionVars false

/-- The literal binary coefficients of a degree-`2^m` locator. -/
def locatorPrefix (P : F[X]) (m : ℕ) (j : ℕ) : F := P.coeff (2^(m-j))
/-- Triangular coefficients below the final challenge position split at the diagonal. -/
theorem binaryLocatorCombination_coeff_lt (P : F[X]) (m s j : ℕ)
    (hs : 1≤s) (hm : s≤m) (hj : j<s) (hdeg : P.natDegree=2^m)
    (hmonic : P.Monic) (b : ℕ → F) :
    (binaryLocatorCombination P s b).coeff (2^(m+s-1-j))=
      b j + ∑ i∈Finset.range j, b i*(locatorPrefix P m (j-i))^(2^(s-1-i)) := by
  classical
  rw [binaryLocatorCombination_coeff P m s j hs hm (by omega) hdeg]
  have he : (∑ i∈Finset.range s, if i≤j then
      b i*(P.coeff (2^(m-(j-i))))^(2^(s-1-i)) else 0)=
      ∑ i∈Finset.range (j+1), b i*(P.coeff (2^(m-(j-i))))^(2^(s-1-i)) := by
    rw [←Finset.sum_subset (Finset.range_mono (show j+1≤s by omega))]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_left (show i≤j by have := Finset.mem_range.mp hi; omega)]
    · intro i hi hni
      rw [ite_eq_right (show ¬i≤j by simpa using hni)]
  rw [he,Finset.sum_range_succ]
  have hc : P.coeff (2^m)=1 := by rw [←hdeg]; exact hmonic.coeff_natDegree
  simp only [Nat.sub_self,Nat.sub_zero,hc,one_pow,mul_one]
  exact add_comm _ _
/-- The recursive coefficients cancel precisely the prescribed free leading coefficients. -/
theorem cancellationCombination_coeff_lt (P : F[X]) (m s j : ℕ)
    (hs : 1≤s) (hm : s≤m) (hj : j<s) (hdeg : P.natDegree=2^m)
    (hmonic : P.Monic) (θ : ℕ → F) :
    (binaryLocatorCombination P s (cancellationCoeff s (locatorPrefix P m) θ)).coeff
      (2^(m+s-1-j))=if j=0 then 1 else θ j := by
  rw [binaryLocatorCombination_coeff_lt P m s j hs hm hj hdeg hmonic]
  cases j with
  | zero => simp
  | succ j =>
    rw [cancellationCoeff_succ]
    simp only [Nat.succ_ne_zero,ite_false]
    rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]
/-- The final remaining leading coefficient is exactly the affine challenge. -/
theorem cancellationCombination_coeff_label (P : F[X]) (m s : ℕ)
    (hs : 1≤s) (hm : s≤m) (hdeg : P.natDegree=2^m) (θ : ℕ → F) :
    (binaryLocatorCombination P s (cancellationCoeff s (locatorPrefix P m) θ)).coeff
      (2^(m-1))=cancellationLabel s (locatorPrefix P m) θ := by
  have he : m+s-1-s=m-1 := by omega
  rw [←he,binaryLocatorCombination_coeff P m s s hs hm le_rfl hdeg,
    cancellationLabel_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ite_eq_left (show i≤s by have := Finset.mem_range.mp hi; omega)]
  rfl
/-- Recursive cancellation produces the exact common head, affine challenge, and strict next
binary gap. -/
theorem exists_cancellation_remainder (P : F[X]) (hP : IsBinaryLinearized P)
    (m s : ℕ) (hs : 1≤s) (hm : s≤m) (hdeg : P.natDegree=2^m)
    (hmonic : P.Monic) (θ : ℕ → F) :
    ∃ R : F[X], R.natDegree≤2^(m-2) ∧ R.coeff 0=0 ∧
      binaryLocatorCombination P s (cancellationCoeff s (locatorPrefix P m) θ)=
        binaryPrefixPolynomial (m+s-1) s (fun j => if j=0 then 1 else θ j)+
        C (cancellationLabel s (locatorPrefix P m) θ)*X^(2^(m-1))+R := by
  let Q := binaryLocatorCombination P s (cancellationCoeff s (locatorPrefix P m) θ)
  let R := Q-binaryPrefixPolynomial (m+s-1) (s+1) (fun j => Q.coeff (2^(m+s-1-j)))
  have hQ := binaryLocatorCombination_support P hP s (cancellationCoeff s (locatorPrefix P m) θ)
  have htail := binaryPrefix_remainder Q hQ (m+s-1) s (by omega)
    (binaryLocatorCombination_natDegree_le P m s hs hdeg _)
  have hexp : m+s-1-s-1=m-2 := by omega
  rw [hexp] at htail
  refine ⟨R,htail.1,htail.2,?_⟩
  have hprefix : binaryPrefixPolynomial (m+s-1) (s+1)
      (fun j => Q.coeff (2^(m+s-1-j)))=
      binaryPrefixPolynomial (m+s-1) s (fun j => if j=0 then 1 else θ j)+
      C (cancellationLabel s (locatorPrefix P m) θ)*X^(2^(m-1)) := by
    unfold binaryPrefixPolynomial
    rw [Finset.sum_range_succ]
    have hexp' : m+s-1-s=m-1 := by omega
    dsimp only [Q]
    rw [hexp',cancellationCombination_coeff_label P m s hs hm hdeg θ]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [cancellationCombination_coeff_lt P m s j hs hm (Finset.mem_range.mp hj) hdeg hmonic θ]
  change Q=_+_+(Q-_)
  rw [hprefix]
  abel
/-- The common first input after removing its zero constant term. -/
noncomputable def cancellationSource (m s : ℕ) (θ : ℕ → F) : F[X] :=
  (binaryPrefixPolynomial (m+s-1) s (fun j => if j=0 then 1 else θ j)).divX
/-- The common first input still has the required strict ambient degree bound. -/
theorem cancellationSource_degree_lt (m s : ℕ) (θ : ℕ → F) :
    (cancellationSource m s θ).degree<2^(m+s-1) := by
  exact degree_divX_lt_of_natDegree_le _ _ (binaryPrefixPolynomial_natDegree_le ..)
/-- Dividing the exact cancellation identity yields a strict-degree witness at every nonzero locator root. -/
theorem exists_cancellation_witness (P : F[X]) (hP : IsBinaryLinearized P)
    (m s : ℕ) (hs : 1≤s) (hm : s≤m) (hdeg : P.natDegree=2^m)
    (hmonic : P.Monic) (θ : ℕ → F) :
    ∃ p : F[X], p.degree<2^(m-2) ∧ ∀ x : F, P.eval x=0 → x≠0 →
      (cancellationSource m s θ).eval x+
        cancellationLabel s (locatorPrefix P m) θ*x^(2^(m-1)-1)=p.eval x := by
  obtain ⟨R,hR,hR0,hshape⟩ := exists_cancellation_remainder P hP m s hs hm hdeg hmonic θ
  refine ⟨R.divX,degree_divX_lt_of_natDegree_le R _ hR,?_⟩
  intro x hx hx0
  have he := congrArg (fun Q : F[X] => Q.eval x) hshape
  rw [binaryLocatorCombination_eval_zero P s _ x hx] at he
  simp only [eval_add,eval_mul,eval_C,eval_pow,eval_X] at he
  have hhead : (cancellationSource m s θ).eval x*x=
      (binaryPrefixPolynomial (m+s-1) s (fun j => if j=0 then 1 else θ j)).eval x :=
    eval_divX_mul_of_coeff_zero _
      (binaryPrefixPolynomial_support (m+s-1) s (fun j => if j=0 then 1 else θ j)).coeff_zero x
  apply mul_right_cancel₀ hx0
  rw [eval_divX_mul_of_coeff_zero R hR0 x,add_mul,hhead,mul_assoc,←pow_succ]
  have hpow : 0<(2:ℕ)^(m-1) := by positivity
  rw [show 2^(m-1)-1+1=2^(m-1) by omega]
  exact (CharTwo.add_eq_zero.mp he.symm)
/-- Every prescribed binary subgroup supplies its concrete strict-degree cancellation witness. -/
theorem exists_subspace_cancellation_witness (W : AddSubgroup F) [Fintype W]
    (m s : ℕ) (hs : 1≤s) (hm : s≤m) (hW : Nat.card W=2^m) (θ : ℕ → F) :
    ∃ p : F[X], p.degree<2^(m-2) ∧ ∀ x : F, x∈W → x≠0 →
      (cancellationSource m s θ).eval x+
        cancellationLabel s (locatorPrefix (subspacePolynomial W) m) θ*x^(2^(m-1)-1)=p.eval x := by
  have hd : (subspacePolynomial W).natDegree=2^m := by
    rw [subspacePolynomial_natDegree,←Nat.card_eq_fintype_card,hW]
  obtain ⟨p,hp,he⟩ := exists_cancellation_witness (subspacePolynomial W)
    (subspacePolynomial_support W) m s hs hm hd (subspacePolynomial_monic W) θ
  exact ⟨p,hp,fun x hx hx0 => he x ((subspacePolynomial_eval_eq_zero_iff W x).mpr hx) hx0⟩
/-- The common first input is literally the paper's sum of shifted binary monomials. -/
theorem cancellationSource_eq_sum (m s : ℕ) (θ : ℕ → F) :
    cancellationSource m s θ=
      ∑ j∈Finset.range s, C (if j=0 then 1 else θ j)*X^(2^(m+s-1-j)-1) := by
  change divX_hom (∑ j∈Finset.range s,
    C (if j=0 then 1 else θ j)*X^(2^(m+s-1-j)))=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [divX_X_pow]
/-- The shared first input has its literal leading degree. -/
theorem cancellationSource_natDegree (m s : ℕ) (hs : 1≤s) (hm : 1≤m) (θ : ℕ → F) :
    (cancellationSource m s θ).natDegree=2^(m+s-1)-1 := by
  unfold cancellationSource
  rw [natDegree_divX_eq_natDegree_tsub_one]
  congr 1
  apply natDegree_eq_of_le_of_coeff_ne_zero (binaryPrefixPolynomial_natDegree_le ..)
  have hc := binaryPrefixPolynomial_coeff (m+s-1) s
    (fun j => if j=0 then (1:F) else θ j) (by omega) 0 (by omega)
  simp only [Nat.sub_zero,ite_true] at hc
  rw [hc]
  exact one_ne_zero
/-- The shared first input is monic, independently of the free cancellation parameters. -/
theorem cancellationSource_monic (m s : ℕ) (hs : 1≤s) (hm : 1≤m) (θ : ℕ → F) :
    (cancellationSource m s θ).Monic := by
  unfold Monic leadingCoeff
  rw [cancellationSource_natDegree m s hs hm θ]
  unfold cancellationSource
  rw [coeff_divX]
  have hp : 0<(2:ℕ)^(m+s-1) := by positivity
  rw [show 2^(m+s-1)-1+1=2^(m+s-1) by omega]
  simpa using binaryPrefixPolynomial_coeff (m+s-1) s
    (fun j => if j=0 then (1:F) else θ j) (by omega) 0 (by omega)
end BinaryFieldCounterexamples.AllRatesConstruction
