/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.LocatorRemainders

/-!
# Binary locator coefficient elimination

Literal Frobenius combinations have a triangular coefficient system. Removing
an initial binary prefix leaves the precise next power-of-two degree gap.
These helpers apply to the actual locator polynomials, not just their functions.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.AllRatesConstruction
open Polynomial BinaryLocator
variable {F : Type*} [Field F] [CharP F 2]
set_option linter.unusedSectionVars false

/-- A coefficient under iterated binary Frobenius, at its literal expanded degree. -/
theorem coeff_pow_two_pow (P : F[X]) (r k : ℕ) :
    (P^(2^r)).coeff (2^(r+k))=(P.coeff (2^k))^(2^r) := by
  rw [←map_iterateFrobenius_expand 2 P r,coeff_map,pow_add,
    coeff_expand_mul' (by positivity : 0<(2:ℕ)^r)]
  rfl
/-- Iterated binary Frobenius preserves actual power-of-two support. -/
theorem binarySupport_pow_two_pow (P : F[X]) (hP : IsBinaryLinearized P) (r : ℕ) :
    IsBinaryLinearized (P^(2^r)) := by
  induction r with
  | zero => simpa using hP
  | succ r ih =>
    rw [pow_succ,pow_mul]
    exact is_binary_linearized_sq _ ih
/-- Finite sums preserve actual binary coefficient support. -/
theorem binarySupport_sum {ι : Type*} (S : Finset ι) (P : ι → F[X])
    (hP : ∀ i∈S, IsBinaryLinearized (P i)) : IsBinaryLinearized (∑ i∈S, P i) := by
  intro n hn
  have hc : (∑ i∈S, (P i).coeff n)≠0 := by
    simpa only [finsetSum_coeff] using mem_support_iff.mp hn
  obtain ⟨i,hi,hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  exact hP i hi n (mem_support_iff.mpr hci)
/-- The actual Frobenius combination used to cancel the leading locator coefficients. -/
noncomputable def binaryLocatorCombination (P : F[X]) (s : ℕ) (b : ℕ → F) : F[X] :=
  ∑ i∈Finset.range s, C (b i)*P^(2^(s-1-i))
/-- The literal combination still has binary support. -/
theorem binaryLocatorCombination_support (P : F[X]) (hP : IsBinaryLinearized P)
    (s : ℕ) (b : ℕ → F) : IsBinaryLinearized (binaryLocatorCombination P s b) := by
  apply binarySupport_sum
  intro i hi
  exact is_binary_linearized_c_mul _ _ (binarySupport_pow_two_pow P hP _)
/-- The combination degree is at most its first Frobenius term's degree. -/
theorem binaryLocatorCombination_natDegree_le (P : F[X]) (m s : ℕ)
    (hs : 1≤s) (hdeg : P.natDegree=2^m) (b : ℕ → F) :
    (binaryLocatorCombination P s b).natDegree≤2^(m+s-1) := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_pow,hdeg,←pow_add]
  apply Nat.pow_le_pow_right (by decide : 1≤(2:ℕ))
  omega
/-- Each summand has the triangular leading-coefficient pattern dictated by its Frobenius shift. -/
theorem binaryLocatorCombination_term_coeff (P : F[X]) (m s i j : ℕ)
    (hs : 1≤s) (hm : s≤m) (hi : i<s) (hj : j≤s) (hdeg : P.natDegree=2^m) :
    (P^(2^(s-1-i))).coeff (2^(m+s-1-j))=
      if i≤j then (P.coeff (2^(m-(j-i))))^(2^(s-1-i)) else 0 := by
  by_cases hij : i≤j
  · rw [ite_eq_left hij]
    have he : m+s-1-j=(s-1-i)+(m-(j-i)) := by omega
    rw [he,coeff_pow_two_pow]
  · rw [ite_eq_right hij]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_pow,hdeg,←pow_add]
    apply Nat.pow_lt_pow_right (by decide : 1<(2:ℕ))
    omega
/-- A prescribed finite prefix in the actual sparse polynomial basis. -/
noncomputable def binaryPrefixPolynomial (N s : ℕ) (c : ℕ → F) : F[X] :=
  ∑ j∈Finset.range s, C (c j)*X^(2^(N-j))
/-- The finite sparse prefix has binary support. -/
theorem binaryPrefixPolynomial_support (N s : ℕ) (c : ℕ → F) :
    IsBinaryLinearized (binaryPrefixPolynomial N s c) := by
  apply binarySupport_sum
  intro j hj
  exact is_binary_linearized_c_mul _ _
    (binarySupport_pow_two_pow X is_binary_linearized_x _)
/-- No term of the sparse prefix exceeds its initial degree. -/
theorem binaryPrefixPolynomial_natDegree_le (N s : ℕ) (c : ℕ → F) :
    (binaryPrefixPolynomial N s c).natDegree≤2^N := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_X_pow]
  exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
/-- Distinct prefix positions recover their literal coefficients. -/
theorem binaryPrefixPolynomial_coeff (N s : ℕ) (c : ℕ → F)
    (hs : s≤N+1) (j : ℕ) (hj : j<s) :
    (binaryPrefixPolynomial N s c).coeff (2^(N-j))=c j := by
  classical
  unfold binaryPrefixPolynomial
  rw [finsetSum_coeff,Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    have hi' : i<s := Finset.mem_range.mp hi
    have he : 2^(N-i)≠(2:ℕ)^(N-j) := by
      intro he
      have := (Nat.pow_right_injective (by decide : 1<(2:ℕ))) he
      omega
    simp [coeff_C_mul,coeff_X_pow,Ne.symm he]
  · simp [Finset.mem_range.mpr hj]
/-- Removing a complete leading binary prefix leaves the next strict coefficient gap. -/
theorem binaryPrefix_remainder (P : F[X]) (hP : IsBinaryLinearized P)
    (N s : ℕ) (hs : s≤N) (hdeg : P.natDegree≤2^N) :
    (P-binaryPrefixPolynomial N (s+1) (fun j => P.coeff (2^(N-j)))).natDegree
      ≤2^(N-s-1) ∧
    (P-binaryPrefixPolynomial N (s+1) (fun j => P.coeff (2^(N-j)))).coeff 0=0 := by
  let R := P-binaryPrefixPolynomial N (s+1) (fun j => P.coeff (2^(N-j)))
  have hR : IsBinaryLinearized R :=
    is_binary_linearized_sub _ _ hP (binaryPrefixPolynomial_support N (s+1) (fun j => P.coeff (2^(N-j))))
  refine ⟨?_,hR.coeff_zero⟩
  by_cases hz : R=0
  · change R.natDegree≤_
    simp [hz]
  have hc : R.coeff R.natDegree≠0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hz
  obtain ⟨i,hi⟩ := hR _ (mem_support_iff.mpr hc)
  have hd : R.natDegree≤2^N :=
    (natDegree_sub_le _ _).trans (max_le hdeg (binaryPrefixPolynomial_natDegree_le ..))
  have hiN : i≤N := by
    rw [hi] at hd
    exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hd
  have his : i<N-s := by
    by_contra h
    apply hc
    change (P-binaryPrefixPolynomial N (s+1) (fun j => P.coeff (2^(N-j)))).coeff _=0
    rw [hi,coeff_sub]
    have hj : N-i<s+1 := by omega
    have hcoeff := binaryPrefixPolynomial_coeff N (s+1)
      (fun j => P.coeff (2^(N-j))) (by omega) (N-i) hj
    rw [show N-(N-i)=i by omega] at hcoeff
    rw [hcoeff,sub_self]
  change R.natDegree≤_
  rw [hi]
  exact Nat.pow_le_pow_right (by decide) (by omega)
/-- The combination has exactly the triangular coefficient sum at every leading position. -/
theorem binaryLocatorCombination_coeff (P : F[X]) (m s j : ℕ)
    (hs : 1≤s) (hm : s≤m) (hj : j≤s) (hdeg : P.natDegree=2^m)
    (b : ℕ → F) :
    (binaryLocatorCombination P s b).coeff (2^(m+s-1-j))=
      ∑ i∈Finset.range s, if i≤j then
        b i*(P.coeff (2^(m-(j-i))))^(2^(s-1-i)) else 0 := by
  unfold binaryLocatorCombination
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_C_mul,binaryLocatorCombination_term_coeff P m s i j hs hm
    (Finset.mem_range.mp hi) hj hdeg]
  split_ifs <;> simp
/-- Every actual root of the locator is a root of the full Frobenius combination. -/
theorem binaryLocatorCombination_eval_zero (P : F[X]) (s : ℕ) (b : ℕ → F)
    (x : F) (hx : P.eval x=0) : (binaryLocatorCombination P s b).eval x=0 := by
  simp [binaryLocatorCombination,eval_finsetSum,hx]
end BinaryFieldCounterexamples.AllRatesConstruction
