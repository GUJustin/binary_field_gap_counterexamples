/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.QuadraticFactorExistence
/-!
# Exact factor degrees and strict quadratic corrections

The literal factorizations and exact function/derivative degrees determine all
factor degrees. A converted locator has a strict-degree correction to the
canonical numerator whenever its quotient has the required smaller degree.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial

/-- Exact degrees of the Frobenius factor, converted locator, and derivative quotient. -/
theorem quadratic_factor_degrees {F : Type*} [Field F]
    (q m t : ℕ) (hq : 2≤q) (ht : 1≤t) (hm : 2*t≤m)
    (G J A P S : F[X]) (lam : F) (hlam : lam≠0) (hA : A≠0)
    (hG : G=A*P) (hJ : J= -C lam*A^q) (hS : G=J*S)
    (hdG : G.natDegree=q^(m-1)+q^(m-t-1)) (hdJ : J.natDegree=q^(m-t)) :
    A.natDegree=q^(m-t-1) ∧ P.natDegree=q^(m-1) ∧
      S.natDegree=q^(m-1)-(q-1)*q^(m-t-1) := by
  have hJ0 : J≠0 := by rw [hJ]; exact mul_ne_zero (neg_ne_zero.mpr (C_ne_zero.mpr hlam)) (pow_ne_zero _ hA)
  have hG0 : G≠0 := by
    intro hz
    rw [hz,natDegree_zero] at hdG
    have hpos := pow_pos (by omega : 0<q) (m-1)
    omega
  have hP0 : P≠0 := by intro hz; rw [hG,hz,mul_zero] at hG0; exact hG0 rfl
  have hS0 : S≠0 := by intro hz; rw [hS,hz,mul_zero] at hG0; exact hG0 rfl
  have he : q*q^(m-t-1)=q^(m-t) := by rw [←pow_succ']; congr 1; omega
  have hdegA : A.natDegree=q^(m-t-1) := by
    rw [hJ,natDegree_mul (neg_ne_zero.mpr (C_ne_zero.mpr hlam)) (pow_ne_zero _ hA),
      natDegree_neg,natDegree_C,zero_add,natDegree_pow,←he] at hdJ
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0<q) hdJ
  have hp := congrArg natDegree hG
  rw [hdG,natDegree_mul hA hP0,hdegA] at hp
  have hdegP : P.natDegree=q^(m-1) := by omega
  have hs := congrArg natDegree hS
  rw [hdG,natDegree_mul hJ0 hS0,hdJ,←he] at hs
  have hqm : q-1+1=q := by omega
  have hmul := congrArg (fun z : ℕ => z*q^(m-t-1)) hqm
  simp only [Nat.add_mul,one_mul] at hmul
  exact ⟨hdegA,hdegP,by omega⟩

/-- The actual conversion identity gives a strict-degree correction to the canonical numerator. -/
theorem converted_quadratic_strict_correction {F : Type*} [Field F] [Fintype F]
    (p r : ℕ) [Fact p.Prime] [CharP F p] (hr : 1≤r)
    (P S L : F[X]) (β : F) (K : ℕ) (hK : 0<K)
    (hs : ∀ e∈L.support,∃ i : ℕ,e=(p^r)^i)
    (hP : P^(p^r)=L-C (L.coeff 1)*S) (hS : S.natDegree<p^r*K) :
    ∃ U : F[X],P=primePowerQuarterNumerator p r L β+U ∧ U.degree<K := by
  have hq : 2≤p^r := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  apply QuadraticLocatorConversion.exists_strict_common_head_correction P
    (primePowerQuarterNumerator p r L β) S L (C (L.coeff 1)*(X-C β)) (L.coeff 1) p r K hP
  · exact primePowerQuarterNumerator_pow p r hr L β hs
  · apply (natDegree_sub_le _ _).trans_lt
    apply max_lt
    · apply (natDegree_C_mul_le _ _).trans_lt
      rw [natDegree_X_sub_C]
      nlinarith
    · exact (natDegree_C_mul_le _ _).trans_lt hS
end BinaryFieldCounterexamples
