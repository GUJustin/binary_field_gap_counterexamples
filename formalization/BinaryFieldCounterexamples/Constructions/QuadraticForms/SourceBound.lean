/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Basic
public import BinaryFieldCounterexamples.Polynomial.DoubleRoots
public import Mathlib.Algebra.CharP.Lemmas
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.Numerator
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The prime-power quarter-rate first-input bound

The numerator of the first input of Lemma 3.13, with the stated Frobenius identity,
has the paper's half-integral first-input bound. The concrete locator and numerator must
still supply that identity; no quadratic-form population is assumed here.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial

/-- The Wronskian bound for the prime-power first input of Lemma 3.13. The integer bound
keeps the rounding required in odd characteristic. -/
theorem agreementLE_primePowerQuarterSource_of_power
    {F : Type*} [Field F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1≤r) (D : Finset F) (β : F) (hβ : β∉D)
    (K : ℕ) (hK : 2≤K) (hKchar : (K:F)=0)
    (L S : F[X]) (lam : F) (hlam : lam≠0)
    (hroots : ∀x∈D, L.eval x=0) (hLβ : L.eval β≠0)
    (hSpow : S^(p^r)=L-C lam*(X-C β))
    (hSdeg : S.natDegree≤p^r*K) (hS'deg : S.derivative.natDegree≤0) :
    agreementLE D K (fun x => S.eval (x:F)*((x:F)-β)⁻¹) (((p^r+1)*K-2)/2) := by
  classical
  let b := p^r
  have hb : 2≤b := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  have hb0 : 0<b := by omega
  have hbchar : (b:F)=0 := by simp [b,Nat.cast_pow,show r≠0 by omega]
  intro h hh
  have hhnat : h.natDegree ≤ K - 1 := by
    by_cases hz : h = 0
    · simp [hz]
    have := (natDegree_lt_iff_degree_lt hz).mpr hh
    omega
  let A := (X - C β) * h
  let P := S - A
  let Q := P ^ b - L
  let roots := D.filter fun x ↦
    h.eval x = S.eval x * (x - β)⁻¹
  rw [agreementCount_eq_card_filter D
    (fun x ↦ S.eval x * (x - β)⁻¹) h]
  have hAdeg : A.natDegree ≤ K := by
    calc
      A.natDegree ≤ (X - C β).natDegree + h.natDegree := natDegree_mul_le
      _ ≤ 1 + (K - 1) := Nat.add_le_add (by simp) hhnat
      _ ≤ K := by omega
  have hPdeg : P.natDegree ≤ b * K :=
    (natDegree_sub_le _ _).trans (max_le hSdeg (hAdeg.trans (by nlinarith)))
  have hderivA : A.derivative.natDegree ≤ K - 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_derivative]
    by_cases htop : n + 1 = K
    · have hcast : ((n + 1 : ℕ) : F) = 0 := by rw [htop, hKchar]
      have hcast' : (n : F) + 1 = 0 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hcast
      rw [hcast', mul_zero]
    · have hgt : K < n + 1 := by omega
      have hc : A.coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt (hAdeg.trans_lt hgt)
      rw [hc, zero_mul]
  have hP'deg : P.derivative.natDegree ≤ K - 2 := by
    simp only [P, derivative_sub]
    exact (natDegree_sub_le _ _).trans (max_le
      (hS'deg.trans (by omega)) hderivA)
  have hQform : Q = -A ^ b - C lam * (X - C β) := by
    dsimp only [Q,P,b]
    rw [sub_pow_char_pow,hSpow]
    ring
  have hQdeg : Q.natDegree ≤ b * K := by
    rw [hQform]
    exact (natDegree_sub_le _ _).trans (max_le
      (by simpa only [natDegree_neg] using (natDegree_pow_le.trans (Nat.mul_le_mul_left b hAdeg)))
      ((natDegree_mul_le).trans (by simp; nlinarith)))
  have hQ' : Q.derivative = -C lam := by
    rw [hQform]
    simp [derivative_pow,hbchar]
  have hQβ : Q.eval β = 0 := by simp [hQform,A,show b≠0 by omega]
  have hPβ : P.eval β ≠ 0 := by
    have hSβpow : S.eval β ^ b = L.eval β := by
      have he := congrArg (Polynomial.eval β) hSpow
      simpa only [eval_pow,eval_sub,eval_mul,eval_C,eval_X,sub_self,mul_zero,sub_zero,b] using he
    have hSβ : S.eval β≠0 := fun hz => hLβ (by simpa [hz,show b≠0 by omega] using hSβpow.symm)
    simpa [P,A] using hSβ
  have hroot : ∀ x ∈ roots, P.eval x = 0 ∧ Q.eval x = 0 := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxD, hxagree⟩
    have hxβ : x - β ≠ 0 := sub_ne_zero.mpr (fun he ↦ hβ (he ▸ hxD))
    have hPzero : P.eval x = 0 := by
      simp only [P, A, eval_sub, eval_mul, eval_X, eval_C]
      field_simp at hxagree
      linear_combination -hxagree
    refine ⟨hPzero, ?_⟩
    simp [Q,hPzero,hroots x hxD,show b≠0 by omega]
  have htwice := twice_card_le_of_wronskian roots P Q lam β hlam hQ' hQβ hPβ
    hroot (b * K) (K - 2) (b * K) hPdeg hP'deg hQdeg
  change roots.card ≤ ((b+1)*K-2)/2
  have hbk : (b+1)*K=b*K+K := by ring
  omega

/-- The explicit inverse-Frobenius numerator satisfies the first-input bound of Lemma 3.13. -/
theorem agreementLE_primePowerQuarterNumerator
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (D : Finset F) (β : F) (hβ : β ∉ D)
    (K : ℕ) (hK : 2 ≤ K) (hKchar : (K : F) = 0)
    (L : F[X]) (hcoeff : L.coeff 1 ≠ 0)
    (hroots : ∀ x ∈ D, L.eval x = 0) (hLβ : L.eval β ≠ 0)
    (hs : ∀ n ∈ L.support, ∃ i : ℕ, n = (p^r)^i)
    (hLdeg : L.natDegree ≤ (p^r)^2*K) :
    agreementLE D K
      (fun x => (primePowerQuarterNumerator p r L β).eval (x:F) * ((x:F)-β)⁻¹)
      (((p^r+1)*K-2)/2) := by
  apply agreementLE_primePowerQuarterSource_of_power p r hr D β hβ K hK hKchar L
    (primePowerQuarterNumerator p r L β) (L.coeff 1) hcoeff hroots hLβ
  · exact primePowerQuarterNumerator_pow p r hr L β hs
  · exact primePowerQuarterNumerator_natDegree_le p r hr L β hs K (by omega) hLdeg
  · rw [primePowerQuarterNumerator_derivative p r hr L β hs]
    simp

/-- The integer Wronskian bound is exactly the paper's rational floor when `N=b²K`. -/
theorem primePowerQuarterSource_floor (b K N : ℕ) (hb : 2 ≤ b) (hK : 2 ≤ K)
    (hN : N = b^2*K) :
    ⌊((b+1 : ℚ)*N/(2*b^2)-1)⌋₊ = ((b+1)*K-2)/2 := by
  have hbk : 2 ≤ (b+1)*K := by nlinarith
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have heq : ((b+1 : ℚ)*N/(2*b^2)-1) = (((b+1)*K-2 : ℕ) : ℚ)/2 := by
    rw [hN, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hbk]
    push_cast
    field_simp
  rw [heq, Nat.floor_div_ofNat]
  simp


end BinaryFieldCounterexamples
