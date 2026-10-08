/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Projection
public import BinaryFieldCounterexamples.Agreement.Domains
public import BinaryFieldCounterexamples.Polynomial.LocatorRemainders
public import Mathlib.Algebra.CharP.Reduced

/-!
# The first-input bound for the proper-extension construction

The two base-field projections of a hypothetical close polynomial imply a
low-degree identity. Squaring that identity cancels the three leading terms of
the domain locator. The resulting low-degree polynomial cannot have too many
roots because its derivative is the nonzero locator derivative.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- Multiplication by `X` converts a strict message bound into a weak bound,
including a zero explaining polynomial. -/
theorem natDegree_X_mul_le_of_degree_lt
    {B : Type*} [Field B] (p : B[X]) (K : ℕ) (hp : p.degree < K) :
    (X * p).natDegree ≤ K := by
  by_cases hz : p = 0
  · simp [hz]
  rw [natDegree_X_mul hz]
  have h := (natDegree_lt_iff_degree_lt hz).mpr hp
  omega

/-- The projected algebraic obstruction. The hypotheses are actual evaluation
equations for two polynomials of degree at most `K`, not agreement assumptions. -/
theorem quadratic_projected_root_bound
    {B : Type*} [Field B] [CharP B 2] [DecidableEq B]
    (S : Finset B) (K : ℕ) (L V A Q : B[X]) (a d s : B)
    (hshape : L = X ^ (16 * K) + C a * X ^ (8 * K) + C d * X ^ (4 * K) + V)
    (hV : V.natDegree ≤ 2 * K) (hA : A.natDegree ≤ K) (hQ : Q.natDegree ≤ K)
    (hs : s ^ 2 = d) (hderiv : derivative L ≠ 0)
    (hroots : ∀ x ∈ S, L.eval x = 0)
    (hproj0 : ∀ x ∈ S, A.eval x = x ^ (8 * K) + s * x ^ (2 * K))
    (hproj1 : ∀ x ∈ S, Q.eval x = x ^ (4 * K)) :
    S.card ≤ 2 * K := by
  classical
  by_contra hbound
  have hlarge : 2 * K < S.card := by omega
  have root_force : ∀ R : B[X], R.natDegree ≤ 2 * K →
      (∀ x ∈ S, R.eval x = 0) → R = 0 := by
    intro R hdeg hr
    by_contra hn
    have heq : S.filter (fun x ↦ R.eval x = 0) = S := by
      exact Finset.filter_eq_self.mpr hr
    have hc := card_filter_eval_eq_zero_le S R hn
    rw [heq] at hc
    omega

  -- Eliminate the eighth-power term using the two coordinate equations.
  let H : B[X] := Q ^ 2 + A + C s * X ^ (2 * K)
  have hHdeg : H.natDegree ≤ 2 * K := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      exact max_le ((natDegree_pow_le).trans (by omega)) (by omega)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  have hH : H = 0 := by
    apply root_force H hHdeg
    intro x hx
    simp only [H, eval_add, eval_pow, eval_mul, eval_C, eval_X,
      hproj0 x hx, hproj1 x hx]
    rw [← pow_mul]
    have he : 4 * K * 2 = 8 * K := by omega
    rw [he]
    simp [add_assoc, CharTwo.add_self_eq_zero]
  have hQs : Q ^ 2 = A + C s * X ^ (2 * K) := by
    have h : Q ^ 2 + (A + C s * X ^ (2 * K)) = 0 := by
      simpa [H, add_assoc] using hH
    exact CharTwo.add_eq_zero.mp h

  -- Squaring the identity cancels the domain locator's three leading terms.
  let P : B[X] := X ^ (4 * K) + Q
  let R : B[X] := L + P ^ 4 + C a * P ^ 2
  have hP2 : P ^ 2 = X ^ (8 * K) + Q ^ 2 := by
    simp only [P, CharTwo.add_sq, ← pow_mul]
    congr 2
    omega
  have hP4 : P ^ 4 = X ^ (16 * K) + A ^ 2 + C d * X ^ (4 * K) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hP2, CharTwo.add_sq, hQs,
      CharTwo.add_sq, mul_pow, ← map_pow, hs]
    simp only [← pow_mul]
    have h8 : 8 * K * 2 = 16 * K := by omega
    have h2 : 2 * K * 2 = 4 * K := by omega
    rw [h8, h2]
    ac_rfl
  have hRform : R = V + A ^ 2 + C a * Q ^ 2 := by
    simp only [R, hshape, hP4, hP2, mul_add]
    ring_nf
    simp [CharTwo.two_eq_zero]
  have hRdeg : R.natDegree ≤ 2 * K := by
    rw [hRform]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_add_le _ _).trans
        (max_le hV ((natDegree_pow_le).trans (by omega)))
    · exact (natDegree_C_mul_le _ _).trans
        ((natDegree_pow_le).trans (by omega))
  have hR : R = 0 := by
    apply root_force R hRdeg
    intro x hx
    have hp : P.eval x = 0 := by
      simp [P, hproj1 x hx, CharTwo.add_self_eq_zero]
    simp [R, hroots x hx, hp]
  apply hderiv
  have hd := congrArg derivative hR
  have h4 : (4 : B) = 0 := by
    calc
      (4 : B) = 2 + 2 := by norm_num
      _ = 0 := by simp [CharTwo.two_eq_zero]
  simpa [R, derivative_add, derivative_mul, derivative_pow,
    CharTwo.two_eq_zero, h4] using hd

/-- A base-linear functional commutes with multiplication by embedded scalars. -/
theorem linearMap_apply_algebraMap_mul
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (l : F →ₗ[B] B) (a : B) (b : F) :
    l (algebraMap B F a * b) = a * l b := by
  simpa [Algebra.smul_def] using l.map_smul a b

/-- Projecting an extension-field explaining polynomial yields the root obstruction above.
The finite set is an arbitrary base-field evaluation domain with the supplied
literal locator identity and nonzero derivative. -/
theorem quadratic_shifted_source_filter_card_le
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    [CharP B 2] [CharP F 2] [DecidableEq B] [DecidableEq F]
    (D : Finset B) (K : ℕ) (hK : 0 < K) (L V : B[X]) (a d s : B)
    (hshape : L = X ^ (16 * K) + C a * X ^ (8 * K) + C d * X ^ (4 * K) + V)
    (hV : V.natDegree ≤ 2 * K) (hs : s ^ 2 = d) (hderiv : derivative L ≠ 0)
    (hroots : ∀ x ∈ D, L.eval x = 0)
    (θ : F) (hθ : θ ∉ Set.range (algebraMap B F))
    (p : F[X]) (hp : p.degree < K) :
    (D.filter fun x ↦ p.eval (algebraMap B F x) =
      (algebraMap B F x) ^ (8 * K - 1) + θ * (algebraMap B F x) ^ (4 * K - 1) +
        algebraMap B F s * (algebraMap B F x) ^ (2 * K - 1)).card ≤ 2 * K := by
  classical
  obtain ⟨l0, l1, hl01, hl0θ, hl11, hl1θ⟩ := exists_extension_coordinates θ hθ
  obtain ⟨p0, hp0, he0⟩ := exists_projected_polynomial l0 K p hp
  obtain ⟨p1, hp1, he1⟩ := exists_projected_polynomial l1 K p hp
  have hl0 (b : B) : l0 (algebraMap B F b) = b := by
    simpa [hl01] using linearMap_apply_algebraMap_mul l0 b 1
  have hl1 (b : B) : l1 (algebraMap B F b) = 0 := by
    simpa [hl11] using linearMap_apply_algebraMap_mul l1 b 1
  have pow_cancel (x : B) (n : ℕ) (hn : 0 < n) : x * x ^ (n - 1) = x ^ n := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  apply quadratic_projected_root_bound _ K L V (X * p0) (X * p1) a d s hshape hV
    (natDegree_X_mul_le_of_degree_lt p0 K hp0)
    (natDegree_X_mul_le_of_degree_lt p1 K hp1) hs hderiv
  · intro x hx
    exact hroots x (Finset.mem_filter.mp hx).1
  · intro x hx
    have he := (Finset.mem_filter.mp hx).2
    rw [eval_mul, eval_X, he0, he]
    simp only [map_add, ← map_pow, ← map_mul, hl0]
    rw [mul_comm θ, linearMap_apply_algebraMap_mul, hl0θ, mul_zero, add_zero,
      mul_add, pow_cancel x (8 * K) (by omega)]
    rw [← mul_assoc, mul_comm x s, mul_assoc, pow_cancel x (2 * K) (by omega)]
  · intro x hx
    have he := (Finset.mem_filter.mp hx).2
    rw [eval_mul, eval_X, he1, he]
    simp only [map_add, ← map_pow, ← map_mul, hl1, zero_add, add_zero]
    rw [mul_comm θ, linearMap_apply_algebraMap_mul, hl1θ, mul_one,
      pow_cancel x (4 * K) (by omega)]

/-- On every prescribed binary additive domain of size `16K`, one base-field
shift makes the first input have agreement at most `2K`. The shift is chosen
once, independently of the explaining polynomial and of all challenges. -/
theorem exists_quadratic_source_shift
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [CharP F 2] [Algebra B F]
    (D : AddSubgroup B) (K : ℕ) (hK : 0 < K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 16 * K)
    (θ : F) (hθ : θ ∉ Set.range (algebraMap B F)) :
    ∃ s : B,
      agreementLE (mappedDomain (algebraMap B F) (additiveDomain D)) K
        (fun x ↦ (x : F) ^ (8 * K - 1) + θ * (x : F) ^ (4 * K - 1) +
          algebraMap B F s * (x : F) ^ (2 * K - 1)) (2 * K) := by
  classical
  let : Fintype D := Fintype.ofFinite D
  obtain ⟨k, hk⟩ := hpow
  have hc : Fintype.card D = 16 * K := by
    simpa [card_additiveDomain, Nat.card_eq_fintype_card] using hD
  have h16 : 2 ^ (k + 1 + 3) = 16 * K := by simp [hk, pow_add]; ring
  have h8 : 2 ^ (k + 1 + 2) = 8 * K := by simp [hk, pow_add]; ring
  have h4 : 2 ^ (k + 1 + 1) = 4 * K := by simp [hk, pow_add]; ring
  have h2 : 2 ^ (k + 1) = 2 * K := by simp [hk, pow_add]; ring
  obtain ⟨V, hV, _, hshape⟩ := subspacePolynomial_three_term_shape D (k + 1) (hc.trans h16.symm)
  rw [h16, h8, h4] at hshape
  rw [h2] at hV
  let L := subspacePolynomial D
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (L.coeff (4 * K))
  have hs2 : s ^ 2 = L.coeff (4 * K) := by simpa [pow_two] using hs.symm
  have hderiv : derivative L ≠ 0 := by
    intro hz
    apply subspacePolynomial_coeff_one_ne_zero D
    have he := congrArg (fun Q : B[X] ↦ Q.coeff 0) hz
    simpa [L, coeff_derivative] using he
  refine ⟨s, ?_⟩
  intro p hp
  rw [agreementCount_mappedDomain (algebraMap B F) (additiveDomain D)
    (fun x ↦ x ^ (8 * K - 1) + θ * x ^ (4 * K - 1) +
      algebraMap B F s * x ^ (2 * K - 1)) p]
  apply quadratic_shifted_source_filter_card_le (additiveDomain D) K hK L V
    (L.coeff (8 * K)) (L.coeff (4 * K)) s hshape hV hs2 hderiv
    ?_ θ hθ p hp
  intro x hx
  exact (subspacePolynomial_eval_eq_zero_iff D x).mpr ((mem_additiveDomain D x).mp hx)

end BinaryFieldCounterexamples
