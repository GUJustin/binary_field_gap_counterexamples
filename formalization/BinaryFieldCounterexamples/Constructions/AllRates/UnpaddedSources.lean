/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.AllRates.LocatorCancellation
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.Witnesses
public import BinaryFieldCounterexamples.Agreement.Domains

/-!
# Exact common agreement before padding

Frobenius remainders on a size-`2^(m-1)` subgroup simultaneously explain all
the sparse input monomials at message length `2^(m-2)`. This
keeps the original low rate, rather than raising the message length to the
direction polynomial's degree as the padding assembly does.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.AllRatesConstruction
open Polynomial Finset

/-- Every Frobenius monomial divided by `X` has a strict-degree representative
on the nonzero points of a subgroup of twice the message length. -/
theorem exists_divided_frobenius_witness
    {F : Type*} [Field F] [CharP F 2]
    (U : AddSubgroup F) [Fintype U] (k j : ℕ)
    (hU : Fintype.card U = 2^(k+1)) :
    ∃ p : F[X], p.degree < 2^k ∧ ∀ x : U, (x:F) ≠ 0 →
      p.eval (x:F) = (x:F)^(2^(k+1+j)-1) := by
  obtain ⟨R, _, hR, hR0, he⟩ := subspacePolynomial_exists_frobenius_remainder U k hU j
  exact ⟨R.divX, degree_divX_lt_of_natDegree_le R _ hR,
    fun x hx ↦ eval_divX_eq_pow_pred R hR0 x hx _ (by positivity) (he x)⟩

/-- The common first input and direction admit simultaneous strict-degree explaining
polynomials on all nonzero points of a size-`2^(m-1)` subgroup, including an arbitrary shift
of the first input. -/
theorem unpadded_common_polynomial_witnesses
    {F : Type*} [Field F] [CharP F 2]
    (U : AddSubgroup F) [Fintype U] (m s : ℕ) (hm : 2 ≤ m)
    (hU : Fintype.card U = 2^(m-1)) (θ : ℕ → F) (τ : F) :
    ∃ p r : F[X], p.degree < 2^(m-2) ∧ r.degree < 2^(m-2) ∧
      ∀ x : U, (x:F) ≠ 0 →
        p.eval (x:F) = (cancellationSource m s θ).eval (x:F) +
          τ*(x:F)^(2^(m-1)-1) ∧
        r.eval (x:F) = (x:F)^(2^(m-1)-1) := by
  classical
  have hU' : Fintype.card U = 2^(m-2+1) := by
    simpa [show m-2+1=m-1 by omega] using hU
  obtain ⟨r, hr, her⟩ := exists_divided_frobenius_witness U (m-2) 0 hU'
  have hex : ∀ j : ℕ, ∃ p : F[X], p.degree < 2^(m-2) ∧
      ∀ x : U, (x:F) ≠ 0 → p.eval (x:F) = (x:F)^(2^(m-2+1+j)-1) :=
    fun j ↦ exists_divided_frobenius_witness U (m-2) j hU'
  choose P hP heP using hex
  let q : F[X] := ∑ j ∈ Finset.range s, C (if j=0 then 1 else θ j)*P (s-j)
  have hq : q.degree < 2^(m-2) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    exact (QuadraticConstruction.degree_C_mul_le _ _).trans_lt (hP _)
  have her' : ∀ x : U, (x:F) ≠ 0 → r.eval (x:F) = (x:F)^(2^(m-1)-1) := by
    simpa [show m-2+1=m-1 by omega] using her
  refine ⟨q+C τ*r, r, (degree_add_le _ _).trans_lt
    (max_lt hq ((QuadraticConstruction.degree_C_mul_le _ _).trans_lt hr)), hr, ?_⟩
  intro x hx
  have heq : q.eval (x:F) = (cancellationSource m s θ).eval (x:F) := by
    rw [cancellationSource_eq_sum]
    simp only [q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    apply Finset.sum_congr rfl
    intro j hj
    rw [heP _ x hx]
    have hj' := Finset.mem_range.mp hj
    rw [show m-2+1+(s-j) = m+s-1-j by omega]
  simp only [eval_add, eval_mul, eval_C, heq, her' x hx, and_self]

/-- A concrete subgroup of the supplied domain attains the claimed common
agreement. The two explaining polynomials agree on the same nonzero coordinates. -/
theorem unpadded_commonAgreementGE
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (E : Finset F) (U : AddSubgroup F) (hUE : ∀ x ∈ U, x ∈ E)
    (m s : ℕ) (hm : 2 ≤ m) (hU : Nat.card U = 2^(m-1))
    (θ : ℕ → F) (τ : F) :
    commonAgreementGE E (2^(m-2))
      (fun x ↦ (cancellationSource m s θ).eval (x:F)+τ*(x:F)^(2^(m-1)-1))
      (fun x ↦ (x:F)^(2^(m-1)-1)) (2^(m-1)-1) := by
  classical
  obtain ⟨p,r,hp,hr,he⟩ := unpadded_common_polynomial_witnesses U m s hm
    (by simpa only [Nat.card_eq_fintype_card] using hU) θ τ
  refine ⟨p,r,hp,hr,?_⟩
  rw [QuadraticConstruction.commonAgreementCount_eq_card_filter E
    (fun x : F ↦ (cancellationSource m s θ).eval x+τ*x^(2^(m-1)-1))
    (fun x : F ↦ x^(2^(m-1)-1)) p r]
  have hucard : (additiveDomain U).card = 2^(m-1) := by
    rw [card_additiveDomain, hU]
  have hz : (0:F) ∈ additiveDomain U := by simp [additiveDomain]
  calc
    2^(m-1)-1 = ((additiveDomain U).erase 0).card := by
      rw [Finset.card_erase_of_mem hz, hucard]
    _ ≤ _ := Finset.card_le_card (by
      intro x hx
      obtain ⟨hx0,hxU⟩ := Finset.mem_erase.mp hx
      have hmem : x ∈ U := (mem_additiveDomain U x).mp hxU
      exact Finset.mem_filter.mpr ⟨hUE x hmem, he ⟨x,hmem⟩ hx0⟩)

end BinaryFieldCounterexamples.AllRatesConstruction
