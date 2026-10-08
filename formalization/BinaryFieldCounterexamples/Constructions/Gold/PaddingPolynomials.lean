/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.PoleReduction
public import BinaryFieldCounterexamples.Agreement.Interpolation
/-!
# Polynomial locator padding and exact common agreement

Multiplication by the padding locator raises every witness degree by at most
its degree and replaces the actual agreement set by its union with the locator
roots. The kept nonzero challenges therefore remain distinct and exceptional at the
new strict degree bound.

A polynomial numerator nonzero at an excluded pole has agreement at most the
message length whenever its degree is at most that length. Interpolation
attains this bound, giving exact second-input and common agreement for the
padded pole pair. The more refined first-input bound is a separate obligation.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq
/-- Multiplying a strict-degree message by a bounded-degree locator preserves the required strict padded bound. -/
theorem padding_witness_degree {F : Type*} [Field F]
    (A p : F[X]) (K s : ℕ) (hA : A.natDegree≤s) (hp : p.degree<K) :
    (A*p).degree<K+s := by
  by_cases hz : p=0
  · subst p; simp
  have hp' : p.natDegree<K := (natDegree_lt_iff_degree_lt hz).mpr hp
  have hn : (A*p).natDegree<K+s := by
    have hm : (A*p).natDegree≤A.natDegree+p.natDegree := natDegree_mul_le
    omega
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hn)
/-- Polynomial multiplication replaces the exact agreement set by its union with the locator roots. -/
theorem agreementCount_padding_union {F : Type*} [Field F]
    (D : Finset F) (w : D → F) (A p : F[X]) :
    agreementCount D (fun x => A.eval (x:F)*w x) (A*p)=
      ((Finset.univ.filter fun x : D => A.eval (x:F)=0) ∪
        (Finset.univ.filter fun x : D => w x=p.eval (x:F))).card := by
  unfold agreementCount Code.agree
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,eval_mul]
  constructor
  · intro h
    by_cases hz : A.eval (x:F)=0
    · exact Or.inl hz
    · exact Or.inr (mul_left_cancel₀ hz h)
  · rintro (hz | he)
    · rw [hz]; simp
    · rw [he]
/-- A numerator nonzero at the excluded pole gives the exact same degree root bound as a
reciprocal second input. -/
theorem agreementLE_polynomialOverPole {F : Type*} [Field F]
    (D : Finset F) (β : F) (hβ : β ∉ D) (A : F[X]) (K : ℕ)
    (hA : A.natDegree≤K) (hAβ : A.eval β≠0) :
    agreementLE D K (fun x => A.eval (x:F)/((x:F)-β)) K := by
  classical
  intro p hp
  let R := (X-C β)*p-A
  have hR : R≠0 := by
    intro hz
    have he := congrArg (Polynomial.eval β) hz
    apply hAβ
    simpa [R] using he
  have hdeg : R.natDegree≤K := by
    apply (natDegree_sub_le _ _).trans
    apply max_le _ hA
    by_cases hz : p=0
    · simp [hz]
    · have hp' : p.natDegree<K := (natDegree_lt_iff_degree_lt hz).mpr hp
      apply natDegree_mul_le.trans
      rw [natDegree_X_sub_C]
      omega
  rw [agreementCount_eq_card_filter D (fun x => A.eval x/(x-β)) p]
  apply (Finset.card_le_card (show (D.filter fun x => p.eval x=A.eval x/(x-β)) ⊆
      D.filter fun x => R.eval x=0 from ?_)).trans
    ((card_filter_eval_eq_zero_le D R hR).trans hdeg)
  intro x hx
  obtain ⟨hxD,hxp⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxD,?_⟩
  have hxβ : x-β≠0 := sub_ne_zero.mpr (fun h => hβ (h ▸ hxD))
  have he := (eq_div_iff hxβ).mp hxp
  simp only [R,eval_sub,eval_mul,eval_X,eval_C]
  rw [mul_comm,he,sub_self]
/-- Interpolation and the pole obstruction give exact individual agreement after padding. -/
theorem agreementEQ_polynomialOverPole {F : Type*} [Field F]
    (D : Finset F) (β : F) (hβ : β ∉ D) (A : F[X]) (K : ℕ)
    (hA : A.natDegree≤K) (hAβ : A.eval β≠0) (hK : K≤D.card) :
    agreementEQ D K (fun x => A.eval (x:F)/((x:F)-β)) K := by
  exact ⟨agreementGE_of_le_card D K _ hK,agreementLE_polynomialOverPole D β hβ A K hA hAβ⟩
/-- With any first input, the padded second input forces exact common agreement at the new
message length. -/
theorem commonAgreementEQ_polynomialOverPole_right {F : Type*} [Field F]
    (D : Finset F) (β : F) (hβ : β ∉ D) (A : F[X]) (K : ℕ)
    (hA : A.natDegree≤K) (hAβ : A.eval β≠0) (hK : K≤D.card) (f : D → F) :
    commonAgreementEQ D K f (fun x => A.eval (x:F)/((x:F)-β)) K := by
  exact ⟨commonAgreementGE_of_le_card D K f _ hK,
    commonAgreementLE_of_right D K f _ K (agreementLE_polynomialOverPole D β hβ A K hA hAβ)⟩
/-- A kept set of nonzero challenges is still exceptional after padding, with its exact union
agreement threshold. -/
theorem nonzeroBadChallenges_padding
    {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (f g : D → F) (A : F[X]) (K s T : ℕ) (hA : A.natDegree≤s)
    (Z : Finset F)
    (hZ : ∀ z ∈ Z, z≠0 ∧ ∃ p : F[X], p.degree<K ∧
      T≤((Finset.univ.filter fun x : D => A.eval (x:F)=0) ∪
        (Finset.univ.filter fun x : D => f x+z*g x=p.eval (x:F))).card) :
    Z.card≤(nonzeroBadChallenges D (K+s) (fun x => A.eval (x:F)*f x)
      (fun x => A.eval (x:F)*g x) T).card := by
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hne,p,hp,hcount⟩ := hZ z hz
  apply Finset.mem_erase.mpr
  refine ⟨hne,(mem_badChallenges D (K+s) _ _ T z).mpr ?_⟩
  refine ⟨A*p,padding_witness_degree A p K s hA hp,?_⟩
  have hw : (fun x : D => A.eval (x:F)*f x+z*(A.eval (x:F)*g x))=
      (fun x : D => A.eval (x:F)*(f x+z*g x)) := by funext x; ring
  rw [hw,agreementCount_padding_union]
  exact hcount
end BinaryFieldCounterexamples.Gold
