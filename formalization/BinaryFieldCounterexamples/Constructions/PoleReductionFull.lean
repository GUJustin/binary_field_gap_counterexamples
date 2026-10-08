/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.NormalizedPoleReduction
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingPolynomials

/-! # The full pole-reduction contract of Lemma 3.11 -/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Lemma 3.11's nonvanishing step: a nonzero polynomial having at least its
degree many roots in `D` cannot also vanish at an exterior pole. -/
theorem eval_ne_zero_of_natDegree_le_domain_roots
    {F : Type*} [Field F] (D : Finset F) (β : F) (hβ : β ∉ D)
    (P : F[X]) (hP : P ≠ 0)
    (hroots : P.natDegree ≤ (D.filter fun x ↦ P.eval x = 0).card) :
    P.eval β ≠ 0 := by
  classical
  intro hz
  have hcount := card_filter_eval_eq_zero_le (insert β D) P hP
  have hnot : β ∉ D.filter (fun x ↦ P.eval x = 0) := by simp [hβ]
  rw [Finset.filter_insert, ite_eq_left hz, Finset.card_insert_of_notMem hnot] at hcount
  omega

/-- Lemma 3.11, first pair: the displayed divided-difference witnesses have
strict degree below `K`, witness every correction's challenge, and the second
input and common agreement are both exactly `K`. -/
theorem poleReduction_full
    {ι F : Type*} [Field F] (D : Finset F) (β : F) (hβ : β ∉ D)
    (R : F[X]) (C : ι → F[X]) (K T : ℕ) (hK : K ≤ D.card)
    (hC : ∀ i, (C i).degree ≤ K)
    (hroots : ∀ i, T ≤ (D.filter fun x ↦ (R+C i).eval x = 0).card) :
    agreementEQ D K (fun x ↦ ((x:F)-β)⁻¹) K ∧
    commonAgreementEQ D K (fun x ↦ R.eval (x:F)*((x:F)-β)⁻¹)
      (fun x ↦ ((x:F)-β)⁻¹) K ∧
    ∀ i, (poleCorrection (C i) β).degree < K ∧
      T ≤ agreementCount D
        (fun x ↦ R.eval (x:F)*((x:F)-β)⁻¹+(C i).eval β*((x:F)-β)⁻¹)
        (poleCorrection (C i) β) := by
  classical
  refine ⟨agreementEQ_reciprocal D β hβ K hK,
    commonAgreementEQ_reciprocal_right D β hβ K hK _, fun i ↦
    ⟨poleCorrection_degree_lt (C i) β K (hC i), ?_⟩⟩
  rw [agreementCount_eq_card_filter D
    (fun x ↦ R.eval x*(x-β)⁻¹+(C i).eval β*(x-β)⁻¹) (poleCorrection (C i) β)]
  apply (hroots i).trans
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxD, hxroot⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
  have hxβ : x ≠ β := fun he ↦ hβ (he ▸ hxD)
  rw [poleCorrection_eval (C i) β x hxβ]
  simp only [eval_add] at hxroot
  field_simp
  linear_combination -hxroot

/-- Lemma 3.11, normalized pair: the same printed witnesses work, all
normalized challenges are nonzero, the first input has agreement at most
`T-1`, and both reciprocal and common agreement are exactly `K`. -/
theorem normalizedPoleReduction_full
    {ι F : Type*} [Field F] (D : Finset F) (β : F) (hβ : β ∉ D)
    (R : F[X]) (C : ι → F[X]) (i₀ : ι) (K T : ℕ)
    (hK : K ≤ D.card) (hTK : K < T)
    (hC : ∀ i, (C i).degree ≤ K)
    (hdeg : ∀ i, (R+C i).natDegree = T)
    (hroots : ∀ i, T ≤ (D.filter fun x ↦ (R+C i).eval x = 0).card) :
    agreementEQ D K (fun x ↦ ((x:F)-β)⁻¹) K ∧
    commonAgreementEQ D K (fun x ↦ (normalizedPoleSource R β).eval (x:F))
      (fun x ↦ ((x:F)-β)⁻¹) K ∧
    agreementLE D K (fun x ↦ (normalizedPoleSource R β).eval (x:F)) (T-1) ∧
    ∀ i, (R+C i).eval β ≠ 0 ∧ (poleCorrection (C i) β).degree < K ∧
      T ≤ agreementCount D
        (fun x ↦ (normalizedPoleSource R β).eval (x:F)+(R+C i).eval β*((x:F)-β)⁻¹)
        (poleCorrection (C i) β) := by
  classical
  have hCnat : ∀ i, (C i).natDegree ≤ K := by
    intro i
    by_cases hz : C i = 0
    · simp [hz]
    · exact natDegree_le_of_degree_le (hC i)
  have hRdeg : R.natDegree = T := by
    have hl : (C i₀).natDegree < (R+C i₀).natDegree := by rw [hdeg]; exact (hCnat i₀).trans_lt hTK
    have he := natDegree_sub_eq_left_of_natDegree_lt hl
    simpa only [add_sub_cancel_right] using he.trans (hdeg i₀)
  refine ⟨agreementEQ_reciprocal D β hβ K hK,
    commonAgreementEQ_reciprocal_right D β hβ K hK _, ?_, ?_⟩
  · rw [← hRdeg]
    exact agreementLE_normalizedPoleSource D R β K (by omega) (by omega)
  · intro i
    have hn : R+C i ≠ 0 := by
      intro hz
      have := hdeg i
      simp only [hz, natDegree_zero] at this
      omega
    refine ⟨eval_ne_zero_of_natDegree_le_domain_roots D β hβ (R+C i) hn
      (by rw [hdeg]; exact hroots i), poleCorrection_degree_lt (C i) β K (hC i), ?_⟩
    have hw : (fun x : D ↦ (normalizedPoleSource R β).eval (x:F)+(R+C i).eval β*((x:F)-β)⁻¹) =
        (fun x : D ↦ R.eval (x:F)*((x:F)-β)⁻¹+(C i).eval β*((x:F)-β)⁻¹) := by
      funext x
      rw [normalizedPoleSource_eval R β x (fun he ↦ hβ (he ▸ x.property)), eval_add, div_eq_mul_inv]
      ring
    rw [hw]
    exact (poleReduction_full D β hβ R C K T hK hC hroots).2.2 i |>.2

/-- Lemma 3.11's general numerator clause, assembled: a polynomial of degree
at most `J` nonzero at the pole gives individual and common agreement exactly `J`. -/
theorem polynomialOverPole_full
    {F : Type*} [Field F] (D : Finset F) (β : F) (hβ : β ∉ D)
    (A : F[X]) (J : ℕ) (hA : A.natDegree ≤ J) (hAβ : A.eval β ≠ 0)
    (hJ : J ≤ D.card) (u : D → F) :
    agreementEQ D J (fun x ↦ A.eval (x:F)/((x:F)-β)) J ∧
    commonAgreementEQ D J u (fun x ↦ A.eval (x:F)/((x:F)-β)) J := by
  exact ⟨Gold.agreementEQ_polynomialOverPole D β hβ A J hA hAβ hJ,
    Gold.commonAgreementEQ_polynomialOverPole_right D β hβ A J hA hAβ hJ u⟩

end BinaryFieldCounterexamples
