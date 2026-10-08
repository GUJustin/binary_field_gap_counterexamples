/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.AllRates.LocatorCancellation
public import BinaryFieldCounterexamples.Constructions.AllRates.LabelRecovery
public import BinaryFieldCounterexamples.Polynomial.LocatorPrefixInjectivity
public import BinaryFieldCounterexamples.Counting.AffineLabelPooling

/-!
# Concrete finite seeds for arbitrary rates

Distinct actual binary subgroups have distinct affine functions giving the cancellation
challenges. Pooling their literal evaluations yields one common first input and direction
with the exact rational ceiling bound on exceptional challenges, including challenge zero.
The strict locator witnesses persist at the direction's degree for padding.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.AllRatesConstruction
open Polynomial BinaryLocator
attribute [local instance] Classical.decEq Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
set_option linter.unusedSectionVars false

/-- Distinct concrete subspaces have distinct affine functions giving the cancellation
challenges. -/
theorem subspace_cancellationLabel_injOn (H : AddSubgroup F) (m s : ℕ)
    (hs : 2≤s) (hm : s≤m) (hH : Nat.card H=2^(m+s))
    (I : Finset (AddSubgroup F))
    (hI : ∀ W∈I, W≤H ∧ Nat.card W=2^m) :
    Set.InjOn (fun W : AddSubgroup F =>
      finiteCancellationLabelAffine s (locatorPrefix (subspacePolynomial W) m)) I := by
  intro U hU W hW he
  apply eq_of_subspacePolynomial_prefix_eq H U W m s hm hH
    (hI U hU).2 (hI W hW).2 (hI U hU).1 (hI W hW).1
  have ha0 : locatorPrefix (subspacePolynomial U) m 0=
      locatorPrefix (subspacePolynomial W) m 0 := by
    have hdu : (subspacePolynomial U).natDegree=2^m := by
      rw [subspacePolynomial_natDegree,←Nat.card_eq_fintype_card,(hI U hU).2]
    have hdw : (subspacePolynomial W).natDegree=2^m := by
      rw [subspacePolynomial_natDegree,←Nat.card_eq_fintype_card,(hI W hW).2]
    simp only [locatorPrefix,Nat.sub_zero]
    calc
      (subspacePolynomial U).coeff (2^m)=(1:F) := by
        rw [←hdu]
        exact (subspacePolynomial_monic U).coeff_natDegree
      _=(subspacePolynomial W).coeff (2^m) := by
        rw [←hdw]
        exact (subspacePolynomial_monic W).coeff_natDegree.symm
  exact cancellationLabelAffine_prefix_injective s hs _ _ ha0
    (cancellationLabelAffine_eq_of_finite_eq s _ _ he)
/-- Each literal challenge is exceptional, with agreement on all nonzero points of its
concrete subgroup. -/
theorem subspace_cancellationLabel_mem_badChallenges (H W : AddSubgroup F)
    (m s : ℕ) (hs : 1≤s) (hm : s≤m) (hW : Nat.card W=2^m) (hWH : W≤H)
    (θ : Fin (s-1) → F) :
    finiteCancellationLabelAffine s (locatorPrefix (subspacePolynomial W) m) θ ∈
      badChallenges (additiveDomain H) (2^(m-2))
        (fun x => (cancellationSource m s (finiteCancellationParameterExtension s θ)).eval (x:F))
        (fun x => (x:F)^(2^(m-1)-1)) (2^m-1) := by
  obtain ⟨p,hp,he⟩ := exists_subspace_cancellation_witness W m s hs hm hW
    (finiteCancellationParameterExtension s θ)
  rw [mem_badChallenges]
  refine ⟨p,hp,?_⟩
  change 2^m-1≤agreementCount (additiveDomain H)
    (fun x => (cancellationSource m s (finiteCancellationParameterExtension s θ)).eval (x:F)+
      cancellationLabel s (locatorPrefix (subspacePolynomial W) m)
        (finiteCancellationParameterExtension s θ)*(x:F)^(2^(m-1)-1)) p
  rw [agreementCount_eq_card_filter (additiveDomain H)
    (fun x : F => (cancellationSource m s (finiteCancellationParameterExtension s θ)).eval x+
      cancellationLabel s (locatorPrefix (subspacePolynomial W) m)
        (finiteCancellationParameterExtension s θ)*x^(2^(m-1)-1)) p]
  have hwcard : (additiveDomain W).card=2^m := by
    rw [←hW,Nat.card_eq_fintype_card,Fintype.card_subtype]
    rfl
  have hz : (0:F)∈additiveDomain W := by simp [additiveDomain]
  calc
    2^m-1=((additiveDomain W).erase 0).card := by
      rw [Finset.card_erase_of_mem hz,hwcard]
    _≤_ := Finset.card_le_card (by
      intro x hx
      obtain ⟨hx0,hxW⟩ := Finset.mem_erase.mp hx
      have hmem : x∈W := by simpa [additiveDomain] using hxW
      exact Finset.mem_filter.mpr ⟨by simpa [additiveDomain] using hWH hmem,(he x hmem hx0).symm⟩)
/-- Collision pooling produces the exact finite seed count, keeping the zero challenge. -/
theorem exists_finite_seed_parameter (H : AddSubgroup F) (m s : ℕ)
    (hs : 2≤s) (hm : s≤m) (hH : Nat.card H=2^(m+s))
    (I : Finset (AddSubgroup F)) (hI : ∀ W∈I, W≤H ∧ Nat.card W=2^m) :
    ∃ θ : Fin (s-1) → F,
      ⌈((Fintype.card F*I.card:ℕ):ℚ)/(Fintype.card F+I.card-1:ℕ)⌉₊ ≤
        (badChallenges (additiveDomain H) (2^(m-2))
          (fun x => (cancellationSource m s (finiteCancellationParameterExtension s θ)).eval (x:F))
          (fun x => (x:F)^(2^(m-1)-1)) (2^m-1)).card := by
  obtain ⟨θ,hθ⟩ := exists_affineLabel_parameter_image_card_lower_ratCeil (s-1) (by omega) I
    (fun W => finiteCancellationLabelAffine s (locatorPrefix (subspacePolynomial W) m))
    (subspace_cancellationLabel_injOn H m s hs hm hH I hI)
  refine ⟨θ,hθ.trans (Finset.card_le_card ?_)⟩
  intro z hz
  obtain ⟨W,hW,rfl⟩ := Finset.mem_image.mp hz
  exact subspace_cancellationLabel_mem_badChallenges H W m s (by omega) hm
    (hI W hW).2 (hI W hW).1 θ
/-- Increasing the strict message length preserves every exceptional challenge. -/
theorem badChallenges_dimension_mono (E : Finset F) (K J T : ℕ)
    (hKJ : K≤J) (f g : E → F) :
    badChallenges E K f g T ⊆ badChallenges E J f g T := by
  intro z hz
  rw [mem_badChallenges] at hz ⊢
  obtain ⟨p,hp,he⟩ := hz
  exact ⟨p,hp.trans_le (by exact_mod_cast hKJ),he⟩
/-- The same finite seed works at the direction polynomial's exact degree,
which is the base message length used by arbitrary-rate padding. -/
theorem exists_finite_seed_parameter_direction_dimension (H : AddSubgroup F) (m s : ℕ)
    (hs : 2≤s) (hm : s≤m) (hH : Nat.card H=2^(m+s))
    (I : Finset (AddSubgroup F)) (hI : ∀ W∈I, W≤H ∧ Nat.card W=2^m) :
    ∃ θ : Fin (s-1) → F,
      ⌈((Fintype.card F*I.card:ℕ):ℚ)/(Fintype.card F+I.card-1:ℕ)⌉₊ ≤
        (badChallenges (additiveDomain H) (2^(m-1)-1)
          (fun x => (cancellationSource m s (finiteCancellationParameterExtension s θ)).eval (x:F))
          (fun x => (x:F)^(2^(m-1)-1)) (2^m-1)).card := by
  obtain ⟨θ,hθ⟩ := exists_finite_seed_parameter H m s hs hm hH I hI
  refine ⟨θ,hθ.trans (Finset.card_le_card (badChallenges_dimension_mono _ _ _ _ ?_ _ _))⟩
  have hpow : 2^(m-1)=(2:ℕ)^(m-2)*2 := by
    rw [←pow_succ]
    congr 1
    omega
  have hp : 0<(2:ℕ)^(m-2) := by positivity
  rw [hpow]
  omega
end BinaryFieldCounterexamples.AllRatesConstruction
