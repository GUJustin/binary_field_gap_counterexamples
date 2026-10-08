/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.SourceConversion

/-!
# Section 7: the subfield bound on exceptional challenges

When the domain and both words lie in a subfield, challenges outside that
subfield cannot exceed the common agreement. Thus, at a threshold strictly
above common agreement, the whole exceptional set lies in the subfield and
its uniform probability is at most the ratio of field sizes. The threshold
hypothesis is necessary and is made explicit here.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.decEq

/-- Section 7, final paragraph: above the common agreement of two native
words, every exceptional challenge belongs to their containing subfield. -/
theorem native_badChallenges_subset_subfield
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] [Algebra B F]
    (D : Finset B) (K C T : ℕ) (f g : B → B)
    (hc : commonAgreementLE D K (fun x => f x) (fun x => g x) C)
    (hCT : C < T) :
    badChallenges (mappedDomain (algebraMap B F) D) K
      (fun x => algebraMap B F (f (Function.invFun (algebraMap B F) x)))
      (fun x => algebraMap B F (g (Function.invFun (algebraMap B F) x))) T ⊆
      Finset.univ.image (algebraMap B F) := by
  classical
  intro θ hθ
  by_contra hn
  have hout : θ ∉ Set.range (algebraMap B F) := by
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hn
  obtain ⟨p, hp, hcount⟩ := (mem_badChallenges _ _ _ _ _ θ).mp hθ
  have hub := agreementLE_extensionLinearWord D K C f g hc θ hout p hp
  exact (not_le_of_gt hCT) (hcount.trans hub)

/-- Section 7, final paragraph: the native pair has at most the subfield's
cardinality many exceptional challenges above its common agreement. -/
theorem native_badChallenges_card_le_subfield
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] [Algebra B F]
    (D : Finset B) (K C T : ℕ) (f g : B → B)
    (hc : commonAgreementLE D K (fun x => f x) (fun x => g x) C)
    (hCT : C < T) :
    (badChallenges (mappedDomain (algebraMap B F) D) K
      (fun x => algebraMap B F (f (Function.invFun (algebraMap B F) x)))
      (fun x => algebraMap B F (g (Function.invFun (algebraMap B F) x))) T).card ≤
      Fintype.card B := by
  classical
  exact (Finset.card_le_card (native_badChallenges_subset_subfield D K C T f g hc hCT)).trans
    (by simp [Finset.card_image_of_injective _ (algebraMap B F).injective])

/-- Section 7, final paragraph: uniform exceptional probability for a native
pair is at most `|B|/|F|`, provided the threshold exceeds common agreement. -/
theorem native_exceptional_probability_le_subfield
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] [Algebra B F]
    (D : Finset B) (K C T : ℕ) (f g : B → B)
    (hc : commonAgreementLE D K (fun x => f x) (fun x => g x) C)
    (hCT : C < T) :
    ((badChallenges (mappedDomain (algebraMap B F) D) K
      (fun x => algebraMap B F (f (Function.invFun (algebraMap B F) x)))
      (fun x => algebraMap B F (g (Function.invFun (algebraMap B F) x))) T).card : ℝ) /
        Fintype.card F ≤ (Fintype.card B : ℝ) / Fintype.card F := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast native_badChallenges_card_le_subfield D K C T f g hc hCT

end BinaryFieldCounterexamples
