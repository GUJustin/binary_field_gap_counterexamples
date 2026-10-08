/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Agreement.SourceConversion
/-!
# Exact exceptional set under the proper-extension conversion of Lemma 3.12

This completes the converse in Lemma 3.12 (p. 23). Above the old common
agreement, every exceptional converted challenge comes from the fractional
linear image of an old challenge, except possibly `-1`. That last challenge
is exceptional exactly when the old second input meets the threshold.
Strict polynomial degree bounds and zero among old challenges are preserved.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Nonzero scaling preserves agreement with strict-degree explaining polynomials. -/
theorem agreementGE_mul_iff
    {F : Type*} [Field F] (D : Finset F) (K T : ℕ) (w : D → F)
    (a : F) (ha : a ≠ 0) :
    agreementGE D K (fun x => a * w x) T ↔ agreementGE D K w T := by
  have forward (b : F) (v : D → F) (hv : agreementGE D K v T) :
      agreementGE D K (fun x => b * v x) T := by
    obtain ⟨p, hp, hc⟩ := hv
    refine ⟨b • p, (degree_smul_le _ _).trans_lt hp, hc.trans ?_⟩
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    simpa using congrArg (b * ·) hx
  constructor
  · intro h
    simpa [← mul_assoc, ha] using forward a⁻¹ _ h
  · exact forward a w

/-- Allowing extension-field coefficients preserves a native word's agreement. -/
theorem agreementGE_mappedWord_iff
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (D : Finset B) (K T : ℕ) (w : B → B) :
    agreementGE (mappedDomain (algebraMap B F) D) K
      (fun x => algebraMap B F (w (Function.invFun (algebraMap B F) x))) T ↔
      agreementGE D K (fun x => w x) T := by
  let φ := algebraMap B F
  constructor
  · rintro ⟨p, hp, hc⟩
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one B
      (one_ne_zero : (1 : F) ≠ 0)
    obtain ⟨r, hr, he⟩ := exists_projected_polynomial l K p hp
    refine ⟨r, hr, hc.trans ?_⟩
    rw [agreementCount_mappedDomain (algebraMap B F) D
      (fun x : F => algebraMap B F (w (Function.invFun (algebraMap B F) x))),
      agreementCount_eq_card_filter]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxD, hx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
    rw [he, hx]
    simp only [Function.leftInverse_invFun (algebraMap B F).injective x]
    have hs := l.map_smul (w x) (1 : F)
    simpa [Algebra.smul_def, hl] using hs
  · rintro ⟨p, hp, hc⟩
    refine ⟨p.map φ, degree_map_le.trans_lt hp, hc.trans ?_⟩
    rw [agreementCount_mappedDomain (algebraMap B F) D
      (fun x : F => algebraMap B F (w (Function.invFun (algebraMap B F) x))),
      agreementCount_eq_card_filter]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxD, hx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
    simp [φ, eval_map, eval₂_at_apply, Function.leftInverse_invFun
      (algebraMap B F).injective x, hx]

/-- The fractional-linear image does not contain `-1`. -/
theorem extensionChallenge_ne_neg_one
    {B F : Type*} [Field B] [Field F] (φ : B →+* F) (θ : F)
    (hθ : θ ∉ Set.range φ) (a : B) : extensionChallenge φ θ a ≠ -1 := by
  intro h
  have hden := extensionChallenge_denominator_ne_zero φ θ hθ a
  have he := (div_eq_iff hden).mp h
  have : (1 : F) = 0 := by linear_combination he
  exact one_ne_zero this

/-- Undo the change of input pair at any challenge other than `-1`. -/
theorem source_conversion_inverse_word
    {B F : Type*} [Field B] [Field F] (φ : B →+* F) (θ z : F)
    (hz : 1 + z ≠ 0) (f g : B → B) (x : F) :
    extensionLinearWord φ θ f g x + z * extensionLinearWord φ (θ + 1) f g x =
      (1 + z) * extensionLinearWord φ (θ + z / (1 + z)) f g x := by
  dsimp [extensionLinearWord]
  field_simp
  ring

/-- Exact classification, assuming the threshold exceeds common agreement. -/
theorem agreementGE_source_conversion_iff
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (D : Finset B) (K C T : ℕ) (f g : B → B)
    (hc : commonAgreementLE D K (fun x => f x) (fun x => g x) C)
    (hCT : C < T) (θ : F) (hθ : θ ∉ Set.range (algebraMap B F)) (z : F) :
    agreementGE (mappedDomain (algebraMap B F) D) K
      (fun x => extensionLinearWord (algebraMap B F) θ f g x +
        z * extensionLinearWord (algebraMap B F) (θ + 1) f g x) T ↔
      (∃ a : B, agreementGE D K (fun x => f x + a * g x) T ∧
        z = extensionChallenge (algebraMap B F) θ a) ∨
      (z = -1 ∧ agreementGE D K (fun x => g x) T) := by
  let φ := algebraMap B F
  have hminus : agreementGE (mappedDomain φ D) K
      (fun x => extensionLinearWord φ θ f g x +
        (-1) * extensionLinearWord φ (θ + 1) f g x) T ↔
        agreementGE D K (fun x => g x) T := by
    have hw : (fun x : mappedDomain φ D => extensionLinearWord φ θ f g x +
        (-1) * extensionLinearWord φ (θ + 1) f g x) =
        (fun x : mappedDomain φ D => (-1 : F) * φ (g (Function.invFun φ (x : F)))) := by
      funext x
      dsimp [extensionLinearWord]
      ring
    rw [hw, agreementGE_mul_iff _ _ _ _ _ (neg_ne_zero.mpr one_ne_zero)]
    exact agreementGE_mappedWord_iff D K T g
  by_cases hz : z = -1
  · subst z
    rw [hminus]
    constructor
    · exact fun hg => Or.inr ⟨rfl, hg⟩
    · rintro (⟨a, _, he⟩ | ⟨_, hg⟩)
      · exact False.elim (extensionChallenge_ne_neg_one φ θ hθ a he.symm)
      · exact hg
  have hz1 : 1 + z ≠ 0 := by intro h; apply hz; linear_combination h
  have hword : (fun x : mappedDomain φ D => extensionLinearWord φ θ f g x +
      z * extensionLinearWord φ (θ + 1) f g x) =
      (fun x : mappedDomain φ D => (1 + z) * extensionLinearWord φ (θ + z / (1 + z)) f g (x : F)) :=
    funext (fun x => source_conversion_inverse_word φ θ z hz1 f g x)
  constructor
  · intro h
    rw [hword, agreementGE_mul_iff _ _ _ _ _ hz1] at h
    by_cases hr : θ + z / (1 + z) ∈ Set.range φ
    · obtain ⟨a, ha⟩ := hr
      have hw' : (fun x : mappedDomain φ D =>
          extensionLinearWord φ (θ + z / (1 + z)) f g x) =
          (fun x : mappedDomain φ D => φ ((fun y => f y + a * g y) (Function.invFun φ (x : F)))) := by
        funext x
        rw [← ha]
        simp [extensionLinearWord]
      rw [hw'] at h
      have hold := (agreementGE_mappedWord_iff D K T (fun y => f y + a * g y)).mp h
      refine Or.inl ⟨a, hold, ?_⟩
      apply (eq_div_iff (extensionChallenge_denominator_ne_zero φ θ hθ a)).mpr
      have hh := ha
      field_simp at hh
      linear_combination -hh
    · obtain ⟨p, hp, hcount⟩ := h
      have hb := agreementLE_extensionLinearWord D K C f g hc
        (θ + z / (1 + z)) hr p hp
      exact False.elim ((not_le_of_gt hCT) (hcount.trans hb))
  · rintro (⟨a, ha, rfl⟩ | ⟨he, _⟩)
    · exact agreementGE_extensionChallenge φ θ hθ D K T f g a ha
    · exact False.elim (hz he)

/-- The whole converted exceptional set is the image of the old exceptional set, with the
single challenge `-1` included precisely when the second input is close. -/
theorem badChallenges_source_conversion_eq
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] [Algebra B F]
    (D : Finset B) (K C T : ℕ) (f g : B → B)
    (hc : commonAgreementLE D K (fun x => f x) (fun x => g x) C)
    (hCT : C < T) (θ : F) (hθ : θ ∉ Set.range (algebraMap B F)) :
    badChallenges (mappedDomain (algebraMap B F) D) K
      (fun x => extensionLinearWord (algebraMap B F) θ f g x)
      (fun x => extensionLinearWord (algebraMap B F) (θ + 1) f g x) T =
      (badChallenges D K (fun x => f x) (fun x => g x) T).image
        (extensionChallenge (algebraMap B F) θ) ∪
      (if agreementGE D K (fun x => g x) T then {-1} else ∅) := by
  ext z
  rw [mem_badChallenges, agreementGE_source_conversion_iff D K C T f g hc hCT θ hθ]
  simp only [Finset.mem_union, Finset.mem_image, mem_badChallenges]
  by_cases hg : agreementGE D K (fun x => g x) T <;> simp [hg, eq_comm]

/-- Exact exceptional count: the conversion of Lemma 3.12 adds at most the one remaining
challenge. No old challenge is lost and the added challenge is distinct. -/
theorem card_badChallenges_source_conversion_eq
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] [Algebra B F]
    (D : Finset B) (K C T : ℕ) (f g : B → B)
    (hc : commonAgreementLE D K (fun x => f x) (fun x => g x) C)
    (hCT : C < T) (θ : F) (hθ : θ ∉ Set.range (algebraMap B F)) :
    (badChallenges (mappedDomain (algebraMap B F) D) K
      (fun x => extensionLinearWord (algebraMap B F) θ f g x)
      (fun x => extensionLinearWord (algebraMap B F) (θ + 1) f g x) T).card =
      (badChallenges D K (fun x => f x) (fun x => g x) T).card +
      (if agreementGE D K (fun x => g x) T then 1 else 0) := by
  rw [badChallenges_source_conversion_eq D K C T f g hc hCT θ hθ]
  have hn : (-1 : F) ∉
      (badChallenges D K (fun x => f x) (fun x => g x) T).image
        (extensionChallenge (algebraMap B F) θ) := by
    intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact extensionChallenge_ne_neg_one _ θ hθ a ha
  by_cases hg : agreementGE D K (fun x => g x) T
  · simp [hg, Finset.union_singleton, Finset.card_insert_of_notMem hn,
      Finset.card_image_of_injective _ (extensionChallenge_injective _ θ hθ)]
  · simp [hg, Finset.card_image_of_injective _ (extensionChallenge_injective _ θ hθ)]

/-- The converted count is bounded by the old exceptional count plus one. -/
theorem card_badChallenges_source_conversion_le
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] [Algebra B F]
    (D : Finset B) (K C T : ℕ) (f g : B → B)
    (hc : commonAgreementLE D K (fun x => f x) (fun x => g x) C)
    (hCT : C < T) (θ : F) (hθ : θ ∉ Set.range (algebraMap B F)) :
    (badChallenges (mappedDomain (algebraMap B F) D) K
      (fun x => extensionLinearWord (algebraMap B F) θ f g x)
      (fun x => extensionLinearWord (algebraMap B F) (θ + 1) f g x) T).card ≤
      (badChallenges D K (fun x => f x) (fun x => g x) T).card + 1 := by
  rw [card_badChallenges_source_conversion_eq D K C T f g hc hCT θ hθ]
  split_ifs <;> omega

/-- The paper's field-size upper bound for the uniform exceptional probability.
The stronger exact count above keeps the actual old exceptional set. -/
theorem source_conversion_exceptional_probability_le
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] [Algebra B F]
    (D : Finset B) (K C T : ℕ) (f g : B → B)
    (hc : commonAgreementLE D K (fun x => f x) (fun x => g x) C)
    (hCT : C < T) (θ : F) (hθ : θ ∉ Set.range (algebraMap B F)) :
    ((badChallenges (mappedDomain (algebraMap B F) D) K
      (fun x => extensionLinearWord (algebraMap B F) θ f g x)
      (fun x => extensionLinearWord (algebraMap B F) (θ + 1) f g x) T).card : ℚ) /
        Fintype.card F ≤ (Fintype.card B + 1 : ℚ) / Fintype.card F := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (card_badChallenges_source_conversion_le D K C T f g hc hCT θ hθ).trans
    (Nat.add_le_add_right (Finset.card_le_univ _) 1)

end BinaryFieldCounterexamples
