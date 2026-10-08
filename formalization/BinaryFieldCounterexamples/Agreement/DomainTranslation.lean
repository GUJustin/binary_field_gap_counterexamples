/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Domains
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Translation of the actual evaluation domain

The affine-translate clauses of Theorem 5.1 and Corollary 5.18 allow shifts
in the challenge field. Translation reindexes the prescribed coordinates and
substitutes a linear polynomial in every explaining polynomial. It preserves
strict degree, simultaneous agreement, decoding-list distinctness, and the
entire exceptional set, including its nonzero restriction.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial

/-- The coordinate bijection for the affine-translate clauses of Theorem 5.1
and Corollary 5.18; the shift is an arbitrary field element. -/
noncomputable def domainTranslationEquiv {F : Type*} [Field F]
    (D : Finset F) (c : F) : D ≃ affineDomain D c := by
  classical
  exact
    { toFun := fun x => ⟨x + c, Finset.mem_image.mpr ⟨x, x.property, rfl⟩⟩
      invFun := fun x => ⟨x - c, by
        obtain ⟨y, hy, he⟩ := Finset.mem_image.mp x.property
        simpa [← he] using hy⟩
      left_inv := fun x => Subtype.ext (add_sub_cancel_right (x : F) c)
      right_inv := fun x => Subtype.ext (sub_add_cancel (x : F) c) }

/-- The transported word in the affine-translate clauses of Theorem 5.1 and
Corollary 5.18, on exactly the translated coordinate subtype. -/
noncomputable def translatedWord {F : Type*} [Field F]
    (D : Finset F) (c : F) (w : D → F) : affineDomain D c → F :=
  w ∘ (domainTranslationEquiv D c).symm

theorem degree_comp_shift {F : Type*} [Field F] (p : F[X]) (c : F) :
    (p.comp (X + C c)).degree = p.degree := by
  rw [degree_comp (by simp)]
  simp

theorem agree_equiv {I J A : Type*} [Fintype I] [Fintype J]
    [DecidableEq A] (e : I ≃ J) (u v : J → A) :
    Code.agree u v = Code.agree (u ∘ e) (v ∘ e) := by
  classical
  unfold Code.agree
  apply Finset.card_bij (fun x _ => e.symm x)
  · intro x hx
    simpa using hx
  · intro x _ y _ h
    exact e.symm.injective h
  · intro x hx
    exact ⟨e x, by simpa using hx, e.symm_apply_apply x⟩

/-- Theorem 5.1's affine-domain substitution preserves each literal polynomial
agreement count; this also covers shifts outside the base field. -/
theorem agreementCount_translatedWord {F : Type*} [Field F]
    (D : Finset F) (c : F) (w : D → F) (p : F[X]) :
    agreementCount (affineDomain D c) (translatedWord D c w) p =
      agreementCount D w (p.comp (X + C c)) := by
  classical
  unfold agreementCount
  rw [agree_equiv (domainTranslationEquiv D c)]
  congr 1
  · funext x
    exact congrArg w ((domainTranslationEquiv D c).symm_apply_apply x)
  · funext x
    simp [domainTranslationEquiv, eval_comp]

/-- Theorem 5.1's affine-translate clause preserves attained strict-degree
agreement at every threshold. -/
theorem agreementGE_translatedWord_iff {F : Type*} [Field F]
    (D : Finset F) (c : F) (K T : ℕ) (w : D → F) :
    agreementGE (affineDomain D c) K (translatedWord D c w) T ↔
      agreementGE D K w T := by
  constructor
  · rintro ⟨p, hp, hc⟩
    exact ⟨p.comp (X + C c), by rwa [degree_comp_shift],
      by rwa [agreementCount_translatedWord] at hc⟩
  · rintro ⟨p, hp, hc⟩
    refine ⟨p.comp (X + C (-c)), by rwa [degree_comp_shift], ?_⟩
    rw [agreementCount_translatedWord]
    simpa [comp_assoc, add_comp, X_comp, C_comp, add_assoc] using hc

/-- Theorem 5.1's affine-translate clause preserves individual agreement upper
bounds, with the same strict degree bound. -/
theorem agreementLE_translatedWord_iff {F : Type*} [Field F]
    (D : Finset F) (c : F) (K T : ℕ) (w : D → F) :
    agreementLE (affineDomain D c) K (translatedWord D c w) T ↔
      agreementLE D K w T := by
  constructor
  · intro h p hp
    have hc := h (p.comp (X + C (-c))) (by rwa [degree_comp_shift])
    rw [agreementCount_translatedWord] at hc
    simpa [comp_assoc, add_comp, X_comp, C_comp, add_assoc] using hc
  · intro h p hp
    rw [agreementCount_translatedWord]
    exact h _ (by rwa [degree_comp_shift])

/-- Theorem 5.1 and Corollary 5.18: exact individual agreement is unchanged
under an arbitrary affine translation of the evaluation domain. -/
theorem agreementEQ_translatedWord_iff {F : Type*} [Field F]
    (D : Finset F) (c : F) (K T : ℕ) (w : D → F) :
    agreementEQ (affineDomain D c) K (translatedWord D c w) T ↔
      agreementEQ D K w T := by
  unfold agreementEQ
  rw [agreementGE_translatedWord_iff, agreementLE_translatedWord_iff]

/-- The affine-translate clauses of Theorem 5.1 and Corollary 5.18 preserve
simultaneous agreement counts of the two inputs. -/
theorem commonAgreementCount_translatedWord {F : Type*} [Field F]
    (D : Finset F) (c : F) (f g : D → F) (p r : F[X]) :
    commonAgreementCount (affineDomain D c)
      (translatedWord D c f) (translatedWord D c g) p r =
    commonAgreementCount D f g (p.comp (X + C c)) (r.comp (X + C c)) := by
  classical
  unfold commonAgreementCount
  rw [agree_equiv (domainTranslationEquiv D c)]
  congr 1
  · funext x
    simp only [Function.comp_apply, translatedWord,
      (domainTranslationEquiv D c).symm_apply_apply]
  · funext x
    simp [domainTranslationEquiv, eval_comp]

/-- The affine-translate clauses of Theorem 5.1 and Corollary 5.18 preserve
exact common agreement of the same fixed pair. -/
theorem commonAgreementEQ_translatedWord_iff {F : Type*} [Field F]
    (D : Finset F) (c : F) (K T : ℕ) (f g : D → F) :
    commonAgreementEQ (affineDomain D c) K
      (translatedWord D c f) (translatedWord D c g) T ↔
    commonAgreementEQ D K f g T := by
  have cancel (p : F[X]) : (p.comp (X + C (-c))).comp (X + C c) = p := by
    simp [comp_assoc, add_comp, X_comp, C_comp, add_assoc]
  constructor
  · rintro ⟨⟨p,r,hp,hr,hc⟩,h⟩
    refine ⟨⟨p.comp (X + C c), r.comp (X + C c), by rwa [degree_comp_shift],
      by rwa [degree_comp_shift], by rwa [commonAgreementCount_translatedWord] at hc⟩, ?_⟩
    intro p r hp hr
    have hc := h (p.comp (X + C (-c))) (r.comp (X + C (-c)))
      (by rwa [degree_comp_shift]) (by rwa [degree_comp_shift])
    rwa [commonAgreementCount_translatedWord, cancel, cancel] at hc
  · rintro ⟨⟨p,r,hp,hr,hc⟩,h⟩
    refine ⟨⟨p.comp (X + C (-c)), r.comp (X + C (-c)), by rwa [degree_comp_shift],
      by rwa [degree_comp_shift], ?_⟩, ?_⟩
    · rwa [commonAgreementCount_translatedWord, cancel, cancel]
    · intro p r hp hr
      rw [commonAgreementCount_translatedWord]
      exact h _ _ (by rwa [degree_comp_shift]) (by rwa [degree_comp_shift])

/-- The affine-translate clauses of Theorem 5.1 and Corollary 5.18 preserve
all exceptional challenges as a set, not merely their number. -/
theorem badChallenges_translatedWord {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (c : F) (K T : ℕ) (f g : D → F) :
    badChallenges (affineDomain D c) K
      (translatedWord D c f) (translatedWord D c g) T = badChallenges D K f g T := by
  classical
  ext z
  rw [mem_badChallenges, mem_badChallenges]
  exact agreementGE_translatedWord_iff D c K T (fun x => f x + z * g x)

/-- Theorem 5.1 and Corollary 5.18: arbitrary domain translation keeps the
entire nonzero exceptional set of one fixed pair. -/
theorem nonzeroBadChallenges_translatedWord {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (c : F) (K T : ℕ) (f g : D → F) :
    nonzeroBadChallenges (affineDomain D c) K
      (translatedWord D c f) (translatedWord D c g) T = nonzeroBadChallenges D K f g T := by
  unfold nonzeroBadChallenges
  rw [badChallenges_translatedWord]

/-- Theorem 5.1's ordinary-list conclusion transports to arbitrary affine
translates, preserving the number of distinct explaining polynomials. -/
theorem ordinaryList_translatedDomain {F : Type*} [Field F]
    (D : Finset F) (c : F) (K T L : ℕ) (h : ordinaryList D K T L) :
    ordinaryList (affineDomain D c) K T L := by
  classical
  obtain ⟨w,ps,hcard,hps⟩ := h
  have cancel (p : F[X]) : (p.comp (X + C (-c))).comp (X + C c) = p := by
    simp [comp_assoc, add_comp, X_comp, C_comp, add_assoc]
  have hinj : Function.Injective (fun p : F[X] => p.comp (X + C (-c))) := by
    intro p r h
    have hh := congrArg (fun q : F[X] => q.comp (X + C c)) h
    simpa only [cancel] using hh
  refine ⟨translatedWord D c w, ps.image (fun p => p.comp (X + C (-c))),
    by rwa [Finset.card_image_of_injective _ hinj], ?_⟩
  intro p hp
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hd,hc⟩ := hps r hr
  exact ⟨by rwa [degree_comp_shift], by rwa [agreementCount_translatedWord, cancel]⟩

end BinaryFieldCounterexamples
