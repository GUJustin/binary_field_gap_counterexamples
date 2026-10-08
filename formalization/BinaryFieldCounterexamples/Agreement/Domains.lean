/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Basic

/-!
# Transport of actual evaluation domains through field embeddings

These equalities relate the finite coordinate subtype in the main theorem to
the additive subgroup used for locators. Injectivity preserves every coordinate
and every agreement; no replacement of the prescribed domain is involved.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- Membership in the finite additive domain is literal subgroup membership. -/
theorem mem_additiveDomain
    {F : Type*} [Field F] [Fintype F] (D : AddSubgroup F) (x : F) :
    x ∈ additiveDomain D ↔ x ∈ D := by
  classical
  simp [additiveDomain]

/-- Domain cardinality is the subgroup's cardinality, independently of instances. -/
theorem card_additiveDomain
    {F : Type*} [Field F] [Fintype F] (D : AddSubgroup F) :
    (additiveDomain D).card = Nat.card D := by
  classical
  simp [additiveDomain, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Mapping the finite domain and mapping the additive subgroup give the same set. -/
theorem mappedDomain_additiveDomain
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F]
    (φ : B →+* F) (D : AddSubgroup B) :
    mappedDomain φ (additiveDomain D) = additiveDomain (D.map φ.toAddMonoidHom) := by
  classical
  ext x
  simp [mappedDomain, additiveDomain, AddSubgroup.mem_map]

/-- A field embedding preserves the number of prescribed coordinates. -/
theorem card_mappedDomain
    {B F : Type*} [Field B] [Field F] (φ : B →+* F) (D : Finset B) :
    (mappedDomain φ D).card = D.card := by
  classical
  exact Finset.card_image_of_injective D φ.injective

/-- Count agreement in the extension by filtering the original base-field domain. -/
theorem agreementCount_mappedDomain
    {B F : Type*} [Field B] [Field F] [DecidableEq B] [DecidableEq F]
    (φ : B →+* F) (D : Finset B) (w : F → F) (p : F[X]) :
    agreementCount (mappedDomain φ D) (fun x ↦ w x) p =
      (D.filter fun x ↦ p.eval (φ x) = w (φ x)).card := by
  rw [agreementCount_eq_card_filter (mappedDomain φ D) w p]
  simp only [mappedDomain, Finset.filter_image]
  have h := Finset.card_image_of_injective
    (D.filter fun x ↦ p.eval (φ x) = w (φ x)) φ.injective
  convert h using 1
  congr 1
  ext x
  simp

/-- A simultaneous attaining pair in particular attains the second-input bound. -/
theorem agreementGE_right_of_common
    {F : Type*} [Field F] (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ)
    (h : commonAgreementGE D K f g T) : agreementGE D K g T := by
  obtain ⟨p, r, _, hr, hcount⟩ := h
  exact ⟨r, hr, hcount.trans (commonAgreementCount_le_right D f g p r)⟩

/-- A simultaneous attaining pair also attains the first-input bound. -/
theorem agreementGE_left_of_common
    {F : Type*} [Field F] (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ)
    (h : commonAgreementGE D K f g T) : agreementGE D K f T := by
  obtain ⟨p, r, hp, _, hcount⟩ := h
  exact ⟨p, hp, hcount.trans (commonAgreementCount_le_left D f g p r)⟩

end BinaryFieldCounterexamples
