/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.PaperSemantics
public import BinaryFieldCounterexamples.Agreement.Domains
public import BinaryFieldCounterexamples.Counting.BinarySubspaces
public import Mathlib.FieldTheory.Finite.Extension
/-!
# Finite fields and hyperplanes for Gold asymptotics
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- Every finite binary field has a finite extension of each prescribed
positive degree, with its canonical embedding and exact cardinality. -/
theorem exists_extension_of_degree
    (B : Type*) [Field B] [Fintype B] [CharP B 2] (e : ℕ) (he : 1≤e) :
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
    letI := fieldF
    letI := finiteF
    ∃ φ : B →+* F, Fintype.card F=(Fintype.card B)^e := by
  letI : NeZero e := ⟨by omega⟩
  let F := FiniteField.Extension B 2 e
  let fieldF : Field F := inferInstance
  let finiteF : Fintype F := Fintype.ofFinite F
  refine ⟨F,fieldF,finiteF,?_⟩
  letI := fieldF
  letI := finiteF
  let φ : B →+* F := algebraMap B F
  refine ⟨φ,?_⟩
  rw [←Nat.card_eq_fintype_card]
  change Nat.card (FiniteField.Extension B 2 e)=(Fintype.card B)^e
  rw [FiniteField.natCard_extension,
    Nat.card_eq_fintype_card]

/-- A binary field of dimension `d+1`, a hyperplane of size `2^d`, and its
finite extension of any prescribed positive degree. -/
theorem exists_hyperplane_with_extension (d e : ℕ) (he : 1≤e) :
    ∃ (B : Type) (fieldB : Field B) (finiteB : Fintype B),
    letI := fieldB
    letI := finiteB
    ∃ (_ : CharP B 2), Fintype.card B=2^(d+1) ∧
    ∃ D : AddSubgroup B, (additiveDomain D).card=2^d ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
    letI := fieldF
    letI := finiteF
    ∃ φ : B →+* F, Fintype.card F=(2^(d+1))^e := by
  classical
  let B := GaloisField 2 (d+1)
  let fieldB : Field B := inferInstance
  let finiteB : Fintype B := Fintype.ofFinite B
  refine ⟨B,fieldB,finiteB,?_⟩
  letI := fieldB
  letI := finiteB
  let charB : CharP B 2 := inferInstance
  refine ⟨charB,?_,?_⟩
  · rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (d+1) (by omega : d+1≠0)
  · let algB : Algebra (ZMod 2) B := ZMod.algebra B 2
    letI := algB
    have hcardB : Nat.card (⊤ : AddSubgroup B)=2^(d+1) := by
      rw [AddSubgroup.card_top]
      exact GaloisField.card 2 (d+1) (by omega : d+1≠0)
    obtain ⟨D,hDle,hD⟩ := exists_binary_subspace_card_eq (⊤ : AddSubgroup B)
      (2^d) ⟨d,rfl⟩ (by rw [hcardB]; exact Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨D,?_,?_⟩
    · rw [card_additiveDomain, hD]
    · letI : NeZero e := ⟨by omega⟩
      let F := FiniteField.Extension B 2 e
      let fieldF : Field F := inferInstance
      let finiteF : Fintype F := Fintype.ofFinite F
      refine ⟨F,fieldF,finiteF,?_⟩
      letI := fieldF
      letI := finiteF
      let φ : B →+* F := algebraMap B F
      refine ⟨φ,?_⟩
      rw [← Nat.card_eq_fintype_card, FiniteField.natCard_extension]
      rw [Nat.card_eq_fintype_card]
      have hc := GaloisField.card 2 (d+1) (by omega : d+1≠0)
      rw [Nat.card_eq_fintype_card] at hc
      exact congrArg (·^e) hc

end BinaryFieldCounterexamples.Gold
