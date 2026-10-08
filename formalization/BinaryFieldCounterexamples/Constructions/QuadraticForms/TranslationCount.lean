/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalQuotient
public import Mathlib.Data.Setoid.Basic
/-!
# Exact counts of translated quadratic functions

Translations of a quadratic form are equal exactly modulo its quadratic radical,
including in characteristic two. Finite differences recover the polar form.
Consequently a family whose polar forms are distinct has disjoint translation
families, each of cardinality the field size to the quadratic rank.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
/-- Equality of two translated functions is exactly radical equivalence of the translating vectors. -/
theorem translated_eq_iff_radical (Q : QuadraticForm k V) (a b : V) :
    (fun x => Q (x-a))=(fun x => Q (x-b)) ↔ a-b ∈ Q.radical := by
  rw [QuadraticMap.mem_radical_iff']
  constructor
  · intro h
    have hpoint (x : V) := congrFun h x
    refine ⟨?_,?_⟩
    · simpa using (hpoint a).symm
    · intro x
      simpa [sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using (hpoint (x+a)).symm
  · rintro ⟨hz,hadd⟩
    funext x
    have h := hadd (x-a)
    convert h.symm using 1
    congr 1
    abel

/-- Actual translated functions are parametrized without multiplicity by the radical quotient. -/
noncomputable def translatedRangeEquiv (Q : QuadraticForm k V) :
    (V ⧸ Q.radical) ≃ Set.range (fun a : V => fun x => Q (x-a)) := by
  let e : (V ⧸ Q.radical) ≃ Quotient (Setoid.ker (fun a : V => fun x => Q (x-a))) :=
    Quotient.congrRight (fun a b => by
      rw [Submodule.quotientRel_def]
      change a-b ∈ Q.radical ↔ (fun x => Q (x-a))=(fun x => Q (x-b))
      exact (translated_eq_iff_radical Q a b).symm)
  exact e.trans (Setoid.quotientKerEquivRange _)

/-- The actual number of distinct translated functions is the field size to the quadratic rank. -/
theorem translatedRange_natCard [Fintype k] [FiniteDimensional k V]
    (Q : QuadraticForm k V) :
    Nat.card (Set.range (fun a : V => fun x => Q (x-a))) =
      (Fintype.card k)^(Module.finrank k V-Module.finrank k Q.radical) := by
  rw [←Nat.card_congr (translatedRangeEquiv Q),Module.natCard_eq_pow_finrank (K:=k),
    Nat.card_eq_fintype_card]
  congr 1
  have := Q.radical.finrank_quotient_add_finrank
  omega

/-- A second finite difference of a translated quadratic function recovers its polar form. -/
theorem translated_polar_identity (Q : QuadraticForm k V) (a x y : V) :
    Q (x+y-a)-Q (x-a)-Q (y-a)+Q (-a)=Q.polarBilin x y := by
  have h := Q.map_add_add_add_map x y (-a)
  rw [show -a+x=x+-a by abel] at h
  simp only [sub_eq_add_neg,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar] at *
  linear_combination h

/-- Equal translated functions have the same polar form, in every characteristic. -/
theorem polar_eq_of_translated_eq (Q R : QuadraticForm k V) (a b : V)
    (h : (fun x => Q (x-a))=(fun x => R (x-b))) : Q.polarBilin=R.polarBilin := by
  ext x y
  rw [←translated_polar_identity Q a x y,←translated_polar_identity R b x y]
  have hxy := congrFun h (x+y)
  have hx := congrFun h x
  have hy := congrFun h y
  have h0 := congrFun h 0
  simp only [zero_sub] at h0
  rw [hxy,hx,hy,h0]

/-- Distinct polar forms give disjoint actual translation families. -/
noncomputable def translatedFamilyRangeEquiv {I : Type*} (Q : I → QuadraticForm k V)
    (hinj : Function.Injective (fun i => (Q i).polarBilin)) :
    (Σ i, Set.range (fun a : V => fun x => Q i (x-a))) ≃
      Set.range (fun z : I × V => fun x => Q z.1 (x-z.2)) := by
  let f : (Σ i, Set.range (fun a : V => fun x => Q i (x-a))) →
      Set.range (fun z : I × V => fun x => Q z.1 (x-z.2)) := fun z =>
    ⟨z.2.val,by obtain ⟨a,ha⟩ := z.2.property; exact ⟨(z.1,a),ha⟩⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i,⟨g,a,ha⟩⟩ ⟨j,⟨h,b,hb⟩⟩ he
    have hef : g=h := congrArg Subtype.val he
    have hij : i=j := hinj (polar_eq_of_translated_eq (Q i) (Q j) a b
      (ha.trans (hef.trans hb.symm)))
    subst j
    congr
  · rintro ⟨g,⟨⟨i,a⟩,rfl⟩⟩
    exact ⟨⟨i,⟨_,⟨a,rfl⟩⟩⟩,rfl⟩

/-- An actual constant-rank family with distinct polar forms has the exact translated-function population. -/
theorem translatedFamilyRange_natCard {I : Type*} [Fintype I] [Finite V]
    [Fintype k] [FiniteDimensional k V] (Q : I → QuadraticForm k V)
    (hinj : Function.Injective (fun i => (Q i).polarBilin)) (r : ℕ)
    (hr : ∀ i,Module.finrank k V-Module.finrank k (Q i).radical=r) :
    Nat.card (Set.range (fun z : I × V => fun x => Q z.1 (x-z.2))) =
      Fintype.card I * (Fintype.card k)^r := by
  rw [←Nat.card_congr (translatedFamilyRangeEquiv Q hinj),Nat.card_sigma]
  simp_rw [translatedRange_natCard,hr]
  simp
end BinaryFieldCounterexamples.QuadraticGeometry
