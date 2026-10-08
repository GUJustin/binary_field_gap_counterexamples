/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.ExteriorIncidence
public import BinaryFieldCounterexamples.Constructions.NormalizedPoleReduction
/-!
# Pole pairs from support incidence

Actual common roots reduce the exterior collision budget. The resulting rational
energy keeps the full incidence correction and supplies both challenge-count
bounds for a single pair with the stated individual and common-agreement guarantees.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators

theorem exterior_collision_rational_energy
    {ι F : Type*} [LinearOrder ι] [Field F] [Fintype F] [DecidableEq F]
    (I : Finset ι) (D : Finset F) (S : ι → Finset F) (P : ι → Polynomial F) (K : ℕ)
    (hS : ∀ i ∈ I, S i ⊆ D) (hroot : ∀ i ∈ I, ∀ x ∈ S i, (P i).eval x=0)
    (hinj : Set.InjOn P I)
    (hdeg : ∀ i ∈ I, ∀ j ∈ I, i≠j → (P i-P j).natDegree≤K) :
    (∑ β ∈ Finset.univ \ D, (unorderedCollisionCount I (fun i => (P i).eval β) : ℚ)) ≤
      (K : ℚ)*I.card.choose 2 - ∑ x ∈ D, (((I.filter fun i => x ∈ S i).card).choose 2 : ℚ) := by
  have h := sum_exterior_collisions_add_incidence_le I D S P K hS hroot hinj hdeg
  have hc : (∑ β ∈ Finset.univ \ D, (unorderedCollisionCount I (fun i => (P i).eval β) : ℚ)) +
      (∑ x ∈ D, (((I.filter fun i => x ∈ S i).card).choose 2 : ℚ)) ≤
      (K : ℚ)*I.card.choose 2 := by exact_mod_cast h
  linarith

attribute [local instance] Classical.propDecidable Classical.decEq
theorem exists_normalizedPolePair_of_support_incidence
    {ι F : Type*} [LinearOrder ι] [Field F] [Fintype F]
    (I : Finset ι) (D : Finset F) (S : ι → Finset F) (R : Polynomial F)
    (P : ι → Polynomial F) (K T : ℕ)
    (hq : D.card<Fintype.card F) (hK : K≤D.card)
    (hR : 0<R.natDegree) (hKR : K≤R.natDegree-1)
    (hS : ∀ i ∈ I, S i ⊆ D) (hsize : ∀ i ∈ I, T≤(S i).card)
    (hroot : ∀ i ∈ I, ∀ x, (P i).eval x=0 ↔ x∈S i)
    (hinj : Set.InjOn P I) (hdeg : ∀ i ∈ I, (P i-R).degree≤K) :
    let energy : ℚ := (K : ℚ)*I.card.choose 2 -
      ∑ x ∈ D, (((I.filter fun i => x ∈ S i).card).choose 2 : ℚ)
    ∃ f g : D → F, commonAgreementEQ D K f g K ∧ agreementEQ D K g K ∧
      agreementLE D K f (R.natDegree-1) ∧
      max (I.card-⌊energy/(Fintype.card F-D.card)⌋₊)
        ⌈(Fintype.card F-D.card : ℚ)*I.card^2/
          ((Fintype.card F-D.card)*I.card+2*energy)⌉₊≤(nonzeroBadChallenges D K f g T).card := by
  dsimp only
  apply exists_normalizedPolePair_of_collision_budget I D R P K T _ hq hK hR hKR hdeg
  · intro i hi
    apply (hsize i hi).trans
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_filter.mpr ⟨hS i hi hx,(hroot i hi x).mpr hx⟩
  · intro β hβ i hi he
    exact hβ (hS i hi ((hroot i hi β).mp he))
  · apply exterior_collision_rational_energy I D S P K hS
      (fun i hi x hx => (hroot i hi x).mpr hx) hinj
    intro i hi j hj hij
    have he : P i-P j=(P i-R)-(P j-R) := by ring
    rw [he]
    apply Polynomial.natDegree_le_of_degree_le
    exact (Polynomial.degree_sub_le _ _).trans (max_le (hdeg i hi) (hdeg j hj))
end BinaryFieldCounterexamples
