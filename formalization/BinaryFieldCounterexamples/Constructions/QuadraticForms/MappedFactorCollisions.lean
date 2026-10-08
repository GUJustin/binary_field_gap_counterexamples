/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.FactorTransport

/-!
# Collision bounds after extending the locator field

Sparse conversion factors retain their saturated domain root sets after a field
embedding. Consequently every pair of distinct mapped locators has the same
sharp exterior collision bound as over the base field.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticLocatorConversion
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Distinct sparse converted locators collide at no more than `(b-1)δ`
points outside the mapped evaluation domain. -/
theorem card_mapped_locator_collision_le
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F]
    (φ : B→+*F) (p r b s δ : ℕ) [Fact p.Prime] [CharP B p] [CharP F p]
    (hb : b=p^r) (hb2 : 2≤b)
    (D : Finset B) (L A₁ A₂ P₁ P₂ : B[X])
    (hL : ∀ x∈D,L.eval x=0)
    (hLoutside : ∀ x∉mappedDomain φ D,(L.map φ).eval x≠0)
    (hconv₁ : A₁^(b-1)*(P₁^b-L)=P₁)
    (hconv₂ : A₂^(b-1)*(P₂^b-L)=P₂)
    (hP : P₁≠P₂)
    (hA₁pos : 0<A₁.natDegree) (hA₂pos : 0<A₂.natDegree)
    (hsupp₁ : ∀ e∈A₁.support,p^(r*s)∣e)
    (hsupp₂ : ∀ e∈A₂.support,p^(r*s)∣e)
    (hdeg₁ : A₁.natDegree≤p^(r*s)*δ)
    (hdeg₂ : A₂.natDegree≤p^(r*s)*δ)
    (hzeros₁ : (D.filter fun x => A₁.eval x=0).card=δ) :
    (((Finset.univ\mappedDomain φ D).filter fun x =>
      (P₁.map φ).eval x=(P₂.map φ).eval x).card)≤(b-1)*δ := by
  have hA₁ : A₁≠0 := fun hz => by rw [hz,natDegree_zero] at hA₁pos; omega
  have hA₂ : A₂≠0 := fun hz => by rw [hz,natDegree_zero] at hA₂pos; omega
  have hrootBound (A : B[X]) (hA : A≠0)
      (hsupp : ∀ e∈A.support,p^(r*s)∣e)
      (hdeg : A.natDegree≤p^(r*s)*δ) :
      (A.map φ).roots.toFinset.card≤δ := by
    apply card_roots_le_of_primePower_support p (r*s) (A.map φ)
      (by simpa using (Polynomial.map_injective φ φ.injective).ne hA)
    · exact map_factor_support_dvd φ A _ hsupp
    · rw [natDegree_map]
      exact hdeg
  have hAroots (A : B[X]) (hA : A≠0)
      (hsupp : ∀ e∈A.support,p^(r*s)∣e)
      (hdeg : A.natDegree≤p^(r*s)*δ)
      (hzeros : (D.filter fun x => A.eval x=0).card=δ) :
      ∀ x,(A.map φ).IsRoot x→(L.map φ).IsRoot x := by
    let S := (mappedDomain φ D).filter fun x => (A.map φ).eval x=0
    apply factor_isRoot_domain_of_saturated_roots (A.map φ) (L.map φ) S δ
      (by simpa using (Polynomial.map_injective φ φ.injective).ne hA)
    · dsimp only [S]
      rw [card_mapped_factor_zeros,hzeros]
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · exact hrootBound A hA hsupp hdeg
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (show x∈mappedDomain φ D from
        (Finset.mem_filter.mp hx).1)
      change (L.map φ).eval (φ y)=0
      rw [eval_map,eval₂_at_apply]
      exact (map_eq_zero φ).2 (hL y hy)
  have houtside₁ : ∀ x∉mappedDomain φ D,(P₁.map φ).eval x≠0 := by
    intro x hx
    exact converted_eval_ne_zero_of_factor_roots (A₁.map φ) (P₁.map φ)
      (L.map φ) b hb2 (map_factor_conversion φ A₁ P₁ L b hconv₁)
      (hAroots A₁ hA₁ hsupp₁ hdeg₁ hzeros₁) x (hLoutside x hx)
  apply card_locator_collision_le_of_factor_differences (mappedDomain φ D)
    (A₁.map φ) (A₂.map φ) (P₁.map φ) (P₂.map φ) (L.map φ) b δ hb2
    (map_factor_conversion φ A₁ P₁ L b hconv₁)
    (map_factor_conversion φ A₂ P₂ L b hconv₂) houtside₁
  intro ζ hζ
  have hne : A₁.map φ-C ζ*(A₂.map φ)≠0 := by
    intro hz
    have hscale : A₁.map φ=C ζ*(A₂.map φ) := sub_eq_zero.mp hz
    have hpeq := locator_eq_of_factor_eq_rootOfUnity_smul p r b hb hb2
      (A₁.map φ) (A₂.map φ) (P₁.map φ) (P₂.map φ) (L.map φ) ζ
      (map_factor_conversion φ A₁ P₁ L b hconv₁)
      (map_factor_conversion φ A₂ P₂ L b hconv₂) hζ hscale (by rwa [natDegree_map])
    exact hP ((Polynomial.map_injective φ φ.injective) hpeq)
  refine ⟨hne,factor_difference_roots_card_le p r s δ (A₁.map φ)
    (A₂.map φ) ζ (map_factor_support_dvd φ A₁ _ hsupp₁)
    (map_factor_support_dvd φ A₂ _ hsupp₂) hne ?_⟩
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · rwa [natDegree_map]
  · exact (natDegree_C_mul_le ζ (A₂.map φ)).trans (by rwa [natDegree_map])

end BinaryFieldCounterexamples.QuadraticLocatorConversion
