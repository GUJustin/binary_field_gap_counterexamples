/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.AffineFlatLocators
public import BinaryFieldCounterexamples.Constructions.Trees.SupportFamily
/-!
# Actual tree-support locators

The proved affine-flat decomposition yields a monic locator for each literal
tree support, including after any injective affine embedding into the challenge
field. Its roots and leading gap are retained, rather than postulated as an
interface assumption.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_locator_of_affine_flat_union
    {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (S : Finset F) (A : ι → AffineSubspace (ZMod 2) F) (m : ℕ)
    (hS : (S : Set F)=⋃ i, (A i : Set F))
    (hne : ∀ i, (A i : Set F).Nonempty) (hcard : ∀ i, Nat.card (A i)=2^(m+1)) :
    ∃ P : F[X], P.Monic ∧ P.natDegree=Fintype.card ι*2^(m+1) ∧
      (∀ x, P.eval x=0 ↔ x∈S) ∧
      (P-X^(Fintype.card ι*2^(m+1))).natDegree≤Fintype.card ι*2^(m+1)-2^m := by
  choose a ha using hne
  have hc (i : ι) : Nat.card (A i).direction=2^(m+1) := by
    rw [←Trees.affineSubspace_card_direction (A i) ⟨a i,ha i⟩,hcard i]
  refine ⟨affineFlatUnionLocator Finset.univ A a, ?_, ?_, ?_, ?_⟩
  · exact monic_prod_of_monic _ _ (fun i hi => affineFlatLocator_monic (A i) (a i))
  · simpa using affineFlatUnionLocator_natDegree Finset.univ A a (2^(m+1)) (fun i hi => hc i)
  · intro x
    rw [affineFlatUnionLocator_eval_eq_zero_iff _ _ _ (fun i hi => ha i)]
    have hs : x∈S ↔ ∃ i, x∈A i := by
      change x∈(S:Set F) ↔ _
      rw [hS,Set.mem_iUnion]
      rfl
    simpa using hs.symm
  · simpa using affineFlatUnionLocator_tail Finset.univ A a m (fun i hi => hc i)

theorem affineSubspace_map_card_of_injective
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module (ZMod 2) V] [Module (ZMod 2) W]
    (A : AffineSubspace (ZMod 2) V) (f : V →ᵃ[ZMod 2] W) (hf : Function.Injective f) :
    Nat.card (A.map f)=Nat.card A := by
  let g : A → A.map f := fun x => ⟨f x,AffineSubspace.mem_map_of_mem f x.property⟩
  have hi : Function.Injective g := by
    intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have hs : Function.Surjective g := by
    intro y
    obtain ⟨x,hx,he⟩ := AffineSubspace.mem_map.mp y.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective g ⟨hi,hs⟩)).symm

theorem exists_locator_of_embedded_flat_union
    {ι V F : Type*} [Fintype ι] [AddCommGroup V] [Module (ZMod 2) V]
    [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (S : Finset V) (A : ι → AffineSubspace (ZMod 2) V) (m : ℕ)
    (f : V →ᵃ[ZMod 2] F) (hf : Function.Injective f)
    (hS : (S : Set V)=⋃ i, (A i : Set V))
    (hne : ∀ i, (A i : Set V).Nonempty) (hcard : ∀ i, Nat.card (A i)=2^(m+1)) :
    ∃ P : F[X], P.Monic ∧ P.natDegree=Fintype.card ι*2^(m+1) ∧
      (∀ x, P.eval x=0 ↔ x∈S.image f) ∧
      (P-X^(Fintype.card ι*2^(m+1))).natDegree≤Fintype.card ι*2^(m+1)-2^m := by
  apply exists_locator_of_affine_flat_union (S.image f) (fun i => (A i).map f) m
  · simp only [Finset.coe_image,AffineSubspace.coe_map,hS,Set.image_iUnion]
  · intro i
    obtain ⟨x,hx⟩ := hne i
    exact ⟨f x,AffineSubspace.mem_map_of_mem f hx⟩
  · intro i
    rw [affineSubspace_map_card_of_injective (A i) f hf,hcard i]

theorem exists_tree_support_locator
    {V F : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (n d : ℕ) (hdim : Module.finrank (ZMod 2) V=d) (hd : n+3≤d)
    (f : V →ᵃ[ZMod 2] F) (hf : Function.Injective f)
    (S : Finset V) (hS : S∈Trees.treeSupportFamily V n) :
    ∃ P : F[X], P.Monic ∧ P.natDegree=2^(d-1) ∧
      (∀ x, P.eval x=0 ↔ x∈S.image f) ∧
      (P-X^(2^(d-1))).natDegree≤2^(d-1)-2^(d-(n+3)) := by
  obtain ⟨A,hA,hdis,hcard⟩ := Trees.treeSupportFamily_flats n S hS
  have hc (i) : Nat.card (A i)=2^((d-(n+3))+1) := by
    rw [(hcard i).2,hdim]
    congr 1
    omega
  have he : Fintype.card (Fin (n+1) → ZMod 2)*2^((d-(n+3))+1)=2^(d-1) := by
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card]
    rw [←pow_add]
    congr 1
    omega
  simpa only [he] using exists_locator_of_embedded_flat_union S A (d-(n+3)) f hf hA
    (fun i => (hcard i).1) hc
end BinaryFieldCounterexamples
