/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.FinitePair
public import BinaryFieldCounterexamples.Counting.TreeSupportCounts
public import BinaryFieldCounterexamples.Agreement.Domains
/-!
# Prescribed-domain assembly for half-agreement trees

The actual support population is the only counting input to this assembly. The
field embedding is the literal subgroup inclusion; all powers, divisions and
input guarantees are converted to the manuscript parameters without changing
the finite collision formula.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem half_agreement_trees_of_population
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (d h : ℕ) (hh : 2≤h) (hd : h+1≤d)
    (hD : (additiveDomain D).card=2^d) (hq : 2^d<Fintype.card F)
    (hpop : (Trees.treeSupportFamily D (h-2)).card=treeSupportCount h d) :
    let N : ℕ := 2^d
    let T : ℕ := N/2
    let K : ℕ := N/2-N/2^(h+1)
    let M : ℕ := treeSupportCount h d
    let E : ℚ := (K:ℚ)*M.choose 2-(N:ℚ)*(M/2).choose 2
    let A := additiveDomain D
    ∃ f g : A → F, commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
      agreementLE A K f (T-1) ∧
      max (M-⌊E/(Fintype.card F-N)⌋₊)
        ⌈(Fintype.card F-N:ℚ)*M^2/((Fintype.card F-N)*M+2*E)⌉₊ ≤
        (nonzeroBadChallenges A K f g T).card := by
  have hDN : Nat.card D=2^d := by rwa [card_additiveDomain] at hD
  have hdim : Module.finrank (ZMod 2) D=d := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hDN] at he
    simp only [Nat.card_eq_fintype_card,ZMod.card] at he
    exact (Nat.pow_right_injective (by decide : 2≤2)) he.symm
  let e : D →ᵃ[ZMod 2] F := (D.subtype.toZModLinearMap 2).toAffineMap
  have he : Function.Injective e := Subtype.val_injective
  have hA : Finset.univ.image e=additiveDomain D := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and,mem_additiveDomain]
    exact ⟨fun ⟨y,hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  have hT : 2^(d-1)=2^d/2 := by
    rw [←Nat.pow_one 2,←Nat.pow_sub_mul_pow 2 (show 1≤d by omega),Nat.mul_div_left _ (by decide : 0<2^1)]
  have hw : 2^(d-((h-2)+3))=2^d/2^(h+1) := by
    rw [show h-2+3=h+1 by omega,←Nat.pow_sub_mul_pow 2 hd,Nat.mul_div_left _ (by positivity)]
  have hp := exists_pair_of_tree_support_family (h-2) d hdim (by omega)
    (by simpa only [Nat.card_eq_fintype_card] using hDN) e he hq
  dsimp only at hp ⊢
  rw [hA] at hp
  simpa only [hpop,hT,hw,Nat.cast_pow,Nat.cast_ofNat] using hp
end BinaryFieldCounterexamples
