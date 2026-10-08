/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.SeedList
public import BinaryFieldCounterexamples.Agreement.Domains
public import Mathlib.FieldTheory.Finite.GaloisField
/-!
# Dense seeds on arbitrary affine additive domains

The prescribed cardinality identity fixes the binary dimension and restriction
rank loss. An actual embedding of the scalar Galois field into the given binary
field supplies the scalar algebra and tower. Thus the Gaussian list count,
strict degree, and uniform agreement estimate apply to every field and affine
additive domain in the dense construction, with no subfield-existence premise.
-/
@[expose] public section
set_option linter.unusedSectionVars false
namespace BinaryFieldCounterexamples.DenseConstruction
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k B : Type*} [Field k] [Fintype k] [CharP k 2]
  [Field B] [Fintype B] [CharP B 2] [Algebra k B]
  [Algebra (ZMod 2) k] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) k B]
/-- The concrete codimension identity determines both binary dimensions. -/
theorem affine_binary_dimensions (ell n c : ℕ) (hq : Fintype.card k=2^ell)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (D : AddSubgroup B)
    (hD : (additiveDomain D).card*2^c=Fintype.card B) :
    Module.finrank (ZMod 2) B=ell*(2*n) ∧
      Module.finrank (ZMod 2) (AddSubgroup.toZModSubmodule 2 D)+c=ell*(2*n) := by
  have hBpow := Module.card_eq_pow_finrank (K:=ZMod 2) (V:=B)
  simp only [ZMod.card,hcard,hq,←pow_mul] at hBpow
  have hBdim := Nat.pow_right_injective (by decide : 1<2) hBpow
  refine ⟨hBdim.symm,?_⟩
  let W:=AddSubgroup.toZModSubmodule 2 D
  have hWpow : Nat.card W=2^Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_eq_fintype_card,ZMod.card]
  have hWcard : Nat.card W=(additiveDomain D).card := by rw [card_additiveDomain]; rfl
  rw [←hWcard,hWpow,hcard,hq,←pow_mul,←pow_add] at hD
  exact Nat.pow_right_injective (by decide : 1<2) hD
/-- Actual seed lists on every prescribed affine additive domain, with the
binary rank-loss parameters fixed by its codimension. -/
theorem additive_dense_trace_seed_list (ell n t c : ℕ) (hell : 1≤ell)
    (hq : Fintype.card k=2^ell) (ht : 1≤t) (htn : t≤n) (hc : c<ell)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (D : AddSubgroup B) (v : B) (hD : (additiveDomain D).card*2^c=Fintype.card B) :
    let S:=affineDomain (additiveDomain D) v
    ∃(w:S→B)(E:Finset B[X]),
      (Fintype.card k:ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) n t/(Fintype.card k-1)≤E.card ∧
      ∀f∈E,f.degree<(Fintype.card k)^(2*n-2) ∧
        (S.card:ℝ)/(Fintype.card k:ℝ)-
          ((Fintype.card k-1:ℕ):ℝ)*(2^(ell*(2*n-t)):ℕ)/(Fintype.card k:ℝ)≤
          (agreementCount S w f:ℝ) := by
  let W:=AddSubgroup.toZModSubmodule 2 D
  obtain ⟨hdB,hdW⟩:=affine_binary_dimensions ell n c hq hcard D hD
  have hgain : c≤ell*t := by nlinarith
  have hbin : 2*(ell*t-c)+2*c≤ell*(2*t) := by
    have hh:=Nat.sub_add_cancel hgain
    linarith
  obtain ⟨w,E,hE,hprop⟩:=QuadraticFormTrace.dense_trace_seed_list ell hell hq n t ht htn
    hcard W v c (ell*(2*n)-c) (ell*t-c) (by dsimp only [W]; omega) (by dsimp only [W]; omega) hbin
  refine ⟨w,E,hE,?_⟩
  have hS : (affineDomain (additiveDomain D) v).card=Nat.card W := by
    rw [affineDomain,Finset.card_image_iff.mpr (by
      intro x hx y hy hxy
      exact add_right_cancel hxy),card_additiveDomain]
    rfl
  have hexp : ell*(2*n)-c-(ell*t-c)=ell*(2*n-t) := by
    have htprod : ell*t≤ell*(2*n) := Nat.mul_le_mul_left ell (by omega)
    rw [Nat.mul_sub_left_distrib]
    omega
  intro f hf
  simpa only [hS,hexp,W,AddSubgroup.toZModSubmodule_toAddSubgroup] using hprop f hf
end BinaryFieldCounterexamples.DenseConstruction
namespace BinaryFieldCounterexamples.DenseConstruction
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
/-- Every binary field with the required size contains an actual scalar field of
size `2^ell`; hence the seed list is uniform over all prescribed affine domains. -/
theorem binary_dense_seed_list
    (ell n t c : ℕ) (hell : 1≤ell) (ht : 1≤t) (htn : t≤n) (hc : c<ell)
    (B : Type*) [Field B] [Fintype B] [CharP B 2]
    (hcard : Fintype.card B=(2^ell)^(2*n))
    (D : AddSubgroup B) (v : B) (hD : (additiveDomain D).card*2^c=Fintype.card B) :
    let S:=affineDomain (additiveDomain D) v
    ∃(w:S→B)(E:Finset B[X]),
      ((2^ell:ℕ):ℚ)^(2*t)*(((2^ell:ℕ):ℚ)^t-1)*
        quadraticGaussian ((2^ell)^2) n t/((2^ell:ℕ)-1)≤E.card ∧
      ∀f∈E,f.degree<(2^ell:ℕ)^(2*n-2) ∧
        (S.card:ℝ)/(2^ell:ℕ)-
          (((2^ell:ℕ)-1:ℕ):ℝ)*(2^(ell*(2*n-t)):ℕ)/(2^ell:ℕ)≤
          (agreementCount S w f:ℝ) := by
  let k:=GaloisField 2 ell
  let : Fintype k:=Fintype.ofFinite k
  let : Algebra (ZMod 2) k:=ZMod.algebra k 2
  let : Algebra (ZMod 2) B:=ZMod.algebra B 2
  have hkcard : Fintype.card k=2^ell := by
    rw [←Nat.card_eq_fintype_card]
    exact GaloisField.card 2 ell (by omega)
  have hkdim : Module.finrank (ZMod 2) k=ell := by
    have hh:=Module.card_eq_pow_finrank (K:=ZMod 2) (V:=k)
    simp only [ZMod.card,hkcard] at hh
    exact (Nat.pow_right_injective (by decide : 1<2) hh).symm
  have hBdim : Module.finrank (ZMod 2) B=ell*(2*n) := by
    have hh:=Module.card_eq_pow_finrank (K:=ZMod 2) (V:=B)
    simp only [ZMod.card,hcard,←pow_mul] at hh
    exact (Nat.pow_right_injective (by decide : 1<2) hh).symm
  obtain ⟨f⟩:=FiniteField.nonempty_algHom_of_finrank_dvd (F:=ZMod 2) (K:=k) (L:=B)
    (by rw [hkdim,hBdim]; exact dvd_mul_right _ _)
  let : Algebra k B:=f.toRingHom.toAlgebra
  let : IsScalarTower (ZMod 2) k B:=IsScalarTower.of_algHom f
  simpa only [hkcard] using additive_dense_trace_seed_list (k:=k) ell n t c hell hkcard ht htn hc
    (by simpa only [hkcard] using hcard) D v hD
end BinaryFieldCounterexamples.DenseConstruction
