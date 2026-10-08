/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.ClassificationHighAgreement
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.ClassificationExactRoots
public import BinaryFieldCounterexamples.Polynomial.Map
/-!
# Exact agreement profile of the quadratic received line

Every strict-degree explaining polynomial with more than `2K` agreements has exactly
`4K-1` agreements and its challenge is that of a size-`4K` subgroup. Consequently
all intermediate thresholds have precisely the same existential subgroup
classification, while every challenge has agreement at most `4K-1`.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial QuadraticConstruction
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A particular strict-degree explaining polynomial above the classification threshold
has exactly `4K-1` agreements and a canonical subgroup challenge. -/
theorem quadratic_high_agreement_count
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [CharP F 2]
    (φ : B →+* F) (θ : F) (hθ : θ∉Set.range φ)
    (D : AddSubgroup B) (K : ℕ) (hK : 2≤K)
    (hpow : ∃ k : ℕ, K=2^k) (hD : (additiveDomain D).card=16*K)
    (z : F) (p : F[X]) (hp : p.degree<K)
    (hcount : 2*K<agreementCount (mappedDomain φ (additiveDomain D))
      (fun x => firstWord K θ x+z*secondWord K (x:F)) p) :
    ∃ W : AddSubgroup B, W≤D ∧ Nat.card W=4*K ∧
      z=finiteLocatorLabel φ θ K W ∧
      agreementCount (mappedDomain φ (additiveDomain D))
        (fun x => firstWord K θ x+z*secondWord K (x:F)) p=4*K-1 := by
  let S := (additiveDomain D).filter fun x =>
    p.eval (φ x)=firstWord K θ (φ x)+z*secondWord K (φ x)
  have hcard : agreementCount (mappedDomain φ (additiveDomain D))
      (fun x => firstWord K θ x+z*secondWord K (x:F)) p=S.card :=
    agreementCount_mappedDomain φ (additiveDomain D)
      (fun x => firstWord K θ x+z*secondWord K x) p
  have hSD : S⊆additiveDomain D := Finset.filter_subset _ _
  have hS : 2*K<S.card := by rwa [hcard] at hcount
  have heval : ∀ x ∈ S, p.eval (φ x)=
      (φ x)^(8*K-1)+θ*(φ x)^(4*K-1)+z*(φ x)^(2*K-1) := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  obtain ⟨W,hWD,hWcard,hlabel,hid⟩ := quadratic_classification_of_high_agreement
    φ θ hθ D K hK hpow hD S hSD hS p hp z heval
  have hexact := quadratic_classification_exact_agreement φ θ hθ W K hK
    (locatorCoeffA W K) z p hid
  have hset : S=(additiveDomain W).erase 0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxW,hx0⟩ := (hexact x).mp ((Finset.mem_filter.mp hx).2)
      exact Finset.mem_erase.mpr ⟨hx0,(mem_additiveDomain W x).mpr hxW⟩
    · intro hx
      obtain ⟨hx0,hxW⟩ := Finset.mem_erase.mp hx
      have hxW' := (mem_additiveDomain W x).mp hxW
      exact Finset.mem_filter.mpr ⟨(mem_additiveDomain D x).mpr (hWD hxW'),
        (hexact x).mpr ⟨hxW',hx0⟩⟩
  refine ⟨W,hWD,?_,?_,?_⟩
  · simpa only [Nat.card_eq_fintype_card] using hWcard
  · have hinst : (Fintype.ofFinite W : Fintype W)=(inferInstance : Fintype W) := Subsingleton.elim _ _
    change z=@locatorLabel B F _ _ φ θ W (Fintype.ofFinite W) K
    rw [hinst]
    exact hlabel
  · rw [hcard,hset,Finset.card_erase_of_mem ((mem_additiveDomain W 0).mpr W.zero_mem),
      card_additiveDomain,Nat.card_eq_fintype_card,hWcard]

/-- Every challenge on the fixed unshifted line has maximum agreement
at most `4K-1`; the statement quantifies every strict-degree polynomial. -/
theorem quadratic_combination_agreementLE
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [CharP F 2]
    (φ : B →+* F) (θ : F) (hθ : θ∉Set.range φ)
    (D : AddSubgroup B) (K : ℕ) (hK : 2≤K)
    (hpow : ∃ k : ℕ, K=2^k) (hD : (additiveDomain D).card=16*K) :
    ∀ z : F, agreementLE (mappedDomain φ (additiveDomain D)) K
      (fun x => firstWord K θ x+z*secondWord K (x:F)) (4*K-1) := by
  intro z p hp
  by_cases hhigh : 2*K<agreementCount (mappedDomain φ (additiveDomain D))
      (fun x => firstWord K θ x+z*secondWord K (x:F)) p
  · obtain ⟨W,_,_,_,heq⟩ := quadratic_high_agreement_count φ θ hθ D K hK hpow hD z p hp hhigh
    exact heq.le
  · omega

/-- Every integer threshold strictly above `2K` and at most `4K-1` has
exactly the same subgroup-challenge classification on the fixed received line. -/
theorem quadratic_combination_agreementGE_iff_subgroup
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (θ : F) (hθ : θ∉Set.range φ)
    (D : AddSubgroup B) (K : ℕ) (hK : 2≤K)
    (hpow : ∃ k : ℕ, K=2^k) (hD : (additiveDomain D).card=16*K)
    (z : F) (T : ℕ) (hTlow : 2*K+1≤T) (hThigh : T≤4*K-1) :
    agreementGE (mappedDomain φ (additiveDomain D)) K
      (fun x => firstWord K θ x+z*secondWord K (x:F)) T ↔
    ∃ W : AddSubgroup B, W≤D ∧ Nat.card W=4*K ∧ z=finiteLocatorLabel φ θ K W := by
  constructor
  · rintro ⟨p,hp,hcount⟩
    obtain ⟨W,hWD,hWcard,hlabel,_⟩ := quadratic_high_agreement_count φ θ hθ D K hK hpow hD
      z p hp (by omega)
    exact ⟨W,hWD,hWcard,hlabel⟩
  · rintro ⟨W,hWD,hWcard,rfl⟩
    let : Fintype W := Fintype.ofFinite W
    let E := mappedDomain φ (additiveDomain D)
    let WF := W.map φ.toAddMonoidHom
    have hWFcard : Nat.card WF=4*K := (natCard_map_addSubgroup φ W).trans hWcard
    have hWFE : ∀ x ∈ WF, x ∈ E := by
      rintro x ⟨y,hy,rfl⟩
      exact Finset.mem_image.mpr ⟨y,(mem_additiveDomain D y).mpr (hWD hy),rfl⟩
    have hbad := bad_challenge_of_subgroup E WF hWFE K hK hpow hWFcard θ 0
    have hbad' : finiteLocatorLabel φ θ K W ∈ badChallenges E K
        (fun x => firstWord K θ x) (fun x => secondWord K (x:F)) (4*K-1) := by
      simpa only [WF,coeff_subspacePolynomial_map,finiteLocatorLabel,locatorLabel,
        locatorCoeffA,locatorCoeffB,map_add,map_pow,zero_mul,add_zero] using hbad
    rw [mem_badChallenges] at hbad'
    obtain ⟨p,hp,hcount⟩ := hbad'
    exact ⟨p,hp,hThigh.trans hcount⟩

end BinaryFieldCounterexamples
