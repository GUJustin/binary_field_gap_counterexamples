/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingRadicals
public import BinaryFieldCounterexamples.Constructions.Gold.PairWitnesses
/-!
# Concrete Gold witnesses kept for additive padding

The normalized pole challenges are selected before forgetting their polynomial
representatives. Their witnesses have the stronger strict degree bound, and
their agreement sets are exactly the mapped locator roots, not merely subsets.
Each selected nonzero challenge therefore comes with a concrete agreement set on the
original additive space, its exact size, and an invariant radical of exact size.
This interface preserves the data needed by the subspace-retention argument.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq
/-- The pole witness has exactly the locator's root agreement set, with no extra agreement points. -/
theorem poleCorrection_agreement_iff_root {F : Type*} [Field F]
    (R C : F[X]) (β x : F) (hx : x≠β) :
    R.eval x*(x-β)⁻¹+C.eval β*(x-β)⁻¹=(poleCorrection C β).eval x ↔
      (R+C).eval x=0 := by
  rw [poleCorrection_eval C β x hx,eval_add]
  have hden : x-β≠0 := sub_ne_zero.mpr hx
  constructor
  · intro he
    field_simp at he
    linear_combination he
  · intro he
    field_simp
    linear_combination he
/-- Distinct nonzero pole challenges keep concrete locators, strict witnesses, and exact root agreement sets. -/
theorem exists_nonzero_locator_label_witnesses
    {B F : Type*} [Field B] [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) [Fintype (D.map φ.toAddMonoidHom)]
    (ps : Finset B[X]) (β : F) (hβ : β ∉ D.map φ.toAddMonoidHom) (J : ℕ)
    (hdegree : ∀ P ∈ ps, (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).degree≤J) :
    ∃ Z : Finset F, (locatorValues φ ps β).card-1≤Z.card ∧
      ∀ z ∈ Z, z≠0 ∧ ∃ P ∈ ps,
        z=(P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval β ∧
        (poleCorrection (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β) β).degree<J ∧
        ∀ x : D,
          (binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval (φ (x:B))*(φ (x:B)-β)⁻¹+
            z*(φ (x:B)-β)⁻¹=
            (poleCorrection (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β) β).eval (φ (x:B)) ↔
            P.eval (x:B)=0 := by
  classical
  let R := binaryQuarterNumerator (D.map φ.toAddMonoidHom) β
  let Zall := ps.image fun P => (P.map φ+R).eval β
  have hcard : Zall.card=(locatorValues φ ps β).card := by
    have he : Zall=(locatorValues φ ps β).image (fun z => z+R.eval β) := by
      simp only [Zall,locatorValues,Finset.image_image,eval_add]
      rfl
    rw [he,Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
  refine ⟨Zall.erase 0,?_,?_⟩
  · by_cases hz : 0 ∈ Zall
    · rw [Finset.card_erase_of_mem hz,hcard]
    · rw [Finset.erase_eq_of_notMem hz,hcard]
      omega
  · intro z hz
    obtain ⟨hne,hz⟩ := Finset.mem_erase.mp hz
    obtain ⟨P,hP,hz⟩ := Finset.mem_image.mp hz
    refine ⟨hne,P,hP,hz.symm,poleCorrection_degree_lt _ β J (hdegree P hP),?_⟩
    intro x
    have hx : φ (x:B)≠β := by
      intro he
      apply hβ
      rw [←he]
      exact ⟨(x:B),x.property,rfl⟩
    rw [←hz,poleCorrection_agreement_iff_root R (P.map φ+R) β (φ (x:B)) hx]
    have he : R+(P.map φ+R)=P.map φ := by
      rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
    rw [he,eval_map_apply,map_eq_zero]
/-- A family whose normalized challenges exclude zero keeps its entire image and every concrete witness. -/
theorem exists_nonzero_locator_label_witnesses_no_loss
    {B F : Type*} [Field B] [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) [Fintype (D.map φ.toAddMonoidHom)]
    (ps : Finset B[X]) (β : F) (hβ : β ∉ D.map φ.toAddMonoidHom) (J : ℕ)
    (hdegree : ∀ P ∈ ps, (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).degree≤J)
    (hlabel : ∀ P ∈ ps, (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval β≠0) :
    ∃ Z : Finset F, (locatorValues φ ps β).card≤Z.card ∧
      ∀ z ∈ Z, z≠0 ∧ ∃ P ∈ ps,
        z=(P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval β ∧
        (poleCorrection (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β) β).degree<J ∧
        ∀ x : D,
          (binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval (φ (x:B))*(φ (x:B)-β)⁻¹+
            z*(φ (x:B)-β)⁻¹=
            (poleCorrection (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β) β).eval (φ (x:B)) ↔
            P.eval (x:B)=0 := by
  classical
  let R := binaryQuarterNumerator (D.map φ.toAddMonoidHom) β
  let Zall := ps.image fun P => (P.map φ+R).eval β
  have hcard : Zall.card=(locatorValues φ ps β).card := by
    have he : Zall=(locatorValues φ ps β).image (fun z => z+R.eval β) := by
      simp only [Zall,locatorValues,Finset.image_image,eval_add]
      rfl
    rw [he,Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
  refine ⟨Zall,by rw [hcard],?_⟩
  · intro z hz
    obtain ⟨P,hP,hz⟩ := Finset.mem_image.mp hz
    have hne : z≠0 := hz ▸ hlabel P hP
    refine ⟨hne,P,hP,hz.symm,poleCorrection_degree_lt _ β J (hdegree P hP),?_⟩
    intro x
    have hx : φ (x:B)≠β := by
      intro he
      apply hβ
      rw [←he]
      exact ⟨(x:B),x.property,rfl⟩
    rw [←hz,poleCorrection_agreement_iff_root R (P.map φ+R) β (φ (x:B)) hx]
    have he : R+(P.map φ+R)=P.map φ := by
      rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
    rw [he,eval_map_apply,map_eq_zero]
/-- The concrete Gold pool yields distinct nonzero challenges with exact radical-invariant agreement sets and the stronger strict message degree. -/
theorem exists_gold_padding_witnesses
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] [Fintype (D.map φ.toAddMonoidHom)]
    (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) (ht0 : 2≤t) (ht : 2*t≤k+1)
    (ps : Finset B[X])
    (hps : ∀ P ∈ ps, ∃ A ∈ momentTensors D v t, ∃ l : D →+ ZMod 2, ∃ κ : ZMod 2,
      P=repairedLocator D v A l κ t ∧
        Nat.card {y : D // tensorQuadraticFunction D v A y+l y+κ=0}=2^k+2^(k-t))
    (β : F) (hβ : β ∉ D.map φ.toAddMonoidHom) :
    ∃ Z : Finset F, (locatorValues φ ps β).card-1≤Z.card ∧
      ∀ z ∈ Z, z≠0 ∧ ∃ p : F[X], p.degree<(2^(k-1)-2^(k-t-1) : ℕ) ∧
        ∃ H : Submodule (ZMod 2) D, Nat.card H=2^(k+1-2*t) ∧
          ∃ S : Finset D, S.card=2^k-2^(k-t) ∧
            (∀ x : D, ∀ h : H, x+(h:D) ∈ S ↔ x ∈ S) ∧
            ∀ x : D,
              (binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval (φ (x:B))*(φ (x:B)-β)⁻¹+
                z*(φ (x:B)-β)⁻¹=p.eval (φ (x:B)) ↔ x ∈ S := by
  have hdegree (P : B[X]) (hP : P ∈ ps) :
      (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).degree≤
        (2^(k-1)-2^(k-t-1) : ℕ) := by
    obtain ⟨A,hA,l,κ,hPeq,hzero⟩ := hps P hP
    obtain ⟨hr,hM⟩ := (mem_momentTensors D v t A).mp hA
    have hp := (repairedLocator_properties D k hD v A l κ t ht0 ht hM hr hzero).2.2.1
    have htail : (P+goldSourcePolynomial D k).natDegree≤2^(k-1)-2^(k-t-1) := by rw [hPeq,hp]
    exact degree_le_natDegree.trans (by exact_mod_cast mapped_gold_correction_natDegree_le φ D k t ht0 ht hD P htail β)
  obtain ⟨Z,hZ,hdata⟩ := exists_nonzero_locator_label_witnesses φ D ps β hβ
    (2^(k-1)-2^(k-t-1)) hdegree
  refine ⟨Z,hZ,?_⟩
  intro z hz
  obtain ⟨hne,P,hP,hzP,hp,hmatch⟩ := hdata z hz
  obtain ⟨A,hA,l,κ,hPeq,hzero⟩ := hps P hP
  obtain ⟨hr,hM⟩ := (mem_momentTensors D v t A).mp hA
  let H := (tensorQuadraticData D v A).radical
  let S : Finset D := Finset.univ.filter fun x : D => P.eval (x:B)=0
  refine ⟨hne,_,hp,H,cardinal_tensorQuadraticData_radical D (k+1) hD v A t ht hr,S,?_,?_,?_⟩
  · have hc := (repairedLocator_properties D k hD v A l κ t ht0 ht hM hr hzero).2.2.2.1
    change (Finset.univ.filter fun x : D => P.eval (x:B)=0).card=_
    rw [←Fintype.card_subtype]
    simpa only [Nat.card_eq_fintype_card,hPeq] using hc
  · intro x h
    change x+(h:D) ∈ Finset.univ.filter (fun x : D => P.eval (x:B)=0) ↔ x ∈ _
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hPeq]
    exact repairedLocator_roots_add_radical D k hD v A l κ t ht0 ht hM hr hzero x h
  · intro x
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hmatch x
/-- The complete Gold image remains after normalization, keeping exact radical-invariant witness sets. -/
theorem exists_gold_padding_witnesses_no_loss
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] [Fintype (D.map φ.toAddMonoidHom)]
    (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) (ht0 : 2≤t) (ht : 2*t≤k+1)
    (ps : Finset B[X])
    (hps : ∀ P ∈ ps, ∃ A ∈ momentTensors D v t, ∃ l : D →+ ZMod 2, ∃ κ : ZMod 2,
      P=repairedLocator D v A l κ t ∧
        Nat.card {y : D // tensorQuadraticFunction D v A y+l y+κ=0}=2^k+2^(k-t))
    (β : F) (hβ : β ∉ D.map φ.toAddMonoidHom) :
    ∃ Z : Finset F, (locatorValues φ ps β).card≤Z.card ∧
      ∀ z ∈ Z, z≠0 ∧ ∃ p : F[X], p.degree<(2^(k-1)-2^(k-t-1) : ℕ) ∧
        ∃ H : Submodule (ZMod 2) D, Nat.card H=2^(k+1-2*t) ∧
          ∃ S : Finset D, S.card=2^k-2^(k-t) ∧
            (∀ x : D, ∀ h : H, x+(h:D) ∈ S ↔ x ∈ S) ∧
            ∀ x : D,
              (binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval (φ (x:B))*(φ (x:B)-β)⁻¹+
                z*(φ (x:B)-β)⁻¹=p.eval (φ (x:B)) ↔ x ∈ S := by
  have hdegree (P : B[X]) (hP : P ∈ ps) :
      (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).degree≤
        (2^(k-1)-2^(k-t-1) : ℕ) := by
    obtain ⟨A,hA,l,κ,hPeq,hzero⟩ := hps P hP
    obtain ⟨hr,hM⟩ := (mem_momentTensors D v t A).mp hA
    have hp := (repairedLocator_properties D k hD v A l κ t ht0 ht hM hr hzero).2.2.1
    have htail : (P+goldSourcePolynomial D k).natDegree≤2^(k-1)-2^(k-t-1) := by rw [hPeq,hp]
    exact degree_le_natDegree.trans (by exact_mod_cast mapped_gold_correction_natDegree_le φ D k t ht0 ht hD P htail β)
  have hlabel (P : B[X]) (hP : P∈ps) :
      (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval β≠0 := by
    let D' := D.map φ.toAddMonoidHom
    let E := additiveDomain D'
    let R := binaryQuarterNumerator D' β
    have hcD : Nat.card D'=2^(k+1) := by rw [natCard_map_addSubgroup,hD]
    have hsource := (binaryQuarterPair_source_bounds D' β hβ k (by omega) hcD).2.2
    have hzero := zero_not_mem_badChallenges_of_source_gap E (2^(k-1)) _ (2^k-2^(k-t))
      (fun x => R.eval (x:F)*((x:F)-β)⁻¹) (fun x => ((x:F)-β)⁻¹)
      hsource (gold_normalized_source_gap k t ht0 ht)
    have hroots : 2^k-2^(k-t)≤(E.filter fun x => (R+(P.map φ+R)).eval x=0).card := by
      rw [show R+(P.map φ+R)=P.map φ by rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]]
      rw [card_mapped_locator_roots φ D P]
      obtain ⟨A,hA,l,κ,rfl,hzero⟩ := hps P hP
      obtain ⟨hr,hM⟩ := (mem_momentTensors D v t A).mp hA
      exact (repairedLocator_properties D k hD v A l κ t ht0 ht hM hr hzero).2.2.2.1.ge
    have hbad := poleReduction_badChallenge E β (by simpa only [E,mem_additiveDomain] using hβ)
      R (P.map φ+R) (2^(k-1)) (2^k-2^(k-t))
      ((hdegree P hP).trans (by exact_mod_cast Nat.sub_le (2^(k-1)) (2^(k-t-1)))) hroots
    intro hz
    exact hzero (hz ▸ hbad)
  obtain ⟨Z,hZ,hdata⟩ := exists_nonzero_locator_label_witnesses_no_loss φ D ps β hβ
    (2^(k-1)-2^(k-t-1)) hdegree hlabel
  refine ⟨Z,hZ,?_⟩
  intro z hz
  obtain ⟨hne,P,hP,hzP,hp,hmatch⟩ := hdata z hz
  obtain ⟨A,hA,l,κ,hPeq,hzero⟩ := hps P hP
  obtain ⟨hr,hM⟩ := (mem_momentTensors D v t A).mp hA
  let H := (tensorQuadraticData D v A).radical
  let S : Finset D := Finset.univ.filter fun x : D => P.eval (x:B)=0
  refine ⟨hne,_,hp,H,cardinal_tensorQuadraticData_radical D (k+1) hD v A t ht hr,S,?_,?_,?_⟩
  · have hc := (repairedLocator_properties D k hD v A l κ t ht0 ht hM hr hzero).2.2.2.1
    change (Finset.univ.filter fun x : D => P.eval (x:B)=0).card=_
    rw [←Fintype.card_subtype]
    simpa only [Nat.card_eq_fintype_card,hPeq] using hc
  · intro x h
    change x+(h:D) ∈ Finset.univ.filter (fun x : D => P.eval (x:B)=0) ↔ x ∈ _
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hPeq]
    exact repairedLocator_roots_add_radical D k hD v A l κ t ht0 ht hM hr hzero x h
  · intro x
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hmatch x
end BinaryFieldCounterexamples.Gold
