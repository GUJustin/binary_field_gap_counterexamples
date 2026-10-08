/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Family
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.SourceBound
public import BinaryFieldCounterexamples.Constructions.PoleReduction
public import BinaryFieldCounterexamples.Polynomial.Map
public import BinaryFieldCounterexamples.ReciprocalAgreement
public import BinaryFieldCounterexamples.Agreement.Interpolation
public import BinaryFieldCounterexamples.Agreement.ExcludeZero
/-!
# The Gold received pair with the first input of Lemma 3.13 and stronger witnesses

At every exterior pole, replace the fixed first-input polynomial by the canonical both-far
quarter-rate numerator. The change has at most eighth degree, preserving the
Gold corrections' stronger half-threshold degree bound. Pole reduction then
turns every distinct locator value into a challenge, with at most one lost
at zero. The same pair has exact second-input and common agreement, the strengthened
bound on the first input's agreement, and the stronger strict-degree witnesses.
All statements transport through the chosen field embedding and the actual
affine translation of the prescribed domain.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B F : Type*} [Field B] [Fintype B] [CharP B 2]
  [Field F] [Fintype F] [CharP F 2]
/-- Field embeddings preserve the canonical binary square root. -/
theorem map_binary_squareRoot (φ : B →+* F) (a : B) :
    φ ((frobeniusEquiv B 2).symm a) = (frobeniusEquiv F 2).symm (φ a) := by
  apply (frobeniusEquiv F 2).injective
  change φ ((frobeniusEquiv B 2).symm a)^2=((frobeniusEquiv F 2).symm (φ a))^2
  rw [← map_pow, frobeniusEquiv_symm_pow_p, frobeniusEquiv_symm_pow_p]
/-- The fixed Gold first-input polynomial transports to the actual embedded subgroup. -/
theorem map_goldSourcePolynomial (φ : B →+* F) (D : AddSubgroup B)
    [Fintype D] [Fintype (D.map φ.toAddMonoidHom)] (k : ℕ) :
    (goldSourcePolynomial D k).map φ = goldSourcePolynomial (D.map φ.toAddMonoidHom) k := by
  simp only [goldSourcePolynomial, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    map_X, map_C, map_binary_squareRoot, coeff_subspacePolynomial_map]
/-- The both-far numerator differs from the fixed Gold first-input polynomial only below eighth degree. -/
theorem binaryQuarterNumerator_add_goldSource_natDegree (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hk : 2 ≤ k) (hD : Nat.card D=2^(k+1)) (β : B) :
    (binaryQuarterNumerator D β+goldSourcePolynomial D k).natDegree ≤ 2^(k-2) := by
  obtain ⟨V,hV,hL⟩ := subspacePolynomial_gold_tail D k (by omega) hD
  have he : (binaryQuarterNumerator D β+goldSourcePolynomial D k)^2 =
      V-C ((subspacePolynomial D).coeff 1)*(X-C β) := by
    rw [CharTwo.add_sq,binaryQuarterNumerator_sq,binaryQuarterRadicand,hL]
    linear_combination (norm := ring_nf)
      goldSourcePolynomial D k ^ 2 * (CharTwo.two_eq_zero (R := B[X]))
  have hd : (V-C ((subspacePolynomial D).coeff 1)*(X-C β)).natDegree ≤ 2^(k-1) := by
    apply (natDegree_sub_le _ _).trans
    apply max_le hV
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_sub_C]; exact Nat.one_le_pow _ _ (by decide))
  rw [← he,natDegree_pow] at hd
  have hpow : 2^(k-1)=2^(k-2)*2 := by rw [← pow_succ]; congr 1; omega
  rw [hpow] at hd
  omega
/-- Replacing the fixed first-input polynomial by the both-far numerator preserves the stronger correction degree bound. -/
theorem gold_correction_natDegree_le (D : AddSubgroup B) [Fintype D]
    (k t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1) (hD : Nat.card D=2^(k+1))
    (P : B[X]) (hP : (P+goldSourcePolynomial D k).natDegree ≤ 2^(k-1)-2^(k-t-1)) (β : B) :
    (P+binaryQuarterNumerator D β).natDegree ≤ 2^(k-1)-2^(k-t-1) := by
  have hs := binaryQuarterNumerator_add_goldSource_natDegree D k (by omega) hD β
  have hpow : 2^(k-1)=2^(k-2)*2 := by rw [← pow_succ]; congr 1; omega
  have hsmall : 2^(k-t-1) ≤ 2^(k-2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hbound : 2^(k-2) ≤ 2^(k-1)-2^(k-t-1) := by rw [hpow]; omega
  have he : P+binaryQuarterNumerator D β =
      (P+goldSourcePolynomial D k)+(binaryQuarterNumerator D β+goldSourcePolynomial D k) := by
    linear_combination (norm := ring_nf)
      -goldSourcePolynomial D k * (CharTwo.two_eq_zero (R := B[X]))
  rw [he]
  exact (natDegree_add_le _ _).trans (max_le hP (hs.trans hbound))
/-- The same correction bound holds after any field embedding, at every exterior pole. -/
theorem mapped_gold_correction_natDegree_le (φ : B →+* F) (D : AddSubgroup B)
    [Fintype D] [Fintype (D.map φ.toAddMonoidHom)]
    (k t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1) (hD : Nat.card D=2^(k+1))
    (P : B[X]) (hP : (P+goldSourcePolynomial D k).natDegree ≤ 2^(k-1)-2^(k-t-1)) (β : F) :
    (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).natDegree ≤ 2^(k-1)-2^(k-t-1) := by
  apply gold_correction_natDegree_le _ k t ht0 ht (by rw [natCard_map_addSubgroup,hD])
  rw [← map_goldSourcePolynomial φ D k,← Polynomial.map_add,natDegree_map]
  exact hP
/-- Mapping the polynomial and the prescribed domain preserves every locator root. -/
theorem card_mapped_locator_roots {B F : Type*} [Field B] [Field F] [Fintype F] [DecidableEq F] (φ : B →+* F) (D : AddSubgroup B)
    (P : B[X]) :
    ((additiveDomain (D.map φ.toAddMonoidHom)).filter fun x ↦ (P.map φ).eval x=0).card =
      Nat.card {x : D // P.eval (x : B)=0} := by
  classical
  let e := D.equivMapOfInjective φ.toAddMonoidHom φ.injective
  have hc : Nat.card {x : D // P.eval (x : B)=0} =
      Nat.card {y : D.map φ.toAddMonoidHom // (P.map φ).eval (y : F)=0} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquiv e.toEquiv
    intro x
    change P.eval (x : B)=0 ↔ (P.map φ).eval (φ (x : B))=0
    rw [eval_map_apply,map_eq_zero]
  have he := agreementCount_add_source_eq_roots (D.map φ.toAddMonoidHom) 0 (P.map φ)
  rw [agreementCount_eq_card_filter (additiveDomain (D.map φ.toAddMonoidHom))
    (fun x : F ↦ (0 : F[X]).eval x) (P.map φ+0)] at he
  simpa only [add_zero,eval_zero,hc] using he
/-- The actual finite set of locator values at a containing-field pole. -/
noncomputable def locatorValues {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (ps : Finset B[X]) (β : F) : Finset F := by
  classical
  exact ps.image fun P ↦ (P.map φ).eval β
/-- An exterior pole turns the distinct locator values into equally many challenge values, with at most one lost at zero. -/
theorem nonzeroBadChallenges_ge_locator_values {B F : Type*} [Field B] [Field F] [Fintype F] [CharP F 2] (φ : B →+* F) (D : AddSubgroup B)
    [Fintype (D.map φ.toAddMonoidHom)] (ps : Finset B[X]) (β : F)
    (hβ : β ∉ D.map φ.toAddMonoidHom) (J T : ℕ)
    (hdegree : ∀ P ∈ ps,
      (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).degree ≤ J)
    (hroots : ∀ P ∈ ps, T ≤ Nat.card {x : D // P.eval (x : B)=0}) :
    (locatorValues φ ps β).card-1 ≤
      (nonzeroBadChallenges (additiveDomain (D.map φ.toAddMonoidHom)) J
        (fun x ↦ (binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval (x : F)*((x : F)-β)⁻¹)
        (fun x ↦ ((x : F)-β)⁻¹) T).card := by
  classical
  let E := additiveDomain (D.map φ.toAddMonoidHom)
  let R := binaryQuarterNumerator (D.map φ.toAddMonoidHom) β
  let f : E → F := fun x ↦ R.eval (x : F)*((x : F)-β)⁻¹
  let g : E → F := fun x ↦ ((x : F)-β)⁻¹
  let Z := ps.image fun P ↦ (P.map φ).eval β+R.eval β
  have hβE : β ∉ E := by simpa only [E,mem_additiveDomain] using hβ
  have hZ : Z ⊆ badChallenges E J f g T := by
    intro z hz
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hz
    have he : R+(P.map φ+R)=P.map φ := by
      rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
    have hcount : T ≤ (E.filter fun x ↦ (R+(P.map φ+R)).eval x=0).card := by
      rw [he]
      change T ≤ ((additiveDomain (D.map φ.toAddMonoidHom)).filter fun x ↦ (P.map φ).eval x=0).card
      rw [card_mapped_locator_roots φ D P]
      exact hroots P hP
    have hb := poleReduction_badChallenge E β hβE R (P.map φ+R) J T (hdegree P hP) hcount
    simpa only [eval_add] using hb
  have hcard : Z.card=(locatorValues φ ps β).card := by
    unfold locatorValues
    have he : Z=(ps.image fun P ↦ (P.map φ).eval β).image (fun z ↦ z+R.eval β) := by
      rw [Finset.image_image]
      rfl
    rw [he,Finset.card_image_of_injective _ (fun a b h ↦ add_right_cancel h)]
  have hle := Finset.card_le_card hZ
  rw [nonzeroBadChallenges]
  change _ ≤ ((badChallenges E J f g T).erase 0).card
  by_cases hz : 0 ∈ badChallenges E J f g T
  · rw [Finset.card_erase_of_mem hz]
    rw [hcard] at hle
    omega
  · rw [Finset.erase_eq_of_notMem hz]
    rw [hcard] at hle
    omega
/-- Every locator value produces a distinct translated challenge before any zero filtering. -/
theorem badChallenges_ge_locator_values {B F : Type*} [Field B] [Field F] [Fintype F] [CharP F 2] (φ : B →+* F) (D : AddSubgroup B)
    [Fintype (D.map φ.toAddMonoidHom)] (ps : Finset B[X]) (β : F)
    (hβ : β ∉ D.map φ.toAddMonoidHom) (J T : ℕ)
    (hdegree : ∀ P ∈ ps,
      (P.map φ+binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).degree ≤ J)
    (hroots : ∀ P ∈ ps, T ≤ Nat.card {x : D // P.eval (x : B)=0}) :
    (locatorValues φ ps β).card ≤
      (badChallenges (additiveDomain (D.map φ.toAddMonoidHom)) J
        (fun x ↦ (binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval (x : F)*((x : F)-β)⁻¹)
        (fun x ↦ ((x : F)-β)⁻¹) T).card := by
  classical
  let E := additiveDomain (D.map φ.toAddMonoidHom)
  let R := binaryQuarterNumerator (D.map φ.toAddMonoidHom) β
  let f : E → F := fun x ↦ R.eval (x : F)*((x : F)-β)⁻¹
  let g : E → F := fun x ↦ ((x : F)-β)⁻¹
  let Z := ps.image fun P ↦ (P.map φ).eval β+R.eval β
  have hβE : β ∉ E := by simpa only [E,mem_additiveDomain] using hβ
  have hZ : Z ⊆ badChallenges E J f g T := by
    intro z hz
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hz
    have he : R+(P.map φ+R)=P.map φ := by
      rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
    have hcount : T ≤ (E.filter fun x ↦ (R+(P.map φ+R)).eval x=0).card := by
      rw [he]
      change T ≤ ((additiveDomain (D.map φ.toAddMonoidHom)).filter fun x ↦ (P.map φ).eval x=0).card
      rw [card_mapped_locator_roots φ D P]
      exact hroots P hP
    have hb := poleReduction_badChallenge E β hβE R (P.map φ+R) J T (hdegree P hP) hcount
    simpa only [eval_add] using hb
  have hcard : Z.card=(locatorValues φ ps β).card := by
    unfold locatorValues
    have he : Z=(ps.image fun P ↦ (P.map φ).eval β).image (fun z ↦ z+R.eval β) := by
      rw [Finset.image_image]
      rfl
    rw [he,Finset.card_image_of_injective _ (fun a b h ↦ add_right_cancel h)]
  have hle := Finset.card_le_card hZ
  simpa only [hcard] using hle
/-- The pair with the first input of Lemma 3.13 has the exact common/right agreements and the strengthened first-input bound. -/
theorem binaryQuarterPair_source_bounds (D : AddSubgroup F) [Fintype D]
    (β : F) (hβ : β ∉ D) (k : ℕ) (hk : 2 ≤ k) (hD : Nat.card D=2^(k+1)) :
    commonAgreementEQ (additiveDomain D) (2^(k-1))
      (fun x ↦ (binaryQuarterNumerator D β).eval (x : F)*((x : F)-β)⁻¹)
      (fun x ↦ ((x : F)-β)⁻¹) (2^(k-1)) ∧
    agreementEQ (additiveDomain D) (2^(k-1)) (fun x ↦ ((x : F)-β)⁻¹) (2^(k-1)) ∧
    agreementLE (additiveDomain D) (2^(k-1))
      (fun x ↦ (binaryQuarterNumerator D β).eval (x : F)*((x : F)-β)⁻¹) (3*2^(k+1)/8-1) := by
  classical
  have hN : 2^(k+1)=4*2^(k-1) := by
    have he : k+1=(k-1)+2 := by omega
    rw [he,pow_add]
    ring
  have hK : 2 ≤ 2^(k-1) := by
    have he := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ k-1 by omega)
    simpa using he
  have hβE : β ∉ additiveDomain D := by simpa only [mem_additiveDomain] using hβ
  have hKcard : 2^(k-1) ≤ (additiveDomain D).card := by rw [card_additiveDomain,hD,hN]; omega
  refine ⟨commonAgreementEQ_reciprocal_right _ β hβE _ hKcard _,
    agreementEQ_reciprocal _ β hβE _ hKcard, ?_⟩
  have he := agreementLE_binaryQuarterSource D β hβ (2^(k-1)) hK ⟨k-1,rfl⟩
    (by rw [← Nat.card_eq_fintype_card,hD,hN])
  have hn : 3*2^(k+1)/8-1=3*2^(k-1)/2-1 := by rw [hN]; omega
  rwa [hn]

/-- Mapping a translated domain is translation of the mapped domain. -/
theorem mappedDomain_affineDomain {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (D : Finset B) (a : B) :
    mappedDomain φ (affineDomain D a)=affineDomain (mappedDomain φ D) (φ a) := by
  classical
  simp only [mappedDomain,affineDomain,Finset.image_image]
  congr 1
  funext x
  exact map_add φ x a
/-- The half-agreement witness dimension is the exact tail degree. -/
theorem gold_half_threshold (k t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1) :
    (2^k-2^(k-t))/2=2^(k-1)-2^(k-t-1) := by
  have h₁ : 2^k=2^(k-1)*2 := by rw [← pow_succ]; congr 1; omega
  have h₂ : 2^(k-t)=2^(k-t-1)*2 := by rw [← pow_succ]; congr 1; omega
  rw [h₁,h₂]
  omega

/-- The Gold agreement threshold strictly exceeds the agreement bound for the first input of Lemma 3.13, including rank four. -/
theorem gold_normalized_source_gap (k t : ℕ) (ht0 : 2≤t) (ht : 2*t≤k+1) : 3*2^(k+1)/8-1 < 2^k-2^(k-t) := by
  have hpow : 2^(k+1)=8*2^(k-2) := by
    rw [show k+1=(k-2)+3 by omega, pow_add]
    ring
  have hpow' : 2^k=4*2^(k-2) := by
    calc
      2^k = 2^((k-2)+2) := by congr 1; omega
      _ = 4*2^(k-2) := by rw [pow_add]; ring
  have hsmall : 2^(k-t)≤2^(k-2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0<2^(k-2) := by positivity
  rw [hpow,hpow']
  omega

/-- The first input of Lemma 3.13 has agreement strictly below the Gold threshold, so no challenge is lost at zero. -/
theorem goldPair_of_locator_pool_no_loss (φ : B →+* F) (D : AddSubgroup B)
    [Fintype D] [Fintype (D.map φ.toAddMonoidHom)]
    (a : B) (k t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1) (hD : Nat.card D=2^(k+1))
    (ps : Finset B[X])
    (hps : ∀ P ∈ ps, (P+goldSourcePolynomial D k).natDegree ≤ 2^(k-1)-2^(k-t-1) ∧
      2^k-2^(k-t) ≤ Nat.card {x : D // P.eval (x : B)=0})
    (β : F) (hβ : β ∉ D.map φ.toAddMonoidHom) :
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F,
      commonAgreementEQ E (2^(k-1)) f g (2^(k-1)) ∧
      agreementEQ E (2^(k-1)) g (2^(k-1)) ∧
      agreementLE E (2^(k-1)) f (3*2^(k+1)/8-1) ∧
      (locatorValues φ ps β).card ≤ (nonzeroBadChallenges E (2^(k-1)) f g (2^k-2^(k-t))).card ∧
      (locatorValues φ ps β).card ≤ (nonzeroBadChallenges E ((2^k-2^(k-t))/2) f g (2^k-2^(k-t))).card := by
  classical
  dsimp only
  rw [mappedDomain_affineDomain,mappedDomain_additiveDomain]
  let D' := D.map φ.toAddMonoidHom
  let E := affineDomain (additiveDomain D') (φ a)
  let f0 : F → F := fun x ↦ (binaryQuarterNumerator D' β).eval x*(x-β)⁻¹
  let g0 : F → F := fun x ↦ (x-β)⁻¹
  let f : E → F := fun x ↦ f0 ((x : F)-φ a)
  let g : E → F := fun x ↦ g0 ((x : F)-φ a)
  have hcD : Nat.card D'=2^(k+1) := by rw [natCard_map_addSubgroup,hD]
  have hβE : β+φ a ∉ E := by
    intro h
    rw [mem_affineDomain_iff,add_sub_cancel_right,mem_additiveDomain] at h
    exact hβ h
  have hgform : g=fun x : E ↦ ((x : F)-(β+φ a))⁻¹ := by
    funext x
    dsimp [g,g0]
    congr 1
    ring
  have hKcard : 2^(k-1) ≤ E.card := by
    rw [card_affineDomain,card_additiveDomain,hcD]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hdegree (P : B[X]) (hP : P ∈ ps) :
      (P.map φ+binaryQuarterNumerator D' β).degree ≤ (2^(k-1)-2^(k-t-1) : ℕ) :=
    degree_le_of_natDegree_le (mapped_gold_correction_natDegree_le φ D k t ht0 ht hD P (hps P hP).1 β)
  have hbad (J : ℕ) : nonzeroBadChallenges E J f g (2^k-2^(k-t)) =
      nonzeroBadChallenges (additiveDomain D') J (fun x ↦ f0 x) (fun x ↦ g0 x) (2^k-2^(k-t)) := by
    simp only [nonzeroBadChallenges]
    rw [badChallenges_affineDomain (additiveDomain D') (φ a) f0 g0 J (2^k-2^(k-t))]
  have hsource := (binaryQuarterPair_source_bounds D' β hβ k (by omega) hcD).2.2
  have hgap := gold_normalized_source_gap k t ht0 ht
  have hexclude (J : ℕ) (hJ : J≤2^(k-1)) :
      nonzeroBadChallenges (additiveDomain D') J (fun x ↦ f0 x) (fun x ↦ g0 x) (2^k-2^(k-t)) =
      badChallenges (additiveDomain D') J (fun x ↦ f0 x) (fun x ↦ g0 x) (2^k-2^(k-t)) := by
    apply nonzeroBadChallenges_eq_of_source_gap _ J _ _ _ _ _ hgap
    intro p hp
    exact hsource p (hp.trans_le (by exact_mod_cast hJ))
  refine ⟨f,g,?_,?_,?_,?_,?_⟩
  · rw [hgform]
    exact commonAgreementEQ_reciprocal_right E (β+φ a) hβE _ hKcard f
  · rw [hgform]
    exact agreementEQ_reciprocal E (β+φ a) hβE _ hKcard
  · exact agreementLE_affineDomain (additiveDomain D') (φ a) f0 _ _
      (binaryQuarterPair_source_bounds D' β hβ k (by omega) hcD).2.2
  · rw [hbad,hexclude _ le_rfl]
    exact badChallenges_ge_locator_values φ D ps β hβ (2^(k-1)) (2^k-2^(k-t))
      (fun P hP ↦ (hdegree P hP).trans (by exact_mod_cast Nat.sub_le (2^(k-1)) (2^(k-t-1))))
      (fun P hP ↦ (hps P hP).2)
  · rw [hbad,gold_half_threshold k t ht0 ht,hexclude _ (Nat.sub_le _ _)]
    exact badChallenges_ge_locator_values φ D ps β hβ (2^(k-1)-2^(k-t-1)) (2^k-2^(k-t))
      hdegree (fun P hP ↦ (hps P hP).2)

/-- Every exterior value pool supplies the same received pair with the first input of Lemma 3.13, including stronger strict-degree witnesses and affine transport. -/
theorem goldPair_of_locator_pool (φ : B →+* F) (D : AddSubgroup B)
    [Fintype D] [Fintype (D.map φ.toAddMonoidHom)]
    (a : B) (k t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1) (hD : Nat.card D=2^(k+1))
    (ps : Finset B[X])
    (hps : ∀ P ∈ ps, (P+goldSourcePolynomial D k).natDegree ≤ 2^(k-1)-2^(k-t-1) ∧
      2^k-2^(k-t) ≤ Nat.card {x : D // P.eval (x : B)=0})
    (β : F) (hβ : β ∉ D.map φ.toAddMonoidHom) :
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F,
      commonAgreementEQ E (2^(k-1)) f g (2^(k-1)) ∧
      agreementEQ E (2^(k-1)) g (2^(k-1)) ∧
      agreementLE E (2^(k-1)) f (3*2^(k+1)/8-1) ∧
      (locatorValues φ ps β).card-1 ≤ (nonzeroBadChallenges E (2^(k-1)) f g (2^k-2^(k-t))).card ∧
      (locatorValues φ ps β).card-1 ≤ (nonzeroBadChallenges E ((2^k-2^(k-t))/2) f g (2^k-2^(k-t))).card := by
  obtain ⟨f,g,hcommon,hg,hf,hbad,hstrong⟩ := goldPair_of_locator_pool_no_loss
    φ D a k t ht0 ht hD ps hps β hβ
  exact ⟨f,g,hcommon,hg,hf,(Nat.sub_le _ _).trans hbad,(Nat.sub_le _ _).trans hstrong⟩

end BinaryFieldCounterexamples.Gold
