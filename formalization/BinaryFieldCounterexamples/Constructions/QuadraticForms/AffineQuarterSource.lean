/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.DomainSource
public import BinaryFieldCounterexamples.Agreement.AffineTransport
public import BinaryFieldCounterexamples.Agreement.Interpolation
public import BinaryFieldCounterexamples.Agreement.ExcludeZero

/-!
# The affine prime-power clause of Lemma 3.13

The affine locator is the literal translation of the product locator. Its
canonical inverse-Frobenius numerator supplies the printed first word and the
exact translation of the exceptional challenge set, including zero.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Lemma 3.13: taking a root of the affine locator radicand recovers it exactly. -/
theorem primePowerQuarterNumerator_pow_affineSupport
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (_hr : 1 ≤ r) (L : F[X]) (β : F)
    (hs : ∀ n ∈ L.support, n = 0 ∨ ∃ i : ℕ, n = (p^r)^i) :
    primePowerQuarterNumerator p r L β ^ (p^r) = primePowerQuarterRadicand L β := by
  apply primePowerPolynomialRoot_pow
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · subst n
    have := mem_support_iff.mp hn
    simp [primePowerQuarterRadicand] at this
  have hLn : L.coeff n ≠ 0 := by
    have := mem_support_iff.mp hn
    simpa [primePowerQuarterRadicand, coeff_sub, coeff_C_mul, coeff_X,
      coeff_C, hn0, hn1, Ne.symm hn1] using this
  rcases hs n (mem_support_iff.mpr hLn) with hz | ⟨i, hi⟩
  · exact (hn0 hz).elim
  · cases i with
    | zero => exact (hn1 (by simpa using hi)).elim
    | succ i => rw [hi, pow_succ]; exact dvd_mul_left _ _

/-- Lemma 3.13: the exact numerator shift for every characteristic prime power,
including affine locators with a constant term. -/
theorem primePowerQuarterNumerator_shift
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (L : F[X]) (β : F)
    (hs : ∀ n ∈ L.support, n = 0 ∨ ∃ i : ℕ, n = (p^r)^i) :
    primePowerQuarterNumerator p r L β = primePowerQuarterNumerator p r L 0 +
      C ((iterateFrobeniusEquiv F p r).symm (L.coeff 1 * β)) := by
  have hroot : ((iterateFrobeniusEquiv F p r).symm (L.coeff 1 * β)) ^ (p^r) =
      L.coeff 1 * β := by
    rw [← iterateFrobeniusEquiv_def]
    exact (iterateFrobeniusEquiv F p r).apply_symm_apply _
  apply sub_eq_zero.mp
  apply eq_zero_of_pow_eq_zero (n := p^r)
  rw [sub_pow_expChar_pow, add_pow_expChar_pow, primePowerQuarterNumerator_pow_affineSupport p r hr L β hs,
    primePowerQuarterNumerator_pow_affineSupport p r hr L 0 hs, ← C_pow, hroot]
  simp only [primePowerQuarterRadicand, map_zero, sub_zero]
  rw [mul_sub, ← C_mul]
  ring

/-- Lemma 3.13: the literal first-word numerator evaluates to the unique
`p^r`th root of `-λ(x-β)` at each coordinate of the domain. -/
theorem primePowerQuarterNumerator_eval_root
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (L : F[X]) (β x : F)
    (hs : ∀ n ∈ L.support, n = 0 ∨ ∃ i : ℕ, n = (p^r)^i)
    (hx : L.eval x = 0) :
    (primePowerQuarterNumerator p r L β).eval x =
      (iterateFrobeniusEquiv F p r).symm (-L.coeff 1 * (x-β)) := by
  apply (iterateFrobeniusEquiv F p r).injective
  rw [(iterateFrobeniusEquiv F p r).apply_symm_apply, iterateFrobeniusEquiv_def,
    ← eval_pow, primePowerQuarterNumerator_pow_affineSupport p r hr L β hs]
  simp [primePowerQuarterRadicand, hx]

/-- Lemma 3.13: replacing the unshifted first word translates the exact challenge
set by the negative `p^r`th root of `λβ`. -/
theorem badChallenges_primePowerQuarterSource_eq_image
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (D : Finset F) (L : F[X]) (β : F) (K T : ℕ)
    (hs : ∀ n ∈ L.support, n = 0 ∨ ∃ i : ℕ, n = (p^r)^i) :
    badChallenges D K
      (fun x => (primePowerQuarterNumerator p r L β).eval (x:F)*((x:F)-β)⁻¹)
      (fun x => ((x:F)-β)⁻¹) T =
      (badChallenges D K
        (fun x => (primePowerQuarterNumerator p r L 0).eval (x:F)*((x:F)-β)⁻¹)
        (fun x => ((x:F)-β)⁻¹) T).image
          (fun z => z-(iterateFrobeniusEquiv F p r).symm (L.coeff 1*β)) := by
  have hw : (fun x : D => (primePowerQuarterNumerator p r L β).eval (x:F)*((x:F)-β)⁻¹) =
      (fun x : D => (primePowerQuarterNumerator p r L 0).eval (x:F)*((x:F)-β)⁻¹ +
        (iterateFrobeniusEquiv F p r).symm (L.coeff 1*β)*((x:F)-β)⁻¹) := by
    funext x
    rw [primePowerQuarterNumerator_shift p r hr L β hs, eval_add, eval_C]
    ring
  rw [hw]
  exact badChallenges_add_direction_eq _ _ _ _ _ _

/-- Lemma 3.13: an affine scalar space has a locator supported at zero and
powers of the size of the scalar field. -/
theorem affine_submoduleLocator_primePowerSupport
    {k F : Type*} [Field k] [Fintype k] [Field F] [Fintype F] [Algebra k F]
    (p r : ℕ) (hq : Fintype.card k = p^r) (U : Submodule k F) (a : F) :
    ∀ n ∈ ((subspacePolynomial U.toAddSubgroup).comp (X-C a)).support,
      n = 0 ∨ ∃ i : ℕ, n = (p^r)^i := by
  have hform : (subspacePolynomial U.toAddSubgroup).comp (X-C a) =
      subspacePolynomial U.toAddSubgroup + C ((subspacePolynomial U.toAddSubgroup).eval (-a)) := by
    simpa only [map_neg, sub_eq_add_neg] using subspacePolynomial_comp_X_add_C U.toAddSubgroup (-a)
  intro n hn
  by_cases hn0 : n = 0
  · exact Or.inl hn0
  · right
    have hcoeff := mem_support_iff.mp hn
    rw [hform] at hcoeff
    have hbase : n ∈ (subspacePolynomial U.toAddSubgroup).support := by
      simpa [mem_support_iff, coeff_C, hn0] using hcoeff
    obtain ⟨i, hi⟩ := FiniteFieldLocator.subspacePolynomial_q_support U n hbase
    exact ⟨i, by simpa only [hq] using hi⟩

/-- Lemma 3.13: the canonical first input satisfies the individual agreement
bound on the actual affine `F_b`-space, with its exterior pole. -/
theorem agreementLE_affineSubmoduleQuarterSource
    {k F : Type*} [Field k] [Fintype k] [Field F] [Fintype F] [Algebra k F]
    (p r : ℕ) [Fact p.Prime] [CharP F p] (hr : 1 ≤ r)
    (hq : Fintype.card k = p^r) (U : Submodule k F) (a β : F)
    (hβ : β ∉ affineDomain (additiveDomain U.toAddSubgroup) a)
    (d : ℕ) (hd : 3 ≤ d) (hcard : Fintype.card U = (Fintype.card k)^d) :
    agreementLE (affineDomain (additiveDomain U.toAddSubgroup) a) ((Fintype.card k)^(d-2))
      (fun x => (primePowerQuarterNumerator p r
        ((subspacePolynomial U.toAddSubgroup).comp (X-C a)) β).eval (x:F)*((x:F)-β)⁻¹)
      (((p^r+1)*(Fintype.card k)^(d-2)-2)/2) := by
  let L := subspacePolynomial U.toAddSubgroup
  let S := (primePowerQuarterNumerator p r L (β-a)).comp (X-C a)
  have hs : ∀ n ∈ L.support, ∃ i : ℕ, n = (p^r)^i := by
    intro n hn
    obtain ⟨i, hi⟩ := FiniteFieldLocator.subspacePolynomial_q_support U n hn
    exact ⟨i, by simpa only [hq] using hi⟩
  have hcoeff : (L.comp (X-C a)).coeff 1 = L.coeff 1 := by
    have hf := subspacePolynomial_comp_X_add_C U.toAddSubgroup (-a)
    have hf' : L.comp (X-C a) = L+C (L.eval (-a)) := by
      simpa only [L, map_neg, sub_eq_add_neg] using hf
    rw [hf']; simp
  have hpow : S^(p^r) = primePowerQuarterRadicand (L.comp (X-C a)) β := by
    dsimp [S]
    rw [← pow_comp, primePowerQuarterNumerator_pow p r hr L (β-a) hs]
    simp only [primePowerQuarterRadicand, sub_comp, mul_comp, C_comp, X_comp, hcoeff]
    rw [map_sub]
    ring
  have hcanon : primePowerQuarterNumerator p r (L.comp (X-C a)) β = S := by
    apply sub_eq_zero.mp
    apply eq_zero_of_pow_eq_zero (n := p^r)
    rw [sub_pow_expChar_pow, primePowerQuarterNumerator_pow_affineSupport p r hr _ β
      (affine_submoduleLocator_primePowerSupport p r hq U a), hpow, sub_self]
  rw [hcanon]
  have hβ' : β-a ∉ U := by
    intro h
    exact hβ ((mem_affineDomain_iff _ _ _).mpr ((mem_additiveDomain _ _).mpr h))
  have hbound := agreementLE_submoduleQuarterSource p r hr hq U
    (additiveDomain U.toAddSubgroup) (fun x => mem_additiveDomain _ x) (β-a) hβ' d hd hcard
  have hb : 2 ≤ Fintype.card k := Fintype.one_lt_card
  have hK : 2 ≤ (Fintype.card k)^(d-2) := hb.trans (Nat.le_self_pow (by omega) _)
  have hN : Fintype.card U = (Fintype.card k)^2*(Fintype.card k)^(d-2) := by
    rw [hcard, ← pow_add]; congr 1; omega
  rw [primePowerQuarterSource_floor _ _ _ hb hK hN] at hbound
  have ht := agreementLE_affineDomain (additiveDomain U.toAddSubgroup) a
    (fun x => (primePowerQuarterNumerator p r L (β-a)).eval x*(x-(β-a))⁻¹)
    _ _ hbound
  have hw : (fun x : affineDomain (additiveDomain U.toAddSubgroup) a => S.eval (x:F)*((x:F)-β)⁻¹) =
      (fun x : affineDomain (additiveDomain U.toAddSubgroup) a => (primePowerQuarterNumerator p r L (β-a)).eval ((x:F)-a)*((x:F)-a-(β-a))⁻¹) := by
    funext x
    dsimp [S]
    simp only [eval_comp, eval_sub, eval_X, eval_C]
    congr 1
    congr 1
    ring
  rw [hw]
  simpa only [hq] using ht

/-- Lemma 3.13 (general prime-power affine clause), assembled: the printed
first input is individually far, the second and common agreements are exactly
`K`, its numerator is the literal unique Frobenius root, the exceptional set
shifts by `-(λβ)^(1/b)` with unchanged cardinality, and zero is excluded at the
paper's threshold. The binary padding clause is proved separately. -/
theorem affine_primePowerQuarterSource_full
    {k F : Type*} [Field k] [Fintype k] [Field F] [Fintype F] [Algebra k F]
    (p r : ℕ) [Fact p.Prime] [CharP F p] (hr : 1 ≤ r)
    (hq : Fintype.card k = p^r) (U : Submodule k F) (a β : F)
    (hβ : β ∉ affineDomain (additiveDomain U.toAddSubgroup) a)
    (d : ℕ) (hd : 3 ≤ d) (hcard : Fintype.card U = (Fintype.card k)^d) (T : ℕ) :
    let D := affineDomain (additiveDomain U.toAddSubgroup) a
    let L := (subspacePolynomial U.toAddSubgroup).comp (X-C a)
    let K := (Fintype.card k)^(d-2)
    let S := primePowerQuarterNumerator p r L β
    let R := primePowerQuarterNumerator p r L 0
    let f : D → F := fun x => (iterateFrobeniusEquiv F p r).symm
      (-L.coeff 1*((x:F)-β))*((x:F)-β)⁻¹
    let g : D → F := fun x => ((x:F)-β)⁻¹
    D.card = (Fintype.card k)^d ∧ L.derivative = C (L.coeff 1) ∧ L.coeff 1 ≠ 0 ∧
    agreementLE D K f (((Fintype.card k+1)*K-2)/2) ∧
    agreementEQ D K g K ∧ commonAgreementEQ D K f g K ∧
    (∀ x ∈ D, S.eval x ^ (p^r) = -L.coeff 1*(x-β)) ∧
    badChallenges D K f g T =
      (badChallenges D K (fun x => R.eval (x:F)*((x:F)-β)⁻¹) g T).image
        (fun z => z-(iterateFrobeniusEquiv F p r).symm (L.coeff 1*β)) ∧
    (badChallenges D K f g T).card =
      (badChallenges D K (fun x => R.eval (x:F)*((x:F)-β)⁻¹) g T).card ∧
    ((Fintype.card k+1)*K ≤ 2*T → 0 ∉ badChallenges D K f g T) := by
  dsimp only
  let D := affineDomain (additiveDomain U.toAddSubgroup) a
  let L := (subspacePolynomial U.toAddSubgroup).comp (X-C a)
  let K := (Fintype.card k)^(d-2)
  let S := primePowerQuarterNumerator p r L β
  let R := primePowerQuarterNumerator p r L 0
  let f : D → F := fun x => (iterateFrobeniusEquiv F p r).symm
    (-L.coeff 1*((x:F)-β))*((x:F)-β)⁻¹
  let g : D → F := fun x => ((x:F)-β)⁻¹
  have hs : ∀ n ∈ L.support, n = 0 ∨ ∃ i : ℕ, n = (p^r)^i :=
    affine_submoduleLocator_primePowerSupport p r hq U a
  have hroots : ∀ x ∈ D, L.eval x = 0 := by
    intro x hx
    have hx' := (mem_additiveDomain U.toAddSubgroup (x-a)).mp
      ((mem_affineDomain_iff _ _ _).mp hx)
    simpa only [L, eval_comp, eval_sub, eval_X, eval_C] using
      (subspacePolynomial_eval_eq_zero_iff U.toAddSubgroup (x-a)).mpr hx'
  have hw : (fun x : D => S.eval (x:F)*((x:F)-β)⁻¹) = f := by
    funext x
    rw [primePowerQuarterNumerator_eval_root p r hr L β (x:F) hs (hroots _ x.property)]
  have hbound : agreementLE D K f (((Fintype.card k+1)*K-2)/2) := by
    have h := agreementLE_affineSubmoduleQuarterSource p r hr hq U a β hβ d hd hcard
    change agreementLE D K (fun x => S.eval (x:F)*((x:F)-β)⁻¹) _ at h
    rw [hw] at h
    simpa only [K, hq] using h
  have hKcard : K ≤ D.card := by
    rw [card_affineDomain, card_additiveDomain, Nat.card_eq_fintype_card]
    change (Fintype.card k)^(d-2) ≤ Fintype.card U
    rw [hcard]
    exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
  have hshift : badChallenges D K f g T =
      (badChallenges D K (fun x => R.eval (x:F)*((x:F)-β)⁻¹) g T).image
        (fun z => z-(iterateFrobeniusEquiv F p r).symm (L.coeff 1*β)) := by
    rw [← hw]
    exact badChallenges_primePowerQuarterSource_eq_image p r hr D L β K T hs
  have hcoeff : L.coeff 1 = (subspacePolynomial U.toAddSubgroup).coeff 1 := by
    have hf : L = subspacePolynomial U.toAddSubgroup +
        C ((subspacePolynomial U.toAddSubgroup).eval (-a)) := by
      simpa only [L, map_neg, sub_eq_add_neg] using
        subspacePolynomial_comp_X_add_C U.toAddSubgroup (-a)
    rw [hf]
    simp
  have hlam : L.coeff 1 ≠ 0 := by
    rw [hcoeff]
    exact subspacePolynomial_coeff_one_ne_zero _
  have hDcard : D.card = (Fintype.card k)^d := by
    rw [card_affineDomain, card_additiveDomain, Nat.card_eq_fintype_card]
    exact hcard
  refine ⟨hDcard, derivative_eq_C_of_primePowerAffineSupport p r hr L hs, hlam,
    hbound, agreementEQ_reciprocal D β hβ K hKcard,
    commonAgreementEQ_reciprocal_right D β hβ K hKcard f, ?_, hshift, ?_, ?_⟩
  · intro x hx
    have he := congrArg (Polynomial.eval x)
      (primePowerQuarterNumerator_pow_affineSupport p r hr L β hs)
    simpa [primePowerQuarterRadicand, hroots x hx, S] using he
  · rw [hshift]
    exact Finset.card_image_of_injective _ (fun x y h => by linear_combination h)
  · intro hT
    change (Fintype.card k+1)*K ≤ 2*T at hT
    apply zero_not_mem_badChallenges_of_source_gap D K _ T f g hbound
    have hb : 2 ≤ Fintype.card k := Fintype.one_lt_card
    have hK : 2 ≤ K := hb.trans (Nat.le_self_pow (by omega) _)
    have hprod : 2 ≤ (Fintype.card k+1)*K := by nlinarith
    omega

/-- Section 3, the root-count remark immediately before Lemma 3.13: a
positive-degree polynomial agrees with `(L_D-λX)^(1/b)` at at most `b` times
its degree many coordinates. This applies to the literal canonical root,
including locators of affine scalar spaces. -/
theorem primePowerLocatorRoot_agreementCount_le
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (D : Finset F) (L C₀ : F[X])
    (hs : ∀ n ∈ L.support, n = 0 ∨ ∃ i : ℕ, n = (p^r)^i)
    (hroots : ∀ x ∈ D, L.eval x = 0) (_hlam : L.coeff 1 ≠ 0)
    (hdegree : 1 ≤ C₀.natDegree) :
    agreementCount D (fun x => (primePowerQuarterNumerator p r L 0).eval (x:F)) C₀ ≤
      (p^r)*C₀.natDegree := by
  have hb : 2 ≤ p^r := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) _)
  let Q := C₀^(p^r)+Polynomial.C (L.coeff 1)*X
  have hsmall : (Polynomial.C (L.coeff 1)*X).natDegree < (C₀^(p^r)).natDegree := by
    rw [natDegree_pow]
    have hc : (Polynomial.C (L.coeff 1)*X).natDegree ≤ 1 := by
      exact natDegree_mul_le.trans (by simp)
    nlinarith
  have hQdeg : Q.natDegree = (p^r)*C₀.natDegree := by
    dsimp only [Q]
    rw [natDegree_add_eq_left_of_natDegree_lt hsmall, natDegree_pow]
  have hQ : Q ≠ 0 := by
    intro hz
    have := congrArg natDegree hz
    rw [hQdeg, natDegree_zero] at this
    nlinarith
  rw [agreementCount_eq_card_filter D
    (fun x => (primePowerQuarterNumerator p r L 0).eval x) C₀]
  apply (Finset.card_le_card (show
    (D.filter fun x => C₀.eval x = (primePowerQuarterNumerator p r L 0).eval x) ⊆
      D.filter fun x => Q.eval x = 0 from ?_)).trans
    ((card_filter_eval_eq_zero_le D Q hQ).trans hQdeg.le)
  intro x hx
  obtain ⟨hxD, hxagree⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
  have he := congrArg (Polynomial.eval x)
    (primePowerQuarterNumerator_pow_affineSupport p r hr L 0 hs)
  simp only [eval_pow, primePowerQuarterRadicand, eval_sub, eval_mul, eval_C,
    eval_X, sub_zero, hroots x hxD, zero_sub] at he
  simp only [Q, eval_add, eval_pow, eval_mul, eval_C, eval_X, hxagree, he]
  ring

end BinaryFieldCounterexamples
