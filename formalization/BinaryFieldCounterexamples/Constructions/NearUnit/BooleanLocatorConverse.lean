/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.NearUnit.BooleanWitnessInterface
public import BinaryFieldCounterexamples.Polynomial.SectionThreeAdditivity
/-!
# Constant-derivative locators and the Boolean converse

This file proves the reformulation following Lemma 3.16 in Section 3: a
constant nonzero derivative on an agreement locator gives a saturated Boolean
factor, and a square-plus-linear locator gives exact twice-degree agreement.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.NearUnit
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The reformulation following Lemma 3.16: a finite set's locator vanishes
exactly at that set. -/
theorem booleanLocator_eval_zero_iff {F : Type*} [Field F] (A : Finset F) (x : F) :
    (Lagrange.nodal A id).eval x = 0 ↔ x ∈ A := by
  simp [Lagrange.nodal, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- The reformulation following Lemma 3.16: splitting a domain into its
agreement set and complement splits its literal monic locator. -/
theorem booleanLocator_partition {F : Type*} [Field F] (D A : Finset F)
    (hA : A ⊆ D) :
    Lagrange.nodal D id = Lagrange.nodal (D \ A) id * Lagrange.nodal A id := by
  exact (Finset.prod_sdiff hA).symm

/-- The converse following Lemma 3.16: the literal scaled complementary
locator satisfies the Boolean differential equation. The domain locator has
constant nonzero derivative `lam`, and the agreement locator has derivative `c`. -/
theorem booleanLocator_converse_differential {F : Type*} [Field F] [CharP F 2]
    (D A : Finset F) (hA : A ⊆ D) (lam c : F) (hlam : lam ≠ 0)
    (hD : (Lagrange.nodal D id).derivative = C lam)
    (hderiv : (Lagrange.nodal A id).derivative = C c) :
    let H := C (c / lam) * (Lagrange.nodal D id / Lagrange.nodal A id)
    H ^ 2 + H = C (lam⁻¹) * Lagrange.nodal D id * H.derivative := by
  have hpart := booleanLocator_partition D A hA
  have hQ0 := Lagrange.nodal_ne_zero (s := A) (v := id)
  have hquot : Lagrange.nodal D id / Lagrange.nodal A id = Lagrange.nodal (D \ A) id := by
    rw [hpart, mul_div_cancel_right₀ _ hQ0]
  dsimp only
  rw [hquot]
  have he := congrArg derivative hpart
  rw [hD, derivative_mul, hderiv] at he
  have hi : C (lam⁻¹) * C lam = (1 : F[X]) := by
    rw [← C_mul, inv_mul_cancel₀ hlam, C_1]
  have he' := congrArg (fun Q : F[X] ↦ C (lam⁻¹) * Q) he
  rw [hi] at he'
  simp only [derivative_mul, derivative_C, zero_mul, zero_add]
  rw [hpart]
  have hc : C (c / lam) = C (lam⁻¹) * C c := by rw [← C_mul]; congr 1; simp [div_eq_mul_inv, mul_comm]
  rw [hc]
  linear_combination -(C (lam⁻¹) * C c * Lagrange.nodal (D \ A) id) * he' +
    (CharP.cast_eq_zero F[X] 2) *
      (C (lam⁻¹) * C c * Lagrange.nodal (D \ A) id -
        C (lam⁻¹)^2 * C c * Lagrange.nodal (D \ A) id *
        (Lagrange.nodal (D \ A) id).derivative * Lagrange.nodal A id)


/-- The converse following Lemma 3.16: the scaled quotient has exactly the
complement's degree and distinct roots, all in the prescribed domain. -/
theorem booleanLocator_converse_roots {F : Type*} [Field F]
    (D A : Finset F) (hA : A ⊆ D) (lam c : F) (hlam : lam ≠ 0) (hc : c ≠ 0) :
    let H := C (c / lam) * (Lagrange.nodal D id / Lagrange.nodal A id)
    H ≠ 0 ∧ H.natDegree = D.card - A.card ∧
      (D.filter fun x ↦ H.eval x = 0) = D \ A ∧
      H.Separable := by
  have hpart := booleanLocator_partition D A hA
  have hQ0 := Lagrange.nodal_ne_zero (s := A) (v := id)
  have hquot : Lagrange.nodal D id / Lagrange.nodal A id = Lagrange.nodal (D \ A) id := by
    rw [hpart, mul_div_cancel_right₀ _ hQ0]
  have hscale : c / lam ≠ 0 := div_ne_zero hc hlam
  dsimp only
  rw [hquot]
  refine ⟨mul_ne_zero (C_ne_zero.mpr hscale) Lagrange.nodal_ne_zero, ?_, ?_, ?_⟩
  · rw [natDegree_C_mul hscale, Lagrange.natDegree_nodal, Finset.card_sdiff_of_subset hA]
  · ext x
    simp only [Finset.mem_filter, eval_mul, eval_C, mul_eq_zero, hscale,
      false_or, booleanLocator_eval_zero_iff, Finset.mem_sdiff]
    tauto
  · apply Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hscale))
    exact separable_prod_X_sub_C_iff'.mpr (by intro a ha b hb h; exact h)

/-- The reformulation following Lemma 3.16 uses the same locator whether the
binary domain is represented by a subgroup or by its finite coordinates. -/
theorem booleanLocator_additiveDomain {F : Type*} [Field F] [Fintype F]
    (D : AddSubgroup F) : Lagrange.nodal (additiveDomain D) id = subspacePolynomial D := by
  exact Finset.prod_subtype (additiveDomain D) (mem_additiveDomain D)
    (fun x : F ↦ X - C x)

/-- The complete converse following Lemma 3.16. A nonzero constant derivative
on the agreement locator gives the literal quotient `H`, its exact degree,
all distinct roots on the domain, and the Boolean differential identity. -/
theorem booleanLocator_converse {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (A : Finset F) (hA : A ⊆ additiveDomain D)
    (c : F) (hc : c ≠ 0) (hderiv : (Lagrange.nodal A id).derivative = C c) :
    let lam := (subspacePolynomial D).coeff 1
    let H := C (c / lam) * (subspacePolynomial D / Lagrange.nodal A id)
    H ≠ 0 ∧ H.natDegree = (additiveDomain D).card - A.card ∧
      ((additiveDomain D).filter fun x ↦ H.eval x = 0) = additiveDomain D \ A ∧
      H.Separable ∧ H ^ 2 + H = C (lam⁻¹) * subspacePolynomial D * H.derivative := by
  have hloc := booleanLocator_additiveDomain D
  have hlin := subspacePolynomial_coeff_one_ne_zero D
  have hD : (Lagrange.nodal (additiveDomain D) id).derivative =
      C ((subspacePolynomial D).coeff 1) := by
    rw [hloc]
    exact Gold.derivative_eq_C_of_binarySupport _ (subspacePolynomial_support D)
  have hr := booleanLocator_converse_roots (additiveDomain D) A hA
    ((subspacePolynomial D).coeff 1) c hlin hc
  have hd := booleanLocator_converse_differential (additiveDomain D) A hA
    ((subspacePolynomial D).coeff 1) c hlin hD hderiv
  rw [hloc] at hr hd
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hd⟩

/-- The reformulation following Lemma 3.16: a polynomial with zero derivative
in a finite binary field is literally the square of its canonical root. -/
theorem booleanLocator_derivative_zero_square {F : Type*} [Field F] [Fintype F]
    [CharP F 2] (Q : F[X]) (hQ : Q.derivative = 0) :
    (primePowerPolynomialRoot 2 1 Q)^2 = Q := by
  apply primePowerPolynomialRoot_pow 2 1 Q
  intro n hn
  simp only [pow_one]
  by_contra hnd
  have hn0 : n ≠ 0 := by intro h; subst n; exact hnd (dvd_zero 2)
  have he := congrArg (fun P : F[X] ↦ P.coeff (n - 1)) hQ
  rw [coeff_derivative, coeff_zero, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)] at he
  have he' : Q.coeff n * (n : F) = 0 := by
    convert he using 1
    congr 1
    calc
      (n : F) = ((n - 1 + 1 : ℕ) : F) := congrArg (fun k : ℕ ↦ (k : F))
        (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)).symm
      _ = (n - 1 : ℕ) + (1 : F) := by rw [Nat.cast_add, Nat.cast_one]
  have hcast : (n : F) ≠ 0 := by
    intro h; exact hnd ((CharP.cast_eq_zero_iff F 2 n).mp h)
  exact (mem_support_iff.mp hn) ((mul_eq_zero.mp he').resolve_right hcast)

/-- The square-plus-linear characterization after Lemma 3.16: the literal
locator has constant derivative `c` exactly when it is a square plus `cX`. -/
theorem booleanLocator_constant_derivative_iff {F : Type*} [Field F] [Fintype F]
    [CharP F 2] (A : Finset F) (c : F) :
    (Lagrange.nodal A id).derivative = C c ↔
      ∃ Q : F[X], Lagrange.nodal A id = Q^2 + C c * X := by
  constructor
  · intro hd
    let Q := Lagrange.nodal A id - C c * X
    have hQ : Q.derivative = 0 := by simp [Q, hd]
    refine ⟨primePowerPolynomialRoot 2 1 Q, ?_⟩
    rw [booleanLocator_derivative_zero_square Q hQ]
    dsimp only [Q]
    ring
  · rintro ⟨Q,hQ⟩
    rw [hQ]
    simp [derivative_pow, CharTwo.two_eq_zero]

/-- The reformulation after Lemma 3.16: a constant-derivative agreement
locator gives a polynomial agreeing with the fixed `R` exactly on `A`, at
exactly twice its degree. It also gives the printed square-plus-linear formula
with `P = Q + R`. -/
theorem booleanLocator_exact_twice_degree {F : Type*} [Field F] [Fintype F]
    [CharP F 2] (D : AddSubgroup F) (A : Finset F)
    (_hA : A ⊆ additiveDomain D) (hsize : 2 ≤ A.card)
    (c : F) (hc : c ≠ 0) (hderiv : (Lagrange.nodal A id).derivative = C c) :
    let lam := (subspacePolynomial D).coeff 1
    let R := binaryQuarterNumerator D 0
    ∃ Q P : F[X], P = Q + R ∧
      2 * Q.natDegree = A.card ∧
      (∀ x ∈ additiveDomain D, Q.eval x = R.eval x ↔ x ∈ A) ∧
      P^2 = subspacePolynomial D + C (lam / c) * Lagrange.nodal A id ∧
      Lagrange.nodal A id = C (c / lam) * (P + R)^2 + C c * X := by
  dsimp only
  let L := subspacePolynomial D
  let lam := L.coeff 1
  let R := binaryQuarterNumerator D 0
  have hlam : lam ≠ 0 := subspacePolynomial_coeff_one_ne_zero D
  let V := C (lam / c) * Lagrange.nodal A id + C lam * X
  have hV : V.derivative = 0 := by
    simp only [V, derivative_add, derivative_mul, derivative_C, zero_mul,
      zero_add, derivative_X, mul_one, hderiv]
    rw [← C_mul, div_mul_cancel₀ lam hc, CharTwo.add_self_eq_zero]
  let Q := primePowerPolynomialRoot 2 1 V
  have hQ : Q^2 = V := booleanLocator_derivative_zero_square V hV
  have hR : R^2 = L + C lam * X := by
    simpa [R, L, lam, binaryQuarterRadicand, CharTwo.sub_eq_add] using binaryQuarterNumerator_sq D 0
  have hscale : lam / c ≠ 0 := div_ne_zero hlam hc
  have hdeg : V.natDegree = A.card := by
    dsimp only [V]
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_C_mul hscale, Lagrange.natDegree_nodal]
    rw [natDegree_C_mul hscale, Lagrange.natDegree_nodal]
    have hlin : (C lam * X).natDegree ≤ 1 := natDegree_mul_le.trans (by simp)
    exact hlin.trans_lt (by omega)
  have hQdeg : 2 * Q.natDegree = A.card := by
    have he := congrArg Polynomial.natDegree hQ
    rw [natDegree_pow, hdeg] at he
    omega
  have heval (x : F) (hx : x ∈ additiveDomain D) :
      Q.eval x = R.eval x ↔ x ∈ A := by
    have hxL : L.eval x = 0 := (subspacePolynomial_eval_eq_zero_iff D x).mpr
      ((mem_additiveDomain D x).mp hx)
    have hqx := congrArg (fun W : F[X] ↦ W.eval x) hQ
    have hrx := congrArg (fun W : F[X] ↦ W.eval x) hR
    simp only [V, eval_pow, eval_add, eval_mul, eval_C, eval_X] at hqx
    simp only [eval_pow, eval_add, eval_mul, eval_C, eval_X, hxL, zero_add] at hrx
    rw [← CharTwo.sq_injective.eq_iff, hqx, hrx]
    rw [add_eq_right, mul_eq_zero, or_iff_right hscale, booleanLocator_eval_zero_iff]
  have hp : (Q + R)^2 = L + C (lam / c) * Lagrange.nodal A id := by
    rw [CharTwo.add_sq, hQ, hR]
    dsimp only [V]
    linear_combination (CharP.cast_eq_zero F[X] 2) * (C lam * X)
  refine ⟨Q, Q + R, rfl, hQdeg, heval, hp, ?_⟩
  have hcancel : Q + R + R = Q := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hcancel, hQ]
  dsimp only [V]
  have hcc : C (c / lam) * C (lam / c) = (1 : F[X]) := by
    rw [← C_mul]
    have he : c / lam * (lam / c) = 1 := by field_simp
    rw [he, C_1]
  have hcl : C (c / lam) * C lam = C c := by rw [← C_mul, div_mul_cancel₀ c hlam]
  rw [mul_add, ← mul_assoc, hcc, one_mul, ← mul_assoc, hcl]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The saturation step in the reformulation after Lemma 3.16: a polynomial
with as many prescribed distinct roots as its degree is a scalar times the
literal locator of those roots. -/
theorem booleanLocator_saturated_eq {F : Type*} [Field F]
    (A : Finset F) (V : F[X]) (hV : V ≠ 0) (hd : V.natDegree = A.card)
    (hr : ∀ x ∈ A, V.eval x = 0) :
    V = C V.leadingCoeff * Lagrange.nodal A id := by
  have hroots : V.roots = A.val := roots_eq_of_natDegree_le_card_of_ne_zero hr hd.le hV
  have hs : V.Splits := splits_iff_card_roots.mpr (by rw [hroots]; exact hd.symm)
  calc
    V = C V.leadingCoeff * (V.roots.map (X - C ·)).prod := hs.eq_prod_roots
    _ = C V.leadingCoeff * Lagrange.nodal A id := by rw [hroots]; rfl

/-- The converse exact-agreement characterization following Lemma 3.16:
saturating the twice-degree root bound forces a nonzero constant derivative
on the agreement locator. -/
theorem booleanLocator_of_exact_twice_degree {F : Type*} [Field F] [Fintype F]
    [CharP F 2] (D : AddSubgroup F) (A : Finset F) (hA : A ⊆ additiveDomain D)
    (hsize : 2 ≤ A.card) (Q : F[X]) (hdeg : 2 * Q.natDegree = A.card)
    (hagr : ∀ x ∈ additiveDomain D, Q.eval x = (binaryQuarterNumerator D 0).eval x ↔ x ∈ A) :
    ∃ c : F, c ≠ 0 ∧ (Lagrange.nodal A id).derivative = C c := by
  let lam := (subspacePolynomial D).coeff 1
  let V := Q^2 + C lam * X
  have hlam : lam ≠ 0 := subspacePolynomial_coeff_one_ne_zero D
  have hVdeg : V.natDegree = A.card := by
    dsimp only [V]
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_pow]
    · omega
    · rw [natDegree_pow]
      have hlin : (C lam * X).natDegree ≤ 1 := natDegree_mul_le.trans (by simp)
      apply hlin.trans_lt
      omega
  have hV0 : V ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hVdeg]; omega)
  have hroots (x : F) (hx : x ∈ A) : V.eval x = 0 := by
    have hxD := hA hx
    have he : Q.eval x = (binaryQuarterNumerator D 0).eval x := (hagr x hxD).mpr hx
    have hR := congrArg (fun W : F[X] ↦ W.eval x) (binaryQuarterNumerator_sq D 0)
    have hL : (subspacePolynomial D).eval x = 0 :=
      (subspacePolynomial_eval_eq_zero_iff D x).mpr ((mem_additiveDomain D x).mp hxD)
    simp only [binaryQuarterRadicand, eval_pow, eval_sub, eval_mul, eval_C,
      eval_X, sub_zero, hL, zero_sub] at hR
    simp only [V, eval_add, eval_pow, eval_mul, eval_C, eval_X, he, hR, lam, neg_add_cancel]
  have hfactor := booleanLocator_saturated_eq A V hV0 hVdeg hroots
  have hv : V.derivative = C lam := by simp [V, derivative_pow, CharTwo.two_eq_zero]
  have hvc : V.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hV0
  have hder := congrArg derivative hfactor
  simp only [hv, derivative_mul, derivative_C, zero_mul, zero_add] at hder
  refine ⟨lam / V.leadingCoeff, div_ne_zero hlam hvc, ?_⟩
  apply mul_left_cancel₀ (C_ne_zero.mpr hvc)
  rw [← hder, ← C_mul, mul_div_cancel₀ lam hvc]

/-- The exact set characterization following Lemma 3.16, with the paper's
implicit size-at-least-two qualification made explicit. -/
theorem booleanLocator_exact_agreement_iff {F : Type*} [Field F] [Fintype F]
    [CharP F 2] (D : AddSubgroup F) (A : Finset F) (hA : A ⊆ additiveDomain D)
    (hsize : 2 ≤ A.card) :
    (∃ c : F, c ≠ 0 ∧ (Lagrange.nodal A id).derivative = C c) ↔
      ∃ Q : F[X], 2 * Q.natDegree = A.card ∧
        ∀ x ∈ additiveDomain D,
          Q.eval x = (binaryQuarterNumerator D 0).eval x ↔ x ∈ A := by
  constructor
  · rintro ⟨c,hc,hd⟩
    obtain ⟨Q,P,hP,hQ,hagr,hs,hformula⟩ :=
      booleanLocator_exact_twice_degree D A hA hsize c hc hd
    exact ⟨Q,hQ,hagr⟩
  · rintro ⟨Q,hd,ha⟩
    exact booleanLocator_of_exact_twice_degree D A hA hsize Q hd ha

/-- The complete hypotheses and level set in the converse after Lemma 3.16:
the literal normalized quotient has all simple roots on the domain, exact
complement degree and root count, takes value one precisely on `A`, and the
agreement cardinality is even. -/
theorem booleanLocator_converse_full {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (A : Finset F) (hA : A ⊆ additiveDomain D)
    (hsize : 2 ≤ A.card) (c : F) (hc : c ≠ 0)
    (hderiv : (Lagrange.nodal A id).derivative = C c) :
    let lam := (subspacePolynomial D).coeff 1
    let H := C (c / lam) * (subspacePolynomial D / Lagrange.nodal A id)
    H ≠ 0 ∧ H.natDegree = (additiveDomain D).card - A.card ∧ H.Separable ∧
      (∀ x : F, H.eval x = 0 ↔ x ∈ additiveDomain D \ A) ∧
      ((additiveDomain D).filter fun x ↦ H.eval x = 0).card =
        (additiveDomain D).card - A.card ∧
      (∀ x ∈ additiveDomain D, H.eval x = 1 ↔ x ∈ A) ∧ Even A.card ∧
      H^2 + H = C (lam⁻¹) * subspacePolynomial D * H.derivative := by
  dsimp only
  let lam := (subspacePolynomial D).coeff 1
  let H := C (c / lam) * (subspacePolynomial D / Lagrange.nodal A id)
  have hlam : lam ≠ 0 := subspacePolynomial_coeff_one_ne_zero D
  have hloc := booleanLocator_additiveDomain D
  have hpart := booleanLocator_partition (additiveDomain D) A hA
  have hquot : subspacePolynomial D / Lagrange.nodal A id =
      Lagrange.nodal (additiveDomain D \ A) id := by
    rw [← hloc, hpart, mul_div_cancel_right₀ _
      (Lagrange.nodal_ne_zero (s := A) (v := id))]
  have hscale : c / lam ≠ 0 := div_ne_zero hc hlam
  have hr (x : F) : H.eval x = 0 ↔ x ∈ additiveDomain D \ A := by
    simp only [H, hquot, eval_mul, eval_C, mul_eq_zero, hscale, false_or,
      booleanLocator_eval_zero_iff]
  have hlevel (x : F) (hx : x ∈ additiveDomain D) : H.eval x = 1 ↔ x ∈ A := by
    constructor
    · intro he
      by_contra hxa
      have hz := (hr x).mpr (Finset.mem_sdiff.mpr ⟨hx,hxa⟩)
      exact zero_ne_one (hz.symm.trans he)
    · intro hxa
      have hd := congrArg (fun W : F[X] ↦ W.derivative.eval x) hpart
      have hD : (Lagrange.nodal (additiveDomain D) id).derivative = C lam := by
        rw [hloc]
        exact Gold.derivative_eq_C_of_binarySupport _ (subspacePolynomial_support D)
      have hz := (booleanLocator_eval_zero_iff A x).mpr hxa
      rw [hD, eval_C, derivative_mul, eval_add, eval_mul, eval_mul,
        hderiv, eval_C, hz, mul_zero, zero_add] at hd
      simp only [H, hquot, eval_mul, eval_C, div_eq_mul_inv]
      calc
        c * lam⁻¹ * (Lagrange.nodal (additiveDomain D \ A) id).eval x =
            ((Lagrange.nodal (additiveDomain D \ A) id).eval x * c) * lam⁻¹ := by ring
        _ = 1 := by rw [←hd, mul_inv_cancel₀ hlam]
  have h := booleanLocator_converse D A hA c hc hderiv
  obtain ⟨Q,P,hP,hQ,hagr,hs,hformula⟩ :=
    booleanLocator_exact_twice_degree D A hA hsize c hc hderiv
  have heven : Even A.card := by
    refine ⟨Q.natDegree, ?_⟩
    omega
  refine ⟨h.1, h.2.1, h.2.2.2.1, hr, ?_, hlevel, heven, h.2.2.2.2⟩
  rw [h.2.2.1, Finset.card_sdiff_of_subset hA]

/-- The forward reformulation after Lemma 3.16, for the literal complementary
square `P`. The agreement set is exactly `H=1`; its locator has derivative
`c ≠ 0` and the paper's displayed formula and quotient normalization. -/
theorem booleanLocator_forward {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (H P : F[X]) (hH : H ≠ 0)
    (hdiv : H ∣ subspacePolynomial D)
    (hbool : H^2 + H = C (((subspacePolynomial D).coeff 1)⁻¹) *
      subspacePolynomial D * H.derivative)
    (hP : P^2 = subspacePolynomial D + subspacePolynomial D / H)
    (T : ℕ) (hT : 2 ≤ T) (hdeg : (subspacePolynomial D / H).natDegree = T)
    (hcount : ((additiveDomain D).filter fun x ↦ P.eval x = 0).card = T) :
    let A := (additiveDomain D).filter fun x ↦ H.eval x = 1
    let lam := (subspacePolynomial D).coeff 1
    let R := binaryQuarterNumerator D 0
    ∃ c : F, c ≠ 0 ∧ A.card = T ∧
      (Lagrange.nodal A id).derivative = C c ∧
      subspacePolynomial D / H = C (lam / c) * Lagrange.nodal A id ∧
      Lagrange.nodal A id = C (c / lam) * (P + R)^2 + C c * X := by
  dsimp only
  let L := subspacePolynomial D
  let lam := L.coeff 1
  let Q := L / H
  let A := (additiveDomain D).filter fun x ↦ H.eval x = 1
  have hlam : lam ≠ 0 := subspacePolynomial_coeff_one_ne_zero D
  have hfactor : L = H * Q := (EuclideanDomain.mul_div_cancel' hH hdiv).symm
  have hD : L.derivative = C lam :=
    Gold.derivative_eq_C_of_binarySupport _ (subspacePolynomial_support D)
  have hroot (x : F) (hx : x ∈ additiveDomain D) : P.eval x = 0 ↔ H.eval x = 1 := by
    have hxL : L.eval x = 0 := (subspacePolynomial_eval_eq_zero_iff D x).mpr
      ((mem_additiveDomain D x).mp hx)
    have he := congrArg (fun V : F[X] ↦ V.eval x) hbool
    simp only [eval_add,eval_pow,eval_mul,eval_C] at he
    change H.eval x ^ 2 + H.eval x = (lam⁻¹ * L.eval x) * H.derivative.eval x at he
    rw [hxL, mul_zero, zero_mul] at he
    have hlevel : H.eval x = 0 ∨ H.eval x = 1 := by
      have hm : H.eval x * (H.eval x + 1) = 0 := by linear_combination he
      rcases mul_eq_zero.mp hm with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h)
    rw [binaryComplement_eval_zero_iff_of_derivative L H Q P lam x hlam hD hfactor hP hxL]
    constructor
    · intro hn; exact hlevel.resolve_left hn
    · intro h; rw [h]; exact one_ne_zero
  have hA : A = (additiveDomain D).filter fun x ↦ P.eval x = 0 := by
    apply Finset.filter_congr
    intro x hx
    exact (hroot x hx).symm
  have hAc : A.card = T := by rw [hA,hcount]
  have hQ0 : Q ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by change 0 < (L / H).natDegree; rw [hdeg]; omega)
  have hQroot (x : F) (hx : x ∈ A) : Q.eval x = 0 := by
    have hp : P.eval x = 0 := (hroot x (Finset.mem_filter.mp hx).1).mpr (Finset.mem_filter.mp hx).2
    have he := congrArg (fun V : F[X] ↦ V.eval x) hP
    have hxL : L.eval x = 0 := (subspacePolynomial_eval_eq_zero_iff D x).mpr
      ((mem_additiveDomain D x).mp (Finset.mem_filter.mp hx).1)
    simp only [eval_add,eval_pow] at he
    change P.eval x ^ 2 = L.eval x + Q.eval x at he
    simpa only [hp, hxL, zero_pow (by decide : 2 ≠ 0), zero_add] using he.symm
  have hs := booleanLocator_saturated_eq A Q hQ0 (hdeg.trans hAc.symm) hQroot
  have hqprime : Q.derivative = C lam := by
    have he := congrArg derivative hP
    rw [derivative_add] at he
    change (P^2).derivative = L.derivative + Q.derivative at he
    simp [derivative_pow, CharTwo.two_eq_zero, hD] at he
    have he' : Q.derivative + C lam = 0 := by simpa only [add_comm] using he.symm
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left he'
  have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  let c := lam / Q.leadingCoeff
  have hc : c ≠ 0 := div_ne_zero hlam hlc
  have hdc : (Lagrange.nodal A id).derivative = C c := by
    have he := congrArg derivative hs
    simp only [hqprime, derivative_mul, derivative_C, zero_mul, zero_add] at he
    apply mul_left_cancel₀ (C_ne_zero.mpr hlc)
    rw [←he, ←C_mul]
    congr 1
    exact (mul_div_cancel₀ lam hlc).symm
  have hratio : lam / c = Q.leadingCoeff := by dsimp only [c]; field_simp
  have hratio' : c / lam = Q.leadingCoeff⁻¹ := by dsimp only [c]; field_simp
  have hsq : (P + binaryQuarterNumerator D 0)^2 = Q + C lam * X := by
    rw [CharTwo.add_sq, hP, binaryQuarterNumerator_sq]
    simp only [binaryQuarterRadicand, map_zero, CharTwo.sub_eq_add]
    linear_combination (CharP.cast_eq_zero F[X] 2) * L
  refine ⟨c,hc,hAc,hdc,?_,?_⟩
  · rw [hratio]; exact hs
  · have hscaled : C Q.leadingCoeff⁻¹ * Q = Lagrange.nodal A id := by
      conv_lhs => arg 2; rw [hs]
      rw [←mul_assoc,←C_mul,inv_mul_cancel₀ hlc,C_1,one_mul]
    rw [hratio',hsq,mul_add,hscaled]
    have hcl : C Q.leadingCoeff⁻¹ * C lam = C c := by
      rw [←C_mul]; congr 1; simp [c,div_eq_mul_inv,mul_comm]
    rw [←mul_assoc,hcl,add_assoc,CharTwo.add_self_eq_zero,add_zero]

/-- The assembled forward reformulation after Lemma 3.16, starting with its
Boolean-factor hypotheses and retaining the literal derivative square-root
polynomial `P` from that lemma. -/
theorem booleanLocator_forward_full {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (H : F[X]) (hH : H ≠ 0) (T : ℕ) (hT : 2 ≤ T)
    (hTN : T ≤ (additiveDomain D).card)
    (hdeg : H.natDegree = (additiveDomain D).card - T)
    (hroots : ((additiveDomain D).filter fun x ↦ H.eval x = 0).card = H.natDegree)
    (hbool : H^2 + H = C (((subspacePolynomial D).coeff 1)⁻¹) *
      subspacePolynomial D * H.derivative) :
    let L := subspacePolynomial D
    let lam := L.coeff 1
    let P := C ((frobeniusEquiv F 2).symm (lam⁻¹)) *
      primePowerPolynomialRoot 2 1 H.derivative * (L / H)
    let A := (additiveDomain D).filter fun x ↦ H.eval x = 1
    let R := binaryQuarterNumerator D 0
    ∃ c : F, c ≠ 0 ∧ A.card = T ∧
      (Lagrange.nodal A id).derivative = C c ∧
      L / H = C (lam / c) * Lagrange.nodal A id ∧
      Lagrange.nodal A id = C (c / lam) * (P + R)^2 + C c * X := by
  dsimp only
  let L := subspacePolynomial D
  let lam := L.coeff 1
  let Q := L / H
  let B := C ((frobeniusEquiv F 2).symm (lam⁻¹)) *
    primePowerPolynomialRoot 2 1 H.derivative
  let P := B * Q
  have hdiv := saturated_boolean_factor_dvd D H hH hroots
  have hfactor : L = H * Q := (EuclideanDomain.mul_div_cancel' hH hdiv).symm
  have hB : B^2 = C (lam⁻¹) * H.derivative := by
    dsimp only [B]
    rw [mul_pow,←map_pow,binaryDerivative_square_root]
    congr 2
    exact (frobeniusEquiv F 2).apply_symm_apply _
  have hc : H + 1 = Q * B^2 := by
    apply mul_left_cancel₀ hH
    rw [hB]
    have hb : H^2 + H = C (lam⁻¹) * L * H.derivative := hbool
    rw [hfactor] at hb
    linear_combination hb
  have hP : P^2 = L + Q := by
    calc
      P^2 = (Q * B^2) * Q := by dsimp only [P]; ring
      _ = (H + 1) * Q := by rw [←hc]
      _ = L + Q := by rw [hfactor]; ring
  have hQ0 : Q ≠ 0 := by
    intro hq
    have he : L = 0 := by rw [hfactor,hq,mul_zero]
    exact (subspacePolynomial_monic D).ne_zero he
  have hQdeg : Q.natDegree = T := by
    have he := congrArg Polynomial.natDegree hfactor
    rw [natDegree_mul hH hQ0,hdeg] at he
    have hcard : L.natDegree = (additiveDomain D).card := by
      simp [L,card_additiveDomain,Nat.card_eq_fintype_card]
    rw [hcard] at he
    omega
  have hlam : lam ≠ 0 := subspacePolynomial_coeff_one_ne_zero D
  have hD : L.derivative = C lam :=
    Gold.derivative_eq_C_of_binarySupport _ (subspacePolynomial_support D)
  have hproot (x : F) (hx : x ∈ additiveDomain D) : P.eval x = 0 ↔ H.eval x ≠ 0 := by
    exact binaryComplement_eval_zero_iff_of_derivative L H Q P lam x hlam hD hfactor hP
      ((subspacePolynomial_eval_eq_zero_iff D x).mpr ((mem_additiveDomain D x).mp hx))
  have hcount : ((additiveDomain D).filter fun x ↦ P.eval x = 0).card = T := by
    have he : (additiveDomain D).filter (fun x ↦ P.eval x = 0) =
        (additiveDomain D).filter (fun x ↦ H.eval x ≠ 0) := by
      apply Finset.filter_congr
      exact hproot
    rw [he]
    have hn := Finset.card_filter_add_card_filter_not (s := additiveDomain D)
      (fun x ↦ H.eval x = 0)
    rw [hroots,hdeg] at hn
    change ((additiveDomain D).card - T) +
      ((additiveDomain D).filter fun x ↦ H.eval x ≠ 0).card =
      (additiveDomain D).card at hn
    omega
  exact booleanLocator_forward D H P hH hdiv hbool hP T hT hQdeg hcount

/-- The corrected affine-subspace clause after Lemma 3.16: every affine flat
of cardinality `2^(m+1)` contained in `D` is the exact agreement set of a
polynomial with `R`, and its cardinality is twice that polynomial's degree.
This includes positive-dimensional flats, hyperplanes, and the whole domain. -/
theorem booleanLocator_affine_exact_agreement
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (D : AddSubgroup F) (flat : AffineSubspace (ZMod 2) F)
    (a : F) (ha : a ∈ flat) (hflat : ∀ x ∈ flat, x ∈ D)
    (m : ℕ) (hcard : Nat.card flat = 2^(m+1)) :
    ∃ Q : F[X], Q.natDegree = 2^m ∧
      ∀ x ∈ additiveDomain D,
        Q.eval x = (binaryQuarterNumerator D 0).eval x ↔ x ∈ flat := by
  let A : Finset F := Finset.univ.filter fun x ↦ x ∈ flat
  have hmem (x : F) : x ∈ A ↔ x ∈ flat := by simp [A]
  have hAc : A.card = 2^(m+1) := by
    have he : A.card = Nat.card flat := by
      simp only [A, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact he.trans hcard
  have hA : A ⊆ additiveDomain D := fun x hx ↦
    (mem_additiveDomain D x).mpr (hflat x ((hmem x).mp hx))
  obtain ⟨hr,c,hc,hd,Q,hQ,hsq⟩ := affineFlatLocator_square_full flat a ha m hcard
  let e : flat.direction ≃ flat :=
    { toFun := fun v ↦ ⟨(v : F) + a, by
        apply (AffineSubspace.vsub_right_mem_direction_iff_mem ha _).mp
        change (v : F) + a - a ∈ flat.direction
        simpa only [add_sub_cancel_right] using v.property⟩
      invFun := fun x ↦ ⟨(x : F) - a,
        (AffineSubspace.vsub_right_mem_direction_iff_mem ha (x : F)).mpr x.property⟩
      left_inv := by intro v; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  have hdegree : (affineFlatLocator flat a).natDegree = A.card := by
    rw [affineFlatLocator_natDegree]
    exact (Nat.card_congr e).trans (hcard.trans hAc.symm)
  have hloc := booleanLocator_saturated_eq A (affineFlatLocator flat a)
    (affineFlatLocator_monic flat a).ne_zero hdegree
    (fun x hx ↦ (hr x).mpr ((hmem x).mp hx))
  rw [(affineFlatLocator_monic flat a).leadingCoeff,C_1,one_mul] at hloc
  have hder : (Lagrange.nodal A id).derivative = C c := by rw [←hloc]; exact hd
  have hsize : 2 ≤ A.card := by rw [hAc,pow_succ]; have := Nat.two_pow_pos m; omega
  obtain ⟨W,P,hP,hW,hagr,hs,hformula⟩ :=
    booleanLocator_exact_twice_degree D A hA hsize c hc hder
  have hWdeg : W.natDegree = 2^m := by rw [hAc,pow_succ] at hW; omega
  exact ⟨W,hWdeg,fun x hx ↦ (hagr x hx).trans (hmem x)⟩

/-- The qualification needed for the affine-subspace sentence after Lemma
3.16: a singleton cannot saturate agreement at twice an integer degree. -/
theorem booleanLocator_singleton_not_twice_degree {F : Type*} [Field F] (a : F) :
    ¬ ∃ Q : F[X], 2 * Q.natDegree = ({a} : Finset F).card := by
  simp only [Finset.card_singleton]
  rintro ⟨Q,hQ⟩
  omega

end BinaryFieldCounterexamples.NearUnit
