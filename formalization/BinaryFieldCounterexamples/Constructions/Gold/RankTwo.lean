/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FullSource
public import BinaryFieldCounterexamples.Polynomial.LocatorElimination
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import BinaryFieldCounterexamples.Polynomial.QuadraticDifferential
/-!
# The rank-two subspace-locator specialization

The rank-two paragraph following Lemma 5.12 uses a codimension-two subspace
`W` of the actual prescribed domain `D`. Its quartic locator composition,
Boolean majority factor, and square-root locator are literal polynomials.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial BinaryLocator
attribute [local instance] Classical.decEq Classical.propDecidable
set_option linter.unusedSectionVars false
variable {B : Type*} [Field B] [Fintype B] [CharP B 2]

/-- The rank-two paragraph after Lemma 5.12: every index-four subspace
locator is a quartic right factor of the prescribed domain locator. -/
theorem rankTwo_locator_composition (D W : AddSubgroup B)
    (hWD : W ≤ D) (hcard : Nat.card D = 4*Nat.card W) :
    ∃ u v : B, v ≠ 0 ∧
      subspacePolynomial D = subspacePolynomial W^4+
        C u*subspacePolynomial W^2+C v*subspacePolynomial W := by
  let f : D →+ B :=
    { toFun := fun x => (subspacePolynomial W).eval x
      map_zero' := by simp
      map_add' := fun x y => subspacePolynomial_eval_add W x y }
  let e : f.ker ≃ W :=
    { toFun := fun x => ⟨x.val.val,(subspacePolynomial_eval_eq_zero_iff W x.val.val).mp x.property⟩
      invFun := fun w => ⟨⟨w.val,hWD w.property⟩,
        (subspacePolynomial_eval_eq_zero_iff W w.val).mpr w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hk : Nat.card f.ker = Nat.card W := Nat.card_congr e
  have hquot := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have hrange : Nat.card f.range = 4 := by
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
    rw [hk,hcard] at hquot
    have hp : 0 < Nat.card W := Nat.card_pos
    nlinarith
  let Q := subspacePolynomial f.range
  have hQdeg : Q.natDegree = 4 := by
    rw [subspacePolynomial_natDegree,← Nat.card_eq_fintype_card,hrange]
  have hQ : Q = X^4+C (Q.coeff 2)*X^2+C (Q.coeff 1)*X := by
    ext n
    by_cases hn : n=4
    · subst n
      have hc := (subspacePolynomial_monic f.range).coeff_natDegree
      rw [show (subspacePolynomial f.range).natDegree = 4 from hQdeg] at hc
      simpa [Q,coeff_add,coeff_C_mul] using hc
    by_cases hn2 : n=2
    · subst n; simp
    by_cases hn1 : n=1
    · subst n; simp
    have hc : Q.coeff n = 0 := by
      by_contra hc
      obtain ⟨i,hi⟩ := subspacePolynomial_support f.range n (mem_support_iff.mpr hc)
      have hh : n ≤ 4 := (le_natDegree_of_ne_zero hc).trans_eq hQdeg
      have hi2 : i ≤ 2 := by
        apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
        simpa only [hi] using hh
      interval_cases i <;> norm_num at hi <;> omega
    simp [hc,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,hn,hn2,Ne.symm hn1]
  have hcomp : Q.comp (subspacePolynomial W) = subspacePolynomial D := by
    have hdvd : subspacePolynomial D ∣ Q.comp (subspacePolynomial W) := by
      apply subspacePolynomial_dvd_of_eval_zero
      intro x
      rw [eval_comp]
      exact (subspacePolynomial_eval_eq_zero_iff f.range (f x)).mpr ⟨x,rfl⟩
    apply eq_of_monic_of_dvd_of_natDegree_le (subspacePolynomial_monic D)
      ((subspacePolynomial_monic f.range).comp (subspacePolynomial_monic W)
        (by rw [subspacePolynomial_natDegree]; exact Fintype.card_ne_zero)) hdvd
    rw [natDegree_comp,hQdeg,subspacePolynomial_natDegree,subspacePolynomial_natDegree,
      ← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hcard]
  refine ⟨Q.coeff 2,Q.coeff 1,subspacePolynomial_coeff_one_ne_zero f.range,?_⟩
  rw [← hcomp,hQ]
  simp


/-- The rank-two paragraph's actual majority polynomial
`H=L_D/(v_W L_W)`, written without polynomial division. -/
noncomputable def rankTwoBooleanFactor (W : AddSubgroup B) (u v : B) : B[X] :=
  C v⁻¹*(subspacePolynomial W^3+C u*subspacePolynomial W+C v)

/-- The rank-two paragraph's literal locator `P=L_W²+√u_W L_W`. -/
noncomputable def rankTwoLocator (W : AddSubgroup B) (u : B) : B[X] :=
  subspacePolynomial W^2+C ((frobeniusEquiv B 2).symm u)*subspacePolynomial W

/-- The rank-two locator's square is `L_D+v_W L_W`, for the actual
index-four locator composition of the rank-two paragraph. -/
theorem rankTwoLocator_sq (D W : AddSubgroup B) (u v : B)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) :
    rankTwoLocator W u^2 = subspacePolynomial D+C v*subspacePolynomial W := by
  rw [rankTwoLocator,CharTwo.add_sq,mul_pow,←map_pow,frobeniusEquiv_symm_pow_p,hcomp]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- The majority factor in the rank-two paragraph is the literal quotient
`L_D/(v_W L_W)` and a divisor of `L_D`. -/
theorem rankTwoBooleanFactor_quotient (D W : AddSubgroup B) (u v : B) (hv : v ≠ 0)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) :
    rankTwoBooleanFactor W u v = subspacePolynomial D/(C v*subspacePolynomial W) := by
  have hm : (C v*subspacePolynomial W)*rankTwoBooleanFactor W u v = subspacePolynomial D := by
    rw [rankTwoBooleanFactor,hcomp]
    have hc : C v*C v⁻¹ = (1 : B[X]) := by rw [←C_mul,mul_inv_cancel₀ hv,C_1]
    calc
      _ = (C v*C v⁻¹)*(subspacePolynomial W*
          (subspacePolynomial W^3+C u*subspacePolynomial W+C v)) := by ring
      _ = _ := by rw [hc]; ring
  exact (EuclideanDomain.eq_div_of_mul_eq_right
    (mul_ne_zero (C_ne_zero.mpr hv) (subspacePolynomial_monic W).ne_zero) hm)


/-- The rank-two paragraph's quotient factorization, as an exact product
identity needed to identify its majority zero set. -/
theorem rankTwoBooleanFactor_mul (D W : AddSubgroup B) (u v : B) (hv : v ≠ 0)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) :
    (C v*subspacePolynomial W)*rankTwoBooleanFactor W u v = subspacePolynomial D := by
  rw [rankTwoBooleanFactor,hcomp]
  have hc : C v*C v⁻¹ = (1 : B[X]) := by rw [←C_mul,mul_inv_cancel₀ hv,C_1]
  calc
    _ = (C v*C v⁻¹)*(subspacePolynomial W*
        (subspacePolynomial W^3+C u*subspacePolynomial W+C v)) := by ring
    _ = _ := by rw [hc]; ring

/-- The rank-two paragraph: the literal factor `H` equals one on `W` and
zero on `D \ W`, so its values on the prescribed domain are Boolean. -/
theorem rankTwoBooleanFactor_eval (D W : AddSubgroup B) (u v : B) (hv : v ≠ 0)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) (x : D) :
    (rankTwoBooleanFactor W u v).eval (x : B) = if (x : B) ∈ W then 1 else 0 := by
  split_ifs with hx
  · simp [rankTwoBooleanFactor,(subspacePolynomial_eval_eq_zero_iff W x).mpr hx,hv]
  · have he := congrArg (fun p : B[X] => p.eval (x : B)) (rankTwoBooleanFactor_mul D W u v hv hcomp)
    rw [eval_mul,eval_mul,eval_C,
      (subspacePolynomial_eval_eq_zero_iff D x).mpr x.property] at he
    exact (mul_eq_zero.mp he).resolve_left
      (mul_ne_zero hv (fun h => hx ((subspacePolynomial_eval_eq_zero_iff W x).mp h)))

/-- The rank-two paragraph: all roots of the majority factor are simple,
and every root belongs to `D`. -/
theorem rankTwoBooleanFactor_roots (D W : AddSubgroup B) (u v : B) (hv : v ≠ 0)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) :
    (rankTwoBooleanFactor W u v).Separable ∧
      ∀ x : B, (rankTwoBooleanFactor W u v).eval x = 0 → x ∈ D := by
  have hdvd : rankTwoBooleanFactor W u v ∣ subspacePolynomial D :=
    ⟨C v*subspacePolynomial W,by rw [mul_comm]; exact (rankTwoBooleanFactor_mul D W u v hv hcomp).symm⟩
  refine ⟨(subspacePolynomial_separable D).of_dvd hdvd,?_⟩
  intro x hx
  apply (subspacePolynomial_eval_eq_zero_iff D x).mp
  exact eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hx

/-- The rank-two paragraph's exact majority count: `H` has `|D|-|W|`
roots on `D`, hence `3N/4` when `W` has index four. -/
theorem rankTwoBooleanFactor_root_count (D W : AddSubgroup B) (hWD : W ≤ D)
    (u v : B) (hv : v ≠ 0)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) :
    ((additiveDomain D).filter (fun x => (rankTwoBooleanFactor W u v).eval x=0)).card =
      Nat.card D-Nat.card W := by
  have he : (additiveDomain D).filter (fun x => (rankTwoBooleanFactor W u v).eval x=0) =
      additiveDomain D \ additiveDomain W := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    constructor
    · rintro ⟨hx,hzero⟩
      have hxD : x ∈ D := by simpa [additiveDomain] using hx
      refine ⟨hx,?_⟩
      intro hxW
      have hmem : x ∈ W := by simpa [additiveDomain] using hxW
      have hh := rankTwoBooleanFactor_eval D W u v hv hcomp ⟨x,hxD⟩
      simp [hmem,hzero] at hh
    · rintro ⟨hx,hxW⟩
      refine ⟨hx,?_⟩
      have hxD : x ∈ D := by simpa [additiveDomain] using hx
      have hmem : x ∉ W := by simpa [additiveDomain] using hxW
      simpa [hmem] using rankTwoBooleanFactor_eval D W u v hv hcomp ⟨x,hxD⟩
  have hsubset : additiveDomain W ⊆ additiveDomain D := by
    intro x hx
    have hw : x ∈ W := by simpa [additiveDomain] using hx
    simpa [additiveDomain] using hWD hw
  rw [he,Finset.card_sdiff_of_subset hsubset]
  have hc (A : AddSubgroup B) : (additiveDomain A).card = Nat.card A := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    rfl
  rw [hc D,hc W]


/-- The rank-two paragraph's linear coefficient identity
`lambda_0 = v_W L_W'`, with `L_W'` expressed by its constant coefficient. -/
theorem rankTwo_linear_coefficient (D W : AddSubgroup B) (u v : B)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) :
    (subspacePolynomial D).coeff 1 = v*(subspacePolynomial W).coeff 1 := by
  have he := congrArg (fun p : B[X] => p.derivative.coeff 0) hcomp
  have hw0 : (subspacePolynomial W).eval 0 = 0 :=
    (subspacePolynomial_eval_eq_zero_iff W 0).mpr W.zero_mem
  simpa [derivative_add,derivative_pow,derivative_mul,derivative_C,hw0,
    derivative_eq_C_of_binarySupport _ (subspacePolynomial_support W),
    derivative_eq_C_of_binarySupport _ (subspacePolynomial_support D),
    coeff_zero_eq_eval_zero,CharTwo.two_eq_zero] using he

/-- The rank-two paragraph's full-source degree: `P+R` has degree `N/8`.
Writing `|W|=2^(k+1)` expresses every domain dimension `d=k+3 ≥ 3`. -/
theorem rankTwoLocator_fullSource_natDegree (D W : AddSubgroup B)
    (k : ℕ) (hW : Nat.card W = 2^(k+1)) (u v : B) (hv : v ≠ 0)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) :
    (rankTwoLocator W u+goldFullSourcePolynomial D).natDegree = 2^k := by
  have hsq : (rankTwoLocator W u+goldFullSourcePolynomial D)^2 =
      C v*subspacePolynomial W+C ((subspacePolynomial D).coeff 1)*X := by
    rw [CharTwo.add_sq,rankTwoLocator_sq D W u v hcomp,goldFullSourcePolynomial_sq]
    ring_nf
    simp [CharTwo.two_eq_zero]
  have hdeg : (C v*subspacePolynomial W).natDegree = 2^(k+1) := by
    rw [natDegree_C_mul hv,subspacePolynomial_natDegree,←Nat.card_eq_fintype_card,hW]
  have hlin : (C ((subspacePolynomial D).coeff 1)*X).natDegree ≤ 1 := by
    simpa using natDegree_mul_le (p := C ((subspacePolynomial D).coeff 1)) (q := X)
  have hbig : 1 < (2 : ℕ)^(k+1) := Nat.one_lt_pow (by omega) (by decide)
  have he := congrArg natDegree hsq
  rw [natDegree_pow,natDegree_add_eq_left_of_natDegree_lt (hlin.trans_lt
    (hdeg.symm ▸ hbig)),hdeg,pow_succ] at he
  omega

/-- The rank-two paragraph's coefficient comparison with Theorem 4.1's
subspace-locator construction: `√u_W=a_W²+√lambda_(d-1)`. -/
theorem rankTwo_sqrt_coefficient (D W : AddSubgroup B)
    (k : ℕ) (hW : Nat.card W = 2^(k+1)) (u v : B)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) :
    (frobeniusEquiv B 2).symm u = (subspacePolynomial W).coeff (2^k)^2+
      (frobeniusEquiv B 2).symm ((subspacePolynomial D).coeff (2^(k+2))) := by
  have hdeg : (subspacePolynomial W).natDegree = 2^(k+1) := by
    rw [subspacePolynomial_natDegree,←Nat.card_eq_fintype_card,hW]
  have htop : (subspacePolynomial W).coeff (2^(k+1)) = 1 := by
    rw [←hdeg]; exact (subspacePolynomial_monic W).coeff_natDegree
  have hlarge : (subspacePolynomial W).coeff (2^(k+2))=0 := coeff_eq_zero_of_natDegree_lt
    (by rw [hdeg]; exact Nat.pow_lt_pow_right (by decide) (by omega))
  have hc := congrArg (fun p : B[X] => p.coeff (2^(k+2))) hcomp
  rw [coeff_add,coeff_add,coeff_C_mul,coeff_C_mul,hlarge,mul_zero,add_zero] at hc
  have h4 : (subspacePolynomial W^4).coeff (2^(k+2)) =
      (subspacePolynomial W).coeff (2^k)^4 := by
    simpa only [Nat.add_comm,show (2:ℕ)^2=4 by decide] using AllRatesConstruction.coeff_pow_two_pow (subspacePolynomial W) 2 k
  have h2 : (subspacePolynomial W^2).coeff (2^(k+2)) = 1 := by
    have hh := AllRatesConstruction.coeff_pow_two_pow (subspacePolynomial W) 1 (k+1)
    simpa [show 1+(k+1)=k+2 by omega,htop] using hh
  rw [h4,h2,mul_one] at hc
  apply CharTwo.sq_injective
  dsimp only
  rw [CharTwo.add_sq,frobeniusEquiv_symm_pow_p,frobeniusEquiv_symm_pow_p,hc]
  ring_nf
  simp [CharTwo.two_eq_zero]


/-- The rank-two paragraph: the majority polynomial satisfies the Boolean
source-conversion differential identity with the prescribed domain locator. -/
theorem rankTwoBooleanFactor_artinSchreier (D W : AddSubgroup B) (u v : B) (hv : v ≠ 0)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) :
    rankTwoBooleanFactor W u v^2+rankTwoBooleanFactor W u v =
      normalizedLocator D*(rankTwoBooleanFactor W u v).derivative := by
  have hH : rankTwoBooleanFactor W u v ≠ 0 := by
    intro hz
    have he := congrArg (fun p : B[X] => p.eval 0) hz
    have hw0 : (subspacePolynomial W).eval 0 = 0 :=
      (subspacePolynomial_eval_eq_zero_iff W 0).mpr W.zero_mem
    simp [rankTwoBooleanFactor,hv,hw0] at he
  have hfactor := rankTwoBooleanFactor_mul D W u v hv hcomp
  have hsmall : (rankTwoBooleanFactor W u v).natDegree < Fintype.card D := by
    have he := congrArg natDegree hfactor
    rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr hv) (subspacePolynomial_monic W).ne_zero)
      hH,natDegree_C_mul hv,subspacePolynomial_natDegree,subspacePolynomial_natDegree] at he
    have hpos : 0 < Fintype.card W := Fintype.card_pos
    omega
  have hfixed : ∀ x ∈ D, (rankTwoBooleanFactor W u v).eval x^2 =
      (rankTwoBooleanFactor W u v).eval x := by
    intro x hx
    rw [rankTwoBooleanFactor_eval D W u v hv hcomp ⟨x,hx⟩]
    split_ifs <;> norm_num
  have he := QuadraticLocatorConversion.differential_identity_of_fixed_values 2 1
    (by omega) D (rankTwoBooleanFactor W u v) ((subspacePolynomial D).coeff 1)
    (subspacePolynomial_coeff_one_ne_zero D)
    (derivative_eq_C_of_binarySupport _ (subspacePolynomial_support D)) hfixed (by
      norm_num
      omega)
  simpa [normalizedLocator,CharTwo.sub_eq_add,CharTwo.neg_eq] using he

/-- The rank-two paragraph's second displayed form of the Boolean identity:
`H²+H=H L_W(L_W²+u_W)/v_W`. -/
theorem rankTwoBooleanFactor_square_add (W : AddSubgroup B) (u v : B) (hv : v ≠ 0) :
    rankTwoBooleanFactor W u v^2+rankTwoBooleanFactor W u v =
      C v⁻¹*rankTwoBooleanFactor W u v*subspacePolynomial W*(subspacePolynomial W^2+C u) := by
  let H := rankTwoBooleanFactor W u v
  have hplus : H+1 = C v⁻¹*subspacePolynomial W*(subspacePolynomial W^2+C u) := by
    have hc : C v⁻¹*C v = (1 : B[X]) := by rw [←C_mul,inv_mul_cancel₀ hv,C_1]
    dsimp [H,rankTwoBooleanFactor]
    calc
      _ = C v⁻¹*(subspacePolynomial W*(subspacePolynomial W^2+C u))+C v⁻¹*C v+1 := by ring
      _ = _ := by rw [hc,add_assoc,CharTwo.add_self_eq_zero,add_zero]; ring
  change H^2+H = _
  calc
    _ = H*(H+1) := by ring
    _ = _ := by rw [hplus]; ring


/-- The rank-two paragraph: for every rank-two quadratic and every linear
repair vanishing on its polar radical, the smaller level is exactly one
coset of that radical. The other level has `3N/4` points. -/
theorem rankTwo_smaller_level_coset {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (Q : BinaryQuadraticData V)
    (l : Module.Dual (ZMod 2) V) (hl : l ∈ Q.repairs) (k : ℕ)
    (hdim : Module.finrank (ZMod 2) V = k+3)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range Q.polarMap) = 2) :
    ∃ κ : ZMod 2, ∃ a : V,
      (∀ x : V, Q.toFun x+l x+κ=1 ↔ x-a ∈ Q.radical) ∧
      BinaryQuadraticData.zeroCount (fun x => Q.toFun x+l x+κ) = 3*2^(k+1) ∧
      Module.finrank (ZMod 2) Q.radical = k+1 := by
  obtain ⟨κ,hκ,_⟩ := Q.exists_bit_zeroCount_of_polarRank l hl (k+3) 1 (by omega) hdim
    (by simpa using hrank)
  have hκ' : BinaryQuadraticData.zeroCount (fun x => Q.toFun x+l x+κ) = 3*2^(k+1) := by
    simp [pow_succ] at hκ ⊢
    omega
  let q : V → ZMod 2 := fun x => Q.toFun x+l x+κ
  have hV : Nat.card V = 2^(k+3) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hdim,Nat.card_eq_fintype_card,ZMod.card]
  have hrad : Nat.card Q.radical = 2^(k+1) := by
    rw [Q.card_radical_of_polarRank 2 hrank,hV]
    rw [show k+3=(k+1)+2 by omega,pow_add]
    norm_num
  have hones : Nat.card {x : V // q x=1} = 2^(k+1) := by
    have he : {x : V // q x=1} ≃ {x : V // ¬q x=0} :=
      Equiv.subtypeEquivRight (fun x => by
        rcases binary_eq_zero_or_one (q x) with h | h <;> simp [h])
    rw [Nat.card_congr he,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
      ←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hV]
    change 2^(k+3)-BinaryQuadraticData.zeroCount q=2^(k+1)
    rw [hκ']
    simp [pow_succ]
    omega
  have honepos : 0 < Nat.card {x : V // q x=1} := by rw [hones]; positivity
  obtain ⟨⟨a,ha⟩⟩ := (Nat.card_pos_iff.mp honepos).1
  let f : Q.radical → {x : V // q x=1} := fun r => ⟨a+r,by
    simpa [q] using (quadraticRepair_add_radical Q l κ hl a r).trans ha⟩
  have hinj : Function.Injective f := by
    intro r s he
    have hh : (r : V) = (s : V) := add_left_cancel (congrArg Subtype.val he)
    exact Subtype.ext hh
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,by
      rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hrad,hones]⟩).2
  have hradDim : Module.finrank (ZMod 2) Q.radical = k+1 := by
    have he := Q.polarMap.finrank_range_add_finrank_ker
    change Module.finrank (ZMod 2) (LinearMap.ker Q.polarMap) = k+1
    rw [hdim,hrank] at he
    omega
  refine ⟨κ,a,?_,hκ',hradDim⟩
  intro x
  constructor
  · intro hx
    obtain ⟨r,hr⟩ := hsurj ⟨x,hx⟩
    have he : a+(r : V)=x := congrArg Subtype.val hr
    rw [←he,add_sub_cancel_left]
    exact r.property
  · intro hx
    have he := quadraticRepair_add_radical Q l κ hl a ⟨x-a,hx⟩
    simpa [q,ha] using he


/-- The rank-two paragraph: `P` vanishes on precisely the smaller subspace
level `W` inside `D`, recovering its `N/4` agreement set. -/
theorem rankTwoLocator_eval_eq_zero_iff (D W : AddSubgroup B) (u v : B) (hv : v ≠ 0)
    (hcomp : subspacePolynomial D = subspacePolynomial W^4+
      C u*subspacePolynomial W^2+C v*subspacePolynomial W) (x : D) :
    (rankTwoLocator W u).eval (x : B)=0 ↔ (x : B) ∈ W := by
  constructor
  · intro hx
    have he := congrArg (fun p : B[X] => p.eval (x : B)) (rankTwoLocator_sq D W u v hcomp)
    simp only [eval_pow,eval_add,eval_mul,eval_C,hx,zero_pow (by decide : 2 ≠ 0),
      (subspacePolynomial_eval_eq_zero_iff D x).mpr x.property,zero_add] at he
    exact (subspacePolynomial_eval_eq_zero_iff W x).mp
      ((mul_eq_zero.mp he.symm).resolve_left hv)
  · intro hx
    simp [rankTwoLocator,(subspacePolynomial_eval_eq_zero_iff W x).mpr hx]

/-- All polynomial clauses of the rank-two paragraph after Lemma 5.12 in
one theorem, on each actual index-four subspace `W ≤ D` with `d=k+3 ≥ 3`:
quartic composition, the normalized Boolean quotient, its `3N/4` simple
roots, the source-conversion identity, the exact locator, its smaller level,
the coefficient match with Theorem 4.1, and full-source degree `N/8`. -/
theorem rankTwo_subspace_locators_full (D W : AddSubgroup B) (hWD : W ≤ D)
    (k : ℕ) (hD : Nat.card D=2^(k+3)) (hW : Nat.card W=2^(k+1)) :
    ∃ u v : B, v ≠ 0 ∧
      subspacePolynomial D = subspacePolynomial W^4+
        C u*subspacePolynomial W^2+C v*subspacePolynomial W ∧
      (subspacePolynomial D).coeff 1 = v*(subspacePolynomial W).coeff 1 ∧
      rankTwoBooleanFactor W u v = subspacePolynomial D/(C v*subspacePolynomial W) ∧
      (rankTwoBooleanFactor W u v).Separable ∧
      (∀ x : B, (rankTwoBooleanFactor W u v).eval x=0 → x ∈ D) ∧
      ((additiveDomain D).filter (fun x => (rankTwoBooleanFactor W u v).eval x=0)).card = 3*2^(k+1) ∧
      rankTwoBooleanFactor W u v^2+rankTwoBooleanFactor W u v =
        normalizedLocator D*(rankTwoBooleanFactor W u v).derivative ∧
      rankTwoBooleanFactor W u v^2+rankTwoBooleanFactor W u v =
        C v⁻¹*rankTwoBooleanFactor W u v*subspacePolynomial W*(subspacePolynomial W^2+C u) ∧
      rankTwoLocator W u^2 = subspacePolynomial D+C v*subspacePolynomial W ∧
      (∀ x : D, (rankTwoLocator W u).eval (x : B)=0 ↔ (x : B) ∈ W) ∧
      (frobeniusEquiv B 2).symm u = (subspacePolynomial W).coeff (2^k)^2+
        (frobeniusEquiv B 2).symm ((subspacePolynomial D).coeff (2^(k+2))) ∧
      (rankTwoLocator W u+goldFullSourcePolynomial D).natDegree=2^k := by
  have hcard : Nat.card D=4*Nat.card W := by rw [hD,hW]; simp [pow_succ]; ring
  obtain ⟨u,v,hv,hcomp⟩ := rankTwo_locator_composition D W hWD hcard
  have hroots := rankTwoBooleanFactor_roots D W u v hv hcomp
  refine ⟨u,v,hv,hcomp,rankTwo_linear_coefficient D W u v hcomp,
    rankTwoBooleanFactor_quotient D W u v hv hcomp,hroots.1,hroots.2,?_,
    rankTwoBooleanFactor_artinSchreier D W u v hv hcomp,
    rankTwoBooleanFactor_square_add W u v hv,rankTwoLocator_sq D W u v hcomp,
    rankTwoLocator_eval_eq_zero_iff D W u v hv hcomp,
    rankTwo_sqrt_coefficient D W k hW u v hcomp,
    rankTwoLocator_fullSource_natDegree D W k hW u v hv hcomp⟩
  rw [rankTwoBooleanFactor_root_count D W hWD u v hv hcomp,hD,hW]
  simp [pow_succ]
  omega


/-- The rank-two paragraph's unrepaired formulation: a rank-two quadratic
vanishing on its radical has a smaller level that is one coset of that
codimension-two radical. This is the case explicitly used by the paper. -/
theorem rankTwo_vanishing_radical_smaller_level_coset {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (Q : BinaryQuadraticData V) (k : ℕ)
    (hdim : Module.finrank (ZMod 2) V = k+3)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range Q.polarMap) = 2)
    (hzero : ∀ x : Q.radical, Q.toFun x=0) :
    ∃ κ : ZMod 2, ∃ a : V,
      (∀ x : V, Q.toFun x+κ=1 ↔ x-a ∈ Q.radical) ∧
      BinaryQuadraticData.zeroCount (fun x => Q.toFun x+κ) = 3*2^(k+1) ∧
      Module.finrank (ZMod 2) Q.radical = k+1 := by
  have hl : (0 : Module.Dual (ZMod 2) V) ∈ Q.repairs := by
    apply (Q.mem_repairs_iff 0).mpr
    intro r
    simpa using hzero r
  simpa using rankTwo_smaller_level_coset Q 0 hl k hdim hrank

end BinaryFieldCounterexamples.Gold
