/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.QuadraticConversionCount
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.TraceRestriction
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceLocators
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceTranslationCount
public import BinaryFieldCounterexamples.Counting.GaussianIdentities
/-!
# Actual quadratic seed lists on every affine binary domain

The literal translated trace polynomials supply distinct conversion inputs.
Their proven polar rank gives a uniform root lower bound on the prescribed
binary affine domain. Conversion loses at most the scalar factor q−1, and the
actual minimum-rank population gives the displayed Gaussian list lower bound.
All explaining polynomials keep the original strict full-field degree bound.
-/
@[expose] public section
set_option warn.classDefReducibility false
namespace BinaryFieldCounterexamples.QuadraticLocatorConversion
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
/-- Quotient conversion multiplicity and build a finite family of distinct strict-degree explaining polynomials. -/
theorem exists_explanation_family_of_conversion_lower {F I : Type*} [Field F] [Fintype I]
    (G : I → F[X]) (L R : F[X]) (D : Finset F) (q K : ℕ) (T : ℝ) (hq : 2≤q)
    (hinj : Function.Injective G) (hne : ∀ i,G i≠0)
    (hfactor : ∀ i,∃ A P U : F[X], G i=A*P ∧ A^(q-1)*(P^q-L)=P ∧
      P=R+U ∧ U.degree<K ∧ T≤(agreementCount D (fun x => R.eval x.val) (-U):ℝ)) :
    ∃ E : Finset F[X], (Fintype.card I : ℚ)/(q-1)≤E.card ∧
      ∀ f∈E,f.degree<K ∧ T≤(agreementCount D (fun x => R.eval x.val) f:ℝ) := by
  classical
  choose A P U hG hconv hPU hdU hagr using hfactor
  let E := Finset.univ.image (fun i => -U i)
  have hE : E=(Finset.univ.image P).image (fun Q => R-Q) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro i hi
    dsimp
    rw [hPU]
    ring
  have hcard : E.card=(Finset.univ.image P).card := by
    rw [hE]
    exact Finset.card_image_iff.mpr (fun Q hQ S hS he => sub_right_injective he)
  have hcNat := converted_family_card_le G A P L q hq hinj hne hG hconv
  rw [←hcard] at hcNat
  refine ⟨E,?_,?_⟩
  · have hcRat : (Fintype.card I : ℚ)≤((q-1 : ℕ) : ℚ)*E.card := by exact_mod_cast hcNat
    have hqRat : (0 : ℚ)<(q : ℚ)-1 := by
      have hq2 : (2 : ℚ)≤q := by exact_mod_cast hq
      linarith
    apply (div_le_iff₀ hqRat).mpr
    simpa [Nat.cast_sub (by omega : 1≤q),mul_comm] using hcRat
  · intro f hf
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
    exact ⟨by simpa using hdU i,hagr i⟩
end BinaryFieldCounterexamples.QuadraticLocatorConversion
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [CharP k 2]
  [Field B] [Fintype B] [CharP B 2] [Algebra k B]
  [Algebra (ZMod 2) k] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) k B]
/-- Actual constant-rank trace subfamilies yield decoding lists with the exact translation factor and scalar quotient loss. -/
theorem dense_list_of_rank_subfamily
    (ell : ℕ) (hell : 1≤ell) (hq : Fintype.card k=2^ell)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (T : Finset (QuadraticForm k B))
    (hT : T ⊆ traceQuadraticFamily n t ht htn hcard)
    (hRank : ∀ Q∈T,Module.finrank k B-Module.finrank k Q.radical=2*t)
    (W : Submodule (ZMod 2) B) (v : B) (codim d gain : ℕ)
    (hcodim : Module.finrank (ZMod 2) B≤Module.finrank (ZMod 2) W+codim)
    (hdim : Module.finrank (ZMod 2) W=d) (hbinaryRank : 2*gain+2*codim≤ell*(2*t)) :
    let S:=affineDomain (additiveDomain W.toAddSubgroup) v
    let Z:ℝ:=(Nat.card W:ℝ)/(Fintype.card k:ℝ)-
      ((Fintype.card k-1:ℕ):ℝ)*(2^(d-gain):ℕ)/(Fintype.card k:ℝ)
    ∃ (w : ↥S → B) (E : Finset B[X]),
      (T.card : ℚ)*(Fintype.card k : ℚ)^(2*t)/(Fintype.card k-1)≤E.card ∧
      ∀ f∈E,f.degree<(Fintype.card k)^(2*n-2) ∧
        Z≤(agreementCount S w f:ℝ) := by
  dsimp only
  let S:=affineDomain (additiveDomain W.toAddSubgroup) v
  let Z:ℝ:=(Nat.card W:ℝ)/(Fintype.card k:ℝ)-
    ((Fintype.card k-1:ℕ):ℝ)*(2^(d-gain):ℕ)/(Fintype.card k:ℝ)
  let I := Set.range (fun z : T × B => fun x => z.1.val (x-z.2))
  let : Fintype I := Fintype.ofFinite _
  let L := subspacePolynomial (⊤ : Submodule k B).toAddSubgroup
  let R := primePowerQuarterNumerator 2 ell L 0
  let K := (Fintype.card k)^(2*n-2)
  have hrep : ∀ f : I,∃ G : B[X], (∀ x,G.eval x=algebraMap k B (f.val x)) ∧ G≠0 ∧
      ∃ A P U : B[X],G=A*P ∧ A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
        P=R+U ∧ U.degree<K ∧ Z≤(agreementCount S (fun x => R.eval x.val) (-U):ℝ) := by
    intro f
    obtain ⟨⟨Q,z⟩,hf⟩ := f.property
    have hQcode := (mem_traceQuadraticCode_iff n t ht htn hcard Q.val).mpr (hT Q.property)
    obtain ⟨u,hu⟩ := hQcode
    have hQne : Q.val≠0 := by
      intro hz
      have hh := hRank Q.val Q.property
      rw [hz] at hh
      have hzrad : (0 : QuadraticForm k B).radical=⊤ := by
        ext x
        simp [QuadraticMap.radical,QuadraticMap.polarBilin,QuadraticMap.polar,LinearMap.ext_iff]
      rw [hzrad,finrank_top, Nat.sub_self] at hh
      omega
    have hpar : u.1≠0 ∨ u.2.val≠0 := by
      by_contra hh
      push Not at hh
      have he : u=0 := Prod.ext hh.1 (Subtype.ext hh.2)
      apply hQne
      rw [←hu,he,map_zero]
    let a := u.1
    let c := u.2.val
    have hc : c^((Fintype.card k)^n)=c := (mem_halfCoefficientSpace n c).mp u.2.property
    have hform : traceFamilyQuadraticForm n t ht htn a c hcard hc=Q.val := hu
    have hrank : Module.finrank k B-
        Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t := by
      rw [hform]
      exact hRank Q.val Q.property
    let G := translatedTracePolynomial (k:=k) n t a c z
    refine ⟨G,?_,?_,?_⟩
    · intro x
      rw [show f.val x=Q.val (x-z) from (congrFun hf x).symm]
      exact (translatedTracePolynomial_eval n t a c z x).trans
        ((algebraMap_traceFamilyQuadraticForm n t ht htn a c hcard hc (x-z)).symm.trans
          (congrArg (algebraMap k B) (congrArg (fun Q : QuadraticForm k B => Q (x-z)) hform)))
    · intro hz
      have hh := translatedTracePolynomial_derivative_ne_zero (k:=k) n t ht htn a c z hpar
      apply hh
      change G.derivative=0
      rw [hz,derivative_zero]
    · obtain ⟨A,P,U,hA,hG,hconv,hU,hdU,hdA,hroots,hagr⟩ :=
        translatedTracePolynomial_exists_locator_of_exact_rank 2 ell hell hq n t ht htn a c z 0
          hcard hc hpar hrank
      refine ⟨A,P,U,hG,hconv,hU,hdU,?_⟩
      have heq : agreementCount S (fun x => R.eval x.val) (-U)=
          (S.filter (fun x => G.eval x=0)).card := by
        rw [agreementCount_eq_card_filter S (fun x:B=>R.eval x) (-U)]
        congr 1
        ext x
        simp only [Finset.mem_filter,eval_neg]
        have hz := QuadraticLocatorConversion.converted_isRoot_iff G A P L
          (Fintype.card k) Fintype.one_lt_card hG hconv x
        change P.eval x=0 ↔ G.eval x=0 at hz
        rw [←hz]
        have hp : P=R+U:=hU
        rw [hp,eval_add]
        constructor
        · rintro ⟨hx,hh⟩
          exact ⟨hx,by linear_combination -hh⟩
        · rintro ⟨hx,hh⟩
          exact ⟨hx,by linear_combination -hh⟩
      rw [heq,DenseConstruction.affineSubmodule_filter_card W v]
      exact DenseConstruction.trace_polynomial_affine_zero_lower ell n t hq ht htn a c z v
        hcard hc hpar W codim d gain hcodim hdim hbinaryRank
  choose G heval hne hfactor using hrep
  have hGinj : Function.Injective G := by
    intro f g hfg
    apply Subtype.ext
    funext x
    apply (algebraMap k B).injective
    rw [←heval f x,←heval g x,hfg]
  obtain ⟨E,hcardE,hE⟩ := QuadraticLocatorConversion.exists_explanation_family_of_conversion_lower
    G L R S (Fintype.card k) K Z Fintype.one_lt_card hGinj hne hfactor
  have hI : Fintype.card I=T.card*(Fintype.card k)^(2*t) := by
    rw [←Nat.card_eq_fintype_card]
    exact traceQuadraticFamily_translated_natCard n t ht htn hcard T hT (2*t) hRank
  refine ⟨fun x => R.eval x.val,E,?_,hE⟩
  simpa only [hI,Nat.cast_mul,Nat.cast_pow] using hcardE
/-- The proved actual trace population yields a uniform seed list on every prescribed affine binary submodule. -/
theorem dense_trace_seed_list
    (ell : ℕ) (hell : 1≤ell) (hq : Fintype.card k=2^ell)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (W : Submodule (ZMod 2) B) (v : B) (codim d gain : ℕ)
    (hcodim : Module.finrank (ZMod 2) B≤Module.finrank (ZMod 2) W+codim)
    (hdim : Module.finrank (ZMod 2) W=d) (hbinaryRank : 2*gain+2*codim≤ell*(2*t)) :
    let S:=affineDomain (additiveDomain W.toAddSubgroup) v
    let Z:ℝ:=(Nat.card W:ℝ)/(Fintype.card k:ℝ)-
      ((Fintype.card k-1:ℕ):ℝ)*(2^(d-gain):ℕ)/(Fintype.card k:ℝ)
    ∃ (w : ↥S → B) (E : Finset B[X]),
      (Fintype.card k : ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) n t/(Fintype.card k-1)≤E.card ∧
      ∀ f∈E,f.degree<(Fintype.card k)^(2*n-2) ∧
        Z≤(agreementCount S w f:ℝ) := by
  let T:=traceRankFamily n t ht htn hcard (2*t)
  have hT : T⊆traceQuadraticFamily n t ht htn hcard := by
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).1
  have hRank : ∀Q∈T,Module.finrank k B-Module.finrank k Q.radical=2*t := by
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).2
  obtain ⟨w,E,hE,hprop⟩ := dense_list_of_rank_subfamily ell hell hq n t ht htn hcard T hT hRank
    W v codim d gain hcodim hdim hbinaryRank
  refine ⟨w,E,?_,hprop⟩
  have hpop:=traceRankFamily_card_lower 2 ell hq n t ht htn hcard
  have hqp : 1≤(Fintype.card k)^t := Nat.one_le_pow _ _ Fintype.card_pos
  have hp : (((Fintype.card k:ℚ)^t-1)*(gaussianPascal ((Fintype.card k)^2) n t:ℚ))≤(T.card:ℚ) := by
    exact_mod_cast hpop
  have hqden : (0:ℚ)<Fintype.card k-1 := by
    have hh : (1:ℚ)<Fintype.card k := by exact_mod_cast (Fintype.one_lt_card (α:=k))
    linarith
  apply le_trans _ hE
  rw [quadraticGaussian_eq_gaussianPascal _ _ _ (Nat.one_lt_pow (by omega) Fintype.one_lt_card) htn]
  apply (div_le_div_iff_of_pos_right hqden).mpr
  linarith [mul_le_mul_of_nonneg_right hp (by positivity : (0:ℚ)≤(Fintype.card k:ℚ)^(2*t))]
end BinaryFieldCounterexamples.QuadraticFormTrace
