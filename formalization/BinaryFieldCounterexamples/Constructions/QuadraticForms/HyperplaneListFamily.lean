/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceHyperplaneLocators
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceTranslationCount
public import BinaryFieldCounterexamples.Polynomial.QuadraticConversionCount
/-!
# Decoding lists on prescribed hyperplanes

Count the actual translated functions whose quadratic radicals contain the
hyperplane kernel vector. Literal polynomial descent preserves their
injectivity. The conversion fiber bound then yields distinct strict-degree
explaining polynomials, with exact agreement on the prescribed hyperplane and the
original translation factor divided by the scalar multiplicity.
-/
@[expose] public section
set_option warn.classDefReducibility false
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Actual constant-rank trace subfamilies yield decoding lists with the exact translation factor and scalar quotient loss. -/
theorem hyperplane_list_of_rank_subfamily
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t<n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (T : Finset (QuadraticForm k B))
    (hT : T ⊆ traceQuadraticFamily n t ht (by omega) hcard)
    (hRank : ∀ Q∈T,Module.finrank k B-Module.finrank k Q.radical=2*t)
    (v : B) (hv : v≠0) (hRad : ∀ Q∈T,v∈Q.radical)
    (D : Submodule k B) (hD : Module.finrank k D+1=Module.finrank k B)
    (hrange : LinearMap.range (hyperplaneMap (k:=k) v)=D) :
    let Df := Finset.univ.filter (fun x : B => x∈D)
    ∃ (w : ↥Df → B) (E : Finset B[X]),
      (T.card : ℚ)*(Fintype.card k : ℚ)^(2*t)/(Fintype.card k-1)≤E.card ∧
      ∀ f∈E,f.degree<(Fintype.card k)^(2*n-3) ∧
        agreementCount Df w f=
          (Fintype.card k)^(2*n-2)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-2) := by
  dsimp only
  let Df := Finset.univ.filter (fun x : B => x∈D)
  let I := Set.range (fun z : T × B => fun x => z.1.val (x-z.2))
  let : Fintype I := Fintype.ofFinite _
  let L := subspacePolynomial D.toAddSubgroup
  let R := primePowerQuarterNumerator p r L 0
  let K := (Fintype.card k)^(2*n-3)
  let Z := (Fintype.card k)^(2*n-2)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-2)
  have hrep : ∀ f : I,∃ G : B[X], (∀ x,G.eval (hyperplaneMap (k:=k) v x)=algebraMap k B (f.val x)) ∧ G≠0 ∧
      ∃ A P U : B[X],G=A*P ∧ A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
        P=R+U ∧ U.degree<K ∧ agreementCount Df (fun x => R.eval x.val) (-U)=Z := by
    intro f
    obtain ⟨⟨Q,z⟩,hf⟩ := f.property
    have hQcode := (mem_traceQuadraticCode_iff n t ht (by omega) hcard Q.val).mpr (hT Q.property)
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
    have hform : traceFamilyQuadraticForm n t ht (by omega) a c hcard hc=Q.val := hu
    have hrank : Module.finrank k B-
        Module.finrank k (traceFamilyQuadraticForm n t ht (by omega) a c hcard hc).radical=2*t := by
      rw [hform]
      exact hRank Q.val Q.property
    have hvrad : v∈(traceFamilyQuadraticForm n t ht (by omega) a c hcard hc).radical := by
      rw [hform]
      exact hRad Q.val Q.property
    obtain ⟨H,hHdegree,he,hd⟩ := translatedTracePolynomial_hyperplane_descent n t ht
      (by omega) a c z v hcard hc hv hvrad D hD hrange
    refine ⟨H,?_,?_,?_⟩
    · intro x
      rw [show f.val x=Q.val (x-z) from (congrFun hf x).symm]
      rw [←hyperplanePolynomial_eval v x hv, ←Polynomial.eval_comp, he]
      exact (translatedTracePolynomial_eval n t a c z x).trans
        ((algebraMap_traceFamilyQuadraticForm n t ht (by omega) a c hcard hc (x-z)).symm.trans
          (congrArg (algebraMap k B) (congrArg (fun Q : QuadraticForm k B => Q (x-z)) hform)))
    · intro hz
      have hh := translatedTracePolynomial_derivative_ne_zero (k:=k) n t ht (by omega) a c z hpar
      apply hh
      have hGzero : translatedTracePolynomial (k:=k) n t a c z=0 := by
        rw [←he,hz,Polynomial.zero_comp]
      rw [hGzero,derivative_zero]
    · obtain ⟨A,P,U,hA,hG,hconv,hU,hdU,hdA,hagr⟩ :=
        descendedTracePolynomial_exists_locator_exact_agreement p r hr hq n t ht htn a c z v 0 hv
          hcard hc hpar hrank D hD hrange H he hd
      exact ⟨A,P,U,hG,hconv,hU,hdU,hagr⟩
  choose G heval hne hfactor using hrep
  have hGinj : Function.Injective G := by
    intro f g hfg
    apply Subtype.ext
    funext x
    apply (algebraMap k B).injective
    rw [←heval f x,←heval g x,hfg]
  obtain ⟨E,hcardE,hE⟩ := QuadraticLocatorConversion.exists_explanation_family_of_conversion
    G L R Df (Fintype.card k) K Z Fintype.one_lt_card hGinj hne hfactor
  have hI : Fintype.card I=T.card*(Fintype.card k)^(2*t) := by
    rw [←Nat.card_eq_fintype_card]
    exact traceQuadraticFamily_translated_natCard n t ht (by omega) hcard T hT (2*t) hRank
  refine ⟨fun x => R.eval x.val,E,?_,hE⟩
  simpa only [hI,Nat.cast_mul,Nat.cast_pow] using hcardE
end BinaryFieldCounterexamples.QuadraticFormTrace
