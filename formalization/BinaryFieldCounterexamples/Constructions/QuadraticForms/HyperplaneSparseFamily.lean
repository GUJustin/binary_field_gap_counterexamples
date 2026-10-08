/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceFactorProperties
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperplaneListFamily
public import BinaryFieldCounterexamples.Polynomial.ConversionFamilyProperties
/-!
# Hyperplane locator families retaining sparse factors

Literal descent and conversion preserve the sparse factor witnesses and their
exact domain root counts. Counting actual translated functions gives the
scalar quotient loss required for subsequent collision estimates.
-/
@[expose] public section
set_option warn.classDefReducibility false
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Actual constant-rank trace subfamilies yield hyperplane locator families with sparse factor witnesses. -/
theorem hyperplane_sparse_locator_family_of_rank_subfamily
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
    let L := subspacePolynomial D.toAddSubgroup
    let R := primePowerQuarterNumerator p r L 0
    ∃ E : Finset B[X],
      (T.card : ℚ)*(Fintype.card k : ℚ)^(2*t)/(Fintype.card k-1)≤E.card ∧
      ∀ P∈E, ∃ A : B[X], A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
        A≠0 ∧ A.natDegree=(Fintype.card k)^(2*n-t-2) ∧
        (∀ e∈A.support,(Fintype.card k)^(t-1)∣e) ∧
        (Df.filter (fun x => A.eval x=0)).card=(Fintype.card k)^(2*n-2*t-1) ∧
        (P-R).degree<(Fintype.card k)^(2*n-3) ∧
        (Df.filter (fun x => P.eval x=0)).card=
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
      ∃ A P : B[X],G=A*P ∧ A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
        A≠0 ∧ A.natDegree=(Fintype.card k)^(2*n-t-2) ∧
        (∀ e∈A.support,(Fintype.card k)^(t-1)∣e) ∧
        (Df.filter (fun x => A.eval x=0)).card=(Fintype.card k)^(2*n-2*t-1) ∧
        (P-R).degree<K ∧ (Df.filter (fun x => P.eval x=0)).card=Z := by
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
      have hlam : L.coeff 1≠0 := subspacePolynomial_coeff_one_ne_zero _
      have hJ : H.derivative = -C (L.coeff 1)*A^(Fintype.card k) :=
        factor_derivative_of_conversion (Fintype.card k) (by have := Fintype.one_lt_card (α := k); omega)
          H A P L H.derivative (L.coeff 1) hlam (subspacePolynomial_monic _).ne_zero hG hconv
          (descendedTracePolynomial_differential p r hr hq n t ht (by omega) a c z v hv hcard hc D hD hrange H he)
      obtain ⟨hsupp,hAz⟩ := descendedTracePolynomial_factor_properties p r hq n t ht htn a c z v hv
        hcard hc hpar hrank D hrange H A (L.coeff 1) hlam hd hJ
      refine ⟨A,P,hG,hconv,hA,hdA,hsupp,hAz,?_,?_⟩
      · rw [hU, add_sub_cancel_left]
        exact hdU
      · rw [agreementCount_eq_card_filter Df (fun x : B => R.eval x) (-U)] at hagr
        convert hagr using 1
        congr 1
        ext x
        simp only [Finset.mem_filter, hU, Polynomial.eval_add, Polynomial.eval_neg]
        change (x∈Df ∧ R.eval x+U.eval x=0) ↔ (x∈Df ∧ -U.eval x=R.eval x)
        constructor <;> rintro ⟨hx,heq⟩ <;> refine ⟨hx,?_⟩ <;> linear_combination -heq
  choose G heval hne hfactor using hrep
  have hGinj : Function.Injective G := by
    intro f g hfg
    apply Subtype.ext
    funext x
    apply (algebraMap k B).injective
    rw [←heval f x,←heval g x,hfg]
  obtain ⟨E,hcardE,hE⟩ := QuadraticLocatorConversion.exists_locator_family_with_properties
    G L (Fintype.card k) Fintype.one_lt_card _ hGinj hne hfactor
  have hI : Fintype.card I=T.card*(Fintype.card k)^(2*t) := by
    rw [←Nat.card_eq_fintype_card]
    exact traceQuadraticFamily_translated_natCard n t ht (by omega) hcard T hT (2*t) hRank
  refine ⟨E,?_,hE⟩
  simpa only [hI,Nat.cast_mul,Nat.cast_pow] using hcardE
end BinaryFieldCounterexamples.QuadraticFormTrace
