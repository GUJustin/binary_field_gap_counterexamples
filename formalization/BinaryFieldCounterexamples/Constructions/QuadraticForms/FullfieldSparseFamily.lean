/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceFactorProperties
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceListFamily
public import BinaryFieldCounterexamples.Polynomial.ConversionFamilyProperties
/-!
# Full-field locator families keeping sparse factors

Counting the actual translated trace polynomials preserves the conversion
factors, their sparse support and exact root counts. These witnesses provide
the collision estimates needed after extending the field.
-/
@[expose] public section
set_option warn.classDefReducibility false
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Actual constant-rank trace subfamilies yield sparse locator families with the exact translation factor and scalar quotient loss. -/
theorem fullfield_sparse_locator_family_of_rank_subfamily
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (T : Finset (QuadraticForm k B))
    (hT : T ⊆ traceQuadraticFamily n t ht htn hcard)
    (hRank : ∀ Q∈T,Module.finrank k B-Module.finrank k Q.radical=2*t) :
    let L := subspacePolynomial (⊤ : Submodule k B).toAddSubgroup
    let R := primePowerQuarterNumerator p r L 0
    ∃ E : Finset B[X],
      (T.card : ℚ)*(Fintype.card k : ℚ)^(2*t)/(Fintype.card k-1)≤E.card ∧
      ∀ P∈E, ∃ A : B[X], A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
        A≠0 ∧ A.natDegree=(Fintype.card k)^(2*n-t-1) ∧
        (∀ e∈A.support,(Fintype.card k)^(t-1)∣e) ∧
        (Finset.univ.filter (fun x : B => A.eval x=0)).card=(Fintype.card k)^(2*n-2*t) ∧
        (P-R).degree<(Fintype.card k)^(2*n-2) ∧
        (Finset.univ.filter (fun x : B => P.eval x=0)).card=
          (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
  let I := Set.range (fun z : T × B => fun x => z.1.val (x-z.2))
  let : Fintype I := Fintype.ofFinite _
  let L := subspacePolynomial (⊤ : Submodule k B).toAddSubgroup
  let R := primePowerQuarterNumerator p r L 0
  let K := (Fintype.card k)^(2*n-2)
  let Z := (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1)
  have hrep : ∀ f : I,∃ G : B[X], (∀ x,G.eval x=algebraMap k B (f.val x)) ∧ G≠0 ∧
      ∃ A P : B[X],G=A*P ∧ A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
        A≠0 ∧ A.natDegree=(Fintype.card k)^(2*n-t-1) ∧
        (∀ e∈A.support,(Fintype.card k)^(t-1)∣e) ∧
        (Finset.univ.filter (fun x : B => A.eval x=0)).card=(Fintype.card k)^(2*n-2*t) ∧
        (P-R).degree<K ∧ (Finset.univ.filter (fun x : B => P.eval x=0)).card=Z := by
    intro f
    obtain ⟨⟨Q,v⟩,hf⟩ := f.property
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
    let G := translatedTracePolynomial (k:=k) n t a c v
    refine ⟨G,?_,?_,?_⟩
    · intro x
      rw [show f.val x=Q.val (x-v) from (congrFun hf x).symm]
      exact (translatedTracePolynomial_eval n t a c v x).trans
        ((algebraMap_traceFamilyQuadraticForm n t ht htn a c hcard hc (x-v)).symm.trans
          (congrArg (algebraMap k B) (congrArg (fun Q : QuadraticForm k B => Q (x-v)) hform)))
    · intro hz
      have hh := translatedTracePolynomial_derivative_ne_zero (k:=k) n t ht htn a c v hpar
      apply hh
      change G.derivative=0
      rw [hz,derivative_zero]
    · obtain ⟨A,P,U,hA,hG,hconv,hU,hdU,hdA,hroots,hagr⟩ :=
        translatedTracePolynomial_exists_locator_of_exact_rank p r hr hq n t ht htn a c v 0
          hcard hc hpar hrank
      have hlam : L.coeff 1≠0 := subspacePolynomial_coeff_one_ne_zero _
      have hJ : G.derivative = -C (L.coeff 1)*A^(Fintype.card k) :=
        factor_derivative_of_conversion (Fintype.card k) (by have := Fintype.one_lt_card (α := k); omega)
          G A P L G.derivative (L.coeff 1) hlam (subspacePolynomial_monic _).ne_zero hG hconv
          (translatedTracePolynomial_differential p r hr hq n t ht htn a c v hcard hc)
      obtain ⟨hsupp,hAz⟩ := translatedTracePolynomial_factor_properties p r hq n t ht htn a c v
        hcard hc hpar hrank A (L.coeff 1) hlam hJ
      refine ⟨A,P,hG,hconv,hA,hdA,hsupp,hAz,?_,hroots⟩
      rw [hU, add_sub_cancel_left]
      exact hdU
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
    exact traceQuadraticFamily_translated_natCard n t ht htn hcard T hT (2*t) hRank
  refine ⟨E,?_,hE⟩
  simpa only [hI,Nat.cast_mul,Nat.cast_pow] using hcardE
end BinaryFieldCounterexamples.QuadraticFormTrace
