/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.DomainSource
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.NumeratorTransport
public import BinaryFieldCounterexamples.Polynomial.Map
public import BinaryFieldCounterexamples.Agreement.Domains

/-!
# Canonical quarter-rate first input after a field embedding

The mapped scalar-submodule locator keeps its q-power support and exact
cardinality. The prime-power first-input bound therefore applies directly in the
containing field, without choosing a new evaluation domain.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The canonical pole-dependent numerator has the paper's exact first-input
bound on a mapped scalar-submodule domain. -/
theorem agreementLE_mappedSubmoduleQuarterSource
    {k B F : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    [Field F] [Fintype F]
    (φ : B→+*F) (p r : ℕ) [Fact p.Prime] [CharP B p] [CharP F p]
    (hr : 1≤r) (hqk : Fintype.card k=p^r)
    (D : Submodule k B) (d : ℕ) (hd : 3≤d)
    (hDcard : (Finset.univ.filter fun x : B => x∈D).card=(Fintype.card k)^d)
    (β : F) (hβ : β∉mappedDomain φ (Finset.univ.filter fun x : B => x∈D)) :
    agreementLE (mappedDomain φ (Finset.univ.filter fun x : B => x∈D))
      ((Fintype.card k)^(d-2))
      (fun x => (primePowerQuarterNumerator p r
        ((subspacePolynomial D.toAddSubgroup).map φ) β).eval (x:F)*((x:F)-β)⁻¹)
      ⌊((Fintype.card k+1:ℚ)*
        (mappedDomain φ (Finset.univ.filter fun x : B => x∈D)).card/
        (2*(Fintype.card k)^2)-1)⌋₊ := by
  let S₀ := Finset.univ.filter fun x : B => x∈D
  let S := mappedDomain φ S₀
  let b := Fintype.card k
  let K := b^(d-2)
  let L := subspacePolynomial D.toAddSubgroup
  have hb : b=p^r := hqk
  have hb2 : 2≤b := Fintype.one_lt_card
  have hK2 : 2≤K := hb2.trans (Nat.le_self_pow (by omega) b)
  have hpzero : (p:F)=0 := CharP.cast_eq_zero F p
  have hKchar : (K:F)=0 := by
    dsimp only [K,b]
    rw [hqk,Nat.cast_pow,Nat.cast_pow,hpzero,zero_pow (by omega),zero_pow (by omega)]
  have hLmap : L.map φ=
      subspacePolynomial (D.toAddSubgroup.map φ.toAddMonoidHom) :=
    map_subspacePolynomial φ D.toAddSubgroup
  have hcoeff : (L.map φ).coeff 1≠0 := by
    rw [hLmap]
    exact subspacePolynomial_coeff_one_ne_zero _
  have hroots : ∀x∈S,(L.map φ).eval x=0 := by
    intro x hx
    rw [hLmap]
    apply (subspacePolynomial_eval_eq_zero_iff _ x).mpr
    rw [←mem_additiveDomain,←mappedDomain_additiveDomain]
    exact hx
  have hLβ : (L.map φ).eval β≠0 := by
    intro hz
    apply hβ
    change β∈mappedDomain φ (additiveDomain D.toAddSubgroup)
    rw [mappedDomain_additiveDomain]
    apply (mem_additiveDomain _ β).mpr
    apply (subspacePolynomial_eval_eq_zero_iff _ β).mp
    rw [←hLmap]
    exact hz
  have hs : ∀z∈(L.map φ).support,∃u : ℕ,z=(p^r)^u := by
    intro z hz
    have hzbase : z∈L.support := by
      rw [mem_support_iff] at hz ⊢
      exact fun hh => hz (by simp only [coeff_map,hh,map_zero])
    obtain ⟨u,hu⟩ := FiniteFieldLocator.subspacePolynomial_q_support D z hzbase
    exact ⟨u,by simpa only [hqk] using hu⟩
  have hLdeg : (L.map φ).natDegree≤(p^r)^2*K := by
    rw [natDegree_map,subspacePolynomial_natDegree]
    dsimp only [K]
    change Fintype.card D≤(p^r)^2*b^(d-2)
    have hcardD : Fintype.card D=b^d := by
      rw [Fintype.card_subtype]
      exact hDcard
    rw [hcardD,←hb,←pow_add]
    exact le_of_eq (by congr 1; omega)
  have hsource := agreementLE_primePowerQuarterNumerator p r hr S β hβ K hK2 hKchar
    (L.map φ) hcoeff hroots hLβ hs hLdeg
  have hS : S.card=b^d := by
    change (mappedDomain φ S₀).card=b^d
    rw [card_mappedDomain,hDcard]
  have hfactor : S.card=b^2*K := by
    rw [hS]
    dsimp only [K]
    rw [←pow_add]
    congr 1
    omega
  have hfloor := primePowerQuarterSource_floor b K S.card hb2 hK2 hfactor
  simpa only [S,S₀,K,L,b,hfloor,←hb] using hsource

end BinaryFieldCounterexamples
