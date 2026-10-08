/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.FullfieldSparseFamily
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperplaneSparseFamily
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TracePopulation
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceHyperplaneCount
public import BinaryFieldCounterexamples.Counting.GaussianIdentities
/-!
# Unconditional sparse locator populations

The actual minimum-rank trace population, and its hyperplane radical incidence
count, yield the original Gaussian lower bounds while keeping every sparse
factor witness needed for collision averaging.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
/-- The full-field population keeps sparse conversion factors and exact root counts. -/
theorem fullfield_sparse_locator_family
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 2≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
 :
    let L := subspacePolynomial (⊤ : Submodule k B).toAddSubgroup
    let R := primePowerQuarterNumerator p r L 0
    ∃ E : Finset B[X],
      (Fintype.card k:ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) n t/(Fintype.card k-1)≤E.card ∧
      ∀ P∈E, ∃ A : B[X], A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
        A≠0 ∧ A.natDegree=(Fintype.card k)^(2*n-t-1) ∧
        (∀ e∈A.support,(Fintype.card k)^(t-1)∣e) ∧
        (Finset.univ.filter (fun x : B => A.eval x=0)).card=(Fintype.card k)^(2*n-2*t) ∧
        (P-R).degree<(Fintype.card k)^(2*n-2) ∧
        (Finset.univ.filter (fun x : B => P.eval x=0)).card=
          (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
  have hpop := traceRankFamily_card_lower p r hq n t (by omega) (by omega) hcard
  let T := traceRankFamily n t (by omega : 1≤t) htn hcard (2*t)
  have hT : T⊆traceQuadraticFamily n t (by omega) htn hcard := by
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).1
  have hRank : ∀ Q∈T,Module.finrank k B-Module.finrank k Q.radical=2*t := by
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).2
  obtain ⟨E,hE,hprop⟩ := fullfield_sparse_locator_family_of_rank_subfamily p r hr hq n t (by omega) htn hcard T hT hRank
  refine ⟨E,?_,hprop⟩
  · have hqp : 1≤(Fintype.card k)^t := Nat.one_le_pow _ _ Fintype.card_pos
    have hp : (((Fintype.card k:ℚ)^t-1)*(gaussianPascal ((Fintype.card k)^2) n t:ℚ))≤(T.card:ℚ) := by
      exact_mod_cast hpop
    have hqden : (0:ℚ)<Fintype.card k-1 := by
      have hh : (1:ℚ)<Fintype.card k := by exact_mod_cast (Fintype.one_lt_card (α:=k))
      linarith
    apply le_trans _ hE
    rw [quadraticGaussian_eq_gaussianPascal _ _ _ (Nat.one_lt_pow (by omega) Fintype.one_lt_card) htn]
    apply (div_le_div_iff_of_pos_right hqden).mpr
    linarith [mul_le_mul_of_nonneg_right hp (by positivity : (0:ℚ)≤(Fintype.card k:ℚ)^(2*t))]

/-- The prescribed hyperplane population keeps sparse conversion factors and exact root counts. -/
theorem hyperplane_sparse_locator_family
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 2≤t) (htn : t≤n-1)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (D : Submodule k B)
    (hDcard : (Finset.univ.filter (fun x : B => x∈D)).card=(Fintype.card k)^(2*n-1))
 :
    let L := subspacePolynomial D.toAddSubgroup
    let R := primePowerQuarterNumerator p r L 0
    ∃ E : Finset B[X],
      (Fintype.card k:ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) (n-1) t/(Fintype.card k-1)≤E.card ∧
      ∀ P∈E, ∃ A : B[X], A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
        A≠0 ∧ A.natDegree=(Fintype.card k)^(2*n-t-2) ∧
        (∀ e∈A.support,(Fintype.card k)^(t-1)∣e) ∧
        ((Finset.univ.filter (fun x : B => x∈D)).filter (fun x : B => A.eval x=0)).card=(Fintype.card k)^(2*n-2*t-1) ∧
        (P-R).degree<(Fintype.card k)^(2*n-3) ∧
        ((Finset.univ.filter (fun x : B => x∈D)).filter (fun x : B => P.eval x=0)).card=
          (Fintype.card k)^(2*n-2)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-2) := by
  have hpop := traceRankFamily_card_lower p r hq n t (by omega) (by omega) hcard
  dsimp only
  let S := Finset.univ.filter (fun x : B => x∈D)
  have hDS : Nat.card D=S.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have hd : Module.finrank k D=2*n-1 := by
    apply Nat.pow_right_injective (Fintype.one_lt_card (α:=k))
    change (Fintype.card k)^Module.finrank k D=(Fintype.card k)^(2*n-1)
    rw [←Nat.card_eq_fintype_card,←Module.natCard_eq_pow_finrank (K:=k),hDS]
    simpa only [Nat.card_eq_fintype_card] using hDcard
  have hdimB : Module.finrank k B=2*n := by
    apply Nat.pow_right_injective (Fintype.one_lt_card (α:=k))
    change (Fintype.card k)^Module.finrank k B=(Fintype.card k)^(2*n)
    rw [←Module.card_eq_pow_finrank (K:=k)]
    exact hcard
  have hD : Module.finrank k D+1=Module.finrank k B := by omega
  obtain ⟨v,hv,hrange⟩ := exists_hyperplaneMap_range D hD
  let T := traceHyperplaneRankFamily n t (by omega) (by omega) hcard v
  have hmem (Q) (hQ:Q∈T) :=
    (mem_traceHyperplaneRankFamily n t (by omega) (by omega) hcard v Q).mp hQ
  have hT : T⊆traceQuadraticFamily n t (by omega) (by omega) hcard := by
    intro Q hQ
    exact (hmem Q hQ).1
  have hRank : ∀Q∈T,Module.finrank k B-Module.finrank k Q.radical=2*t := by
    intro Q hQ
    exact (hmem Q hQ).2.1
  have hRad : ∀Q∈T,v∈Q.radical := by
    intro Q hQ
    exact (hmem Q hQ).2.2
  have hpopulation := traceHyperplaneRankFamily_card_lower n t (by omega) (by omega) hcard v hv hpop
  obtain ⟨E,hE,hprop⟩ := hyperplane_sparse_locator_family_of_rank_subfamily p r hr hq n t (by omega)
    (by omega) hcard T hT hRank v hv hRad D hD hrange
  refine ⟨E,?_,hprop⟩
  · have hqp : 1≤(Fintype.card k)^t := Nat.one_le_pow _ _ Fintype.card_pos
    have hp : (((Fintype.card k:ℚ)^t-1)*(gaussianPascal ((Fintype.card k)^2) (n-1) t:ℚ))≤(T.card:ℚ) := by
      exact_mod_cast hpopulation
    have hqden : (0:ℚ)<Fintype.card k-1 := by
      have hh : (1:ℚ)<Fintype.card k := by exact_mod_cast (Fintype.one_lt_card (α:=k))
      linarith
    apply le_trans _ hE
    rw [quadraticGaussian_eq_gaussianPascal _ _ _ (Nat.one_lt_pow (by omega) Fintype.one_lt_card) htn]
    apply (div_le_div_iff_of_pos_right hqden).mpr
    linarith [mul_le_mul_of_nonneg_right hp (by positivity : (0:ℚ)≤(Fintype.card k:ℚ)^(2*t))]
end BinaryFieldCounterexamples.QuadraticFormTrace
