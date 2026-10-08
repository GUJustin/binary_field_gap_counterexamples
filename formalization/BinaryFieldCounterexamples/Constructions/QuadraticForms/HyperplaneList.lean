/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperplaneListFamily
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.FullfieldList
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceHyperplaneCount
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TracePopulation
/-!
# Unconditional decoding lists on prescribed hyperplanes

The actual trace minimum-rank population and radical-incidence count supply the
hyperplane Gaussian correction. A scalar normal chooses the literal descent map
onto the prescribed domain. The resulting list has the exact agreement count,
strict degree, and rational lower bound stated in the finite theorem.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
/-- The hyperplane decoding list follows from the actual minimum-rank population, keeping the scalar quotient and exact agreement count. -/
theorem hyperplane_list_of_minimum_population
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 2≤t) (htn : t≤n-1)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (D : Submodule k B)
    (hDcard : (Finset.univ.filter (fun x : B => x∈D)).card=(Fintype.card k)^(2*n-1))
    (hpop : ((Fintype.card k)^t-1)*gaussianPascal ((Fintype.card k)^2) n t≤
      (traceRankFamily n t (by omega) (by omega) hcard (2*t)).card) :
    let S := Finset.univ.filter (fun x : B => x∈D)
    ∃ (w : ↥S → B) (E : Finset B[X]),
      (Fintype.card k:ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) (n-1) t/(Fintype.card k-1)≤E.card ∧
      ∀ f∈E,f.degree<S.card/(Fintype.card k)^2 ∧
        agreementCount S w f=
          S.card/Fintype.card k-(Fintype.card k-1)*S.card/(Fintype.card k)^(t+1) := by
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
  obtain ⟨w,E,hE,hprop⟩ := hyperplane_list_of_rank_subfamily p r hr hq n t (by omega)
    (by omega) hcard T hT hRank v hv hRad D hD hrange
  refine ⟨w,E,?_,?_⟩
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
  · have hqpos : 0<Fintype.card k := Fintype.card_pos
    have hK : S.card/(Fintype.card k)^2=(Fintype.card k)^(2*n-3) := by
      rw [hDcard,Nat.pow_div (by omega) hqpos]
      congr 1
    have hN : S.card/Fintype.card k=(Fintype.card k)^(2*n-2) := by
      rw [hDcard]
      have hp : (Fintype.card k)^(2*n-1)/(Fintype.card k)^1=(Fintype.card k)^(2*n-2) := Nat.pow_div (by omega) hqpos
      simpa only [pow_one] using hp
    have hT : (Fintype.card k-1)*S.card/(Fintype.card k)^(t+1)=
        (Fintype.card k-1)*(Fintype.card k)^(2*n-t-2) := by
      rw [hDcard,Nat.mul_div_assoc _ (pow_dvd_pow _ (by omega : t+1≤2*n-1)),Nat.pow_div (by omega) hqpos]
      congr 2
      omega
    intro f hf
    change f.degree< S.card/(Fintype.card k)^2 ∧ agreementCount S w f= S.card/Fintype.card k-(Fintype.card k-1)*S.card/(Fintype.card k)^(t+1)
    simpa only [hK,hN,hT,Nat.cast_pow] using hprop f hf
/-- The prescribed hyperplane decoding list follows from the proved actual minimum-rank population, keeping the scalar quotient and exact agreement count. -/
theorem hyperplane_submodule_list
    (n t : ℕ) (ht : 2≤t) (htn : t≤n-1)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (D : Submodule k B)
    (hDcard : (Finset.univ.filter (fun x : B => x∈D)).card=(Fintype.card k)^(2*n-1)) :
    let S := Finset.univ.filter (fun x : B => x∈D)
    ∃ (w : ↥S → B) (E : Finset B[X]),
      (Fintype.card k:ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) (n-1) t/(Fintype.card k-1)≤E.card ∧
      ∀ f∈E,f.degree<S.card/(Fintype.card k)^2 ∧
        agreementCount S w f=
          S.card/Fintype.card k-(Fintype.card k-1)*S.card/(Fintype.card k)^(t+1) := by
  obtain ⟨p,hchar,r,hprime,hq⟩ := FiniteField.card' k
  let : CharP k p := hchar
  let : CharP B p := charP_of_injective_algebraMap' k p
  let : Fact p.Prime := ⟨hprime⟩
  exact hyperplane_list_of_minimum_population p r r.property hq n t ht htn hcard D hDcard
    (traceRankFamily_card_lower p r hq n t (by omega) (by omega) hcard)
end BinaryFieldCounterexamples.QuadraticFormTrace
