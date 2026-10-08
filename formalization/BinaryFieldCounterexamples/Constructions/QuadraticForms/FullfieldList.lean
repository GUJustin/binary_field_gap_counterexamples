/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceListFamily
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceRadicalIncidence
public import BinaryFieldCounterexamples.Counting.GaussianIdentities
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
/-- The full-field decoding list follows from the actual minimum-rank population, keeping the scalar quotient and exact agreement count. -/
theorem fullfield_list_of_minimum_population
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 2≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (hpop : ((Fintype.card k)^t-1)*gaussianPascal ((Fintype.card k)^2) n t≤
      (traceRankFamily n t (by omega) htn hcard (2*t)).card) :
    ∃ (w : ↥(Finset.univ : Finset B) → B) (E : Finset B[X]),
      (Fintype.card k:ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) n t/(Fintype.card k-1)≤E.card ∧
      ∀ f∈E,f.degree<Fintype.card B/(Fintype.card k)^2 ∧
        agreementCount Finset.univ w f=
          Fintype.card B/Fintype.card k-(Fintype.card k-1)*Fintype.card B/(Fintype.card k)^(t+1) := by
  let T := traceRankFamily n t (by omega : 1≤t) htn hcard (2*t)
  have hT : T⊆traceQuadraticFamily n t (by omega) htn hcard := by
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).1
  have hRank : ∀ Q∈T,Module.finrank k B-Module.finrank k Q.radical=2*t := by
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).2
  obtain ⟨w,E,hE,hprop⟩ := fullfield_list_of_rank_subfamily p r hr hq n t (by omega) htn hcard T hT hRank
  refine ⟨w,E,?_,?_⟩
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
  · have hqpos : 0<Fintype.card k := Fintype.card_pos
    have hK : Fintype.card B/(Fintype.card k)^2=(Fintype.card k)^(2*n-2) := by
      rw [hcard,Nat.pow_div (by omega) hqpos]
    have hN : Fintype.card B/Fintype.card k=(Fintype.card k)^(2*n-1) := by
      rw [hcard]
      have hp : (Fintype.card k)^(2*n)/(Fintype.card k)^1=(Fintype.card k)^(2*n-1) := Nat.pow_div (by omega) hqpos
      simpa only [pow_one] using hp
    have hT : (Fintype.card k-1)*Fintype.card B/(Fintype.card k)^(t+1)=
        (Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
      rw [hcard,Nat.mul_div_assoc _ (pow_dvd_pow _ (by omega : t+1≤2*n)),Nat.pow_div (by omega) hqpos]
      congr 2
    intro f hf
    simpa only [hK,hN,hT,Nat.cast_pow] using hprop f hf
/-- The finite scalar field supplies its committed prime-power and characteristic data automatically. -/
theorem fullfield_list_of_population
    (n t : ℕ) (ht : 2≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (hpop : ((Fintype.card k)^t-1)*gaussianPascal ((Fintype.card k)^2) n t≤
      (traceRankFamily n t (by omega) htn hcard (2*t)).card) :
    ∃ (w : ↥(Finset.univ : Finset B) → B) (E : Finset B[X]),
      (Fintype.card k:ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) n t/(Fintype.card k-1)≤E.card ∧
      ∀ f∈E,f.degree<Fintype.card B/(Fintype.card k)^2 ∧
        agreementCount Finset.univ w f=
          Fintype.card B/Fintype.card k-(Fintype.card k-1)*Fintype.card B/(Fintype.card k)^(t+1) := by
  obtain ⟨p,hchar,r,hprime,hq⟩ := FiniteField.card' k
  let : CharP k p := hchar
  let : CharP B p := charP_of_injective_algebraMap' k p
  let : Fact p.Prime := ⟨hprime⟩
  exact fullfield_list_of_minimum_population p r r.property hq n t ht htn hcard hpop
/-- The full-field list assembly uses the original prescribed submodule domain when its cardinality is full. -/
theorem fullfield_submodule_list_of_population
    (n t : ℕ) (ht : 2≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (D : Submodule k B) (hD : (Finset.univ.filter (fun x : B => x∈D)).card=Fintype.card B)
    (hpop : ((Fintype.card k)^t-1)*gaussianPascal ((Fintype.card k)^2) n t≤
      (traceRankFamily n t (by omega) htn hcard (2*t)).card) :
    let S := Finset.univ.filter (fun x : B => x∈D)
    ∃ (w : S → B) (E : Finset B[X]),
      (Fintype.card k:ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) n t/(Fintype.card k-1)≤E.card ∧
      ∀ f∈E,f.degree<S.card/(Fintype.card k)^2 ∧
        agreementCount S w f=S.card/Fintype.card k-
          (Fintype.card k-1)*S.card/(Fintype.card k)^(t+1) := by
  have hS : Finset.univ.filter (fun x : B => x∈D)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ,hD] using (le_refl (Fintype.card B))
  dsimp only
  rw [hS,Finset.card_univ]
  exact fullfield_list_of_population n t ht htn hcard hpop
end BinaryFieldCounterexamples.QuadraticFormTrace
