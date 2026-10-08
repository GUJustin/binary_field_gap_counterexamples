/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.FullfieldList
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TracePopulation
/-!
# Unconditional full-field decoding lists

The actual minimum-rank population supplies the final input to polynomial list
assembly. The prescribed full-cardinality scalar submodule is kept literally,
as are the strict degree bound, exact agreement, and rational list lower bound.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
/-- The full-field list assembly uses the original prescribed submodule domain when its cardinality is full. -/
theorem fullfield_submodule_list
    (n t : ℕ) (ht : 2≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (D : Submodule k B) (hD : (Finset.univ.filter (fun x : B => x∈D)).card=Fintype.card B)
 :
    let S := Finset.univ.filter (fun x : B => x∈D)
    ∃ (w : S → B) (E : Finset B[X]),
      (Fintype.card k:ℚ)^(2*t)*((Fintype.card k:ℚ)^t-1)*
        quadraticGaussian ((Fintype.card k)^2) n t/(Fintype.card k-1)≤E.card ∧
      ∀ f∈E,f.degree<S.card/(Fintype.card k)^2 ∧
        agreementCount S w f=S.card/Fintype.card k-
          (Fintype.card k-1)*S.card/(Fintype.card k)^(t+1) := by
  obtain ⟨p,hchar,r,hprime,hq⟩ := FiniteField.card' k
  let : CharP k p := hchar
  let : CharP B p := charP_of_injective_algebraMap' k p
  let : Fact p.Prime := ⟨hprime⟩
  have hpop := traceRankFamily_card_lower p r hq n t (by omega) htn hcard
  have hS : Finset.univ.filter (fun x : B => x∈D)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ,hD] using (le_refl (Fintype.card B))
  dsimp only
  rw [hS,Finset.card_univ]
  exact fullfield_list_of_population n t ht htn hcard hpop
end BinaryFieldCounterexamples.QuadraticFormTrace
