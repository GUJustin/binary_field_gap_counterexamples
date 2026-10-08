/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperbolicSplit
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
/-!
# Exact zero counts under actual hyperbolic splitting

The product fiber ab=z has q-1 elements for nonzero z and 2q-1 elements
at zero. Summing these literal fibers gives the hyperbolic zero-count
recurrence, which is then transported through the proven all-characteristic
quadratic isometry. No classification or rank/type formula is assumed.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {k : Type*} [Field k] [Fintype k]

/-- Every nonzero scalar multiplier has a singleton prescribed-product fiber. -/
theorem card_mul_fiber_of_ne_zero (a z : k) (ha : a≠0) :
    Fintype.card {b : k // a*b=z}=1 := by
  have he (b : k) : a*b=z ↔ b=a⁻¹*z := by
    constructor
    · intro h
      rw [← h,← mul_assoc,inv_mul_cancel₀ ha,one_mul]
    · rintro rfl
      rw [← mul_assoc,mul_inv_cancel₀ ha,one_mul]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  simp

/-- The literal product fiber has q-1 points off zero and 2q-1 points at zero. -/
theorem card_mul_fiber (z : k) :
    Fintype.card {p : k × k // p.1*p.2=z}=
      if z=0 then 2*Fintype.card k-1 else Fintype.card k-1 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b : k => a*b=z)),Fintype.card_sigma]
  have hs (a : k) : Fintype.card {b : k // a*b=z}=
      if a=0 then (if z=0 then Fintype.card k else 0) else 1 := by
    by_cases ha : a=0
    · subst a
      by_cases hz : z=0
      · simp [hz]
      · simp [hz,Ne.symm hz]
    · simp [ha,card_mul_fiber_of_ne_zero a z ha]
  simp_rw [hs]
  have heq : Finset.univ.filter (fun x : k => x=0)={0} := by ext x; simp
  have hne : Finset.univ.filter (fun x : k => ¬x=0)=Finset.univ.erase 0 := by ext x; simp
  rw [Finset.sum_ite,heq,hne]
  by_cases hz : z=0 <;> simp [hz,Finset.card_erase_of_mem]
  all_goals omega
/-- Adding a literal hyperbolic product has the exact finite zero-count recurrence. -/
theorem card_zero_add_hyperbolic {X : Type*} [Fintype X] (f : X → k) :
    Fintype.card {w : X × (k × k) // f w.1+w.2.1*w.2.2=0} =
      (Fintype.card k-1)*Fintype.card X+
        Fintype.card k*Fintype.card {x : X // f x=0} := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun x (p : k × k) => f x+p.1*p.2=0)),Fintype.card_sigma]
  have hf (x : X) : Fintype.card {p : k × k // f x+p.1*p.2=0}=
      if f x=0 then 2*Fintype.card k-1 else Fintype.card k-1 := by
    have he (p : k × k) : f x+p.1*p.2=0 ↔ p.1*p.2= -f x := by
      constructor <;> intro h <;> linear_combination h
    rw [Fintype.card_congr (Equiv.subtypeEquivRight he),card_mul_fiber]
    simp only [neg_eq_zero]
  simp_rw [hf]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hc := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun x : X => f x=0)
  rw [Finset.card_univ] at hc
  have hz : Fintype.card {x : X // f x=0}=(Finset.univ.filter (fun x : X => f x=0)).card :=
    Fintype.card_of_subtype _ (by intro x; simp)
  rw [hz]
  have hq : 1 ≤ Fintype.card k := Fintype.card_pos
  have he1 : Fintype.card k-1+1=Fintype.card k := by omega
  have he2 : 2*Fintype.card k-1=2*(Fintype.card k-1)+1 := by omega
  rw [he2]
  nlinarith
/-- The actual hyperbolic splitting gives its exact quadratic zero-count recurrence. -/
theorem hyperbolicSplit_zero_count {V : Type*} [AddCommGroup V] [Module k V] [Fintype V]
    (Q : QuadraticForm k V) (x y : V) (hx : Q x=0) (hy : Q y=0)
    (hxy : Q.polarBilin x y=1) :
    Fintype.card {z : V // Q z=0} =
      (Fintype.card k-1)*Fintype.card (hyperbolicComplement Q x y)+
        Fintype.card k*Fintype.card {z : hyperbolicComplement Q x y // Q (z : V)=0} := by
  let e := hyperbolicSplitIsometry Q x y hx hy hxy
  have he (z : V) : Q z=Q ((e z).1 : V)+(e z).2.1*(e z).2.2 := (e.map_app z).symm
  let es : {z : V // Q z=0} ≃
      {w : hyperbolicComplement Q x y × (k × k) // Q (w.1 : V)+w.2.1*w.2.2=0} :=
    Equiv.subtypeEquiv e.toEquiv (fun z => by rw [he z]; rfl)
  rw [Fintype.card_congr es]
  exact card_zero_add_hyperbolic (fun z : hyperbolicComplement Q x y => Q (z : V))
end BinaryFieldCounterexamples.QuadraticGeometry
