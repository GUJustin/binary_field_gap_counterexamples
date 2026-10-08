/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ActualHyperbolicIncidence
public import BinaryFieldCounterexamples.Counting.QuadraticRankOneWeight
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open scoped BigOperators
variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]
/-- An anisotropic form has only the zero totally singular subspace. -/
theorem totallySingularSubspaces_card_anisotropic (Q : QuadraticForm k V)
    (hQ : ∀ x,Q x=0→x=0) (e : ℕ) :
    Nat.card (TotallySingularSubspaces Q e)=if e=0 then 1 else 0 := by
  classical
  by_cases he : e=0
  · subst e
    simp [totallySingularSubspaces_zero_card]
  · rw [ite_eq_right he]
    let : IsEmpty (TotallySingularSubspaces Q e) := ⟨fun S => by
      have hS : S.val=⊥ := by
        apply bot_unique
        intro x hx
        exact hQ x (S.property.2 x hx)
      have hh := S.property.1
      rw [hS,finrank_bot] at hh
      exact he hh.symm⟩
    simp
/-- Convolving the anisotropic delta sequence leaves exactly the radical's Gaussian subspace count. -/
theorem rationalRadicalConvolution_delta (q h e : ℕ) :
    rationalRadicalConvolution q h (fun i => if i=0 then 1 else 0) e=
      (gaussianPascal q h e:ℚ) := by
  unfold rationalRadicalConvolution
  rw [Finset.sum_eq_single e]
  · simp
  · intro a ha hne
    have he : e-a≠0 := by have := Finset.mem_range.mp ha; omega
    simp [he]
  · simp
/-- If the quadratic radical quotient is anisotropic, all actual singular subspaces lie in the radical. -/
theorem totallySingularSubspaces_card_of_anisotropic_quotient (Q : QuadraticForm k V)
    (hQ : ∀ x : V ⧸ Q.radical,Q.lift Q.radical le_rfl x=0→x=0) (e : ℕ) :
    (Nat.card (TotallySingularSubspaces Q e):ℚ)=
      (gaussianPascal (Fintype.card k) (Module.finrank k Q.radical) e:ℚ) := by
  classical
  let : Fintype (V ⧸ Q.radical) := Fintype.ofFinite _
  rw [actual_singular_count_eq_rationalRadicalConvolution]
  simp_rw [totallySingularSubspaces_card_anisotropic _ hQ,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  exact rationalRadicalConvolution_delta _ _ _
/-- The actual inverse kernel of an anisotropic radical quotient is its explicit codimension incidence sum. -/
theorem rankIncidenceKernel_anisotropic_quotient (Q : QuadraticForm k V)
    (hQ : ∀ x : V ⧸ Q.radical,Q.lift Q.radical le_rfl x=0→x=0) (r : ℕ) :
    rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q) r=
      ∑ e ∈ Finset.range (r+1),gaussianMobius (Fintype.card k) (r-e)*
        (gaussianPascal (Fintype.card k) (Module.finrank k V-e) (r-e):ℚ)*
        (Fintype.card k:ℚ)^(e*(e+1)/2)*
        (gaussianPascal (Fintype.card k) (Module.finrank k Q.radical) e:ℚ) := by
  unfold rankIncidenceKernel quadraticIncidenceSequence
  simp_rw [totallySingularSubspaces_card_of_anisotropic_quotient Q hQ,mul_assoc]
end BinaryFieldCounterexamples.QuadraticGeometry
