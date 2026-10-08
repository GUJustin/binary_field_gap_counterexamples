/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularLineFlags
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularFlags
/-!
# Actual through-line singular-subspace fibers

The flag fibers are identified with the literal radical or perpendicular
quotients. Nonradical singular lines admit actual hyperbolic generators.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
/-- Unpack the actual through-line flag subtype into the subspace description. -/
noncomputable def throughLineSubtypeEquiv (Q : QuadraticForm k V) (L : SingularLines Q) (e : ℕ) :
    {S : TotallySingularSubspaces Q e // L.val≤S.val} ≃
      {S : Submodule k V // L.val≤S ∧ Module.finrank k S=e ∧ ∀ z ∈ S,Q z=0} :=
  { toFun := fun S => ⟨S.val.val,S.property,S.val.property⟩
    invFun := fun S => ⟨⟨S.val,S.property.2⟩,S.property.1⟩
    left_inv := by intro S; rfl
    right_inv := by intro S; rfl }
/-- Through a radical line, the exact fiber is the singular-subspace count of the radical quotient. -/
theorem through_radical_line_card [FiniteDimensional k V]
    (Q : QuadraticForm k V) (L : SingularLines Q) (hL : L.val≤Q.radical) (e : ℕ) :
    Nat.card {S : TotallySingularSubspaces Q (e+1) // L.val≤S.val}=
      Nat.card (TotallySingularSubspaces (Q.lift L.val hL) e) := by
  rw [Nat.card_congr (throughLineSubtypeEquiv Q L (e+1))]
  let eqv := isotropicQuotientDimensionEquiv Q L.val hL e
  rw [L.property.1] at eqv
  exact Nat.card_congr eqv.symm
/-- An actual nonradical singular line has a hyperbolic generating vector and partner. -/
theorem nonradical_line_hyperbolic [FiniteDimensional k V]
    (Q : QuadraticForm k V) (L : SingularLines Q) (hL : ¬L.val≤Q.radical) :
    ∃ x y : V, x≠0 ∧ Q x=0 ∧ Q y=0 ∧ Q.polarBilin x y=1 ∧ k ∙ x=L.val := by
  classical
  obtain ⟨x,hxL,hxr⟩ := SetLike.not_le_iff_exists.mp hL
  have hx : Q x=0 := L.property.2 x hxL
  have hne : x≠0 := by intro h; subst x; exact hxr Q.radical.zero_mem
  have hxp : x∉Q.polarBilin.ker := by intro hp; exact hxr ⟨hx,hp⟩
  obtain ⟨y,hy,hxy⟩ := exists_hyperbolic_partner Q x hx hxp
  refine ⟨x,y,hne,hx,hy,hxy,?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_singleton_le_iff_mem]; exact hxL
  · rw [finrank_span_singleton hne,L.property.1]
/-- Through a singular line, the exact fiber is the count in its literal perpendicular quotient. -/
theorem through_singular_line_card [FiniteDimensional k V]
    (Q : QuadraticForm k V) (L : SingularLines Q) (x : V) (hx : Q x=0)
    (hne : x≠0) (hspan : k ∙ x=L.val) (e : ℕ) :
    Nat.card {S : TotallySingularSubspaces Q (e+1) // L.val≤S.val}=
      Nat.card (TotallySingularSubspaces
        ((Q.comp (Q.polarBilin x).ker.subtype).lift (singularPerpLine Q x hx)
          (singularPerpLine_le_radical Q x hx)) e) := by
  rw [Nat.card_congr (throughLineSubtypeEquiv Q L (e+1)),←hspan]
  exact Nat.card_congr (singularLineFlagQuotientEquiv Q x hx hne e)
end BinaryFieldCounterexamples.QuadraticGeometry
