/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.IsotropicDimension
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.Projection
/-!
# Quadratic radical quotients and exact zero fibers

Quotienting by the quadratic radical gives an actual radical-free form in every
characteristic. A linear complement provides a concrete equivalence between
its zero fibers and the original zeros times the radical; no classification
or polar-radical equality is assumed.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
/-- The form lifted through its quadratic radical has zero quadratic radical. -/
theorem radical_lift_radical_eq_bot (Q : QuadraticForm k V) :
    (Q.lift Q.radical le_rfl).radical = ⊥ := by
  apply bot_unique
  intro x hx
  change x=0
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    apply (Submodule.Quotient.mk_eq_zero Q.radical).mpr
    rw [QuadraticMap.mem_radical_iff'] at hx ⊢
    refine ⟨hx.1,?_⟩
    intro y
    have h := hx.2 (Submodule.Quotient.mk y)
    exact h
/-- The radical quotient dimension is the actual quadratic rank. -/
theorem radical_quotient_finrank (Q : QuadraticForm k V) [FiniteDimensional k V] :
    Module.finrank k (V ⧸ Q.radical) = Module.finrank k V - Module.finrank k Q.radical := by
  have h := Q.radical.finrank_quotient_add_finrank
  omega

/-- A radical-contained quotient has a literal product decomposition of its zero fiber. -/
noncomputable def radicalQuotientZeroEquiv (Q : QuadraticForm k V)
    (N : Submodule k V) (hN : N ≤ Q.radical) :
    {x : V // Q x=0} ≃ N × {y : V ⧸ N // Q.lift N hN y=0} := by
  classical
  let W := Classical.choose N.exists_isCompl
  have hw : IsCompl N W := Classical.choose_spec N.exists_isCompl
  let f := N.quotientEquivOfIsCompl W hw
  let e : (N × (V ⧸ N)) ≃ₗ[k] V :=
    ((LinearEquiv.refl k N).prodCongr f).trans (N.prodEquivOfIsCompl W hw)
  have he (z : N × (V ⧸ N)) : N.mkQ (e z)=z.2 := by
    change N.mkQ (z.1.val+(f z.2).val)=z.2
    rw [map_add]
    have hz : N.mkQ z.1.val=0 := (Submodule.Quotient.mk_eq_zero N).mpr z.1.property
    rw [hz,zero_add]
    exact N.mk_quotientEquivOfIsCompl_apply hw z.2
  have hQ (z : N × (V ⧸ N)) : Q (e z)=Q.lift N hN z.2 := by
    rw [←he z]
    rfl
  refine {
    toFun := fun x => ((e.symm x.val).1,⟨(e.symm x.val).2,?_⟩)
    invFun := fun y => ⟨e (y.1,y.2.val),?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [←hQ,e.apply_symm_apply]
    exact x.property
  · rw [hQ]
    exact y.2.property
  · intro x
    apply Subtype.ext
    exact e.apply_symm_apply x.val
  · rintro ⟨a,⟨b,hb⟩⟩
    simp only [e.symm_apply_apply]

/-- Zero-fiber cardinalities multiply by the radical-contained subspace cardinality. -/
theorem quadratic_zero_natCard_quotient (Q : QuadraticForm k V)
    (N : Submodule k V) (hN : N ≤ Q.radical) :
    Nat.card {x : V // Q x=0} = Nat.card N * Nat.card {y : V ⧸ N // Q.lift N hN y=0} := by
  rw [Nat.card_congr (radicalQuotientZeroEquiv Q N hN),Nat.card_prod]

/-- The actual radical contributes its scalar-field power to the zero count. -/
theorem quadratic_zero_natCard_radical [Fintype k] [Fintype V] (Q : QuadraticForm k V) :
    Nat.card {x : V // Q x=0} =
      (Fintype.card k)^(Module.finrank k Q.radical) *
        Nat.card {y : V ⧸ Q.radical // Q.lift Q.radical le_rfl y=0} := by
  rw [quadratic_zero_natCard_quotient Q Q.radical le_rfl,
    Module.natCard_eq_pow_finrank (K:=k),Nat.card_eq_fintype_card]

end BinaryFieldCounterexamples.QuadraticGeometry
