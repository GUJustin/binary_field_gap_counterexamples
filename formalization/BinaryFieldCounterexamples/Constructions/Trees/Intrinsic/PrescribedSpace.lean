/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Counts
/-!
# Intrinsic trees with prescribed essential coordinates

Lemma 6.6 in Section 6.2 states that every prescribed essential dual space of
dimension `t_h = 2^h - 1` carries exactly `C_h` tree functions. This module
constructs the literal bijection with tree functions on the quotient by that
space's common kernel. The quotient has dimension `t_h`, and every tree on it
uses all its coordinates. Consequently its pullback has exactly the prescribed
essential dual space. The count follows from the already proved minimal-space
count, without counting tree presentations or assuming unique roots.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
open Module
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Quotienting by the common kernel of `E` leaves exactly `dim E` coordinates. -/
theorem finrank_quotient_dualCoannihilator (E : Submodule (ZMod 2) (Dual (ZMod 2) V)) :
    finrank (ZMod 2) (V ⧸ E.dualCoannihilator) = finrank (ZMod 2) E := by
  have hq := E.dualCoannihilator.finrank_quotient_add_finrank
  have he := Subspace.finrank_add_finrank_dualCoannihilator_eq E
  omega

/-- On a minimal-dimensional space every intrinsic tree has no ignored directions. -/
theorem IsTreeFunction.periodSubmodule_eq_bot_of_finrank_eq {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    {h : ℕ} {f : W → ZMod 2} (hf : IsTreeFunction h f)
    (hd : finrank (ZMod 2) W = 2^h-1) : periodSubmodule f = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  have he := hf.essentialDimension
  have ha := essentialDimension_add_finrank_periodSubmodule f
  omega

/-- Every tree on the quotient by `E` pulls back with exactly essential space `E`. -/
theorem IsTreeFunction.essentialDualSpace_quotient_pullback {h : ℕ}
    (E : Submodule (ZMod 2) (Dual (ZMod 2) V))
    (hE : finrank (ZMod 2) E = 2^h-1)
    {g : V ⧸ E.dualCoannihilator → ZMod 2} (hg : IsTreeFunction h g) :
    essentialDualSpace (fun x => g (E.dualCoannihilator.mkQ x)) = E := by
  let : Fintype (V ⧸ E.dualCoannihilator) := Fintype.ofFinite _
  have hd : finrank (ZMod 2) (V ⧸ E.dualCoannihilator) = 2^h-1 :=
    (finrank_quotient_dualCoannihilator E).trans hE
  have hp := hg.periodSubmodule_eq_bot_of_finrank_eq hd
  have hfree (u : V ⧸ E.dualCoannihilator) : IsPeriod g u ↔ u=0 := by
    change u ∈ periodSubmodule g ↔ _
    rw [hp, Submodule.mem_bot]
  have he := essentialDualSpace_affineMap_precompose_periodFree g hfree
    E.dualCoannihilator.mkQ.toAffineMap E.dualCoannihilator.mkQ_surjective
  change essentialDualSpace (fun x => g (E.dualCoannihilator.mkQ x)) =
    E.dualCoannihilator.mkQ.ker.dualAnnihilator at he
  rw [he, Submodule.ker_mkQ]
  exact Subspace.dualCoannihilator_dualAnnihilator_eq

omit [Fintype V] in
/-- A function with essential space `E` is constant along the common kernel of `E`. -/
theorem dualCoannihilator_le_periodSubmodule_of_essentialDualSpace_eq
    (E : Submodule (ZMod 2) (Dual (ZMod 2) V)) (f : V → ZMod 2)
    (hf : essentialDualSpace f = E) : E.dualCoannihilator ≤ periodSubmodule f := by
  rw [← hf, essentialDualSpace_dualCoannihilator]

/-- Literal tree functions with prescribed essential space correspond to trees on
its minimal quotient. Both maps are actual quotient descent and pullback. -/
noncomputable def treeFunctionsPrescribedEssentialEquivQuotient (h : ℕ)
    (E : Submodule (ZMod 2) (Dual (ZMod 2) V))
    (hE : finrank (ZMod 2) E = 2^h-1) :
    {f : V → ZMod 2 // IsTreeFunction h f ∧ essentialDualSpace f = E} ≃
      {g : V ⧸ E.dualCoannihilator → ZMod 2 // IsTreeFunction h g} := by
  letI : Fintype (V ⧸ E.dualCoannihilator) := Fintype.ofFinite _
  let P := E.dualCoannihilator
  let hp (f : {f : V → ZMod 2 // IsTreeFunction h f ∧ essentialDualSpace f = E}) :
      P ≤ periodSubmodule f.1 :=
    dualCoannihilator_le_periodSubmodule_of_essentialDualSpace_eq E f.1 f.2.2
  refine {
    toFun := fun f => ⟨quotientFunction f.1 P (hp f),
      (isTreeFunction_quotient_iff h f.1 P (hp f)).mp f.2.1⟩
    invFun := fun g => ⟨fun x => g.1 (P.mkQ x),
      g.2.affineMap_precompose P.mkQ.toAffineMap P.mkQ_surjective,
      g.2.essentialDualSpace_quotient_pullback E hE⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro f
    apply Subtype.ext
    funext x
    exact quotientFunction_mkQ f.1 P (hp f) x
  · intro g
    apply Subtype.ext
    funext q
    obtain ⟨x, rfl⟩ := P.mkQ_surjective q
    rfl

/-- Lemma 6.6: every prescribed `t_h`-dimensional essential dual space carries
exactly `C_h`, the minimal-space count, intrinsic tree functions. -/
theorem isTreeFunction_prescribed_essentialDualSpace_count (n : ℕ)
    (E : Submodule (ZMod 2) (Dual (ZMod 2) V))
    (hE : finrank (ZMod 2) E = 2^(n+2)-1) :
    Nat.card {f : V → ZMod 2 // IsTreeFunction (n+2) f ∧ essentialDualSpace f = E} =
      treeSupportCount (n+2) (2^(n+2)-1) := by
  let : Fintype (V ⧸ E.dualCoannihilator) := Fintype.ofFinite _
  rw [Nat.card_congr (treeFunctionsPrescribedEssentialEquivQuotient (n+2) E hE)]
  have hd : finrank (ZMod 2) (V ⧸ E.dualCoannihilator) = 2^(n+2)-1 :=
    (finrank_quotient_dualCoannihilator E).trans hE
  rw [isTreeFunction_count n (by rw [hd]), hd]

end BinaryFieldCounterexamples.Trees
