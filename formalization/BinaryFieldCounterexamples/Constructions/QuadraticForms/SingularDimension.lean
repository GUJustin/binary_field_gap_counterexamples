/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SingularProducts
/-!
# Exact vanishing ranges for radical-free singular-subspace counts

Induction through the actual singular-line quotient bounds singular dimension
by half the ambient dimension, including characteristic two. The elliptic
cleared product also excludes the boundary half-dimensional subspaces.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
universe u v
variable {k : Type u} [Field k]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
/-- In every characteristic, a totally singular subspace of a radical-free quadratic space has at most half the ambient dimension. -/
theorem totally_singular_finrank_le_half (e : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (Q : QuadraticForm k V), Q.radical=⊥ → ∀ S : Submodule k V,
      (∀ z ∈ S,Q z=0) → Module.finrank k S=e → 2*e≤Module.finrank k V := by
  induction e with
  | zero => intro V _ _ _ Q hQ S hS he; omega
  | succ e ih =>
    intro V _ _ _ Q hQ S hS he
    have hSbot : S≠⊥ := by intro h; rw [h,finrank_bot] at he; omega
    obtain ⟨x,hxS,hxne⟩ := S.ne_bot_iff.mp hSbot
    have hx := hS x hxS
    obtain ⟨y,hy,hxy⟩ := exists_hyperbolic_partner Q x hx
      (singular_not_mem_polar_ker_of_radical_bot Q hQ x hx hxne)
    let T := singularLineFlagQuotientEquiv Q x hx hxne e
      ⟨S,by rw [Submodule.span_singleton_le_iff_mem]; exact hxS,he,hS⟩
    let Q' := (Q.comp (Q.polarBilin x).ker.subtype).lift (singularPerpLine Q x hx)
      (singularPerpLine_le_radical Q x hx)
    have hQ' : Q'.radical=⊥ := by
      apply Submodule.finrank_eq_zero.mp
      rw [singularLineQuotient_radical_finrank Q x y hx hy hxy,hQ,finrank_bot]
    have h := ih Q' hQ' T.val T.property.2 T.property.1
    rw [singularLineQuotient_finrank Q x y hx hy hxy] at h
    have hd := hyperbolicComplement_finrank Q x y hx hy hxy
    omega
/-- Beyond half dimension, a radical-free form has no actual totally singular subspaces. -/
theorem totallySingularSubspaces_card_eq_zero_of_large [Fintype k]
    {V : Type v} [AddCommGroup V] [Module k V] [Fintype V]
    (Q : QuadraticForm k V) (hQ : Q.radical=⊥) (e : ℕ) (he : Module.finrank k V<2*e) :
    Nat.card (TotallySingularSubspaces Q e)=0 := by
  have hempty : IsEmpty (TotallySingularSubspaces Q e) := ⟨fun S => by
    have h := totally_singular_finrank_le_half e Q hQ S.val S.property.2 S.property.1
    omega⟩
  let := hempty
  simp
/-- An elliptic radical-free even-dimensional form has no maximal half-dimensional singular subspace. -/
theorem totallySingularSubspaces_card_eq_zero_elliptic [Fintype k]
    {V : Type v} [AddCommGroup V] [Module k V] [Fintype V]
    (Q : QuadraticForm k V) (hQ : Q.radical=⊥) (s : ℕ) (hs : 1≤s)
    (hd : Module.finrank k V=2*s)
    (hz : Nat.card {x : V // Q x=0}=evenQuadraticZeroCount (Fintype.card k) s false) :
    Nat.card (TotallySingularSubspaces Q s)=0 := by
  classical
  have hp := totallySingularSubspaces_product_even Q hQ s s le_rfl hd false hz
  have hzprod : (∏ i ∈ Finset.range s,(evenQuadraticZeroCount (Fintype.card k) (s-i) false-1))=0 := by
    apply Finset.prod_eq_zero (i:=s-1) (Finset.mem_range.mpr (by omega))
    rw [show s-(s-1)=1 by omega]
    simp only [evenQuadraticZeroCount,Bool.false_eq_true,↓reduceIte,
      Nat.reduceSub,pow_one,pow_zero,mul_one]
    have hq := Fintype.card_pos (α:=k)
    omega
  rw [hzprod] at hp
  have hpos : 0 < ∏ i ∈ Finset.range s,((Fintype.card k)^(i+1)-1) := by
    apply Finset.prod_pos
    intro i hi
    have hq : 1<Fintype.card k := Fintype.one_lt_card
    have hpow : Fintype.card k≤(Fintype.card k)^(i+1) := by
      simpa using Nat.pow_le_pow_right (by omega : 1≤Fintype.card k) (by omega : 1 ≤ i + 1)
    omega
  exact (Nat.mul_eq_zero.mp hp).resolve_right (by omega)
end BinaryFieldCounterexamples.QuadraticGeometry
