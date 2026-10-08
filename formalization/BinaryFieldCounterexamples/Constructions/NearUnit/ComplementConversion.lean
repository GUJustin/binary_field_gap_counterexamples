/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.TraceRestriction
public import BinaryFieldCounterexamples.Constructions.Gold.RankParity
public import BinaryFieldCounterexamples.Polynomial.QuadraticDifferential
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalRoots
/-!
# Complement conversion for binary native locators

This module isolates the algebra shared by even and odd native Boolean
families.  An exhausted native factor and its differential identity produce a
complement locator, a strict quarter-degree correction, the exact complementary
root count, and the exterior reciprocal value relation.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.NearUnit
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Every derivative in characteristic two has a literal polynomial square
root, without any finite-field coordinate choices. -/
theorem binaryDerivative_square_root
    {B:Type*} [Field B] [Fintype B] [CharP B 2] (H:B[X]):
    (primePowerPolynomialRoot 2 1 H.derivative)^2=H.derivative := by
  apply primePowerPolynomialRoot_pow 2 1 H.derivative
  intro j hj
  norm_num only [pow_one]
  by_contra hj2
  have hd:2∣j+1:=by omega
  have hz:((j+1:ℕ):B)=0:=(CharP.cast_eq_zero_iff B 2 _).mpr hd
  have hc:=mem_support_iff.mp hj
  apply hc
  simp only [Nat.cast_add,Nat.cast_one] at hz
  rw [coeff_derivative,hz,mul_zero]

/-- The differential and factorization identities produce the literal square
identity for the complement conversion. -/
theorem binaryComplement_exists_conversion
    {B:Type*} [Field B] [Fintype B] [CharP B 2]
    (L H R:B[X]) (hH:H≠0) (hfactor:L=H*R)
    (hdifferential:H^2+H=L*H.derivative) :
    ∃P:B[X],P=primePowerPolynomialRoot 2 1 H.derivative*R ∧ P^2=L+R := by
  let A:=primePowerPolynomialRoot 2 1 H.derivative
  have hA:A^2=H.derivative:=binaryDerivative_square_root H
  have hcancel:H+1=R*A^2:=by
    apply mul_left_cancel₀ hH
    rw [←hA,hfactor] at hdifferential
    linear_combination hdifferential
  refine ⟨A*R,rfl,?_⟩
  calc
    (A*R)^2=(R*A^2)*R:=by ring
    _=(H+1)*R:=by rw [←hcancel]
    _=L+R:=by rw [hfactor];ring

/-- On the full binary field, the converted polynomial vanishes exactly at
points outside the native zero set. -/
theorem binaryComplement_eval_zero_iff
    {B:Type*} [Field B] [Fintype B] [CharP B 2]
    (L H R P:B[X])
    (hL:L=X^(Fintype.card B)+X) (hfactor:L=H*R)
    (hP:P^2=L+R) (x:B) : P.eval x=0 ↔ H.eval x≠0 := by
  have hLeval:L.eval x=0:=by
    rw [hL]
    simp [FiniteField.pow_card,CharTwo.add_self_eq_zero]
  have he:=congrArg (fun Q:B[X]=>Q.eval x) hfactor
  rw [hLeval,eval_mul] at he
  have hp:=congrArg (fun Q:B[X]=>Q.eval x) hP
  rw [eval_pow,eval_add,hLeval,zero_add] at hp
  have hd:L.derivative=1:=by
    rw [hL]
    simp [derivative_pow]
  constructor
  · intro hz hh
    have hr:R.eval x=0:=by rw [hz,zero_pow (by decide)] at hp;exact hp.symm
    have hder:=congrArg (fun Q:B[X]=>Q.derivative.eval x) hfactor
    rw [hd,eval_one,derivative_mul,eval_add,eval_mul,eval_mul,hh,hr,
      mul_zero,zero_mul,add_zero] at hder
    exact one_ne_zero hder
  · intro hh
    have hr:R.eval x=0:=(mul_eq_zero.mp he.symm).resolve_left hh
    rw [hr] at hp
    exact (pow_eq_zero_iff (by decide)).mp hp

/-- A factor with `2K+r` native roots converts to a locator with exactly
`2K-r` complementary roots and a strict correction below `K`. -/
theorem binaryComplement_exists_locator
    {B:Type*} [Field B] [Fintype B] [CharP B 2]
    (K r:ℕ) (hK:0<K) (hr:0<r) (hrK:r≤2*K)
    (hcard:Fintype.card B=4*K) (H R:B[X]) (hH:H≠0)
    (hHdegree:H.natDegree=2*K+r)
    (hHroots:(Finset.univ.filter (fun x:B=>H.eval x=0)).card=2*K+r)
    (hfactor:X^(4*K)+X=H*R)
    (hdifferential:H^2+H=(X^(4*K)+X)*H.derivative) :
    ∃U:B[X],(X^(2*K)+U)^2=X^(4*K)+X+R ∧
      U.natDegree<K ∧
      (Finset.univ.filter (fun x:B=>(X^(2*K)+U).eval x=0)).card=2*K-r := by
  let L:B[X]:=X^(4*K)+X
  obtain ⟨P,hPdef,hP⟩:=binaryComplement_exists_conversion L H R hH hfactor hdifferential
  have hLdegree:L.natDegree=4*K:=by
    rw [show L=X^(4*K)-X by simp only [L,CharTwo.sub_eq_add]]
    rw [←hcard]
    exact FiniteField.X_pow_card_sub_X_natDegree_eq B Fintype.one_lt_card
  have hL0:L≠0:=by
    intro hz
    rw [hz,natDegree_zero] at hLdegree
    omega

  have hR0:R≠0:=by intro hz;rw [hz,mul_zero] at hfactor;exact hL0 hfactor
  have hRdegree:R.natDegree=2*K-r:=by
    have hh:=congrArg natDegree hfactor
    change L.natDegree=(H*R).natDegree at hh
    rw [hLdegree,natDegree_mul hH hR0,hHdegree] at hh
    omega
  let U:=P-X^(2*K)
  have hPU:X^(2*K)+U=P:=by dsimp [U];ring
  refine ⟨U,by simpa only [hPU,L] using hP,?_,?_⟩
  · have hcommon:(P-X^(2*K)).natDegree<K:=by
      apply QuadraticLocatorConversion.common_head_natDegree_lt P (X^(2*K)) (X+R) 2 1
      · norm_num only [pow_one]
        rw [←pow_mul,show 2*K*2=4*K by omega,hP,CharTwo.sub_eq_add]
        have hz:(2:B[X])=0:=CharP.cast_eq_zero B[X] 2
        linear_combination hz*(X^(4*K))
      · norm_num only [pow_one]
        have hX: (X:B[X]).natDegree<2*K:=by simp only [natDegree_X];omega
        exact (natDegree_add_le _ _).trans_lt
          (max_lt hX (by rw [hRdegree];omega))
    exact hcommon
  · rw [hPU]
    have he:(Finset.univ.filter (fun x:B=>P.eval x=0))=
        Finset.univ.filter (fun x:B=>H.eval x≠0):=by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      apply binaryComplement_eval_zero_iff L H R P
        (show L=X^(Fintype.card B)+X by dsimp [L];rw [hcard]) hfactor hP x
    rw [he]
    have hc:=Finset.card_filter_add_card_filter_not (s:=Finset.univ)
      (fun x:B=>H.eval x=0)
    have hc':(Finset.univ.filter (fun x:B=>H.eval x=0)).card+
        (Finset.univ.filter (fun x:B=>H.eval x≠0)).card=
          (Finset.univ:Finset B).card:=by
      simpa only [ne_eq] using hc
    rw [hHroots,Finset.card_univ,hcard] at hc'
    omega

end BinaryFieldCounterexamples.NearUnit
