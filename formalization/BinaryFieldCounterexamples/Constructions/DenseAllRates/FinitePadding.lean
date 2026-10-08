/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.BalancedPaddingTransfer
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.DomainSeed
/-!
# Finite balanced padding of actual dense seed lists

First select exactly the requested number of distinct seed explaining polynomials,
so the balanced-padding error depends on that number. Multiplication by one common
nonzero nodal polynomial preserves cardinality and adds the exact degree budget.
The actual trace seed specializes this construction on every affine additive
domain; natural floors convert its real lower bounds to integer thresholds.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.DenseConstruction
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
/-- Select an exact-size list before balanced nodal padding. Polynomial
multiplication preserves every distinct explaining polynomial. -/
theorem finite_list_balanced_padding {B:Type*} [Field B]
    (S:Finset B) (w:S→B) (E:Finset B[X]) (K J T L:ℕ)
    (hE:∀f∈E,f.degree<K ∧ T≤agreementCount S w f)
    (hL:L≤E.card) (hK:K≤J) (hJ:J-K≤S.card) :
    ∃(w':S→B)(E':Finset B[X]), E'.card=L ∧
      ∀f∈E',f.degree<J ∧
        (J-K:ℕ)+(T:ℝ)-((J-K:ℕ)*T/S.card+
          Real.sqrt (((J-K:ℕ)/2:ℝ)*Real.log (2*L)))≤(agreementCount S w' f:ℝ) := by
  obtain ⟨I,hIE,hI⟩:=Finset.exists_subset_card_eq hL
  let g:B→B:=fun x=>if hx:x∈S then w ⟨x,hx⟩ else 0
  have hg : (fun x:S=>g x)=w := by
    funext x
    simp [g,x.property]
  obtain ⟨W,hWS,hW,hprop⟩:=exists_common_nodal_padding_of_agreementGE S I g id K T (J-K)
    (fun f hf=>(hE f (hIE hf)).1)
    (fun f hf=>by simpa only [hg,id_eq] using (hE f (hIE hf)).2) hJ
  let A:=Lagrange.nodal W id
  let E':=I.image (fun f=>A*f)
  refine ⟨fun x=>A.eval x.val*w x,E',?_,?_⟩
  · rw [Finset.card_image_iff.mpr (by
      intro f hf g hg hfg
      exact mul_left_cancel₀ Lagrange.nodal_ne_zero hfg),hI]
  · intro f hf
    obtain ⟨f0,hgI,rfl⟩:=Finset.mem_image.mp hf
    have hp:=hprop f0 hgI
    have hw : (fun x:S=>A.eval x.val*w x)=
        (fun x:S=>(Lagrange.nodal W id).eval x.val*g x) := by
      funext x
      simp only [A,congrFun hg x]
    rw [hw]
    simpa only [hI,id_eq,A,←Nat.cast_add,Nat.sub_add_cancel hK] using hp
end BinaryFieldCounterexamples.DenseConstruction
namespace BinaryFieldCounterexamples.DenseConstruction
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
/-- The actual binary trace seed admits a common exact-size balanced padding,
keeping any prescribed integer number of its distinct explaining polynomials. -/
theorem binary_dense_padded_list
    (ell n t c : ℕ) (hell : 1≤ell) (ht : 1≤t) (htn : t≤n) (hc : c<ell)
    (B : Type*) [Field B] [Fintype B] [CharP B 2]
    (hcard : Fintype.card B=(2^ell)^(2*n))
    (D : AddSubgroup B) (v : B) (hD : (additiveDomain D).card*2^c=Fintype.card B)
    (J L:ℕ) (hK:(2^ell)^(2*n-2)≤J)
    (hJ:J-(2^ell)^(2*n-2)≤(affineDomain (additiveDomain D) v).card)
    (hL:(L:ℚ)≤((2^ell:ℕ):ℚ)^(2*t)*(((2^ell:ℕ):ℚ)^t-1)*
      quadraticGaussian ((2^ell)^2) n t/((2^ell:ℕ)-1)) :
    let S:=affineDomain (additiveDomain D) v
    let K:ℕ:=(2^ell)^(2*n-2)
    let T0:ℕ:=⌊(S.card:ℝ)/(2^ell:ℕ)-
      (((2^ell:ℕ)-1:ℕ):ℝ)*(2^(ell*(2*n-t)):ℕ)/(2^ell:ℕ)⌋₊
    ∃(w:S→B)(E:Finset B[X]), E.card=L ∧
      ∀f∈E,f.degree<J ∧
        (J-K:ℕ)+(T0:ℝ)-((J-K:ℕ)*T0/S.card+
          Real.sqrt (((J-K:ℕ)/2:ℝ)*Real.log (2*L)))≤(agreementCount S w f:ℝ) := by
  dsimp only
  obtain ⟨w,E,hE,hprop⟩:=binary_dense_seed_list ell n t c hell ht htn hc B hcard D v hD
  apply finite_list_balanced_padding _ w E _ J _ L _ _ hK hJ
  · intro f hf
    exact ⟨(hprop f hf).1,Nat.floor_le_of_le (hprop f hf).2⟩
  · exact_mod_cast le_trans hL hE
/-- An explicit real agreement bound gives a decoding list at its natural
floor, keeping the exact selected list size. -/
theorem ordinaryList_of_real_bound {B:Type*} [Field B]
    (S:Finset B) (J L:ℕ) (T:ℝ) (w:S→B) (E:Finset B[X]) (hE:E.card=L)
    (hprop:∀f∈E,f.degree<J ∧ T≤(agreementCount S w f:ℝ)) :
    ordinaryList S J ⌊T⌋₊ L := by
  refine ⟨w,E,?_,?_⟩
  · omega
  · intro f hf
    exact ⟨(hprop f hf).1,Nat.floor_le_of_le (hprop f hf).2⟩
end BinaryFieldCounterexamples.DenseConstruction
