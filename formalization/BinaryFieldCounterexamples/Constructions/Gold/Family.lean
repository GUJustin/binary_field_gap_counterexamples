/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Distinctness
public import BinaryFieldCounterexamples.Constructions.Gold.QuadraticCharacters
public import BinaryFieldCounterexamples.Agreement.AffineTransport
public import BinaryFieldCounterexamples.Constructions.Gold.MatrixRank
/-!
# The complete finite Gold locator and decoding-list family

The actual finite set of moment-constrained rank-`2t` tensors is paired with
all radical-compatible repairs. Walsh counting supplies each repair's unique
majority level; polynomial recovery proves every resulting locator distinct.
The family size is exactly the tensor count times `2^(2t)`. The fixed received word
and affine translation then give a decoding list with the paper's strict
message degree and root threshold on the prescribed translated domain.

The remaining population theorem must lower-bound `momentTensors.card` by
the alternating-form rank-and-moment count. No such bound is assumed in the
finite family construction proved here.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
open scoped BigOperators
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- The literal finite set of rank-constrained tensors whose initial Gold moments vanish. -/
noncomputable def momentTensors (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) : Finset (TensorCoordinates d) := by
  classical
  letI : Fintype (TensorCoordinates d) := inferInstanceAs (Fintype (TensorIndex d → ZMod 2))
  exact Finset.univ.filter fun A ↦ tensorPolarRank D v A=2*t ∧
    ∀ r, 1 ≤ r → r<t → goldMoment D v A r=0
/-- Membership in the finite moment-constrained tensor set preserves the concrete rank and equations. -/
theorem mem_momentTensors (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) (A : TensorCoordinates d) :
    A ∈ momentTensors D v t ↔ tensorPolarRank D v A=2*t ∧
      ∀ r, 1 ≤ r → r<t → goldMoment D v A r=0 := by
  classical
  simp [momentTensors]
/-- Adding a locator to the fixed received word turns its actual roots into codeword agreements. -/
theorem agreementCount_add_source_eq_roots {B : Type*} [Field B] [Fintype B] (D : AddSubgroup B) (R P : B[X]) :
    agreementCount (additiveDomain D) (fun x ↦ R.eval (x : B)) (P+R) =
      Nat.card {x : D // P.eval (x : B)=0} := by
  classical
  rw [agreementCount_eq_card_filter (additiveDomain D) (fun x : B ↦ R.eval x) (P+R)]
  let S := Finset.univ.image (fun x : {x : D // P.eval (x : B)=0} ↦ (x.val : B))
  have he : (additiveDomain D).filter (fun x ↦ (P+R).eval x=R.eval x)=S := by
    ext x
    simp only [Finset.mem_filter, mem_additiveDomain, eval_add, add_eq_right, S, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx,hr⟩
      exact ⟨⟨⟨x,hx⟩,hr⟩,rfl⟩
    · rintro ⟨y,rfl⟩
      exact ⟨y.val.property,y.property⟩
  rw [he, Finset.card_image_iff.mpr (show Function.Injective (fun x : {x : D // P.eval (x : B)=0} ↦ (x.val : B)) from
    fun a b h ↦ Subtype.ext (Subtype.ext h)).injOn, Finset.card_univ, Nat.card_eq_fintype_card]
/-- A finite injective locator family gives a literal decoding list on every translated prescribed domain. -/
theorem ordinaryList_of_locator_family {B : Type*} [Field B] [Fintype B] (D : AddSubgroup B) (a : B) (R : B[X])
    {ι : Type*} [Fintype ι] (P : ι → B[X]) (hP : Function.Injective P) (K T : ℕ)
    (hdegree : ∀ i, (P i+R).degree<K)
    (hroots : ∀ i, T ≤ Nat.card {x : D // (P i).eval (x : B)=0}) :
    ordinaryList (affineDomain (additiveDomain D) a) K T (Fintype.card ι) := by
  classical
  let p := fun i ↦ (P i+R).comp (X-C a)
  have hp : Function.Injective p := by
    intro i j h
    have he := congrArg (fun Q : B[X] ↦ Q.comp (X+C a)) h
    simp only [p, comp_assoc] at he
    have hc : (X-C a).comp (X+C a)=(X : B[X]) := by simp
    rw [hc, comp_X, comp_X] at he
    exact hP (add_right_cancel he)
  refine ⟨fun x ↦ R.eval ((x : B)-a), Finset.univ.image p, ?_, ?_⟩
  · rw [Finset.card_image_iff.mpr hp.injOn, Finset.card_univ]
  · intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    constructor
    · change ((P i+R).comp (X-C a)).degree<K
      rw [degree_comp (by simp), degree_X_sub_C, mul_one]
      exact hdegree i
    · rw [agreementCount_affineDomain (additiveDomain D) a (fun x : B ↦ R.eval x)]
      have hc : (p i).comp (X+C a)=P i+R := by simp [p, comp_assoc]
      rw [hc, agreementCount_add_source_eq_roots]
      exact hroots i
/-- The actual tensor function and polar form as finite quadratic data for Walsh counting. -/
noncomputable def tensorQuadraticData (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) : BinaryQuadraticData D :=
  BinaryQuadraticData.mk (tensorQuadraticFunction D v A) (tensorPolarLinearMap D v A)
    (tensorQuadraticFunction_zero D v A) (tensorQuadraticFunction_add D v A)
/-- Changing the dual representation preserves the concrete polar rank. -/
theorem tensorQuadraticData_rank (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    Module.finrank (ZMod 2) (LinearMap.range (tensorQuadraticData D v A).polarMap)=tensorPolarRank D v A := by
  exact tensorPolarLinearMap_finrank_range D v A
/-- Every moment-constrained tensor is paired with every radical-compatible linear repair. -/
noncomputable def tensorRepairIndices (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) :
    Finset ((_A : TensorCoordinates d) × Module.Dual (ZMod 2) D) := by
  classical
  exact (momentTensors D v t).sigma fun A ↦ (tensorQuadraticData D v A).repairs
/-- The concrete repair index set has exactly the tensor count times `2^(2t)` elements. -/
theorem card_tensorRepairIndices (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) :
    (tensorRepairIndices D v t).card=(momentTensors D v t).card*2^(2*t) := by
  classical
  rw [tensorRepairIndices, Finset.card_sigma]
  calc
    ∑ A ∈ momentTensors D v t, (tensorQuadraticData D v A).repairs.card =
        ∑ A ∈ momentTensors D v t, 2^(2*t) := by
      apply Finset.sum_congr rfl
      intro A hA
      apply BinaryQuadraticData.card_repairs_of_polarRank
      rw [tensorQuadraticData_rank]
      exact (mem_momentTensors D v t A).mp hA |>.1
    _ = _ := by simp
/-- Every moment-constrained tensor and every radical-compatible repair contributes a distinct actual locator. -/
theorem exists_repairedLocator_family (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j) = if i=j then 1 else 0)
    (t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1) :
    ∃ ps : Finset B[X], ps.card=(momentTensors D v t).card*2^(2*t) ∧
      ∀ p ∈ ps, ∃ A ∈ momentTensors D v t, ∃ l : D →+ ZMod 2, ∃ κ : ZMod 2,
        p=repairedLocator D v A l κ t ∧
          Nat.card {y : D // tensorQuadraticFunction D v A y+l y+κ=0}=2^k+2^(k-t) := by
  classical
  let I := tensorRepairIndices D v t
  have hgood (z : I) : tensorPolarRank D v z.val.1=2*t ∧
      ∀ r, 1 ≤ r → r<t → goldMoment D v z.val.1 r=0 :=
    (mem_momentTensors D v t _).mp (Finset.mem_sigma.mp z.property).1
  have hdim : Module.finrank (ZMod 2) D=k+1 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hD, Nat.card_eq_fintype_card, ZMod.card] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hc.symm
  have hbit (z : I) : ∃ κ : ZMod 2,
      Nat.card {y : D // tensorQuadraticFunction D v z.val.1 y+z.val.2 y+κ=0}=2^k+2^(k-t) := by
    have he := BinaryQuadraticData.exists_bit_zeroCount_of_polarRank (tensorQuadraticData D v z.val.1)
      z.val.2 (Finset.mem_sigma.mp z.property).2 (k+1) t (by omega) hdim
      (by rw [tensorQuadraticData_rank]; exact (hgood z).1)
    obtain ⟨κ,hκ,_⟩ := he
    refine ⟨κ,?_⟩
    have heq : k+1-t-1=k-t := by omega
    simpa only [BinaryQuadraticData.zeroCount, tensorQuadraticData, BinaryQuadraticData.toFun,
      BinaryQuadraticData.mk, Nat.add_sub_cancel, heq] using hκ
  choose κ hκ using hbit
  let P : I → B[X] := fun z ↦ repairedLocator D v z.val.1 z.val.2.toAddMonoidHom (κ z) t
  have hP : Function.Injective P := by
    intro z z' he
    have hn (w : I) : repairedPolynomial D v w.val.1 w.val.2.toAddMonoidHom (κ w) ≠ 0 := by
      intro hz
      have hd := (repairedPolynomial_natDegrees D k hD v w.val.1 w.val.2.toAddMonoidHom (κ w)
        t ht0 ht (hgood w).2 (hgood w).1).1
      rw [hz,natDegree_zero] at hd
      have : 0 < (2:ℕ)^k+2^(k-t) := by positivity
      omega
    have hdiv (w : I) := (repairedPolynomial_dvd_locator D k hD v w.val.1 w.val.2.toAddMonoidHom (κ w)
      t ht0 ht (hgood w).2 (hgood w).1 (hκ w)).1
    obtain ⟨hA,hl,_⟩ := repairedLocator_injective_parameters D k hD v x hdual
      z.val.1 z'.val.1 z.val.2.toAddMonoidHom z'.val.2.toAddMonoidHom (κ z) (κ z') t (by omega)
      (hgood z).2 (hgood z').2 (hn z) (hn z') (hdiv z) (hdiv z') he
    have hl' : z.val.2=z'.val.2 := by
      ext y
      exact congrArg (fun l : D →+ ZMod 2 ↦ l y) hl
    apply Subtype.ext
    exact Sigma.ext hA (heq_of_eq hl')
  refine ⟨Finset.univ.image P, ?_, ?_⟩
  · rw [Finset.card_image_iff.mpr hP.injOn, Finset.card_univ, Fintype.card_coe]
    exact card_tensorRepairIndices D v t
  · intro p hp
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨z.val.1, (Finset.mem_sigma.mp z.property).1, z.val.2.toAddMonoidHom, κ z, rfl, hκ z⟩
/-- The complete literal Gold decoding list, with size measured by the actual finite rank-and-moment tensor count. -/
theorem ordinaryList_from_momentTensors (D : AddSubgroup B) [Fintype D]
    (a : B) (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j) = if i=j then 1 else 0)
    (t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1) :
    ordinaryList (affineDomain (additiveDomain D) a) (2^(k-1)) (2^k-2^(k-t))
      ((momentTensors D v t).card*2^(2*t)) := by
  classical
  obtain ⟨ps,hcard,hps⟩ := exists_repairedLocator_family D k hD v x hdual t ht0 ht
  have hprop (z : ps) : (z.val+goldSourcePolynomial D k).degree<2^(k-1) ∧
      2^k-2^(k-t) ≤ Nat.card {x : D // z.val.eval (x : B)=0} := by
    obtain ⟨A,hA,l,κ,he,hzero⟩ := hps z.val z.property
    rw [he]
    obtain ⟨hr,hM⟩ := (mem_momentTensors D v t A).mp hA
    have hp := repairedLocator_properties D k hD v A l κ t ht0 ht hM hr hzero
    refine ⟨?_,hp.2.2.2.1.ge⟩
    apply degree_le_natDegree.trans_lt
    rw [hp.2.2.1]
    exact_mod_cast Nat.sub_lt (by positivity : 0 < (2:ℕ)^(k-1)) (by positivity : 0 < (2:ℕ)^(k-t-1))
  have hlist := ordinaryList_of_locator_family D a (goldSourcePolynomial D k)
    (fun z : ps ↦ z.val) Subtype.val_injective (2^(k-1)) (2^k-2^(k-t))
    (fun z ↦ (hprop z).1) (fun z ↦ (hprop z).2)
  rwa [Fintype.card_coe,hcard] at hlist
/-- A basis supplies the required dual frame on every prescribed binary subgroup, in the paper's domain-size notation. -/
theorem ordinaryList_from_basis_momentTensors (D : AddSubgroup B) [Fintype D]
    (a : B) (d t : ℕ) (hD : Nat.card D=2^d)
    (e : Module.Basis (Fin d) (ZMod 2) D) (ht0 : 2 ≤ t) (ht : 2*t ≤ d) :
    ordinaryList (affineDomain (additiveDomain D) a) (2^d/4) (2^d/2-2^d/2^(t+1))
      ((momentTensors D (basisParameter D e) t).card*2^(2*t)) := by
  have hd : d-1+1=d := by omega
  have he : Nat.card D=2^(d-1+1) := by simpa only [hd] using hD
  have hlist := ordinaryList_from_momentTensors D a (d-1) he (basisParameter D e) e
    (basisParameter_eval D e) t ht0 (by omega)
  have hK : 2^d/4=2^(d-1-1) := by
    change 2^d/2^2=2^(d-1-1)
    rw [Nat.pow_div (by omega : 2 ≤ d) (by decide : 0 < 2)]
    congr 1
  have hN : 2^d/2=2^(d-1) := by
    change 2^d/2^1=2^(d-1)
    rw [Nat.pow_div (by omega : 1 ≤ d) (by decide : 0 < 2)]
  have hT : 2^d/2^(t+1)=2^(d-1-t) := by
    rw [Nat.pow_div (by omega : t+1 ≤ d) (by decide : 0 < 2)]
    congr 1
    omega
  simpa only [hK,hN,hT] using hlist

end BinaryFieldCounterexamples.Gold
