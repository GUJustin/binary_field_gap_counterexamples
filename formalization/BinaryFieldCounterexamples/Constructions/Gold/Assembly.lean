/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.PairWitnesses
public import BinaryFieldCounterexamples.Constructions.Gold.Collisions
/-!
# Gold counting conclusions from the actual tensor population

The finite Gold locator family is pooled over every point outside the prescribed
additive domain. The collision bound gives precisely the rational ceiling used
in the paper, including the empty-family case. Affine transport and the pole
construction supply both the decoding list and the pair's first-input, common
agreement, and distinct nonzero challenge guarantees on the prescribed domain.

The population parameter remains the cardinality of the literal moment-constrained
rank-`2t` tensor set times its exact repair count. The quantitative rank-population
lower bound is a separate mathematical input still needed for the headline.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
/-- The natural collision quotient is exactly the paper's rational ceiling, including an empty family. -/
theorem gold_energy_ceiling (M q N δ : ℕ) (hq : N<q) :
    natCeilDiv (M*(q-N)) ((q-N)+δ*(M-1)) =
      ⌈(M : ℚ)*((q : ℚ)-(N : ℚ))/((q : ℚ)-(N : ℚ)+(δ : ℚ)*((M : ℚ)-1))⌉₊ := by
  by_cases hM : M=0
  · subst M
    simp [natCeilDiv]
  have hden : 0 < (q-N)+δ*(M-1) := by omega
  rw [natCeilDiv_eq_rat_ceil _ _ hden]
  congr 1
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_sub hq.le,Nat.cast_sub (show 1 ≤ M by omega),Nat.cast_one]
/-- Collision pooling over the entire actual exterior gives the exact energy bound for a finite Gold locator family. -/
theorem exists_exterior_locatorValues_energy
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1)
    (ps : Finset B[X])
    (hps : ∀ p ∈ ps, ∃ A ∈ momentTensors D v t, ∃ l : D →+ ZMod 2, ∃ κ : ZMod 2,
      p=repairedLocator D v A l κ t ∧
        Nat.card {y : D // tensorQuadraticFunction D v A y+l y+κ=0}=2^k+2^(k-t))
    (hq : 2^(k+1)<Fintype.card F) :
    ∃ β : F, β ∉ D.map φ.toAddMonoidHom ∧
      ⌈(ps.card : ℚ)*((Fintype.card F : ℚ)-(2^(k+1) : ℕ))/
        ((Fintype.card F : ℚ)-(2^(k+1) : ℕ)+(2^(k+1-2*t) : ℕ)*((ps.card : ℚ)-1))⌉₊ ≤
        (locatorValues φ ps β).card := by
  classical
  let D' := D.map φ.toAddMonoidHom
  let : Fintype D' := Fintype.ofFinite D'
  let E : Finset F := Finset.univ \ additiveDomain D'
  have hEcard : E.card=Fintype.card F-2^(k+1) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,card_additiveDomain,
      natCard_map_addSubgroup,hD]
  have hE : E.Nonempty := Finset.card_pos.mp (by rw [hEcard]; omega)
  have hext (β : F) (hβ : β ∈ E) : ((subspacePolynomial D).map φ).eval β ≠ 0 := by
    have hnot : β ∉ D' := by simpa only [E,Finset.mem_sdiff,Finset.mem_univ,true_and,mem_additiveDomain] using hβ
    rw [map_subspacePolynomial φ D]
    intro hz
    exact hnot ((subspacePolynomial_eval_eq_zero_iff (D.map φ.toAddMonoidHom) β).mp hz)
  obtain ⟨β,hβ,hpool⟩ := exists_exterior_parameter_repairedLocator_image_bound φ φ.injective D k hD v t ht0 ht ps hps E hE hext
  refine ⟨β,?_,?_⟩
  · simpa only [E,Finset.mem_sdiff,Finset.mem_univ,true_and,mem_additiveDomain] using hβ
  · rw [hEcard,gold_energy_ceiling ps.card (Fintype.card F) (2^(k+1)) (2^(k+1-2*t)) hq] at hpool
    exact hpool
/-- Simultaneous collision-subtraction and energy bounds over the full exterior. -/
theorem exists_exterior_locatorValues_bounds
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D=2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1)
    (ps : Finset B[X])
    (hps : ∀ p ∈ ps, ∃ A ∈ momentTensors D v t, ∃ l : D →+ ZMod 2, ∃ κ : ZMod 2,
      p=repairedLocator D v A l κ t ∧
        Nat.card {y : D // tensorQuadraticFunction D v A y+l y+κ=0}=2^k+2^(k-t))
    (hq : 2^(k+1)<Fintype.card F) :
    ∃ β : F, β ∉ D.map φ.toAddMonoidHom ∧
      ps.card - (2^(k+1-2*t)*ps.card.choose 2)/(Fintype.card F-2^(k+1)) ≤
        (locatorValues φ ps β).card ∧
      ⌈(ps.card : ℚ)*((Fintype.card F : ℚ)-(2^(k+1) : ℕ))/
        ((Fintype.card F : ℚ)-(2^(k+1) : ℕ)+(2^(k+1-2*t) : ℕ)*((ps.card : ℚ)-1))⌉₊ ≤
        (locatorValues φ ps β).card := by
  classical
  let D' := D.map φ.toAddMonoidHom
  let : Fintype D' := Fintype.ofFinite D'
  let E : Finset F := Finset.univ \ additiveDomain D'
  have hEcard : E.card=Fintype.card F-2^(k+1) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,card_additiveDomain,
      natCard_map_addSubgroup,hD]
  have hE : E.Nonempty := Finset.card_pos.mp (by rw [hEcard]; omega)
  have hext (β : F) (hβ : β ∈ E) : ((subspacePolynomial D).map φ).eval β ≠ 0 := by
    have hnot : β ∉ D' := by simpa only [E,Finset.mem_sdiff,Finset.mem_univ,true_and,mem_additiveDomain] using hβ
    rw [map_subspacePolynomial φ D]
    intro hz
    exact hnot ((subspacePolynomial_eval_eq_zero_iff (D.map φ.toAddMonoidHom) β).mp hz)
  obtain ⟨β,hβ,hfirst,hpool⟩ := exists_exterior_parameter_repairedLocator_image_bounds φ φ.injective D k hD v t ht0 ht ps hps E hE hext
  refine ⟨β,?_,?_,?_⟩
  · simpa only [E,Finset.mem_sdiff,Finset.mem_univ,true_and,mem_additiveDomain] using hβ
  · simpa only [hEcard,locatorValues] using hfirst
  · rw [hEcard,gold_energy_ceiling ps.card (Fintype.card F) (2^(k+1)) (2^(k+1-2*t)) hq] at hpool
    exact hpool
/-- The full Gold list-decoding and received-pair conclusions, parameterized by the actual finite rank-and-moment tensor population. -/
theorem gold_counting_from_actual_tensors
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B) (d t : ℕ)
    (hD : Nat.card D=2^d) (e : Module.Basis (Fin d) (ZMod 2) D)
    (ht0 : 2 ≤ t) (ht : 2*t ≤ d) (hq : 2^d<Fintype.card F) :
    let N : ℕ := 2^d
    let M : ℕ := (momentTensors D (basisParameter D e) t).card*2^(2*t)
    let T : ℕ := N/2-N/2^(t+1)
    let δ : ℕ := N/2^(2*t)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    let q : ℕ := Fintype.card F
    let Z : ℕ := ⌈(M : ℚ)*((q : ℚ)-(N : ℚ))/
      ((q : ℚ)-(N : ℚ)+(δ : ℚ)*((M : ℚ)-1))⌉₊-1
    ordinaryList (affineDomain (additiveDomain D) a) (N/4) T M ∧
      ∃ f g : E → F,
        commonAgreementEQ E (N/4) f g (N/4) ∧
        agreementEQ E (N/4) g (N/4) ∧
        agreementLE E (N/4) f (3*N/8-1) ∧
        Z ≤ (nonzeroBadChallenges E (N/4) f g T).card ∧
        Z ≤ (nonzeroBadChallenges E (T/2) f g T).card := by
  classical
  dsimp only
  refine ⟨ordinaryList_from_basis_momentTensors D a d t hD e ht0 ht,?_⟩
  let : Fintype (D.map φ.toAddMonoidHom) := Fintype.ofFinite _
  have hd : d-1+1=d := by omega
  have hcD : Nat.card D=2^(d-1+1) := by simpa only [hd] using hD
  obtain ⟨ps,hcard,hps⟩ := exists_repairedLocator_family D (d-1) hcD (basisParameter D e) e
    (basisParameter_eval D e) t ht0 (by omega)
  obtain ⟨β,hβ,hpool⟩ := exists_exterior_locatorValues_energy φ D (d-1) hcD (basisParameter D e) t ht0 (by omega)
    ps hps (by simpa only [hd] using hq)
  have hproperties (P : B[X]) (hP : P ∈ ps) :
      (P+goldSourcePolynomial D (d-1)).natDegree ≤ 2^(d-1-1)-2^(d-1-t-1) ∧
        2^(d-1)-2^(d-1-t) ≤ Nat.card {x : D // P.eval (x : B)=0} := by
    obtain ⟨A,hA,l,κ,rfl,hzero⟩ := hps P hP
    obtain ⟨hr,hM⟩ := (mem_momentTensors D (basisParameter D e) t A).mp hA
    have hp := repairedLocator_properties D (d-1) hcD (basisParameter D e) A l κ t ht0 (by omega) hM hr hzero
    exact ⟨hp.2.2.1.le,hp.2.2.2.1.ge⟩
  obtain ⟨f,g,hcommon,hg,hf,hbad,hstrong⟩ := goldPair_of_locator_pool φ D a (d-1) t ht0 (by omega) hcD ps hproperties β hβ
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
  have hδ : 2^d/2^(2*t)=2^(d-2*t) := by
    rw [Nat.pow_div ht (by decide : 0 < 2)]
  rw [hK,hN,hT]
  refine ⟨f,g,hcommon,hg,?_,?_,?_⟩
  · simpa only [hd] using hf
  · apply le_trans (Nat.sub_le_sub_right ?_ 1) hbad
    simpa only [hcard,hd,← hδ] using hpool
  · apply le_trans (Nat.sub_le_sub_right ?_ 1) hstrong
    simpa only [hcard,hd,← hδ] using hpool
end BinaryFieldCounterexamples.Gold
