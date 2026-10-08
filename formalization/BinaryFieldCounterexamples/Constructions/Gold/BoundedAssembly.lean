/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Assembly
/-!
# Gold conclusions from a lower bound on the actual population

Select exactly `L` distinct locators from the proved tensor-and-repair family.
All polynomial witnesses and guarantees on the inputs are inherited by the subset,
and collision pooling therefore yields the exact energy expression with `L`.
This avoids any additional monotonicity condition on the energy denominator.
The empty-family case is included, and the prescribed affine domain is unchanged.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial

/-- An exact-size subfamily gives both collision bounds at one pole, with no loss at zero and the sharper witness degree. -/
theorem gold_counting_from_tensor_lower_bound_sharp
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B) (d t : ℕ)
    (hD : Nat.card D=2^d) (e : Module.Basis (Fin d) (ZMod 2) D)
    (ht0 : 2 ≤ t) (ht : 2*t ≤ d) (hq : 2^d<Fintype.card F)
    (L : ℕ) (hL : L≤(momentTensors D (basisParameter D e) t).card*2^(2*t)) :
    let N : ℕ := 2^d
    let T : ℕ := N/2-N/2^(t+1)
    let δ : ℕ := N/2^(2*t)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    let q : ℕ := Fintype.card F
    let Z : ℕ := max (L-(δ*L.choose 2)/(q-N)) ⌈(L : ℚ)*((q : ℚ)-(N : ℚ))/
      ((q : ℚ)-(N : ℚ)+(δ : ℚ)*((L : ℚ)-1))⌉₊
    ordinaryList (affineDomain (additiveDomain D) a) (N/4) T L ∧
      ∃ f g : E → F,
        commonAgreementEQ E (N/4) f g (N/4) ∧
        agreementEQ E (N/4) g (N/4) ∧
        agreementLE E (N/4) f (3*N/8-1) ∧
        Z ≤ (nonzeroBadChallenges E (N/4) f g T).card ∧
        Z ≤ (nonzeroBadChallenges E (T/2) f g T).card := by
  classical
  dsimp only
  have hlist : ordinaryList (affineDomain (additiveDomain D) a) (2^d/4) (2^d/2-2^d/2^(t+1)) L := by
    obtain ⟨w,ps,hcard,hps⟩ := ordinaryList_from_basis_momentTensors D a d t hD e ht0 ht
    exact ⟨w,ps,hL.trans hcard,hps⟩
  refine ⟨hlist,?_⟩
  let : Fintype (D.map φ.toAddMonoidHom) := Fintype.ofFinite _
  have hd : d-1+1=d := by omega
  have hcD : Nat.card D=2^(d-1+1) := by simpa only [hd] using hD
  obtain ⟨allLocators,hallCard,hall⟩ := exists_repairedLocator_family D (d-1) hcD (basisParameter D e) e
    (basisParameter_eval D e) t ht0 (by omega)
  obtain ⟨ps,hsub,hcard⟩ := Finset.exists_subset_card_eq (show L≤allLocators.card by rw [hallCard]; exact hL)
  have hps := fun P (hP : P ∈ ps) => hall P (hsub hP)
  obtain ⟨β,hβ,hfirst,hsecond⟩ := exists_exterior_locatorValues_bounds φ D (d-1) hcD (basisParameter D e) t ht0 (by omega)
    ps hps (by simpa only [hd] using hq)
  have hproperties (P : B[X]) (hP : P ∈ ps) :
      (P+goldSourcePolynomial D (d-1)).natDegree ≤ 2^(d-1-1)-2^(d-1-t-1) ∧
        2^(d-1)-2^(d-1-t) ≤ Nat.card {x : D // P.eval (x : B)=0} := by
    obtain ⟨A,hA,l,κ,rfl,hzero⟩ := hps P hP
    obtain ⟨hr,hM⟩ := (mem_momentTensors D (basisParameter D e) t A).mp hA
    have hp := repairedLocator_properties D (d-1) hcD (basisParameter D e) A l κ t ht0 (by omega) hM hr hzero
    exact ⟨hp.2.2.1.le,hp.2.2.2.1.ge⟩
  obtain ⟨f,g,hcommon,hg,hf,hbad,hstrong⟩ := goldPair_of_locator_pool_no_loss φ D a (d-1) t ht0 (by omega) hcD ps hproperties β hβ
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
  · apply le_trans (max_le ?_ ?_) hbad
    · simpa only [hcard,hd,← hδ] using hfirst
    · simpa only [hcard,hd,← hδ] using hsecond
  · apply le_trans (max_le ?_ ?_) hstrong
    · simpa only [hcard,hd,← hδ] using hfirst
    · simpa only [hcard,hd,← hδ] using hsecond
/-- Any lower bound on the actual tensor-and-repair population gives the exact Gold list and pair bounds by selecting that many locators. -/
theorem gold_counting_from_tensor_lower_bound
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B) (d t : ℕ)
    (hD : Nat.card D=2^d) (e : Module.Basis (Fin d) (ZMod 2) D)
    (ht0 : 2 ≤ t) (ht : 2*t ≤ d) (hq : 2^d<Fintype.card F)
    (L : ℕ) (hL : L≤(momentTensors D (basisParameter D e) t).card*2^(2*t)) :
    let N : ℕ := 2^d
    let T : ℕ := N/2-N/2^(t+1)
    let δ : ℕ := N/2^(2*t)
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    let q : ℕ := Fintype.card F
    let Z : ℕ := ⌈(L : ℚ)*((q : ℚ)-(N : ℚ))/
      ((q : ℚ)-(N : ℚ)+(δ : ℚ)*((L : ℚ)-1))⌉₊-1
    ordinaryList (affineDomain (additiveDomain D) a) (N/4) T L ∧
      ∃ f g : E → F,
        commonAgreementEQ E (N/4) f g (N/4) ∧
        agreementEQ E (N/4) g (N/4) ∧
        agreementLE E (N/4) f (3*N/8-1) ∧
        Z ≤ (nonzeroBadChallenges E (N/4) f g T).card ∧
        Z ≤ (nonzeroBadChallenges E (T/2) f g T).card := by
  obtain ⟨hlist,f,g,hcommon,hg,hf,hbad,hstrong⟩ :=
    gold_counting_from_tensor_lower_bound_sharp φ D a d t hD e ht0 ht hq L hL
  exact ⟨hlist,f,g,hcommon,hg,hf,
    (Nat.sub_le _ _).trans ((le_max_right _ _).trans hbad),
    (Nat.sub_le _ _).trans ((le_max_right _ _).trans hstrong)⟩

end BinaryFieldCounterexamples.Gold
