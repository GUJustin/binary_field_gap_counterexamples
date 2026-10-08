/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.GoldAllRates.FiniteTransfer
public import BinaryFieldCounterexamples.Constructions.HigherRateLengthening.FieldBounds
public import BinaryFieldCounterexamples.Constructions.Gold.DenseAsymptoticTheorem
/-!
# Gold lists with padding outside the seed domain

Choose a codimension-`r` subspace of the prescribed additive domain, and use the
dense Gold list there at degree bound one quarter of its size. Multiplication
by the locator of an arbitrary outside padding set raises the degree bound to
`J` and adds exactly the padding size to the guaranteed agreement.

The same list can be translated before separating-pole conversion, so the
finite extension and the exact individual and common agreement conclusions
hold on every translate as well. No balanced padding or concentration bound
is used.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.GoldAllRates
open Polynomial
open HigherRateLengthening
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Finite outside-only Gold padding on every prescribed dense domain and its
translates. The seed threshold is at most half its length, with a vanishing
upper bound on its deficit. The selected list count and extension size use the
same uniform bounds as higher-rate lengthening. -/
theorem gold_outside_padding_finite (c r : ℕ) :
    let theta : ℝ := min (1/4) (1/((c+r : ℕ)+1))
    let alpha : ℝ := theta*(1-2*theta)
    ∃ C : ℝ, 0 < C ∧ ∃ d0 : ℕ, ∀ d : ℕ, d0+r ≤ d → 1 ≤ d → c ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [CharP B 2],
      Fintype.card B = 2^(d+c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2^d →
    let N := 2^d
    let M := 2^(d-r)
    ∀ J L : ℕ, M/4 ≤ J → J ≤ N → J-M/4 ≤ N-M → L ≤ 2^(d^2) →
      (L : ℝ) ≤ (2 : ℝ)^(alpha*(d-r : ℕ)^2-C*(d-r : ℕ)) →
    ∃ T0 : ℕ, (T0 : ℝ)/M ≤ 1/2 ∧ 1/2-(T0 : ℝ)/M ≤ C*(M : ℝ)^(-theta) ∧
    ∀ a : B,
      ordinaryList (affineDomain (additiveDomain D) a) J (J-M/4+T0) L ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ phi : B →+* F,
      ∃ f g : mappedDomain phi (affineDomain (additiveDomain D) a) → F,
        agreementEQ (mappedDomain phi (affineDomain (additiveDomain D) a)) J f J ∧
        agreementEQ (mappedDomain phi (affineDomain (additiveDomain D) a)) J g J ∧
        commonAgreementEQ (mappedDomain phi (affineDomain (additiveDomain D) a)) J f g J ∧
        L ≤ (nonzeroBadChallenges
          (mappedDomain phi (affineDomain (additiveDomain D) a)) J f g (J-M/4+T0)).card ∧
        (Fintype.card F : ℝ) ≤ (N : ℝ)^((32/Real.log 2)*Real.log N) := by
  dsimp only
  obtain ⟨A,C,p,hA,hC,hp,d0,hseed⟩ := Gold.denseGold_asymptotic (c+r)
  refine ⟨C,hC,d0,?_⟩
  intro d hd hd1 hcd B fieldB finiteB charB hB D hD J L hK hJ hw hLupper hLseed

  -- Restrict the dense Gold construction to a subspace of the supplied domain.
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  obtain ⟨H,hHD,hH⟩ := exists_binary_subspace_card_eq D (2^(d-r)) ⟨d-r,rfl⟩ (by
    rw [←card_additiveDomain,hD]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  have hcardH : (additiveDomain H).card = 2^(d-r) := by
    rw [card_additiveDomain,hH]
  have hsub : additiveDomain H ⊆ additiveDomain D := by
    intro x hx
    exact (mem_additiveDomain D x).mpr (hHD ((mem_additiveDomain H x).mp hx))
  have hdiff : (additiveDomain D \ additiveDomain H).card = 2^d-2^(d-r) := by
    rw [Finset.card_sdiff_of_subset hsub,hD,hcardH]
  have hB' : Fintype.card B = 2^((d-r)+(c+r)) := by
    rw [hB]
    congr 1
    omega
  obtain ⟨T0,L0,hTlow,hThigh,hcount,hlist,hrest⟩ :=
    hseed (d-r) (by omega) B hB' H hcardH
  obtain ⟨w,E,hLE,hE⟩ := hlist
  have hLL : L ≤ E.card := by
    have hLL0 : L ≤ L0 := by exact_mod_cast hLseed.trans hcount
    exact hLL0.trans hLE
  have hhalf : (T0 : ℝ)/(2^(d-r) : ℕ) ≤ 1/2 := by
    have hpos : 0 ≤ A * ((2^(d-r) : ℕ) : ℝ)^(-(min (1/4) (1/((c+r : ℕ)+1)) : ℝ)) :=
      mul_nonneg hA.le (Real.rpow_nonneg (by positivity) _)
    linarith

  -- Any outside set of the required size suffices; translate the resulting list.
  have hlen := finite_list_outside_padding (additiveDomain D) (additiveDomain H)
    hsub w E (2^(d-r)/4) T0 (J-2^(d-r)/4) L hE hLL (by simpa only [hdiff] using hw)
  have hdegree : J-2^(d-r)/4+2^(d-r)/4 = J := Nat.sub_add_cancel hK
  rw [hdegree] at hlen
  refine ⟨T0,hhalf,hThigh,?_⟩
  intro a
  have htranslate := ordinaryList_affineDomain (additiveDomain D) a J _ L hlen
  refine ⟨htranslate,?_⟩

  -- Separate every selected polynomial over a genuine finite extension, then
  -- make both individual agreements and their common agreement exactly J.
  obtain ⟨w1,E1,hLE1,hE1⟩ := htranslate
  obtain ⟨I,hIE,hI⟩ := Finset.exists_subset_card_eq hLE1
  obtain ⟨F,fieldF,finiteF,phi,hcardF,f,g,hf,hg,hfg,hbad⟩ :=
    DenseConstruction.ordinary_family_extension_pair B
      (affineDomain (additiveDomain D) a) w1 I J _ (4*d+4) (by omega)
      (fun p hp => hE1 p (hIE hp))
      (by simpa only [card_affineDomain,hD] using hJ)
      (by rw [card_affineDomain,hD,hI,hB]; exact pole_field_capacity c d J L hd1 hJ hLupper)
  let := fieldF
  let := finiteF
  refine ⟨F,fieldF,finiteF,phi,f,g,hf,hg,hfg,?_,?_⟩
  · simpa only [hI] using hbad
  · apply final_field_real_bound d
    rw [hcardF,hB]
    exact final_field_binary_bound c d hd1 hcd

end BinaryFieldCounterexamples.GoldAllRates
