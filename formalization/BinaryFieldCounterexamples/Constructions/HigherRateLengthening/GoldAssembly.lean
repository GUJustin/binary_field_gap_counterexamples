/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.HigherRateLengthening.FiniteTransfer
public import BinaryFieldCounterexamples.Constructions.HigherRateLengthening.FieldBounds
public import BinaryFieldCounterexamples.Constructions.Gold.DenseAsymptoticTheorem
/-!
# Gold lists on a smaller subspace and higher-rate lengthening

The prescribed binary domain contains a subspace of any smaller binary
dimension. Apply the proved dense Gold theorem there, select the desired
number of explaining polynomials, balance additional degree within that subspace,
and lengthen to the original domain. The decoding-list-to-pair construction keeps
every selected challenge over an explicit quasipolynomial-size containing field.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.HigherRateLengthening
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The complete finite construction on every prescribed dense domain. The
remaining assumptions are scalar bounds for the selected count and degree;
all lists, fields, and received pairs are constructed in the conclusion. -/
theorem gold_lengthening_finite (c r : ℕ) :
    let theta : ℝ := min (1/4) (1/((c+r : ℕ)+1))
    let alpha : ℝ := theta*(1-2*theta)
    ∃ C : ℝ, 0 < C ∧ ∃ d0 : ℕ, ∀ d : ℕ, d0+r ≤ d → 1 ≤ d → c ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [CharP B 2],
    Fintype.card B = 2^(d+c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2^d →
    let N := 2^d
    let M := 2^(d-r)
    let K0 := N-M+M/4
    ∀ J L : ℕ, K0 ≤ J → J ≤ N → J-K0 ≤ M → L ≤ 2^(d^2) →
      (L : ℝ) ≤ (2 : ℝ)^(alpha*(d-r : ℕ)^2-C*(d-r : ℕ)) →
    ∃ T0 : ℕ, 1/2-(T0 : ℝ)/M ≤ C*(M : ℝ)^(-theta) ∧
    let a := J-K0
    let U : ℝ := (N-M : ℕ)+a+T0-
      ((a : ℝ)*T0/M+Real.sqrt (((a : ℝ)/2)*Real.log (2*L)))
    ordinaryList (additiveDomain D) J ⌊U⌋₊ L ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ phi : B →+* F, ∃ f g : mappedDomain phi (additiveDomain D) → F,
        agreementEQ (mappedDomain phi (additiveDomain D)) J f J ∧
        agreementEQ (mappedDomain phi (additiveDomain D)) J g J ∧
        commonAgreementEQ (mappedDomain phi (additiveDomain D)) J f g J ∧
        L ≤ (nonzeroBadChallenges (mappedDomain phi (additiveDomain D)) J f g ⌊U⌋₊).card ∧
        (Fintype.card F : ℝ) ≤ (N : ℝ)^((32/Real.log 2)*Real.log N) := by
  dsimp only
  obtain ⟨A,C,p,hA,hC,hp,d0,hseed⟩ := Gold.denseGold_asymptotic (c+r)
  refine ⟨C,hC,d0,?_⟩
  intro d hd hd1 hcd B fieldB finiteB charB hB D hD J L hK hJ ha hLupper hLseed
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
    have hLL0 : L ≤ L0 := by
      exact_mod_cast hLseed.trans hcount
    exact hLL0.trans hLE
  have hlen := finite_balanced_lengthening (additiveDomain D) (additiveDomain H)
    hsub w E (2^(d-r)/4) (J-(2^d-2^(d-r)+2^(d-r)/4)) T0 L hE hLL
    (by simpa only [hcardH] using ha)
  have hdegree : (2^d-2^(d-r)) +
      (2^(d-r)/4 + (J-(2^d-2^(d-r)+2^(d-r)/4))) = J := by omega
  dsimp only at hlen
  rw [hdiff,hcardH,hdegree] at hlen
  refine ⟨T0,hThigh,hlen,?_⟩
  obtain ⟨w1,E1,hLE1,hE1⟩ := hlen
  obtain ⟨I,hIE,hI⟩ := Finset.exists_subset_card_eq hLE1
  obtain ⟨F,fieldF,finiteF,phi,hcardF,f,g,hf,hg,hfg,hbad⟩ :=
    DenseConstruction.ordinary_family_extension_pair B (additiveDomain D) w1 I J _
      (4*d+4) (by omega) (fun p hp => hE1 p (hIE hp))
      (by simpa only [hD] using hJ)
      (by rw [hD,hI,hB]; exact pole_field_capacity c d J L hd1 hJ hLupper)
  let := fieldF
  let := finiteF
  refine ⟨F,fieldF,finiteF,phi,f,g,hf,hg,hfg,?_,?_⟩
  · simpa only [hI] using hbad
  · apply final_field_real_bound d
    rw [hcardF,hB]
    exact final_field_binary_bound c d hd1 hcd

end BinaryFieldCounterexamples.HigherRateLengthening
