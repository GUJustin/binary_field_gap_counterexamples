/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Longfellow.NonAffineDomain
public import BinaryFieldCounterexamples.Agreement.Interpolation
/-!
# Main theorem: Corollary 5.19 on the actual specified index domains

Section 5.8 defines the queried set as the binary images of `[2K-1,e)`.
The domain cardinality and its embedded affine eleven-space are proved,
rather than assumed. The same domain is proved non-affine and has rate at
most `1/7`. Corollary 5.19's counterexample and probability therefore apply
on the specification's actual coordinates for each of the four circuit
lengths. A final companion uses the literal powers of the specified generator.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
open Longfellow
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 5.8: mapping the actual eleven-space and then translating is the
same coordinate set as translating its native points and mapping them. -/
theorem longfellow_mapped_affine_space
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F]
    (φ : B →+* F) (D : AddSubgroup B) (a : B) :
    affineDomain (additiveDomain (D.map φ.toAddMonoidHom)) (φ a)=
      mappedDomain φ (affineDomain (additiveDomain D) a) := by
  rw [←mappedDomain_additiveDomain]
  simp only [affineDomain,mappedDomain,Finset.image_image,Function.comp_def,map_add]

/-- Corollary 5.19 on the actual Section 5.8 index domain, with no conditional
cardinality or affine-subspace inclusion premise. This also certifies its
non-affineness, exact queried length, and rate at most `1/7`. -/
theorem longfellow_specification_domain
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (φ : B →+* F) (b : Module.Basis (Fin 16) (ZMod 2) B)
    (e : ℕ) (he : e ∈ configuredLengths)
    (hB : Fintype.card B=2^16) (hF : Fintype.card F=2^128) :
    let K := (e+1)/9
    let S := mappedDomain φ (domain b e K)
    S.card=e-2*K+1 ∧
    (K : ℚ)/S.card≤1/7 ∧
    (¬∃ A : AffineSubspace (ZMod 2) F, (A : Set F)=(S : Set F)) ∧
    ∃ f g : S → F, commonAgreementEQ S K f g K ∧ agreementEQ S K g K ∧
      5843376≤(nonzeroBadChallenges S K f g (K+384)).card ∧
      (2 : ℝ)^(-105.522 : ℝ)<
        ((nonzeroBadChallenges S K f g (K+384)).card : ℝ)/(Fintype.card F : ℝ) := by
  obtain ⟨he16,hK,h2K,hlo,hhi,hupper,hconfig⟩ := configured_length_bounds e he
  have hcard : (mappedDomain φ (domain b e ((e+1)/9))).card=e-2*((e+1)/9)+1 := by
    rw [card_mappedDomain,domain_card b e ((e+1)/9) he16 hK h2K]
  dsimp only
  refine ⟨hcard,?_,mapped_domain_not_affine φ b e he,?_⟩
  · rw [card_mappedDomain]
    exact configured_domain_rate_le_seventh b e he
  · let : Fintype (lowSpace b) := Fintype.ofFinite _
    apply longfellow_counterexample_probability φ (lowSpace b) (b ⟨11,by decide⟩)
      (mappedDomain φ (domain b e ((e+1)/9))) ((e+1)/9) hB hF (lowSpace_card b)
    · rw [longfellow_mapped_affine_space]
      exact Finset.image_subset_image
        (central_space_subset_domain b e ((e+1)/9) (by omega) hhi.le)
    · rwa [hcard]

/-- Section 5.8's least-possible common agreement: on the actual queried
coordinate set every pair admits simultaneous strict-degree interpolation
on `K` positions. Corollary 5.19 attains this universal lower bound. -/
theorem longfellow_specification_minimal_common_agreement
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] (φ : B →+* F)
    (b : Module.Basis (Fin 16) (ZMod 2) B) (e : ℕ) (he : e ∈ configuredLengths)
    (f g : mappedDomain φ (domain b e ((e+1)/9)) → F) :
    commonAgreementGE (mappedDomain φ (domain b e ((e+1)/9))) ((e+1)/9) f g ((e+1)/9) := by
  obtain ⟨he16,hK,h2K,hlo,hhi,hupper,hconfig⟩ := configured_length_bounds e he
  have hconf : ((mappedDomain φ (domain b e ((e+1)/9))).card,(e+1)/9) ∈ parameterPairs := by
    rw [card_mappedDomain,domain_card b e ((e+1)/9) he16 hK h2K]
    exact hconfig
  exact commonAgreementGE_of_le_card _ _ f g (configured_parameter_bounds hconf).2.1

namespace Longfellow

/-- Section 5.8's literal specification domain, using powers of its generator
and the integer interval `[2K-1,e)` exactly as printed. -/
noncomputable def powerDomain
    {B : Type*} [Field B] [Algebra (ZMod 2) B] (g : B) (e K : ℕ) : Finset B :=
  (Finset.Ico (2*K-1) e).image (fun j =>
    ∑ i : Fin 16, (if j.testBit i then (1 : ZMod 2) else 0) • g^(i : ℕ))

/-- Section 5.8's injection in the prescribed power basis is exactly the
literal sum of the binary digits times `g^i`; consequently the queried sets coincide. -/
theorem powerDomain_eq_domain
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (g : B) (b : Module.Basis (Fin 16) (ZMod 2) B) (hb : ∀ i, b i=g^(i : ℕ))
    (e K : ℕ) : powerDomain g e K=domain b e K := by
  unfold powerDomain domain
  congr 1
  funext j
  rw [inj_eq_sum]
  simp_rw [hb]

end Longfellow

/-- Corollary 5.19 for the specification's actual generator-power coordinates:
`1,g,...,g^15` is the given binary basis and `S=inj([2K-1,e))`. All domain,
rate, non-affineness and counterexample conclusions are proved together. -/
theorem longfellow_specification_power_basis
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (φ : B →+* F) (g : B) (b : Module.Basis (Fin 16) (ZMod 2) B)
    (hb : ∀ i, b i=g^(i : ℕ)) (e : ℕ) (he : e ∈ configuredLengths)
    (hB : Fintype.card B=2^16) (hF : Fintype.card F=2^128) :
    let K := (e+1)/9
    let S := mappedDomain φ (powerDomain g e K)
    S.card=e-2*K+1 ∧
    (K : ℚ)/S.card≤1/7 ∧
    (¬∃ A : AffineSubspace (ZMod 2) F, (A : Set F)=(S : Set F)) ∧
    ∃ f g : S → F, commonAgreementEQ S K f g K ∧ agreementEQ S K g K ∧
      5843376≤(nonzeroBadChallenges S K f g (K+384)).card ∧
      (2 : ℝ)^(-105.522 : ℝ)<
        ((nonzeroBadChallenges S K f g (K+384)).card : ℝ)/(Fintype.card F : ℝ) := by
  dsimp only
  rw [powerDomain_eq_domain g b hb]
  exact longfellow_specification_domain φ b e he hB hF

end BinaryFieldCounterexamples
