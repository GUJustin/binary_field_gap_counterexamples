/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.ExactChallengeSets
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.CanonicalSourceAgreement
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.SharpSource
/-!
# Main theorem: exact quadratic exceptional population on prescribed binary domains

Paper statement: [Theorem 4.1, p. 28](../../../binary-field-counterexamples.pdf#page=28).
For every binary additive domain D of size N=16K, with K≥2 a power of two,
and every proper finite extension, one pair has exact common agreement2K−1,
first-input agreement at most2K, and second-input agreement exactly2K−1.
The same exceptional set occurs at every integer threshold2K+1≤T≤4K−1.
Its cardinality is exactly (N−1)(N−2)/6, it excludes zero, each of its challenges
has maximum agreement exactly4K−1, and no challenge reaches4K agreements.

The companion for extension degree at least three gives exact individual
agreement2K−1 for both inputs while keeping the same complete exceptional
profile. The extension-degree condition is expressed by |B|^3≤|F|. All message
polynomials have degree strictly below K; counts are of distinct challenges
for one fixed pair on the literal mapped domain. The earlier lower-bound
endpoints remain unchanged.

Coordinate projection, polynomial elimination and the literal quartic locator
composition identify every explaining polynomial above2K with a subgroup locator. The
actual explaining identity gives precisely its nonzero roots as agreement
points. The existing challenge injection and exact binary subspace population give
the exact count. A single shift of the first input preserves the full profile and
supplies the individual guarantees.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open QuadraticConstruction
/-- The complete proper-extension exceptional profile, on every prescribed
domain. The pair and its one exceptional set precede every threshold and challenge. -/
theorem quadratic_near_johnson_exact
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hproper : ¬Function.Surjective φ)
    (D : AddSubgroup B) (K : ℕ) (hK : 2≤K)
    (hpow : ∃ k : ℕ, K=2^k) (hD : (additiveDomain D).card=16*K) :
    let E := mappedDomain φ (additiveDomain D)
    ∃ f g : E → F, ∃ I : Finset F,
      commonAgreementEQ E K f g (2*K-1) ∧
      agreementLE E K f (2*K) ∧ agreementEQ E K g (2*K-1) ∧
      I.card=(16*K-1)*(16*K-2)/6 ∧ 0∉I ∧
      (∀ T : ℕ, 2*K+1≤T → T≤4*K-1 → badChallenges E K f g T=I) ∧
      (∀ z∈I, agreementEQ E K (fun x=>f x+z*g x) (4*K-1)) ∧
      badChallenges E K f g (4*K)=∅ := by
  classical
  let : Algebra B F := φ.toAlgebra
  -- One exterior coordinate and one fixed shift of the first input serve all thresholds.
  have hex : ∃ θ:F, θ∉Set.range φ := by
    simpa only [Function.Surjective,not_forall,Set.mem_range] using hproper
  obtain ⟨θ,hθ⟩ := hex
  obtain ⟨s,hs⟩ := exists_quadratic_source_shift D K (by omega) hpow hD θ hθ
  let E := mappedDomain φ (additiveDomain D)
  let f : E → F := fun x=>firstWord K θ x+φ s*secondWord K (x:F)
  let g : E → F := fun x=>secondWord K (x:F)
  have hf : agreementLE E K f (2*K) := hs
  obtain ⟨hc,hg⟩ := canonical_quadratic_source_agreement φ D K hK hpow hD θ (φ s)

  -- The exact classified set survives that same shift of the first input.
  obtain ⟨I,hI,hT,hmax,hempty⟩ := quadratic_shifted_exact_challenges φ θ hθ D K hK hpow hD (φ s)
  refine ⟨f,g,I,hc,hf,hg,hI,?_,hT,hmax,hempty⟩
  intro hz
  have hbad : 0∈badChallenges E K f g (4*K-1) := by
    rw [hT (4*K-1) (by omega) le_rfl]
    exact hz
  obtain ⟨p,hp,hcount⟩ := (mem_badChallenges E K f g (4*K-1) 0).mp hbad
  simp only [zero_mul,add_zero] at hcount
  change 4*K-1≤agreementCount E f p at hcount
  have hu := hf p hp
  omega

/-- In extension degree at least three, both individual bounds are
sharp, with the same exact count, common agreement and full threshold profile. -/
theorem quadratic_near_johnson_both_far_exact
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hext : Fintype.card B^3≤Fintype.card F)
    (D : AddSubgroup B) (K : ℕ) (hK : 2≤K)
    (hpow : ∃ k : ℕ, K=2^k) (hD : (additiveDomain D).card=16*K) :
    let E := mappedDomain φ (additiveDomain D)
    ∃ f g : E → F, ∃ I : Finset F,
      commonAgreementEQ E K f g (2*K-1) ∧
      agreementEQ E K f (2*K-1) ∧ agreementEQ E K g (2*K-1) ∧
      I.card=(16*K-1)*(16*K-2)/6 ∧ 0∉I ∧
      (∀ T : ℕ, 2*K+1≤T → T≤4*K-1 → badChallenges E K f g T=I) ∧
      (∀ z∈I, agreementEQ E K (fun x=>f x+z*g x) (4*K-1)) ∧
      badChallenges E K f g (4*K)=∅ := by
  classical
  let : Algebra B F := φ.toAlgebra
  -- A third coordinate supplies the sharp first-input bound.
  obtain ⟨θ,s,hθ,l,hl1,hlθ,hls⟩ := exists_quadratic_sharp_coordinates (B:=B) hext
  let E := mappedDomain φ (additiveDomain D)
  let f : E → F := fun x=>firstWord K θ x+s*secondWord K (x:F)
  let g : E → F := fun x=>secondWord K (x:F)
  have hf : agreementLE E K f (2*K-1) :=
    quadratic_source_agreementLE_of_projection (additiveDomain D) K (by omega) θ s l hl1 hlθ hls
  obtain ⟨hc,hg⟩ := canonical_quadratic_source_agreement φ D K hK hpow hD θ s

  -- The same shifted line has the full classified exceptional profile.
  obtain ⟨I,hI,hT,hmax,hempty⟩ := quadratic_shifted_exact_challenges φ θ hθ D K hK hpow hD s
  refine ⟨f,g,I,hc,⟨agreementGE_left_of_common E K f g _ hc.1,hf⟩,hg,hI,?_,hT,hmax,hempty⟩
  intro hz
  have hbad : 0∈badChallenges E K f g (4*K-1) := by
    rw [hT (4*K-1) (by omega) le_rfl]
    exact hz
  obtain ⟨p,hp,hcount⟩ := (mem_badChallenges E K f g (4*K-1) 0).mp hbad
  simp only [zero_mul,add_zero] at hcount
  change 4*K-1≤agreementCount E f p at hcount
  have hu := hf p hp
  omega
end BinaryFieldCounterexamples
