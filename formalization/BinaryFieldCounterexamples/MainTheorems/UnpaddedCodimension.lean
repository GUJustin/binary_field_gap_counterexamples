/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.AllRates.ExtensionSeed
public import BinaryFieldCounterexamples.Constructions.AllRates.UnpaddedSources
public import BinaryFieldCounterexamples.Constructions.AllRates.UnpaddedFamily

/-!
# Main theorem: Exact finite counts before additive-domain padding

Paper statements: [Lemma 4.3, p. 31](../../../binary-field-counterexamples.pdf#page=31)
and [Corollary 4.4, p. 32](../../../binary-field-counterexamples.pdf#page=32).
These results extract the unpadded construction in the section on every fixed
rate. Let the supplied binary additive domain have
size `N = 2^(m+s)`, where `2 ≤ s ≤ m`, and let the supplied extension have
degree at least `s+1`. At strict message length `K=N/2^(s+2)` there is
one pair whose two individual agreements and common agreement all equal
`N/2^(s+1)-1`, and with at least `[m+s choose s]_2` distinct nonzero exceptional
challenges at threshold `N/2^s-1`.

The statement quantifies over the domain and fields before producing the
pair. Counts concern challenges, not subspaces or polynomial witnesses.
The exact lower bound on the individual agreements uses simultaneous Frobenius
remainders; ordinary interpolation alone is insufficient at this lower message length.

The cubic specialization has rate `1/32`, exact individual/common agreement
`N/16-1`, and threshold `N/8-1`, for every `d≥6` and extension degree at
least four. Its full count is `(N-1)(N-2)(N-4)/168`.

All proofs are complete. Dependencies are the concrete locator cancellation,
independent extension coordinates, the full Gaussian subspace count, and
strict-degree witnesses for the inputs. Lemma 4.3 extracts the formerly unlabelled
finite seed from the all-rates proof; Corollary 4.4 specializes it to cubic
counts without introducing an additional construction.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial AllRatesConstruction

/-- The finite collision-averaged construction needs no proper subfield. Its
count includes zero, while the second input and common agreement are exact. -/
theorem unpadded_codimension_collision_counterexample
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (m s : ℕ) (hs : 2 ≤ s) (hm : s ≤ m)
    (hD : Nat.card D = 2^(m+s)) :
    let E := additiveDomain D
    let M := gaussianBinomial 2 (m+s) s
    let q := Fintype.card F
    ∃ f g : E → F,
      agreementEQ E (2^(m-2)) g (2^(m-1)-1) ∧
      commonAgreementEQ E (2^(m-2)) f g (2^(m-1)-1) ∧
      ⌈((q*M : ℕ) : ℚ) / (q+M-1 : ℕ)⌉₊ ≤
        (badChallenges E (2^(m-2)) f g (2^m-1)).card := by
  classical
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  dsimp only
  obtain ⟨I,hIc,hI⟩ := exists_binary_full_subgroup_family D m s hD
  obtain ⟨θ,hθ⟩ := exists_finite_seed_parameter D m s hs hm hD I hI
  let E := additiveDomain D
  let params := finiteCancellationParameterExtension s θ
  let R := 2^(m-1)-1
  let f : E → F := fun x ↦ (cancellationSource m s params).eval (x:F)
  let g : E → F := fun x ↦ (x:F)^R
  have hdim : 2^(m-2) ≤ R := by
    have he : 2^(m-1) = (2:ℕ)^(m-2)*2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hp : 0 < (2:ℕ)^(m-2) := by positivity
    dsimp [R]
    rw [he]
    omega
  have hg : agreementLE E (2^(m-2)) g R := by
    have hd : ((2^(m-2):ℕ) : WithBot ℕ) ≤ (X^R : F[X]).degree := by
      rw [degree_X_pow]
      exact_mod_cast hdim
    simpa [g] using agreementLE_polynomial E (2^(m-2)) (X^R : F[X]) hd
  have hsmall : 2^(m-1) ≤ Nat.card D := by
    rw [hD]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨U,hUD,hU⟩ := exists_binary_subspace_card_eq D (2^(m-1)) ⟨m-1,rfl⟩ hsmall
  have hUE : ∀ x ∈ U, x ∈ E := by
    intro x hx
    exact (mem_additiveDomain D x).mpr (hUD hx)
  have hc : commonAgreementGE E (2^(m-2)) f g R := by
    simpa only [mul_zero, zero_mul, add_zero] using
      unpadded_commonAgreementGE E U hUE m s (by omega) hU params (0:F)
  refine ⟨f,g,⟨agreementGE_right_of_common E _ f g R hc,hg⟩,
    ⟨hc,commonAgreementLE_of_right E _ f g R hg⟩,?_⟩
  simpa only [hIc] using hθ

/-- Exact finite codimension-s construction on every supplied domain. The
extension-degree hypothesis provides the independent challenge and input coordinates. -/
theorem unpadded_codimension_counterexample
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2] [Algebra B F]
    (D : AddSubgroup B) (m s : ℕ) (hs : 2 ≤ s) (hm : s ≤ m)
    (hD : Nat.card D = 2^(m+s)) (hext : s+1 ≤ Module.finrank B F) :
    let E := additiveDomain (D.map (algebraMap B F).toAddMonoidHom)
    ∃ f g : E → F,
      agreementEQ E (2^(m-2)) f (2^(m-1)-1) ∧
      agreementEQ E (2^(m-2)) g (2^(m-1)-1) ∧
      commonAgreementEQ E (2^(m-2)) f g (2^(m-1)-1) ∧
      gaussianBinomial 2 (m+s) s ≤
        (nonzeroBadChallenges E (2^(m-2)) f g (2^m-1)).card := by
  classical
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  dsimp only
  let φ : B →+* F := algebraMap B F
  let DF := D.map φ.toAddMonoidHom
  let E := additiveDomain DF
  have hframe : Fintype.card B ^ (s+1) ≤ Fintype.card F := by
    rw [Module.card_eq_pow_finrank (K := B) (V := F)]
    exact Nat.pow_le_pow_right (by positivity) hext
  obtain ⟨v,hv,hv0⟩ := exists_normalized_independent_frame (B := B) (F := F)
    (s+1) (by omega) hframe
  let θ := finiteCancellationParameterExtension s (extensionCancellationParameters s v)
  let src : F[X] := cancellationSource m s θ
  let R := 2^(m-1)-1
  let f : E → F := fun x ↦ src.eval (x:F)+v (Fin.last s)*(x:F)^R
  let g : E → F := fun x ↦ (x:F)^R

  -- Projection bounds each input; one smaller subgroup attains the same bound.
  have hdim : 2^(m-2) ≤ R := by
    have he : 2^(m-1) = (2:ℕ)^(m-2)*2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hp : 0 < (2:ℕ)^(m-2) := by positivity
    dsimp [R]
    rw [he]
    omega
  have hg : agreementLE E (2^(m-2)) g R := by
    have hd : ((2^(m-2):ℕ) : WithBot ℕ) ≤ (X^R : F[X]).degree := by
      rw [degree_X_pow]
      exact_mod_cast hdim
    simpa [g] using agreementLE_polynomial E (2^(m-2)) (X^R : F[X]) hd
  have hmap : mappedDomain φ (additiveDomain D) = E := mappedDomain_additiveDomain φ D
  have hf : agreementLE E (2^(m-2)) f R := by
    have hd : ((2^(m-2):ℕ) : WithBot ℕ) ≤ (X^R : B[X]).degree := by
      rw [degree_X_pow]
      exact_mod_cast hdim
    have hproj := agreementLE_extensionFrameWordOnMapped s (by omega) v hv hv0
      (additiveDomain D) (2^(m-2))
      (fun x : B ↦ x^(2^(m+s-1)-1))
      (fun j x ↦ x^(2^(m+s-2-j.1)-1)) (X^R) hd
    rw [hmap] at hproj
    have hfun : f = fun x : E ↦ extensionFrameWordOnMapped s v
        (fun y : B ↦ y^(2^(m+s-1)-1))
        (fun j y ↦ y^(2^(m+s-2-j.1)-1))
        (fun y ↦ (X^R : B[X]).eval y) (x:F) := by
      funext x
      obtain ⟨y,hy,he⟩ : ∃ y ∈ additiveDomain D, φ y = (x:F) := by
        have hx : (x:F) ∈ mappedDomain φ (additiveDomain D) := by
          rw [hmap]
          exact x.property
        exact Finset.mem_image.mp hx
      change src.eval (x:F)+v (Fin.last s)*(x:F)^R = _
      rw [← he, extensionFrameWordOnMapped_apply]
      rw [show src = cancellationSource m s
        (finiteCancellationParameterExtension s (extensionCancellationParameters s v)) from rfl,
        cancellationSource_extensionFrameWord m s hs v y]
      simp only [extensionFrameWord, eval_pow, eval_X, map_zero, zero_mul,
        add_zero, map_pow, φ]
      rw [mul_comm (v (Fin.last s))]
    rw [hfun]
    simpa only [natDegree_X_pow] using hproj
  have hsmall : 2^(m-1) ≤ Nat.card D := by
    rw [hD]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨U,hUD,hU⟩ := exists_binary_subspace_card_eq D (2^(m-1)) ⟨m-1,rfl⟩ hsmall
  let UF := U.map φ.toAddMonoidHom
  have hUF : Nat.card UF = 2^(m-1) :=
    (AddSubgroup.card_map_of_injective φ.injective).trans hU
  have hUFE : ∀ x ∈ UF, x ∈ E := by
    intro x hx
    exact (mem_additiveDomain DF x).mpr (AddSubgroup.map_mono hUD hx)
  have hc : commonAgreementGE E (2^(m-2)) f g R :=
    unpadded_commonAgreementGE E UF hUFE m s (by omega) hUF θ (v (Fin.last s))
  refine ⟨f,g,⟨agreementGE_left_of_common E _ f g R hc,hf⟩,
    ⟨agreementGE_right_of_common E _ f g R hc,hg⟩,
    ⟨hc,commonAgreementLE_of_right E _ f g R hg⟩,?_⟩

  -- Every subspace contributes a different nonzero challenge for this one fixed pair.
  obtain ⟨I,hIc,hI⟩ := exists_binary_full_subgroup_family D m s hD
  rw [← hIc]
  exact highExtension_seed_badChallenges_of_dimension D m s (2^(m-2)) hs hm le_rfl
    hD I hI v hv hv0

/-- Cubic count at rate `1/32`, including the smallest dimension `d=6`.
For every supplied domain and extension of degree at least four, the same pair
has both individual and common agreement exactly `N/16-1`; at least
`(N-1)(N-2)(N-4)/168` distinct nonzero challenges attain `N/8-1` agreements. -/
theorem cubic_count_rate_one_thirtytwo
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2] [Algebra B F]
    (D : AddSubgroup B) (d : ℕ) (hd : 6 ≤ d)
    (hD : Nat.card D = 2^d) (hext : 4 ≤ Module.finrank B F) :
    let E := additiveDomain (D.map (algebraMap B F).toAddMonoidHom)
    let N := 2^d
    ∃ f g : E → F,
      agreementEQ E (N/32) f (N/16-1) ∧
      agreementEQ E (N/32) g (N/16-1) ∧
      commonAgreementEQ E (N/32) f g (N/16-1) ∧
      (N-1)*(N-2)*(N-4)/168 ≤
        (nonzeroBadChallenges E (N/32) f g (N/8-1)).card := by
  have hexp : d-3+3 = d := by omega
  have hdomain : Nat.card D = 2^(d-3+3) := by simpa only [hexp] using hD
  have h := unpadded_codimension_counterexample (F := F) D (d-3) 3
    (by decide) (by omega) hdomain hext
  have hdiv (k : ℕ) (hk : k ≤ d) : 2^d / 2^k = (2:ℕ)^(d-k) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_add]
    exact Nat.mul_div_cancel _ (by positivity)
  have h32 : (2:ℕ)^d/32 = 2^(d-3-2) := by
    simpa [show d-3-2=d-5 by omega] using hdiv 5 (by omega)
  have h16 : (2:ℕ)^d/16 = 2^(d-3-1) := by
    simpa [show d-3-1=d-4 by omega] using hdiv 4 (by omega)
  have h8 : (2:ℕ)^d/8 = 2^(d-3) := by simpa using hdiv 3 (by omega)
  have hcount : gaussianBinomial 2 (d-3+3) 3 =
      (2^d-1)*(2^d-2)*(2^d-4)/168 := by
    norm_num [gaussianBinomial, hexp, show 3 ≤ d by omega, Finset.prod_range_succ]
  simpa only [h32,h16,h8,hcount] using h

end BinaryFieldCounterexamples
