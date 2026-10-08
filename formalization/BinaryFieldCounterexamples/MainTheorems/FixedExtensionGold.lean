/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FixedExtensionAsymptotic
/-!
# Main theorem: fixed-extension Gold probability with the exact leading constant

Paper statement: [Corollary 5.3, p. 38](../../../binary-field-counterexamples.pdf#page=38). Fix an extension exponent e≥2. For
arbitrarily small positive error ε, all sufficiently large n admit the paper's
bound uniformly over finite binary fields B,F of cardinalities 2^(2n) and
(2^(2n))^e, every embedding, every binary hyperplane D, and every translate.
The length is N=2^(2n−1), the strict message degree is N/4, and the agreement
threshold is exactly N/2−2^(e−3/2)√N (written with a natural ceiling, which is
redundant because the displayed real value is an integer on these parameters).

One fixed pair has exact common and second-input agreement N/4, first-input
agreement at most 3N/8−1, and at least (2^(1−2e)−ε)|F| distinct nonzero exceptional
challenges. The cutoff depends only on e and ε. The proof uses the actual Gold
collision quotient and explicit vanishing errors, keeping the leading
coefficient rather than replacing it by a smaller positive constant.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
/-- The exact fixed-extension probability coefficient holds on every prescribed
affine hyperplane after a cutoff chosen before the fields, domain and translate.
All exceptional challenges refer to the same pair; only polynomial witnesses vary. -/
theorem gold_fixed_extension_probability
    (e : ℕ) (he : 2≤e) (ε : ℝ) (hε : 0<ε) :
    ∃ n₀ : ℕ, e+2≤n₀ ∧ ∀ n : ℕ, n₀≤n →
    ∀ {B F : Type} [Field B] [Fintype B] [CharP B 2]
      [Field F] [Fintype F] [CharP F 2]
      (φ : B →+* F) (D : AddSubgroup B) (a : B),
      Fintype.card B=2^(2*n) → (additiveDomain D).card=2^(2*n-1) →
      Fintype.card F=(2^(2*n))^e →
    let N : ℕ := 2^(2*n-1)
    let T : ℕ := ⌈(N:ℝ)/2-(2:ℝ)^((e:ℝ)-3/2)*Real.sqrt (N:ℝ)⌉₊
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F,
      commonAgreementEQ E (N/4) f g (N/4) ∧
      agreementEQ E (N/4) g (N/4) ∧
      agreementLE E (N/4) f (3*N/8-1) ∧
      ((2:ℝ)^(1-2*(e:ℝ))-ε)*(Fintype.card F:ℝ) ≤
        ((nonzeroBadChallenges E (N/4) f g T).card:ℝ) := by
  -- The finite Gold estimate gives its full coefficient with any chosen error.
  obtain ⟨n₀,hn₀,hpair⟩ := Gold.gold_fixed_extension_probability_asymptotic e he ε hε
  refine ⟨n₀,hn₀,?_⟩
  intro n hnn B F _ _ _ _ _ _ φ D a hB hD hF
  have hn : e+2≤n := hn₀.trans hnn
  have hp := hpair n hnn φ D a hB hD hF

  -- Identify both displayed real expressions with their exact finite parameters.
  have hT : ⌈((2^(2*n-1):ℕ):ℝ)/2-
      (2:ℝ)^((e:ℝ)-3/2)*Real.sqrt (2^(2*n-1):ℕ)⌉₊ =
      2^(2*n-2)-2^(n+e-2) := by
    rw [←Gold.fixed_extension_threshold_eq_radical n e he hn]
    exact Nat.ceil_natCast _
  have hc : (2:ℝ)^(1-2*(e:ℝ))=(1:ℝ)/(2:ℝ)^(2*e-1) := by
    have hexp : 1-2*(e:ℝ)=-((2*e-1:ℕ):ℝ) := by
      rw [Nat.cast_sub (by omega : 1≤2*e)]
      push_cast
      ring
    rw [hexp,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,one_div]
  dsimp only at hp ⊢
  rw [hT,hc]
  exact hp
end BinaryFieldCounterexamples
