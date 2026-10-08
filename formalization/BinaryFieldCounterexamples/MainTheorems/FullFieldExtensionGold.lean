/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FullFieldExtensionAsymptotic

/-!
# Main theorem: Fixed-extension Gold probability on the full field

Paper statement: [Corollary 5.3, p. 38](../../../binary-field-counterexamples.pdf#page=38),
the full-field clause of the fixed-extension Gold corollary. Fix an extension
exponent `e≥2` and an error `ε>0`. After a cutoff
depending only on these two parameters, every even-dimensional binary field
`B` of size `N=2^(2n)` and extension `F` of size `N^e` admit the result on
the full evaluation field, embedded in `F`.

The code has strict message degree `N/4`. One pair has exact common and
second-input agreement `N/4`, first-input agreement at most `3N/8-1`, and
at least `(1/4^(e-1)-ε)|F|` distinct nonzero exceptional challenges at agreement
threshold `N/2-2^(e-2)√N`. The natural ceiling in the formal statement is
redundant: the radical expression is the nonnegative integer
`2^(2n-1)-2^(n+e-2)` under the stated cutoff.

For `e=2`, this gives agreement `N/2-√N` and exceptional probability at
least `1/4-ε`. It is a full-field result; it does not replace the companion
hyperplane result on prescribed domains of half the containing field's size.

The domain is represented by an arbitrary supplied subgroup `D` whose
cardinality equals `|B|`; hence it is the full field. Every embedding and
translate is allowed. The cutoff precedes the choice of fields and domain,
and one fixed pair serves the entire counted challenge set. All proofs are
complete and use the actual Gold locator population and collision estimate.
-/

@[expose] public section
namespace BinaryFieldCounterexamples

/-- On every supplied full-field domain, fixed extension degree `e≥2` yields
probability at least `1/4^(e-1)-ε` at the exact radical threshold, uniformly
after a cutoff depending only on `e` and `ε`. All counts are distinct nonzero
challenges for the same pair, with strict degree-`<N/4` witnesses. -/
theorem gold_full_field_fixed_extension_probability
    (e : ℕ) (he : 2 ≤ e) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, e+2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∀ {B F : Type} [Field B] [Fintype B] [CharP B 2]
      [Field F] [Fintype F] [CharP F 2]
      (φ : B →+* F) (D : AddSubgroup B) (a : B),
      Fintype.card B = 2^(2*n) → (additiveDomain D).card = 2^(2*n) →
      Fintype.card F = (2^(2*n))^e →
    let N : ℕ := 2^(2*n)
    let T : ℕ := ⌈(N:ℝ)/2-(2:ℝ)^(e-2)*Real.sqrt (N:ℝ)⌉₊
    let E := mappedDomain φ (affineDomain (additiveDomain D) a)
    ∃ f g : E → F,
      commonAgreementEQ E (N/4) f g (N/4) ∧
      agreementEQ E (N/4) g (N/4) ∧
      agreementLE E (N/4) f (3*N/8-1) ∧
      ((1:ℝ)/(4:ℝ)^(e-1)-ε)*(Fintype.card F:ℝ) ≤
        ((nonzeroBadChallenges E (N/4) f g T).card:ℝ) := by
  -- Choose the uniform cutoff before the fields, embedding, and domain.
  obtain ⟨n₀, hn₀, hpair⟩ := Gold.gold_full_field_extension_probability_asymptotic e he ε hε
  refine ⟨n₀, hn₀, ?_⟩
  intro n hnn B F _ _ _ _ _ _ φ D a hB hD hF
  have hn : e+2 ≤ n := hn₀.trans hnn
  have hp := hpair n hnn φ D a hB hD hF

  -- Both displayed expressions agree exactly with the finite construction.
  have hT : ⌈((2^(2*n):ℕ):ℝ)/2-
      (2:ℝ)^(e-2)*Real.sqrt (2^(2*n):ℕ)⌉₊ =
      2^(2*n-1)-2^(n+e-2) := by
    rw [← Gold.full_field_extension_threshold_eq_radical n e he hn]
    exact Nat.ceil_natCast _
  have hc : (1:ℝ)/(4:ℝ)^(e-1) = (1:ℝ)/(2:ℝ)^(2*(e-1)) := by
    rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul]
  dsimp only at hp ⊢
  rw [hT, hc]
  exact hp

end BinaryFieldCounterexamples
