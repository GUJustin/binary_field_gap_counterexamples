/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.OrdinaryListAsymptotics.MonomialCenter
public import BinaryFieldCounterexamples.Constructions.OrdinaryListAsymptotics.Bounds
public import BinaryFieldCounterexamples.Constructions.OrdinaryListAsymptotics.SlowRates

/-!
# Main theorem: decoding lists approaching Johnson over the domain field

Paper statement: [Corollary 5.23, p. 55](../../../binary-field-counterexamples.pdf#page=55).

For each fixed scalar field of cardinality `b`, all `n ≥ 4` and every field
`B` of cardinality `N=b^(2n)` carrying the scalar embedding, the explicit
received word `x ↦ x^(N/b)` has at least `N^(A log N)` distinct strict-degree
`<N/b²` explaining polynomials. Every explaining polynomial agrees in exactly `T` positions, and
`c N^(-1/4) ≤ 1/b-T/N ≤ C N^(-1/4)`. The positive constants `A,c,C` and cutoff
are chosen before `n` or `B`; thus both sides of the printed Θ bound hold
uniformly over the fields. The alphabet is `B` itself, of size exactly `N`.

The proof specializes the actual full-field sparse locator family to
`t=floor(n/2)`, identifies its center as the advertised monomial, and uses the
Gaussian leading-power bound. There are no additional population assumptions.
The additional slowly vanishing-rate specialization takes `b=2^u`, `n=2u`,
`t=u`. Its endpoint below gives `N=2^(4u²)`, list size at least `N^(u/2)`,
and relative agreement `1-(2^u-1)/2^(u²)`. The imported `SlowRates` support
proves that the rate tends to zero, the relative agreement tends to one,
and the list exponent tends to infinity, as well as `ρ=N^(-1/(2u))`.
All statements in this module are proved.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open OrdinaryListConstruction
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Explicit finite version of Corollary 5.23, with a cutoff of four and
positive constants depending only on the fixed scalar cardinality. -/
theorem ordinary_lists_near_johnson_finite
    (k B : Type*) [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (n : ℕ) (hn : 4 ≤ n)
    (hcard : Fintype.card B = Fintype.card k^(2*n)) :
    let b := Fintype.card k
    let N := Fintype.card B
    let T := b^(2*n-1)-(b-1)*b^(2*n-n/2-1)
    ∃ E : Finset B[X],
      (N:ℝ)^((1/(32*Real.log b))*Real.log N) ≤ E.card ∧
      (((b:ℝ)-1)/b)*(N:ℝ)^(-(1/4:ℝ)) ≤ 1/(b:ℝ)-(T:ℝ)/N ∧
      1/(b:ℝ)-(T:ℝ)/N ≤ ((b:ℝ)-1)*(N:ℝ)^(-(1/4:ℝ)) ∧
      ∀ f ∈ E, f.degree < N/b^2 ∧
        agreementCount Finset.univ (fun x => x.val^(N/b)) f=T := by
  -- Specialize the actual locator population to the middle rank.

  let b := Fintype.card k
  have hb : 2 ≤ b := Fintype.one_lt_card
  obtain ⟨E,hE,hprop⟩ := fullfield_monomial_list k B n (n/2) (by omega)
    (Nat.div_le_self _ _) hcard
  -- Quantify both population growth and the two-sided agreement deficit.

  have hcount : b^(2*(n/2)*(n-n/2)) ≤ E.card :=
    (quadraticListCount_lower b n (n/2) hb (by omega) (Nat.div_le_self _ _)).trans hE
  have hgrowth := middle_rank_power_superpolynomial b n hb hn
  have hfrac := fullfield_agreement_fraction b n (n/2) hb (by omega) (Nat.div_le_self _ _)
  have hgap := middle_rank_deficit_bounds b n hb
  -- Express the polynomial degrees and center using the literal domain size.

  have hNdiv : Fintype.card B/b=b^(2*n-1) := by
    rw [hcard]
    simpa only [pow_one] using Nat.pow_div (show 1≤2*n by omega) (show 0<b by omega)
  have hK : Fintype.card B/b^2=b^(2*n-2) := by
    rw [hcard,Nat.pow_div (by omega) (show 0<b by omega)]
  dsimp only [b] at hfrac hgap hNdiv hK
  dsimp only
  refine ⟨E,?_,?_,?_,?_⟩
  · have hcountR : (b:ℝ)^(2*(n/2)*(n-n/2)) ≤ E.card := by exact_mod_cast hcount
    simpa only [hcard,Nat.cast_pow] using hgrowth.trans hcountR
  · simpa only [hcard,Nat.cast_pow,hfrac,sub_sub_cancel] using hgap.1
  · simpa only [hcard,Nat.cast_pow,hfrac,sub_sub_cancel] using hgap.2
  · intro f hf
    simpa only [hK,hNdiv,Nat.cast_pow] using hprop f hf

/-- Corollary 5.23 with the asymptotic quantifiers exposed: all three positive
constants and the dimension cutoff depend only on the fixed scalar field,
and precede the extension field and every resulting codeword family. -/
theorem ordinary_lists_near_johnson
    (k : Type*) [Field k] [Fintype k] :
    ∃ A c C : ℝ, 0<A ∧ 0<c ∧ 0<C ∧ ∃ n0 : ℕ,
      ∀ n : ℕ, n0≤n → ∀ (B : Type*) [Field B] [Fintype B] [Algebra k B],
        Fintype.card B = Fintype.card k^(2*n) →
        let b := Fintype.card k
        let N := Fintype.card B
        ∃ (T : ℕ) (E : Finset B[X]),
          (N:ℝ)^(A*Real.log N) ≤ E.card ∧
          c*(N:ℝ)^(-(1/4:ℝ)) ≤ 1/(b:ℝ)-(T:ℝ)/N ∧
          1/(b:ℝ)-(T:ℝ)/N ≤ C*(N:ℝ)^(-(1/4:ℝ)) ∧
          ∀ f∈E, f.degree<N/b^2 ∧
            agreementCount Finset.univ (fun x => x.val^(N/b)) f=T := by
  have hb : (1:ℝ)<Fintype.card k := by exact_mod_cast (Fintype.one_lt_card (α := k))
  have hlog := Real.log_pos hb
  refine ⟨1/(32*Real.log (Fintype.card k)),
    ((Fintype.card k:ℝ)-1)/Fintype.card k,(Fintype.card k:ℝ)-1,
    by positivity,by positivity,by linarith,4,?_⟩
  intro n hn B _ _ _ hcard
  obtain ⟨E,hE⟩ := ordinary_lists_near_johnson_finite k B n hn hcard
  exact ⟨_,E,hE⟩

/-- The slowly vanishing-rate specialization, for every `u ≥ 2`. The scalar
field now has size `2^u`, the alphabet and full domain have size `N=2^(4u²)`,
and the explicit monomial center has at least `N^(u/2)` explaining polynomials. Agreement
is normalized by the shrinking Johnson threshold, rather than by a constant.
The supporting `slow_rate_*tendsto*` theorems prove the limiting claims. -/
theorem ordinary_lists_slowly_vanishing_rate
    (u : ℕ) (hu : 2≤u)
    (k B : Type*) [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (hk : Fintype.card k=2^u) (hcard : Fintype.card B=2^(4*u^2)) :
    let N := Fintype.card B
    let b : ℕ := 2^u
    ∃ (T : ℕ) (E : Finset B[X]),
      (N:ℝ)^((u:ℝ)/2) ≤ E.card ∧
      ((T:ℝ)/N)/Real.sqrt (1/(b:ℝ)^2)=
        1-((2:ℝ)^u-1)/(2:ℝ)^(u^2) ∧
      1/(b:ℝ)^2=(N:ℝ)^(-1/(2*(u:ℝ))) ∧
      ∀ f∈E, f.degree<N/b^2 ∧
        agreementCount Finset.univ (fun x => x.val^(N/b)) f=T := by
  have hb : 2≤2^u := by
    simpa using Nat.pow_le_pow_right (by decide : 0<2) (show 1≤u by omega)
  -- Retain the finite construction while allowing the scalar field to grow.

  have hB : Fintype.card B=Fintype.card k^(2*(2*u)) := by
    rw [hk,slow_rate_length,hcard]
  obtain ⟨E,hE,hprop⟩ := fullfield_monomial_list k B (2*u) u hu (by omega) hB
  simp only [hk] at hE hprop
  -- Convert the Gaussian power and agreement into the printed length parameters.

  have hcount : (2^u)^(2*u*(2*u-u))≤E.card :=
    (quadraticListCount_lower (2^u) (2*u) u hb (by omega) (by omega)).trans hE
  have hcountR : ((2^u:ℕ):ℝ)^(2*u*(2*u-u))≤E.card := by exact_mod_cast hcount
  have hNdiv : Fintype.card B/(2^u)=(2^u)^(2*(2*u)-1) := by
    rw [hB,hk]
    simpa only [pow_one] using Nat.pow_div (show 1≤2*(2*u) by omega)
      (show 0<2^u by positivity)
  have hK : Fintype.card B/(2^u)^2=(2^u)^(2*(2*u)-2) := by
    rw [hB,hk,Nat.pow_div (by omega) (show 0<2^u by positivity)]
  dsimp only
  refine ⟨(2^u)^(2*(2*u)-1)-(2^u-1)*(2^u)^(2*(2*u)-u-1),E,?_,?_,?_,?_⟩
  · simpa only [hcard,Nat.cast_pow,Nat.cast_ofNat,slow_rate_list_power] using hcountR
  · simpa only [hcard,Nat.cast_pow,Nat.cast_ofNat] using slow_rate_relative_agreement u hu
  · simpa only [hcard,Nat.cast_pow,Nat.cast_ofNat] using slow_rate_as_power_of_length u (by omega)
  · intro f hf
    simpa only [hK,hNdiv,Nat.cast_pow,Nat.cast_ofNat] using hprop f hf
end BinaryFieldCounterexamples
