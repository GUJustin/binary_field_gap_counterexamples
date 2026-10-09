/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.OrdinaryListAsymptotics
public import BinaryFieldCounterexamples.MainTheorems.FixedAgreementListObstruction
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-!
# Fixed-agreement list obstructions at every scalar-field rate

Section 1, lines 348--352, states the fixed-threshold list obstruction at all
rates supplied by Corollary 5.23, including the binary rates `4^(-k)`.
For a fixed finite scalar field of size `b`, every positive agreement fraction
below `1/b` admits lists exceeding every proposed polynomial bound, uniformly
on sufficiently large full extension fields of size `b^(2n)`.
The code has message length `N/b^2`; its alphabet and domain both have size `N`.
The final statements give explicit codeword-output length and output-cost
lower bounds, without assuming machine-level algorithm semantics.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Filter
open Polynomial

/-- Section 1, lines 348--352: at every scalar-field rate `1/b^2`,
Corollary 5.23 rules out a polynomial decoding-list bound at each positive
fixed agreement below Johnson. The dimension cutoff precedes every extension
field; the full domain and alphabet both have cardinality `N`, and the actual
strict-degree list threshold is `ceil(α N)`. -/
theorem full_field_fixed_agreement_ordinary_list_obstruction
    (k : Type*) [Field k] [Fintype k]
    (α v C₀ : ℝ) (_hα : 0 < α)
    (hαjohnson : α < 1/(Fintype.card k : ℝ)) (_hC₀ : 0 < C₀) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∀ (B : Type*) [Field B] [Fintype B] [Algebra k B],
    Fintype.card B = Fintype.card k^(2*n) →
    let N := Fintype.card B
    α ≤ (⌈α*(N:ℝ)⌉₊ : ℝ)/N ∧
      ∃ L : ℕ, C₀*(N:ℝ)^v < L ∧
        ordinaryList (Finset.univ : Finset B)
          (N/Fintype.card k^2) ⌈α*(N:ℝ)⌉₊ L := by
  let b : ℕ := Fintype.card k
  have hb : (1:ℝ) < b := by exact_mod_cast Fintype.one_lt_card (α := k)
  have hlogb : 0 < Real.log (b:ℝ) := Real.log_pos hb
  obtain ⟨A,c,C,hA,hc,hC,n₁,hsource⟩ := ordinary_lists_near_johnson k
  have hNlim : Tendsto (fun n : ℕ => (b:ℝ)^(2*n)) atTop atTop := by
    have hbase : (1:ℝ) < (b:ℝ)^2 := by nlinarith
    simpa only [pow_mul] using tendsto_pow_atTop_atTop_of_one_lt hbase
  have hlim : Tendsto (fun n : ℕ => ((b:ℝ)^(2*n))^(-(1/4:ℝ)))
      atTop (nhds 0) := (tendsto_rpow_neg_atTop (by norm_num)).comp hNlim

  -- The fractional agreement deficit eventually lies below the fixed margin.
  have hdeficit : ∀ᶠ n : ℕ in atTop,
      C*((b:ℝ)^(2*n))^(-(1/4:ℝ)) < 1/(b:ℝ)-α := by
    have hzero : C*0 < 1/(b:ℝ)-α := by dsimp [b]; linarith
    have hh := (hlim.const_mul C).eventually (eventually_lt_nhds hzero)
    simpa only [mul_zero] using hh
  obtain ⟨n₂,hn₂⟩ := eventually_atTop.mp hdeficit

  -- Logarithmic growth in the list exponent dominates every fixed power.
  have hscale : 0 < 2*A*Real.log (b:ℝ) := by positivity
  obtain ⟨n₃,hn₃⟩ := exists_nat_gt ((v+1)/(2*A*Real.log (b:ℝ)))
  have hlength : ∀ᶠ n : ℕ in atTop, C₀ < (b:ℝ)^(2*n) :=
    hNlim.eventually (eventually_gt_atTop C₀)
  obtain ⟨n₄,hn₄⟩ := eventually_atTop.mp hlength
  let n₀ := max n₁ (max n₂ (max n₃ (max n₄ 2)))
  refine ⟨n₀,by dsimp [n₀]; omega,?_⟩
  intro n hn B fieldB finiteB algB hB
  have hnall : n₁ ≤ n ∧ n₂ ≤ n ∧ n₃ ≤ n ∧ n₄ ≤ n ∧ 2 ≤ n := by
    dsimp [n₀] at hn
    omega
  have hN : (0:ℝ) < Fintype.card B := by positivity
  have hNgt : (1:ℝ) < Fintype.card B := by exact_mod_cast Fintype.one_lt_card (α := B)
  have hNpow : (Fintype.card B : ℝ) = (b:ℝ)^(2*n) := by
    exact_mod_cast hB
  have hlogN : Real.log (Fintype.card B : ℝ) =
      (2*(n:ℝ))*Real.log (b:ℝ) := by
    rw [hNpow,Real.log_pow]
    push_cast
    rfl
  have hexponent : v+1 < A*Real.log (Fintype.card B : ℝ) := by
    have hh : (v+1)/(2*A*Real.log (b:ℝ)) < (n:ℝ) :=
      hn₃.trans_le (by exact_mod_cast hnall.2.2.1)
    have hx := (div_lt_iff₀ hscale).mp hh
    rw [hlogN]
    nlinarith
  obtain ⟨T,E,hcount,_,hhi,hfamily⟩ := hsource n hnall.1 B hB
  have hfraction : α < (T:ℝ)/(Fintype.card B : ℝ) := by
    have hh := hn₂ n hnall.2.1
    rw [←hNpow] at hh
    dsimp [b] at hh
    linarith
  have hthreshold : ⌈α*(Fintype.card B : ℝ)⌉₊ ≤ T := by
    apply Nat.ceil_le.mpr
    exact ((lt_div_iff₀ hN).mp hfraction).le
  have hconstant : C₀ < (Fintype.card B : ℝ) := by
    rw [hNpow]
    exact hn₄ n hnall.2.2.2.1
  have hpolynomial : C₀*(Fintype.card B : ℝ)^v <
      (Fintype.card B : ℝ)^(v+1) := by
    rw [Real.rpow_add hN,Real.rpow_one]
    nlinarith [Real.rpow_pos_of_pos hN v]
  have hlarge : C₀*(Fintype.card B : ℝ)^v < E.card := by
    exact hpolynomial.trans
      ((Real.rpow_lt_rpow_of_exponent_lt hNgt hexponent).trans_le hcount)
  refine ⟨?_,E.card,hlarge,?_⟩
  · apply (le_div_iff₀ hN).mpr
    exact Nat.le_ceil _
  · refine ⟨(fun x => x.val^(Fintype.card B/Fintype.card k)),E,le_rfl,?_⟩
    intro q hq
    obtain ⟨hdegree,hagreement⟩ := hfamily q hq
    exact ⟨hdegree,hthreshold.trans hagreement.ge⟩

/-- Section 1, lines 351--352: at every scalar-field rate `1/b^2`,
an explicit output list containing all codewords above any fixed agreement
below `1/b` has more than every proposed polynomial number of entries. This
includes all binary scalar-field rates `4^(-k)` and allows repeated outputs. -/
theorem full_field_fixed_agreement_explicit_output_obstruction
    (k : Type*) [Field k] [Fintype k]
    (α v C₀ : ℝ) (hα : 0 < α)
    (hαjohnson : α < 1/(Fintype.card k : ℝ)) (hC₀ : 0 < C₀) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∀ (B : Type*) [Field B] [Fintype B] [Algebra k B],
    Fintype.card B = Fintype.card k^(2*n) →
    let N := Fintype.card B
    ∃ w : ↥(Finset.univ : Finset B) → B,
      ∀ output : List (↥(Finset.univ : Finset B) → B),
      (∀ q : B[X], q.degree < (N/Fintype.card k^2 : ℕ) →
        ⌈α*(N:ℝ)⌉₊ ≤ agreementCount Finset.univ w q →
        (fun x : (Finset.univ : Finset B) => q.eval (x : B)) ∈ output) →
      C₀*(N:ℝ)^v < output.length := by
  obtain ⟨n₀,hn₀,h⟩ :=
    full_field_fixed_agreement_ordinary_list_obstruction k α v C₀ hα hαjohnson hC₀
  refine ⟨n₀,hn₀,?_⟩
  intro n hn B fieldB finiteB algB hB
  obtain ⟨_,L,hlarge,hlist⟩ := h n hn B hB
  have hK : Fintype.card B/Fintype.card k^2 ≤ (Finset.univ : Finset B).card := by
    rw [Finset.card_univ]
    exact Nat.div_le_self _ _
  obtain ⟨w,hw⟩ := ordinaryList_explicit_output_length Finset.univ
    (Fintype.card B/Fintype.card k^2) ⌈α*(Fintype.card B : ℝ)⌉₊ L hK hlist
  refine ⟨w,?_⟩
  intro output houtput
  exact hlarge.trans_le (by exact_mod_cast hw output houtput)

/-- Section 1, lines 351--352: the same scalar-field list obstruction
excludes every polynomial step budget under the standard explicit-output
convention that listing each codeword costs at least one step. This is a
combinatorial output-cost statement, not a machine-level complexity model. -/
theorem full_field_fixed_agreement_explicit_output_step_obstruction
    (k : Type*) [Field k] [Fintype k]
    (α v C₀ : ℝ) (hα : 0 < α)
    (hαjohnson : α < 1/(Fintype.card k : ℝ)) (hC₀ : 0 < C₀) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∀ (B : Type*) [Field B] [Fintype B] [Algebra k B],
    Fintype.card B = Fintype.card k^(2*n) →
    let N := Fintype.card B
    ∃ w : ↥(Finset.univ : Finset B) → B,
      ∀ (output : List (↥(Finset.univ : Finset B) → B)) (steps : ℕ),
      (∀ q : B[X], q.degree < (N/Fintype.card k^2 : ℕ) →
        ⌈α*(N:ℝ)⌉₊ ≤ agreementCount Finset.univ w q →
        (fun x : (Finset.univ : Finset B) => q.eval (x : B)) ∈ output) →
      output.length ≤ steps → C₀*(N:ℝ)^v < steps := by
  obtain ⟨n₀,hn₀,h⟩ :=
    full_field_fixed_agreement_explicit_output_obstruction k α v C₀ hα hαjohnson hC₀
  refine ⟨n₀,hn₀,?_⟩
  intro n hn B fieldB finiteB algB hB
  obtain ⟨w,hw⟩ := h n hn B hB
  refine ⟨w,?_⟩
  intro output steps houtput hcost
  exact (hw output houtput).trans_le (by exact_mod_cast hcost)

end BinaryFieldCounterexamples
