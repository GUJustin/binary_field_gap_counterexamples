/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.SuperpolynomialNearJohnson
public import BinaryFieldCounterexamples.Polynomial.SectionThreeCanonical
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-!
# No polynomial decoding-list bound at fixed agreement below Johnson

The abstract and Section 1, lines 158--159 and 351--352, draw this consequence
of the dense Gold construction. Fix a density codimension, a positive
agreement fraction strictly below `1/2`, and a proposed bound `C₀ N^b`.
Every sufficiently large prescribed dense binary additive domain has an actual
received word with more than that many distinct strict-degree explaining
polynomials at threshold `ceil(α N)`. Its alphabet has exactly `2^c N` elements.
This states the quantitative list obstruction without introducing a model of
algorithm execution or its output cost.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Filter
open Polynomial

/-- Abstract and Section 1, lines 158--159 and 351--352: at every positive
fixed agreement fraction below the quarter-rate Johnson limit, dense binary
Reed--Solomon decoding lists exceed every proposed polynomial bound. The cutoff
precedes the containing field and each prescribed domain, whose alphabet size
is exactly the fixed multiple `2^c N`. Lists contain actual strict-degree
polynomials for one received word at the explicit threshold `ceil(α N)`. -/
theorem fixed_agreement_dense_ordinary_list_obstruction
    (c : ℕ) (α b C₀ : ℝ) (_hα : 0 < α) (hαhalf : α < 1/2) (_hC₀ : 0 < C₀) :
    ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = 2^(d+c) →
    ∀ D : AddSubgroup B, (additiveDomain D).card = 2^d →
    let N : ℕ := 2^d
    Fintype.card B = 2^c*N ∧
      α ≤ (⌈α*(N:ℝ)⌉₊ : ℝ)/N ∧
      ∃ L : ℕ, C₀*(N:ℝ)^b < L ∧
        ordinaryList (additiveDomain D) (N/4) ⌈α*(N:ℝ)⌉₊ L := by
  let θ : ℝ := min (1/4) (1/((c:ℝ)+1))
  let γ : ℝ := θ*(1-2*θ)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθu : θ ≤ 1/4 := min_le_left _ _
  have hγ : 0 < γ := mul_pos hθ (by linarith)
  obtain ⟨A,C,p,hA,hC,hp,d₁,hlist⟩ := superpolynomial_near_johnson c
  change ∀ d : ℕ, d₁ ≤ d → _ at hlist

  -- Make the actual agreement exceed the chosen fixed fraction.
  have hlim : Tendsto (fun d : ℕ => ((2:ℝ)^d)^(-θ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hθ).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  have hdeficit : ∀ᶠ d : ℕ in atTop,
      C*((2:ℝ)^d)^(-θ) < 1/2-α := by
    have hzero : C*0 < 1/2-α := by linarith
    have hh := (hlim.const_mul C).eventually (eventually_lt_nhds hzero)
    simpa only [mul_zero] using hh
  obtain ⟨d₂,hd₂⟩ := eventually_atTop.mp hdeficit

  -- The quadratic count exponent beats the proposed degree with room for C₀.
  obtain ⟨d₃,hd₃⟩ := exists_nat_gt ((C+b+2)/γ)
  have hlength : ∀ᶠ d : ℕ in atTop, C₀ < (2:ℝ)^d :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually
      (eventually_gt_atTop C₀)
  obtain ⟨d₄,hd₄⟩ := eventually_atTop.mp hlength
  let d₀ := max d₁ (max d₂ (max d₃ (max d₄ 2)))
  refine ⟨d₀,by dsimp [d₀]; omega,?_⟩
  intro d hd B fieldB finiteB decB charB hB D hD
  have hdall : d₁ ≤ d ∧ d₂ ≤ d ∧ d₃ ≤ d ∧ d₄ ≤ d ∧ 2 ≤ d := by
    dsimp [d₀] at hd
    omega
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0<d by omega)
  have hscale : C+b+2 < γ*(d:ℝ) := by
    have hh : (C+b+2)/γ < (d:ℝ) :=
      hd₃.trans_le (by exact_mod_cast hdall.2.2.1)
    simpa only [mul_comm] using (div_lt_iff₀ hγ).mp hh
  have hexp : (d:ℝ)*(b+1) < γ*(d:ℝ)^2-C*d := by
    have hh : 0 < (d:ℝ)*(γ*(d:ℝ)-C-b-1) := mul_pos hdR (by linarith)
    nlinarith
  have hN : (0:ℝ) < (2^d:ℕ) := by positivity
  obtain ⟨T,L,_,hhi,hcount,hfamily,_⟩ :=
    hlist d hdall.1 B hB D hD
  have hfraction : α < (T:ℝ)/(2^d:ℕ) := by
    have hh := hd₂ d hdall.2.1
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hhi ⊢
    linarith
  have hthreshold : ⌈α*((2^d:ℕ):ℝ)⌉₊ ≤ T := by
    apply Nat.ceil_le.mpr
    exact ((lt_div_iff₀ hN).mp hfraction).le
  have hconstant : C₀ < ((2^d:ℕ):ℝ) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hd₄ d hdall.2.2.2.1
  have hpower : (((2^d:ℕ):ℝ))^(b+1) = (2:ℝ)^((d:ℝ)*(b+1)) := by
    rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,
      ←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  have hpolynomial : C₀*(((2^d:ℕ):ℝ))^b < (((2^d:ℕ):ℝ))^(b+1) := by
    rw [Real.rpow_add hN, Real.rpow_one]
    nlinarith [Real.rpow_pos_of_pos hN b]
  have hlarge : C₀*(((2^d:ℕ):ℝ))^b < L := by
    apply hpolynomial.trans
    rw [hpower]
    have hs := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hexp
    exact hs.trans_le hcount
  refine ⟨?_,?_,L,hlarge,?_⟩
  · rw [hB, pow_add]
    exact Nat.mul_comm _ _
  · apply (le_div_iff₀ hN).mpr
    exact Nat.le_ceil _
  · obtain ⟨w,ps,hL,hps⟩ := hfamily
    refine ⟨w,ps,hL,?_⟩
    intro q hq
    obtain ⟨hdegree,hagreement⟩ := hps q hq
    exact ⟨hdegree,hthreshold.trans hagreement⟩

/-- Section 1, lines 351--352: an explicit list containing every qualifying
codeword must contain at least as many entries as the actual decoding list.
Repeated output words do not evade this lower bound. -/
theorem ordinaryList_explicit_output_length
    {F : Type*} [Field F] (D : Finset F) (K T L : ℕ)
    (hK : K ≤ D.card) (hlist : ordinaryList D K T L) :
    ∃ w : D → F, ∀ output : List (D → F),
      (∀ q : F[X], q.degree < K → T ≤ agreementCount D w q →
        (fun x : D => q.eval (x : F)) ∈ output) → L ≤ output.length := by
  classical
  obtain ⟨w,ps,hL,hps⟩ := hlist
  refine ⟨w,?_⟩
  intro output houtput
  have hsubset : ps.image (fun q => fun x : D => q.eval (x : F)) ⊆
      output.toFinset := by
    intro v hv
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    exact List.mem_toFinset.mpr (houtput q (hps q hq).1 (hps q hq).2)
  have hcard := Finset.card_le_card hsubset
  rw [strictDegree_codeword_image_card D K hK ps (fun q hq => (hps q hq).1)] at hcard
  exact hL.trans (hcard.trans (List.toFinset_card_le output))

/-- Section 1, lines 351--352: at any fixed positive agreement below the
quarter-rate Johnson limit, explicitly outputting all qualifying codewords
requires more than every prescribed polynomial number of entries. This is a
statement about the actual output list length, independent of a machine-cost
model. The containing alphabet remains the fixed multiple `2^c` of the domain. -/
theorem fixed_agreement_dense_explicit_output_obstruction
    (c : ℕ) (α b C₀ : ℝ) (hα : 0 < α) (hαhalf : α < 1/2) (hC₀ : 0 < C₀) :
    ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = 2^(d+c) →
    ∀ D : AddSubgroup B, (additiveDomain D).card = 2^d →
    let N : ℕ := 2^d
    Fintype.card B = 2^c*N ∧
      ∃ w : additiveDomain D → B, ∀ output : List (additiveDomain D → B),
        (∀ q : B[X], q.degree < (N/4 : ℕ) →
          ⌈α*(N:ℝ)⌉₊ ≤ agreementCount (additiveDomain D) w q →
          (fun x : additiveDomain D => q.eval (x : B)) ∈ output) →
        C₀*(N:ℝ)^b < output.length := by
  obtain ⟨d₀,hd₀,h⟩ :=
    fixed_agreement_dense_ordinary_list_obstruction c α b C₀ hα hαhalf hC₀
  refine ⟨d₀,hd₀,?_⟩
  intro d hd B fieldB finiteB decB charB hB D hD
  obtain ⟨halphabet,_,L,hlarge,hlist⟩ := h d hd B hB D hD
  have hK : 2^d/4 ≤ (additiveDomain D).card := by
    rw [hD]
    exact Nat.div_le_self _ _
  obtain ⟨w,hw⟩ := ordinaryList_explicit_output_length (additiveDomain D)
    (2^d/4) ⌈α*((2^d:ℕ):ℝ)⌉₊ L hK hlist
  refine ⟨halphabet,w,?_⟩
  intro output houtput
  exact hlarge.trans_le (by exact_mod_cast hw output houtput)

/-- Section 1, lines 351--352: in the standard explicit-output cost
convention where listing each codeword costs at least one step, no fixed
polynomial step budget suffices. The cost hypothesis states only this output
convention; the strictly larger lower bound follows from actual decoding lists. -/
theorem fixed_agreement_dense_explicit_output_step_obstruction
    (c : ℕ) (α b C₀ : ℝ) (hα : 0 < α) (hαhalf : α < 1/2) (hC₀ : 0 < C₀) :
    ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = 2^(d+c) →
    ∀ D : AddSubgroup B, (additiveDomain D).card = 2^d →
    let N : ℕ := 2^d
    Fintype.card B = 2^c*N ∧
      ∃ w : additiveDomain D → B,
        ∀ (output : List (additiveDomain D → B)) (steps : ℕ),
        (∀ q : B[X], q.degree < (N/4 : ℕ) →
          ⌈α*(N:ℝ)⌉₊ ≤ agreementCount (additiveDomain D) w q →
          (fun x : additiveDomain D => q.eval (x : B)) ∈ output) →
        output.length ≤ steps → C₀*(N:ℝ)^b < steps := by
  obtain ⟨d₀,hd₀,h⟩ :=
    fixed_agreement_dense_explicit_output_obstruction c α b C₀ hα hαhalf hC₀
  refine ⟨d₀,hd₀,?_⟩
  intro d hd B fieldB finiteB decB charB hB D hD
  obtain ⟨halphabet,w,hw⟩ := h d hd B hB D hD
  refine ⟨halphabet,w,?_⟩
  intro output steps houtput hcost
  exact (hw output houtput).trans_le (by exact_mod_cast hcost)

end BinaryFieldCounterexamples
