/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.HigherRateLengthening.GoldAssembly
public import BinaryFieldCounterexamples.Constructions.HigherRateLengthening.RateParameters
public import BinaryFieldCounterexamples.Constructions.HigherRateLengthening.AsymptoticBounds
/-!
# Main theorem: higher rates on every dense binary domain

Paper statement: [Corollary 5.16, p. 47](../../../binary-field-counterexamples.pdf#page=47),
“Higher rates on every dense binary domain”.
Public theorem: `BinaryFieldCounterexamples.higher_rate_lengthening`.
**Proved.** Fix a codimension `c` and a
positive integer `r`, and put `lambda = 2^(-r)`. For every fixed rate
`1-3*lambda/4 ≤ rho < 1-lambda/4`, every sufficiently large dimension, and
every prescribed binary domain of that dimension in the field of size
`2^(d+c)`, there are quasipolynomial decoding lists and fixed-pair nonzero
exceptional sets at agreement at least `(1+rho)/2-lambda/8-o(1)`.

The list exponent and containing-field exponent are fixed before the rate,
accuracy, dimension, field, or domain. The `o(1)` term is expressed by an
arbitrary positive `epsilon` and an eventual dimension cutoff. Both individual
agreements, as well as their common agreement, equal `floor(rho*N)`;
the first-input equality strengthens the corollary's guarantee.

The proof applies dense Gold lists on a codimension-`r` subspace, balanced
padding within that subspace, complement lengthening, and separating-pole
conversion over a genuine finite extension. All mathematical dependencies are
proved; there are no admitted components.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open HigherRateLengthening
open Filter
open scoped Topology
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The stated open upper rate bound gives a strictly positive limiting gap
between the combination's agreement and the inputs' common agreement. -/
theorem higher_rate_lengthening_gap (r : ℕ) (rho : ℝ)
    (hrho : rho < 1-(1/(2^r : ℕ))/4) :
    0 < (1+rho)/2-(1/(2^r : ℕ))/8-rho := by linarith

/-- Corollary 5.16: higher-rate lengthening on every prescribed dense domain.
Constants depend only on the fixed codimension and dyadic lengthening parameter; the cutoff may also depend on
the requested rate and accuracy. The domain is supplied universally. -/
theorem higher_rate_lengthening (c r : ℕ) (_hr : 1 ≤ r) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    ∀ rho : ℝ, 1-3*(1/(2^r : ℕ))/4 ≤ rho → rho < 1-(1/(2^r : ℕ))/4 →
    ∀ epsilon : ℝ, 0 < epsilon → ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [CharP B 2],
      Fintype.card B = 2^(d+c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2^d →
    let N : ℕ := 2^d
    let J := ⌊rho*(N : ℝ)⌋₊
    ∃ T L : ℕ,
      (1+rho)/2-(1/(2^r : ℕ))/8-epsilon ≤ (T : ℝ)/N ∧
      (N : ℝ)^(A*Real.log N) ≤ L ∧ ordinaryList (additiveDomain D) J T L ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ phi : B →+* F, ∃ f g : mappedDomain phi (additiveDomain D) → F,
        agreementEQ (mappedDomain phi (additiveDomain D)) J f J ∧
        agreementEQ (mappedDomain phi (additiveDomain D)) J g J ∧
        commonAgreementEQ (mappedDomain phi (additiveDomain D)) J f g J ∧
        L ≤ (nonzeroBadChallenges (mappedDomain phi (additiveDomain D)) J f g T).card ∧
        (Fintype.card F : ℝ) ≤ (N : ℝ)^(C*Real.log N) := by
  let theta : ℝ := min (1/4) (1/((c+r : ℕ)+1))
  let alpha : ℝ := theta*(1-2*theta)
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have hthetaU : theta ≤ 1/4 := min_le_left _ _
  have halpha : 0 < alpha := mul_pos htheta (by linarith)
  have halphaU : alpha ≤ 1 := by dsimp [alpha]; linarith [sq_nonneg theta]
  obtain ⟨C,hC,dSeed,hconstruction⟩ := gold_lengthening_finite c r
  obtain ⟨hA,dList,hList⟩ := selected_list_bounds alpha C halpha halphaU hC.le r
  refine ⟨alpha/8/(2*Real.log 2),32/Real.log 2,hA,by positivity,?_⟩
  intro rho hrho hrho' epsilon hepsilon

  -- Choose a single cutoff for seed construction, list growth and vanishing errors.
  have hevent := (lengthening_error_tendsto C theta htheta r).eventually
    (gt_mem_nhds hepsilon)
  obtain ⟨dError,hError⟩ := Filter.eventually_atTop.mp hevent
  let d0 := max (max (dSeed+r) dList) (max dError (max c (r+2)))
  refine ⟨d0,?_⟩
  intro d hd B fieldB finiteB charB hB D hD
  have hdSeed : dSeed+r ≤ d := (le_max_left _ _).trans ((le_max_left _ _).trans hd)
  have hdList : dList ≤ d := (le_max_right _ _).trans ((le_max_left _ _).trans hd)
  have hdError : dError ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hdC : c ≤ d := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  have hdr : r+2 ≤ d := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  let N : ℕ := 2^d
  let M : ℕ := 2^(d-r)
  let J := ⌊rho*(N : ℝ)⌋₊
  let a := J-(N-M+M/4)
  let L : ℕ := 2^⌊alpha/8*(d : ℝ)^2⌋₊
  obtain ⟨hK,hJ,ha,hMN,haeq⟩ := rate_parameters r d hdr rho hrho hrho'
  obtain ⟨hrd,hLupper,hLlower,hLseed⟩ := hList d hdList
  rw [←Nat.cast_sub hrd] at hLseed

  -- Construct the literal decoding list and one fixed pair on the supplied domain.
  obtain ⟨T0,hseed,hordinary,F,fieldF,finiteF,phi,f,g,hf,hg,hfg,hbad,hfield⟩ :=
    hconstruction d hdSeed (by omega) hdC B hB D hD J L hK hJ ha hLupper hLseed
  let := fieldF
  let := finiteF
  let U : ℝ := (N-M : ℕ)+a+T0-
    ((a : ℝ)*T0/M+Real.sqrt (((a : ℝ)/2)*Real.log (2*L)))
  refine ⟨⌊U⌋₊,L,?_,hLlower,hordinary,F,fieldF,finiteF,phi,f,g,hf,hg,hfg,hbad,hfield⟩

  -- The exact finite formula has the claimed rate curve and a vanishing error.
  have hLpos : 1 ≤ L := Nat.one_le_pow _ _ (by omega)
  have hJfloor : rho*(N : ℝ)-1 ≤ (J : ℝ) := (Nat.sub_one_lt_floor _).le
  have hbound := normalized_lengthening_lower N M a T0 J L rho
    (C*(M : ℝ)^(-theta)) (by dsimp [N]; positivity) (by dsimp [M]; positivity)
    hMN ha hLpos (by positivity) hseed hJfloor haeq
  have hU : ((N : ℝ)-M+a+T0-
      ((a : ℝ)*T0/M+Real.sqrt (((a : ℝ)/2)*Real.log (2*L)))) = U := by
    dsimp [U]
    rw [Nat.cast_sub hMN]
  dsimp only at hbound
  rw [hU,seed_size_ratio r d (by omega)] at hbound
  have hlog := selected_list_log_bound (alpha/8) (by linarith) d
  have hsqrt : Real.sqrt (Real.log (2*L)/(2*N)) ≤
      Real.sqrt ((((d : ℝ)^2+1)*Real.log 2)/(2*((2^d : ℕ) : ℝ))) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right hlog (by dsimp [N]; positivity)
  have herr := hError d hdError
  change C*(M : ℝ)^(-theta)+
      Real.sqrt ((((d : ℝ)^2+1)*Real.log 2)/(2*(N : ℝ)))+3/(2*(N : ℝ)) < epsilon at herr
  linarith

end BinaryFieldCounterexamples
