/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.OrdinaryPolePair
/-!
# Dense decoding lists and received pairs with exact individual agreement

The actual padded middle-rank list is kept at its exact Gaussian size.
A pole field of extension degree 8n+8 separates all its challenges, and the further
quadratic conversion gives both individual agreements and common
agreement exactly J. The final field has binary exponent at most 40 ell n²,
which is bounded by N raised to a fixed multiple of log N. The decoding list
and pair use the same threshold and uniform constants, fixed in the original
quantifier order.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.DenseConstruction
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
/-- A pole extension of degree linear in the quadratic dimension separates the
entire chosen middle-rank list. -/
theorem dense_pole_field_capacity (ell n N J:ℕ) (hell:0<ell) (hn:4≤n)
    (hN:N≤(2^ell)^(2*n)) (hJ:J≤N) :
    N+J*(denseQuadraticListCount (2^ell) n (n/2))^2<
      ((2^ell)^(2*n))^(8*n+8) := by
  let U:=n+ell*(4*n^2+2)
  let M:=(2^ell)^(2*n)
  let L:=denseQuadraticListCount (2^ell) n (n/2)
  have hL:L≤2^U:=(denseQuadraticListCount_binary_half_bounds ell n hell (by omega)).2
  have hL2:L^2≤2^(2*U) := by
    simpa only [←pow_mul,Nat.mul_comm U 2] using Nat.pow_le_pow_left hL 2
  have hone:1≤2^(2*U):=Nat.one_le_pow _ _ (by omega)
  calc
    N+J*L^2≤M+M*2^(2*U) := Nat.add_le_add hN (Nat.mul_le_mul (hJ.trans hN) hL2)
    _≤2*M*2^(2*U) := by nlinarith
    _=2^(1+ell*(2*n)+2*U) := by dsimp [M]; rw [pow_add,pow_add,pow_one,←pow_mul]
    _<2^(ell*(2*n)*(8*n+8)) := by
      apply Nat.pow_lt_pow_right (by decide : 1<2)
      dsimp [U]
      nlinarith [Nat.mul_le_mul_left ell (by nlinarith : 4≤n^2)]
    _=((2^ell)^(2*n))^(8*n+8) := by rw [pow_mul,pow_mul]
/-- The final quadratic extension has a uniform quadratic binary exponent. -/
theorem dense_final_field_binary_bound (ell n:ℕ) (hn:4≤n) :
    (((2^ell)^(2*n))^(2*(8*n+8)))≤2^(40*ell*n^2) := by
  simp only [←pow_mul]
  apply Nat.pow_le_pow_right (by decide : 0<2)
  have hh:4*n≤n^2:=by nlinarith
  linarith [Nat.mul_le_mul_left ell hh]
/-- Quadratic binary field growth is quasipolynomial in the prescribed dense
domain size, with a constant fixed before the rate. -/
theorem dense_final_field_real_bound (ell c n N F:ℕ) (hell:0<ell) (hc:c<ell)
    (hn:4≤n) (hN:N=2^(2*ell*n-c)) (hF:F≤2^(40*ell*n^2)) :
    (F:ℝ)≤(N:ℝ)^((40*ell:ℝ)/Real.log 2*Real.log N) := by
  let d:=2*ell*n-c
  have hd:n≤d:=by
    have hh:n+c≤2*ell*n:=by nlinarith [Nat.mul_le_mul_left ell (show 1≤n by omega)]
    dsimp [d]
    omega
  have hsq:n^2≤d^2:=Nat.pow_le_pow_left hd 2
  have hexp:40*ell*n^2≤40*ell*d^2:=Nat.mul_le_mul_left _ hsq
  have hlog:Real.log (N:ℝ)=(d:ℝ)*Real.log 2 := by
    rw [hN]
    push_cast
    exact Real.log_pow 2 d
  have hNpos:(0:ℝ)<N:=by rw [hN]; positivity
  have hlog2pos:0<Real.log 2:=Real.log_pos (by norm_num)
  calc
    (F:ℝ)≤(2^(40*ell*n^2):ℕ):=by exact_mod_cast hF
    _=Real.exp ((40*ell*n^2:ℕ)*Real.log 2) := by
      norm_num only [Nat.cast_pow,Nat.cast_ofNat]
      rw [←Real.log_pow,Real.exp_log]
      positivity
    _≤Real.exp ((40*ell*d^2:ℕ)*Real.log 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hexp) hlog2pos.le
    _=(N:ℝ)^((40*ell:ℝ)/Real.log 2*Real.log N) := by
      rw [Real.rpow_def_of_pos hNpos,hlog]
      congr 1
      push_cast
      field_simp
/-- The same padded list supplies a received pair over a genuine finite
extension, with exact individual and common agreement and no challenge lost. -/
theorem binary_dense_pair_finite (ell c n:ℕ) (hell:0<ell) (hc:c<ell) (hn:4≤n)
    (ρ:ℝ) (hρ:(2:ℝ)^c/((2:ℝ)^ell)^2<ρ)
    (hρ':ρ<1-(2:ℝ)^c/(2:ℝ)^ell+(2:ℝ)^c/((2:ℝ)^ell)^2)
    (B:Type) [Field B] [Fintype B] [CharP B 2]
    (hcard:Fintype.card B=(2^ell)^(2*n)) (D:AddSubgroup B) (v:B)
    (hD:(additiveDomain D).card*2^c=Fintype.card B) :
    let S:=affineDomain (additiveDomain D) v
    let N:=S.card
    let J:=⌊ρ*N⌋₊
    let α:ℝ:=1/(2^ell:ℕ)+(ρ-(2:ℝ)^c/((2:ℝ)^ell)^2)*(1-1/(2^ell:ℕ))
    ∃T L:ℕ,α-denseOrdinaryConstant ell c*(N:ℝ)^(-(1/4:ℝ))≤(T:ℝ)/N ∧
      (N:ℝ)^((1/(32*ell:ℝ))*Real.log N)≤L ∧ ordinaryList S J T L ∧
      ∃(F:Type)(fieldF:Field F)(finiteF:Fintype F),
      letI:=fieldF
      letI:=finiteF
      ∃φ:B→+*F,∃f g:mappedDomain φ S→F,
        agreementEQ (mappedDomain φ S) J f J ∧ agreementEQ (mappedDomain φ S) J g J ∧
        commonAgreementEQ (mappedDomain φ S) J f g J ∧
        L≤(nonzeroBadChallenges (mappedDomain φ S) J f g T).card ∧
        (Fintype.card F:ℝ)≤(N:ℝ)^((40*ell:ℝ)/Real.log 2*Real.log N) := by
  dsimp only
  let S:=affineDomain (additiveDomain D) v
  let N:=S.card
  let J:=⌊ρ*N⌋₊
  let L:=denseQuadraticListCount (2^ell) n (n/2)
  obtain ⟨T,hT,hL,hlist⟩:=binary_dense_ordinary_finite_exact ell c n hell hc hn ρ hρ hρ' B hcard D v hD
  refine ⟨T,L,hT,hL,hlist,?_⟩
  obtain ⟨w,E,hLE,hprop⟩:=hlist
  obtain ⟨I,hIE,hI⟩:=Finset.exists_subset_card_eq hLE
  have hNM:N*2^c=(2^ell)^(2*n) := by
    dsimp [N,S]
    rw [affineDomain,Finset.card_image_iff.mpr (by
      intro x hx y hy hxy
      exact add_right_cancel hxy)]
    exact hD.trans hcard
  have hNMle:N≤(2^ell)^(2*n) := by
    have ha:1≤2^c:=Nat.one_le_pow _ _ (by omega)
    exact (le_mul_of_one_le_right (Nat.zero_le N) ha).trans_eq hNM
  have hρ1:ρ<1 := by
    have hb:1<(2:ℝ)^ell:=one_lt_pow₀ (by norm_num) (by omega)
    have ha:(0:ℝ)<2^c:=by positivity
    have hh:(2:ℝ)^c/((2:ℝ)^ell)^2<(2:ℝ)^c/(2:ℝ)^ell := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      exact mul_lt_mul_of_pos_left (by
        rw [pow_two]
        exact lt_mul_of_one_lt_right (lt_trans zero_lt_one hb) hb) ha
    linarith
  have hJN:J≤N:=Nat.floor_le_of_le
    (mul_le_of_le_one_left (Nat.cast_nonneg N) hρ1.le)
  obtain ⟨F,fieldF,finiteF,φ,hF,f,g,hf,hg,hfg,hcount⟩:=ordinary_family_extension_pair
    B S w I J T (8*n+8) (by omega) (fun p hp=>hprop p (hIE hp)) hJN
    (by rw [hI,hcard]; exact dense_pole_field_capacity ell n N J hell hn hNMle hJN)
  let :=fieldF
  let :=finiteF
  refine ⟨F,fieldF,finiteF,φ,f,g,hf,hg,hfg,?_,?_⟩
  · simpa only [hI] using hcount
  · have hNpow:N=2^(2*ell*n-c) := by
      have hexp:c≤ell*(2*n):=hc.le.trans
        (le_mul_of_one_le_right (Nat.zero_le ell) (by omega))
      have hh:N=(2^ell)^(2*n)/2^c:=Nat.eq_div_of_mul_eq_right (by positivity)
        (by simpa only [Nat.mul_comm] using hNM)
      rw [hh,←pow_mul,Nat.pow_div hexp (by decide)]
      rw [show ell*(2*n)=2*ell*n by ring]
    apply dense_final_field_real_bound ell c n N _ hell hc hn hNpow
    rw [hF,hcard]
    exact dense_final_field_binary_bound ell n hn
/-- Uniform dense all-rate construction with decoding lists and actual
finite-extension received pairs, sharing the same constants and threshold. -/
theorem dense_ordinary_and_pair_asymptotic (ell:ℕ) (hell:0<ell) :
    ∃A:ℝ,0<A ∧ ∀c:ℕ,c<ell→∃C:ℝ,0<C ∧ ∀ρ:ℝ,
      (2:ℝ)^c/((2:ℝ)^ell)^2<ρ→
      ρ<1-(2:ℝ)^c/(2:ℝ)^ell+(2:ℝ)^c/((2:ℝ)^ell)^2→
      ∃n0:ℕ,∀n:ℕ,n0≤n→∀(B:Type) [Field B] [Fintype B] [CharP B 2],
      Fintype.card B=(2^ell)^(2*n)→∀(D:AddSubgroup B)(v:B),
      (additiveDomain D).card*2^c=Fintype.card B→
      let S:=affineDomain (additiveDomain D) v
      let N:=S.card
      let J:=⌊ρ*N⌋₊
      let α:ℝ:=1/(2^ell:ℕ)+(ρ-(2:ℝ)^c/((2:ℝ)^ell)^2)*(1-1/(2^ell:ℕ))
      ∃T L:ℕ,α-C*(N:ℝ)^(-(1/4:ℝ))≤(T:ℝ)/N ∧
        (N:ℝ)^(A*Real.log N)≤L ∧ ordinaryList S J T L ∧
        ∃(F:Type)(fieldF:Field F)(finiteF:Fintype F),
        letI:=fieldF
        letI:=finiteF
        ∃φ:B→+*F,∃f g:mappedDomain φ S→F,
          agreementEQ (mappedDomain φ S) J f J ∧ agreementEQ (mappedDomain φ S) J g J ∧
          commonAgreementEQ (mappedDomain φ S) J f g J ∧
          (N:ℝ)^(A*Real.log N)≤(nonzeroBadChallenges (mappedDomain φ S) J f g T).card ∧
          (Fintype.card F:ℝ)≤(N:ℝ)^(C*Real.log N) := by
  refine ⟨1/(32*ell:ℝ),by positivity,?_⟩
  intro c hc
  let C0:=denseOrdinaryConstant ell c
  let C1:ℝ:=(40*ell:ℝ)/Real.log 2
  have hC0:0<C0 := by
    have hp:0≤(2:ℝ)^ell-1:=sub_nonneg.mpr (one_le_pow₀ (by norm_num))
    have hm:=mul_nonneg (show (0:ℝ)≤2^c by positivity) hp
    have hs:=Real.sqrt_nonneg (((256*(ell+1)*2^c:ℕ):ℝ)/2)
    dsimp [C0,denseOrdinaryConstant]
    linarith
  have hC1:0<C1:=by dsimp [C1]; exact div_pos (by positivity) (Real.log_pos (by norm_num))
  refine ⟨C0+C1,by positivity,?_⟩
  intro ρ hρ hρ'
  refine ⟨4,?_⟩
  intro n hn B _ _ _ hcard D v hD
  dsimp only
  let S:=affineDomain (additiveDomain D) v
  let N:=S.card
  obtain ⟨T,L,hT,hL,hlist,F,fieldF,finiteF,φ,f,g,hf,hg,hfg,hcount,hsize⟩:=
    binary_dense_pair_finite ell c n hell hc hn ρ hρ hρ' B hcard D v hD
  let :=fieldF
  let :=finiteF
  refine ⟨T,L,?_,hL,hlist,F,fieldF,finiteF,φ,f,g,hf,hg,hfg,?_,?_⟩
  · apply le_trans _ hT
    apply sub_le_sub_left
    exact mul_le_mul_of_nonneg_right (by dsimp [C0]; linarith)
      (Real.rpow_nonneg (by positivity) _)
  · exact hL.trans (by exact_mod_cast hcount)
  · have hNpos:0<N := by
      have hDpos:0<(additiveDomain D).card := by
        have hh:=Fintype.card_pos (α:=B)
        by_contra hz
        have hz0:(additiveDomain D).card=0:=by omega
        rw [hz0,zero_mul] at hD
        omega
      dsimp [N,S]
      rw [affineDomain,Finset.card_image_iff.mpr (by
        intro x hx y hy hxy
        exact add_right_cancel hxy)]
      exact hDpos
    have hN1:(1:ℝ)≤N:=by exact_mod_cast hNpos
    apply hsize.trans
    apply Real.rpow_le_rpow_of_exponent_le hN1
    exact mul_le_mul_of_nonneg_right (by dsimp [C1]; linarith)
      (Real.log_nonneg hN1)
end BinaryFieldCounterexamples.DenseConstruction
