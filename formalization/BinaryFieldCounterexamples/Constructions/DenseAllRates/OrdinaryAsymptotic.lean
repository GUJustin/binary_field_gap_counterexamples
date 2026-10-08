/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.FinitePadding
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.ErrorBounds
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.PaddingBounds
/-!
# Uniform decoding-list dense all-rate asymptotics

Choose the literal middle-rank Gaussian population and pad its actual affine
seed list to the requested degree. The three floor errors, rank-restriction
error, and balanced-padding error are bounded by an explicit multiple of the
inverse fourth root. The list exponent is fixed before codimension, and the
error constant before rate, field, or domain. The finite argument already works
for every n at least four in the prescribed open rate interval.

This is the list-decoding clause only. A received pair, the first input of Lemma 3.13,
and an actual extension with the stated size bound remain separate obligations.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.DenseConstruction
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
/-- Three natural-floor errors suffice for the normalized balanced list bound. -/
theorem balanced_floor_fraction_lower (N K L : ℕ) (b a ρ err : ℝ)
    (hN:0<N) (hb:1≤b) (herr:0≤err)
    (hK:(K:ℝ)/N=a/b^2) (hKJ:K≤⌊ρ*N⌋₊) (hJN:⌊ρ*N⌋₊≤N) :
    let J:=⌊ρ*N⌋₊
    let T0:=⌊(N:ℝ)/b-err⌋₊
    let Δ:=Real.sqrt (((J-K:ℕ)/2:ℝ)*Real.log (2*L))
    let U:ℝ:=(J-K:ℕ)+T0-((J-K:ℕ)*T0/N+Δ)
    1/b+(ρ-a/b^2)*(1-1/b)-err/N-3/N-Δ/N≤(⌊U⌋₊:ℝ)/N := by
  dsimp only
  let J:=⌊ρ*N⌋₊
  let T0:=⌊(N:ℝ)/b-err⌋₊
  let Δ:=Real.sqrt (((J-K:ℕ)/2:ℝ)*Real.log (2*L))
  let U:ℝ:=(J-K:ℕ)+T0-((J-K:ℕ)*T0/N+Δ)
  have hNR:(0:ℝ)<N:=by exact_mod_cast hN
  have hJfloor:=Nat.lt_floor_add_one (ρ*(N:ℝ))
  have hTfloor:=Nat.lt_floor_add_one ((N:ℝ)/b-err)
  have hx:ρ-a/b^2-1/N≤((J-K:ℕ):ℝ)/N := by
    rw [Nat.cast_sub hKJ,sub_div,hK]
    have hh:ρ-1/N≤(J:ℝ)/N := by
      apply (le_div_iff₀ hNR).mpr
      dsimp [J]
      field_simp
      linarith
    linarith
  have hτ:1/b-(err/N+1/N)≤(T0:ℝ)/N := by
    apply (le_div_iff₀ hNR).mpr
    have hi:(1/b-(err/(N:ℝ)+1/N))*N=(N:ℝ)/b-err-1 := by field_simp; ring
    rw [hi]
    exact le_of_lt (by linarith)
  have hbase:=dense_balanced_padding_fraction_lower a b ρ (err/N+1/N) (1/N)
    N ((J-K:ℕ):ℝ) T0 Δ hb (by positivity) (by positivity) hNR (by positivity)
    (by exact_mod_cast (Nat.sub_le J K).trans hJN) hx hτ
  have hfloor:=Nat.lt_floor_add_one U
  have hround:U/N-1/N≤(⌊U⌋₊:ℝ)/N := by
    rw [←sub_div]
    exact (div_le_div_iff_of_pos_right hNR).mpr (by linarith)
  change 1/b+(ρ-a/b^2)*(1-1/b)-err/N-3/N-Δ/N≤(⌊U⌋₊:ℝ)/N
  have hi:(((J-K:ℕ):ℝ)+T0-((J-K:ℕ):ℝ)*T0/N-Δ)/N=U/N := by dsimp [U]; ring
  rw [hi] at hbase
  have hthree:(3:ℝ)/N=3*(1/N):=by ring
  rw [hthree]
  linarith
/-- The natural dense population is bounded by the exact rational list count. -/
theorem denseListCount_le_rational (b n t:ℕ) (hb:1<b) (ht:t≤n) :
    (denseQuadraticListCount b n t:ℚ)≤(b:ℚ)^(2*t)*((b:ℚ)^t-1)*
      quadraticGaussian (b^2) n t/(b-1) := by
  rw [quadraticGaussian_eq_gaussianPascal _ _ _ (Nat.one_lt_pow (by omega) hb) ht]
  have hp:1≤b^t:=Nat.one_le_pow _ _ (by omega)
  have hq:1≤b:=by omega
  have hdiv:(((b^t-1)/(b-1):ℕ):ℚ)≤((b:ℚ)^t-1)/(b-1) := by
    simpa only [Nat.cast_sub hp,Nat.cast_sub hq,Nat.cast_pow,Nat.cast_one] using
      (Nat.cast_div_le (α:=ℚ) (m:=b^t-1) (n:=b-1))
  dsimp [denseQuadraticListCount]
  push_cast
  have hh:=mul_le_mul_of_nonneg_left hdiv (by positivity : (0:ℚ)≤(b:ℚ)^(2*t))
  have hh':=mul_le_mul_of_nonneg_right hh (by positivity : (0:ℚ)≤gaussianPascal (b^2) n t)
  convert hh' using 1
  ring
/-- The inverse fourth root dominates the inverse size. -/
theorem inverse_size_le_inverse_fourth_root (N:ℕ) (hN:0<N) :
    (1:ℝ)/N≤1/Real.sqrt (Real.sqrt N) := by
  have hNR:(1:ℝ)≤N:=by exact_mod_cast hN
  have hs:Real.sqrt (Real.sqrt N)≤(N:ℝ) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [sq_nonneg ((N:ℝ)-1)]
  exact one_div_le_one_div_of_le (by positivity) hs
/-- The fourth-root notation agrees with the target real power. -/
theorem inverse_fourth_root_eq_rpow (N:ℕ) :
    1/Real.sqrt (Real.sqrt N)=(N:ℝ)^(-(1/4:ℝ)) := by
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul (by positivity)]
  norm_num
  rw [Real.rpow_neg (by positivity),one_div]
/-- Uniform dense-list constant: restriction, balanced padding, and three floors. -/
noncomputable def denseOrdinaryConstant (ell c:ℕ):ℝ :=
  (2:ℝ)^c*((2:ℝ)^ell-1)+
    Real.sqrt (((256*(ell+1)*2^c:ℕ):ℝ)/2)+3
/-- Actual dense decoding lists with the uniform fourth-root agreement error. -/
theorem binary_dense_ordinary_finite_exact (ell c n:ℕ) (hell:0<ell) (hc:c<ell) (hn:4≤n)
    (ρ:ℝ) (hρ:(2:ℝ)^c/((2:ℝ)^ell)^2<ρ)
    (hρ':ρ<1-(2:ℝ)^c/(2:ℝ)^ell+(2:ℝ)^c/((2:ℝ)^ell)^2)
    (B:Type*) [Field B] [Fintype B] [CharP B 2]
    (hcard:Fintype.card B=(2^ell)^(2*n)) (D:AddSubgroup B) (v:B)
    (hD:(additiveDomain D).card*2^c=Fintype.card B) :
    let S:=affineDomain (additiveDomain D) v
    let N:=S.card
    let J:=⌊ρ*N⌋₊
    let α:ℝ:=1/(2^ell:ℕ)+(ρ-(2:ℝ)^c/((2:ℝ)^ell)^2)*(1-1/(2^ell:ℕ))
    let L:=denseQuadraticListCount (2^ell) n (n/2)
    ∃T:ℕ, α-denseOrdinaryConstant ell c*(N:ℝ)^(-(1/4:ℝ))≤(T:ℝ)/N ∧
      (N:ℝ)^((1/(32*ell:ℝ))*Real.log N)≤L ∧ ordinaryList S J T L := by
  dsimp only
  let S:=affineDomain (additiveDomain D) v
  let N:=S.card
  let b:ℕ:=2^ell
  let a:ℕ:=2^c
  let K:=b^(2*n-2)
  let t:=n/2
  let J:=⌊ρ*N⌋₊
  let L:=denseQuadraticListCount b n t
  have hb:1<b:=Nat.one_lt_pow (by omega) (by decide)
  have ha:0<a:=by dsimp [a]; positivity
  have hNM:N*a=b^(2*n) := by
    dsimp [N,S,a,b]
    rw [affineDomain,Finset.card_image_iff.mpr (by
      intro x hx y hy hxy
      exact add_right_cancel hxy)]
    exact hD.trans hcard
  have hN:0<N:=by have hh:0<b^(2*n):=pow_pos (by omega) _; nlinarith only [hh, hNM]
  have hNR:(0:ℝ)<N:=by exact_mod_cast hN
  have hbR:(1:ℝ)<b:=by exact_mod_cast hb
  have haR:(0:ℝ)<a:=by exact_mod_cast ha
  have hρ0:(a:ℝ)/(b:ℝ)^2<ρ := by simpa only [a,b,Nat.cast_pow,Nat.cast_ofNat] using hρ
  have hρupper:ρ<1-(a:ℝ)/b+(a:ℝ)/(b:ℝ)^2 := by
    simpa only [a,b,Nat.cast_pow,Nat.cast_ofNat] using hρ'
  have hρ1:ρ<1 := by
    have hh:(a:ℝ)/(b:ℝ)^2<(a:ℝ)/b := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      exact mul_lt_mul_of_pos_left (by nlinarith only [hbR] : (b:ℝ)<(b:ℝ)^2) haR
    linarith
  have hKM:K*b^2=b^(2*n) := by
    dsimp [K]
    rw [←pow_add]
    congr 1
    omega
  have hKratio:(K:ℝ)/N=(a:ℝ)/(b:ℝ)^2 := by
    apply (div_eq_div_iff hNR.ne' (by positivity)).mpr
    have h1: (K:ℝ)*b^2=(b:ℝ)^(2*n):=by exact_mod_cast hKM
    have h2: (N:ℝ)*a=(b:ℝ)^(2*n):=by exact_mod_cast hNM
    linarith
  have hKJ:K≤J := by
    apply Nat.le_floor
    exact (div_le_iff₀ hNR).mp (hKratio ▸ hρ0.le)
  have hJN:J≤N := Nat.floor_le_of_le (by nlinarith only [hρ1, hNR] : ρ*(N:ℝ)≤N)
  have hNpow:N=2^(2*ell*n-c) := by
    have hexp:c≤ell*(2*n):=by nlinarith only [hc, hn]
    have hh:N=(2^ell)^(2*n)/2^c := Nat.eq_div_of_mul_eq_right (by positivity) (by simpa only [Nat.mul_comm] using hNM)
    rw [hh,←pow_mul,Nat.pow_div hexp (by decide)]
    rw [show ell*(2*n)=2*ell*n by ring]
  have hLbounds:=denseQuadraticListCount_binary_half_bounds ell n hell (by omega)
  have hLpos:0<L:=by
    have hh:0<2^(2*ell*(n/2)^2):=by positivity
    exact lt_of_lt_of_le hh hLbounds.1
  have hLrat:(L:ℚ)≤(b:ℚ)^(2*t)*((b:ℚ)^t-1)*quadraticGaussian (b^2) n t/(b-1) :=
    denseListCount_le_rational b n t hb (by dsimp [t]; omega)
  obtain ⟨w,E,hE,hprop⟩:=binary_dense_padded_list ell n t c (by omega) (by dsimp [t]; omega)
    (by dsimp [t]; omega) hc B hcard D v hD J L hKJ
    ((Nat.sub_le J K).trans hJN) hLrat
  let err:ℝ:=((b-1:ℕ):ℝ)*(2^(ell*(2*n-t)):ℕ)/b
  let T0:=⌊(N:ℝ)/b-err⌋₊
  let Δ:=Real.sqrt (((J-K:ℕ)/2:ℝ)*Real.log (2*L))
  let U:ℝ:=(J-K:ℕ)+T0-((J-K:ℕ)*T0/N+Δ)
  refine ⟨⌊U⌋₊,?_,?_,?_⟩
  · have hbase:=balanced_floor_fraction_lower N K L b a ρ err hN hbR.le (by dsimp [err]; positivity)
      hKratio hKJ hJN
    have hΔ:Δ/N≤Real.sqrt (((256*(ell+1)*2^c:ℕ):ℝ)/2)/Real.sqrt (Real.sqrt N) := by
      simpa only [hNpow] using dense_balanced_deviation_fourth_root ell n c (J-K) L hell
        (by omega) hLpos (by rw [←hNpow]; exact (Nat.sub_le J K).trans hJN) (le_refl L)
    have herr:err/N≤(a:ℝ)*(b-1)/Real.sqrt (Real.sqrt N) := by
      have hpow:2^(ell*(2*n-t))*b^t=b^(2*n) := by
        simp only [b,←pow_mul]
        rw [←pow_add]
        congr 1
        have ht:t≤2*n:=by dsimp [t]; omega
        rw [Nat.mul_sub_left_distrib,Nat.sub_add_cancel (Nat.mul_le_mul_left ell ht)]
      have herrEq:err/N=(a:ℝ)*(b-1)/(b:ℝ)^(t+1) := by
        dsimp [err]
        rw [Nat.cast_sub (by omega : 1≤b),Nat.cast_one,pow_succ]
        have h1:(2^(ell*(2*n-t)):ℕ)*(b:ℝ)^t=(b:ℝ)^(2*n):=by exact_mod_cast hpow
        have h2:(N:ℝ)*a=(b:ℝ)^(2*n):=by exact_mod_cast hNM
        field_simp
        nlinarith only [h1, h2]
      rw [herrEq]
      simpa only [a,b,t,hNpow,Nat.cast_pow,Nat.cast_ofNat] using
        dense_rank_error_le_inverse_fourth_root ell n c a
    have hi:=inverse_size_le_inverse_fourth_root N hN
    have hbound:err/N+3/N+Δ/N≤denseOrdinaryConstant ell c*(N:ℝ)^(-(1/4:ℝ)) := by
      rw [←inverse_fourth_root_eq_rpow]
      dsimp [denseOrdinaryConstant]
      have hthree:(3:ℝ)/N=3*(1/N):=by ring
      have haeq:(a:ℝ)=(2:ℝ)^c:=by simp [a]
      have hbeq:(b:ℝ)=(2:ℝ)^ell:=by simp [b]
      rw [hthree]
      rw [haeq,hbeq] at herr
      have hsum:=add_le_add (add_le_add herr (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤3))) hΔ
      convert hsum using 1
      ring
    have hbase':1/(b:ℝ)+(ρ-(a:ℝ)/(b:ℝ)^2)*(1-1/b)-(err/N+3/N+Δ/N)≤(⌊U⌋₊:ℝ)/N := by
      convert hbase using 1
      dsimp [U,T0,Δ,J]
      ring
    have hh:=le_trans (sub_le_sub_left hbound _) hbase'
    simpa only [a,b,Nat.cast_pow,Nat.cast_ofNat] using hh
  · exact binary_middle_rank_population_superpolynomial ell n c N L hell hn hNpow hLbounds.1
  · exact ordinaryList_of_real_bound S J L U w E hE hprop
/-- Actual dense decoding lists with the uniform fourth-root agreement error. -/
theorem binary_dense_ordinary_finite (ell c n:ℕ) (hell:0<ell) (hc:c<ell) (hn:4≤n)
    (ρ:ℝ) (hρ:(2:ℝ)^c/((2:ℝ)^ell)^2<ρ)
    (hρ':ρ<1-(2:ℝ)^c/(2:ℝ)^ell+(2:ℝ)^c/((2:ℝ)^ell)^2)
    (B:Type*) [Field B] [Fintype B] [CharP B 2]
    (hcard:Fintype.card B=(2^ell)^(2*n)) (D:AddSubgroup B) (v:B)
    (hD:(additiveDomain D).card*2^c=Fintype.card B) :
    let S:=affineDomain (additiveDomain D) v
    let N:=S.card
    let J:=⌊ρ*N⌋₊
    let α:ℝ:=1/(2^ell:ℕ)+(ρ-(2:ℝ)^c/((2:ℝ)^ell)^2)*(1-1/(2^ell:ℕ))
    ∃T L:ℕ, α-denseOrdinaryConstant ell c*(N:ℝ)^(-(1/4:ℝ))≤(T:ℝ)/N ∧
      (N:ℝ)^((1/(32*ell:ℝ))*Real.log N)≤L ∧ ordinaryList S J T L := by
  obtain ⟨T,hT,hL,hlist⟩:=binary_dense_ordinary_finite_exact ell c n hell hc hn ρ hρ hρ' B hcard D v hD
  exact ⟨T,denseQuadraticListCount (2^ell) n (n/2),hT,hL,hlist⟩
/-- Uniform list-decoding clause, with the exponent fixed before codimension
and the error constant fixed before the rate and affine domain. -/
theorem dense_ordinary_asymptotic (ell:ℕ) (hell:0<ell) :
    ∃A:ℝ,0<A ∧ ∀c:ℕ,c<ell→∃C:ℝ,0<C ∧ ∀ρ:ℝ,
      (2:ℝ)^c/((2:ℝ)^ell)^2<ρ→
      ρ<1-(2:ℝ)^c/(2:ℝ)^ell+(2:ℝ)^c/((2:ℝ)^ell)^2→
      ∃n0:ℕ,∀n:ℕ,n0≤n→∀(B:Type*) [Field B] [Fintype B] [CharP B 2],
      Fintype.card B=(2^ell)^(2*n)→∀(D:AddSubgroup B)(v:B),
      (additiveDomain D).card*2^c=Fintype.card B→
      let S:=affineDomain (additiveDomain D) v
      let N:=S.card
      let J:=⌊ρ*N⌋₊
      let α:ℝ:=1/(2^ell:ℕ)+(ρ-(2:ℝ)^c/((2:ℝ)^ell)^2)*(1-1/(2^ell:ℕ))
      ∃T L:ℕ,α-C*(N:ℝ)^(-(1/4:ℝ))≤(T:ℝ)/N ∧
        (N:ℝ)^(A*Real.log N)≤L ∧ ordinaryList S J T L := by
  refine ⟨1/(32*ell:ℝ),by positivity,?_⟩
  intro c hc
  refine ⟨denseOrdinaryConstant ell c,?_,?_⟩
  · have hp:0≤(2:ℝ)^ell-1:=sub_nonneg.mpr (one_le_pow₀ (by norm_num))
    have hm:=mul_nonneg (show (0:ℝ)≤2^c by positivity) hp
    have hs:=Real.sqrt_nonneg (((256*(ell+1)*2^c:ℕ):ℝ)/2)
    dsimp [denseOrdinaryConstant]
    linarith
  · intro ρ hρ hρ'
    refine ⟨4,?_⟩
    intro n hn B _ _ _ hcard D v hD
    exact binary_dense_ordinary_finite ell c n hell hc hn ρ hρ hρ' B hcard D v hD
end BinaryFieldCounterexamples.DenseConstruction
