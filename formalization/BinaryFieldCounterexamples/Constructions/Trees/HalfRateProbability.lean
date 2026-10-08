/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.TreeAsymptotics
public import BinaryFieldCounterexamples.Counting.CollisionAsymptotics
public import BinaryFieldCounterexamples.Constructions.Trees.DomainPair
public import BinaryFieldCounterexamples.Constructions.Trees.HalfAgreementAsymptotic
public import Mathlib.Algebra.Algebra.ZMod
/-!
# Fixed-height probability bounds for avoiding tree supports

The finite collision theorem implies the manuscript probability and large-field
count bounds once supplied as an explicit premise. This keeps the asymptotic
argument independent of the finite construction assembly.
-/
@[expose] public section

namespace BinaryFieldCounterexamples
set_option maxHeartbeats 800000
universe u

/-- Theorem 6.10: the avoiding-family collision energy is nonnegative and
satisfies the quadratic bound needed for second-moment averaging, including
the height-two remark following the theorem. -/
theorem avoiding_tree_energy_bounds (d h M : ℕ) (hh : 2≤h)
    (hd : 2^h-1≤d) (hM : 1≤M) :
    let N : ℕ := 2^d
    let K : ℕ := N/2
    let w : ℕ := N/2^(h+1)
    let E : ℚ := (((K:ℚ)-w-(K:ℚ)^2/(N-w))*M^2+w*M)/2
    0≤E ∧ E≤(N:ℚ)*M^2/4 := by
  dsimp only
  have hh1d : h+1≤d := by
    have hp : h+2≤2^h := by
      induction h,hh using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
        rw [pow_succ]
        have hp : 1≤2^n := Nat.one_le_pow _ _ (by decide)
        omega
    omega
  have hd1 : 1≤d := by omega
  have hhalf : (((2^d/2:ℕ):ℚ))=(2^d:ℕ)/2 := by
    rw [Nat.pow_div hd1 (by decide),Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat]
    rw [show d=(d-1)+1 by omega,pow_succ]
    norm_num
  have hw : (((2^d/2^(h+1):ℕ):ℚ))=(2^d:ℕ)/(2:ℚ)^(h+1) := by
    rw [Nat.pow_div hh1d (by decide),Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat]
    apply (eq_div_iff (by positivity : (2:ℚ)^(h+1)≠0)).mpr
    rw [←pow_add,Nat.sub_add_cancel hh1d]
  have hw8 : (((2^d/2^(h+1):ℕ):ℚ))≤(2^d:ℕ)/8 := by
    rw [hw]
    have hpN : (8:ℕ)≤2^(h+1) := by
      rw [show 8=2^3 by norm_num]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hp : (8:ℚ)≤2^(h+1) := by exact_mod_cast hpN
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hp
  have hwN : 2^d/2^(h+1)≤2^d := Nat.div_le_self _ _
  have hdenN : 0<2^d-2^d/2^(h+1) := by
    have hstrict : 2^d/2^(h+1)<2^d := by
      apply Nat.div_lt_self (by positivity)
      have : 1<2^(h+1) := one_lt_pow₀ (by decide) (by omega)
      exact this
    omega
  have hden : (0:ℚ)<(2^d:ℕ)-(2^d/2^(h+1):ℕ) := by
    rw [←Nat.cast_sub hwN]
    exact_mod_cast hdenN
  rw [hhalf]
  let n : ℚ := (2^d:ℕ)
  let w : ℚ := (2^d/2^(h+1):ℕ)
  have hn : 0<n := by dsimp [n]; positivity
  have hw0 : 0≤w := by dsimp [w]; positivity
  have hwn : w≤n/8 := by exact hw8
  have hden' : 0<n-w := by simpa [n,w] using hden
  have hkw : 0≤n/2-w := by linarith
  have hprod : (n/2)^2≤(n/2-w)*(n-w) := by
    have haux : 0≤(n-4*w)*(n-4*w) := by simpa [pow_two] using sq_nonneg (n-4*w)
    nlinarith
  have hcoeff : 0≤n/2-w-(n/2)^2/(n-w) := by
    apply (sub_nonneg.mpr ((div_le_iff₀ hden').mpr ?_))
    linarith
  have hcoeffU : n/2-w-(n/2)^2/(n-w)≤n/2-w := by
    exact sub_le_self _ (div_nonneg (sq_nonneg _) hden'.le)
  have hMR : (1:ℚ)≤M := by exact_mod_cast hM
  constructor
  · positivity
  · have hterm : (n/2-w-(n/2)^2/(n-w))*(M:ℚ)^2+w*M≤n/2*(M:ℚ)^2 := by
      have hmul := mul_le_mul_of_nonneg_right hcoeffU (sq_nonneg (M:ℚ))
      have hwM : w*(M:ℚ)≤w*(M:ℚ)^2 := by
        linarith [mul_nonneg hw0 (mul_nonneg (show (0:ℚ)≤M by positivity) (sub_nonneg.mpr hMR))]
      linarith
    dsimp [n,w] at hterm ⊢
    linarith

/-- Theorem 6.10 and its height-two remark: the exact finite avoiding-tree
theorem implies its fixed-height probability consequence, keeping the common
and individual agreement guarantees for the same pair. -/
theorem half_rate_decision_trees_probability_of_finite
    (hfinite : ∀ {F : Type u} [Field F] [Fintype F] [CharP F 2]
      (D : AddSubgroup F) (d h : ℕ) (hh : 2 ≤ h) (hd : 2 ^ h - 1 ≤ d)
      (hD : (additiveDomain D).card = 2 ^ d) (hq : 2 ^ d < Fintype.card F),
      let N : ℕ := 2 ^ d
      let K : ℕ := N / 2
      let w : ℕ := N / 2 ^ (h + 1)
      let M : ℕ := avoidingTreeSupportCount h d
      let q : ℕ := Fintype.card F
      let E : ℚ := (((K : ℚ) - w - (K : ℚ) ^ 2 / (N - w)) * M ^ 2 + w * M) / 2
      let A := additiveDomain D
      ∃ f g : A → F,
        commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
        agreementLE A K f (K + w - 1) ∧
        max (M - ⌊E / (q - N)⌋₊)
          ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E)⌉₊ ≤
          (nonzeroBadChallenges A K f g (K + w)).card)
    (h : ℕ) (hh : 2≤h) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ (d : ℕ), d₀ ≤ d → 2 ^ h - 1 ≤ d →
      ∀ (F : Type u) [Field F] [Fintype F] [CharP F 2]
        (D : AddSubgroup F),
        (additiveDomain D).card = 2 ^ d → 2 ^ d < Fintype.card F →
        let A := additiveDomain D
        let N : ℕ := 2 ^ d
        let q : ℕ := Fintype.card F
        let K : ℕ := N / 2
        ∃ f g : A → F,
          commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
          agreementLE A K f (K + N / 2 ^ (h + 1) - 1) ∧
          c * min ((N : ℝ) ^ (2 ^ h - h - 1) / q) (1 / N) ≤
            ((nonzeroBadChallenges A K f g (K + N / 2 ^ (h + 1))).card : ℝ) / q ∧
          (N * avoidingTreeSupportCount h d ≤ q →
            c * avoidingTreeSupportCount h d ≤
              ((nonzeroBadChallenges A K f g (K + N / 2 ^ (h + 1))).card : ℝ)) := by
  obtain ⟨a,C,ha,hC,dg,hgrowth⟩ := avoidingTreeSupportCount_growth h (by omega)
  obtain ⟨d₁,hd₁⟩ := pow_unbounded_of_one_lt (1/a) (by norm_num : (1:ℝ)<2)
  let a₀ : ℝ := min a 1
  have ha₀ : 0<a₀ := lt_min ha (by norm_num)
  refine ⟨a₀/3,by positivity,max dg d₁,?_⟩
  intro d hd hdheight F _ _ _ D hD hq
  let N : ℕ := 2^d
  let K : ℕ := N/2
  let w : ℕ := N/2^(h+1)
  let M : ℕ := avoidingTreeSupportCount h d
  let q : ℕ := Fintype.card F
  let E : ℚ := (((K:ℚ)-w-(K:ℚ)^2/(N-w))*M^2+w*M)/2
  have hdg : dg≤d := (le_max_left _ _).trans hd
  have hd₁d : d₁≤d := (le_max_right _ _).trans hd
  obtain ⟨hMlower,hMupper⟩ := hgrowth d hdg
  have hexp : 0<2^h-h-1 := by
    have hp : h+2≤2^h := by
      have hlt := Nat.lt_two_pow_self (n:=h-1)
      have hx2 : 2≤2^(h-1) := by
        rw [show 2=2^1 by norm_num]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      rw [show h=(h-1)+1 by omega,pow_succ]
      omega
    omega
  have hpowd : (2:ℝ)^d≤((2:ℝ)^d)^(2^h-h-1) :=
    le_self_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) (Nat.ne_of_gt hexp)
  have hMoneR : (1:ℝ)<M := by
    calc
      (1:ℝ)=a*(1/a) := by field_simp
      _ < a*(2:ℝ)^d₁ := mul_lt_mul_of_pos_left hd₁ ha
      _ ≤ a*(2:ℝ)^d := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hd₁d) ha.le
      _ ≤ a*((2:ℝ)^d)^(2^h-h-1) := mul_le_mul_of_nonneg_left hpowd ha.le
      _ ≤ M := hMlower
  have hMone : 1≤M := by exact_mod_cast hMoneR.le
  have hMpos : 0<M := by omega
  have hNpos : 0<N := by dsimp [N]; positivity
  have hqpos : 0<q := lt_of_lt_of_le hNpos (Nat.le_of_lt hq)
  have hq2 : 2*N≤q := by
    dsimp [N,q]
    exact two_mul_pow_le_card_of_charTwo d hq
  have henergy := avoiding_tree_energy_bounds d h M hh hdheight hMone
  have henergy' : 0≤E ∧ E≤(N:ℚ)*M^2/4 := by
    simpa only [N,K,w,E] using henergy
  obtain ⟨f,g,hcommon,hg,hf,hbad⟩ := hfinite D d h hh hdheight hD hq
  have hceil : ⌈(q-N:ℚ)*M^2/((q-N)*M+2*E)⌉₊≤
      (nonzeroBadChallenges (additiveDomain D) K f g (K+w)).card :=
    (le_max_right _ _).trans hbad
  have hcollision := one_third_min_real_le_of_second_moment N M q
    (nonzeroBadChallenges (additiveDomain D) K f g (K+w)).card E
    hNpos hMpos hq2 henergy'.1 henergy'.2 hceil
  have ha₀a : a₀≤a := min_le_left _ _
  have ha₀one : a₀≤1 := min_le_right _ _
  have ha₀nonneg : 0≤a₀ := ha₀.le
  have hscale : a₀*min ((N:ℝ)^(2^h-h-1)/(q:ℝ)) (1/(N:ℝ))≤
      min ((M:ℝ)/(q:ℝ)) (1/(N:ℝ)) := by
    apply le_min
    · calc
        _ ≤ a₀*((N:ℝ)^(2^h-h-1)/(q:ℝ)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) ha₀nonneg
        _ ≤ a*((N:ℝ)^(2^h-h-1)/(q:ℝ)) :=
          mul_le_mul_of_nonneg_right ha₀a (by positivity)
        _ = (a*((N:ℝ)^(2^h-h-1)))/(q:ℝ) := by ring
        _ ≤ (M:ℝ)/(q:ℝ) := div_le_div_of_nonneg_right
          (by simpa [N] using hMlower) (by positivity)
    · calc
        _ ≤ 1*min ((N:ℝ)^(2^h-h-1)/(q:ℝ)) (1/(N:ℝ)) :=
          mul_le_mul_of_nonneg_right ha₀one (by positivity)
        _ ≤ 1/(N:ℝ) := by simpa only [one_mul] using
          (min_le_right ((N:ℝ)^(2^h-h-1)/(q:ℝ)) (1/(N:ℝ)))
  have hminform : min ((M:ℝ)/(q:ℝ)) (1/(N:ℝ))=
      min (M:ℝ) ((q:ℝ)/N)/(q:ℝ) := by
    rw [←min_div_div_right (show (0:ℝ)≤q by positivity)]
    congr 1
    field_simp
  have hprob : a₀/3*min ((N:ℝ)^(2^h-h-1)/(q:ℝ)) (1/(N:ℝ))≤
      ((nonzeroBadChallenges (additiveDomain D) K f g (K+w)).card:ℝ)/(q:ℝ) := by
    calc
      _ = (1/3:ℝ)*(a₀*min ((N:ℝ)^(2^h-h-1)/(q:ℝ)) (1/(N:ℝ))) := by ring
      _ ≤ (1/3:ℝ)*min ((M:ℝ)/(q:ℝ)) (1/(N:ℝ)) :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = ((1/3:ℝ)*min (M:ℝ) ((q:ℝ)/N))/(q:ℝ) := by rw [hminform]; ring
      _ ≤ _ := div_le_div_of_nonneg_right hcollision (by positivity)
  refine ⟨f,g,hcommon,hg,hf,hprob,?_⟩
  intro hlarge
  have hMq : (M:ℝ)≤(q:ℝ)/N := by
    apply (le_div_iff₀ (by exact_mod_cast hNpos)).mpr
    have hlarge' : M*N≤q := by simpa [N,M,q,Nat.mul_comm] using hlarge
    exact_mod_cast hlarge'
  have hcM : a₀/3*(M:ℝ)≤(1/3:ℝ)*(M:ℝ) := by
    exact mul_le_mul_of_nonneg_right (by linarith [ha₀one]) (by positivity)
  calc
    a₀/3*(M:ℝ)≤(1/3:ℝ)*(M:ℝ) := hcM
    _ = (1/3:ℝ)*min (M:ℝ) ((q:ℝ)/N) := by rw [min_eq_left hMq]
    _ ≤ _ := hcollision

end BinaryFieldCounterexamples
