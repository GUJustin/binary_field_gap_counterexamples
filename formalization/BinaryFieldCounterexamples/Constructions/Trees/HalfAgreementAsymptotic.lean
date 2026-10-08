/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.DomainPair
public import BinaryFieldCounterexamples.Constructions.Trees.TemplateCounts
public import BinaryFieldCounterexamples.Counting.CollisionAsymptotics
public import BinaryFieldCounterexamples.Counting.TreeWholeGrowth
public import Mathlib.Algebra.Algebra.ZMod
/-!
# Fixed-height asymptotics for whole-domain tree supports

The exact finite collision count implies a uniform constant times the smaller
of the support population scale and the exterior field budget.
-/
@[expose] public section

namespace BinaryFieldCounterexamples

open scoped BigOperators
set_option maxHeartbeats 800000

/-- The whole-tree collision energy is nonnegative and at most the quadratic bound
needed by the second-moment estimate. -/
theorem tree_collision_energy_bounds (d h M : ℕ) (hh : 2 ≤ h)
    (hd : 2^h-1 ≤ d) (hM : 3 ≤ M) :
    let N : ℕ := 2^d
    let K : ℕ := N/2-N/2^(h+1)
    let E : ℚ := (K:ℚ)*M.choose 2-(N:ℚ)*(M/2).choose 2
    0 ≤ E ∧ E ≤ (N:ℚ)*M^2/4 := by
  dsimp only
  have hd3 : 3 ≤ d := by
    have hp : 4 ≤ 2^h := by
      calc 4=2^2 := by norm_num
           _≤_ := Nat.pow_le_pow_right (by decide) hh
    omega
  have hh1d : h+1 ≤ d := by
    have hs0 : h+2 ≤ 2^h := by
      induction h, hh using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
        rw [pow_succ]
        omega
    have hs : h+1 ≤ 2^h-1 := by omega
    omega
  have hhalf : (((2^d/2:ℕ):ℚ))=(2^d:ℕ)/2 := by
    rw [Nat.pow_div (show 1≤d by omega) (by decide),Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat]
    rw [show d=(d-1)+1 by omega,pow_succ]
    norm_num
  have hw : (((2^d/2^(h+1):ℕ):ℚ))=(2^d:ℕ)/(2:ℚ)^(h+1) := by
    rw [Nat.pow_div hh1d (by decide),Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat]
    apply (eq_div_iff (by positivity : (2:ℚ)^(h+1)≠0)).mpr
    rw [←pow_add,Nat.sub_add_cancel hh1d]
  have hw8 : (((2^d/2^(h+1):ℕ):ℚ)) ≤ (2^d:ℕ)/8 := by
    rw [hw]
    have hp : (8:ℚ) ≤ 2^(h+1) := by
      have hpN : (8:ℕ) ≤ 2^(h+1) := by
        rw [show 8=2^3 by norm_num]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      exact_mod_cast hpN
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hp
  have hpden : (2:ℕ) ≤ 2^(h+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
      (show 1 ≤ h+1 by omega)
  have hsub : 2^d/2^(h+1) ≤ 2^d/2 :=
    Nat.div_le_div_left hpden (by decide)
  have hK : (3:ℚ)*(2^d:ℕ)/8 ≤ ((2^d/2-2^d/2^(h+1):ℕ):ℚ) := by
    rw [Nat.cast_sub hsub,hhalf]
    calc
      _ = ((2^d:ℕ):ℚ)/2 - ((2^d:ℕ):ℚ)/8 := by ring
      _ ≤ _ := sub_le_sub_left hw8 _
  have hKupper : (((2^d/2-2^d/2^(h+1):ℕ):ℚ)) ≤ (2^d:ℕ)/2 := by
    rw [Nat.cast_sub hsub,hhalf]
    exact sub_le_self _ (by positivity)
  have hm2 : (((M/2:ℕ):ℚ)) ≤ (M:ℚ)/2 := by
    have hn : 2*(M/2)≤M := by omega
    apply (le_div_iff₀ (by norm_num : (0:ℚ)<2)).2
    exact_mod_cast (show (M/2)*2≤M by omega)
  rw [Nat.cast_choose_two ℚ,Nat.cast_choose_two ℚ]
  have hM0 : (0:ℚ)≤M := by positivity
  have hm20 : (0:ℚ)≤(M/2:ℕ) := by positivity
  have hM1 : (1:ℚ)≤M := by exact_mod_cast (show 1≤M by omega)
  have hm21 : (1:ℚ)≤(M/2:ℕ) := by exact_mod_cast (show 1≤M/2 by omega)
  have hchooseM0 : (0:ℚ)≤(M:ℚ)*((M:ℚ)-1)/2 := by positivity
  have hchooseHalf0 : (0:ℚ)≤(M/2:ℕ)*((M/2:ℕ)-1)/2 := by positivity
  constructor
  · have hfirst : (3*(2^d:ℕ)/8)*((M:ℚ)*((M:ℚ)-1)/2) ≤
        (((2^d/2-2^d/2^(h+1):ℕ):ℚ))*((M:ℚ)*((M:ℚ)-1)/2) :=
      mul_le_mul_of_nonneg_right hK hchooseM0
    have hsquare : ((M/2:ℕ):ℚ)*((M/2:ℕ)-1) ≤ (M:ℚ)^2/4 := by
      exact (mul_le_mul hm2 ((sub_le_self _ zero_le_one).trans hm2)
        (sub_nonneg.mpr hm21) (div_nonneg hM0 (by norm_num))).trans_eq (by ring)
    have hsecond : ((2^d:ℕ):ℚ)*(((M/2:ℕ):ℚ)*((M/2:ℕ)-1)/2) ≤
        ((2^d:ℕ):ℚ)*(M:ℚ)^2/8 := by
      exact (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hsquare (by norm_num))
        (Nat.cast_nonneg _)).trans_eq (by ring)
    have hmain : ((2^d:ℕ):ℚ)*(M:ℚ)^2/8 ≤
        (3*(2^d:ℕ)/8)*((M:ℚ)*((M:ℚ)-1)/2) := by
      have hMM : 0 ≤ (M:ℚ)*((M:ℚ)-3) :=
        mul_nonneg hM0 (sub_nonneg.mpr (by exact_mod_cast hM))
      apply sub_nonneg.mp
      calc
        _ = ((2^d:ℕ):ℚ) * ((M:ℚ)*((M:ℚ)-3)) / 16 := by ring
        _ ≥ 0 := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hMM) (by norm_num)
    have hnonneg : 0 ≤
        (((2^d/2-2^d/2^(h+1):ℕ):ℚ))*((M:ℚ)*((M:ℚ)-1)/2) -
          ((2^d:ℕ):ℚ)*(((M/2:ℕ):ℚ)*((M/2:ℕ)-1)/2) := by
      calc
      0 = ((2^d:ℕ):ℚ)*(M:ℚ)^2/8-((2^d:ℕ):ℚ)*(M:ℚ)^2/8 := by ring
      _ ≤ (((2^d/2-2^d/2^(h+1):ℕ):ℚ))*((M:ℚ)*((M:ℚ)-1)/2) -
          ((2^d:ℕ):ℚ)*(((M/2:ℕ):ℚ)*((M/2:ℕ)-1)/2) :=
        sub_le_sub (hmain.trans hfirst) hsecond
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hnonneg
  · have hfirst : (((2^d/2-2^d/2^(h+1):ℕ):ℚ))*
        ((M:ℚ)*((M:ℚ)-1)/2) ≤ ((2^d:ℕ):ℚ)/2*(M:ℚ)^2/2 := by
      have hchooseU : (M:ℚ)*((M:ℚ)-1)/2 ≤ (M:ℚ)^2/2 := by
        rw [pow_two]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) hM0) (by norm_num)
      exact (mul_le_mul hKupper hchooseU hchooseM0 (by positivity)).trans_eq (by ring)
    have hsecond0 : 0 ≤ ((2^d:ℕ):ℚ)*
        (((M/2:ℕ):ℚ)*((M/2:ℕ)-1)/2) := mul_nonneg (by positivity) hchooseHalf0
    have hbound :
        (((2^d/2-2^d/2^(h+1):ℕ):ℚ))*((M:ℚ)*((M:ℚ)-1)/2) -
          ((2^d:ℕ):ℚ)*(((M/2:ℕ):ℚ)*((M/2:ℕ)-1)/2) ≤
          ((2^d:ℕ):ℚ)*(M:ℚ)^2/4 := by
      calc
      _ ≤ (((2^d/2-2^d/2^(h+1):ℕ):ℚ))*((M:ℚ)*((M:ℚ)-1)/2) :=
        sub_le_self _ hsecond0
      _ ≤ ((2^d:ℕ):ℚ)/2*(M:ℚ)^2/2 := hfirst
      _ = ((2^d:ℕ):ℚ)*(M:ℚ)^2/4 := by ring
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hbound

/-- A finite characteristic-two field strictly larger than `2^d` has at least
twice that cardinality. -/
theorem two_mul_pow_le_card_of_charTwo
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (d : ℕ) (h : 2^d < Fintype.card F) : 2 * 2^d ≤ Fintype.card F := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [Nat.card_eq_fintype_card] at hc
  have hz : Nat.card (ZMod 2) = 2 := by simp
  rw [hz] at hc
  rw [hc] at h ⊢
  rw [← pow_succ']
  exact Nat.pow_le_pow_right (by decide) (by
    exact Nat.succ_le_iff.mpr ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h))

/-- The exact finite whole-domain tree construction, factored out so its
asymptotic consequence can be imported by the main theorem module. -/
theorem half_agreement_trees_finite_count
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (d h : ℕ) (hh : 2 ≤ h) (hd : 2 ^ h - 1 ≤ d)
    (hD : (additiveDomain D).card = 2 ^ d) (hq : 2 ^ d < Fintype.card F) :
    let N : ℕ := 2 ^ d
    let T : ℕ := N / 2
    let K : ℕ := N / 2 - N / 2 ^ (h + 1)
    let M : ℕ := treeSupportCount h d
    let q : ℕ := Fintype.card F
    let E : ℚ := (K : ℚ) * Nat.choose M 2 - (N : ℚ) * Nat.choose (M / 2) 2
    let A := additiveDomain D
    ∃ f g : A → F,
      commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
      agreementLE A K f (T - 1) ∧
      max (M - ⌊E / (q - N)⌋₊)
        ⌈(q - N : ℚ) * M ^ 2 / ((q - N) * M + 2 * E)⌉₊ ≤
        (nonzeroBadChallenges A K f g T).card := by
  classical
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Fintype D := Fintype.ofFinite D
  have hDN : Nat.card D=2^d := by rwa [card_additiveDomain] at hD
  have hdim : Module.finrank (ZMod 2) D=d := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hDN] at he
    simp only [Nat.card_eq_fintype_card,ZMod.card] at he
    exact Nat.pow_right_injective (by decide : 2≤2) he.symm
  have hheight : h+2≤2^h := by
    induction h,hh using Nat.le_induction with
    | base => decide
    | succ h hh ih => rw [pow_succ]; omega
  have hpop : (Trees.treeSupportFamily D (h-2)).card=treeSupportCount h d := by
    have he : h-2+2=h := by omega
    simpa only [he,hdim] using Trees.treeSupportFamily_card_eq (V := D) (h-2)
      (by simpa only [he,hdim] using hd)
  exact half_agreement_trees_of_population D d h hh (by omega) hD hq hpop

theorem half_agreement_trees_asymptotic_proved (h : ℕ) (hh : 2 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ (d : ℕ), d₀ ≤ d → 2 ^ h - 1 ≤ d →
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2]
        (D : AddSubgroup F),
        (additiveDomain D).card = 2 ^ d → 2 ^ d < Fintype.card F →
        let A := additiveDomain D
        let N : ℕ := 2 ^ d
        let K : ℕ := N / 2 - N / 2 ^ (h + 1)
        ∃ f g : A → F,
          commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
          agreementLE A K f (N / 2 - 1) ∧
          c * min ((N : ℝ) ^ (2 ^ h - 1)) ((Fintype.card F : ℝ) / N) ≤
            ((nonzeroBadChallenges A K f g (N / 2)).card : ℝ) := by
  obtain ⟨a,C,ha,hC,dg,hgrowth⟩ := treeSupportCount_growth h hh
  obtain ⟨d₁,hd₁⟩ := pow_unbounded_of_one_lt (3/a) (by norm_num : (1:ℝ)<2)
  let a₀ : ℝ := min a 1
  have ha₀ : 0<a₀ := lt_min ha (by norm_num)
  refine ⟨a₀/3,by positivity,max dg d₁,?_⟩
  intro d hd hdheight F _ _ _ D hD hq
  let N : ℕ := 2^d
  let K : ℕ := N/2-N/2^(h+1)
  let M : ℕ := treeSupportCount h d
  let q : ℕ := Fintype.card F
  let E : ℚ := (K:ℚ)*Nat.choose M 2-(N:ℚ)*Nat.choose (M/2) 2
  have hdg : dg≤d := (le_max_left _ _).trans hd
  have hd₁d : d₁≤d := (le_max_right _ _).trans hd
  obtain ⟨hMlower,hMupper⟩ := hgrowth d hdg
  have hτ : 0<2^h-1 := by
    have hp : 2^2≤2^h := Nat.pow_le_pow_right (by decide) hh
    omega
  have hpowd : (2:ℝ)^d ≤ ((2:ℝ)^d)^(2^h-1) :=
    le_self_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) (Nat.ne_of_gt hτ)
  have hM3R : (3:ℝ)<M := by
    calc
      (3:ℝ) = a*(3/a) := by field_simp
      _ < a*(2:ℝ)^d₁ := mul_lt_mul_of_pos_left hd₁ ha
      _ ≤ a*(2:ℝ)^d := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hd₁d) ha.le
      _ ≤ a*((2:ℝ)^d)^(2^h-1) := mul_le_mul_of_nonneg_left hpowd ha.le
      _ ≤ M := hMlower
  have hM3 : 3≤M := by exact_mod_cast hM3R.le
  have hMpos : 0<M := by omega
  have hNpos : 0<N := by dsimp [N]; positivity
  have hq2 : 2*N≤q := by
    dsimp [N,q]
    exact two_mul_pow_le_card_of_charTwo d hq
  have henergy := tree_collision_energy_bounds d h M hh hdheight hM3
  have henergy' : 0≤E ∧ E≤(N:ℚ)*M^2/4 := by
    simpa only [N,K,E] using henergy
  obtain ⟨f,g,hcommon,hagreeg,hagreef,hbad⟩ :=
    half_agreement_trees_finite_count D d h hh hdheight hD hq
  have hceil : ⌈(q-N:ℚ)*M^2/((q-N)*M+2*E)⌉₊ ≤
      (nonzeroBadChallenges (additiveDomain D) K f g (N/2)).card := by
    exact (le_max_right _ _).trans hbad
  have hcollision := one_third_min_real_le_of_second_moment N M q
    (nonzeroBadChallenges (additiveDomain D) K f g (N/2)).card E
    hNpos hMpos hq2 henergy'.1 henergy'.2 hceil
  have ha₀a : a₀≤a := min_le_left _ _
  have ha₀one : a₀≤1 := min_le_right _ _
  have ha₀nonneg : 0≤a₀ := ha₀.le
  have hscale : a₀*min (((N:ℝ))^(2^h-1)) ((q:ℝ)/N) ≤
      min (M:ℝ) ((q:ℝ)/N) := by
    apply le_min
    · calc
        _ ≤ a₀*(N:ℝ)^(2^h-1) := mul_le_mul_of_nonneg_left (min_le_left _ _) ha₀nonneg
        _ ≤ a*(N:ℝ)^(2^h-1) := mul_le_mul_of_nonneg_right ha₀a (by positivity)
        _ = a*((2:ℝ)^d)^(2^h-1) := by simp [N]
        _ ≤ M := hMlower
    · calc
        _ ≤ 1*min ((N:ℝ)^(2^h-1)) ((q:ℝ)/N) :=
          mul_le_mul_of_nonneg_right ha₀one (by positivity)
        _ ≤ (q:ℝ)/N := by
          simpa only [one_mul] using
            (min_le_right ((N:ℝ)^(2^h-1)) ((q:ℝ)/N))
  refine ⟨f,g,hcommon,hagreeg,hagreef,?_⟩
  calc
    a₀/3*min ((N:ℝ)^(2^h-1)) ((q:ℝ)/N) =
        (1/3:ℝ)*(a₀*min ((N:ℝ)^(2^h-1)) ((q:ℝ)/N)) := by ring
    _ ≤ (1/3:ℝ)*min (M:ℝ) ((q:ℝ)/N) :=
      mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ ≤ _ := hcollision

end BinaryFieldCounterexamples
