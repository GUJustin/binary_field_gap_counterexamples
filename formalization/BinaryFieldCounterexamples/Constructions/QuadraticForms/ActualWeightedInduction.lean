/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ActualWeightedStep
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ActualZeroBase
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ActualAnisotropicBase
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RankOneKernelIdentification
public import BinaryFieldCounterexamples.Counting.QuadraticKernelTails
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
/-- A zero-dimensional quadratic radical quotient means the original form vanishes identically. -/
theorem quadratic_zero_of_quotient_finrank_zero {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (Q : QuadraticForm k V)
    (hr : Module.finrank k (V ⧸ Q.radical)=0) : ∀ x,Q x=0 := by
  have hd := Q.radical.finrank_quotient_add_finrank
  have hrad : Q.radical=⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  intro x
  have hx : x∈Q.radical := by rw [hrad]; trivial
  exact hx.1
variable {k V W : Type*} [Field k] [Fintype k]
  [AddCommGroup V] [Module k V] [Fintype V]
  [AddCommGroup W] [Module k W] [Fintype W]
/-- The rational rank-character kernel determined by the actual singular-subspace incidence of a quadratic form. -/
noncomputable def quadraticRankKernel (Q : QuadraticForm k V) : ℕ→ℚ :=
  rankIncidenceKernel (Fintype.card k) (Module.finrank k V) (quadraticIncidenceSequence Q)
/-- The claimed pair of universal weighted evaluations, normalized by the actual zeroth upper kernel. -/
def WeightedQuadraticEvaluation (Q : QuadraticForm k V) (n : ℕ) : Prop :=
  ∀ j,j≤n→
    gaussianWeightedSum ((Fintype.card k)^2) n j (groupedRankKernelA (quadraticRankKernel Q))=
      (Fintype.card k:ℚ)^((2*n+1)*j)*
        (gaussianPascal ((Fintype.card k)^2) (n-(Module.finrank k (V ⧸ Q.radical)+1)/2) j:ℚ) ∧
    gaussianWeightedSum ((Fintype.card k)^2) n j (groupedRankKernelB (quadraticRankKernel Q))=
      (Fintype.card k:ℚ)^((2*n-1)*j)*
        (gaussianPascal ((Fintype.card k)^2) (n-Module.finrank k (V ⧸ Q.radical)/2) j:ℚ)*
        groupedRankKernelB (quadraticRankKernel Q) 0
/-- The universal weighted evaluation is preserved by an actual hyperbolic extension. -/
theorem weightedQuadraticEvaluation_hyperbolic (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (R : QuadraticForm k W) (n : ℕ)
    (hdQ : Module.finrank k V=2*n) (hd : Module.finrank k W=Module.finrank k V+2)
    (hh : Module.finrank k R.radical=Module.finrank k Q.radical)
    (hz : Nat.card {x : W // R x=0}=(Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V)+
      Fintype.card k*Nat.card {x : V // Q x=0})
    (hQ : WeightedQuadraticEvaluation Q n) : WeightedQuadraticEvaluation R (n+1) := by
  have hrQ := Q.radical.finrank_quotient_add_finrank
  have hrR := R.radical.finrank_quotient_add_finrank
  have hr : Module.finrank k (W ⧸ R.radical)=Module.finrank k (V ⧸ Q.radical)+2 := by omega
  have hia : n+1-(Module.finrank k (W ⧸ R.radical)+1)/2=
      n-(Module.finrank k (V ⧸ Q.radical)+1)/2 := by omega
  have hib : n+1-Module.finrank k (W ⧸ R.radical)/2=
      n-Module.finrank k (V ⧸ Q.radical)/2 := by omega
  have hb0 : groupedRankKernelB (quadraticRankKernel R) 0=
      (Fintype.card k:ℚ)*groupedRankKernelB (quadraticRankKernel Q) 0 := by
    exact groupedRankKernelB_zero _ _ _
      (by simp only [quadraticRankKernel,quadraticRankKernel_zero])
      (quadraticRankKernel_hyperbolic_one p Q R hd hh hz)
  intro j hj
  have ha := actual_weightedKernelA_step p Q R n j hj hd hh hz
  have hb := actual_weightedKernelB_step p Q R n j hj hd hh hz
  change gaussianWeightedSum _ _ _ (groupedRankKernelA (quadraticRankKernel R))=_ at ha
  change gaussianWeightedSum _ _ _ (groupedRankKernelB (quadraticRankKernel R))=_ at hb
  rw [hia,hib]
  by_cases hjn : j≤n
  · obtain ⟨hQa,hQb⟩ := hQ j hjn
    change gaussianWeightedSum _ _ _ (groupedRankKernelA (quadraticRankKernel Q))=_ at hQa
    change gaussianWeightedSum _ _ _ (groupedRankKernelB (quadraticRankKernel Q))=_ at hQb
    change gaussianWeightedSum _ _ _ (groupedRankKernelA (quadraticRankKernel R))=
      (Fintype.card k:ℚ)^(2*j)*gaussianWeightedSum _ _ _ (groupedRankKernelA (quadraticRankKernel Q)) at ha
    change gaussianWeightedSum _ _ _ (groupedRankKernelB (quadraticRankKernel R))=
      (Fintype.card k:ℚ)^(2*j+1)*gaussianWeightedSum _ _ _ (groupedRankKernelB (quadraticRankKernel Q)) at hb
    constructor
    · rw [ha,hQa,←mul_assoc,←pow_add]
      congr 2
      ring
    · rw [hb,hQb,hb0]
      have he : (2*j+1)+(2*n-1)*j=(2*(n+1)-1)*j+1 := by
        by_cases hn : n=0
        · subst n
          have hj0 : j=0 := by omega
          subst j
          norm_num
        · have hh : 2*n-1+1=2*n := by omega
          rw [show 2*(n+1)-1=2*n+1 by omega]
          calc
            (2*j+1)+(2*n-1)*j = ((2*n-1+1)+1)*j+1 := by ring
            _ = (2*n+1)*j+1 := by rw [hh]
      calc
        _ = ((Fintype.card k:ℚ)^(2*j+1)*(Fintype.card k:ℚ)^((2*n-1)*j))*
              (gaussianPascal ((Fintype.card k)^2) (n-Module.finrank k (V ⧸ Q.radical)/2) j:ℚ)*
              groupedRankKernelB (quadraticRankKernel Q) 0 := by ring
        _ = _ := by rw [←pow_add,he,pow_succ]; ring
  · have htailA := gaussianWeightedSum_eq_zero_of_tail ((Fintype.card k)^2) n j
      (groupedRankKernelA (quadraticRankKernel Q)) (by omega)
      (fun u hu => actual_groupedKernelA_tail Q n u hdQ hu)
    have htailB := gaussianWeightedSum_eq_zero_of_tail ((Fintype.card k)^2) n j
      (groupedRankKernelB (quadraticRankKernel Q)) (by omega)
      (fun u hu => actual_groupedKernelB_tail Q n u hdQ hu)
    change gaussianWeightedSum _ _ _ (groupedRankKernelA (quadraticRankKernel Q))=0 at htailA
    change gaussianWeightedSum _ _ _ (groupedRankKernelB (quadraticRankKernel Q))=0 at htailB
    change gaussianWeightedSum _ _ _ (groupedRankKernelA (quadraticRankKernel R))=
      (Fintype.card k:ℚ)^(2*j)*gaussianWeightedSum _ _ _ (groupedRankKernelA (quadraticRankKernel Q)) at ha
    change gaussianWeightedSum _ _ _ (groupedRankKernelB (quadraticRankKernel R))=
      (Fintype.card k:ℚ)^(2*j+1)*gaussianWeightedSum _ _ _ (groupedRankKernelB (quadraticRankKernel Q)) at hb
    rw [htailA,mul_zero] at ha
    rw [htailB,mul_zero] at hb
    constructor
    · rw [ha,gaussianPascal_eq_zero _ _ _ (by omega)]
      simp
    · rw [hb,gaussianPascal_eq_zero _ _ _ (by omega)]
      simp
/-- At index zero the Gaussian weighting retains the zeroth sequence entry. -/
theorem gaussianWeightedSum_zero_index (q n : ℕ) (K : ℕ→ℚ) :
    gaussianWeightedSum q n 0 K=K 0 := by
  simp [gaussianWeightedSum,gaussianBinomial]
/-- The actual rank-zero base satisfies the normalized universal evaluation. -/
theorem weightedQuadraticEvaluation_zero (Q : QuadraticForm k V) (n : ℕ)
    (hd : Module.finrank k V=2*n) (hr : Module.finrank k (V ⧸ Q.radical)=0) :
    WeightedQuadraticEvaluation Q n := by
  have hQ := quadratic_zero_of_quotient_finrank_zero Q hr
  have hb0 := actual_zero_weightedB Q hQ n 0 hd (by omega)
  simp only [gaussianWeightedSum_zero_index,Nat.mul_zero,add_zero,
    gaussianPascal_zero,Nat.cast_one,mul_one] at hb0
  intro j hj
  rw [hr]
  norm_num only
  constructor
  · exact actual_zero_weightedA Q hQ n j hd hj
  · change groupedRankKernelB (quadraticRankKernel Q) 0=_ at hb0
    rw [hb0]
    have hh := actual_zero_weightedB Q hQ n j hd hj
    change gaussianWeightedSum _ _ _ (groupedRankKernelB (quadraticRankKernel Q))=_ at hh
    rw [hh,pow_add]
    simp only [Nat.sub_zero]
    ring
/-- Every anisotropic radical quotient gives one of the three proved actual weighted bases. -/
theorem weightedQuadraticEvaluation_anisotropic (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (n : ℕ) (hd : Module.finrank k V=2*n)
    (hQ : (Q.lift Q.radical le_rfl).Anisotropic) : WeightedQuadraticEvaluation Q n := by
  have hrle := QuadraticCoordinates.anisotropic_finrank_le_two p (Q.lift Q.radical le_rfl) hQ
  have hdim := Q.radical.finrank_quotient_add_finrank
  have hcases : Module.finrank k (V ⧸ Q.radical)=0 ∨
      Module.finrank k (V ⧸ Q.radical)=1 ∨ Module.finrank k (V ⧸ Q.radical)=2 := by omega
  rcases hcases with hr | hr | hr
  · exact weightedQuadraticEvaluation_zero Q n hd hr
  · have hn : 1≤n := by omega
    have hrad : Module.finrank k Q.radical=2*n-1 := by omega
    have hker : quadraticRankKernel Q=rankOneIncidenceKernel (Fintype.card k) n := by
      funext r
      exact actual_rankOne_kernel Q hQ n hn hd hrad r
    have hb0 := actual_rankOne_weightedB Q hQ n 0 hn hd hrad (by omega)
    rw [gaussianWeightedSum_zero_index] at hb0
    change groupedRankKernelB (quadraticRankKernel Q) 0=0 at hb0
    intro j hj
    rw [hr]
    norm_num only
    simp only [Nat.sub_zero]
    constructor
    · by_cases hjn : j<n
      · exact actual_rankOne_weightedA Q hQ n j hn hd hrad hjn
      · have hjn : j=n := by omega
        subst j
        rw [hker,rankOneIncidenceKernel_weighted_boundary _ n Fintype.one_lt_card (by omega),
          gaussianPascal_eq_zero _ (n-1) n (by omega)]
        simp
    · rw [hb0,mul_zero,hker]
      by_cases hjn : j<n
      · exact rankOneIncidenceKernel_weightedB _ n j Fintype.one_lt_card hjn
      · have hjn : j=n := by omega
        subst j
        exact rankOneIncidenceKernel_weightedB_boundary _ n Fintype.one_lt_card (by omega)
  · have hn : 1≤n := by omega
    let m := n-1
    have hnm : n=m+1 := by dsimp [m]; omega
    have hd' : Module.finrank k V=2*m+2 := by omega
    have hrad : Module.finrank k Q.radical=2*m := by omega
    have hker : quadraticRankKernel Q=anisotropicPlaneKernel (Fintype.card k) (2*m) := by
      funext r
      exact actual_anisotropic_plane_kernel Q hQ (2*m) hd' hrad r
    have hb0 := actual_anisotropic_plane_weightedB Q hQ m 0 hd' hrad (by omega)
    simp only [gaussianWeightedSum_zero_index,zero_add,mul_one,gaussianPascal_zero,Nat.cast_one] at hb0
    change groupedRankKernelB (quadraticRankKernel Q) 0= -(Fintype.card k:ℚ)^(2*m+1) at hb0
    intro j hj
    rw [hr,hnm]
    norm_num only
    simp only [Nat.add_sub_cancel]
    constructor
    · by_cases hjm : j≤m
      · have ha := actual_anisotropic_plane_weightedA Q hQ m j hd' hrad hjm
        simpa only [quadraticRankKernel,show 2*(m+1)+1=2*m+3 by omega] using ha
      · have hjn : j=m+1 := by omega
        subst j
        rw [hker,anisotropicPlaneKernel_weightedA_boundary _ m Fintype.one_lt_card,
          gaussianPascal_eq_zero _ m (m+1) (by omega)]
        simp
    · rw [hb0]
      by_cases hjm : j≤m
      · have hb := actual_anisotropic_plane_weightedB Q hQ m j hd' hrad hjm
        change gaussianWeightedSum _ _ _ (groupedRankKernelB (quadraticRankKernel Q))=_ at hb
        rw [hb,show 2*(m+1)-1=2*m+1 by omega,
          show (2*m+1)*(j+1)=(2*m+1)*j+(2*m+1) by ring,pow_add]
        ring
      · have hjn : j=m+1 := by omega
        subst j
        rw [hker,anisotropicPlaneKernel_weightedB_boundary _ m Fintype.one_lt_card,
          gaussianPascal_eq_zero _ m (m+1) (by omega)]
        simp
/-- Universal weighted Fourier evaluations for every actual even-dimensional quadratic form over a finite field. -/
theorem actual_weightedQuadraticEvaluation (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (Q : QuadraticForm k V) (hd : Module.finrank k V=2*n) :
    WeightedQuadraticEvaluation Q n := by
  classical
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    rcases anisotropic_quotient_or_hyperbolic_vector Q with hQ | ⟨x,hx,hxp⟩
    · exact weightedQuadraticEvaluation_anisotropic p Q n hd hQ
    · obtain ⟨y,hy,hxy⟩ := exists_hyperbolic_partner Q x hx hxp
      let H := hyperbolicComplement Q x y
      let R := Q.comp H.subtype
      have hdim := hyperbolicComplement_finrank Q x y hx hy hxy
      have hn : 0<n := by omega
      have hdR : Module.finrank k H=2*(n-1) := by dsimp [H]; omega
      have hR : WeightedQuadraticEvaluation R (n-1) := ih (n-1) (by omega) R hdR
      have hh : Module.finrank k Q.radical=Module.finrank k R.radical :=
        (hyperbolicComplementRadicalEquiv Q x y hx hy hxy).finrank_eq.symm
      have hz : Nat.card {x : V // Q x=0}=(Fintype.card k-1)*(Fintype.card k)^(Module.finrank k H)+
          Fintype.card k*Nat.card {x : H // R x=0} := by
        have hh := hyperbolicSplit_zero_count Q x y hx hy hxy
        have hc := Module.natCard_eq_pow_finrank (K:=k) (V:=H)
        simp only [Nat.card_eq_fintype_card] at hc ⊢
        rw [←hc]
        exact hh
      have hs := weightedQuadraticEvaluation_hyperbolic p R Q (n-1) hdR hdim hh hz hR
      simpa only [Nat.sub_add_cancel hn] using hs
/-- The universal lower weighted Fourier identity for the actual quadratic rank. -/
theorem actual_weightedKernelA (p : ℕ) [Fact p.Prime] [CharP k p]
    (n j : ℕ) (Q : QuadraticForm k V) (hd : Module.finrank k V=2*n) (hj : j≤n) :
    gaussianWeightedSum ((Fintype.card k)^2) n j (groupedRankKernelA (quadraticRankKernel Q))=
      (Fintype.card k:ℚ)^((2*n+1)*j)*
        (gaussianPascal ((Fintype.card k)^2) (n-(Module.finrank k (V ⧸ Q.radical)+1)/2) j:ℚ) := by
  exact (actual_weightedQuadraticEvaluation p n Q hd j hj).1
/-- The universal upper weighted Fourier identity, retaining the actual type in its zeroth kernel. -/
theorem actual_weightedKernelB (p : ℕ) [Fact p.Prime] [CharP k p]
    (n j : ℕ) (Q : QuadraticForm k V) (hd : Module.finrank k V=2*n) (hj : j≤n) :
    gaussianWeightedSum ((Fintype.card k)^2) n j (groupedRankKernelB (quadraticRankKernel Q))=
      (Fintype.card k:ℚ)^((2*n-1)*j)*
        (gaussianPascal ((Fintype.card k)^2) (n-Module.finrank k (V ⧸ Q.radical)/2) j:ℚ)*
        groupedRankKernelB (quadraticRankKernel Q) 0 := by
  exact (actual_weightedQuadraticEvaluation p n Q hd j hj).2
end BinaryFieldCounterexamples.QuadraticGeometry
