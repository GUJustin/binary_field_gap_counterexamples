/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.HalfRateDecisionTrees
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.Avoiding
public import BinaryFieldCounterexamples.Constructions.Trees.SharpEnergy
/-!
# Main theorem: half-rate pairs from intrinsic avoiding trees

Theorem 6.10, Section 6.3 of the manuscript, with its population `M` counted
literally by Definition 6.8. The preceding intrinsic-coordinate bridge proves
that this population equals Lemma 6.9's formula; no template-membership
hypothesis is hidden in the count. The finite theorem retains both collision
bounds and all individual and common agreement guarantees. Its height guard
includes the height-two remark following Theorem 6.10.

The probability companion chooses its constant and dimension cutoff before
the ambient field, domain, or padding subspace. It also retains the intrinsic
population in the large-field conclusion. All declarations are proved.
-/
@[expose] public section
namespace BinaryFieldCounterexamples

/-- Lemma 6.9 in actual-height notation: the intrinsic Definition 6.8 count is
the paper's recurrence for every codimension-`h+1` subspace. -/
theorem intrinsicAvoidingTreeFunction_count
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (h : ℕ) (hh : 2≤h) (W : Submodule (ZMod 2) U)
    (hd : 2^h-1≤Module.finrank (ZMod 2) U)
    (hW : Module.finrank (ZMod 2) W+(h+1)=Module.finrank (ZMod 2) U) :
    Nat.card {φ : U → ZMod 2 // Trees.IsAvoidingTree h W φ}=
      avoidingTreeSupportCount h (Module.finrank (ZMod 2) U) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hh
  exact Trees.isAvoidingTree_count n W hd (by simpa using hW)

/-- Theorem 6.10's full finite statement with `M` the intrinsic count of
Definition 6.8, and including the height-two remark at agreement `5N/8`.
The same pair has the individual bounds and both image-size bounds. -/
theorem half_rate_decision_trees_intrinsic_full
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (d h : ℕ) (hh : 2≤h) (hd : 2^h-1≤d)
    (W : Submodule (ZMod 2) D)
    (hW : Module.finrank (ZMod 2) W+(h+1)=d)
    (hD : (additiveDomain D).card=2^d) (hq : 2^d<Fintype.card F) :
    let N : ℕ := 2^d
    let K : ℕ := N/2
    let w : ℕ := N/2^(h+1)
    let M := Nat.card {φ : D → ZMod 2 // Trees.IsAvoidingTree h W φ}
    let E : ℚ := (((K : ℚ)-w-(K : ℚ)^2/(N-w))*M^2+w*M)/2
    let A := additiveDomain D
    M=avoidingTreeSupportCount h d ∧
    ∃ f g : A → F, commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
      agreementLE A K f (K+w-1) ∧
      max (M-⌊E/(Fintype.card F-N)⌋₊)
        ⌈(Fintype.card F-N : ℚ)*M^2/((Fintype.card F-N)*M+2*E)⌉₊ ≤
        (nonzeroBadChallenges A K f g (K+w)).card ∧
      min ((M : ℝ)/2) ((Fintype.card F : ℝ)/N)≤
        ((nonzeroBadChallenges A K f g (K+w)).card : ℝ) := by
  have hDN : Nat.card D=2^d := by rwa [card_additiveDomain] at hD
  have hdim : Module.finrank (ZMod 2) D=d := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hDN] at he
    simp only [Nat.card_eq_fintype_card,ZMod.card] at he
    exact Nat.pow_right_injective (by decide : 2≤2) he.symm
  have hc := intrinsicAvoidingTreeFunction_count h hh W
    (by rwa [hdim]) (by rwa [hdim])
  rw [hdim] at hc
  dsimp only
  rw [hc]
  obtain ⟨f,g,hcommon,hg,hf,hbad⟩ := half_rate_decision_trees D d h hh hd hD hq
  refine ⟨rfl,f,g,hcommon,hg,hf,hbad,?_⟩
  let N : ℕ := 2^d
  let K : ℕ := N/2
  let w : ℕ := N/2^(h+1)
  let M : ℕ := avoidingTreeSupportCount h d
  let E : ℚ := (((K : ℚ)-w-(K : ℚ)^2/(N-w))*M^2+w*M)/2
  change min ((M : ℝ)/2) ((Fintype.card F : ℝ)/N)≤_
  by_cases hM : M=0
  · simp only [hM,Nat.cast_zero,zero_div,min_le_iff]
    exact Or.inl (by positivity)
  · have hMpos : 0<M := Nat.pos_of_ne_zero hM
    have hN : 0<N := by dsimp [N]; positivity
    have hd1 : 1≤d := by
      have hp : 4≤(2 : ℕ)^h := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) hh
      omega
    have hK : (K : ℚ)=(N : ℚ)/2 := by
      apply (eq_div_iff (by norm_num : (2 : ℚ)≠0)).mpr
      exact_mod_cast Nat.div_mul_cancel (dvd_pow_self (2 : ℕ) (by omega : d≠0))
    have hw : w<N := Nat.div_lt_self hN (by
      exact one_lt_pow₀ (by decide : 1<(2 : ℕ)) (by omega))
    have hE0 : 0≤E := (avoiding_tree_energy_bounds d h M hh hd (by omega)).1
    have hE : E≤(N : ℚ)*M^2/8 :=
      avoiding_tree_energy_le_eighth_of_half N K w M hN hK hw (by omega)
    exact half_or_field_min_real_le_of_second_moment N M (Fintype.card F) _ E
      hN hMpos (two_mul_pow_le_card_of_charTwo d hq) hE0 hE
      ((le_max_right _ _).trans hbad)

/-- Theorem 6.10's uniform probability and large-field count consequences,
with the actual intrinsic Definition 6.8 population on every admissible `W`.
At height two this gives the paper's `Ω(min{N,q/N})` count remark. -/
theorem half_rate_decision_trees_probability_intrinsic_full (h : ℕ) (hh : 2≤h) :
    ∃ c : ℝ, 0<c ∧ ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀≤d → 2^h-1≤d →
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (D : AddSubgroup F) [Fintype D],
        (additiveDomain D).card=2^d → 2^d<Fintype.card F →
        let A := additiveDomain D
        let N : ℕ := 2^d
        let q : ℕ := Fintype.card F
        let K : ℕ := N/2
        ∃ f g : A → F,
          commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
          agreementLE A K f (K+N/2^(h+1)-1) ∧
          c*min ((N : ℝ)^(2^h-h-1)/q) (1/N)≤
            ((nonzeroBadChallenges A K f g (K+N/2^(h+1))).card : ℝ)/q ∧
          ∀ W : Submodule (ZMod 2) D, Module.finrank (ZMod 2) W+(h+1)=d →
            let M := Nat.card {φ : D → ZMod 2 // Trees.IsAvoidingTree h W φ}
            M=avoidingTreeSupportCount h d ∧
            (N*M≤q → c*M≤
              ((nonzeroBadChallenges A K f g (K+N/2^(h+1))).card : ℝ)) := by
  obtain ⟨c,hc,d₀,hbound⟩ := half_rate_decision_trees_probability h hh
  refine ⟨c,hc,d₀,?_⟩
  intro d hd₀ hd F _ _ _ _ D _ hD hq
  obtain ⟨f,g,hcommon,hg,hf,hp,hlarge⟩ := hbound d hd₀ hd F D hD hq
  refine ⟨f,g,hcommon,hg,hf,hp,?_⟩
  intro W hW
  have hDN : Nat.card D=2^d := by rwa [card_additiveDomain] at hD
  have hdim : Module.finrank (ZMod 2) D=d := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hDN] at he
    simp only [Nat.card_eq_fintype_card,ZMod.card] at he
    exact Nat.pow_right_injective (by decide : 2≤2) he.symm
  dsimp only
  rw [intrinsicAvoidingTreeFunction_count h hh W (by rwa [hdim]) (by rwa [hdim]),hdim]
  exact ⟨rfl,hlarge⟩

/-- The fractional common-agreement gap in Theorem 6.10 is exactly
`2^(-h-1)`, expressed without a negative natural exponent. -/
theorem binary_tree_fractional_gap (d h : ℕ) (hd : h+1≤d) :
    (((2^d/2^(h+1) : ℕ) : ℚ)/(2^d : ℕ))=1/(2 : ℚ)^(h+1) := by
  rw [Nat.pow_div hd (by decide),Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat]
  apply (div_eq_iff (by positivity : (2 : ℚ)^d≠0)).mpr
  rw [div_mul_eq_mul_div,one_mul]
  apply (eq_div_iff (by positivity : (2 : ℚ)^(h+1)≠0)).mpr
  rw [←pow_add,Nat.sub_add_cancel hd]

/-- Corollary 6.7's proof, assembled with Lemma 6.1's sharp final clause:
the same received pair attains the exact collision bound and
`min{M/2,q/N}`, with its common and individual agreement guarantees. -/
theorem half_agreement_trees_full
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (d h : ℕ) (hh : 2≤h) (hd : 2^h-1≤d)
    (hD : (additiveDomain D).card=2^d) (hq : 2^d<Fintype.card F) :
    let N : ℕ := 2^d
    let T : ℕ := N/2
    let K : ℕ := N/2-N/2^(h+1)
    let M := treeSupportCount h d
    let E : ℚ := (K : ℚ)*M.choose 2-(N : ℚ)*(M/2).choose 2
    let A := additiveDomain D
    ∃ f g : A → F, commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
      agreementLE A K f (T-1) ∧
      max (M-⌊E/(Fintype.card F-N)⌋₊)
        ⌈(Fintype.card F-N : ℚ)*M^2/((Fintype.card F-N)*M+2*E)⌉₊ ≤
        (nonzeroBadChallenges A K f g T).card ∧
      min ((M : ℝ)/2) ((Fintype.card F : ℝ)/N)≤
        ((nonzeroBadChallenges A K f g T).card : ℝ) := by
  obtain ⟨f,g,hcommon,hg,hf,hbad⟩ := half_agreement_trees D d h hh hd hD hq
  refine ⟨f,g,hcommon,hg,hf,hbad,?_⟩
  let N : ℕ := 2^d
  let K : ℕ := N/2-N/2^(h+1)
  let M : ℕ := treeSupportCount h d
  let E : ℚ := (K : ℚ)*M.choose 2-(N : ℚ)*(M/2).choose 2
  have heven : 2∣M := by
    have hDN : Nat.card D=2^d := by rwa [card_additiveDomain] at hD
    have hdim : Module.finrank (ZMod 2) D=d := by
      have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
      rw [hDN] at he
      simp only [Nat.card_eq_fintype_card,ZMod.card] at he
      exact Nat.pow_right_injective (by decide : 2≤2) he.symm
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hh
    have hc := Trees.treeSupportFamily_card_eq (V := D) n (by rwa [hdim])
    rw [hdim] at hc
    have hi := Trees.treeSupportFamily_point_incidence n (0:D)
    rw [hc] at hi
    exact ⟨_,hi.symm⟩
  change min ((M : ℝ)/2) ((Fintype.card F : ℝ)/N)≤_
  by_cases hM : M=0
  · simp only [hM,Nat.cast_zero,zero_div,min_le_iff]
    exact Or.inl (by positivity)
  · have hMpos : 0<M := Nat.pos_of_ne_zero hM
    have hN : 0<N := by dsimp [N]; positivity
    have hd1 : 1≤d := by
      have hp : 4≤(2 : ℕ)^h := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) hh
      omega
    have hhalf : ((N/2 : ℕ) : ℚ)=(N : ℚ)/2 := by
      apply (eq_div_iff (by norm_num : (2 : ℚ)≠0)).mpr
      exact_mod_cast Nat.div_mul_cancel (dvd_pow_self (2 : ℕ) (by omega : d≠0))
    have hK : (K : ℚ)≤(N : ℚ)/2 := by
      have hk : K≤N/2 := Nat.sub_le _ _
      exact (show (K : ℚ)≤((N/2 : ℕ) : ℚ) by exact_mod_cast hk).trans_eq hhalf
    have hE0 : 0≤E := by
      by_cases hM3 : 3≤M
      · exact (tree_collision_energy_bounds d h M hh hd hM3).1
      · obtain ⟨m,hm⟩ := heven
        have hM2 : M=2 := by omega
        simp only [E,hM2]
        norm_num
    have hE : E≤(N : ℚ)*M^2/8 := whole_tree_energy_le_eighth N K M hK heven
    exact half_or_field_min_real_le_of_second_moment N M (Fintype.card F) _ E
      hN hMpos (two_mul_pow_le_card_of_charTwo d hq) hE0 hE
      ((le_max_right _ _).trans hbad)

end BinaryFieldCounterexamples
