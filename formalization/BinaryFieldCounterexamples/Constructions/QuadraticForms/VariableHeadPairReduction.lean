/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.PoleReduction
public import BinaryFieldCounterexamples.Counting.RationalCollision
public import BinaryFieldCounterexamples.Counting.AffineLabelPooling
public import BinaryFieldCounterexamples.Agreement.Interpolation
public import BinaryFieldCounterexamples.Agreement.ExcludeZero

/-!
# Received pairs with a pole-dependent common head

Rational collision averaging chooses one exterior pole. The first input's numerator may
depend on that pole; translating every locator value by the chosen common head
preserves the image size and hence the exact collision denominator.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A uniform rational collision budget for common-head locators gives the
exact received-pair denominator, losing at most the zero challenge. -/
theorem exists_polePair_of_variableHead_collision_budget
    {ι F : Type*} [Field F] [Fintype F]
    (I : Finset ι) (D : Finset F) (R : F → F[X]) (P : ι → F[X])
    (K T : ℕ) (δ : ℚ)
    (hq : D.card<Fintype.card F) (hK : K≤D.card)
    (hI : I.Nonempty) (hδ : 0≤δ)
    (A : ℕ)
    (hsource : ∀ β∉D,agreementLE D K
      (fun x => (R β).eval (x:F)*((x:F)-β)⁻¹) A)
    (hdeg : ∀ β∉D,∀ i∈I,(P i-R β).degree≤K)
    (hroots : ∀ i∈I,T≤(D.filter fun x => (P i).eval x=0).card)
    (htotal : (∑ β∈Finset.univ\D,
      (unorderedCollisionCount I (fun i => (P i).eval β):ℚ))≤δ*I.card.choose 2) :
    ∃ f g : D→F,
      agreementEQ D K g K ∧ commonAgreementEQ D K f g K ∧
      agreementLE D K f A ∧
      ⌈(I.card:ℚ)*(Fintype.card F-D.card:ℚ)/
        ((Fintype.card F-D.card:ℚ)+δ*((I.card:ℚ)-1))⌉₊-1≤
        (nonzeroBadChallenges D K f g T).card := by
  let exterior := Finset.univ\D
  have hecard : exterior.card=Fintype.card F-D.card := by
    simp [exterior,Finset.card_sdiff]
  have he : exterior.Nonempty := Finset.card_pos.mp (by rw [hecard]; omega)
  obtain ⟨β,hβ,himage⟩ := exists_parameter_image_card_rational_bounds exterior I
    (fun β i => (P i).eval β) (δ*I.card.choose 2) he htotal
  have hβD : β∉D := (Finset.mem_sdiff.mp hβ).2
  let f : D→F := fun x => (R β).eval (x:F)*((x:F)-β)⁻¹
  let g : D→F := fun x => ((x:F)-β)⁻¹
  refine ⟨f,g,agreementEQ_reciprocal D β hβD K hK,
    commonAgreementEQ_reciprocal_right D β hβD K hK f,hsource β hβD,?_⟩
  have himagebad : (I.image (fun i => (P i-R β).eval β)).card≤
      (badChallenges D K f g T).card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hpole := poleReduction_badChallenge D β hβD (R β) (P i-R β) K T (hdeg β hβD i hi) (by
      have heq : R β+(P i-R β)=P i := by ring
      simpa only [heq] using hroots i hi)
    exact hpole
  have himagecard : (I.image (fun i => (P i).eval β)).card=
      (I.image (fun i => (P i-R β).eval β)).card := by
    rw [show I.image (fun i => (P i-R β).eval β)=
      (I.image (fun i => (P i).eval β)).image (fun z => z-(R β).eval β) by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro i hi
        simp]
    symm
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    exact sub_left_injective hxy
  have hnonzero : (I.image (fun i => (P i-R β).eval β)).card-1≤
      (nonzeroBadChallenges D K f g T).card :=
    (Nat.sub_le_sub_right himagebad 1).trans
      (card_badChallenges_sub_one_le_nonzero D K f g T)
  have hsecond := (le_max_right
    (I.card-⌊(δ*I.card.choose 2)/exterior.card⌋₊)
    ⌈(exterior.card:ℚ)*I.card^2/
      ((exterior.card:ℚ)*I.card+2*(δ*I.card.choose 2))⌉₊).trans himage
  apply le_trans (Nat.sub_le_sub_right ?_ 1) hnonzero
  have ha : (0:ℚ)<(Fintype.card F:ℚ)-D.card := by
    exact sub_pos.mpr (by exact_mod_cast hq)
  have hM : (0:ℚ)<I.card := by exact_mod_cast Finset.card_pos.mpr hI
  have hchoose : (I.card.choose 2:ℚ)=((I.card:ℚ)*((I.card:ℚ)-1))/2 := by
    have hs := sq_eq_add_two_mul_choose_two I.card
    have hsQ : (I.card:ℚ)^2=(I.card:ℚ)+2*(I.card.choose 2:ℚ) := by exact_mod_cast hs
    linarith
  have hden1 : (0:ℚ)<(Fintype.card F-D.card:ℚ)+δ*((I.card:ℚ)-1) := by
    have hM1 : (0:ℚ)≤(I.card:ℚ)-1 := by
      have hh : (1:ℚ)≤I.card := by exact_mod_cast (Finset.card_pos.mpr hI)
      linarith
    exact add_pos_of_pos_of_nonneg ha (mul_nonneg hδ hM1)
  have hratio :
      (I.card:ℚ)*(Fintype.card F-D.card:ℚ)/
          ((Fintype.card F-D.card:ℚ)+δ*((I.card:ℚ)-1)) =
      (exterior.card:ℚ)*I.card^2/
          ((exterior.card:ℚ)*I.card+2*(δ*I.card.choose 2)) := by
    rw [hecard,Nat.cast_sub hq.le,hchoose]
    field_simp [hden1.ne',hM.ne']
  rw [hratio]
  exact himagecard ▸ hsecond

/-- Pairwise exterior collision bounds supply the uniform rational budget used
by `exists_polePair_of_variableHead_collision_budget`. -/
theorem exists_polePair_of_variableHead_pairwise_collision_bound
    {ι F : Type*} [LinearOrder ι] [Field F] [Fintype F]
    (I : Finset ι) (D : Finset F) (R : F → F[X]) (P : ι → F[X])
    (K T A δ : ℕ)
    (hq : D.card<Fintype.card F) (hK : K≤D.card)
    (hI : I.Nonempty)
    (hsource : ∀ β∉D,agreementLE D K
      (fun x => (R β).eval (x:F)*((x:F)-β)⁻¹) A)
    (hdeg : ∀ β∉D,∀ i∈I,(P i-R β).degree≤K)
    (hroots : ∀ i∈I,T≤(D.filter fun x => (P i).eval x=0).card)
    (hpair : ∀ i∈I,∀j∈I,i≠j →
      ((Finset.univ\D).filter fun β => (P i).eval β=(P j).eval β).card≤δ) :
    ∃ f g : D→F,
      agreementEQ D K g K ∧ commonAgreementEQ D K f g K ∧
      agreementLE D K f A ∧
      ⌈(I.card:ℚ)*(Fintype.card F-D.card:ℚ)/
        ((Fintype.card F-D.card:ℚ)+δ*((I.card:ℚ)-1))⌉₊-1≤
        (nonzeroBadChallenges D K f g T).card := by
  apply exists_polePair_of_variableHead_collision_budget I D R P K T δ hq hK hI
    (by positivity) A hsource hdeg hroots
  have htotal := sum_unorderedCollisionCount_le_choose_two_mul
    (Finset.univ\D) I (fun β i => (P i).eval β) δ
  have htotal' :
      ∑ β∈Finset.univ\D,unorderedCollisionCount I (fun i => (P i).eval β)≤
        δ*I.card.choose 2 := by
    apply le_trans (htotal (fun i hi j hj hij => hpair i hi j hj hij))
    rw [mul_comm]
  have hcast :
      (∑ β∈Finset.univ\D,
        (unorderedCollisionCount I (fun i => (P i).eval β):ℚ))≤
          (δ:ℚ)*I.card.choose 2 := by
    exact_mod_cast htotal'
  exact hcast

/-- Both simultaneous collision bounds remain valid after normalization when the first-input
bound excludes zero. -/
theorem exists_polePair_of_variableHead_collision_bounds
    {ι F : Type*} [Field F] [Fintype F]
    (I : Finset ι) (D : Finset F) (R : F → F[X]) (P : ι → F[X])
    (K T : ℕ) (δ : ℚ)
    (hq : D.card<Fintype.card F) (hK : K≤D.card)
    (hI : I.Nonempty) (hδ : 0≤δ)
    (A : ℕ) (hgap : A<T)
    (hsource : ∀ β∉D,agreementLE D K
      (fun x => (R β).eval (x:F)*((x:F)-β)⁻¹) A)
    (hdeg : ∀ β∉D,∀ i∈I,(P i-R β).degree≤K)
    (hroots : ∀ i∈I,T≤(D.filter fun x => (P i).eval x=0).card)
    (htotal : (∑ β∈Finset.univ\D,
      (unorderedCollisionCount I (fun i => (P i).eval β):ℚ))≤δ*I.card.choose 2) :
    ∃ f g : D→F,
      agreementEQ D K g K ∧ commonAgreementEQ D K f g K ∧
      agreementLE D K f A ∧
      max (I.card-⌊(δ*I.card.choose 2)/(Fintype.card F-D.card:ℚ)⌋₊)
        ⌈(I.card:ℚ)*(Fintype.card F-D.card:ℚ)/
        ((Fintype.card F-D.card:ℚ)+δ*((I.card:ℚ)-1))⌉₊≤
        (nonzeroBadChallenges D K f g T).card := by
  let exterior := Finset.univ\D
  have hecard : exterior.card=Fintype.card F-D.card := by
    simp [exterior,Finset.card_sdiff]
  have he : exterior.Nonempty := Finset.card_pos.mp (by rw [hecard]; omega)
  obtain ⟨β,hβ,himage⟩ := exists_parameter_image_card_rational_bounds exterior I
    (fun β i => (P i).eval β) (δ*I.card.choose 2) he htotal
  have hβD : β∉D := (Finset.mem_sdiff.mp hβ).2
  let f : D→F := fun x => (R β).eval (x:F)*((x:F)-β)⁻¹
  let g : D→F := fun x => ((x:F)-β)⁻¹
  refine ⟨f,g,agreementEQ_reciprocal D β hβD K hK,
    commonAgreementEQ_reciprocal_right D β hβD K hK f,hsource β hβD,?_⟩
  have himagebad : (I.image (fun i => (P i-R β).eval β)).card≤
      (badChallenges D K f g T).card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hpole := poleReduction_badChallenge D β hβD (R β) (P i-R β) K T (hdeg β hβD i hi) (by
      have heq : R β+(P i-R β)=P i := by ring
      simpa only [heq] using hroots i hi)
    exact hpole
  have himagecard : (I.image (fun i => (P i).eval β)).card=
      (I.image (fun i => (P i-R β).eval β)).card := by
    rw [show I.image (fun i => (P i-R β).eval β)=
      (I.image (fun i => (P i).eval β)).image (fun z => z-(R β).eval β) by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro i hi
        simp]
    symm
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    exact sub_left_injective hxy
  rw [nonzeroBadChallenges_eq_of_source_gap D K A T f g (hsource β hβD) hgap]
  apply le_trans ?_ himagebad
  have ha : (0:ℚ)<(Fintype.card F:ℚ)-D.card := by
    exact sub_pos.mpr (by exact_mod_cast hq)
  have hM : (0:ℚ)<I.card := by exact_mod_cast Finset.card_pos.mpr hI
  have hchoose : (I.card.choose 2:ℚ)=((I.card:ℚ)*((I.card:ℚ)-1))/2 := by
    have hs := sq_eq_add_two_mul_choose_two I.card
    have hsQ : (I.card:ℚ)^2=(I.card:ℚ)+2*(I.card.choose 2:ℚ) := by exact_mod_cast hs
    linarith
  have hden1 : (0:ℚ)<(Fintype.card F-D.card:ℚ)+δ*((I.card:ℚ)-1) := by
    have hM1 : (0:ℚ)≤(I.card:ℚ)-1 := by
      have hh : (1:ℚ)≤I.card := by exact_mod_cast (Finset.card_pos.mpr hI)
      linarith
    exact add_pos_of_pos_of_nonneg ha (mul_nonneg hδ hM1)
  have hratio :
      (I.card:ℚ)*(Fintype.card F-D.card:ℚ)/
          ((Fintype.card F-D.card:ℚ)+δ*((I.card:ℚ)-1)) =
      (exterior.card:ℚ)*I.card^2/
          ((exterior.card:ℚ)*I.card+2*(δ*I.card.choose 2)) := by
    rw [hecard,Nat.cast_sub hq.le,hchoose]
    field_simp [hden1.ne',hM.ne']
  rw [hratio]
  have hfirstCast : (exterior.card:ℚ)=(Fintype.card F-D.card:ℚ) := by
    rw [hecard,Nat.cast_sub hq.le]
  rw [←hfirstCast]
  exact himagecard ▸ himage


/-- A pairwise collision bound gives both nonzero counts without losing a challenge. -/
theorem exists_polePair_of_variableHead_pairwise_collision_bounds
    {ι F : Type*} [LinearOrder ι] [Field F] [Fintype F]
    (I : Finset ι) (D : Finset F) (R : F → F[X]) (P : ι → F[X])
    (K T A δ : ℕ) (hgap : A<T)
    (hq : D.card<Fintype.card F) (hK : K≤D.card)
    (hI : I.Nonempty)
    (hsource : ∀ β∉D,agreementLE D K
      (fun x => (R β).eval (x:F)*((x:F)-β)⁻¹) A)
    (hdeg : ∀ β∉D,∀ i∈I,(P i-R β).degree≤K)
    (hroots : ∀ i∈I,T≤(D.filter fun x => (P i).eval x=0).card)
    (hpair : ∀ i∈I,∀j∈I,i≠j →
      ((Finset.univ\D).filter fun β => (P i).eval β=(P j).eval β).card≤δ) :
    ∃ f g : D→F,
      agreementEQ D K g K ∧ commonAgreementEQ D K f g K ∧
      agreementLE D K f A ∧
      max (I.card-⌊((δ:ℚ)*I.card.choose 2)/(Fintype.card F-D.card:ℚ)⌋₊)
        ⌈(I.card:ℚ)*(Fintype.card F-D.card:ℚ)/
        ((Fintype.card F-D.card:ℚ)+δ*((I.card:ℚ)-1))⌉₊≤
        (nonzeroBadChallenges D K f g T).card := by
  apply exists_polePair_of_variableHead_collision_bounds I D R P K T δ hq hK hI
    (by positivity) A hgap hsource hdeg hroots
  have htotal := sum_unorderedCollisionCount_le_choose_two_mul
    (Finset.univ\D) I (fun β i => (P i).eval β) δ
  have htotal' :
      ∑ β∈Finset.univ\D,unorderedCollisionCount I (fun i => (P i).eval β)≤
        δ*I.card.choose 2 := by
    apply le_trans (htotal (fun i hi j hj hij => hpair i hi j hj hij))
    rw [mul_comm]
  have hcast :
      (∑ β∈Finset.univ\D,
        (unorderedCollisionCount I (fun i => (P i).eval β):ℚ))≤
          (δ:ℚ)*I.card.choose 2 := by
    exact_mod_cast htotal'
  exact hcast

end BinaryFieldCounterexamples
