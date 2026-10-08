/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.RationalCollision
public import BinaryFieldCounterexamples.Constructions.PoleReduction
public import BinaryFieldCounterexamples.Agreement.Interpolation
/-!
# Normalized pole reduction

A divided difference of the common polynomial head gives a first input whose degree
is exactly one less than the head degree. Exterior evaluations of the full
locators are nonzero challenges, so rational collision averaging keeps
both challenge-count bounds without deleting a challenge.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def normalizedPoleSource {F : Type*} [Field F] (R : F[X]) (β : F) : F[X] :=
  (R-C (R.eval β))/(X-C β)

theorem normalizedPoleSource_natDegree {F : Type*} [Field F] (R : F[X]) (β : F) :
    (normalizedPoleSource R β).natDegree=R.natDegree-1 := by
  rw [normalizedPoleSource,←divByMonic_eq_div _ (monic_X_sub_C β),natDegree_divByMonic _ (monic_X_sub_C β),
    natDegree_sub_C,natDegree_X_sub_C]

theorem normalizedPoleSource_eval {F : Type*} [Field F] (R : F[X]) (β x : F) (hx : x≠β) :
    (normalizedPoleSource R β).eval x=(R.eval x-R.eval β)/(x-β) := by
  have h := poleCorrection_eval R β x hx
  simpa only [poleCorrection,normalizedPoleSource,eval_neg,neg_inj] using h

theorem normalizedPoleSource_ne_zero {F : Type*} [Field F] (R : F[X]) (β : F)
    (hR : 0<R.natDegree) : normalizedPoleSource R β≠0 := by
  intro hz
  have hm := (mul_div_eq_iff_isRoot (p := R-C (R.eval β)) (a := β)).mpr (by simp [IsRoot])
  change (X-C β)*normalizedPoleSource R β=R-C (R.eval β) at hm
  rw [hz,mul_zero] at hm
  have hd := congrArg natDegree hm
  rw [natDegree_zero,natDegree_sub_C] at hd
  omega

theorem agreementLE_normalizedPoleSource {F : Type*} [Field F]
    (D : Finset F) (R : F[X]) (β : F) (K : ℕ) (hR : 0<R.natDegree) (hK : K≤R.natDegree-1) :
    agreementLE D K (fun x => (normalizedPoleSource R β).eval (x:F)) (R.natDegree-1) := by
  have hd : (K : WithBot ℕ)≤(normalizedPoleSource R β).degree := by
    rw [degree_eq_natDegree (normalizedPoleSource_ne_zero R β hR),normalizedPoleSource_natDegree]
    exact_mod_cast hK
  simpa only [normalizedPoleSource_natDegree] using agreementLE_polynomial D K (normalizedPoleSource R β) hd

theorem normalizedPoleReduction_agreementGE
    {F : Type*} [Field F]
    (D : Finset F) (β : F) (hβ : β ∉ D) (R C : F[X])
    (K T : ℕ) (hC : C.degree≤K)
    (hroots : T≤(D.filter (fun x => (R+C).eval x=0)).card) :
    agreementGE D K (fun x => (normalizedPoleSource R β).eval (x:F)+
      (R+C).eval β*((x:F)-β)⁻¹) T := by
  have h := poleReduction_agreementGE D β hβ R C K T hC hroots
  have hw : (fun x : D => (normalizedPoleSource R β).eval (x:F)+(R+C).eval β*((x:F)-β)⁻¹)=
      (fun x : D => R.eval (x:F)*((x:F)-β)⁻¹+C.eval β*((x:F)-β)⁻¹) := by
    funext x
    rw [normalizedPoleSource_eval R β x (fun he => hβ (he ▸ x.property)),eval_add,div_eq_mul_inv]
    ring
  rw [hw]
  exact h
theorem normalizedPoleReduction_nonzero_image_card_le
    {ι F : Type*} [Field F] [Fintype F]
    (I : Finset ι) (D : Finset F) (β : F) (hβ : β ∉ D) (R : F[X]) (P : ι → F[X])
    (K T : ℕ) (hdeg : ∀ i ∈ I, (P i-R).degree≤K)
    (hroots : ∀ i ∈ I, T≤(D.filter (fun x => (P i).eval x=0)).card)
    (hnonzero : ∀ i ∈ I, (P i).eval β≠0) :
    (I.image (fun i => (P i).eval β)).card≤
      (nonzeroBadChallenges D K (fun x => (normalizedPoleSource R β).eval (x:F))
        (fun x => ((x:F)-β)⁻¹) T).card := by
  classical
  apply Finset.card_le_card
  intro z hz
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
  apply Finset.mem_erase.mpr
  refine ⟨hnonzero i hi,(mem_badChallenges D K _ _ T _).mpr ?_⟩
  have he : R+(P i-R)=P i := by ring
  have hr : T≤(D.filter (fun x => (R+(P i-R)).eval x=0)).card := by rw [he]; exact hroots i hi
  have h := normalizedPoleReduction_agreementGE D β hβ R (P i-R) K T (hdeg i hi) hr
  simpa only [he] using h
theorem exists_normalizedPolePair_of_collision_budget
    {ι F : Type*} [Field F] [Fintype F]
    (I : Finset ι) (D : Finset F) (R : F[X]) (P : ι → F[X]) (K T : ℕ) (energy : ℚ)
    (hq : D.card<Fintype.card F) (hK : K≤D.card)
    (hR : 0<R.natDegree) (hKR : K≤R.natDegree-1)
    (hdeg : ∀ i ∈ I, (P i-R).degree≤K)
    (hroots : ∀ i ∈ I, T≤(D.filter (fun x => (P i).eval x=0)).card)
    (hnonzero : ∀ β ∉ D, ∀ i ∈ I, (P i).eval β≠0)
    (htotal : (∑ β ∈ Finset.univ \ D,
      (unorderedCollisionCount I (fun i => (P i).eval β) : ℚ))≤energy) :
    ∃ f g : D → F, commonAgreementEQ D K f g K ∧ agreementEQ D K g K ∧
      agreementLE D K f (R.natDegree-1) ∧
      max (I.card-⌊energy/(Fintype.card F-D.card)⌋₊)
        ⌈(Fintype.card F-D.card : ℚ)*I.card^2/
          ((Fintype.card F-D.card)*I.card+2*energy)⌉₊≤(nonzeroBadChallenges D K f g T).card := by
  classical
  let exterior := Finset.univ \ D
  have hc : exterior.card=Fintype.card F-D.card := by
    simp [exterior,Finset.card_sdiff]
  have hn : exterior.Nonempty := Finset.card_pos.mp (by rw [hc]; omega)
  obtain ⟨β,hβ,hbound⟩ := exists_parameter_image_card_rational_bounds exterior I
    (fun β i => (P i).eval β) energy hn htotal
  have hβD : β ∉ D := (Finset.mem_sdiff.mp hβ).2
  refine ⟨(fun x => (normalizedPoleSource R β).eval (x:F)),(fun x => ((x:F)-β)⁻¹),
    commonAgreementEQ_reciprocal_right D β hβD K hK _,agreementEQ_reciprocal D β hβD K hK,
    agreementLE_normalizedPoleSource D R β K hR hKR,?_⟩
  have himage := normalizedPoleReduction_nonzero_image_card_le I D β hβD R P K T hdeg hroots
    (hnonzero β hβD)
  apply le_trans ?_ himage
  simpa only [hc,Nat.cast_sub hq.le] using hbound
end BinaryFieldCounterexamples
