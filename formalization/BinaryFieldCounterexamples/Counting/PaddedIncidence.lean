/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.CollisionAveraging
/-!
# Incidence energy for padded supports

All supports contain the same padding set, while their remaining parts have
the same size and avoid the padding. Double counting and Cauchy--Schwarz give
the manuscript rational collision energy without assuming uniform incidence
on the unpadded coordinates.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sum_choose_two_lower_bound
    {X : Type*} (D : Finset X) (a : X → ℕ) (hD : 0<D.card) :
    (((∑ x∈D, (a x:ℚ))^2/D.card)-(∑ x∈D, (a x:ℚ)))/2 ≤
      ∑ x∈D, ((a x).choose 2:ℚ) := by
  have he : (∑ x∈D, (a x:ℚ)^2)=(∑ x∈D, (a x:ℚ))+2*∑ x∈D, ((a x).choose 2:ℚ) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    exact_mod_cast sq_eq_add_two_mul_choose_two (a x)
  have hc := sq_sum_le_card_mul_sum_sq (s := D) (f := fun x => (a x:ℚ))
  rw [he] at hc
  have hd : (0:ℚ)<D.card := by exact_mod_cast hD
  have hh : (∑ x∈D, (a x:ℚ))^2/D.card≤(∑ x∈D, (a x:ℚ))+2*∑ x∈D, ((a x).choose 2:ℚ) :=
    (div_le_iff₀ hd).mpr (by linarith [hc])
  linarith

theorem sum_support_incidence_eq_sum_card
    {ι X : Type*} (I : Finset ι) (D : Finset X) (S : ι → Finset X)
    (hS : ∀ i∈I, S i⊆D) :
    (∑ x∈D, (I.filter fun i => x∈S i).card)=∑ i∈I, (S i).card := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Finset.card_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun hx => hx.2,fun hx => ⟨hS i hi hx,hx⟩⟩

theorem padded_support_incidence_energy_le
    {ι X : Type*} (I : Finset ι) (D W : Finset X) (A : ι → Finset X) (K : ℕ)
    (hWD : W⊆D) (hw : W.card<D.card)
    (hA : ∀ i∈I, A i⊆D \ W) (hsize : ∀ i∈I, (A i).card=K) :
    (K:ℚ)*I.card.choose 2-∑ x∈D, (((I.filter fun i => x∈W ∪ A i).card).choose 2:ℚ) ≤
      (((K:ℚ)-W.card-(K:ℚ)^2/((D.card:ℚ)-W.card))*I.card^2+W.card*I.card)/2 := by
  let a : X → ℕ := fun x => (I.filter fun i => x∈A i).card
  let b : X → ℕ := fun x => (I.filter fun i => x∈W ∪ A i).card
  have hbw (x) (hx : x∈W) : b x=I.card := by simp [b,hx]
  have hbo (x) (hx : x∈D \ W) : b x=a x := by
    have hn := (Finset.mem_sdiff.mp hx).2
    simp [b,a,hn]
  have hd : (D \ W).card=D.card-W.card := Finset.card_sdiff_of_subset hWD
  have hmassN : (∑ x∈D \ W, a x)=K*I.card := by
    rw [sum_support_incidence_eq_sum_card I (D \ W) A hA]
    rw [Finset.sum_congr rfl hsize]
    simp [mul_comm]
  have hmass : (∑ x∈D \ W, (a x:ℚ))=(K:ℚ)*I.card := by exact_mod_cast hmassN
  have hc := sum_choose_two_lower_bound (D \ W) a (by rw [hd]; omega)
  rw [hmass,hd,Nat.cast_sub (Finset.card_le_card hWD)] at hc
  have hsplit : (∑ x∈D, ((b x).choose 2:ℚ))=
      (∑ x∈D \ W, ((a x).choose 2:ℚ))+(W.card:ℚ)*I.card.choose 2 := by
    rw [←Finset.sum_sdiff hWD]
    congr 1
    · exact Finset.sum_congr rfl (fun x hx => by rw [hbo x hx])
    · rw [Finset.sum_congr rfl (fun x hx => by rw [hbw x hx])]
      simp
  change (K:ℚ)*I.card.choose 2-(∑ x∈D, ((b x).choose 2:ℚ))≤_
  rw [hsplit]
  have hchoose : (I.card.choose 2:ℚ)=((I.card:ℚ)^2-I.card)/2 := by
    have he : (I.card:ℚ)^2=(I.card:ℚ)+2*(I.card.choose 2:ℚ) := by
      exact_mod_cast sq_eq_add_two_mul_choose_two I.card
    linarith
  calc
    _ ≤ (K:ℚ)*I.card.choose 2-
        ((((K:ℚ)*I.card)^2/((D.card:ℚ)-W.card)-(K:ℚ)*I.card)/2+(W.card:ℚ)*I.card.choose 2) := by linarith
    _ = _ := by rw [hchoose]; ring
end BinaryFieldCounterexamples
