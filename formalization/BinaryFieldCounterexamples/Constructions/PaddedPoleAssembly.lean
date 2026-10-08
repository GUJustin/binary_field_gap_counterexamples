/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.SupportIncidenceAssembly
public import BinaryFieldCounterexamples.Counting.PaddedIncidence
public import Mathlib.LinearAlgebra.Lagrange
/-!
# Padded locators and the exact half-rate pole bound

Multiplying each actual support locator by the nodal polynomial of a disjoint
padding set preserves the common leading head and raises agreement by the
padding size. Incidence counting supplies the exact rational energy, with
nonzero exterior challenges and strict-degree witnesses for the same input pair.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem eval_nodal_id_eq_zero_iff {F : Type*} [Field F] (W : Finset F) (x : F) :
    (Lagrange.nodal W id).eval x=0 ↔ x∈W := by
  simp [Lagrange.eval_nodal,Finset.prod_eq_zero_iff,sub_eq_zero]

theorem exists_padded_pole_pair
    {ι F : Type*} [LinearOrder ι] [Field F] [Fintype F]
    (I : Finset ι) (D W : Finset F) (A : ι → Finset F) (P : ι → F[X]) (K : ℕ)
    (hWD : W⊆D) (hw : 0<W.card) (hwD : W.card<D.card) (hwK : W.card≤K)
    (hq : D.card<Fintype.card F) (hK : K≤D.card)
    (hA : ∀ i∈I, A i⊆D \ W) (hsize : ∀ i∈I, (A i).card=K)
    (hinj : Set.InjOn A I) (hroot : ∀ i∈I, ∀ x, (P i).eval x=0 ↔ x∈A i)
    (htail : ∀ i∈I, (P i-X^K).natDegree≤K-W.card) :
    let E : ℚ := (((K:ℚ)-W.card-(K:ℚ)^2/((D.card:ℚ)-W.card))*I.card^2+W.card*I.card)/2
    ∃ f g : D → F, commonAgreementEQ D K f g K ∧ agreementEQ D K g K ∧
      agreementLE D K f (K+W.card-1) ∧
      max (I.card-⌊E/(Fintype.card F-D.card)⌋₊)
        ⌈(Fintype.card F-D.card:ℚ)*I.card^2/((Fintype.card F-D.card)*I.card+2*E)⌉₊ ≤
        (nonzeroBadChallenges D K f g (K+W.card)).card := by
  let L := Lagrange.nodal W id
  let R := L*X^K
  let Q : ι → F[X] := fun i => L*P i
  let S : ι → Finset F := fun i => W ∪ A i
  have hL : L≠0 := Lagrange.nodal_ne_zero
  have hRdeg : R.natDegree=W.card+K := by
    rw [natDegree_mul hL (pow_ne_zero _ X_ne_zero),Lagrange.natDegree_nodal,natDegree_X_pow]
  have hS (i) (hi : i∈I) : S i⊆D := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hWD hx
    · exact (Finset.mem_sdiff.mp (hA i hi hx)).1
  have hQroot (i) (hi : i∈I) (x) : (Q i).eval x=0 ↔ x∈S i := by
    simp only [Q,eval_mul,mul_eq_zero,L,eval_nodal_id_eq_zero_iff,hroot i hi x,S,Finset.mem_union]
  have hQdeg (i) (hi : i∈I) : (Q i-R).degree≤(K:WithBot ℕ) := by
    have he : Q i-R=L*(P i-X^K) := by dsimp [Q,R]; ring
    rw [he]
    apply degree_le_of_natDegree_le
    apply natDegree_mul_le.trans
    rw [show L.natDegree=W.card from Lagrange.natDegree_nodal]
    have ht := htail i hi
    omega
  have hQi : Set.InjOn Q I := by
    intro i hi j hj he
    have hp : P i=P j := mul_left_cancel₀ hL he
    apply hinj hi hj
    ext x
    rw [←hroot i hi x,←hroot j hj x,hp]
  have hroots (i) (hi : i∈I) : K+W.card≤(D.filter fun x => (Q i).eval x=0).card := by
    have he : D.filter (fun x => (Q i).eval x=0)=S i := by
      ext x
      simp only [Finset.mem_filter,hQroot i hi x]
      exact ⟨fun hx => hx.2,fun hx => ⟨hS i hi hx,hx⟩⟩
    rw [he]
    have hdis : Disjoint W (A i) := by
      apply Finset.disjoint_left.mpr
      intro x hx ha
      exact (Finset.mem_sdiff.mp (hA i hi ha)).2 hx
    rw [Finset.card_union_of_disjoint hdis,hsize i hi]
    omega
  have htotal := exterior_collision_rational_energy I D S Q K hS
    (fun i hi x hx => (hQroot i hi x).mpr hx) hQi
    (fun i hi j hj hij => by
      have he : Q i-Q j=(Q i-R)-(Q j-R) := by ring
      rw [he]
      exact natDegree_le_of_degree_le ((degree_sub_le _ _).trans (max_le (hQdeg i hi) (hQdeg j hj))))
  have henergy := padded_support_incidence_energy_le I D W A K hWD hwD hA hsize
  have hp := exists_normalizedPolePair_of_collision_budget I D R Q K (K+W.card) _ hq hK
    (by rw [hRdeg]; omega) (by rw [hRdeg]; omega) hQdeg hroots
    (fun β hβ i hi hz => hβ (hS i hi ((hQroot i hi β).mp hz))) (htotal.trans henergy)
  simpa only [hRdeg,Nat.add_comm W.card K] using hp
end BinaryFieldCounterexamples
