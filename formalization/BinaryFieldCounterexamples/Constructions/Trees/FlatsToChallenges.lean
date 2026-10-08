/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.LocatorProductsGeneral
public import BinaryFieldCounterexamples.Constructions.PaddedPoleAssembly
public import BinaryFieldCounterexamples.Counting.CollisionSimplifiedBound
/-!
# Unions of unequal flats give exceptional challenges

Lemma 6.1 (p. 58), `lem:flats-to-challenges`, in Section 6.1 of the manuscript.
A family of distinct nonempty supports of size `T₀`, disjoint from a reserved
set `W`, is converted to one fixed pair at message length `T₀-w+|W|` and
agreement threshold `T₀+|W|`. Flats may have different sizes within and between
supports; every size need only be at least `2w`.

The proof retains the exterior incidence correction, both rounded collision
bounds, exact common and second-input agreement, and the first-input upper
bound `T-1`. In fact the reserved set may have any size, so the paper's empty
or size-`w` alternatives are included.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Padding locators with a common gap, with an arbitrary rational upper bound
on the manuscript exterior incidence expression. No regularity of `W` is used. -/
theorem exists_pair_of_locator_gap_incidence
    {ι F : Type*} [LinearOrder ι] [Field F] [Fintype F]
    (I : Finset ι) (D W : Finset F) (A : ι → Finset F) (P : ι → F[X])
    (T₀ w : ℕ) (E : ℚ)
    (hw : 1 ≤ w) (hTw : w ≤ T₀) (hI : I.Nonempty)
    (hWD : W ⊆ D) (hq : D.card < Fintype.card F)
    (hA : ∀ i ∈ I, A i ⊆ D \ W) (hsize : ∀ i ∈ I, (A i).card = T₀)
    (hinj : Set.InjOn A I)
    (hroot : ∀ i ∈ I, ∀ x, (P i).eval x = 0 ↔ x ∈ A i)
    (htail : ∀ i ∈ I, (P i-X^T₀).natDegree ≤ T₀-w)
    (hE : ((T₀-w : ℕ) : ℚ)*I.card.choose 2 -
      ∑ x ∈ D \ W, (((I.filter fun i => x ∈ A i).card).choose 2 : ℚ) ≤ E) :
    0 ≤ E ∧
    let K : ℕ := T₀-w+W.card
    let T : ℕ := T₀+W.card
    ∃ f g : D → F, commonAgreementEQ D K f g K ∧ agreementEQ D K g K ∧
      agreementLE D K f (T-1) ∧
      max (I.card-⌊E/(Fintype.card F-D.card)⌋₊)
        ⌈(Fintype.card F-D.card : ℚ)*I.card^2/
          ((Fintype.card F-D.card)*I.card+2*E)⌉₊ ≤ (nonzeroBadChallenges D K f g T).card := by
  let L := Lagrange.nodal W id
  let R := L*X^T₀
  let Q : ι → F[X] := fun i => L*P i
  let S : ι → Finset F := fun i => W ∪ A i
  let K := T₀-w+W.card
  have hL : L ≠ 0 := Lagrange.nodal_ne_zero
  have hRdeg : R.natDegree = T₀+W.card := by
    rw [natDegree_mul hL (pow_ne_zero _ X_ne_zero), Lagrange.natDegree_nodal, natDegree_X_pow]
    omega
  have hS (i) (hi : i ∈ I) : S i ⊆ D := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hWD hx
    · exact (Finset.mem_sdiff.mp (hA i hi hx)).1
  have hdis (i) (hi : i ∈ I) : Disjoint W (A i) :=
    Finset.disjoint_left.mpr (fun x hx ha => (Finset.mem_sdiff.mp (hA i hi ha)).2 hx)
  have hSc (i) (hi : i ∈ I) : (S i).card = T₀+W.card := by
    rw [Finset.card_union_of_disjoint (hdis i hi), hsize i hi]
    omega
  have hKN : K ≤ D.card := by
    obtain ⟨i, hi⟩ := hI
    have hn := Finset.card_le_card (hS i hi)
    rw [hSc i hi] at hn
    dsimp [K]
    omega
  have hQroot (i) (hi : i ∈ I) (x) : (Q i).eval x = 0 ↔ x ∈ S i := by
    simp only [Q, eval_mul, mul_eq_zero, L, eval_nodal_id_eq_zero_iff,
      hroot i hi x, S, Finset.mem_union]
  have hQdeg (i) (hi : i ∈ I) : (Q i-R).degree ≤ (K : WithBot ℕ) := by
    have he : Q i-R = L*(P i-X^T₀) := by dsimp [Q, R]; ring
    rw [he]
    apply degree_le_of_natDegree_le
    apply natDegree_mul_le.trans
    rw [show L.natDegree = W.card from Lagrange.natDegree_nodal]
    have ht := htail i hi
    dsimp [K]
    omega
  have hQi : Set.InjOn Q I := by
    intro i hi j hj he
    have hp : P i = P j := mul_left_cancel₀ hL he
    apply hinj hi hj
    ext x
    rw [←hroot i hi x, ←hroot j hj x, hp]
  have hroots (i) (hi : i ∈ I) : T₀+W.card ≤ (D.filter fun x => (Q i).eval x=0).card := by
    have he : D.filter (fun x => (Q i).eval x=0) = S i := by
      ext x
      simp only [Finset.mem_filter, hQroot i hi x]
      exact ⟨fun hx => hx.2, fun hx => ⟨hS i hi hx, hx⟩⟩
    rw [he, hSc i hi]
  -- Shared interior roots leave fewer collision roots outside the domain.
  have htotal := exterior_collision_rational_energy I D S Q K hS
    (fun i hi x hx => (hQroot i hi x).mpr hx) hQi
    (fun i hi j hj hij => by
      have he : Q i-Q j = (Q i-R)-(Q j-R) := by ring
      rw [he]
      exact natDegree_le_of_degree_le ((degree_sub_le _ _).trans
        (max_le (hQdeg i hi) (hQdeg j hj))))
  have hbw (x) (hx : x ∈ W) : (I.filter fun i => x ∈ S i).card = I.card := by
    simp [S, hx]
  have hbo (x) (hx : x ∈ D \ W) :
      (I.filter fun i => x ∈ S i).card = (I.filter fun i => x ∈ A i).card := by
    simp [S, (Finset.mem_sdiff.mp hx).2]
  have hsplit : (∑ x ∈ D, (((I.filter fun i => x ∈ S i).card).choose 2 : ℚ)) =
      (∑ x ∈ D \ W, (((I.filter fun i => x ∈ A i).card).choose 2 : ℚ)) +
        (W.card : ℚ)*I.card.choose 2 := by
    rw [←Finset.sum_sdiff hWD]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      rw [hbo x hx]
    · rw [Finset.sum_congr rfl (fun x hx => by rw [hbw x hx])]
      simp
  rw [hsplit] at htotal
  have hbudget : (∑ β ∈ Finset.univ \ D,
      (unorderedCollisionCount I (fun i => (Q i).eval β) : ℚ)) ≤ E := by
    have hk : (K : ℚ) = (T₀-w : ℕ)+ (W.card : ℚ) := by dsimp [K]; norm_cast
    rw [hk] at htotal
    linarith
  have hE0 : 0 ≤ E := le_trans (by positivity) hbudget
  refine ⟨hE0, ?_⟩
  -- Pool collisions at one pole, then construct the fixed received pair.
  have hp := exists_normalizedPolePair_of_collision_budget I D R Q K (T₀+W.card) E hq hKN
    (by rw [hRdeg]; omega) (by rw [hRdeg]; dsimp [K]; omega) hQdeg hroots
    (fun β hβ i hi hz => hβ (hS i hi ((hQroot i hi β).mp hz))) hbudget
  simpa only [hRdeg] using hp

/-- The full unequal-flat construction of Lemma 6.1, for any rational budget
satisfying its incidence inequality. The number of flats may also vary by set. -/
theorem flats_to_challenges_rational
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (D W : Finset F) (family : Finset (Finset F)) (T₀ w : ℕ) (E : ℚ)
    (hw : 1 ≤ w) (hfamily : family.Nonempty) (hWD : W ⊆ D)
    (hq : D.card < Fintype.card F)
    (hA : ∀ S ∈ family, S ⊆ D \ W) (hsize : ∀ S ∈ family, S.card = T₀)
    (hne : ∀ S ∈ family, S.Nonempty)
    (hflats : ∀ S ∈ family, ∃ n : ℕ, ∃ A : Fin n → AffineSubspace (ZMod 2) F,
      (S : Set F) = ⋃ i, (A i : Set F) ∧
      (∀ i, (A i : Set F).Nonempty) ∧
      Pairwise (fun i j => Disjoint (A i : Set F) (A j : Set F)) ∧
      (∀ i, 2*w ≤ Nat.card (A i)))
    (hE : ((T₀-w : ℕ) : ℚ)*family.card.choose 2 -
      ∑ x ∈ D \ W, (((family.filter fun S => x ∈ S).card).choose 2 : ℚ) ≤ E) :
    0 ≤ E ∧
    let K : ℕ := T₀-w+W.card
    let T : ℕ := T₀+W.card
    ∃ f g : D → F, commonAgreementEQ D K f g K ∧ agreementEQ D K g K ∧
      agreementLE D K f (T-1) ∧
      max (family.card-⌊E/(Fintype.card F-D.card)⌋₊)
        ⌈(Fintype.card F-D.card : ℚ)*family.card^2/
          ((Fintype.card F-D.card)*family.card+2*E)⌉₊ ≤ (nonzeroBadChallenges D K f g T).card := by
  let : LinearOrder (Finset F) := (Fintype.equivFin (Finset F)).linearOrder
  have hloc (S) (hS : S ∈ family) : ∃ P : F[X], P.Monic ∧ P.natDegree = T₀ ∧
      (∀ x, P.eval x = 0 ↔ x ∈ S) ∧ (P-X^T₀).natDegree ≤ T₀-w := by
    obtain ⟨n, A, he, hn, hd, hs⟩ := hflats S hS
    simpa only [hsize S hS] using
      exists_locator_of_variable_affine_flat_union S A w hw he hn hd hs
  let P : Finset F → F[X] := fun S => if hS : S ∈ family then (hloc S hS).choose else 0
  have hP (S) (hS : S ∈ family) : (P S).Monic ∧ (P S).natDegree = T₀ ∧
      (∀ x, (P S).eval x = 0 ↔ x ∈ S) ∧ (P S-X^T₀).natDegree ≤ T₀-w := by
    simpa only [P, dite_eq_left hS] using (hloc S hS).choose_spec
  have hTw : w ≤ T₀ := by
    obtain ⟨S, hS⟩ := hfamily
    obtain ⟨x, hx⟩ := hne S hS
    obtain ⟨n, A, he, hn, hd, hs⟩ := hflats S hS
    have hx' : x ∈ (S : Set F) := hx
    rw [he, Set.mem_iUnion] at hx'
    obtain ⟨i, hi⟩ := hx'
    have hsub : (A i : Set F) ⊆ S := by rw [he]; exact Set.subset_iUnion (fun j => (A j : Set F)) i
    have hc : Nat.card (A i) ≤ S.card := by
      let f : A i → S := fun y => ⟨y, hsub y.property⟩
      have hf : Function.Injective f := fun y z he => Subtype.ext (congrArg (fun u : S => (u : F)) he)
      have hh := Fintype.card_le_of_injective f hf
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hh
    have hh := hs i
    rw [hsize S hS] at hc
    omega
  exact exists_pair_of_locator_gap_incidence family D W id P T₀ w E hw hTw hfamily
    hWD hq hA hsize (fun i hi j hj he => he)
    (fun S hS => (hP S hS).2.2.1)
    (fun S hS => (hP S hS).2.2.2) hE

/-- Lemma 6.1 in full: any real number satisfying the incidence inequality
gives the stated pair and literal `Z(M,F)` distinct nonzero challenges.
The domain need not be additive, and `W` may have arbitrary size. -/
theorem flats_to_challenges
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (D W : Finset F) (family : Finset (Finset F)) (T₀ w : ℕ) (budget : ℝ)
    (hw : 1 ≤ w) (hfamily : family.Nonempty) (hWD : W ⊆ D)
    (hq : D.card < Fintype.card F)
    (hA : ∀ S ∈ family, S ⊆ D \ W) (hsize : ∀ S ∈ family, S.card = T₀)
    (hne : ∀ S ∈ family, S.Nonempty)
    (hflats : ∀ S ∈ family, ∃ n : ℕ, ∃ A : Fin n → AffineSubspace (ZMod 2) F,
      (S : Set F) = ⋃ i, (A i : Set F) ∧
      (∀ i, (A i : Set F).Nonempty) ∧
      Pairwise (fun i j => Disjoint (A i : Set F) (A j : Set F)) ∧
      (∀ i, 2*w ≤ Nat.card (A i)))
    (hE : ((T₀-w : ℕ) : ℝ)*family.card.choose 2 -
      ∑ x ∈ D \ W, (((family.filter fun S => x ∈ S).card).choose 2 : ℝ) ≤ budget) :
    0 ≤ budget ∧
    let K : ℕ := T₀-w+W.card
    let T : ℕ := T₀+W.card
    ∃ f g : D → F, commonAgreementEQ D K f g K ∧ agreementEQ D K g K ∧
      agreementLE D K f (T-1) ∧
      max (family.card-⌊budget/(Fintype.card F-D.card)⌋₊)
        ⌈(Fintype.card F-D.card : ℝ)*family.card^2/
          ((Fintype.card F-D.card)*family.card+2*budget)⌉₊ ≤ (nonzeroBadChallenges D K f g T).card := by
  -- Use the exact rational incidence energy, then enlarge to the real budget.
  let E : ℚ := ((T₀-w : ℕ) : ℚ)*family.card.choose 2 -
    ∑ x ∈ D \ W, (((family.filter fun S => x ∈ S).card).choose 2 : ℚ)
  obtain ⟨hE0, f, g, hcommon, hright, hleft, hcount⟩ :=
    flats_to_challenges_rational D W family T₀ w E hw hfamily hWD hq
      hA hsize hne hflats (le_refl E)
  have hEB : (E : ℝ) ≤ budget := by
    simpa only [E, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sum] using hE
  have hb0 : 0 ≤ budget := (by exact_mod_cast hE0 : (0 : ℝ) ≤ E).trans hEB
  refine ⟨hb0, f, g, hcommon, hright, hleft, ?_⟩
  exact (real_collision_bound_le_rat_of_budget_le D.card family.card (Fintype.card F)
    E budget (Finset.card_pos.mpr hfamily) hq hE0 hEB).trans hcount

end BinaryFieldCounterexamples
