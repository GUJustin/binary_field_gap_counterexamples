/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.Intrinsic.HeightTwo
/-!
# The three height-two root decompositions

This proves the unnumbered height-two observations immediately before
Definition 6.3 and after Lemma 6.5 in `additive-support-trees.tex`. The literal
function `(1+s)a+sb` is an intrinsic height-two tree. Its four-point support
has exactly three partitions into affine lines, obtained by three different
linear first tests. The two lines in each partition are not parallel: their
directions differ. Their containing root-test slices are parallel planes.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees

attribute [local instance] binaryFintype

/-- The function `(1+s)a+sb` from the height-two prose before Definition 6.3,
with coordinates ordered as `s,a,b`. -/
def heightTwoMux (x : Fin 3 → ZMod 2) : ZMod 2 :=
  (1 + x 0) * x 1 + x 0 * x 2

/-- The three independent coordinate triples giving the same height-two
function in the prose before Definition 6.3 and after Lemma 6.5. -/
def heightTwoDecompositionCoordinates (i : Fin 3) (x : Fin 3 → ZMod 2) :
    Fin 3 → ZMod 2 :=
  ![![x 0, x 1, x 2], ![x 1 + x 2, x 1, x 1 + x 0],
    ![x 0 + x 1 + x 2, x 1 + x 0, x 1]] i

/-- The coordinate triples in the height-two observation before Definition 6.3
are invertible linear changes of coordinates. -/
def heightTwoDecompositionLinear (i : Fin 3) :
    (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  { toFun := heightTwoDecompositionCoordinates i,
    map_add' := by
      intro x y
      ext j
      fin_cases i <;> fin_cases j <;>
        simp [heightTwoDecompositionCoordinates] <;> ring,
    map_smul' := by
      intro a x
      ext j
      fin_cases i <;> fin_cases j <;>
        simp [heightTwoDecompositionCoordinates, mul_add] }

/-- Each coordinate triple in the height-two observation before Definition 6.3
is bijective, so its three linear tests are independent. -/
theorem heightTwoDecompositionCoordinates_bijective :
    ∀ i : Fin 3, Function.Bijective (heightTwoDecompositionCoordinates i) := by
  decide +kernel

/-- All three height-two coordinate triples in the prose after Lemma 6.5
compute exactly the same function, using the repository's `branch` operation. -/
theorem heightTwoDecomposition_branch : ∀ (i : Fin 3) (x : Fin 3 → ZMod 2),
    branch (fun a : ZMod 2 => a) (fun b : ZMod 2 => b)
      ((heightTwoDecompositionCoordinates i x) 0,
        (heightTwoDecompositionCoordinates i x) 1,
        (heightTwoDecompositionCoordinates i x) 2) = heightTwoMux x := by
  decide +kernel

/-- The first tests of the three height-two decompositions before Definition 6.3
are literal linear functionals, rather than roots with the height-three guard. -/
def heightTwoDecompositionFirstTest (i : Fin 3) :
    Module.Dual (ZMod 2) (Fin 3 → ZMod 2) :=
  (LinearMap.proj 0).comp (heightTwoDecompositionLinear i)

/-- The three root decompositions in the height-two prose after Lemma 6.5
have three different first linear tests. -/
theorem heightTwoDecompositionFirstTest_injective :
    Function.Injective heightTwoDecompositionFirstTest := by
  intro i j h
  have ht : (fun x => (heightTwoDecompositionCoordinates i x) 0) =
      (fun x => (heightTwoDecompositionCoordinates j x) 0) := by
    exact congrArg (fun l : Module.Dual (ZMod 2) (Fin 3 → ZMod 2) => fun x => l x) h
  have hi : ∀ i j : Fin 3,
      (∀ x, (heightTwoDecompositionCoordinates i x) 0 =
        (heightTwoDecompositionCoordinates j x) 0) → i = j := by
    decide +kernel
  exact hi i j (congrFun ht)

/-- Each of the three first linear tests in the height-two observation before
Definition 6.3 is nonzero. -/
theorem heightTwoDecompositionFirstTest_nonzero (i : Fin 3) :
    heightTwoDecompositionFirstTest i ≠ 0 := by
  have h : ∀ i : Fin 3, ∃ x : Fin 3 → ZMod 2,
      (heightTwoDecompositionCoordinates i x) 0 = 1 := by
    decide +kernel
  obtain ⟨x, hx⟩ := h i
  intro hz
  have he := LinearMap.congr_fun hz x
  change (heightTwoDecompositionCoordinates i x) 0 = 0 at he
  rw [hx] at he
  norm_num at he

/-- The four-point support in the height-two observation before Definition 6.3. -/
def heightTwoMuxSupport : Finset (Fin 3 → ZMod 2) :=
  Finset.univ.filter (fun x => heightTwoMux x = 1)

/-- The height-two function before Definition 6.3 has exactly four support points. -/
theorem heightTwoMuxSupport_card : heightTwoMuxSupport.card = 4 := by
  decide +kernel

/-- An unordered partition into two two-point lines, as in the height-two
observation before Definition 6.3. The parts are disjoint subsets of the support. -/
def heightTwoMuxLinePartitions : Finset (Finset (Finset (Fin 3 → ZMod 2))) :=
  (heightTwoMuxSupport.powersetCard 2).powersetCard 2 |>.filter
    (fun P => ∀ L ∈ P, ∀ M ∈ P, L ≠ M → Disjoint L M)

/-- Exactly three unordered line partitions occur in the height-two
observation before Definition 6.3. -/
theorem heightTwoMuxLinePartitions_card : heightTwoMuxLinePartitions.card = 3 := by
  decide +kernel

/-- The two support fibers of each first test in the height-two observation
before Definition 6.3, regarded as an unordered line partition. -/
def heightTwoDecompositionLinePartition (i : Fin 3) :
    Finset (Finset (Fin 3 → ZMod 2)) :=
  {heightTwoMuxSupport.filter (fun x => (heightTwoDecompositionCoordinates i x) 0 = 0),
   heightTwoMuxSupport.filter (fun x => (heightTwoDecompositionCoordinates i x) 0 = 1)}

/-- The three different first tests exhaust exactly the three unordered support
partitions in the height-two prose before Definition 6.3. -/
theorem heightTwoMuxLinePartitions_eq_firstTests :
    heightTwoMuxLinePartitions = Finset.univ.image heightTwoDecompositionLinePartition := by
  decide +kernel

/-- The two parts cover all four points in every line partition from the
height-two observation before Definition 6.3. -/
theorem heightTwoMuxLinePartitions_cover (P : Finset (Finset (Fin 3 → ZMod 2)))
    (hP : P ∈ heightTwoMuxLinePartitions) : P.biUnion id = heightTwoMuxSupport := by
  rw [heightTwoMuxLinePartitions_eq_firstTests] at hP
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hP
  have h : ∀ i : Fin 3,
      (heightTwoDecompositionLinePartition i).biUnion id = heightTwoMuxSupport := by
    decide +kernel
  exact h i

/-- The three first tests give distinct support partitions, as asserted in the
height-two prose before Definition 6.3. -/
theorem heightTwoDecompositionLinePartition_injective :
    Function.Injective heightTwoDecompositionLinePartition := by
  decide +kernel

/-- Every part in the height-two support partitions before Definition 6.3 is
an actual affine line over the binary field. -/
theorem heightTwoDecomposition_parts_are_affine_lines : ∀ i : Fin 3,
    ∀ b : ZMod 2, ∃ p d : Fin 3 → ZMod 2, d ≠ 0 ∧
      heightTwoMuxSupport.filter (fun x => (heightTwoDecompositionCoordinates i x) 0 = b) =
        {p, p + d} := by
  decide +kernel

/-- The affine lines in the height-two observation before Definition 6.3 are
not parallel: no nonzero direction can describe both support fibers. -/
theorem heightTwoDecomposition_lines_not_parallel : ∀ i : Fin 3,
    ¬ ∃ p q d : Fin 3 → ZMod 2, d ≠ 0 ∧
      heightTwoMuxSupport.filter (fun x => (heightTwoDecompositionCoordinates i x) 0 = 0) =
        {p, p + d} ∧
      heightTwoMuxSupport.filter (fun x => (heightTwoDecompositionCoordinates i x) 0 = 1) =
        {q, q + d} := by
  decide +kernel

/-- The function in the height-two observation before Definition 6.3 is a tree
of actual height two under the repository's intrinsic tree definition. -/
theorem heightTwoMux_isTreeFunction : IsTreeFunction 2 heightTwoMux := by
  rw [isTreeFunction_two, isHeightTwoTree_iff_balanced_essentialDimension]
  refine ⟨?_, ?_⟩
  · intro b
    have hb : ∀ b : ZMod 2,
        Fintype.card {x : Fin 3 → ZMod 2 // heightTwoMux x = b} = 4 := by
      decide +kernel
    simp only [Nat.card_eq_fintype_card, hb]
    norm_num [Fintype.card_fun]
  · have hp : ∀ u : Fin 3 → ZMod 2,
        (∀ x, heightTwoMux (x + u) = heightTwoMux x) → u = 0 := by
      decide +kernel
    have hbot : periodSubmodule heightTwoMux = ⊥ := by
      apply eq_bot_iff.mpr
      intro u hu
      exact hp u hu
    rw [essentialDimension_eq_finrank_sub, hbot]
    simp

/-- On any three-dimensional binary space with coordinates `s,a,b`, the
height-two observation before Definition 6.3 and after Lemma 6.5 supplies an
actual intrinsic height-two tree and three distinct independent linear root
decompositions of the very same function. -/
theorem heightTwoMux_coordinate_transport {U : Type*} [AddCommGroup U]
    [Module (ZMod 2) U] [Finite U]
    (e : U ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    IsTreeFunction 2 (fun x => heightTwoMux (e x)) ∧
      Function.Injective (fun i : Fin 3 =>
        (heightTwoDecompositionFirstTest i).comp e.toLinearMap) ∧
      ∀ i : Fin 3, Function.Bijective (fun x => heightTwoDecompositionCoordinates i (e x)) ∧
        ∀ x : U, branch (fun a : ZMod 2 => a) (fun b : ZMod 2 => b)
          ((heightTwoDecompositionCoordinates i (e x)) 0,
            (heightTwoDecompositionCoordinates i (e x)) 1,
            (heightTwoDecompositionCoordinates i (e x)) 2) = heightTwoMux (e x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [isTreeFunction_two]
    apply (isHeightTwoTree_affineMap_precompose_iff heightTwoMux
      e.toAffineEquiv.toAffineMap e.surjective).mpr
    exact isTreeFunction_two _ |>.mp heightTwoMux_isTreeFunction
  · intro i j hij
    apply heightTwoDecompositionFirstTest_injective
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun hij (e.symm x)
    simpa using h
  · intro i
    exact ⟨(heightTwoDecompositionCoordinates_bijective i).comp e.bijective,
      fun x => heightTwoDecomposition_branch i (e x)⟩

end BinaryFieldCounterexamples.Trees
