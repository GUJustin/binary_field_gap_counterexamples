/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Projection
public import BinaryFieldCounterexamples.Agreement.Domains
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Independent extension parameters

A sufficiently large finite extension contains a normalized independent frame
`1, θ₁, …, θ_{s-1}, τ`. Coordinate projections on this frame show that
base-affine challenges shifted by `τ` are distinct and nonzero. The `τ` projection
also isolates the direction used by the first input.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

namespace AllRatesConstruction

open Finset Polynomial

attribute [local instance] Classical.decEq Classical.propDecidable

/-- Cardinality at least `|B|^n` gives a normalized `B`-independent frame of
length `n`, whose first vector is one. -/
theorem exists_normalized_independent_frame
    {B F : Type*} [Field B] [Fintype B] [Field F] [Fintype F] [Algebra B F]
    (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card B ^ n ≤ Fintype.card F) :
    ∃ v : Fin n → F, LinearIndependent B v ∧ v ⟨0, by omega⟩ = 1 := by
  classical
  have hb : 1 < Fintype.card B := Fintype.one_lt_card
  have hfin : n ≤ Module.finrank B F := by
    rw [Module.card_eq_pow_finrank (K := B) (V := F)] at hcard
    exact (Nat.pow_le_pow_iff_right hb).mp hcard
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hfin
  have hv0 : v ⟨0, by omega⟩ ≠ 0 := hv.ne_zero ⟨0, by omega⟩
  let c : F := (v ⟨0, by omega⟩)⁻¹
  let L : F →ₗ[B] F := LinearMap.mulRight B c
  have hc : c ≠ 0 := inv_ne_zero hv0
  have hL : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr (by
    intro x y hxy
    change x * c = y * c at hxy
    exact mul_right_cancel₀ hc hxy)
  let w : Fin n → F := fun i ↦ L (v i)
  have hw : LinearIndependent B w := by
    exact hv.map' L hL
  refine ⟨w, hw, ?_⟩
  simp [w, L, c, hv0]

/-- A coordinate functional dual to one member of a linearly independent
finite frame, extended from its span to the ambient space. -/
noncomputable def independentFrameCoordinate
    {B F ι : Type*} [Field B] [Field F] [Algebra B F] [Fintype ι]
    (v : ι → F) (hv : LinearIndependent B v) (i : ι) : F →ₗ[B] B :=
  Classical.choose (LinearMap.exists_extend
    ((Finsupp.lapply i).comp hv.repr))

/-- The extended coordinate functionals have the expected Kronecker values. -/
theorem independentFrameCoordinate_apply
    {B F ι : Type*} [Field B] [Field F] [Algebra B F] [Fintype ι]
    (v : ι → F) (hv : LinearIndependent B v) (i j : ι) :
    independentFrameCoordinate v hv i (v j) = if i = j then 1 else 0 := by
  classical
  let T : Submodule B F := Submodule.span B (Set.range v)
  have hvj : v j ∈ T := Submodule.subset_span ⟨j, rfl⟩
  have hext : (independentFrameCoordinate v hv i).comp
      (Submodule.span B (Set.range v)).subtype = (Finsupp.lapply i).comp hv.repr := by
    unfold independentFrameCoordinate
    exact Classical.choose_spec (LinearMap.exists_extend
      ((Finsupp.lapply i).comp hv.repr))
  have happ := DFunLike.congr_fun hext ⟨v j, hvj⟩
  have happ' : independentFrameCoordinate v hv i (v j) =
      ((Finsupp.lapply i).comp hv.repr) ⟨v j, hvj⟩ := by
    simpa only [LinearMap.comp_apply, Submodule.coe_subtype] using happ
  rw [happ']
  have hrepr : hv.repr ⟨v j, hvj⟩ = Finsupp.single j 1 := by
    apply hv.repr_eq
    simp
  rw [LinearMap.comp_apply, hrepr]
  simp [Finsupp.lapply, Finsupp.single_apply, eq_comm]

/-- Position of parameter `θ_j` inside the frame
`1, θ₁, …, θ_{s-1}, τ`. -/
def extensionThetaIndex (s : ℕ) (j : Fin (s - 1)) : Fin (s + 1) :=
  ⟨j.1 + 1, by omega⟩

/-- The genuine parameter positions in the extension frame are distinct. -/
theorem extensionThetaIndex_injective (s : ℕ) :
    Function.Injective (extensionThetaIndex s) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [extensionThetaIndex] at hv
  omega

/-- No genuine parameter occupies the final `τ` position. -/
theorem extensionThetaIndex_ne_last (s : ℕ) (j : Fin (s - 1)) :
    extensionThetaIndex s j ≠ Fin.last s := by
  intro h
  have hv := congrArg Fin.val h
  simp [extensionThetaIndex] at hv
  omega

/-- Evaluate a base-field affine functional using the independent extension
parameters in positions `1,…,s-1`. -/
def extensionAffineValue
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F)
    (A : (Fin (s - 1) → B) →ᵃ[B] B) : F :=
  algebraMap B F (A 0) +
    ∑ j : Fin (s - 1), algebraMap B F (A.linear (Pi.single j 1)) *
      v (extensionThetaIndex s j)

/-- Coordinate zero extracts the constant term of an extension affine value. -/
theorem independentFrameCoordinate_extensionAffineValue_zero
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F) (hv : LinearIndependent B v)
    (hv0 : v 0 = 1) (A : (Fin (s - 1) → B) →ᵃ[B] B) :
    independentFrameCoordinate v hv 0 (extensionAffineValue s v A) = A 0 := by
  let l := independentFrameCoordinate v hv (0 : Fin (s + 1))
  have hmul (b : B) (x : F) : l (algebraMap B F b * x) = b * l x := by
    simpa [Algebra.smul_def] using l.map_smul b x
  have hl1 : l 1 = 1 := by
    rw [← hv0]
    simpa [l] using independentFrameCoordinate_apply v hv (0 : Fin (s + 1)) 0
  have hbase (b : B) : l (algebraMap B F b) = b := by
    simpa [hl1] using hmul b 1
  have htheta (j : Fin (s - 1)) : l (v (extensionThetaIndex s j)) = 0 := by
    rw [show l = independentFrameCoordinate v hv 0 by rfl,
      independentFrameCoordinate_apply]
    simp [extensionThetaIndex]
  rw [extensionAffineValue, map_add, hbase]
  have hsum : l (∑ j : Fin (s - 1),
      algebraMap B F (A.linear (Pi.single j 1)) * v (extensionThetaIndex s j)) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [hmul, htheta, mul_zero]
  rw [hsum, add_zero]

/-- The coordinate at `θ_j` extracts the corresponding linear coefficient. -/
theorem independentFrameCoordinate_extensionAffineValue_theta
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F) (hv : LinearIndependent B v)
    (hv0 : v 0 = 1) (A : (Fin (s - 1) → B) →ᵃ[B] B)
    (j : Fin (s - 1)) :
    independentFrameCoordinate v hv (extensionThetaIndex s j)
      (extensionAffineValue s v A) = A.linear (Pi.single j 1) := by
  let l := independentFrameCoordinate v hv (extensionThetaIndex s j)
  have hmul (b : B) (x : F) : l (algebraMap B F b * x) = b * l x := by
    simpa [Algebra.smul_def] using l.map_smul b x
  have hl1 : l 1 = 0 := by
    rw [← hv0]
    rw [show l = independentFrameCoordinate v hv (extensionThetaIndex s j) by rfl,
      independentFrameCoordinate_apply]
    simp [extensionThetaIndex]
  have hbase (b : B) : l (algebraMap B F b) = 0 := by
    simpa [hl1] using hmul b 1
  rw [extensionAffineValue, map_add, hbase, zero_add, map_sum]
  calc
    (∑ x : Fin (s - 1), l
      (algebraMap B F (A.linear (Pi.single x 1)) * v (extensionThetaIndex s x))) =
        ∑ x : Fin (s - 1), A.linear (Pi.single x 1) *
          (if j = x then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hmul]
      congr 1
      rw [independentFrameCoordinate_apply]
      by_cases h : j = x
      · subst x
        simp
      · rw [if_neg h, if_neg]
        exact fun he ↦ h (extensionThetaIndex_injective s he)
    _ = A.linear (Pi.single j 1) := by simp

/-- The last coordinate vanishes on every base-affine evaluation. -/
theorem independentFrameCoordinate_extensionAffineValue_last
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F) (hv : LinearIndependent B v)
    (hv0 : v 0 = 1) (hs : 1 ≤ s) (A : (Fin (s - 1) → B) →ᵃ[B] B) :
    independentFrameCoordinate v hv (Fin.last s)
      (extensionAffineValue s v A) = 0 := by
  let l := independentFrameCoordinate v hv (Fin.last s)
  have hmul (b : B) (x : F) : l (algebraMap B F b * x) = b * l x := by
    simpa [Algebra.smul_def] using l.map_smul b x
  have hl1 : l 1 = 0 := by
    rw [← hv0]
    rw [show l = independentFrameCoordinate v hv (Fin.last s) by rfl,
      independentFrameCoordinate_apply]
    simp [show s ≠ 0 by omega]
  have hbase (b : B) : l (algebraMap B F b) = 0 := by
    simpa [hl1] using hmul b 1
  rw [extensionAffineValue, map_add, hbase, zero_add, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [hmul]
  have hcoord : l (v (extensionThetaIndex s j)) = 0 := by
    rw [show l = independentFrameCoordinate v hv (Fin.last s) by rfl,
      independentFrameCoordinate_apply]
    rw [if_neg]
    exact (extensionThetaIndex_ne_last s j).symm
  rw [hcoord, mul_zero]

/-- Shift a base-affine challenge by the independent final coordinate `τ`. -/
def extensionShiftedAffineValue
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F)
    (A : (Fin (s - 1) → B) →ᵃ[B] B) : F :=
  extensionAffineValue s v A + v (Fin.last s)

/-- Every `τ`-shifted base-affine challenge is nonzero. -/
theorem extensionShiftedAffineValue_ne_zero
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (hs : 1 ≤ s) (v : Fin (s + 1) → F)
    (hv : LinearIndependent B v) (hv0 : v 0 = 1)
    (A : (Fin (s - 1) → B) →ᵃ[B] B) :
    extensionShiftedAffineValue s v A ≠ 0 := by
  intro hzero
  let l := independentFrameCoordinate v hv (Fin.last s)
  have happ := congrArg l hzero
  rw [extensionShiftedAffineValue, map_add,
    independentFrameCoordinate_extensionAffineValue_last s v hv hv0 hs A,
    independentFrameCoordinate_apply] at happ
  simp at happ

/-- Evaluation followed by the `τ` shift is injective on base-affine challenges. -/
theorem extensionShiftedAffineValue_injective
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F)
    (hv : LinearIndependent B v) (hv0 : v 0 = 1) :
    Function.Injective (extensionShiftedAffineValue (B := B) (F := F) s v) := by
  intro A A' heq
  have hvalue : extensionAffineValue s v A = extensionAffineValue s v A' := by
    simpa [extensionShiftedAffineValue] using add_right_cancel heq
  have hconst : A 0 = A' 0 := by
    have h := congrArg (independentFrameCoordinate v hv 0) hvalue
    simpa [independentFrameCoordinate_extensionAffineValue_zero s v hv hv0]
      using h
  have hcoeff (j : Fin (s - 1)) :
      A.linear (Pi.single j 1) = A'.linear (Pi.single j 1) := by
    have h := congrArg (independentFrameCoordinate v hv (extensionThetaIndex s j)) hvalue
    simpa [independentFrameCoordinate_extensionAffineValue_theta s v hv hv0]
      using h
  have hlinear : A.linear = A'.linear := by
    apply LinearMap.pi_ext
    intro j x
    have hsingle : Pi.single j x = x • Pi.single j (1 : B) := by
      ext k
      simp [Pi.single_apply]
    rw [hsingle, map_smul, map_smul, hcoeff]
  apply AffineMap.ext
  intro x
  have hA := congrFun (AffineMap.decomp A) x
  have hA' := congrFun (AffineMap.decomp A') x
  change A x = A.linear x + A 0 at hA
  change A' x = A'.linear x + A' 0 at hA'
  rw [hA, hA', hlinear, hconst]

/-- A word whose frame coefficients lie in the base field, with a distinguished
final direction multiplied by `τ`. -/
def extensionFrameWord
    {B F X : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F) (base : X → B)
    (parts : Fin (s - 1) → X → B) (direction : X → B) (x : X) : F :=
  algebraMap B F (base x) +
    ∑ j : Fin (s - 1), algebraMap B F (parts j x) *
      v (extensionThetaIndex s j) +
    algebraMap B F (direction x) * v (Fin.last s)

/-- Projection onto the `τ` coordinate extracts exactly the distinguished
base-field direction, independently of the other frame coefficients. -/
theorem independentFrameCoordinate_extensionFrameWord_last
    {B F X : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (hs : 1 ≤ s) (v : Fin (s + 1) → F)
    (hv : LinearIndependent B v) (hv0 : v 0 = 1)
    (base : X → B) (parts : Fin (s - 1) → X → B)
    (direction : X → B) (x : X) :
    independentFrameCoordinate v hv (Fin.last s)
      (extensionFrameWord s v base parts direction x) = direction x := by
  let l := independentFrameCoordinate v hv (Fin.last s)
  have hmul (b : B) (y : F) : l (algebraMap B F b * y) = b * l y := by
    simpa [Algebra.smul_def] using l.map_smul b y
  have hl1 : l 1 = 0 := by
    rw [← hv0]
    rw [show l = independentFrameCoordinate v hv (Fin.last s) by rfl,
      independentFrameCoordinate_apply]
    simp [show s ≠ 0 by omega]
  have hbase (b : B) : l (algebraMap B F b) = 0 := by
    simpa [hl1] using hmul b 1
  rw [extensionFrameWord, map_add, map_add, hbase, zero_add, map_sum]
  have hparts : ∑ j : Fin (s - 1),
      l (algebraMap B F (parts j x) * v (extensionThetaIndex s j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hmul]
    have hcoord : l (v (extensionThetaIndex s j)) = 0 := by
      rw [show l = independentFrameCoordinate v hv (Fin.last s) by rfl,
        independentFrameCoordinate_apply, if_neg]
      exact (extensionThetaIndex_ne_last s j).symm
    rw [hcoord, mul_zero]
  rw [hparts, zero_add, hmul, independentFrameCoordinate_apply, if_pos rfl, mul_one]

/-- Extend a frame word from the base field to the ambient extension, evaluated
on the literal mapped domain through the inverse of the algebra embedding. -/
noncomputable def extensionFrameWordOnMapped
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F) (base : B → B)
    (parts : Fin (s - 1) → B → B) (direction : B → B) (x : F) : F :=
  extensionFrameWord s v base parts direction
    (Function.invFun (algebraMap B F) x)

@[simp]
theorem extensionFrameWordOnMapped_apply
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F) (base : B → B)
    (parts : Fin (s - 1) → B → B) (direction : B → B) (x : B) :
    extensionFrameWordOnMapped s v base parts direction (algebraMap B F x) =
      extensionFrameWord s v base parts direction x := by
  unfold extensionFrameWordOnMapped
  rw [Function.leftInverse_invFun (algebraMap B F).injective x]

/-- Projection onto `τ` bounds agreement of a frame word by the degree of its
distinguished polynomial direction. All other frame coefficients are arbitrary
base-field functions, which includes later padding values. -/
theorem agreementLE_extensionFrameWordOnMapped
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (hs : 1 ≤ s) (v : Fin (s + 1) → F)
    (hv : LinearIndependent B v) (hv0 : v 0 = 1)
    (D : Finset B) (K : ℕ) (base : B → B)
    (parts : Fin (s - 1) → B → B) (G : B[X])
    (hdegree : (K : WithBot ℕ) ≤ G.degree) :
    agreementLE (mappedDomain (algebraMap B F) D) K
      (fun x ↦ extensionFrameWordOnMapped s v base parts (fun y ↦ G.eval y) x)
      G.natDegree := by
  intro p hp
  obtain ⟨q, hq, heq⟩ := exists_projected_polynomial
    (independentFrameCoordinate v hv (Fin.last s)) K p hp
  rw [agreementCount_mappedDomain (algebraMap B F) D
    (extensionFrameWordOnMapped s v base parts (fun x ↦ G.eval x)) p]
  have hsub : (D.filter fun x ↦ p.eval (algebraMap B F x) =
      extensionFrameWordOnMapped s v base parts (fun y ↦ G.eval y)
        (algebraMap B F x)) ⊆
      D.filter (fun x ↦ q.eval x = G.eval x) := by
    intro x hx
    obtain ⟨hxD, hx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
    rw [heq, hx, extensionFrameWordOnMapped_apply]
    exact independentFrameCoordinate_extensionFrameWord_last
      s hs v hv hv0 base parts (fun y ↦ G.eval y) x
  apply (Finset.card_le_card hsub).trans
  have hbound := agreementLE_polynomial D K G hdegree q hq
  rw [agreementCount_eq_card_filter D (fun x ↦ G.eval x) q] at hbound
  simpa using hbound

end AllRatesConstruction

end BinaryFieldCounterexamples
