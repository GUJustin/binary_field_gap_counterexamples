/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.DenseAllRates.RestrictedWalsh
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Basic.Real.Basic

/-!
# Scalar zero counts from binary trace characters

Averaging all prime-field trace characters is the indicator of a scalar zero.
Consequently a uniform Walsh bound for every nonzero scalar character gives a
lower bound for the zero count of a finite-field-valued function.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold
open BinaryQuadraticData
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The prime-field trace character associated with multiplication by `a`. -/
noncomputable def traceMulFunctional
    {k : Type*} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    (a : k) : Module.Dual (ZMod 2) k :=
  (Algebra.trace (ZMod 2) k).comp (LinearMap.mulRight (ZMod 2) a)

@[simp] theorem traceMulFunctional_apply
    {k : Type*} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    (a x : k) : traceMulFunctional a x = Algebra.trace (ZMod 2) k (x * a) := by
  rfl

/-- Orthogonality of all prime-field trace characters of a finite field. -/
theorem sum_binarySign_trace_mul
    {k : Type*} [Field k] [Fintype k] [CharP k 2] [Algebra (ZMod 2) k]
    (a : k) :
    (∑ v : k, binarySign (Algebra.trace (ZMod 2) k (v * a))) =
      if a = 0 then (Fintype.card k : ℤ) else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [binarySign_zero]
  · rw [ite_eq_right ha]
    have hfun : traceMulFunctional a ≠ 0 := by
      intro hz
      have htr := (traceForm_nondegenerate (ZMod 2) k).1 a
      simp_rw [Algebra.traceForm_apply] at htr
      apply ha
      apply htr
      intro b
      have hb := LinearMap.congr_fun hz b
      simpa [traceMulFunctional, mul_comm] using hb
    simpa only [traceMulFunctional_apply, mul_comm] using
      sum_binarySign_linear_eq_zero (traceMulFunctional a) hfun

/-- Number of zeros of a finite-field-valued function. -/
noncomputable def scalarZeroCount {V k : Type*} [Fintype V] [Zero k]
    (f : V → k) : ℕ := Nat.card {x : V // f x = 0}

/-- Exact character average for the zero set of a finite-field-valued
function. -/
theorem sum_walsh_trace_eq_card_mul_zeroCount
    {V k : Type*} [Fintype V] [Field k] [Fintype k]
    [CharP k 2] [Algebra (ZMod 2) k]
    (f : V → k) :
    (∑ v : k, walshSum (fun x ↦ Algebra.trace (ZMod 2) k (v * f x))) =
      (Fintype.card k : ℤ) * scalarZeroCount f := by
  classical
  rw [show (∑ v : k, walshSum
      (fun x ↦ Algebra.trace (ZMod 2) k (v * f x))) =
      ∑ x : V, ∑ v : k,
        binarySign (Algebra.trace (ZMod 2) k (v * f x)) by
    simp only [walshSum]
    rw [Finset.sum_comm]]
  simp_rw [sum_binarySign_trace_mul]
  rw [scalarZeroCount]
  have hc : (Finset.univ.filter fun x : V ↦ f x = 0).card =
      Nat.card {x : V // f x = 0} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, hc]
  ring

/-- The zero character has Walsh sum equal to the full domain size. -/
theorem walshSum_trace_zero
    {V k : Type*} [Fintype V] [Field k] [Fintype k]
    [CharP k 2] [Algebra (ZMod 2) k]
    (f : V → k) :
    walshSum (fun x ↦ Algebra.trace (ZMod 2) k ((0 : k) * f x)) = Nat.card V := by
  simp [walshSum, Nat.card_eq_fintype_card]

/-- A uniform absolute bound for all nonzero trace characters gives an exact
integer lower bound for the scalar zero count. -/
theorem scalarZeroCount_int_lower
    {V k : Type*} [Fintype V] [Field k] [Fintype k]
    [CharP k 2] [Algebra (ZMod 2) k]
    (f : V → k) (E : ℕ)
    (hE : ∀ v : k, v ≠ 0 →
      |walshSum (fun x ↦ Algebra.trace (ZMod 2) k (v * f x))| ≤ E) :
    (Nat.card V : ℤ) - (Fintype.card k - 1 : ℕ) * E ≤
      (Fintype.card k : ℤ) * scalarZeroCount f := by
  classical
  let S : k → ℤ := fun v ↦
    walshSum (fun x ↦ Algebra.trace (ZMod 2) k (v * f x))
  have hsum := sum_walsh_trace_eq_card_mul_zeroCount f
  have hzero : S 0 = Nat.card V := walshSum_trace_zero f
  have hrest : -((Fintype.card k - 1 : ℕ) * E : ℤ) ≤
      ∑ v ∈ (Finset.univ.erase (0 : k)), S v := by
    calc
      -((Fintype.card k - 1 : ℕ) * E : ℤ) =
          ∑ _v ∈ (Finset.univ.erase (0 : k)), -(E : ℤ) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 0),
          Finset.card_univ]
        simp only [nsmul_eq_mul]
        ring
      _ ≤ ∑ v ∈ (Finset.univ.erase (0 : k)), S v := by
        apply Finset.sum_le_sum
        intro v hv
        have hv0 : v ≠ 0 := by
          simpa only [Finset.mem_erase, Finset.mem_univ, and_true] using hv
        have hb := hE v hv0
        have := (abs_le.mp hb).1
        exact_mod_cast this
  have hsplit : ∑ v : k, S v = S 0 +
      ∑ v ∈ (Finset.univ.erase (0 : k)), S v := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : k))]
    ring
  change (Nat.card V : ℤ) - ((Fintype.card k - 1 : ℕ) : ℤ) * E ≤ _
  rw [← hsum, show (∑ v : k, _) = ∑ v : k, S v by rfl, hsplit, hzero]
  linarith

/-- Real form of the scalar zero-count lower bound. -/
theorem scalarZeroCount_real_lower
    {V k : Type*} [Fintype V] [Field k] [Fintype k]
    [CharP k 2] [Algebra (ZMod 2) k]
    (f : V → k) (E : ℕ)
    (hE : ∀ v : k, v ≠ 0 →
      |walshSum (fun x ↦ Algebra.trace (ZMod 2) k (v * f x))| ≤ E) :
    (Nat.card V : Real) / (Fintype.card k : Real) -
        ((Fintype.card k - 1 : ℕ) : Real) * (E : Real) / (Fintype.card k : Real) ≤
      (scalarZeroCount f : Real) := by
  have hi := scalarZeroCount_int_lower f E hE
  have hiR : (Nat.card V : Real) -
      ((Fintype.card k - 1 : ℕ) : Real) * (E : Real) ≤
      (Fintype.card k : Real) * (scalarZeroCount f : Real) := by exact_mod_cast hi
  have hq : (0 : Real) < Fintype.card k := by positivity
  rw [← sub_div]
  exact (div_le_iff₀ hq).2 (by simpa only [mul_comm] using hiR)


/-- Binary quadratic data obtained by tracing a scalar multiple of an actual
finite-field-valued quadratic function. -/
noncomputable def traceQuadraticData
    {k V : Type*} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    [AddCommGroup V] [Module k V] [Module (ZMod 2) V]
    [IsScalarTower (ZMod 2) k V]
    (f : V → k) (C : V →ₗ[k] Module.Dual k V)
    (hf0 : f 0 = 0) (hfadd : ∀ x y, f (x + y) = f x + f y + C y x)
    (v : k) : BinaryQuadraticData V :=
  BinaryQuadraticData.mk
    (fun x ↦ Algebra.trace (ZMod 2) k (v * f x))
    (binaryTracePolarMap v C) (by simp [hf0]) (by
      intro x y
      rw [hfadd]
      simp only [mul_add, map_add]
      rfl)

@[simp] theorem traceQuadraticData_toFun
    {k V : Type*} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    [AddCommGroup V] [Module k V] [Module (ZMod 2) V]
    [IsScalarTower (ZMod 2) k V]
    (f : V → k) (C : V →ₗ[k] Module.Dual k V)
    (hf0 : f 0 = 0) (hfadd : ∀ x y, f (x + y) = f x + f y + C y x)
    (v : k) (x : V) :
    (traceQuadraticData f C hf0 hfadd v).toFun x =
      Algebra.trace (ZMod 2) k (v * f x) := by rfl

@[simp] theorem traceQuadraticData_polarMap
    {k V : Type*} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    [AddCommGroup V] [Module k V] [Module (ZMod 2) V]
    [IsScalarTower (ZMod 2) k V]
    (f : V → k) (C : V →ₗ[k] Module.Dual k V)
    (hf0 : f 0 = 0) (hfadd : ∀ x y, f (x + y) = f x + f y + C y x)
    (v : k) :
    (traceQuadraticData f C hf0 hfadd v).polarMap = binaryTracePolarMap v C := by rfl

/-- On an affine translate, the literal traced scalar function is the
normalized affine restriction plus its constant value. -/
theorem traceQuadraticData_affineRestrict_add_const
    {k V : Type*} [Field k] [Finite k] [CharP k 2] [Algebra (ZMod 2) k]
    [AddCommGroup V] [Module k V] [Module (ZMod 2) V]
    [IsScalarTower (ZMod 2) k V]
    (f : V → k) (C : V →ₗ[k] Module.Dual k V)
    (hf0 : f 0 = 0) (hfadd : ∀ x y, f (x + y) = f x + f y + C y x)
    (v : k) (W : Submodule (ZMod 2) V) (a : V) (x : W) :
    ((traceQuadraticData f C hf0 hfadd v).affineRestrict W a).toFun x +
        Algebra.trace (ZMod 2) k (v * f a) =
      Algebra.trace (ZMod 2) k (v * f ((x : V) + a)) := by
  rw [BinaryQuadraticData.affineRestrict_toFun]
  simp only [traceQuadraticData_toFun]
  have hz : Algebra.trace (ZMod 2) k (v * f a) +
      Algebra.trace (ZMod 2) k (v * f a) = 0 := CharTwo.add_self_eq_zero _
  calc
    _ = Algebra.trace (ZMod 2) k (v * f ((x : V) + a)) +
        (Algebra.trace (ZMod 2) k (v * f a) +
          Algebra.trace (ZMod 2) k (v * f a)) := by ring
    _ = _ := by rw [hz, add_zero]

/-- Scalar zero count on every binary affine restriction, from the actual
field-valued polar rank and the codimension-two rank-loss bound. -/
theorem scalarZeroCount_affine_quadratic_real_lower
    {k V : Type*} [Field k] [Fintype k] [CharP k 2] [Algebra (ZMod 2) k]
    [AddCommGroup V] [Module k V] [Module (ZMod 2) V]
    [IsScalarTower (ZMod 2) k V]
    [Fintype V] [FiniteDimensional k V] [FiniteDimensional (ZMod 2) V]
    (f : V → k) (C : V →ₗ[k] Module.Dual k V)
    (hf0 : f 0 = 0) (hfadd : ∀ x y, f (x + y) = f x + f y + C y x)
    (W : Submodule (ZMod 2) V) (a : V) (c d t : ℕ)
    (hcodim : Module.finrank (ZMod 2) V ≤ Module.finrank (ZMod 2) W + c)
    (hdim : Module.finrank (ZMod 2) W = d)
    (hrank : 2 * t + 2 * c ≤
      Module.finrank (ZMod 2) k * Module.finrank k (LinearMap.range C)) :
    (Nat.card W : Real) / (Fintype.card k : Real) -
        ((Fintype.card k - 1 : ℕ) : Real) * (2 ^ (d - t) : ℕ) /
          (Fintype.card k : Real) ≤
      (scalarZeroCount (fun x : W ↦ f ((x : V) + a)) : Real) := by
  apply scalarZeroCount_real_lower (fun x : W ↦ f ((x : V) + a)) (2 ^ (d - t))
  intro v hv
  let Q := traceQuadraticData f C hf0 hfadd v
  have hfull := binaryTracePolarMap_rank v hv C
  have hloss := Gold.polar_rank_le_restriction_add_two_codim W Q.polarMap c hcodim
  have hloss' : Module.finrank (ZMod 2)
      (LinearMap.range (binaryTracePolarMap v C)) ≤
      Module.finrank (ZMod 2)
        (LinearMap.range (Gold.restrictPolarMap W (binaryTracePolarMap v C))) + 2*c := by
    change Module.finrank (ZMod 2)
      (LinearMap.range (binaryTracePolarMap v C)) ≤
      Module.finrank (ZMod 2)
        (LinearMap.range (Gold.restrictPolarMap W (binaryTracePolarMap v C))) + 2*c at hloss
    exact hloss
  have hres : 2 * t ≤ Module.finrank (ZMod 2)
      (LinearMap.range (Q.affineRestrict W a).polarMap) := by
    change 2 * t ≤ Module.finrank (ZMod 2)
      (LinearMap.range (Gold.restrictPolarMap W (binaryTracePolarMap v C)))
    omega
  have hw := BinaryQuadraticData.abs_walshSum_linear_const_le_of_rank
    (Q.affineRestrict W a) 0
    (Algebra.trace (ZMod 2) k (v * f a)) d t hdim hres
  have hfun : (fun x : W ↦ Algebra.trace (ZMod 2) k (v * f ((x : V) + a))) =
      (fun x : W ↦ (Q.affineRestrict W a).toFun x +
        (0 : Module.Dual (ZMod 2) W) x +
        Algebra.trace (ZMod 2) k (v * f a)) := by
    funext x
    simpa using (traceQuadraticData_affineRestrict_add_const
      f C hf0 hfadd v W a x).symm
  rw [hfun]
  exact hw

end BinaryFieldCounterexamples.Gold
