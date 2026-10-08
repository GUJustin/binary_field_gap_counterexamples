/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.AllRates.ExtensionParameters
public import BinaryFieldCounterexamples.Constructions.AllRates.FiniteSeed
public import BinaryFieldCounterexamples.Polynomial.Map

/-!
# High-extension all-rate seeds

The affine functions giving the cancellation challenges commute with scalar
extension.  An independent frame in the extension field then turns every such
function in an injective binary-subspace family into a distinct nonzero
exceptional challenge for one fixed pair.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

namespace AllRatesConstruction
open Finset Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Scalar extension of a finite-dimensional base-field linear functional. -/
def scalarExtensionLinear {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (r : ℕ) (L : (Fin r → B) →ₗ[B] B) :
    (Fin r → F) →ₗ[F] F := by
  exact {
    toFun := fun θ ↦ ∑ j : Fin r, φ (L (Pi.single j 1)) * θ j
    map_add' := by
      intro θ ψ
      simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c θ
      simp [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring }

/-- Scalar extension of an affine functional, coefficient by coefficient. -/
def scalarExtensionAffine {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (r : ℕ) (A : (Fin r → B) →ᵃ[B] B) :
    (Fin r → F) →ᵃ[F] F :=
  (scalarExtensionLinear φ r A.linear).toAffineMap +
    AffineMap.const F (Fin r → F) (φ (A 0))

@[simp]
theorem scalarExtensionAffine_apply {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (r : ℕ) (A : (Fin r → B) →ᵃ[B] B)
    (θ : Fin r → F) :
    scalarExtensionAffine φ r A θ = φ (A 0) +
      ∑ j : Fin r, φ (A.linear (Pi.single j 1)) * θ j := by
  simp [scalarExtensionAffine, scalarExtensionLinear, add_comm]

/-- The independent-frame evaluator is scalar extension evaluated at its
chosen parameter coordinates. -/
theorem extensionAffineValue_eq_scalarExtensionAffine
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F)
    (A : (Fin (s - 1) → B) →ᵃ[B] B) :
    extensionAffineValue s v A =
      scalarExtensionAffine (algebraMap B F) (s - 1) A
        (fun j ↦ v (extensionThetaIndex s j)) := by
  simp [extensionAffineValue, scalarExtensionAffine_apply]

@[simp]
theorem scalarExtensionAffine_const {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (r : ℕ) (b : B) :
    scalarExtensionAffine φ r (AffineMap.const B (Fin r → B) b) =
      AffineMap.const F (Fin r → F) (φ b) := by
  apply AffineMap.ext
  intro θ
  simp [scalarExtensionAffine_apply]

@[simp]
theorem scalarExtensionAffine_add {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (r : ℕ) (A C : (Fin r → B) →ᵃ[B] B) :
    scalarExtensionAffine φ r (A + C) =
      scalarExtensionAffine φ r A + scalarExtensionAffine φ r C := by
  apply AffineMap.ext
  intro θ
  simp only [scalarExtensionAffine_apply, AffineMap.coe_add, Pi.add_apply,
    AffineMap.add_linear, LinearMap.add_apply, map_add, mul_add,
    Finset.sum_add_distrib]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring

@[simp]
theorem scalarExtensionAffine_smul {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (r : ℕ) (b : B) (A : (Fin r → B) →ᵃ[B] B) :
    scalarExtensionAffine φ r (b • A) =
      φ b • scalarExtensionAffine φ r A := by
  apply AffineMap.ext
  intro θ
  simp only [scalarExtensionAffine_apply, AffineMap.coe_smul, Pi.smul_apply,
    AffineMap.smul_linear, LinearMap.smul_apply, smul_eq_mul, map_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp]
theorem scalarExtensionAffine_proj {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (r : ℕ) (j : Fin r) :
    scalarExtensionAffine φ r
      (LinearMap.proj (R := B) (φ := fun _ : Fin r ↦ B) j).toAffineMap =
      (LinearMap.proj (R := F) (φ := fun _ : Fin r ↦ F) j).toAffineMap := by
  apply AffineMap.ext
  intro θ
  simp [scalarExtensionAffine_apply, Pi.single_apply]


/-- Scalar extension commutes with finite sums of affine maps. -/
theorem scalarExtensionAffine_sum {B F ι : Type*} [Field B] [Field F]
    (φ : B →+* F) (r : ℕ) (S : Finset ι)
    (A : ι → ((Fin r → B) →ᵃ[B] B)) :
    scalarExtensionAffine φ r (∑ i ∈ S, A i) =
      ∑ i ∈ S, scalarExtensionAffine φ r (A i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      apply AffineMap.ext
      intro θ
      simp [scalarExtensionAffine_apply]
  | @insert i S hi ih => simp [hi, ih]

/-- Recursive coefficient as an affine function of the genuine finite
parameter vector. -/
def finiteCancellationCoeffAffine {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) (i : ℕ) : (Fin (s - 1) → F) →ᵃ[F] F :=
  (cancellationCoeffAffine s a i).comp
    (finiteCancellationParameterExtension s).toAffineMap

@[simp]
theorem finiteCancellationCoeffAffine_zero {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) :
    finiteCancellationCoeffAffine s a 0 =
      AffineMap.const F (Fin (s - 1) → F) 1 := by
  apply AffineMap.ext
  intro θ
  simp [finiteCancellationCoeffAffine, cancellationCoeffAffine.eq_1]

/-- Within the genuine parameter range, the finite coefficient affine maps
obey the same triangular recursion. -/
theorem finiteCancellationCoeffAffine_succ {F : Type*} [Field F]
    (s : ℕ) (a : ℕ → F) (j : ℕ) (hjs : j + 1 < s) :
    finiteCancellationCoeffAffine s a (j + 1) =
      (LinearMap.proj (R := F) (φ := fun _ : Fin (s - 1) ↦ F)
        ⟨j, by omega⟩).toAffineMap +
      ∑ i ∈ Finset.range (j + 1),
        (a (j + 1 - i) ^ (2 ^ (s - 1 - i))) •
          finiteCancellationCoeffAffine s a i := by
  apply AffineMap.ext
  intro θ
  change cancellationCoeff s a (finiteCancellationParameterExtension s θ) (j + 1) = _
  rw [cancellationCoeff_succ,
    finiteCancellationParameterExtension_apply_of_mem s θ (j + 1) (by omega) hjs]
  simp only [AffineMap.coe_add, Pi.add_apply, LinearMap.coe_toAffineMap,
    LinearMap.proj_apply, affineMap_sum_apply, AffineMap.coe_smul,
    Pi.smul_apply, smul_eq_mul, finiteCancellationCoeffAffine,
    AffineMap.comp_apply, cancellationCoeff]
  apply congrArg₂ (· + ·)
  · congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]

/-- Scalar extension commutes with every recursive coefficient affine map
inside the genuine parameter range. -/
theorem scalarExtension_finiteCancellationCoeffAffine
    {B F : Type*} [Field B] [Field F] (φ : B →+* F)
    (s : ℕ) (a : ℕ → B) {i : ℕ} (his : i < s) :
    scalarExtensionAffine φ (s - 1) (finiteCancellationCoeffAffine s a i) =
      finiteCancellationCoeffAffine s (fun u ↦ φ (a u)) i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp
      | succ j =>
          rw [finiteCancellationCoeffAffine_succ s a j his,
            finiteCancellationCoeffAffine_succ s (fun u ↦ φ (a u)) j his,
            scalarExtensionAffine_add, scalarExtensionAffine_proj]
          congr 1
          rw [scalarExtensionAffine_sum]
          apply Finset.sum_congr rfl
          intro u hu
          have huj : u < j + 1 := Finset.mem_range.mp hu
          rw [scalarExtensionAffine_smul, ih u huj (by omega), map_pow]

/-- The finite residual challenge is the corresponding combination of finite
recursive coefficient affine maps. -/
theorem finiteCancellationLabelAffine_eq_sum {K : Type*} [Field K]
    (s : ℕ) (b : ℕ → K) :
    finiteCancellationLabelAffine s b =
      ∑ i ∈ Finset.range s,
        (b (s - i) ^ (2 ^ (s - 1 - i))) •
          finiteCancellationCoeffAffine s b i := by
  apply AffineMap.ext
  intro θ
  simp only [finiteCancellationLabelAffine, cancellationLabelAffine,
    AffineMap.comp_apply, affineMap_sum_apply, AffineMap.coe_smul,
    Pi.smul_apply, smul_eq_mul, finiteCancellationCoeffAffine]

/-- Scalar extension commutes with the full residual cancellation challenge. -/
theorem scalarExtension_finiteCancellationLabelAffine
    {B F : Type*} [Field B] [Field F] (φ : B →+* F)
    (s : ℕ) (a : ℕ → B) :
    scalarExtensionAffine φ (s - 1) (finiteCancellationLabelAffine s a) =
      finiteCancellationLabelAffine s (fun u ↦ φ (a u)) := by
  rw [finiteCancellationLabelAffine_eq_sum,
    finiteCancellationLabelAffine_eq_sum, scalarExtensionAffine_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have his : i < s := Finset.mem_range.mp hi
  rw [scalarExtensionAffine_smul,
    scalarExtension_finiteCancellationCoeffAffine φ s a his, map_pow]


/-- The concrete high-extension parameter vector. -/
def extensionCancellationParameters
    {F : Type*} [Field F] (s : ℕ) (v : Fin (s + 1) → F) :
    Fin (s - 1) → F := fun j ↦ v (extensionThetaIndex s j)

/-- Evaluating mapped cancellation challenges at the independent extension
parameters is exactly the generic extension-affine evaluation of the base challenge. -/
theorem mapped_finiteCancellationLabelAffine_apply
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (s : ℕ) (v : Fin (s + 1) → F) (a : ℕ → B) :
    finiteCancellationLabelAffine s (fun u ↦ algebraMap B F (a u))
        (extensionCancellationParameters s v) =
      extensionAffineValue s v (finiteCancellationLabelAffine s a) := by
  rw [extensionAffineValue_eq_scalarExtensionAffine,
    scalarExtension_finiteCancellationLabelAffine]
  rfl

/-- Locator prefixes commute coefficientwise with a field embedding. -/
theorem locatorPrefix_mapped_subspace
    {B F : Type*} [Field B] [Field F] (φ : B →+* F)
    (W : AddSubgroup B) [Fintype W] [Fintype (W.map φ.toAddMonoidHom)]
    (m j : ℕ) :
    locatorPrefix (subspacePolynomial (W.map φ.toAddMonoidHom)) m j =
      φ (locatorPrefix (subspacePolynomial W) m j) := by
  unfold locatorPrefix
  exact coeff_subspacePolynomial_map φ W _

/-- The cancellation first input with extension-frame parameters is the literal
frame word whose coefficients are the paper's sparse binary monomials. -/
theorem cancellationSource_extensionFrameWord
    {B F : Type*} [Field B] [Field F] [CharP F 2] [Algebra B F]
    (m s : ℕ) (hs : 2 ≤ s) (v : Fin (s + 1) → F) (x : B) :
    (cancellationSource m s
      (finiteCancellationParameterExtension s
        (extensionCancellationParameters s v))).eval (algebraMap B F x) =
      extensionFrameWord s v
        (fun y : B ↦ y ^ (2 ^ (m + s - 1) - 1))
        (fun j y ↦ y ^ (2 ^ (m + s - 2 - j.1) - 1))
        (fun _ ↦ 0) x := by
  rw [cancellationSource_eq_sum, eval_finset_sum]
  let q : ℕ → F := fun j ↦
    eval (algebraMap B F x)
      (C (if j = 0 then 1 else
          finiteCancellationParameterExtension s
            (extensionCancellationParameters s v) j) *
        X ^ (2 ^ (m + s - 1 - j) - 1))
  change (∑ j ∈ Finset.range s, q j) = _
  have hs' : s - 1 + 1 = s := by omega
  rw (occs := .pos [1]) [← hs']
  rw [Finset.sum_range_succ']
  have htail : (∑ j ∈ Finset.range (s - 1), q (j + 1)) =
      ∑ j : Fin (s - 1),
        algebraMap B F (x ^ (2 ^ (m + s - 2 - j.1) - 1)) *
          v (extensionThetaIndex s j) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjs : j < s - 1 := Finset.mem_range.mp hj
    have hj0 : j + 1 ≠ 0 := by omega
    have hexp : m + s - 1 - (j + 1) = m + s - 2 - j := by
      omega
    simp only [hjs, dite_true, q, eval_mul, eval_C, eval_pow, eval_X,
      if_neg hj0]
    rw [finiteCancellationParameterExtension_apply_of_mem s
      (extensionCancellationParameters s v) (j + 1) (by omega) (by omega)]
    simp only [extensionCancellationParameters, extensionThetaIndex, map_pow, hexp]
    rw [mul_comm]
    congr 2
  rw [htail]
  unfold extensionFrameWord
  simp only [q, if_pos, eval_mul, eval_C, eval_pow, eval_X,
    one_mul, map_pow, map_zero, zero_mul, add_zero, Nat.sub_zero]
  ac_rfl

/-- The high-extension seed uses every challenge in the supplied subspace family: they are
distinct, nonzero, and exceptional for one fixed pair. -/
theorem highExtension_seed_badChallenges_of_dimension
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2] [Algebra B F]
    (H : AddSubgroup B) (m s J : ℕ) (hs : 2 ≤ s) (hm : s ≤ m)
    (hJ : 2^(m-2) ≤ J)
    (hH : Nat.card H = 2 ^ (m + s))
    (I : Finset (AddSubgroup B))
    (hI : ∀ W ∈ I, W ≤ H ∧ Nat.card W = 2 ^ m)
    (v : Fin (s + 1) → F) (hv : LinearIndependent B v) (hv0 : v 0 = 1) :
    let HF := H.map (algebraMap B F).toAddMonoidHom
    let θ := extensionCancellationParameters s v
    let K := 2 ^ (m - 1) - 1
    let src := cancellationSource m s (finiteCancellationParameterExtension s θ)
    let f : additiveDomain HF → F := fun x ↦ src.eval (x : F) +
      v (Fin.last s) * (x : F) ^ K
    let g : additiveDomain HF → F := fun x ↦ (x : F) ^ K
    I.card ≤ (nonzeroBadChallenges (additiveDomain HF) J f g (2 ^ m - 1)).card := by
  classical
  dsimp only
  let φ : B →+* F := algebraMap B F
  let HF := H.map φ.toAddMonoidHom
  let θ := extensionCancellationParameters s v
  let K := 2 ^ (m - 1) - 1
  let src : F[X] := cancellationSource m s (finiteCancellationParameterExtension s θ)
  let f : additiveDomain HF → F := fun x ↦ src.eval (x : F) +
    v (Fin.last s) * (x : F) ^ K
  let g : additiveDomain HF → F := fun x ↦ (x : F) ^ K
  let z : AddSubgroup B → F := fun W ↦
    extensionShiftedAffineValue s v
      (finiteCancellationLabelAffine s
        (locatorPrefix (subspacePolynomial W) m))
  have hzInj : Set.InjOn z I := by
    intro U hU W hW he
    apply (subspace_cancellationLabel_injOn H m s hs (by omega) hH I hI) hU hW
    exact extensionShiftedAffineValue_injective s v hv hv0 he
  have hzNonzero : ∀ W ∈ I, z W ≠ 0 := by
    intro W _
    exact extensionShiftedAffineValue_ne_zero s (by omega) v hv hv0 _
  have hzBad : ∀ W ∈ I, z W ∈ badChallenges (additiveDomain HF) J f g (2 ^ m - 1) := by
    intro W hW
    let WF := W.map φ.toAddMonoidHom
    have hWFcard : Nat.card WF = 2 ^ m := by
      rw [natCard_map_addSubgroup, (hI W hW).2]
    have hWFHF : WF ≤ HF := AddSubgroup.map_mono (hI W hW).1
    have hbase := subspace_cancellationLabel_mem_badChallenges HF WF m s
      (by omega) (by omega) hWFcard hWFHF θ
    have hprefix : locatorPrefix (subspacePolynomial WF) m =
        fun u ↦ φ (locatorPrefix (subspacePolynomial W) m u) := by
      funext u
      exact locatorPrefix_mapped_subspace φ W m u
    have hlabel : finiteCancellationLabelAffine s
        (locatorPrefix (subspacePolynomial WF) m) θ =
        extensionAffineValue s v
          (finiteCancellationLabelAffine s
            (locatorPrefix (subspacePolynomial W) m)) := by
      rw [hprefix]
      exact mapped_finiteCancellationLabelAffine_apply s v _
    rw [mem_badChallenges] at hbase ⊢
    obtain ⟨P, hP, hagr⟩ := hbase
    have hdim : 2 ^ (m - 2) ≤ J := hJ
    refine ⟨P, hP.trans_le (by exact_mod_cast hdim), ?_⟩
    have hreceived : (fun x : additiveDomain HF ↦ f x + z W * g x) =
        fun x : additiveDomain HF ↦
          src.eval (x : F) +
            finiteCancellationLabelAffine s
              (locatorPrefix (subspacePolynomial WF) m) θ *
                (x : F) ^ (2 ^ (m - 1) - 1) := by
      funext x
      simp only [f, g, z, extensionShiftedAffineValue, hlabel, K]
      have htwo := CharTwo.two_eq_zero (R := F)
      ring_nf at htwo ⊢
      linear_combination htwo * (v (Fin.last s) * (x : F) ^ (2 ^ (m - 1) - 1))
    rw [hreceived]
    exact hagr
  have hsubset : I.image z ⊆
      nonzeroBadChallenges (additiveDomain HF) J f g (2 ^ m - 1) := by
    intro y hy
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hy
    rw [nonzeroBadChallenges, Finset.mem_erase]
    exact ⟨hzNonzero W hW, hzBad W hW⟩
  have hcard : I.card ≤
      (nonzeroBadChallenges (additiveDomain HF) J f g (2 ^ m - 1)).card := by
    rw [← Finset.card_image_iff.mpr hzInj]
    exact Finset.card_le_card hsubset
  simpa [HF, K, f, g] using hcard

/-- The high-extension seed uses all graph-subspace challenges: they are distinct,
nonzero, and exceptional for one fixed pair. -/
theorem highExtension_seed_badChallenges
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2] [Algebra B F]
    (H : AddSubgroup B) (m s : ℕ) (hs : 2 ≤ s) (hm : s + 1 ≤ m)
    (hH : Nat.card H = 2 ^ (m + s))
    (I : Finset (AddSubgroup B))
    (hI : ∀ W ∈ I, W ≤ H ∧ Nat.card W = 2 ^ m)
    (v : Fin (s + 1) → F) (hv : LinearIndependent B v) (hv0 : v 0 = 1) :
    let HF := H.map (algebraMap B F).toAddMonoidHom
    let θ := extensionCancellationParameters s v
    let K := 2 ^ (m - 1) - 1
    let src := cancellationSource m s (finiteCancellationParameterExtension s θ)
    let f : additiveDomain HF → F := fun x ↦ src.eval (x : F) +
      v (Fin.last s) * (x : F) ^ K
    let g : additiveDomain HF → F := fun x ↦ (x : F) ^ K
    I.card ≤ (nonzeroBadChallenges (additiveDomain HF) K f g (2 ^ m - 1)).card := by
  have hdim : 2^(m-2) ≤ 2^(m-1)-1 := by
    have he : 2^(m-1) = (2:ℕ)^(m-2)*2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hp : 0 < (2:ℕ)^(m-2) := by positivity
    rw [he]
    omega
  exact highExtension_seed_badChallenges_of_dimension H m s (2^(m-1)-1)
    hs (by omega) hdim hH I hI v hv hv0

end AllRatesConstruction

end BinaryFieldCounterexamples
