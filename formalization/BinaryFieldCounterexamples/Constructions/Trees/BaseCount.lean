/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.AffineOrbits
/-!
# The base tree-template stabilizer

An affine automorphism is encoded by its translation and the images of the
three coordinate vectors. This gives a small executable finite model of the
stabilizer of `baseTemplate`, whose exact cardinality is 24. The 24 data are
listed explicitly; one exhaustive check, pruned column by column, shows that
the list is complete, so later finite checks run through the list alone.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Trees


/-- An executable enumeration of the binary field used by the finite check. -/
def binaryFintype : Fintype (ZMod 2) := Fin.fintype 2

attribute [local instance] binaryFintype

/-- The linear map whose columns are the three vectors `u i`. -/
def baseLinear (u : Fin 3 → (Fin 3 → ZMod 2)) (x : (Fin 3 → ZMod 2)) : (Fin 3 → ZMod 2) :=
  ∑ i, x i • u i

/-- Executable translation-and-column data for affine maps preserving the base template. -/
def baseAffineData := {p : (Fin 3 → ZMod 2) × (Fin 3 → (Fin 3 → ZMod 2)) //
  Function.Bijective (baseLinear p.2) ∧
  ∀ x, baseTemplate (baseLinear p.2 x+p.1)=baseTemplate x}

/-- `baseLinear` packaged as a linear map. -/
noncomputable def baseLinearMap (u : Fin 3 → (Fin 3 → ZMod 2)) : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  { toFun := baseLinear u,
    map_add' := by
      intro x y
      ext j
      simp [baseLinear, add_mul, Finset.sum_add_distrib],
    map_smul' := by
      intro a x
      ext j
      simp [baseLinear]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      change (a * x i) * u i j = a * (x i * u i j)
      ring }

/-- Evaluation of the packaged column map. -/
@[simp] theorem baseLinearMap_apply (u : Fin 3 → (Fin 3 → ZMod 2)) (x : (Fin 3 → ZMod 2)) :
    baseLinearMap u x = baseLinear u x := by rfl

/-- The column map sends the `i`th coordinate vector to its `i`th column. -/
@[simp] theorem baseLinear_basis (u : Fin 3 → (Fin 3 → ZMod 2)) (i : Fin 3) :
    baseLinear u (Pi.single i 1) = u i := by
  classical
  ext j
  simp only [baseLinear, Pi.single_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [hbi]
  · simp

/-- The vector in `F₂³` whose coordinate `i` is bit `i` of `n`. -/
def binaryVec (n : ℕ) : Fin 3 → ZMod 2 := fun i => ⟨n/2^i.val%2, Nat.mod_lt _ two_pos⟩

/-- Translation-and-column data from the bit codes of the translation and the columns. -/
def baseDatum (t a b c : ℕ) : (Fin 3 → ZMod 2) × (Fin 3 → (Fin 3 → ZMod 2)) :=
  (binaryVec t, ![binaryVec a, binaryVec b, binaryVec c])

/-- The 24 translation-and-column data preserving the base template, by bit codes.
Bit codes keep `ZMod 2` numerals out of the kernel checks below. -/
def baseAffineList : List ((Fin 3 → ZMod 2) × (Fin 3 → (Fin 3 → ZMod 2))) :=
  [baseDatum 0 2 1 4, baseDatum 0 2 7 4, baseDatum 0 1 2 4, baseDatum 0 1 7 4,
   baseDatum 0 7 2 4, baseDatum 0 7 1 4, baseDatum 2 2 5 4, baseDatum 2 2 3 4,
   baseDatum 2 5 2 4, baseDatum 2 5 3 4, baseDatum 2 3 2 4, baseDatum 2 3 5 4,
   baseDatum 1 6 1 4, baseDatum 1 6 3 4, baseDatum 1 1 6 4, baseDatum 1 1 3 4,
   baseDatum 1 3 6 4, baseDatum 1 3 1 4, baseDatum 7 6 5 4, baseDatum 7 6 7 4,
   baseDatum 7 5 6 4, baseDatum 7 5 7 4, baseDatum 7 7 6 4, baseDatum 7 7 5 4]

/-- Addition on `ZMod 2` through residues, which the kernel evaluates cheaply. -/
def binaryAdd (a b : ZMod 2) : ZMod 2 := ⟨(a.val+b.val)%2, Nat.mod_lt _ two_pos⟩

/-- Multiplication on `ZMod 2` through residues, which the kernel evaluates cheaply. -/
def binaryMul (a b : ZMod 2) : ZMod 2 := ⟨a.val*b.val%2, Nat.mod_lt _ two_pos⟩

theorem binaryAdd_eq : ∀ a b : ZMod 2, binaryAdd a b=a+b := by decide

theorem binaryMul_eq : ∀ a b : ZMod 2, binaryMul a b=a*b := by decide

/-- The base template, written with `binaryAdd` and `binaryMul`. -/
def binaryTemplate (x : Fin 3 → ZMod 2) : ZMod 2 := binaryAdd (binaryMul (x 0) (x 1)) (x 2)

/-- The affine image `baseLinear p.2 x+p.1`, written with `binaryAdd` and `binaryMul`. -/
def binaryImage (p : (Fin 3 → ZMod 2) × (Fin 3 → (Fin 3 → ZMod 2))) (x : Fin 3 → ZMod 2) :
    Fin 3 → ZMod 2 := fun j => binaryAdd (binaryAdd (binaryAdd (binaryMul (x 0) (p.2 0 j))
  (binaryMul (x 1) (p.2 1 j))) (binaryMul (x 2) (p.2 2 j))) (p.1 j)

/-- The template condition in kernel-cheap form. -/
abbrev baseTemplateCheck (p : (Fin 3 → ZMod 2) × (Fin 3 → (Fin 3 → ZMod 2))) : Prop :=
  ∀ x, binaryTemplate (binaryImage p x)=binaryTemplate x

theorem baseTemplateCheck_iff (p : (Fin 3 → ZMod 2) × (Fin 3 → (Fin 3 → ZMod 2))) :
    baseTemplateCheck p ↔ ∀ x, baseTemplate (baseLinear p.2 x+p.1)=baseTemplate x := by
  simp [baseTemplateCheck, binaryTemplate, binaryImage, binaryAdd_eq, binaryMul_eq, baseTemplate, baseLinear,
    Fin.sum_univ_three]

/-- Every template-preserving datum is listed. The template values at `0` and at the
three coordinate vectors constrain the translation and each column separately, so
the search visits a few hundred partial data instead of all 4096. -/
theorem mem_baseAffineList_of_columns : ∀ t : Fin 3 → ZMod 2, baseTemplate t=0 →
    ∀ u₀ : Fin 3 → ZMod 2, baseTemplate (u₀+t)=baseTemplate (Pi.single 0 1) →
    ∀ u₁ : Fin 3 → ZMod 2, baseTemplate (u₁+t)=baseTemplate (Pi.single 1 1) →
    ∀ u₂ : Fin 3 → ZMod 2, baseTemplate (u₂+t)=baseTemplate (Pi.single 2 1) →
    baseTemplateCheck (t, ![u₀, u₁, u₂]) → (t, ![u₀, u₁, u₂]) ∈ baseAffineList := by
  have hcheck : ∀ t : Fin 3 → ZMod 2, baseTemplate t=0 →
      ∀ u₀ : Fin 3 → ZMod 2, baseTemplate (u₀+t)=baseTemplate (Pi.single 0 1) →
      ∀ u₁ : Fin 3 → ZMod 2, baseTemplate (u₁+t)=baseTemplate (Pi.single 1 1) →
      binaryTemplate (binaryImage (t, ![u₀, u₁, 0]) (binaryVec 3))=binaryTemplate (binaryVec 3) →
      ∀ u₂ : Fin 3 → ZMod 2, baseTemplate (u₂+t)=baseTemplate (Pi.single 2 1) →
      binaryTemplate (binaryImage (t, ![u₀, u₁, u₂]) (binaryVec 5))=binaryTemplate (binaryVec 5) →
      binaryTemplate (binaryImage (t, ![u₀, u₁, u₂]) (binaryVec 6))=binaryTemplate (binaryVec 6) →
      (t, ![u₀, u₁, u₂]) ∈ baseAffineList := by
    decide +kernel
  intro t ht u₀ h₀ u₁ h₁ u₂ h₂ hpres
  have himage : binaryImage (t, ![u₀, u₁, 0]) (binaryVec 3) =
      binaryImage (t, ![u₀, u₁, u₂]) (binaryVec 3) := by
    funext j
    change binaryAdd (binaryAdd (binaryAdd (binaryMul 1 (u₀ j)) (binaryMul 1 (u₁ j)))
        (binaryMul 0 0)) (t j) =
      binaryAdd (binaryAdd (binaryAdd (binaryMul 1 (u₀ j)) (binaryMul 1 (u₁ j)))
        (binaryMul 0 (u₂ j))) (t j)
    simp only [binaryMul_eq, zero_mul]
  exact hcheck t ht u₀ h₀ u₁ h₁ ((congrArg binaryTemplate himage).trans (hpres (binaryVec 3)))
    u₂ h₂ (hpres (binaryVec 5)) (hpres (binaryVec 6))

/-- Every listed datum has trivial kernel and preserves the base template. The check
runs through the list itself; a bare `∀ p ∈ baseAffineList` would be decided by
enumerating every datum. -/
theorem baseAffineList_spec : ∀ p ∈ baseAffineList,
    (∀ x, binaryImage (0, p.2) x=0 → x=0) ∧ baseTemplateCheck p := by
  have h : baseAffineList.all (fun p =>
      decide ((∀ x, binaryImage (0, p.2) x=0 → x=0) ∧ baseTemplateCheck p))=true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem baseAffineList_nodup : baseAffineList.Nodup := by
  decide +kernel

theorem mem_baseAffineList_iff (p : (Fin 3 → ZMod 2) × (Fin 3 → (Fin 3 → ZMod 2))) :
    p ∈ baseAffineList ↔ Function.Bijective (baseLinear p.2) ∧
      ∀ x, baseTemplate (baseLinear p.2 x+p.1)=baseTemplate x := by
  obtain ⟨t, u⟩ := p
  have hu : ![u 0, u 1, u 2]=u := by funext i; fin_cases i <;> rfl
  constructor
  · intro h
    obtain ⟨hker, hcheck⟩ := baseAffineList_spec _ h
    refine ⟨?_, (baseTemplateCheck_iff _).1 hcheck⟩
    have hlin : ∀ x, binaryImage (0, u) x=baseLinear u x := fun x => by
      funext j
      simp [binaryImage, binaryAdd_eq, binaryMul_eq, baseLinear, Fin.sum_univ_three]
    have hinj : Function.Injective (baseLinearMap u) :=
      (injective_iff_map_eq_zero (baseLinearMap u)).2 fun x hx => hker x (by simpa [hlin] using hx)
    exact Finite.injective_iff_bijective.1 hinj
  · rintro ⟨-, h⟩
    have hcol (i : Fin 3) := h (Pi.single i 1)
    simp only [baseLinear_basis] at hcol
    have h0 := h 0
    simp only [baseLinear, Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add] at h0
    have hmem := mem_baseAffineList_of_columns t (h0.trans (by decide)) (u 0) (hcol 0) (u 1)
      (hcol 1) (u 2) (hcol 2) ((baseTemplateCheck_iff _).2 (by rw [hu]; exact h))
    rwa [hu] at hmem

/-- The finite enumeration given by the explicit list. Later finite checks over
`baseAffineData` therefore run through 24 elements rather than 4096 candidates. -/
def baseAffineDataFintype : Fintype baseAffineData :=
  Fintype.subtype ⟨baseAffineList, baseAffineList_nodup⟩ fun p =>
    (Multiset.mem_coe.trans (mem_baseAffineList_iff p))

attribute [local instance] baseAffineDataFintype

/-- A linear map is reconstructed from the images of the coordinate vectors. -/
theorem baseLinear_columns (L : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (x : (Fin 3 → ZMod 2)) :
    baseLinear (fun i => L (Pi.single i 1)) x = L x := by
  unfold baseLinear
  simp_rw [← L.map_smul]
  rw [← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply]



/-- Exactly 24 translation-and-column data preserve the base template. -/
theorem baseAffineData_card : Fintype.card baseAffineData = 24 := by
  decide +kernel

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] affineFunctionMulAction

/-- Record the translation and linear columns of a base-template stabilizer. -/
noncomputable def baseStabilizerDataMap :
    affineFunctionStabilizer baseTemplate → baseAffineData := fun e =>
  ⟨(e.1 0, fun i => e.1.linear (Pi.single i 1)), by
    constructor
    · change Function.Bijective (baseLinear (fun i => e.1.linear (Pi.single i 1)))
      have heq : baseLinear (fun i => e.1.linear (Pi.single i 1)) = e.1.linear := by
        funext x
        exact baseLinear_columns e.1.linear x
      rw [heq]
      exact e.1.linear.bijective
    · intro x
      change baseTemplate (baseLinear (fun i => e.1.linear (Pi.single i 1)) x + e.1 0) = baseTemplate x
      have hcol := baseLinear_columns e.1.linear x
      have heval : e.1 x = e.1.linear x + e.1 0 := by
        have h := e.1.map_vadd (0 : (Fin 3 → ZMod 2)) x
        simpa [add_comm] using h
      calc
        baseTemplate (baseLinear (fun i => e.1.linear (Pi.single i 1)) x + e.1 0) =
            baseTemplate (e.1.linear x + e.1 0) := by
          exact congrArg baseTemplate (congrArg (fun y => y + e.1 0) hcol)
        _ = baseTemplate (e.1 x) := by rw [heval]
        _ = baseTemplate x := (mem_affineFunctionStabilizer baseTemplate e.1).mp e.2 x⟩


/-- Translation and column data classify the base-template stabilizer. -/
theorem baseStabilizerDataMap_bijective : Function.Bijective baseStabilizerDataMap := by
  constructor
  · intro e e' h
    apply Subtype.ext
    apply affineEquivCoordinates.injective
    apply Prod.ext
    · exact congrArg (fun p : baseAffineData => p.1.1) h
    · apply LinearEquiv.ext
      intro x
      change e.1.linear x = e'.1.linear x
      have hc := congrArg (fun p : baseAffineData => p.1.2) h
      have hc' : (fun i => e.1.linear (Pi.single i 1)) =
          (fun i => e'.1.linear (Pi.single i 1)) := by
        simpa [baseStabilizerDataMap] using hc
      calc
        e.1.linear x = baseLinear (fun i => e.1.linear (Pi.single i 1)) x :=
          (baseLinear_columns e.1.linear x).symm
        _ = baseLinear (fun i => e'.1.linear (Pi.single i 1)) x := by rw [hc']
        _ = e'.1.linear x := baseLinear_columns e'.1.linear x
  · intro p
    let L : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
      LinearEquiv.ofBijective (baseLinearMap p.1.2) p.2.1
    let e : (Fin 3 → ZMod 2) ≃ᵃ[ZMod 2] (Fin 3 → ZMod 2) := affineEquivCoordinates.symm (p.1.1, L)
    have hL (x : (Fin 3 → ZMod 2)) : L x = baseLinear p.1.2 x := by
      change (LinearEquiv.ofBijective (baseLinearMap p.1.2) p.2.1) x =
        baseLinearMap p.1.2 x
      exact LinearEquiv.ofBijective_apply (baseLinearMap p.1.2) x
    have heval (x : (Fin 3 → ZMod 2)) : e x = baseLinear p.1.2 x + p.1.1 := by
      simp [e, affineEquivCoordinates, hL, add_comm]
    have he : e ∈ affineFunctionStabilizer baseTemplate := by
      rw [mem_affineFunctionStabilizer]
      intro x
      rw [heval]
      exact p.2.2 x
    refine ⟨⟨e, he⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · simp [baseStabilizerDataMap, e, affineEquivCoordinates, L]
    · funext i
      change L (Pi.single i 1) = p.1.2 i
      rw [hL]
      exact baseLinear_basis p.1.2 i

/-- The base-template stabilizer is equivalent to its executable data model. -/
noncomputable def baseStabilizerDataEquiv :
    affineFunctionStabilizer baseTemplate ≃ baseAffineData := by
  exact Equiv.ofBijective baseStabilizerDataMap baseStabilizerDataMap_bijective

/-- The affine stabilizer of `x₀x₁+x₂` has exactly 24 elements. -/
theorem baseTemplate_stabilizer_card :
    Nat.card (affineFunctionStabilizer baseTemplate) = 24 := by
  rw [Nat.card_congr baseStabilizerDataEquiv, Nat.card_eq_fintype_card, baseAffineData_card]

end BinaryFieldCounterexamples.Trees
