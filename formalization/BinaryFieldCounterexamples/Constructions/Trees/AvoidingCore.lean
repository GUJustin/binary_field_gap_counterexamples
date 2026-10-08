/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.StabilizerForms
public import BinaryFieldCounterexamples.Constructions.Trees.BranchRecovery
/-!
# Canonical avoiding cores

The core selects the zero branch at every recursive root and the actual
quadratic zero fiber at the base. Root recovery and the full stabilizer normal
form prove that every origin-fixing stabilizer preserves this concrete core.
Thus constrained surjective frames have representation-independent fibers.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
attribute [local instance] templateSpaceAddCommGroup templateSpaceModule templateSpaceFintype
/-- The canonical zero branch is selected at each recursive root. -/
def templateAvoidingCore : (n : ℕ) → TemplateSpace n → Prop
  | 0, x => baseTemplate x=0
  | n+1, x => x.1=0 ∧ templateAvoidingCore n x.2.1
/-- The canonical avoiding core is contained in the actual template zero fiber. -/
theorem templateAvoidingCore_zero (n : ℕ) (x : TemplateSpace n) (hx : templateAvoidingCore n x) :
    template n x=0 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    change x.1=0 ∧ templateAvoidingCore n x.2.1 at hx
    change branch (template n) (template n) x=0
    simp only [branch,hx.1,↓reduceIte]
    exact ih x.2.1 hx.2
/-- The origin lies in every canonical avoiding core. -/
theorem templateAvoidingCore_origin (n : ℕ) : templateAvoidingCore n 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨rfl,ih⟩
/-- Origin-fixing template stabilizers preserve the actual root coordinate. -/
theorem template_origin_stabilizer_first (n : ℕ)
    (e : affineFunctionStabilizer (template (n+1))) (he0 : e.1 0=0) :
    ∀ x, (e.1 x).1=x.1 := by
  change affineFunctionStabilizer (branch (template n) (template n)) at e
  change e.1 (0 : ZMod 2 × TemplateSpace n × TemplateSpace n)=0 at he0
  change ∀ x : ZMod 2 × TemplateSpace n × TemplateSpace n, (e.1 x).1=x.1
  have hf : ∃ x y, template n x≠template n y := by
    obtain ⟨x,hx⟩ := template_surjective n 0
    obtain ⟨y,hy⟩ := template_surjective n 1
    exact ⟨x,y,by rw [hx,hy]; decide⟩
  have hfp : ∀ u, IsPeriod (template n) u → u=0 := fun u => (template_period_iff n u).mp
  have hV : 2<Nat.card (TemplateSpace n) := by
    rw [Nat.card_eq_fintype_card,templateSpace_card]
    have hp : 4≤(2:ℕ)^(n+2) := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : 2≤n+2)
    calc
      2<2^3 := by decide
      _≤_ := Nat.pow_le_pow_right (by decide) (by omega)
  have hz := affine_branch_stabilizer_first_linear (template n) (template n) hf hf hfp hfp hV e.1
    ((mem_affineFunctionStabilizer _ _).mp e.2)
  intro x
  have hel : e.1.linear x=e.1 x := by
    have h := e.1.map_vadd (0:ZMod 2 × TemplateSpace n × TemplateSpace n) x
    simpa [he0] using h.symm
  rw [←hel]
  exact hz x
/-- The canonical avoiding core is invariant under every actual origin-fixing template stabilizer. -/
theorem templateAvoidingCore_stabilizer (n : ℕ) (e : affineFunctionStabilizer (template n))
    (he0 : e.1 0=0) (x : TemplateSpace n) :
    templateAvoidingCore n (e.1 x) ↔ templateAvoidingCore n x := by
  induction n with
  | zero =>
    change baseTemplate (e.1 x)=0 ↔ baseTemplate x=0
    exact congrArg (fun z : ZMod 2 => z=0) ((mem_affineFunctionStabilizer _ _).mp e.2 x) |>.to_iff
  | succ n ih =>
    change affineFunctionStabilizer (branch (template n) (template n)) at e
    change ZMod 2 × TemplateSpace n × TemplateSpace n at x
    change e.1 (0 : ZMod 2 × TemplateSpace n × TemplateSpace n)=0 at he0
    have hz : ∀ x : ZMod 2 × TemplateSpace n × TemplateSpace n, (e.1 x).1=x.1 :=
      template_origin_stabilizer_first n e he0
    obtain ⟨e0,e1,h0,h1,a,b,he⟩ := branch_stabilizer_normal_form (template n)
      (fun u => (template_period_iff n u).mp) e.1 e.2 hz
    have he00 : e0 0=0 := by
      have h := congrArg (fun x : ZMod 2 × TemplateSpace n × TemplateSpace n => x.2.1) he0
      change (e.1 (0 : ZMod 2 × TemplateSpace n × TemplateSpace n)).2.1=0 at h
      rw [he,branchPreservingForm_apply] at h
      simpa using h
    change (e.1 x).1=0 ∧ templateAvoidingCore n (e.1 x).2.1 ↔
      x.1=0 ∧ templateAvoidingCore n x.2.1
    rw [hz]
    by_cases hx : x.1=0
    · simp only [hx,true_and]
      rw [he,branchPreservingForm_apply]
      simp only [hx,zero_smul,add_zero]
      exact ih ⟨e0,h0⟩ he00 x.2.1
    · simp [hx]
end BinaryFieldCounterexamples.Trees
