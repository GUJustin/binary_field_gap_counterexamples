/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperbolicZeroCount
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.IsotropicDimension
/-!
# Exact zero-count alternatives for radical-free finite quadratic spaces

Strong induction on the actual vector-space dimension uses an explicit
hyperbolic split whenever a nonzero singular vector exists. The complement
remains quadratic-radical-free, including in characteristic two. Anisotropic
spaces have dimension at most two by the proved Chevalley–Warning consequence,
which supplies the base cases. The resulting odd/even alternatives are literal
natural-number zero counts; no rank/type enumeration is assumed.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open Module
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A nonzero singular vector of a radical-free quadratic form lies outside its polar kernel. -/
theorem singular_not_mem_polar_ker_of_radical_bot (Q : QuadraticForm k V)
    (hQ : Q.radical=⊥) (x : V) (hx : Q x=0) (hne : x≠0) : x ∉ Q.polarBilin.ker := by
  intro hp
  have hr : x ∈ Q.radical := ⟨hx,hp⟩
  rw [hQ] at hr
  exact hne hr

/-- The actual hyperbolic complement of a radical-free quadratic form remains radical-free. -/
theorem hyperbolicComplement_radical_bot (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (x y : V) (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    (Q.comp (hyperbolicComplement Q x y).subtype).radical=⊥ := by
  apply bot_unique
  intro z hz
  have hzQ : Q (z : V)=0 := hz.1
  have hzH (w : hyperbolicComplement Q x y) : Q.polarBilin (z : V) (w : V)=0 := by
    exact congrArg (fun L : hyperbolicComplement Q x y →ₗ[k] k => L w) hz.2
  have hzx : Q.polarBilin (z : V) x=0 := (polar_symm Q _ _).trans z.property.1
  have hzy : Q.polarBilin (z : V) y=0 := (polar_symm Q _ _).trans z.property.2
  have hzrad : (z : V) ∈ Q.radical := by
    refine ⟨hzQ,?_⟩
    ext v
    let e := hyperbolicSplitEquiv Q x y hx hy hxy
    rw [← e.symm_apply_apply v]
    change Q.polarBilin (z : V) ((e v).1.val+(e v).2.1 • x+(e v).2.2 • y)=0
    simp only [map_add,map_smul,hzH,hzx,hzy,smul_zero,add_zero]
  rw [hQ] at hzrad
  exact Subtype.ext hzrad

/-- An anisotropic form has exactly its zero vector as a zero. -/
theorem anisotropic_zero_card [Fintype V] (Q : QuadraticForm k V) (hQ : Q.Anisotropic) :
    Fintype.card {x : V // Q x=0}=1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0,Q.map_zero⟩,?_⟩
  intro x
  exact Subtype.ext (hQ x.val x.property)

/-- The positive even zero-count correction never exceeds its leading term. -/
theorem even_correction_le (q s : ℕ) (hq : 1 ≤ q) :
    (q-1)*q^s ≤ q^(2*s+1) := by
  have hs : s+1 ≤ 2*s+1 := by omega
  have he := Nat.pow_le_pow_right hq hs
  rw [pow_succ',Nat.mul_comm] at he
  have hmul : (q-1)*q^s ≤ q*q^s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  exact hmul.trans (by simpa [Nat.mul_comm] using he)
/-- The actual finite-field zero-count alternatives, indexed without truncated half-exponents. -/
def ZeroCountPattern (q d z : ℕ) : Prop :=
  (d=0 ∧ z=1) ∨ (∃ s : ℕ, d=2*s+1 ∧ z=q^(2*s)) ∨
    (∃ s : ℕ, d=2*s+2 ∧ (z=q^(2*s+1)+(q-1)*q^s ∨ z=q^(2*s+1)-(q-1)*q^s))

/-- The exact hyperbolic recurrence preserves the zero-count alternatives. -/
theorem zeroCountPattern_hyperbolic (q d z : ℕ) (hq : 1 ≤ q) (h : ZeroCountPattern q d z) :
    ZeroCountPattern q (d+2) ((q-1)*q^d+q*z) := by
  have hqm : q-1+1=q := by omega
  rcases h with ⟨rfl,rfl⟩ | ⟨s,rfl,rfl⟩ | ⟨s,rfl,hz⟩
  · right; right
    refine ⟨0,by omega,Or.inl ?_⟩
    simp [Nat.add_comm]
  · right; left
    refine ⟨s+1,by omega,?_⟩
    rw [show 2*(s+1)=2*s+2 by omega,pow_succ q (2*s),pow_add q (2*s) 2,pow_two]
    linarith [congrArg (fun u => u*(q*q^(2*s))) hqm]
  · right; right
    refine ⟨s+1,by omega,?_⟩
    have hp2 : q^(2*s+2)=q*q^(2*s+1) := by rw [show 2*s+2=(2*s+1)+1 by omega,pow_succ']
    have hp3 : q^(2*(s+1)+1)=q*q*q^(2*s+1) := by
      rw [show 2*(s+1)+1=(2*s+1)+2 by omega,pow_add,pow_two]
      ring
    rw [hp2,hp3,pow_succ' q s]
    have hbase : (q-1)*(q*q^(2*s+1))+q*q^(2*s+1)=q*q*q^(2*s+1) := by
      linarith [congrArg (fun u => u*(q*q^(2*s+1))) hqm]
    rcases hz with rfl | rfl
    · left
      linarith
    · right
      have hsub := Nat.sub_add_cancel (even_correction_le q s hq)
      have hnew : (q-1)*(q*q^s) ≤ q*q*q^(2*s+1) := by
        have hh := even_correction_le q (s+1) hq
        rw [hp3,pow_succ' q s] at hh
        exact hh
      have hsubnew := Nat.sub_add_cancel hnew
      linarith [congrArg (fun u => q*u) hsub]
/-- Every actual radical-free finite-field quadratic form has the classical zero-count alternatives. -/
theorem zeroCountPattern_of_radical_bot [Fintype k] [Fintype V]
    (p : ℕ) [Fact p.Prime] [CharP k p] (Q : QuadraticForm k V) (hQ : Q.radical=⊥) :
    ZeroCountPattern (Fintype.card k) (Module.finrank k V) (Fintype.card {x : V // Q x=0}) := by
  generalize hd : Module.finrank k V=d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
    have hq : 1 ≤ Fintype.card k := Fintype.card_pos
    by_cases ha : Q.Anisotropic
    · have hdim := QuadraticCoordinates.anisotropic_finrank_le_two p Q ha
      rw [hd] at hdim
      rw [anisotropic_zero_card Q ha]
      have hc : d=0 ∨ d=1 ∨ d=2 := by omega
      rcases hc with rfl | rfl | rfl
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨0,rfl,by simp⟩)
      · refine Or.inr (Or.inr ⟨0,rfl,Or.inr ?_⟩)
        simp only [Nat.mul_zero,Nat.zero_add,pow_one,pow_zero,Nat.mul_one]
        omega
    · change ¬ ∀ x, Q x=0 → x=0 at ha
      push Not at ha
      obtain ⟨x,hx,hne⟩ := ha
      obtain ⟨y,hy,hxy⟩ := exists_hyperbolic_partner Q x hx
        (singular_not_mem_polar_ker_of_radical_bot Q hQ x hx hne)
      let H := hyperbolicComplement Q x y
      let QH := Q.comp H.subtype
      have hH : QH.radical=⊥ := hyperbolicComplement_radical_bot Q hQ x y hx hy hxy
      have hdim : d=Module.finrank k H+2 := by
        rw [← hd]
        exact hyperbolicComplement_finrank Q x y hx hy hxy
      have hlt : Module.finrank k H < d := by omega
      have hpat := ih (Module.finrank k H) hlt QH hH rfl
      have hstep := zeroCountPattern_hyperbolic (Fintype.card k) (Module.finrank k H)
        (Fintype.card {x : H // QH x=0}) hq hpat
      rw [hdim,hyperbolicSplit_zero_count Q x y hx hy hxy]
      have hcH : Fintype.card H=(Fintype.card k)^(Module.finrank k H) :=
        Module.card_eq_pow_finrank (K:=k)
      change ZeroCountPattern _ _ ((Fintype.card k-1)*Fintype.card H+
        Fintype.card k*Fintype.card {x : H // QH x=0})
      rw [hcH]
      exact hstep
/-- In positive odd dimension a radical-free quadratic form has exactly q^(d-1) zeros. -/
theorem zero_card_of_radical_bot_odd [Fintype k] [Fintype V]
    (p : ℕ) [Fact p.Prime] [CharP k p] (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (hodd : Odd (Module.finrank k V)) :
    Fintype.card {x : V // Q x=0}=(Fintype.card k)^(Module.finrank k V-1) := by
  obtain ⟨r,hr⟩ := hodd
  rcases zeroCountPattern_of_radical_bot p Q hQ with h0 | ⟨s,hs,hz⟩ | ⟨s,hs,hz⟩
  · omega
  · rw [hz,hs]
    congr 1
  · omega

/-- In positive even dimension the two actual zero counts are precisely the plus and minus values. -/
theorem zero_card_of_radical_bot_even [Fintype k] [Fintype V]
    (p : ℕ) [Fact p.Prime] [CharP k p] (Q : QuadraticForm k V) (hQ : Q.radical=⊥)
    (s : ℕ) (hs : 0 < s) (hd : Module.finrank k V=2*s) :
    Fintype.card {x : V // Q x=0}=(Fintype.card k)^(2*s-1)+
        (Fintype.card k-1)*(Fintype.card k)^(s-1) ∨
      Fintype.card {x : V // Q x=0}=(Fintype.card k)^(2*s-1)-
        (Fintype.card k-1)*(Fintype.card k)^(s-1) := by
  rcases zeroCountPattern_of_radical_bot p Q hQ with h0 | ⟨r,hr,hz⟩ | ⟨r,hr,hz⟩
  · omega
  · omega
  · have hs1 : s=r+1 := by omega
    rw [hs1,show 2*(r+1)-1=2*r+1 by omega,show r+1-1=r by omega]
    exact hz
end BinaryFieldCounterexamples.QuadraticGeometry
