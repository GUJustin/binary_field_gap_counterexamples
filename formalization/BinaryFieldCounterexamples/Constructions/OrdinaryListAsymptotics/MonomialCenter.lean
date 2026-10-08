/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SparseFamilyPopulation
public import BinaryFieldCounterexamples.Constructions.NearUnit.LocatorIdentity
public import BinaryFieldCounterexamples.Counting.QuadraticListCount
public import BinaryFieldCounterexamples.Counting.GaussianLowerBound

/-!
# The explicit monomial center of the full-field decoding lists

The sparse locator construction keeps its common high part. On the full
field its domain locator is `X^N-X`, and its canonical Frobenius root is
`X^(N/b)`. Subtracting each locator from this center gives distinct codeword
polynomials with strict degree bound and exact agreement.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.OrdinaryListConstruction
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The full-field additive locator is the usual vanishing polynomial. -/
theorem fullfield_locator {k B : Type*} [Field k] [Field B] [Fintype B]
    [Algebra k B] :
    subspacePolynomial (⊤ : Submodule k B).toAddSubgroup = X ^ Fintype.card B - X := by
  apply NearUnit.subspacePolynomial_eq_of_monic_natDegree_eq
  · exact (monic_X_pow _).sub_of_left (by
      rw [degree_X, degree_X_pow]
      exact_mod_cast (Fintype.one_lt_card (α := B)))
  · rw [FiniteField.X_pow_card_sub_X_natDegree_eq B Fintype.one_lt_card]
    exact (Fintype.card_congr (show ↥(⊤ : Submodule k B).toAddSubgroup ≃ B from
      ⟨Subtype.val,fun x => ⟨x,by simp⟩,fun _ => rfl,fun _ => rfl⟩)).symm
  · intro x _
    simp [FiniteField.pow_card]

/-- The full-field canonical high part is literally a monomial. -/
theorem fullfield_numerator {k B : Type*} [Field k] [Fintype k]
    [Field B] [Fintype B] [Algebra k B]
    (p r n : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r)
    (hq : Fintype.card k = p ^ r) (hn : 1 ≤ n)
    (hcard : Fintype.card B = Fintype.card k ^ (2*n)) :
    primePowerQuarterNumerator p r
      (subspacePolynomial (⊤ : Submodule k B).toAddSubgroup) 0 =
      X ^ (Fintype.card k ^ (2*n-1)) := by
  let b := Fintype.card k
  have hb : 1 < b := Fintype.one_lt_card
  have hN : 1 < b^(2*n) := Nat.one_lt_pow (by omega) hb
  have hshape : ∀ e ∈ (X^(b^(2*n))-X : B[X]).support, ∃ i : ℕ, e=(p^r)^i := by
    intro e he
    by_cases heq : e=b^(2*n)
    · exact ⟨2*n,by simpa [b,←hq] using heq⟩
    by_cases he1 : e=1
    · exact ⟨0,by simpa using he1⟩
    have hc := mem_support_iff.mp he
    simp [coeff_sub,coeff_X_pow,coeff_X,heq,Ne.symm he1] at hc
  rw [fullfield_locator,hcard]
  have hpow := primePowerQuarterNumerator_pow p r hr (X^(b^(2*n))-X : B[X]) 0 hshape
  have hrad : primePowerQuarterRadicand (X^(b^(2*n))-X : B[X]) 0=X^(b^(2*n)) := by
    simp [primePowerQuarterRadicand,coeff_X_pow,show 1≠b^(2*n) by omega]
  rw [hrad] at hpow
  have hexp : (b^(2*n-1))*p^r=b^(2*n) := by
    rw [←hq,←pow_succ]
    congr 1
    omega
  have hz : (primePowerQuarterNumerator p r (X^(b^(2*n))-X : B[X]) 0-
      X^(b^(2*n-1)))^(p^r)=0 := by
    rw [sub_pow_expChar_pow,hpow,←pow_mul,hexp,sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)

/-- Exact finite decoding list around the prescribed monomial center. The
natural list count is the integral version of the paper's Gaussian expression. -/
theorem fullfield_monomial_list
    (k B : Type*) [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (n t : ℕ) (ht : 2 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = Fintype.card k ^ (2*n)) :
    let b := Fintype.card k
    ∃ E : Finset B[X], quadraticListCount b n 0 t ≤ E.card ∧
      ∀ f ∈ E, f.degree < b^(2*n-2) ∧
        agreementCount Finset.univ (fun x => x.val^(b^(2*n-1))) f =
          b^(2*n-1)-(b-1)*b^(2*n-t-1) := by
  obtain ⟨p,hchar,r,hprime,hq⟩ := FiniteField.card' k
  let : CharP k p := hchar
  let : CharP B p := charP_of_injective_algebraMap' k p
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨E,hE,hprop⟩ := QuadraticFormTrace.fullfield_sparse_locator_family p r r.property
    hq n t ht htn hcard
  let R : B[X] := X^(Fintype.card k^(2*n-1))
  have hR := fullfield_numerator p r n r.property hq (by omega) hcard
  rw [hR] at hprop
  refine ⟨E.image (fun P => R-P),?_,?_⟩
  · rw [Finset.card_image_iff.mpr (fun _ _ _ _ h => sub_right_injective h)]
    have hcount := quadratic_list_size_eq_natCast (Fintype.card k) n 0 t
      (by have := Fintype.one_lt_card (α := k); omega) (by simpa using htn)
    simp only [Nat.sub_zero] at hcount
    rw [hcount] at hE
    exact_mod_cast hE
  · intro f hf
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨A,_,_,_,_,_,hdeg,hroots⟩ := hprop P hP
    constructor
    · simpa only [←neg_sub P R,degree_neg] using hdeg
    · rw [agreementCount_eq_card_filter Finset.univ
        (fun x : B => x^(Fintype.card k^(2*n-1))) (R-P)]
      convert hroots using 2
      apply Finset.filter_congr
      intro x _
      simp only [R,eval_sub,eval_pow,eval_X]
      exact sub_eq_self

/-- The integral quadratic list count dominates the Gaussian's leading power. -/
theorem quadraticListCount_lower (b n t : ℕ) (hb : 2 ≤ b) (ht : 1 ≤ t)
    (htn : t ≤ n) : b^(2*t*(n-t)) ≤ quadraticListCount b n 0 t := by
  have hg := pow_mul_sub_le_gaussianPascal (b^2) n t htn
  have hs : 1 ≤ ∑ i ∈ Finset.range t, b^i := by
    simpa using Finset.single_le_sum (fun i _ => Nat.zero_le (b^i))
      (show 0 ∈ Finset.range t by simp; omega)
  have hp : 1 ≤ b^(2*t) := Nat.one_le_pow _ _ (by omega)
  have hbase : 1 ≤ b^(2*t)*(∑ i ∈ Finset.range t,b^i) := by nlinarith
  have hmul := Nat.mul_le_mul_right (gaussianPascal (b^2) n t) hbase
  dsimp only [quadraticListCount]
  simp only [Nat.sub_zero]
  have he : (b^2)^(t*(n-t))=b^(2*t*(n-t)) := by rw [←pow_mul]; congr 1; ring
  exact (he ▸ hg).trans (by simpa using hmul)
end BinaryFieldCounterexamples.OrdinaryListConstruction
