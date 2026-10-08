/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.SubspacePolynomial
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Prime-power support of actual finite scalar-subspace locators

For a finite scalar field of cardinality `q`, the concrete product locator of
a finite scalar subspace has support only at exponents `q^i`. The proof uses
scalar-field Frobenius, induction along an independent tuple, and monic root
interpolation to establish the literal flag recurrence. A basis reindexes that
product to `subspacePolynomial`; no polynomial is inferred merely from its
function on the ambient finite field. Evaluation is scalar-linear and the
actual derivative is the constant coefficient of `X`.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.FiniteFieldLocator
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {k K : Type*} [Field k] [Fintype k] [Field K] [Algebra k K]

/-- Literal polynomial support at powers of the scalar-field cardinality. -/
def IsQLinearized (P : K[X]) : Prop := ∀ n∈P.support, ∃ i : ℕ, n=(Fintype.card k)^i
/-- Iterated scalar-field Frobenius is an actual linear map. -/
noncomputable def qPowerLinearMap : ℕ → K →ₗ[k] K
  | 0 => LinearMap.id
  | i+1 => (FiniteField.frobeniusAlgHom k K).toLinearMap.comp (qPowerLinearMap i)
/-- The linear Frobenius iterate has its literal power function. -/
theorem qPowerLinearMap_apply (i : ℕ) (x : K) :
    qPowerLinearMap (k:=k) i x=x^((Fintype.card k)^i) := by
  induction i with
  | zero => simp [qPowerLinearMap]
  | succ i ih =>
    simp only [qPowerLinearMap,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
      FiniteField.frobeniusAlgHom_apply,ih,pow_succ,pow_mul]
/-- A q-supported polynomial evaluates additively. -/
theorem IsQLinearized.eval_add (P : K[X]) (hP : IsQLinearized (k:=k) P) (x y : K) :
    P.eval (x+y)=P.eval x+P.eval y := by
  simp only [eval_eq_sum,Polynomial.sum]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨i,rfl⟩ := hP n hn
  have he := (qPowerLinearMap (k:=k) (K:=K) i).map_add x y
  simp only [qPowerLinearMap_apply] at he
  rw [he,mul_add]
/-- A q-supported polynomial evaluates homogeneously over the scalar field. -/
theorem IsQLinearized.eval_smul (P : K[X]) (hP : IsQLinearized (k:=k) P) (c : k) (x : K) :
    P.eval (c • x)=c • P.eval x := by
  simp only [eval_eq_sum,Polynomial.sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨i,rfl⟩ := hP n hn
  have he := (qPowerLinearMap (k:=k) (K:=K) i).map_smul c x
  simp only [qPowerLinearMap_apply] at he
  rw [he,Algebra.smul_def,Algebra.smul_def]
  ring
/-- The evaluations of a q-supported polynomial form a literal linear map. -/
noncomputable def IsQLinearized.evalLinearMap (P : K[X]) (hP : IsQLinearized (k:=k) P) : K →ₗ[k] K :=
  { toFun := fun x => P.eval x
    map_add' := hP.eval_add P
    map_smul' := hP.eval_smul P }
/-- The coordinate polynomial has q-power support. -/
theorem isQLinearized_X : IsQLinearized (k:=k) (X:K[X]) := by
  intro n hn
  rw [support_X,Finset.mem_singleton] at hn
  exact ⟨0,by simpa using hn⟩
/-- Constant multiplication preserves q-power support. -/
theorem IsQLinearized.c_mul (P : K[X]) (hP : IsQLinearized (k:=k) P) (c : K) :
    IsQLinearized (k:=k) (C c*P) := by
  intro n hn
  rw [mem_support_iff,coeff_C_mul] at hn
  exact hP n (mem_support_iff.mpr (fun hz => hn (by rw [hz,mul_zero])))
/-- Subtraction preserves q-power support. -/
theorem IsQLinearized.sub (P Q : K[X]) (hP : IsQLinearized (k:=k) P)
    (hQ : IsQLinearized (k:=k) Q) : IsQLinearized (k:=k) (P-Q) := by
  intro n hn
  rw [mem_support_iff,coeff_sub] at hn
  by_cases hp : P.coeff n=0
  · exact hQ n (mem_support_iff.mpr (fun hq => hn (by rw [hp,hq,sub_self])))
  · exact hP n (mem_support_iff.mpr hp)
/-- Scalar-field Frobenius multiplies each supported exponent by q. -/
theorem IsQLinearized.pow_card (P : K[X]) (hP : IsQLinearized (k:=k) P) :
    IsQLinearized (k:=k) (P^(Fintype.card k)) := by
  obtain ⟨p,hchar,n,hprime,hcard⟩ := FiniteField.card' k
  let : CharP k p := hchar
  let : CharP K p := charP_of_injective_algebraMap' k p
  let : Fact p.Prime := ⟨hprime⟩
  intro e he
  have hc : (P^(Fintype.card k)).coeff e≠0 := mem_support_iff.mp he
  rw [hcard,←map_iterateFrobenius_expand p P n,coeff_map,
    coeff_expand (pow_pos hprime.pos (n:ℕ))] at hc
  by_cases hd : p^(n:ℕ)∣e
  · rw [ite_eq_left hd] at hc
    have hn : P.coeff (e/p^(n:ℕ))≠0 := by
      intro hz
      exact hc (by rw [hz,map_zero])
    obtain ⟨i,hi⟩ := hP _ (mem_support_iff.mpr hn)
    refine ⟨i+1,?_⟩
    rw [pow_succ,←hi,hcard]
    exact (Nat.div_mul_cancel hd).symm
  · rw [ite_eq_right hd,map_zero] at hc
    exact False.elim (hc rfl)
/-- The literal locator product over all scalar combinations of a tuple. -/
noncomputable def qSpanPolynomial {d : ℕ} (v : Fin d → K) : K[X] :=
  ∏ c : Fin d → k, (X-C (∑ i, c i • v i))
/-- The coefficient-tuple product is monic. -/
theorem qSpanPolynomial_monic {d : ℕ} (v : Fin d → K) :
    (qSpanPolynomial (k:=k) v).Monic := by
  exact monic_prod_X_sub_C _ _
/-- The coefficient-tuple product has its literal degree, even for a dependent tuple. -/
theorem qSpanPolynomial_natDegree {d : ℕ} (v : Fin d → K) :
    (qSpanPolynomial (k:=k) v).natDegree=(Fintype.card k)^d := by
  unfold qSpanPolynomial
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_fun,Fintype.card_fin]
/-- Every scalar combination is an actual root of its tuple product. -/
theorem qSpanPolynomial_eval_combination {d : ℕ} (v : Fin d → K) (c : Fin d → k) :
    (qSpanPolynomial (k:=k) v).eval (∑ i, c i • v i)=0 := by
  simp only [qSpanPolynomial,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_eq_zero_iff]
  exact ⟨c,Finset.mem_univ _,sub_self _⟩
/-- Frobenius extension of the tuple product is monic of the next flag degree. -/
theorem qSpan_recurrence_monic_degree {d : ℕ} (v : Fin d → K) (a : K) :
    IsMonicOfDegree ((qSpanPolynomial (k:=k) v)^(Fintype.card k)-
      C (((qSpanPolynomial (k:=k) v).eval a)^(Fintype.card k-1))*qSpanPolynomial (k:=k) v)
      ((Fintype.card k)^(d+1)) := by
  let P := qSpanPolynomial (k:=k) v
  have hp : P.Monic := qSpanPolynomial_monic v
  have hsmall : (C ((P.eval a)^(Fintype.card k-1))*P).natDegree<
      (P^(Fintype.card k)).natDegree := by
    apply (natDegree_C_mul_le _ _).trans_lt
    rw [natDegree_pow]
    have hpos : 0<P.natDegree := by
      rw [qSpanPolynomial_natDegree]
      exact pow_pos Fintype.card_pos _
    nlinarith [Fintype.one_lt_card (α:=k)]
  refine ⟨?_,hp.pow _ |>.sub_of_left ?_⟩
  · rw [natDegree_sub_eq_left_of_natDegree_lt hsmall,natDegree_pow,qSpanPolynomial_natDegree,pow_succ]
    exact Nat.mul_comm _ _
  · rw [degree_eq_natDegree (pow_ne_zero _ hp.ne_zero)]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hsmall)
/-- Independent tuple extension obeys the actual q-Frobenius locator recurrence. -/
theorem qSpanPolynomial_snoc_recurrence {d : ℕ} (v : Fin d → K) (a : K)
    (hv : LinearIndependent k (Fin.snoc v a))
    (hP : IsQLinearized (k:=k) (qSpanPolynomial (k:=k) v)) :
    qSpanPolynomial (k:=k) (Fin.snoc v a)=
      (qSpanPolynomial (k:=k) v)^(Fintype.card k)-
      C (((qSpanPolynomial (k:=k) v).eval a)^(Fintype.card k-1))*qSpanPolynomial (k:=k) v := by
  let P := qSpanPolynomial (k:=k) v
  let Q := P^(Fintype.card k)-C ((P.eval a)^(Fintype.card k-1))*P
  have hmonic : IsMonicOfDegree Q ((Fintype.card k)^(d+1)) := qSpan_recurrence_monic_degree v a
  have hinj : Function.Injective (fun c : Fin (d+1) → k => ∑ i, c i • (Fin.snoc v a : Fin (d+1) → K) i) := by
    exact hv.fintypeLinearCombination_injective
  apply sub_eq_zero.mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
  · intro c
    have hsum : (∑ i : Fin (d+1), c i • (Fin.snoc v a : Fin (d+1) → K) i)=
        (∑ i : Fin d, c i.castSucc • v i)+c (Fin.last d) • a := by
      rw [Fin.sum_univ_castSucc]
      simp
    have hPeval : P.eval (∑ i, c i • (Fin.snoc v a : Fin (d+1) → K) i)=c (Fin.last d) • P.eval a := by
      rw [hsum,IsQLinearized.eval_add P hP,IsQLinearized.eval_smul P hP,
        qSpanPolynomial_eval_combination,zero_add]
    rw [eval_sub,qSpanPolynomial_eval_combination]
    change 0-Q.eval _=0
    simp only [Q,eval_sub,eval_pow,eval_mul,eval_C,hPeval]
    rw [Algebra.smul_def,mul_pow,←map_pow,FiniteField.pow_card]
    have hpw : (P.eval a)^(Fintype.card k)=(P.eval a)^(Fintype.card k-1)*P.eval a := by
      rw [←pow_succ]
      congr 1
      have := Fintype.card_pos (α:=k)
      omega
    rw [hpw]
    ring
  · have hpmonic : IsMonicOfDegree (qSpanPolynomial (k:=k) (Fin.snoc v a))
        ((Fintype.card k)^(d+1)) := ⟨qSpanPolynomial_natDegree _,qSpanPolynomial_monic _⟩
    simpa only [Fintype.card_fun,Fintype.card_fin] using hpmonic.natDegree_sub_lt (pow_ne_zero _ Fintype.card_ne_zero) hmonic
/-- The empty coefficient tuple gives the actual locator `X`. -/
theorem qSpanPolynomial_zero (v : Fin 0 → K) : qSpanPolynomial (k:=k) v=X := by
  simp [qSpanPolynomial]
/-- The actual product locator of an independent tuple has q-power support. -/
theorem qSpanPolynomial_support {d : ℕ} (v : Fin d → K) (hv : LinearIndependent k v) :
    IsQLinearized (k:=k) (qSpanPolynomial (k:=k) v) := by
  refine Fin.snocInduction (motive := fun {d} v => LinearIndependent k v →
    IsQLinearized (k:=k) (qSpanPolynomial (k:=k) v)) ?_ ?_ v hv
  · intro hv
    rw [qSpanPolynomial_zero]
    exact isQLinearized_X
  · intro d v a ih hv
    have hvold : LinearIndependent k v := by
      simpa only [Function.comp_def,Fin.snoc_castSucc] using hv.comp
        (Fin.castSucc : Fin d → Fin (d+1)) (Fin.castSucc_injective d)
    have hP := ih hvold
    rw [qSpanPolynomial_snoc_recurrence v a hv hP]
    exact IsQLinearized.sub _ _ (IsQLinearized.pow_card _ hP) (IsQLinearized.c_mul _ hP _)
/-- A finite scalar subspace's concrete product locator has only q-power
exponents; the ambient field need not be finite. -/
theorem subspacePolynomial_q_support (D : Submodule k K) [Fintype D] :
    IsQLinearized (k:=k) (subspacePolynomial D.toAddSubgroup) := by
  let b := Module.finBasis k D
  let v : Fin (Module.finrank k D) → K := fun i => (b i : K)
  have hv : LinearIndependent k v := b.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  have heq : subspacePolynomial D.toAddSubgroup=qSpanPolynomial (k:=k) v := by
    unfold subspacePolynomial qSpanPolynomial
    apply Fintype.prod_equiv b.equivFun.toEquiv
    intro w
    congr 2
    change (w:K)=∑ i, b.equivFun w i • (b i : K)
    have hb := b.sum_equivFun w
    simpa only [Submodule.coe_sum,Submodule.coe_smul_of_tower] using
      congrArg (fun z : D => (z:K)) hb.symm
  rw [heq]
  exact qSpanPolynomial_support v hv
/-- The actual subspace locator defines a scalar-linear evaluation map. -/
noncomputable def subspacePolynomial_evalLinearMap (D : Submodule k K) [Fintype D] : K →ₗ[k] K :=
  IsQLinearized.evalLinearMap _ (subspacePolynomial_q_support D)
/-- Q-power support excludes a constant term. -/
theorem IsQLinearized.coeff_zero (P : K[X]) (hP : IsQLinearized (k:=k) P) :
    P.coeff 0=0 := by
  by_contra hz
  obtain ⟨i,hi⟩ := hP 0 (mem_support_iff.mpr hz)
  exact (pow_ne_zero i Fintype.card_ne_zero) hi.symm
/-- In the scalar field's characteristic, a q-supported polynomial has a
constant derivative equal to its actual coefficient of `X`. -/
theorem IsQLinearized.derivative (P : K[X]) (hP : IsQLinearized (k:=k) P) :
    P.derivative=C (P.coeff 1) := by
  have hq : ((Fintype.card k:ℕ):K)=0 := by
    rw [←map_natCast (algebraMap k K),FiniteField.cast_card_eq_zero,map_zero]
  ext n
  rw [coeff_derivative,coeff_C]
  by_cases hn : n=0
  · subst n
    simp
  · rw [ite_eq_right hn]
    by_cases hc : P.coeff (n+1)=0
    · rw [hc,zero_mul]
    · obtain ⟨i,hi⟩ := hP (n+1) (mem_support_iff.mpr hc)
      have hi0 : i≠0 := by
        intro hz
        simp only [hz,pow_zero] at hi
        omega
      have he : ((n+1:ℕ):K)=0 := by rw [hi,Nat.cast_pow,hq,zero_pow hi0]
      simpa only [Nat.cast_add,Nat.cast_one,mul_zero] using congrArg (fun z : K => P.coeff (n+1)*z) he
/-- The concrete subspace locator has the required constant derivative. -/
theorem subspacePolynomial_derivative (D : Submodule k K) [Fintype D] :
    (subspacePolynomial D.toAddSubgroup).derivative=C ((subspacePolynomial D.toAddSubgroup).coeff 1) := by
  exact IsQLinearized.derivative _ (subspacePolynomial_q_support D)
end BinaryFieldCounterexamples.FiniteFieldLocator
