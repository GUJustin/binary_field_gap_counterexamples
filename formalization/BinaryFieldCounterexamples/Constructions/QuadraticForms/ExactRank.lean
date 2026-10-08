/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ZeroBound
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceTranslation
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceRadical
/-!
# Exact-rank radicals and the smaller zero-count bound

The concrete trace family's polar rank bound forces quadratic and polar radicals
to agree at exact minimum quadratic rank, including characteristic two.
Saturation of the sparse derivative root bound gives exact multiplicities.
The literal differential identity then gives the smaller zero-count upper bound,
without assuming a type classification or a global splitting theorem.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
set_option linter.unusedSectionVars false
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
/-- The polar rank lower bound forces equality of the quadratic radical and polar kernel. -/
theorem radical_eq_polar_ker_of_rank_ge (Q : QuadraticForm k B) (d : ℕ)
    (hQ : Module.finrank k B - Module.finrank k Q.radical = d)
    (hP : d ≤ Module.finrank k Q.polarBilin.range) :
    Q.radical = Q.polarBilin.ker := by
  apply Submodule.eq_of_le_of_finrank_eq QuadraticMap.radical_le_ker_polarBilin
  have hm := Submodule.finrank_mono (QuadraticMap.radical_le_ker_polarBilin (Q := Q))
  have he := Q.polarBilin.finrank_range_add_finrank_ker
  omega
/-- At exact minimum quadratic rank the actual trace radical is the derivative kernel. -/
theorem traceFamily_radical_eq_derivative_ker_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical = 2*t) :
    (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical =
      (traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c).ker := by
  rw [← traceFamilyQuadraticForm_ker_polarBilin n t ht htn a c hcard hc]
  exact radical_eq_polar_ker_of_rank_ge _ _ hrank
    (traceFamilyQuadraticForm_polar_rank_ge p r hq n t ht htn a c hcard hc hne)

/-- The exact quadratic rank determines the actual radical cardinality. -/
theorem traceFamily_radical_natCard_of_exact_rank
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical = 2*t) :
    Nat.card (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical =
      (Fintype.card k)^(2*n-2*t) := by
  have hd : Module.finrank k B = 2*n := by
    apply (Nat.pow_right_injective (Fintype.one_lt_card (α:=k)))
    change (Fintype.card k)^(Module.finrank k B) = (Fintype.card k)^(2*n)
    rw [← Module.card_eq_pow_finrank (K:=k), hcard]
  have hle := Submodule.finrank_le (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical
  have he : Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical = 2*n-2*t := by
    omega
  rw [Module.natCard_eq_pow_finrank (K:=k), Nat.card_eq_fintype_card, he]

/-- The translated derivative has a full radical-sized zero set. -/
theorem translatedTracePolynomial_derivative_root_card_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical = 2*t) :
    (Finset.univ.filter (fun x : B =>
      (translatedTracePolynomial (k:=k) n t a c v).derivative.eval x=0)).card =
      (Fintype.card k)^(2*n-2*t) := by
  have he := translatedTracePolynomial_card_derivative_zero (k:=k) n t ht htn a c v
  rw [← traceFamily_radical_eq_derivative_ker_of_exact_rank p r hq n t ht htn a c hcard hc hne hrank,
    traceFamily_radical_natCard_of_exact_rank n t ht htn a c hcard hc hrank] at he
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using he

/-- Every derivative root has the exact prime-power multiplicity. -/
theorem translatedTracePolynomial_derivative_multiplicity_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical = 2*t)
    (x : B) (hx : (translatedTracePolynomial (k:=k) n t a c v).derivative.eval x=0) :
    rootMultiplicity x (translatedTracePolynomial (k:=k) n t a c v).derivative =
      (Fintype.card k)^t := by
  let G := translatedTracePolynomial (k:=k) n t a c v
  let S := Finset.univ.filter (fun x : B => G.derivative.eval x=0)
  have hG := translatedTracePolynomial_derivative_ne_zero (k:=k) n t ht htn a c v hne
  have hS : S.card = (Fintype.card k)^(2*n-2*t) :=
    translatedTracePolynomial_derivative_root_card_of_exact_rank p r hq n t ht htn a c v hcard hc hne hrank
  have hd : G.derivative.natDegree ≤ (Fintype.card k)^(2*n-t) := by
    dsimp [G, translatedTracePolynomial]
    simp only [derivative_comp,derivative_sub,derivative_X,derivative_C,sub_zero,
      one_mul,natDegree_comp,natDegree_X_sub_C,mul_one]
    exact traceFamily_derivative_natDegree_le n t ht htn a c
  have hh := primePower_root_multiplicity_of_full_card p (r*t) G.derivative hG S
    (by intro e he; simpa [pow_mul,←hq] using
          translatedTracePolynomial_derivative_support_dvd n t ht htn a c v hcard e he)
    (by intro y hy; exact (Finset.mem_filter.mp hy).2)
    (by
      rw [pow_mul,←hq,hS,←pow_add]
      convert hd using 1
      congr 1
      omega)
  have hm := hh.2.2 x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
  simpa [pow_mul,←hq] using hm

/-- A literal differential product determines multiplicity at every function root. -/
theorem rootMultiplicity_of_differential_product (G L J : B[X]) (q : ℕ)
    (hq : 2 ≤ q) (hL : L ≠ 0) (hJ : J ≠ 0)
    (hid : G^q-G=L*J) (x : B) (hx : G.eval x=0) :
    rootMultiplicity x G = rootMultiplicity x L + rootMultiplicity x J := by
  have hp : G*G^(q-1)=G^q := by
    rw [←pow_succ']; congr 1; omega
  have hf : G*(G^(q-1)-1)=L*J := by
    rw [mul_sub,hp,mul_one]; exact hid
  have hn : ¬(G^(q-1)-1).IsRoot x := by
    simp [IsRoot.def,hx,zero_pow (show q-1≠0 by omega)]
  have he := congrArg (rootMultiplicity x) hf
  rw [rootMultiplicity_mul (hf.symm ▸ mul_ne_zero hL hJ),
    rootMultiplicity_eq_zero hn,add_zero,rootMultiplicity_mul (mul_ne_zero hL hJ)] at he
  exact he

/-- The translated function has one additional multiplicity at each radical root. -/
theorem translatedTracePolynomial_multiplicity_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical = 2*t)
    (x : B) (hx : (translatedTracePolynomial (k:=k) n t a c v).derivative.eval x=0) :
    rootMultiplicity x (translatedTracePolynomial (k:=k) n t a c v) =
      (Fintype.card k)^t+1 := by
  let G := translatedTracePolynomial (k:=k) n t a c v
  let L := subspacePolynomial (⊤ : Submodule k B).toAddSubgroup
  have hL : L ≠ 0 := (subspacePolynomial_monic _).ne_zero
  have hC : -C ((L.coeff 1)⁻¹) ≠ 0 := by
    apply neg_ne_zero.mpr
    exact C_ne_zero.mpr (inv_ne_zero (subspacePolynomial_coeff_one_ne_zero _))
  have hzero : G.eval x=0 := by
    apply translatedTracePolynomial_zero_of_radical n t ht htn a c v x hcard hc
    rw [traceFamily_radical_eq_derivative_ker_of_exact_rank p r hq n t ht htn a c hcard hc hne hrank]
    exact (translatedTracePolynomial_derivative_zero_iff n t ht htn a c v x).mp hx
  have hm := rootMultiplicity_of_differential_product G (-C ((L.coeff 1)⁻¹)*L) G.derivative
    (Fintype.card k) (by exact Fintype.one_lt_card) (mul_ne_zero hC hL)
    (translatedTracePolynomial_derivative_ne_zero n t ht htn a c v hne)
    (translatedTracePolynomial_differential p r hr hq n t ht htn a c v hcard hc) x hzero
  have hsimple : rootMultiplicity x L=1 := by
    apply (roots_eq_and_simple_of_full_card L hL Finset.univ
      (by intro y hy; exact (subspacePolynomial_eval_eq_zero_iff _ y).mpr (by trivial))
      (by
        rw [subspacePolynomial_natDegree,Finset.card_univ]
        exact le_of_eq (Fintype.card_congr (Submodule.topEquiv (R:=k) (M:=B)).toEquiv))).2.2
    exact Finset.mem_univ _
  have hconst : rootMultiplicity x (-C ((L.coeff 1)⁻¹))=0 := by
    apply rootMultiplicity_eq_zero
    simp only [IsRoot.def,eval_neg,eval_C,neg_eq_zero]
    exact inv_ne_zero (subspacePolynomial_coeff_one_ne_zero _)
  rw [rootMultiplicity_mul (mul_ne_zero hC hL),hconst,zero_add,hsimple] at hm
  rw [translatedTracePolynomial_derivative_multiplicity_of_exact_rank p r hq n t ht htn a c v hcard hc hne hrank x hx] at hm
  simpa [Nat.add_comm] using hm

/-- Known roots and radical multiplicities force the smaller translated zero count. -/
theorem translatedTracePolynomial_zero_card_le_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical = 2*t) :
    (Finset.univ.filter (fun x : B => (translatedTracePolynomial (k:=k) n t a c v).eval x=0)).card ≤
      (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
  let G := translatedTracePolynomial (k:=k) n t a c v
  let S := Finset.univ.filter (fun x : B => G.eval x=0)
  let R := Finset.univ.filter (fun x : B => G.derivative.eval x=0)
  have hG : G ≠ 0 := by
    intro hz
    have hd := translatedTracePolynomial_derivative_ne_zero (k:=k) n t ht htn a c v hne
    apply hd
    change G.derivative=0
    rw [hz,derivative_zero]
  apply zero_card_le_of_radical_multiplicities (Fintype.card k) (2*n) t
    Fintype.one_lt_card ht (by omega) G hG S R
  · intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    apply translatedTracePolynomial_zero_of_radical n t ht htn a c v x hcard hc
    rw [traceFamily_radical_eq_derivative_ker_of_exact_rank p r hq n t ht htn a c hcard hc hne hrank]
    exact (translatedTracePolynomial_derivative_zero_iff n t ht htn a c v x).mp
      (Finset.mem_filter.mp hx).2
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx
    exact le_of_eq (translatedTracePolynomial_multiplicity_of_exact_rank p r hr hq n t ht htn a c v hcard hc hne hrank x
      (Finset.mem_filter.mp hx).2).symm
  · exact translatedTracePolynomial_derivative_root_card_of_exact_rank p r hq n t ht htn a c v hcard hc hne hrank
  · exact translatedTracePolynomial_natDegree_le n t ht htn a c v

/-- The actual scalar-valued quadratic form satisfies the smaller zero-count upper bound. -/
theorem traceFamilyQuadraticForm_zero_card_le_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B -
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical = 2*t) :
    (Finset.univ.filter (fun x : B => traceFamilyQuadraticForm n t ht htn a c hcard hc x=0)).card ≤
      (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
  have hh := translatedTracePolynomial_zero_card_le_of_exact_rank p r hr hq n t ht htn a c 0 hcard hc hne hrank
  have he : Finset.univ.filter (fun x : B => traceFamilyQuadraticForm n t ht htn a c hcard hc x=0) =
      Finset.univ.filter (fun x : B => (translatedTracePolynomial (k:=k) n t a c 0).eval x=0) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,translatedTracePolynomial_eval,sub_zero]
    rw [←algebraMap_traceFamilyQuadraticForm n t ht htn a c hcard hc]
    exact (map_eq_zero_iff (algebraMap k B) (FaithfulSMul.algebraMap_injective k B)).symm
  rw [he]
  exact hh

end BinaryFieldCounterexamples.QuadraticFormTrace
