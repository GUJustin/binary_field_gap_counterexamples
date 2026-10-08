/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceDilation
/-!
# Actual radical incidence through prescribed nonzero vectors

Input dilation makes radical fibers equinumerous. Double counting literal
(form, nonzero radical vector) pairs then gives the exact incidence identity
for every rank layer of the actual trace family, without assuming its population.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Dilation closure gives equal actual radical-fiber counts at any two nonzero vectors. -/
theorem radical_fiber_card_eq_of_dilation (T : Finset (QuadraticForm k B))
    (hT : ∀ z : B,z≠0 → ∀ Q∈T,Q.comp (LinearMap.mulLeft k z)∈T)
    (v w : B) (hv : v≠0) (hw : w≠0) :
    (T.filter (fun Q => v∈Q.radical)).card=(T.filter (fun Q => w∈Q.radical)).card := by
  let z := v/w
  have hz : z≠0 := div_ne_zero hv hw
  have hzw : z*w=v := by dsimp [z]; field_simp
  have hzinv : z⁻¹*v=w := by rw [←hzw]; simp [hz]
  have hinverse (Q : QuadraticForm k B) :
      (Q.comp (LinearMap.mulLeft k z)).comp (LinearMap.mulLeft k z⁻¹)=Q := by
    ext x
    simp [QuadraticMap.comp_apply,hz]
  apply Finset.card_bij (fun Q _ => Q.comp (LinearMap.mulLeft k z))
  · intro Q hQ
    obtain ⟨hQT,hQv⟩ := Finset.mem_filter.mp hQ
    apply Finset.mem_filter.mpr
    refine ⟨hT z hz Q hQT,?_⟩
    rw [mem_radical_comp_mul Q z w hz,hzw]
    exact hQv
  · intro Q hQ R hR he
    have h := congrArg (fun Q : QuadraticForm k B => Q.comp (LinearMap.mulLeft k z⁻¹)) he
    simpa only [hinverse] using h
  · intro Q hQ
    obtain ⟨hQT,hQw⟩ := Finset.mem_filter.mp hQ
    refine ⟨Q.comp (LinearMap.mulLeft k z⁻¹),?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨hT z⁻¹ (inv_ne_zero hz) Q hQT,?_⟩
      rw [mem_radical_comp_mul Q z⁻¹ v (inv_ne_zero hz),hzinv]
      exact hQw
    · ext x
      simp [QuadraticMap.comp_apply,hz]

/-- Count actual form-vector pairs to compute a prescribed nonzero radical fiber. -/
theorem radical_fiber_count_of_dilation (T : Finset (QuadraticForm k B))
    (hT : ∀ z : B,z≠0 → ∀ Q∈T,Q.comp (LinearMap.mulLeft k z)∈T)
    (R : ℕ) (hR : ∀ Q∈T,Nat.card Q.radical=R) (v : B) (hv : v≠0) :
    (T.filter (fun Q => v∈Q.radical)).card*(Fintype.card B-1)=T.card*(R-1) := by
  let S := (Finset.univ : Finset B).erase 0
  have hdouble : (∑ x∈S,(T.filter (fun Q => x∈Q.radical)).card)=
      ∑ Q∈T,(S.filter (fun x => x∈Q.radical)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hleft : (∑ x∈S,(T.filter (fun Q => x∈Q.radical)).card)=
      (T.filter (fun Q => v∈Q.radical)).card*(Fintype.card B-1) := by
    have he (x : B) (hx : x∈S) : (T.filter (fun Q => x∈Q.radical)).card=
        (T.filter (fun Q => v∈Q.radical)).card :=
      radical_fiber_card_eq_of_dilation T hT x v (Finset.mem_erase.mp hx).1 hv
    rw [Finset.sum_congr rfl he]
    simp [S,Nat.mul_comm]
  have hright : (∑ Q∈T,(S.filter (fun x => x∈Q.radical)).card)=T.card*(R-1) := by
    have he (Q : QuadraticForm k B) (hQ : Q∈T) :
        (S.filter (fun x => x∈Q.radical)).card=R-1 := by
      have hs : S.filter (fun x => x∈Q.radical)=
          (Finset.univ.filter (fun x : B => x∈Q.radical)).erase 0 := by
        ext x
        simp [S]
      rw [hs,Finset.card_erase_of_mem (by simp)]
      have hr : (Finset.univ.filter (fun x : B => x∈Q.radical)).card=Nat.card Q.radical := by
        rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      rw [hr,hR Q hQ]
    rw [Finset.sum_congr rfl he]
    simp
  rw [hleft,hright] at hdouble
  exact hdouble

/-- The literal finite rank layer of the concrete trace family. -/
noncomputable def traceRankFamily (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (s : ℕ) : Finset (QuadraticForm k B) :=
  (traceQuadraticFamily n t ht htn hcard).filter
    (fun Q => Module.finrank k B-Module.finrank k Q.radical=s)

/-- Nonzero input dilation preserves the literal finite rank layer. -/
theorem traceRankFamily_dilate_mem (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (s : ℕ)
    (z : B) (hz : z≠0) (Q : QuadraticForm k B)
    (hQ : Q∈traceRankFamily n t ht htn hcard s) :
    Q.comp (LinearMap.mulLeft k z)∈traceRankFamily n t ht htn hcard s := by
  obtain ⟨hQ,hRank⟩ := Finset.mem_filter.mp hQ
  apply Finset.mem_filter.mpr
  refine ⟨?_,?_⟩
  · apply (mem_traceQuadraticCode_iff n t ht htn hcard _).mp
    apply traceQuadraticCode_comp_mul_mem n t ht htn hcard z Q
    exact (mem_traceQuadraticCode_iff n t ht htn hcard _).mpr hQ
  · rw [radical_finrank_comp_mul Q z hz]
    exact hRank

/-- The exact prescribed-vector radical incidence identity for the actual trace rank layer. -/
theorem traceRankFamily_radical_incidence (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (s : ℕ) (v : B) (hv : v≠0) :
    ((traceRankFamily n t ht htn hcard s).filter (fun Q => v∈Q.radical)).card*
      ((Fintype.card k)^(2*n)-1)=
      (traceRankFamily n t ht htn hcard s).card*((Fintype.card k)^(2*n-s)-1) := by
  rw [←hcard]
  apply radical_fiber_count_of_dilation (traceRankFamily n t ht htn hcard s)
    (fun z hz Q hQ => traceRankFamily_dilate_mem n t ht htn hcard s z hz Q hQ)
    ((Fintype.card k)^(2*n-s)) _ v hv
  intro Q hQ
  have hR := (Finset.mem_filter.mp hQ).2
  have hd := finrank_eq_of_card (k:=k) (2*n) hcard
  have hle := Submodule.finrank_le Q.radical
  have he : Module.finrank k Q.radical=2*n-s := by omega
  rw [Module.natCard_eq_pow_finrank (K:=k),Nat.card_eq_fintype_card,he]
end BinaryFieldCounterexamples.QuadraticFormTrace
