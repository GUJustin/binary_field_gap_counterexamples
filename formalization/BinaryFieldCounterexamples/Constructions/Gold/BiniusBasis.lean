/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.SubspaceIncidence
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The subfield containing the Binius64 prefix domains

Section 5.7 fixes a binary basis with the Artin–Schreier recurrence. The
first 32 basis vectors span precisely the roots of `X^(2^32)-X`. The proof
uses the linear Artin–Schreier operator and polynomial root counting.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
set_option maxRecDepth 4096
open Polynomial

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Section 5.7: the Frobenius part of the binary Artin–Schreier operator. -/
noncomputable def binaryFrobeniusLinear : Module.End (ZMod 2) F :=
  (FiniteField.frobeniusAlgHom (ZMod 2) F).toLinearMap

/-- Section 5.7: the binary Artin–Schreier operator `A(x)=x²+x`. -/
noncomputable def binaryArtinSchreier : Module.End (ZMod 2) F :=
  binaryFrobeniusLinear + 1

omit [Fintype F] [CharP F 2] in
theorem binaryFrobeniusLinear_apply (x : F) :
    binaryFrobeniusLinear x = x ^ 2 := by
  simp [binaryFrobeniusLinear]

omit [Fintype F] [CharP F 2] in
theorem binaryArtinSchreier_apply (x : F) :
    binaryArtinSchreier x = x ^ 2 + x := by
  simp [binaryArtinSchreier, binaryFrobeniusLinear_apply]

omit [Fintype F] in
/-- Section 5.7: 32 successive Artin–Schreier applications give
`x^(2^32)+x`, as asserted in the subfield argument. -/
theorem binaryArtinSchreier_pow_thirtytwo (x : F) :
    (binaryArtinSchreier ^ 32) x = x ^ (2 ^ 32) + x := by
  have hpower : ∀ n : ℕ, (binaryFrobeniusLinear (F := F) ^ n) x = x ^ (2 ^ n) := by
    intro n
    rw [Module.End.pow_apply]
    change ((fun y : F => y ^ 2)^[n]) x = x ^ (2 ^ n)
    exact congr_fun (pow_iterate 2 n) x
  let : CharP (Module.End (ZMod 2) F) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
      ext y
      change (2 : ℕ) • y = 0
      rw [two_nsmul]
      exact CharTwo.add_self_eq_zero y)
  have h := add_pow_char_pow_of_commute 2 5
    (Commute.one_right (binaryFrobeniusLinear (F := F)))
  change (binaryFrobeniusLinear + 1 : Module.End (ZMod 2) F) ^ 32 =
    binaryFrobeniusLinear ^ 32 + 1 at h
  rw [binaryArtinSchreier, h]
  simp [hpower]

/-- Section 5.7: the prefix evaluation domain is the binary span of the
first `d` members of the specified Binius64 basis. -/
noncomputable def biniusPrefixDomain (β : Module.Basis (Fin 128) (ZMod 2) F)
    (d : ℕ) (hd : d ≤ 128) : Submodule (ZMod 2) F :=
  Submodule.span (ZMod 2) (Set.range fun i : Fin d => β ⟨i, lt_of_lt_of_le i.isLt hd⟩)

omit [Fintype F] in
theorem binius_basis_annihilated
    (β : Module.Basis (Fin 128) (ZMod 2) F) (hzero : β 0 = 1)
    (hrec : ∀ i : Fin 127, β i.castSucc = (β i.succ) ^ 2 + β i.succ)
    (i : ℕ) (hi : i < 128) :
    (binaryArtinSchreier ^ (i + 1)) (β ⟨i, hi⟩) = 0 := by
  induction i with
  | zero => simp [binaryArtinSchreier_apply, hzero, CharTwo.add_self_eq_zero]
  | succ i ih =>
    have he := hrec ⟨i, by omega⟩
    change β ⟨i, by omega⟩ = (β ⟨i + 1, hi⟩) ^ 2 + β ⟨i + 1, hi⟩ at he
    rw [pow_succ, Module.End.mul_apply, binaryArtinSchreier_apply, ← he]
    exact ih (by omega)

/-- Section 5.7: the Binius64 first-32-vector domain is exactly the
subfield defined by `x^(2^32)=x`, under the paper's basis recurrence. -/
theorem biniusPrefixDomain_thirtytwo_eq_fixed
    (β : Module.Basis (Fin 128) (ZMod 2) F) (hzero : β 0 = 1)
    (hrec : ∀ i : Fin 127, β i.castSucc = (β i.succ) ^ 2 + β i.succ) :
    ∀ x : F, x ∈ biniusPrefixDomain β 32 (by decide) ↔ x ^ (2 ^ 32) = x := by
  classical
  let V := biniusPrefixDomain β 32 (by decide)
  have hle : V ≤ LinearMap.ker (binaryArtinSchreier (F := F) ^ 32) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    change (binaryArtinSchreier ^ 32) (β ⟨i.val, by omega⟩) = 0
    have hann := binius_basis_annihilated β hzero hrec i.val (by omega)
    have he : 32 = (32 - (i.val + 1)) + (i.val + 1) := by omega
    have hp : (binaryArtinSchreier (F := F) ^ 32) =
        binaryArtinSchreier ^ (32 - (i.val + 1)) * binaryArtinSchreier ^ (i.val + 1) := by
      rw [← pow_add, ← he]
    rw [hp, Module.End.mul_apply, hann, map_zero]
  have hdim : Module.finrank (ZMod 2) V = 32 := by
    apply (finrank_span_eq_card (β.linearIndependent.comp
      (fun i : Fin 32 => (⟨i.val, by omega⟩ : Fin 128)) (by
        intro i j h; exact Fin.ext (congrArg (fun j : Fin 128 => j.val) h)))).trans
    exact Fintype.card_fin 32
  let S : Finset F := Finset.univ.filter (fun x => x ∈ V)
  have hcard : S.card = 2 ^ 32 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    simpa [S, Nat.card_eq_fintype_card, Fintype.card_subtype, hdim, ZMod.card] using hc
  let p : F[X] := X ^ (2 ^ 32) - X
  have hpn : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F (by norm_num)
  have hroots : p.roots = S.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      have hk := hle (Finset.mem_filter.mp hx).2
      rw [LinearMap.mem_ker, binaryArtinSchreier_pow_thirtytwo] at hk
      have hxpow : x ^ (2 ^ 32) = x := by
        exact (CharTwo.add_eq_zero).mp hk
      simp only [p, eval_sub, eval_pow, eval_X, hxpow, sub_self]
    · rw [hcard]
      exact le_of_eq (FiniteField.X_pow_card_sub_X_natDegree_eq F (by norm_num))
    · exact hpn
  intro x
  have hm := p.mem_roots hpn (a := x)
  rw [hroots] at hm
  simpa [S, V, p, Polynomial.IsRoot, sub_eq_zero] using hm

/-- Section 5.7: every Binius64 prefix domain of dimension at most 32
lies in the `2^32`-element subfield, using the actual basis recurrence. -/
theorem biniusPrefixDomain_le_fixed_thirtytwo
    (β : Module.Basis (Fin 128) (ZMod 2) F) (hzero : β 0 = 1)
    (hrec : ∀ i : Fin 127, β i.castSucc = (β i.succ) ^ 2 + β i.succ)
    (d : ℕ) (hd : d ≤ 32) (x : F) (hx : x ∈ biniusPrefixDomain β d (by omega)) :
    x ^ (2 ^ 32) = x := by
  apply (biniusPrefixDomain_thirtytwo_eq_fixed β hzero hrec x).mp
  apply (Submodule.span_mono ?_) hx
  rintro y ⟨i, rfl⟩
  exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hd⟩, rfl⟩


omit [CharP F 2] in
/-- Section 5.7: the paper's Binius64 prefix span has exactly `2^d` points,
so the fixed-point domain at `d=32` is the `2^32`-element subfield. -/
theorem biniusPrefixDomain_card (β : Module.Basis (Fin 128) (ZMod 2) F)
    (d : ℕ) (hd : d ≤ 128) : Nat.card (biniusPrefixDomain β d hd) = 2 ^ d := by
  have hdim : Module.finrank (ZMod 2) (biniusPrefixDomain β d hd) = d := by
    apply (finrank_span_eq_card (β.linearIndependent.comp
      (fun i : Fin d => (⟨i.val, lt_of_lt_of_le i.isLt hd⟩ : Fin 128)) (by
        intro i j h; exact Fin.ext (congrArg (fun j : Fin 128 => j.val) h)))).trans
    exact Fintype.card_fin d
  simpa [hdim, ZMod.card] using
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := biniusPrefixDomain β d hd))

/-- Section 5.7: using the whole 128-dimensional field in Theorem 5.1,
the positive-Delta guard is impossible for `d≤32` and `t≥2`. -/
theorem binius_fullfield_gold_guard_impossible (d t : ℕ) (hd : d ≤ 32) (ht : 2 ≤ t) :
    ¬ 1 ≤ 128 - t * (128 - d + if Even d then 1 else 0) := by
  have hf : 96 ≤ 128 - d + if Even d then 1 else 0 := by split <;> omega
  have hm := Nat.mul_le_mul ht hf
  omega

/-- Section 5.7's range observation for a domain lying in no proper subfield
of the 128-bit field: the Theorem 5.1 guard with `t ≥ 2` forces dimension
at least `65`, and hence cannot apply at any of the printed dimensions. -/
theorem binius_fullfield_gold_min_dimension (d t : ℕ) (ht : 2 ≤ t)
    (hΔ : 1 ≤ 128 - t * (128 - d + if Even d then 1 else 0)) :
    65 ≤ d := by
  by_contra h
  have hd : d ≤ 64 := by omega
  have hf : 65 ≤ 128 - d + if Even d then 1 else 0 := by
    split
    · omega
    · rename_i heven
      have hne : d ≠ 64 := by
        intro he
        subst d
        exact heven (by decide : Even 64)
      omega
  have hm := Nat.mul_le_mul ht hf
  omega

end BinaryFieldCounterexamples.Gold
