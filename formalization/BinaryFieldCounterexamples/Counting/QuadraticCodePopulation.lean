/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.QuadraticLiteralMoments
public import BinaryFieldCounterexamples.Counting.QuadraticSingleMomentPopulation

/-!
# Minimum-rank population in an additive quadratic code

The actual symmetric-matrix Fourier moment, together with the complementary
Gaussian cutoff, forces the Schmidt lower bound on the exact minimum-rank
layer of any additive quadratic code with the prescribed size and distance.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticCoordinates
open scoped BigOperators
open QuadraticGeometry
set_option warn.classDefReducibility false
attribute [local instance] Classical.decEq Classical.propDecidable upperIndexFintype

/-- A finite additive quadratic code of dimension `2n`, cardinality
`q^((2n+1)(n-t)+t)`, and minimum quadratic rank `2t` contains at least the
Schmidt lower bound of exact minimum-rank forms. -/
theorem quadraticCode_minimumRank_population_lower
    {k : Type*} [Field k] [Fintype k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n t : ℕ) (ht0 : 0<t) (htn : t≤n)
    (C : AddSubgroup (QuadraticForm k (Fin (2*n)→k))) [Fintype C]
    (hcard : Fintype.card C=(Fintype.card k)^((2*n+1)*(n-t))*(Fintype.card k)^t)
    (hmin : ∀ Q : C, Q≠0 → 2*t ≤ Module.finrank k ((Fin (2*n)→k) ⧸ Q.val.radical)) :
    ((Fintype.card k)^t-1)*gaussianPascal ((Fintype.card k)^2) n t ≤
      (Finset.univ.filter (fun Q : C =>
        Module.finrank k ((Fin (2*n)→k) ⧸ Q.val.radical)=2*t)).card := by
  let psi : AddChar k ℂ := AddChar.FiniteField.primitiveChar_to_Complex k
  let rank : C→ℕ := fun Q => Module.finrank k ((Fin (2*n)→k) ⧸ Q.val.radical)
  let q := Fintype.card k
  let j := n-t
  let H : ℝ := q^((2*n+1)*j)
  let G : ℝ := gaussianPascal (q^2) n t
  let X : ℝ := exactRankPopulation rank (2*t)
  have hpsi : psi≠1 := primitiveComplexChar_ne_one k
  have hweight (r : ℕ) : 0≤quadraticMinusRankWeight q n t r := by
    unfold quadraticMinusRankWeight
    positivity
  have hlower := quadratic_code_rank_kernel_lower (k:=k) (2*n) C psi
    (quadraticMinusRankWeight q n t) hweight
  have hw0 : quadraticMinusRankWeight q n t 0=(gaussianPascal (q^2) n t:ℚ) := by
    simp [quadraticMinusRankWeight]
  rw [hw0] at hlower
  have heval (Q : C) : Complex.reCLM
      (∑ M : symmetricMatrices (k:=k) (2*n),
        (quadraticMinusRankWeight q n t M.val.rank : ℂ) *
          psi (matrixPairing (2*n) Q.val M)) =
        H*(gaussianPascal (q^2) (n-(rank Q+1)/2) j : ℝ) := by
    rw [quadraticMinusRankWeight_characterSum_eq_weightedKernel n t htn psi hpsi Q.val]
    rw [actual_weightedKernelA p n j Q.val (by simp) (by dsimp [j]; omega)]
    change (((q:ℚ)^((2*n+1)*j)*
      (gaussianPascal (q^2) (n-(rank Q+1)/2) j:ℚ):ℚ):ℂ).re = _
    dsimp [H,q,rank,j]
    norm_num
  have hsum :
      (∑ Q : C, ∑ M : symmetricMatrices (k:=k) (2*n),
        (quadraticMinusRankWeight q n t M.val.rank : ℂ) *
          psi (matrixPairing (2*n) Q.val M)).re =
        H*(G+X) := by
    change Complex.reCLM (∑ Q : C, ∑ M : symmetricMatrices (k:=k) (2*n),
      (quadraticMinusRankWeight q n t M.val.rank : ℂ) *
        psi (matrixPairing (2*n) Q.val M)) = _
    rw [map_sum]
    simp_rw [heval]
    have hr0 : rank 0=0 := by
      dsimp [rank]
      rw [radical_quotient_finrank]
      have hp : (0 : QuadraticForm k (Fin (2*n)→k)).polarBilin=0 := by
        ext x y
        change (0 : k) - 0 - 0 = 0
        simp
      have hrad : (0 : QuadraticForm k (Fin (2*n)→k)).radical=⊤ := by
        ext x
        simp [QuadraticMap.radical,hp]
      rw [hrad,finrank_top]
      simp
    have hrmax (Q : C) : rank Q≤2*n := by
      dsimp [rank]
      rw [radical_quotient_finrank]
      simp
    have hc := gaussianCeilRankSum_collapse q n t rank Fintype.one_lt_card ht0 htn
      hr0 hmin hrmax
    have hcR : (∑ x : C,
        (gaussianPascal (q^2) (n-(rank x+1)/2) (n-t):ℝ)) =
        (gaussianPascal (q^2) n t:ℝ)+exactRankPopulation rank (2*t) := by
      exact_mod_cast hc
    change (∑ x : C, H*(gaussianPascal (q^2) (n-(rank x+1)/2) (n-t):ℝ)) =
      H*((gaussianPascal (q^2) n t:ℝ)+exactRankPopulation rank (2*t))
    rw [← Finset.mul_sum, hcR]
  rw [hsum] at hlower
  have hM : (Fintype.card C:ℝ)=H*(q^t:ℕ) := by
    rw [hcard]
    dsimp [H,j,q]
    push_cast
    rw [← pow_add]
  have hpop := minimumPopulation_lower_of_single_moment q t G H (Fintype.card C) X
    (by dsimp [H,q]; positivity) hM (by simpa [G] using hlower)
  dsimp [G,X,rank,q] at hpop ⊢
  have hqt : 1≤(Fintype.card k)^t := Nat.one_le_pow t _ Fintype.card_pos
  have hnatcast :
      ((((Fintype.card k)^t-1)*gaussianPascal ((Fintype.card k)^2) n t:ℕ):ℝ) ≤
        (exactRankPopulation (fun Q : C =>
          Module.finrank k ((Fin (2*n)→k) ⧸ Q.val.radical)) (2*t):ℝ) := by
    rw [Nat.cast_mul,Nat.cast_sub hqt]
    simpa only [Nat.cast_one] using hpop
  exact_mod_cast hnatcast

end BinaryFieldCounterexamples.QuadraticCoordinates
