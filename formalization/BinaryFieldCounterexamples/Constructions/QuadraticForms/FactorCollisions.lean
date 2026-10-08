/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Polynomial.QuadraticLocatorConversion
public import BinaryFieldCounterexamples.Agreement.Basic
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalRoots

/-!
# Collision bounds from quadratic conversion factors

A collision of two nonvanishing converted locators makes their factors differ
by a `(b-1)`st root of unity. Uniform root bounds for those factor differences
therefore give the precise `(b-1)δ` collision budget.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticLocatorConversion
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proportional nonconstant conversion factors with `(b-1)`st-power-one
ratio determine the same converted locator. -/
theorem locator_eq_of_factor_eq_rootOfUnity_smul
    {F : Type*} [Field F] (p r b : ℕ) [ExpChar F p] (hb : b=p^r) (hb2 : 2≤b)
    (A B P Q L : F[X]) (ζ : F)
    (hA : A^(b-1)*(P^b-L)=P) (hB : B^(b-1)*(Q^b-L)=Q)
    (hζ : ζ^(b-1)=1) (hAB : A=C ζ*B) (hAdeg : 0<A.natDegree) : P=Q := by
  have hfactorpow : A^(b-1)=B^(b-1) := by
    rw [hAB,mul_pow,←C_pow,hζ,C_1,one_mul]
  have hdiff : A^(b-1)*(P-Q)^b=P-Q := by
    rw [hb]
    rw [sub_pow_expChar_pow]
    rw [←hb]
    have hB' : A^(b-1)*(Q^b-L)=Q := by rw [hfactorpow]; exact hB
    linear_combination hA-hB'
  by_contra hPQ
  have hA0 : A≠0 := fun hz => by rw [hz,natDegree_zero] at hAdeg; omega
  have hApow : A^(b-1)≠0 := pow_ne_zero _ hA0
  have hdiff0 : P-Q≠0 := sub_ne_zero.mpr hPQ
  have hpow0 : (P-Q)^b≠0 := pow_ne_zero _ hdiff0
  have hdegree := congrArg natDegree hdiff
  rw [natDegree_mul hApow hpow0,natDegree_pow,natDegree_pow] at hdegree
  have hbpos : 0<b-1 := by omega
  nlinarith

/-- Saturating the distinct-root bound by known domain roots shows that every
factor root lies in the domain locator. -/
theorem factor_isRoot_domain_of_saturated_roots
    {F : Type*} [Field F] (A L : F[X]) (S : Finset F) (δ : ℕ)
    (hA : A≠0) (hcard : S.card=δ)
    (hroot : ∀ x∈S,A.eval x=0)
    (hbound : A.roots.toFinset.card≤δ)
    (hdomain : ∀ x∈S,L.IsRoot x) :
    ∀ x,A.IsRoot x → L.IsRoot x := by
  have hsub : S⊆A.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((mem_roots hA).mpr (hroot x hx))
  have heq : S=A.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hbound)
  intro x hx
  apply hdomain x
  rw [heq]
  exact Multiset.mem_toFinset.mpr ((mem_roots hA).mpr hx)

/-- The conversion identity alone excludes exterior locator roots once all
factor roots lie in the domain locator. -/
theorem converted_eval_ne_zero_of_factor_roots
    {F : Type*} [Field F] (A P L : F[X]) (b : ℕ) (hb : 2≤b)
    (hconversion : A^(b-1)*(P^b-L)=P)
    (hAroots : ∀ x,A.IsRoot x → L.IsRoot x)
    (x : F) (houtside : L.eval x≠0) : P.eval x≠0 := by
  intro hP
  have he := congrArg (fun Q : F[X] => Q.eval x) hconversion
  simp only [eval_mul,eval_pow,eval_sub,hP,zero_pow (show b≠0 by omega)] at he
  have hAeval : A.eval x=0 := by
    by_contra hA
    have hp : (A.eval x)^(b-1)≠0 := pow_ne_zero _ hA
    have hz := (mul_eq_zero.mp he).resolve_left hp
    exact houtside (by simpa using hz)
  exact houtside (hAroots x hAeval)

/-- Divisible support of two factors gives the required distinct-root bound
for every scalar factor difference. -/
theorem factor_difference_roots_card_le
    {F : Type*} [Field F] [Fintype F]
    (p r s δ : ℕ) [Fact p.Prime] [CharP F p]
    (A B : F[X]) (ζ : F)
    (hA : ∀ e∈A.support,p^(r*s)∣e)
    (hB : ∀ e∈B.support,p^(r*s)∣e)
    (hne : A-C ζ*B≠0)
    (hdeg : (A-C ζ*B).natDegree≤p^(r*s)*δ) :
    (A-C ζ*B).roots.toFinset.card≤δ := by
  apply card_roots_le_of_primePower_support p (r*s) (A-C ζ*B) hne
  · intro e he
    rw [mem_support_iff,coeff_sub,coeff_C_mul] at he
    by_cases ha : A.coeff e=0
    · apply hB e
      rw [mem_support_iff]
      intro hb
      exact he (by rw [ha,hb,mul_zero,sub_zero])
    · exact hA e (mem_support_iff.mpr ha)
  · exact hdeg

/-- Conversion-factor differences bound collisions of two nonvanishing locators.
The trace specialization supplies `hsmall` by extracting a Frobenius root from
each scalar factor difference. -/
theorem card_locator_collision_le_of_factor_differences
    {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (A B P Q L : F[X]) (b δ : ℕ) (hb : 2≤b)
    (hP : A^(b-1)*(P^b-L)=P) (hQ : B^(b-1)*(Q^b-L)=Q)
    (hnonzero : ∀ x∉D,P.eval x≠0)
    (hsmall : ∀ ζ : F,ζ^(b-1)=1 → A-C ζ*B≠0 ∧
      (A-C ζ*B).roots.toFinset.card≤δ) :
    ((Finset.univ\D).filter fun x => P.eval x=Q.eval x).card≤(b-1)*δ := by
  let Z := Finset.univ.filter (fun ζ : F => ζ^(b-1)=1)
  have hZ : Z.card≤b-1 := by
    let H : F[X] := X^(b-1)-C 1
    have hH : H≠0 := by
      have hd : H.natDegree=b-1 := by
        dsimp [H]
        exact (natDegree_X_pow_sub_C :
          (X^(b-1)-(C 1:F[X])).natDegree=b-1)
      intro hz
      rw [hz,natDegree_zero] at hd
      omega
    apply (Finset.card_le_card (show Z⊆H.roots.toFinset from ?_)).trans
      ((Multiset.toFinset_card_le _).trans ((card_roots' H).trans_eq (by
        dsimp [H]
        exact (natDegree_X_pow_sub_C :
          (X^(b-1)-(C 1:F[X])).natDegree=b-1))))
    intro ζ hζ
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hH).mpr
    simpa [H] using sub_eq_zero.mpr (Finset.mem_filter.mp hζ).2
  have hsub : ((Finset.univ\D).filter fun x => P.eval x=Q.eval x)⊆
      Z.biUnion (fun ζ => Finset.univ.filter fun x => (A-C ζ*B).eval x=0) := by
    intro x hx
    obtain ⟨hxext,hcollision⟩ := Finset.mem_filter.mp hx
    have hxD := (Finset.mem_sdiff.mp hxext).2
    obtain ⟨ζ,hζ,hfactor⟩ := factor_eval_scalar_of_collision A B P Q L b hb x
      hP hQ hcollision (hnonzero x hxD)
    apply Finset.mem_biUnion.mpr
    refine ⟨ζ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hζ⟩,?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [eval_sub,eval_mul,eval_C]
    exact sub_eq_zero.mpr hfactor
  calc
    _≤(Z.biUnion (fun ζ => Finset.univ.filter fun x => (A-C ζ*B).eval x=0)).card :=
      Finset.card_le_card hsub
    _≤∑ ζ∈Z,(Finset.univ.filter fun x => (A-C ζ*B).eval x=0).card :=
      Finset.card_biUnion_le
    _≤∑ _ζ∈Z,δ := by
      apply Finset.sum_le_sum
      intro ζ hζ
      obtain ⟨hne,hroots⟩ := hsmall ζ (Finset.mem_filter.mp hζ).2
      apply (Finset.card_le_card (show (Finset.univ.filter fun x =>
        (A-C ζ*B).eval x=0)⊆(A-C ζ*B).roots.toFinset from ?_)).trans hroots
      intro x hx
      exact Multiset.mem_toFinset.mpr ((mem_roots hne).mpr (Finset.mem_filter.mp hx).2)
    _=Z.card*δ := by simp
    _≤(b-1)*δ := Nat.mul_le_mul_right δ hZ

end BinaryFieldCounterexamples.QuadraticLocatorConversion
