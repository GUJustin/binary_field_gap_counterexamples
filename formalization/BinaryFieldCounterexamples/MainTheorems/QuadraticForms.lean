/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianBinomial
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.FullfieldConstruction
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperplaneList

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.PrescribedSparseFamily
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.MappedDomainSource
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SparsePairAssembly
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.Numerics
public import BinaryFieldCounterexamples.Counting.QuadraticListCount

@[expose] public section

/-!
# Main theorem: Near-Johnson counterexamples from quadratic forms in every characteristic

## Manuscript statement and status

Paper statement: [Theorem 5.22, p. 53](../../../binary-field-counterexamples.pdf#page=53).
Public theorem: `BinaryFieldCounterexamples.quadratic_forms_near_johnson_sharp`.
The original `quadratic_forms_near_johnson` is a weaker compatibility corollary.
**Both clauses proved.** The received pair keeps the exact individual bounds,
common agreement and distinct nonzero challenge count.
The list proof includes the actual rank population, prescribed hyperplane
descent, strict degree, exact agreement, and distinct explaining-polynomial count.

Let `b` be a prime power, `m = 2 n`, and `B = GF(b^m)`. The evaluation domain
`D` is either all of `B` or an `GF(b)`-hyperplane. Write `d = dim_(GF(b)) D`,
`h = m - d ∈ {0,1}`, `N = b^d`, and choose `2 ≤ t ≤ n - h`. Put

`M = b^(2 t) (b^t - 1) [n - h choose t]_(b²)`,
`δ = (b - 1) N/b^(2 t)`, `K = N/b²`,
`T = N/b - (b - 1) N/b^(t+1)`, and `L = M/(b - 1)`.

There exists a word over `B` with at least `L` distinct degree-`< K`
explaining polynomials, each agreeing on exactly `T` coordinates. For every finite
extension `F/B` with `q = |F| > N`, there is one pair over `F` with

* `agr_K(g) = CA_K(f,g) = K`;
* `agr_K(f) ≤ (b + 1) N/(2 b²) - 1 < T`; and
* at least the maximum of `L - floor(δ choose(L,2)/(q-N))` and
  `ceil(L (q-N)/(q-N+δ (L-1)))` distinct nonzero exceptional challenges at
  agreement `T`. Both bounds hold for one pair.

The numerical expressions are rational until their integrality has been proved;
the first-input inequality is a rational bound on an integer. This matters in
odd characteristic. Agreement and common agreement follow the manuscript's
strict-degree conventions and will reuse ArkLib's shared interfaces.
-/

/-!
## Proof assembly: 1. Establish the rank distribution

Formalize the particular trace family of quadratic forms and its elliptic rank
distribution, corresponding to the cited Schmidt theorems in the paper.
Define the quadratic radical with the additional condition that the quadratic
form vanishes: in characteristic two, the polar radical alone is insufficient.
For the hyperplane case, prove the restriction count, rather than reusing a
full-field rank distribution without its codimension correction.
-/

/-!
## Proof assembly: 2. Recover explaining polynomials

Count affine shifts, quotient the scalar multiplicity `b - 1`, and prove the
resulting explaining polynomials are distinct. Establish the exact root count
`T`, the strict degree bound, and the common high-coefficient property needed
by pole reduction. A count of forms before this quotient is not a list size.
-/

/-!
## Proof assembly: 3. Pass from lists to one received line

Use the common pole-reduction and collision-pooling lemmas to obtain the displayed
collision bounds. After normalization, the strict first-input bound excludes
zero, so every challenge is kept.
Prove both the second-input equality and the bound for the first input of Lemma 3.13.
Keep the decoding-list alphabet `B` distinct from the input/challenge field `F`.
The dense all-rate corollary belongs downstream of this theorem and padding;
it must not be used as an assumption in this file's eventual proof.
-/

namespace BinaryFieldCounterexamples

open Polynomial

attribute [local instance] Classical.propDecidable Classical.decEq

/-- List-decoding clause of the every-characteristic finite theorem. A finite
scalar field `k` specifies the prime power, and the submodule cardinality
specifies full fields/hyperplanes. All explaining polynomials have exactly `T` agreements.
Together with `quadratic_forms_near_johnson`, this is the full theorem. Proved. -/
theorem quadratic_forms_list
    (k B : Type) [Field k] [Fintype k] [Field B] [Fintype B]
    [DecidableEq B] [Algebra k B]
    (n h t : ℕ) (hh : h ≤ 1) (ht : 2 ≤ t) (ht' : t ≤ n - h)
    (hB : Fintype.card B = Fintype.card k ^ (2 * n))
    (D : Submodule k B)
    (hD : (Finset.univ.filter (fun x : B => x ∈ D)).card =
      Fintype.card k ^ (2 * n - h)) :
    let b : ℕ := Fintype.card k
    let S := Finset.univ.filter (fun x : B => x ∈ D)
    let N : ℕ := S.card
    let K : ℕ := N / b ^ 2
    let T : ℕ := N / b - (b - 1) * N / b ^ (t + 1)
    let L : ℚ := (b : ℚ) ^ (2 * t) * ((b : ℚ) ^ t - 1) *
      quadraticGaussian (b ^ 2) (n - h) t / (b - 1)
    ∃ (w : S → B) (P : Finset B[X]),
      L ≤ P.card ∧ ∀ p ∈ P, p.degree < K ∧ agreementCount S w p = T := by
  -- The actual trace-code population and polynomial descent give both domains.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hh with rfl | rfl
  · simpa only [Nat.sub_zero] using
      QuadraticFormTrace.fullfield_submodule_list n t ht (by simpa using ht') hB D
        (by simpa only [Nat.sub_zero, ← hB] using hD)
  · exact QuadraticFormTrace.hyperplane_submodule_list n t ht ht' hB D hD


/-- The full finite quadratic-form theorem with both simultaneous collision bounds and no loss of a zero challenge. The rational parameter `L` is integral; its natural floor only exposes that integer to `Nat.choose`. -/
theorem quadratic_forms_near_johnson_sharp
    (k B F : Type) [Field k] [Fintype k] [Field B] [Fintype B]
    [DecidableEq B] [Algebra k B] [Field F] [Fintype F] [DecidableEq F]
    (φ : B →+* F)
    (n h t : ℕ) (hh : h ≤ 1) (ht : 2 ≤ t) (ht' : t ≤ n - h)
    (hB : Fintype.card B = Fintype.card k ^ (2 * n))
    (D : Submodule k B)
    (hD : (Finset.univ.filter (fun x : B => x ∈ D)).card =
      Fintype.card k ^ (2 * n - h))
    (hq : (Finset.univ.filter (fun x : B => x ∈ D)).card < Fintype.card F) :
    let b : ℕ := Fintype.card k
    let S := Finset.univ.filter (fun x : B => x ∈ D)
    let N : ℕ := S.card
    let K : ℕ := N / b ^ 2
    let T : ℕ := N / b - (b - 1) * N / b ^ (t + 1)
    let L : ℚ := (b : ℚ) ^ (2 * t) * ((b : ℚ) ^ t - 1) *
      quadraticGaussian (b ^ 2) (n - h) t / (b - 1)
    let δ : ℚ := (b - 1) * N / (b : ℚ) ^ (2 * t)
    let S' := mappedDomain φ S
    ∃ f g : S' → F,
      agreementEQ S' K g K ∧ commonAgreementEQ S' K f g K ∧
      agreementLE S' K f ⌊((b + 1 : ℚ) * N / (2 * b ^ 2) - 1)⌋₊ ∧
      ((b + 1 : ℚ) * N / (2 * b ^ 2) - 1) < T ∧
      max (⌊L⌋₊-⌊(δ*(⌊L⌋₊).choose 2)/(Fintype.card F-N:ℚ)⌋₊)
        ⌈L * (Fintype.card F - N : ℚ) /
        ((Fintype.card F - N : ℚ) + δ * (L - 1))⌉₊ ≤
        (nonzeroBadChallenges S' K f g T).card := by
  obtain ⟨p,hchar,r,hprime,hqk⟩ := FiniteField.card' k
  let : CharP k p := hchar
  let : CharP B p := charP_of_injective_algebraMap' k p
  let : CharP F p := charP_of_injective_ringHom φ.injective p
  let : Fact p.Prime := ⟨hprime⟩
  let b := Fintype.card k
  let S := Finset.univ.filter (fun x : B => x∈D)
  let N := S.card
  let d := 2*n-h
  let M := quadraticListCount b n h t
  have hb : 2≤b := Fintype.one_lt_card
  have hbpos : 0<b := by omega
  have hd : 3≤d := by dsimp [d]; omega
  have htd : 2*t≤d := by dsimp [d]; omega
  have hN : N=b^d := hD
  have hL := quadratic_list_size_eq_natCast b n h t hb ht'
  obtain ⟨E,hE,hprop⟩ := QuadraticFormTrace.prescribed_sparse_locator_family p r r.property hqk
    n h t hh ht ht' hB D hD
  have hM : M≤E.card := by
    rw [hL] at hE
    exact_mod_cast hE
  have hMpos : 0<M := quadraticListCount_pos b n h t hb (by omega) ht'
  have hsource := fun β hβ => agreementLE_mappedSubmoduleQuarterSource φ p r r.property hqk
    D d hd hD β hβ
  have hK : N/b^2=b^(d-2) := by rw [hN,Nat.pow_div (by omega) hbpos]
  have hNdiv : N/b=b^(d-1) := by
    rw [hN]
    simpa only [pow_one] using Nat.pow_div (show 1≤d by omega) hbpos
  have hTdiv : (b-1)*N/b^(t+1)=(b-1)*b^(d-t-1) := by
    rw [hN,Nat.mul_div_assoc _ (pow_dvd_pow b (by omega : t+1≤d)),Nat.pow_div (by omega) hbpos]
    congr 2
  have hdelta : (b-1:ℚ)*N/(b:ℚ)^(2*t)=((b-1)*b^(d-2*t):ℕ) := by
    have hp : (b:ℚ)^d=(b:ℚ)^(2*t)*(b:ℚ)^(d-2*t) := by
      rw [←pow_add]
      congr 1
      omega
    rw [hN,Nat.cast_pow,hp,Nat.cast_mul,Nat.cast_sub (by omega : 1≤b),Nat.cast_pow,Nat.cast_one]
    have hbnz : (b:ℚ)≠0 := by exact_mod_cast (by omega : b≠0)
    field_simp
  have hthreshold : b^(d-1)-(b-1)*b^(d-t-1) ≠ 0 := by
    have hlt : (b-1)*b^(d-t-1)<b*b^(d-t-1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    have hle : b*b^(d-t-1)≤b^(d-1) := by
      rw [←pow_succ']
      exact Nat.pow_le_pow_right hbpos (by omega)
    omega
  have hgap : ⌊((b+1:ℚ)*N/(2*b^2)-1)⌋₊ < b^(d-1)-(b-1)*b^(d-t-1) := by
    apply (Nat.floor_lt' hthreshold).mpr
    simpa only [hNdiv,hTdiv] using
      primePowerQuarterSource_lt_ellipticAgreement b d t N hb hd ht (by omega) hN
  obtain ⟨f,g,hg,hfg,hf,hcount⟩ := exists_mapped_polePair_of_sparse_locator_family_sharp φ p r
    r.property hqk D d t M ht htd hD hq E hM hMpos hprop _ (by simpa only [card_mappedDomain] using hgap) hsource
  dsimp only [N,S,b] at hK hNdiv hTdiv hdelta hL
  dsimp only [M,b] at hcount
  dsimp only
  refine ⟨f,g,?_,?_,?_,?_,?_⟩
  · simpa only [hK] using hg
  · simpa only [hK] using hfg
  · simpa only [card_mappedDomain,hK] using hf
  · exact primePowerQuarterSource_lt_ellipticAgreement b d t N hb hd ht (by omega) hN
  · simpa only [hK,hNdiv,hTdiv,hL,hdelta,card_mappedDomain,Nat.floor_natCast] using hcount


/-- Received-pair clause of the every-characteristic finite theorem, for every
finite extension with more elements than the domain. It keeps the exact
collision-energy bound and both individual/common-agreement conclusions. Together
with `quadratic_forms_list`, this is the full theorem. Proved. -/
theorem quadratic_forms_near_johnson
    (k B F : Type) [Field k] [Fintype k] [Field B] [Fintype B]
    [DecidableEq B] [Algebra k B] [Field F] [Fintype F] [DecidableEq F]
    (φ : B →+* F)
    (n h t : ℕ) (hh : h ≤ 1) (ht : 2 ≤ t) (ht' : t ≤ n - h)
    (hB : Fintype.card B = Fintype.card k ^ (2 * n))
    (D : Submodule k B)
    (hD : (Finset.univ.filter (fun x : B => x ∈ D)).card =
      Fintype.card k ^ (2 * n - h))
    (hq : (Finset.univ.filter (fun x : B => x ∈ D)).card < Fintype.card F) :
    let b : ℕ := Fintype.card k
    let S := Finset.univ.filter (fun x : B => x ∈ D)
    let N : ℕ := S.card
    let K : ℕ := N / b ^ 2
    let T : ℕ := N / b - (b - 1) * N / b ^ (t + 1)
    let L : ℚ := (b : ℚ) ^ (2 * t) * ((b : ℚ) ^ t - 1) *
      quadraticGaussian (b ^ 2) (n - h) t / (b - 1)
    let δ : ℚ := (b - 1) * N / (b : ℚ) ^ (2 * t)
    let S' := mappedDomain φ S
    ∃ f g : S' → F,
      agreementEQ S' K g K ∧ commonAgreementEQ S' K f g K ∧
      agreementLE S' K f ⌊((b + 1 : ℚ) * N / (2 * b ^ 2) - 1)⌋₊ ∧
      ((b + 1 : ℚ) * N / (2 * b ^ 2) - 1) < T ∧
      ⌈L * (Fintype.card F - N : ℚ) /
        ((Fintype.card F - N : ℚ) + δ * (L - 1))⌉₊ - 1 ≤
        (nonzeroBadChallenges S' K f g T).card := by
  obtain ⟨f,g,hg,hcommon,hf,hgap,hbad⟩ :=
    quadratic_forms_near_johnson_sharp k B F φ n h t hh ht ht' hB D hD hq
  exact ⟨f,g,hg,hcommon,hf,hgap,
    (Nat.sub_le _ _).trans ((le_max_right _ _).trans hbad)⟩

end BinaryFieldCounterexamples
