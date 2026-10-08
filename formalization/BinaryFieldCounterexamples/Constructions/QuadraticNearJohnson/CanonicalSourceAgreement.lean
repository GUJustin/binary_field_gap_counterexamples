/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.Witnesses
public import BinaryFieldCounterexamples.Counting.BinarySubspaces
public import BinaryFieldCounterexamples.Agreement.Domains
/-!
# Common agreement of the canonical quadratic pair

A binary subgroup of size 2K gives simultaneous strict-degree explaining
polynomials at its nonzero points. The monomial second input bounds all agreements by2K−1.
The same pair therefore has exact common and second-input agreement for any
extension-field coefficient and shift, as needed by both exact companions.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial QuadraticConstruction

/-- The canonical pair has exact common and second-input agreement for every
extension-field shift; no exterior-coordinate hypothesis is required. -/
theorem canonical_quadratic_source_agreement
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 16*K)
    (θ s : F) :
    let E := mappedDomain φ (additiveDomain D)
    let f : E → F := fun x ↦ firstWord K θ x + s * secondWord K (x : F)
    let g : E → F := fun x ↦ secondWord K (x : F)
    commonAgreementEQ E K f g (2*K-1) ∧ agreementEQ E K g (2*K-1) := by
  classical
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  let E := mappedDomain φ (additiveDomain D)
  let f : E → F := fun x ↦ firstWord K θ x + s * secondWord K (x : F)
  let g : E → F := fun x ↦ secondWord K (x : F)
  have hg : agreementLE E K g (2*K-1) := by
    have hdeg : (K : WithBot ℕ) ≤ (X ^ (2*K-1) : F[X]).degree := by
      rw [degree_X_pow]
      exact_mod_cast (show K ≤ 2*K-1 by omega)
    simpa [g, secondWord] using agreementLE_polynomial E K (X ^ (2*K-1) : F[X]) hdeg
  have hcD : Nat.card D = 16*K := by simpa [card_additiveDomain] using hD
  have hpow2 : ∃ m : ℕ, 2*K = 2^m := by
    obtain ⟨k, hk⟩ := hpow
    exact ⟨k+1, by rw [pow_succ, hk]; omega⟩
  obtain ⟨U, hUD, hUc⟩ := exists_binary_subspace_card_eq D (2*K) hpow2 (by omega)
  let UF := U.map φ.toAddMonoidHom
  have hUFc : Nat.card UF = 2*K :=
    (AddSubgroup.card_map_of_injective φ.injective).trans hUc
  have hUFE : ∀ x ∈ UF, x ∈ E := by
    rintro x ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, (mem_additiveDomain D y).mpr (hUD hy), rfl⟩
  have hcommon : commonAgreementGE E K f g (2*K-1) :=
    commonAgreementGE_of_subgroup E UF hUFE K hpow hUFc θ s
  exact ⟨⟨hcommon, commonAgreementLE_of_right E K f g _ hg⟩,
    ⟨agreementGE_right_of_common E K f g _ hcommon, hg⟩⟩
end BinaryFieldCounterexamples
