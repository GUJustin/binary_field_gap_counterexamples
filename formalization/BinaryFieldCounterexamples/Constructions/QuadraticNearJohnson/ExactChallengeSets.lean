/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.ClassificationProfile
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.ChallengeShift
public import BinaryFieldCounterexamples.Counting.BinaryCodimTwoExact
/-!
# Exact exceptional sets on the shifted quadratic received line

The actual subgroup classification and exact codimension-two population identify
one finite challenge set for every threshold above2K through4K−1. Translating the
first input translates that whole set injectively. Every challenge in it has
maximum agreement4K−1, and no challenge qualifies at4K.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open QuadraticConstruction
/-- One exact exceptional set works at every threshold above 2K through4K−1;
its members have exact maximum4K−1, and the next threshold has no exceptional challenges. -/
theorem quadratic_shifted_exact_challenges
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (θ : F) (hθ : θ∉Set.range φ)
    (D : AddSubgroup B) (K : ℕ) (hK : 2≤K)
    (hpow : ∃ k : ℕ, K=2^k) (hD : (additiveDomain D).card=16*K) (s : F) :
    let E := mappedDomain φ (additiveDomain D)
    let f : E → F := fun x=>firstWord K θ x+s*secondWord K (x:F)
    let g : E → F := fun x=>secondWord K (x:F)
    ∃ I : Finset F, I.card=(16*K-1)*(16*K-2)/6 ∧
      (∀ T : ℕ, 2*K+1≤T → T≤4*K-1 → badChallenges E K f g T=I) ∧
      (∀ z∈I, agreementEQ E K (fun x=>f x+z*g x) (4*K-1)) ∧
      badChallenges E K f g (4*K)=∅ := by
  classical
  let : Algebra (ZMod 2) B := ZMod.algebra B 2
  let E := mappedDomain φ (additiveDomain D)
  let f0 : E → F := fun x=>firstWord K θ x
  let g : E → F := fun x=>secondWord K (x:F)
  let f : E → F := fun x=>f0 x+s*g x
  have hcD : Nat.card D=16*K := by simpa [card_additiveDomain] using hD
  obtain ⟨hcard,hmem⟩ := codimTwoBinarySubspaces_exact_of_card_sixteen_mul D K (by omega) hcD
  let labels := (codimTwoBinarySubspaces D).image (finiteLocatorLabel φ θ K)
  have hlcard : labels.card=(16*K-1)*(16*K-2)/6 := by
    rw [Finset.card_image_of_injOn]
    · exact hcard
    · exact finiteLocatorLabel_injOn φ θ hθ D (codimTwoBinarySubspaces D) K hK hpow hcD
        (fun W hW=>(hmem W).mp hW |>.2) (fun W hW=>(hmem W).mp hW |>.1)
  have hlabels (T:ℕ) (hlo:2*K+1≤T) (hhi:T≤4*K-1) :
      badChallenges E K f0 g T=labels := by
    ext z
    rw [mem_badChallenges]
    change agreementGE E K (fun x=>firstWord K θ x+z*secondWord K (x:F)) T ↔ _
    rw [quadratic_combination_agreementGE_iff_subgroup φ θ hθ D K hK hpow hD z T hlo hhi]
    constructor
    · rintro ⟨W,hWD,hWc,rfl⟩
      exact Finset.mem_image.mpr ⟨W,(hmem W).mpr ⟨hWD,hWc⟩,rfl⟩
    · intro hz
      obtain ⟨W,hW,he⟩ := Finset.mem_image.mp hz
      exact ⟨W,((hmem W).mp hW).1,((hmem W).mp hW).2,he.symm⟩
  let I := labels.image (fun z=>z+s)
  have hI (T:ℕ) (hlo:2*K+1≤T) (hhi:T≤4*K-1) : badChallenges E K f g T=I := by
    rw [badChallenges_charTwo_shift,hlabels T hlo hhi]
  have hupper (z:F) : agreementLE E K (fun x=>f x+z*g x) (4*K-1) := by
    have hh := quadratic_combination_agreementLE φ θ hθ D K hK hpow hD (s+z)
    have he : (fun x:E=>f x+z*g x)=(fun x:E=>firstWord K θ x+(s+z)*secondWord K (x:F)) := by
      funext x
      dsimp [f,f0,g]
      ring
    rw [he]
    exact hh
  refine ⟨I,?_,hI,?_,?_⟩
  · exact (Finset.card_image_of_injective labels (fun _ _ h=>add_right_cancel h)).trans hlcard
  · intro z hz
    refine ⟨?_,hupper z⟩
    apply (mem_badChallenges E K f g (4*K-1) z).mp
    rwa [hI (4*K-1) (by omega) le_rfl]
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨p,hp,hcount⟩ := (mem_badChallenges E K f g (4*K) z).mp hz
    have hu := hupper z p hp
    omega
end BinaryFieldCounterexamples
