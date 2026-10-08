/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.PaddedPoleAssembly
public import BinaryFieldCounterexamples.Constructions.Trees.SupportLocators
public import BinaryFieldCounterexamples.Constructions.Trees.AvoidingSupports
/-!
# Finite pairs from actual avoiding tree supports

The literal constrained family keeps the existing tree locators and avoids
the prescribed padding subspace. After any injective affine embedding, nodal
padding and the exact incidence energy give one pair with both count bounds.
The population is the actual family cardinality, awaiting its recursive formula.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_pair_of_avoiding_tree_support_family
    {V F : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (n d : ℕ) (hdim : Module.finrank (ZMod 2) V=d) (hd : n+3≤d)
    (hV : Fintype.card V=2^d) (W : Submodule (ZMod 2) V)
    (hW : Nat.card W=2^(d-(n+3)))
    (e : V →ᵃ[ZMod 2] F) (he : Function.Injective e) (hq : 2^d<Fintype.card F) :
    let D := Finset.univ.image e
    let K : ℕ := 2^(d-1)
    let w : ℕ := 2^(d-(n+3))
    let M := (Trees.avoidingTreeSupportFamily n W).card
    let E : ℚ := (((K:ℚ)-w-(K:ℚ)^2/((2^d:ℚ)-w))*M^2+w*M)/2
    ∃ f g : D → F, commonAgreementEQ D K f g K ∧ agreementEQ D K g K ∧
      agreementLE D K f (K+w-1) ∧
      max (M-⌊E/(Fintype.card F-2^d)⌋₊)
        ⌈(Fintype.card F-2^d:ℚ)*M^2/((Fintype.card F-2^d)*M+2*E)⌉₊ ≤
        (nonzeroBadChallenges D K f g (K+w)).card := by
  classical
  let : LinearOrder (Finset V) := (Fintype.equivFin (Finset V)).linearOrder
  let I := Trees.avoidingTreeSupportFamily n W
  let D := Finset.univ.image e
  let Wf := (W : Set V).toFinset.image e
  let K : ℕ := 2^(d-1)
  let w : ℕ := 2^(d-(n+3))
  have hloc (S : Finset V) (hS : S∈I) := exists_tree_support_locator n d hdim hd e he S
    (Trees.avoidingTreeSupportFamily_subset n W hS)
  let P : Finset V → F[X] := fun S => if hS : S∈I then (hloc S hS).choose else 0
  have hP (S : Finset V) (hS : S∈I) :
      (∀ x, (P S).eval x=0 ↔ x∈S.image e) ∧ (P S-X^K).natDegree≤K-w := by
    have hp := (hloc S hS).choose_spec
    simpa only [P,dite_eq_left hS,K,w] using hp.2.2
  have hDc : D.card=2^d := by rw [Finset.card_image_of_injective _ he,Finset.card_univ,hV]
  have hWc : Wf.card=w := by
    rw [Finset.card_image_of_injective _ he,Set.toFinset_card]
    change _=2^(d-(n+3))
    rw [←hW,Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.refl _)
  have hWD : Wf⊆D := Finset.image_subset_image (Finset.subset_univ _)
  have hpow : 2^d=2*K := by
    dsimp [K]
    calc
      2^d=2^((d-1)+1) := by congr 1; omega
      _=2*2^(d-1) := by rw [pow_succ]; omega
  have hKpos : 0<K := pow_pos (by decide) _
  have hwpos : 0<w := pow_pos (by decide) _
  have hwK : w≤K := Nat.pow_le_pow_right (by decide) (by omega)
  have hA (S : Finset V) (hS : S∈I) : S.image e⊆D \ Wf := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩,?_⟩
    intro hw
    obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp hw
    have hzy : z=y := he heq
    subst z
    exact Trees.avoidingTreeSupportFamily_disjoint n W S hS y hy (Set.mem_toFinset.mp hz)
  have hsize (S : Finset V) (hS : S∈I) : (S.image e).card=K := by
    rw [Finset.card_image_of_injective _ he]
    have hs := Trees.avoidingTreeSupportFamily_balanced n W S hS
    rw [hV,hpow] at hs
    omega
  have hp := exists_padded_pole_pair I D Wf (fun S => S.image e) P K hWD
    (by rwa [hWc]) (by rw [hWc,hDc,hpow]; omega) (by rwa [hWc])
    (by rwa [hDc]) (by rw [hDc,hpow]; omega) hA hsize
    (Finset.image_injective he).injOn (fun S hS => (hP S hS).1)
    (fun S hS => by simpa only [hWc] using (hP S hS).2)
  dsimp only at hp ⊢
  simpa only [hWc,hDc,K,w,Nat.cast_pow,Nat.cast_ofNat] using hp
end BinaryFieldCounterexamples
