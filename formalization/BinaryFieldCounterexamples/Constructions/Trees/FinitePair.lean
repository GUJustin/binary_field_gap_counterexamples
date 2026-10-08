/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.SupportLocators
public import BinaryFieldCounterexamples.Constructions.SupportIncidenceAssembly
/-!
# Exact finite pair from the actual balanced tree family

Every literal support receives its proved locator. Distinct roots ensure distinct
polynomials, complementation supplies exact half incidence, and normalized pole
reduction gives one pair satisfying both count bounds and all guarantees on the inputs.
The population here is the actual finite family cardinality.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_pair_of_tree_support_family
    {V F : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (n d : ℕ) (hdim : Module.finrank (ZMod 2) V=d) (hd : n+3≤d)
    (hV : Fintype.card V=2^d)
    (f : V →ᵃ[ZMod 2] F) (hf : Function.Injective f) (hq : 2^d<Fintype.card F) :
    let D := Finset.univ.image f
    let T : ℕ := 2^(d-1)
    let K : ℕ := T-2^(d-(n+3))
    let M := (Trees.treeSupportFamily V n).card
    let E : ℚ := (K:ℚ)*M.choose 2-(2^d:ℚ)*(M/2).choose 2
    ∃ u v : D → F, commonAgreementEQ D K u v K ∧ agreementEQ D K v K ∧
      agreementLE D K u (T-1) ∧
      max (M-⌊E/(Fintype.card F-2^d)⌋₊)
        ⌈(Fintype.card F-2^d:ℚ)*M^2/((Fintype.card F-2^d)*M+2*E)⌉₊ ≤
        (nonzeroBadChallenges D K u v T).card := by
  classical
  let : LinearOrder (Finset V) := (Fintype.equivFin (Finset V)).linearOrder
  let I := Trees.treeSupportFamily V n
  let D := Finset.univ.image f
  let T : ℕ := 2^(d-1)
  let K : ℕ := T-2^(d-(n+3))
  have hloc (S : Finset V) (hS : S∈I) := exists_tree_support_locator n d hdim hd f hf S hS
  let P : Finset V → F[X] := fun S => if hS : S∈I then (hloc S hS).choose else 0
  have hP (S : Finset V) (hS : S∈I) :
      (P S).Monic ∧ (P S).natDegree=T ∧ (∀ x, (P S).eval x=0 ↔ x∈S.image f) ∧
      (P S-X^T).natDegree≤K := by
    simpa only [P,dite_eq_left hS,T,K] using (hloc S hS).choose_spec
  have hDc : D.card=2^d := by rw [Finset.card_image_of_injective _ hf,Finset.card_univ,hV]
  have hpow : 2^d=2*T := by
    dsimp [T]
    calc
      2^d=2^((d-1)+1) := by congr 1; omega
      _=2*2^(d-1) := by rw [pow_succ]; omega
  have hgap : 1≤2^(d-(n+3)) := Nat.one_le_pow _ _ (by decide)
  have hTpos : 0<T := pow_pos (by decide) _
  have hKT : K≤T-1 := by dsimp [K]; omega
  have hK : K≤D.card := by rw [hDc,hpow]; dsimp [K]; omega
  have hsubset (S : Finset V) (hS : S∈I) : S.image f⊆D :=
    Finset.image_subset_image (Finset.subset_univ _)
  have hsize (S : Finset V) (hS : S∈I) : T≤(S.image f).card := by
    rw [Finset.card_image_of_injective _ hf]
    have hs := Trees.treeSupportFamily_balanced n S hS
    rw [hV,hpow] at hs
    omega
  have hinj : Set.InjOn P I := by
    intro S hS U hU he
    apply (Finset.image_inj hf).mp
    ext x
    rw [←(hP S hS).2.2.1 x,←(hP U hU).2.2.1 x,he]
  have hdeg (S : Finset V) (hS : S∈I) : (P S-X^T).degree≤(K : WithBot ℕ) :=
    degree_le_of_natDegree_le (hP S hS).2.2.2
  have hinc (x : F) (hx : x∈D) : (I.filter (fun S => x∈S.image f)).card=I.card/2 := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    have he : I.filter (fun S => f y∈S.image f)=I.filter (fun S => y∈S) := by
      ext S
      simp only [Finset.mem_filter,Finset.mem_image]
      exact and_congr_right (fun _ => ⟨fun ⟨z,hz,he⟩ => hf he ▸ hz,fun hz => ⟨y,hz,rfl⟩⟩)
    rw [he]
    have hh := Trees.treeSupportFamily_point_incidence n y
    change 2*(I.filter (fun S => y∈S)).card=I.card at hh
    omega
  have henergy : (K:ℚ)*I.card.choose 2-
      ∑ x∈D, (((I.filter fun S => x∈S.image f).card).choose 2:ℚ)=
      (K:ℚ)*I.card.choose 2-(2^d:ℚ)*(I.card/2).choose 2 := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [hinc x hx])]
    simp [hDc]
  have h := exists_normalizedPolePair_of_support_incidence I D (fun S => S.image f) (X^T) P K T
    (by rwa [hDc]) hK (by simpa using hTpos) (by simpa using hKT)
    hsubset hsize (fun S hS => (hP S hS).2.2.1) hinj hdeg
  dsimp only at h
  rw [henergy] at h
  simpa only [natDegree_X_pow,hDc,Nat.cast_pow,Nat.cast_ofNat] using h
end BinaryFieldCounterexamples
