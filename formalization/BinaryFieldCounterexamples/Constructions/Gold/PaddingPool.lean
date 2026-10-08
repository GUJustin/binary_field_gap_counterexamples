/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingWitnesses
public import BinaryFieldCounterexamples.Constructions.Gold.Assembly
/-!
# Energy pooling with invariant agreement sets

The exact-size Gold locator family keeps its radical-invariant agreement sets
through collision pooling and deletion of the zero challenge. These concrete sets
are the input to simultaneous polynomial padding.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
/-- Exact energy pooling preserves the concrete radical-invariant Gold witnesses needed by padding. -/
theorem exists_gold_padding_pool
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] [Fintype (D.map φ.toAddMonoidHom)]
    (d t : ℕ) (hD : Nat.card D=2^d) (e : Module.Basis (Fin d) (ZMod 2) D)
    (ht0 : 2≤t) (ht : 2*t≤d) (hq : 2^d<Fintype.card F)
    (L : ℕ) (hL : L≤(momentTensors D (basisParameter D e) t).card*2^(2*t)) :
    let T := 2^d/2-2^d/2^(t+1)
    let δ : ℕ := 2^d/2^(2*t)
    let Zbound := ⌈(L:ℚ)*((Fintype.card F:ℚ)-(2^d:ℕ))/
      ((Fintype.card F:ℚ)-(2^d:ℕ)+(δ:ℚ)*((L:ℚ)-1))⌉₊-1
    ∃ β : F, β ∉ D.map φ.toAddMonoidHom ∧ ∃ Z : Finset F, Zbound≤Z.card ∧
      ∀ z ∈ Z, z≠0 ∧ ∃ p : F[X], p.degree<(T/2:ℕ) ∧
        ∃ H : Submodule (ZMod 2) D, Module.finrank (ZMod 2) H=d-2*t ∧
          ∃ S : Finset D, S.card=T ∧
            (∀ x : D, ∀ h : H, x+(h:D) ∈ S ↔ x ∈ S) ∧
            ∀ x : D,
              (binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval (φ (x:B))*(φ (x:B)-β)⁻¹+
                z*(φ (x:B)-β)⁻¹=p.eval (φ (x:B)) ↔ x ∈ S := by
  classical
  dsimp only
  have hd : d-1+1=d := by omega
  have hcD : Nat.card D=2^(d-1+1) := by simpa only [hd] using hD
  obtain ⟨allLocators,hallCard,hall⟩ := exists_repairedLocator_family D (d-1) hcD (basisParameter D e) e
    (basisParameter_eval D e) t ht0 (by omega)
  obtain ⟨ps,hsub,hcard⟩ := Finset.exists_subset_card_eq (show L≤allLocators.card by rw [hallCard]; exact hL)
  have hps := fun P (hP : P ∈ ps) => hall P (hsub hP)
  obtain ⟨β,hβ,hpool⟩ := exists_exterior_locatorValues_energy φ D (d-1) hcD (basisParameter D e) t ht0 (by omega)
    ps hps (by simpa only [hd] using hq)
  obtain ⟨Z,hZ,hdata⟩ := exists_gold_padding_witnesses φ D (d-1) hcD (basisParameter D e) t ht0 (by omega) ps hps β hβ
  refine ⟨β,hβ,Z,?_,?_⟩
  · apply le_trans (Nat.sub_le_sub_right ?_ 1) hZ
    have hδ : 2^d/2^(2*t)=2^(d-2*t) := Nat.pow_div ht (by decide)
    simpa only [hcard,hd,←hδ] using hpool
  · intro z hz
    obtain ⟨hne,p,hp,H,hH,S,hS,hinv,hmatch⟩ := hdata z hz
    have hN : 2^d/2=2^(d-1) := by
      change 2^d/2^1=2^(d-1)
      rw [Nat.pow_div (by omega : 1≤d) (by decide : 0<2)]
    have hT : 2^d/2^(t+1)=2^(d-1-t) := by
      rw [Nat.pow_div (by omega : t+1≤d) (by decide : 0<2)]
      congr 1
      omega
    have hhalf := gold_half_threshold (d-1) t ht0 (by omega)
    refine ⟨hne,p,?_,H,?_,S,?_,hinv,hmatch⟩
    · rw [hN,hT,hhalf]
      exact hp
    · rw [hd,Module.natCard_eq_pow_finrank (K := ZMod 2),
        show Nat.card (ZMod 2)=2 by rw [Nat.card_eq_fintype_card,ZMod.card]] at hH
      exact (Nat.pow_right_injective (by decide : 1<2)) hH
    · simpa only [hN,hT] using hS
/-- The full normalized Gold image satisfies both collision bounds and keeps every radical-invariant witness. -/
theorem exists_gold_padding_pool_sharp
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] [CharP F 2] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] [Fintype (D.map φ.toAddMonoidHom)]
    (d t : ℕ) (hD : Nat.card D=2^d) (e : Module.Basis (Fin d) (ZMod 2) D)
    (ht0 : 2≤t) (ht : 2*t≤d) (hq : 2^d<Fintype.card F)
    (L : ℕ) (hL : L≤(momentTensors D (basisParameter D e) t).card*2^(2*t)) :
    let T := 2^d/2-2^d/2^(t+1)
    let δ : ℕ := 2^d/2^(2*t)
    let Zbound := max (L-(δ*L.choose 2)/(Fintype.card F-2^d)) ⌈(L:ℚ)*((Fintype.card F:ℚ)-(2^d:ℕ))/
      ((Fintype.card F:ℚ)-(2^d:ℕ)+(δ:ℚ)*((L:ℚ)-1))⌉₊
    ∃ β : F, β ∉ D.map φ.toAddMonoidHom ∧ ∃ Z : Finset F, Zbound≤Z.card ∧
      ∀ z ∈ Z, z≠0 ∧ ∃ p : F[X], p.degree<(T/2:ℕ) ∧
        ∃ H : Submodule (ZMod 2) D, Module.finrank (ZMod 2) H=d-2*t ∧
          ∃ S : Finset D, S.card=T ∧
            (∀ x : D, ∀ h : H, x+(h:D) ∈ S ↔ x ∈ S) ∧
            ∀ x : D,
              (binaryQuarterNumerator (D.map φ.toAddMonoidHom) β).eval (φ (x:B))*(φ (x:B)-β)⁻¹+
                z*(φ (x:B)-β)⁻¹=p.eval (φ (x:B)) ↔ x ∈ S := by
  classical
  dsimp only
  have hd : d-1+1=d := by omega
  have hcD : Nat.card D=2^(d-1+1) := by simpa only [hd] using hD
  obtain ⟨allLocators,hallCard,hall⟩ := exists_repairedLocator_family D (d-1) hcD (basisParameter D e) e
    (basisParameter_eval D e) t ht0 (by omega)
  obtain ⟨ps,hsub,hcard⟩ := Finset.exists_subset_card_eq (show L≤allLocators.card by rw [hallCard]; exact hL)
  have hps := fun P (hP : P ∈ ps) => hall P (hsub hP)
  obtain ⟨β,hβ,hfirst,hsecond⟩ := exists_exterior_locatorValues_bounds φ D (d-1) hcD (basisParameter D e) t ht0 (by omega)
    ps hps (by simpa only [hd] using hq)
  obtain ⟨Z,hZ,hdata⟩ := exists_gold_padding_witnesses_no_loss φ D (d-1) hcD (basisParameter D e) t ht0 (by omega) ps hps β hβ
  refine ⟨β,hβ,Z,?_,?_⟩
  · apply le_trans (max_le ?_ ?_) hZ
    · have hδ : 2^d/2^(2*t)=2^(d-2*t) := Nat.pow_div ht (by decide)
      simpa only [hcard,hd,←hδ] using hfirst
    · have hδ : 2^d/2^(2*t)=2^(d-2*t) := Nat.pow_div ht (by decide)
      simpa only [hcard,hd,←hδ] using hsecond
  · intro z hz
    obtain ⟨hne,p,hp,H,hH,S,hS,hinv,hmatch⟩ := hdata z hz
    have hN : 2^d/2=2^(d-1) := by
      change 2^d/2^1=2^(d-1)
      rw [Nat.pow_div (by omega : 1≤d) (by decide : 0<2)]
    have hT : 2^d/2^(t+1)=2^(d-1-t) := by
      rw [Nat.pow_div (by omega : t+1≤d) (by decide : 0<2)]
      congr 1
      omega
    have hhalf := gold_half_threshold (d-1) t ht0 (by omega)
    refine ⟨hne,p,?_,H,?_,S,?_,hinv,hmatch⟩
    · rw [hN,hT,hhalf]
      exact hp
    · rw [hd,Module.natCard_eq_pow_finrank (K := ZMod 2),
        show Nat.card (ZMod 2)=2 by rw [Nat.card_eq_fintype_card,ZMod.card]] at hH
      exact (Nat.pow_right_injective (by decide : 1<2)) hH
    · simpa only [hN,hT] using hS
end BinaryFieldCounterexamples.Gold
