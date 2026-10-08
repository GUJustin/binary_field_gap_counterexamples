/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Trees.BinaryFrames
public import BinaryFieldCounterexamples.Constructions.Trees.SurjectiveLinearCount
/-!
# Exact constrained binary frame counts

Three independent functionals satisfy the zero-restriction condition precisely
in four disjoint forms: an inside triple, or an inside pair with an exterior
vector in one of three arrangements. The literal parameter bijection gives
the exact raw-frame population for the height-two avoiding construction.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Trees
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- Actual independent triples satisfying the three possible zero-restriction patterns. -/
def ConstrainedFrames (U : Submodule (ZMod 2) V) :=
  {s : Fin 3 → V // LinearIndependent (ZMod 2) s ∧
    ((s 0 ∈ U ∧ s 2 ∈ U) ∨ (s 1 ∈ U ∧ s 2 ∈ U) ∨
      (s 0+s 1 ∈ U ∧ s 0+s 2 ∈ U))}
/-- Literal frame parameters: a triple inside, or a pair inside and an exterior vector. -/
def ConstrainedFrameData (U : Submodule (ZMod 2) V) :=
  {s : Fin 3 → U // LinearIndependent (ZMod 2) s} ⊕
    (Fin 3 × {s : Fin 2 → U // LinearIndependent (ZMod 2) s} × {b : V // b ∉ U})
/-- Binary module elements cancel with themselves. -/
theorem binary_module_add_self (x : V) : x+x=0 := by
  have h : (2 : ZMod 2) • x=0 := by rw [show (2 : ZMod 2)=0 by decide,zero_smul]
  simpa only [two_smul] using h
/-- Three concrete arrangements of the independent inside pair and exterior vector. -/
def exteriorTriple (i : Fin 3) (u v b : V) : Fin 3 → V :=
  if i=0 then ![u,b,v] else if i=1 then ![b,u,v] else ![b,b+u,b+v]
/-- Every such arrangement is independent. -/
theorem exteriorTriple_independent (U : Submodule (ZMod 2) V) (u v : U)
    (h : LinearIndependent (ZMod 2) ![u,v]) (b : V) (hb : b ∉ U) (i : Fin 3) :
    LinearIndependent (ZMod 2) (exteriorTriple i (u:V) (v:V) b) := by
  have hp : LinearIndependent (ZMod 2) ![(u:V),(v:V)] := by
    have hh := h.map' U.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have he : (U.subtype ∘ ![u,v]) = ![(u:V),(v:V)] := by ext i; fin_cases i <;> rfl
    rw [he] at hh
    exact hh
  have ht := (triple_independent_outside U b (u:V) (v:V) hb u.property v.property).mpr hp
  fin_cases i
  · change LinearIndependent (ZMod 2) ![(u:V),b,(v:V)]
    have he : ![(u:V),b,(v:V)] = ![b,(u:V),(v:V)] ∘ Equiv.swap (0:Fin 3) 1 := by
      ext j; fin_cases j <;> rfl
    rw [he]
    exact ht.comp (Equiv.swap (0:Fin 3) 1) (Equiv.injective _)
  · exact ht
  · exact (binary_triple_shear_independent_iff b (u:V) (v:V)).mpr ht
/-- Every arrangement satisfies the actual restriction pattern. -/
theorem exteriorTriple_condition (U : Submodule (ZMod 2) V) (u v : U) (b : V) (i : Fin 3) :
    let s := exteriorTriple i (u:V) (v:V) b
    (s 0 ∈ U ∧ s 2 ∈ U) ∨ (s 1 ∈ U ∧ s 2 ∈ U) ∨
      (s 0+s 1 ∈ U ∧ s 0+s 2 ∈ U) := by
  fin_cases i
  · exact Or.inl ⟨u.property,v.property⟩
  · exact Or.inr (Or.inl ⟨u.property,v.property⟩)
  · exact Or.inr (Or.inr ⟨by simp [exteriorTriple,←add_assoc,binary_module_add_self],
      by simp [exteriorTriple,←add_assoc,binary_module_add_self]⟩)
/-- The parameterization sends literal inside frames to actual constrained frames. -/
def constrainedFrameOfData (U : Submodule (ZMod 2) V) : ConstrainedFrameData U → ConstrainedFrames U
  | Sum.inl s => ⟨fun i => (s.1 i : V),
      s.2.map' U.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective),
      Or.inl ⟨(s.1 0).property,(s.1 2).property⟩⟩
  | Sum.inr ⟨i,s,b⟩ => ⟨exteriorTriple i (s.1 0:V) (s.1 1:V) b.1, by
      have he : ![s.1 0,s.1 1]=s.1 := by ext j; fin_cases j <;> rfl
      exact ⟨exteriorTriple_independent U _ _ (he.symm ▸ s.2) b.1 b.2 i,
        exteriorTriple_condition U _ _ b.1 i⟩⟩
/-- Membership of the first coordinate recovers the first arrangement. -/
theorem exteriorTriple_zero_mem_iff (U : Submodule (ZMod 2) V) (u v : U)
    (b : V) (hb : b ∉ U) (i : Fin 3) :
    exteriorTriple i (u:V) (v:V) b 0 ∈ U ↔ i=0 := by
  fin_cases i <;> simp [exteriorTriple,hb,u.property]
/-- Membership of the second coordinate recovers the second arrangement. -/
theorem exteriorTriple_one_mem_iff (U : Submodule (ZMod 2) V) (u v : U)
    (b : V) (hb : b ∉ U) (i : Fin 3) :
    exteriorTriple i (u:V) (v:V) b 1 ∈ U ↔ i=1 := by
  have hbu : b+(u:V) ∉ U := by
    rw [U.add_mem_iff_left u.property]
    exact hb
  fin_cases i <;> simp [exteriorTriple,hb,u.property,hbu]
/-- The three arrangements retain their index, exterior vector, and inside pair. -/
theorem exteriorTriple_injective (U : Submodule (ZMod 2) V) :
    Function.Injective (fun p : Fin 3 × U × U × {b : V // b ∉ U} =>
      exteriorTriple p.1 (p.2.1:V) (p.2.2.1:V) p.2.2.2.1) := by
  rintro ⟨i,u,v,b⟩ ⟨j,u',v',b'⟩ h
  have h0 := congrArg (fun s : Fin 3 → V => s 0 ∈ U) h
  have h1 := congrArg (fun s : Fin 3 → V => s 1 ∈ U) h
  have hi : i=j := by
    have hz : (i=0 ↔ j=0) := by
      rw [←exteriorTriple_zero_mem_iff U u v b.1 b.2 i,
        ←exteriorTriple_zero_mem_iff U u' v' b'.1 b'.2 j]
      exact iff_of_eq h0
    have ho : (i=1 ↔ j=1) := by
      rw [←exteriorTriple_one_mem_iff U u v b.1 b.2 i,
        ←exteriorTriple_one_mem_iff U u' v' b'.1 b'.2 j]
      exact iff_of_eq h1
    fin_cases i <;> fin_cases j <;> simp_all
  subst j
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  fin_cases i <;> simp only [exteriorTriple] at e0 e1 e2
  · have hu : u=u' := Subtype.ext e0
    have hb : b=b' := Subtype.ext e1
    have hv : v=v' := Subtype.ext e2
    subst_vars; rfl
  · have hb : b=b' := Subtype.ext e0
    have hu : u=u' := Subtype.ext e1
    have hv : v=v' := Subtype.ext e2
    subst_vars; rfl
  · have hb : b=b' := Subtype.ext e0
    subst b'
    have hu : u=u' := Subtype.ext (add_left_cancel e1)
    have hv : v=v' := Subtype.ext (add_left_cancel e2)
    subst_vars; rfl
/-- No two literal frame parameters encode the same constrained frame. -/
theorem constrainedFrameOfData_injective (U : Submodule (ZMod 2) V) :
    Function.Injective (constrainedFrameOfData U) := by
  intro p q h
  have he := congrArg Subtype.val h
  cases p with
  | inl s =>
    cases q with
    | inl t =>
      congr 1
      apply Subtype.ext
      funext i
      exact Subtype.ext (congrFun he i)
    | inr p =>
      rcases p with ⟨i,t,b⟩
      dsimp only [constrainedFrameOfData] at he
      have h0 : i=0 := (exteriorTriple_zero_mem_iff U (t.1 0) (t.1 1) b.1 b.2 i).mp
        (by rw [←congrFun he 0]; exact (s.1 0).property)
      have h1 : i=1 := (exteriorTriple_one_mem_iff U (t.1 0) (t.1 1) b.1 b.2 i).mp
        (by rw [←congrFun he 1]; exact (s.1 1).property)
      omega
  | inr p =>
    rcases p with ⟨i,s,b⟩
    cases q with
    | inl t =>
      dsimp only [constrainedFrameOfData] at he
      have h0 : i=0 := (exteriorTriple_zero_mem_iff U (s.1 0) (s.1 1) b.1 b.2 i).mp
        (by rw [congrFun he 0]; exact (t.1 0).property)
      have h1 : i=1 := (exteriorTriple_one_mem_iff U (s.1 0) (s.1 1) b.1 b.2 i).mp
        (by rw [congrFun he 1]; exact (t.1 1).property)
      omega
    | inr q =>
      rcases q with ⟨j,t,c⟩
      have hp := exteriorTriple_injective U (a₁ := (i,s.1 0,s.1 1,b))
        (a₂ := (j,t.1 0,t.1 1,c)) he
      have hi := congrArg Prod.fst hp
      have hs0 := congrArg (fun p => p.2.1) hp
      have hs1 := congrArg (fun p => p.2.2.1) hp
      have hb := congrArg (fun p => p.2.2.2) hp
      have hs : s=t := by
        apply Subtype.ext
        funext k
        fin_cases k
        · exact hs0
        · exact hs1
      subst_vars
      rfl
/-- Inclusion preserves and reflects independence of an explicit pair. -/
theorem independent_submodule_pair_iff (U : Submodule (ZMod 2) V) (a b : U) :
    LinearIndependent (ZMod 2) ![a,b] ↔ LinearIndependent (ZMod 2) ![(a:V),(b:V)] := by
  have h := U.subtype.linearIndependent_iff (v := ![a,b])
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have he : (U.subtype ∘ ![a,b]) = ![(a:V),(b:V)] := by ext i; fin_cases i <;> rfl
  rw [he] at h
  exact h.symm
/-- Every actual constrained frame admits one of the four literal parameter forms. -/
theorem constrainedFrameOfData_surjective (U : Submodule (ZMod 2) V) :
    Function.Surjective (constrainedFrameOfData U) := by
  rintro ⟨s,hs,hcond⟩
  have he : ![s 0,s 1,s 2]=s := by ext i; fin_cases i <;> rfl
  by_cases ha : s 0 ∈ U
  · by_cases hb : s 1 ∈ U
    · have hc : s 2 ∈ U := by
        rcases hcond with h|h|h
        · exact h.2
        · exact h.2
        · exact (U.add_mem_iff_right ha).mp h.2
      have hm (i : Fin 3) : s i ∈ U := by fin_cases i <;> assumption
      let u : Fin 3 → U := fun i => ⟨s i,hm i⟩
      have hu : LinearIndependent (ZMod 2) u :=
        (U.subtype.linearIndependent_iff (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).mp hs
      exact ⟨Sum.inl ⟨u,hu⟩,rfl⟩
    · have hc : s 2 ∈ U := by
        rcases hcond with h|h|h
        · exact h.2
        · exact False.elim (hb h.1)
        · exact False.elim (hb ((U.add_mem_iff_right ha).mp h.1))
      let u : U := ⟨s 0,ha⟩
      let v : U := ⟨s 2,hc⟩
      have hp : LinearIndependent (ZMod 2) ![u,v] := by
        apply (independent_submodule_pair_iff U u v).mpr
        have hh := hs.comp ![(0:Fin 3),2] (by decide)
        have hepair : s ∘ ![(0:Fin 3),2] = ![(u:V),(v:V)] := by ext i; fin_cases i <;> rfl
        rw [hepair] at hh
        exact hh
      refine ⟨Sum.inr (0,⟨![u,v],hp⟩,⟨s 1,hb⟩),?_⟩
      apply Subtype.ext
      exact he
  · by_cases hb : s 1 ∈ U
    · have hc : s 2 ∈ U := by
        rcases hcond with h|h|h
        · exact False.elim (ha h.1)
        · exact h.2
        · exact False.elim (ha ((U.add_mem_iff_left hb).mp h.1))
      let u : U := ⟨s 1,hb⟩
      let v : U := ⟨s 2,hc⟩
      have hp : LinearIndependent (ZMod 2) ![u,v] := by
        apply (independent_submodule_pair_iff U u v).mpr
        have hh := hs.comp ![(1:Fin 3),2] (by decide)
        have hepair : s ∘ ![(1:Fin 3),2] = ![(u:V),(v:V)] := by ext i; fin_cases i <;> rfl
        rw [hepair] at hh
        exact hh
      refine ⟨Sum.inr (1,⟨![u,v],hp⟩,⟨s 0,ha⟩),?_⟩
      apply Subtype.ext
      exact he
    · have hsum : s 0+s 1 ∈ U ∧ s 0+s 2 ∈ U := by tauto
      let u : U := ⟨s 0+s 1,hsum.1⟩
      let v : U := ⟨s 0+s 2,hsum.2⟩
      have hp : LinearIndependent (ZMod 2) ![u,v] := by
        apply (independent_submodule_pair_iff U u v).mpr
        have ht : LinearIndependent (ZMod 2) ![s 0,s 0+s 1,s 0+s 2] :=
          (binary_triple_shear_independent_iff _ _ _).mpr (he.symm ▸ hs)
        have hh := ht.comp ![(1:Fin 3),2] (by decide)
        have hepair : ![s 0,s 0+s 1,s 0+s 2] ∘ ![(1:Fin 3),2] = ![(u:V),(v:V)] := by ext i; fin_cases i <;> rfl
        rw [hepair] at hh
        exact hh
      refine ⟨Sum.inr (2,⟨![u,v],hp⟩,⟨s 0,ha⟩),?_⟩
      apply Subtype.ext
      funext i
      fin_cases i <;> simp [constrainedFrameOfData,exteriorTriple,u,v,←add_assoc,binary_module_add_self]
/-- The exact constrained frame decomposition is a literal finite equivalence. -/
noncomputable def constrainedFrameEquiv (U : Submodule (ZMod 2) V) :
    ConstrainedFrameData U ≃ ConstrainedFrames U :=
  Equiv.ofBijective (constrainedFrameOfData U)
    ⟨constrainedFrameOfData_injective U,constrainedFrameOfData_surjective U⟩
/-- A three-dimensional annihilator gives the exact constrained raw-frame population. -/
theorem constrainedFrames_card [Fintype V] (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U=3) :
    Nat.card (ConstrainedFrames U)=168+126*(2^Module.finrank (ZMod 2) V-8) := by
  classical
  let : Fintype U := Fintype.ofFinite U
  have ht : Nat.card {s : Fin 3 → U // LinearIndependent (ZMod 2) s}=168 := by
    rw [card_linearIndependent (by omega : 3≤Module.finrank (ZMod 2) U)]
    norm_num [hU,Fin.prod_univ_succ]
  have hp : Nat.card {s : Fin 2 → U // LinearIndependent (ZMod 2) s}=42 := by
    rw [card_linearIndependent (by omega : 2≤Module.finrank (ZMod 2) U)]
    norm_num [hU,Fin.prod_univ_succ]
  have ho : Nat.card {b : V // b ∉ U}=2^Module.finrank (ZMod 2) V-8 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := V),
      Module.card_eq_pow_finrank (K := ZMod 2) (V := U)]
    norm_num [hU]
  rw [←Nat.card_congr (constrainedFrameEquiv U)]
  change Nat.card ({s : Fin 3 → U // LinearIndependent (ZMod 2) s} ⊕
    (Fin 3 × {s : Fin 2 → U // LinearIndependent (ZMod 2) s} × {b : V // b ∉ U}))=_
  rw [Nat.card_sum,Nat.card_prod,Nat.card_prod,ht,hp,ho]
  norm_num
  ring
end BinaryFieldCounterexamples.Trees
