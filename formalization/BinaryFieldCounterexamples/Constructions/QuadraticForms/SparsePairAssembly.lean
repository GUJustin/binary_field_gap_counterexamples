/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.MappedFactorCollisions
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.VariableHeadPairReduction
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.NumeratorTransport
public import BinaryFieldCounterexamples.Polynomial.Map
public import BinaryFieldCounterexamples.Polynomial.PrimePowerSupport

/-!
# Received pairs from sparse quadratic locator families

An exact-size subfamily of sparse conversion locators is transported to the
containing field. The sharp pairwise factor collision bound and pole averaging
then produce one received pair with the original rational denominator.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- A sparse locator family on a scalar submodule gives the exact received-pair
collision denominator after any proper field embedding. -/
theorem exists_mapped_polePair_of_sparse_locator_family
    {k B F : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    [Field F] [Fintype F]
    (φ : B→+*F) (p r : ℕ) [Fact p.Prime] [CharP B p] [CharP F p]
    (hr : 1≤r) (hqk : Fintype.card k=p^r)
    (D : Submodule k B) (d t M : ℕ) (ht : 2≤t) (htd : 2*t≤d)
    (hDcard : (Finset.univ.filter fun x : B => x∈D).card=(Fintype.card k)^d)
    (hqF : (Finset.univ.filter fun x : B => x∈D).card<Fintype.card F)
    (E : Finset B[X]) (hM : M≤E.card) (hMpos : 0<M)
    (hprop : ∀ P∈E,∃ A : B[X],
      A^(Fintype.card k-1)*(P^(Fintype.card k)-subspacePolynomial D.toAddSubgroup)=P ∧
      A≠0 ∧ A.natDegree=(Fintype.card k)^(d-t-1) ∧
      (∀ e∈A.support,(Fintype.card k)^(t-1)∣e) ∧
      ((Finset.univ.filter fun x : B => x∈D).filter fun x => A.eval x=0).card=
        (Fintype.card k)^(d-2*t) ∧
      (P-primePowerQuarterNumerator p r (subspacePolynomial D.toAddSubgroup) 0).degree<
        (Fintype.card k)^(d-2) ∧
      ((Finset.univ.filter fun x : B => x∈D).filter fun x => P.eval x=0).card=
        (Fintype.card k)^(d-1)-(Fintype.card k-1)*(Fintype.card k)^(d-t-1))
    (A₀ : ℕ)
    (hsource : ∀ β∉mappedDomain φ (Finset.univ.filter fun x : B => x∈D),
      agreementLE (mappedDomain φ (Finset.univ.filter fun x : B => x∈D))
        ((Fintype.card k)^(d-2))
        (fun x =>
          (primePowerQuarterNumerator p r
            ((subspacePolynomial D.toAddSubgroup).map φ) β).eval (x:F)*((x:F)-β)⁻¹) A₀) :
    let S := mappedDomain φ (Finset.univ.filter fun x : B => x∈D)
    let K := (Fintype.card k)^(d-2)
    let T := (Fintype.card k)^(d-1)-
      (Fintype.card k-1)*(Fintype.card k)^(d-t-1)
    let δ := (Fintype.card k-1)*(Fintype.card k)^(d-2*t)
    ∃ f g : S→F,
      agreementEQ S K g K ∧ commonAgreementEQ S K f g K ∧
      agreementLE S K f A₀ ∧
      ⌈(M:ℚ)*(Fintype.card F-S.card:ℚ)/
        ((Fintype.card F-S.card:ℚ)+δ*((M:ℚ)-1))⌉₊-1≤
        (nonzeroBadChallenges S K f g T).card := by
  let S₀ := Finset.univ.filter fun x : B => x∈D
  let S := mappedDomain φ S₀
  let b := Fintype.card k
  let K := b^(d-2)
  let T := b^(d-1)-(b-1)*b^(d-t-1)
  let δ₀ := b^(d-2*t)
  let δ := (b-1)*δ₀
  let L := subspacePolynomial D.toAddSubgroup
  let R := primePowerQuarterNumerator p r L 0
  obtain ⟨E₀,hE₀,hE₀card⟩ := Finset.exists_subset_card_eq hM
  let e : Fin M≃E₀ := (Fin.castOrderIso hE₀card).symm.toEquiv.trans E₀.equivFin.symm
  let P₀ : Fin M→B[X] := fun i => (e i).val
  have hP₀mem (i : Fin M) : P₀ i∈E := hE₀ (e i).property
  choose A hconv hAne hAdeg hsupp hAzeros hcorr hProots using
    fun i : Fin M => hprop (P₀ i) (hP₀mem i)
  let I : Finset (Fin M) := Finset.univ
  let PF : Fin M→F[X] := fun i => (P₀ i).map φ
  have hIcard : I.card=M := by simp [I]
  have hI : I.Nonempty := ⟨⟨0,hMpos⟩,Finset.mem_univ _⟩
  have hb : b=p^r := hqk
  have hb2 : 2≤b := Fintype.one_lt_card
  have hd2 : 2≤d := by omega
  have hpowfactor : p^(r*(t-1))*δ₀=b^(d-t-1) := by
    change p^(r*(t-1))*b^(d-2*t)=b^(d-t-1)
    rw [show p^(r*(t-1))=(p^r)^(t-1) by rw [←pow_mul],←hb,←pow_add]
    congr 1
    omega
  have hLdomain : ∀x∈S₀,L.eval x=0 := by
    intro x hx
    exact (subspacePolynomial_eval_eq_zero_iff D.toAddSubgroup x).mpr
      (Finset.mem_filter.mp hx).2
  have hLoutside : ∀x∉S,(L.map φ).eval x≠0 := by
    intro x hx hz
    have hxmap : x∈D.toAddSubgroup.map φ.toAddMonoidHom := by
      apply (subspacePolynomial_eval_eq_zero_iff
        (D.toAddSubgroup.map φ.toAddMonoidHom) x).mp
      rw [←map_subspacePolynomial φ D.toAddSubgroup]
      exact hz
    apply hx
    change x∈mappedDomain φ (additiveDomain D.toAddSubgroup)
    rw [mappedDomain_additiveDomain]
    exact (mem_additiveDomain _ x).mpr hxmap
  have hpair : ∀i∈I,∀j∈I,i≠j→
      ((Finset.univ\S).filter fun β => (PF i).eval β=(PF j).eval β).card≤δ := by
    intro i hi j hj hij
    have hPneq : P₀ i≠P₀ j := by
      intro heq
      apply hij
      exact e.injective (Subtype.ext heq)
    apply QuadraticLocatorConversion.card_mapped_locator_collision_le φ p r b (t-1) δ₀
      hb hb2 S₀ L (A i) (A j) (P₀ i) (P₀ j) hLdomain hLoutside
      (hconv i) (hconv j) hPneq
    · rw [hAdeg i]
      positivity
    · rw [hAdeg j]
      positivity
    · intro z hz
      simpa only [pow_mul,←hb] using hsupp i z hz
    · intro z hz
      simpa only [pow_mul,←hb] using hsupp j z hz
    · rw [hpowfactor,hAdeg i]
    · rw [hpowfactor,hAdeg j]
    · exact hAzeros i
  have hKcard : K≤S.card := by
    change b^(d-2)≤(mappedDomain φ S₀).card
    rw [card_mappedDomain,hDcard]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hsL : ∀n∈L.support,∃u : ℕ,n=(p^r)^u := by
    intro z hz
    obtain ⟨u,hu⟩ := FiniteFieldLocator.subspacePolynomial_q_support D z hz
    exact ⟨u,by simpa only [hqk] using hu⟩
  let RF : F→F[X] := fun β => primePowerQuarterNumerator p r (L.map φ) β
  have hmapR : R.map φ=RF 0 := by
    dsimp only [R,RF]
    simpa using map_primePowerQuarterNumerator φ p r hr L 0 hsL
  have hdeg : ∀β∉S,∀i∈I,(PF i-RF β).degree≤K := by
    intro β hβ i hi
    have htail : (RF 0-RF β).natDegree≤0 :=
      primePowerQuarterNumerator_sub_natDegree_le_zero p r hr (L.map φ) 0 β (by
        intro z hz
        obtain ⟨u,hu⟩ := hsL z (by
          rw [mem_support_iff] at hz ⊢
          exact fun hh => hz (by simp only [coeff_map,hh,map_zero]))
        exact ⟨u,hu⟩)
    change ((P₀ i).map φ-RF β).degree≤K
    rw [show (P₀ i).map φ-RF β=(P₀ i-R).map φ+(RF 0-RF β) by
      rw [Polynomial.map_sub φ,hmapR]
      ring]
    apply (degree_add_le _ _).trans
    apply max_le
    · exact (degree_map_le).trans (hcorr i).le
    · exact (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr htail)).trans (by simp [K])
  have hroots : ∀i∈I,T≤(S.filter fun x => (PF i).eval x=0).card := by
    intro i hi
    change T≤((mappedDomain φ S₀).filter fun x => ((P₀ i).map φ).eval x=0).card
    rw [QuadraticLocatorConversion.card_mapped_factor_zeros,hProots i]
  have hp := exists_polePair_of_variableHead_pairwise_collision_bound I S RF PF K T A₀ δ
    (by change (mappedDomain φ S₀).card<Fintype.card F
        rwa [card_mappedDomain]) hKcard hI
  have hsource' : ∀β∉S,agreementLE S K
      (fun x => (RF β).eval (x:F)*((x:F)-β)⁻¹) A₀ := by
    simpa only [S,S₀,K,RF,L,b] using hsource
  obtain ⟨f,g,hg,hcommon,hf,hbad⟩ := hp hsource' hdeg hroots hpair
  dsimp only
  refine ⟨f,g,hg,hcommon,hf,?_⟩
  simpa only [S,S₀,K,T,δ,δ₀,b,hIcard] using hbad

/-- Both collision bounds for sparse locators, assuming the strict gap above the agreement bound
for the first input of Lemma 3.13, which excludes zero. -/
theorem exists_mapped_polePair_of_sparse_locator_family_sharp
    {k B F : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    [Field F] [Fintype F]
    (φ : B→+*F) (p r : ℕ) [Fact p.Prime] [CharP B p] [CharP F p]
    (hr : 1≤r) (hqk : Fintype.card k=p^r)
    (D : Submodule k B) (d t M : ℕ) (ht : 2≤t) (htd : 2*t≤d)
    (hDcard : (Finset.univ.filter fun x : B => x∈D).card=(Fintype.card k)^d)
    (hqF : (Finset.univ.filter fun x : B => x∈D).card<Fintype.card F)
    (E : Finset B[X]) (hM : M≤E.card) (hMpos : 0<M)
    (hprop : ∀ P∈E,∃ A : B[X],
      A^(Fintype.card k-1)*(P^(Fintype.card k)-subspacePolynomial D.toAddSubgroup)=P ∧
      A≠0 ∧ A.natDegree=(Fintype.card k)^(d-t-1) ∧
      (∀ e∈A.support,(Fintype.card k)^(t-1)∣e) ∧
      ((Finset.univ.filter fun x : B => x∈D).filter fun x => A.eval x=0).card=
        (Fintype.card k)^(d-2*t) ∧
      (P-primePowerQuarterNumerator p r (subspacePolynomial D.toAddSubgroup) 0).degree<
        (Fintype.card k)^(d-2) ∧
      ((Finset.univ.filter fun x : B => x∈D).filter fun x => P.eval x=0).card=
        (Fintype.card k)^(d-1)-(Fintype.card k-1)*(Fintype.card k)^(d-t-1))
    (A₀ : ℕ)
    (hgap : A₀<(Fintype.card k)^(d-1)-(Fintype.card k-1)*(Fintype.card k)^(d-t-1))
    (hsource : ∀ β∉mappedDomain φ (Finset.univ.filter fun x : B => x∈D),
      agreementLE (mappedDomain φ (Finset.univ.filter fun x : B => x∈D))
        ((Fintype.card k)^(d-2))
        (fun x =>
          (primePowerQuarterNumerator p r
            ((subspacePolynomial D.toAddSubgroup).map φ) β).eval (x:F)*((x:F)-β)⁻¹) A₀) :
    let S := mappedDomain φ (Finset.univ.filter fun x : B => x∈D)
    let K := (Fintype.card k)^(d-2)
    let T := (Fintype.card k)^(d-1)-
      (Fintype.card k-1)*(Fintype.card k)^(d-t-1)
    let δ := (Fintype.card k-1)*(Fintype.card k)^(d-2*t)
    ∃ f g : S→F,
      agreementEQ S K g K ∧ commonAgreementEQ S K f g K ∧
      agreementLE S K f A₀ ∧
      max (M-⌊((δ:ℚ)*M.choose 2)/(Fintype.card F-S.card:ℚ)⌋₊)
        ⌈(M:ℚ)*(Fintype.card F-S.card:ℚ)/
        ((Fintype.card F-S.card:ℚ)+δ*((M:ℚ)-1))⌉₊≤
        (nonzeroBadChallenges S K f g T).card := by
  let S₀ := Finset.univ.filter fun x : B => x∈D
  let S := mappedDomain φ S₀
  let b := Fintype.card k
  let K := b^(d-2)
  let T := b^(d-1)-(b-1)*b^(d-t-1)
  let δ₀ := b^(d-2*t)
  let δ := (b-1)*δ₀
  let L := subspacePolynomial D.toAddSubgroup
  let R := primePowerQuarterNumerator p r L 0
  obtain ⟨E₀,hE₀,hE₀card⟩ := Finset.exists_subset_card_eq hM
  let e : Fin M≃E₀ := (Fin.castOrderIso hE₀card).symm.toEquiv.trans E₀.equivFin.symm
  let P₀ : Fin M→B[X] := fun i => (e i).val
  have hP₀mem (i : Fin M) : P₀ i∈E := hE₀ (e i).property
  choose A hconv hAne hAdeg hsupp hAzeros hcorr hProots using
    fun i : Fin M => hprop (P₀ i) (hP₀mem i)
  let I : Finset (Fin M) := Finset.univ
  let PF : Fin M→F[X] := fun i => (P₀ i).map φ
  have hIcard : I.card=M := by simp [I]
  have hI : I.Nonempty := ⟨⟨0,hMpos⟩,Finset.mem_univ _⟩
  have hb : b=p^r := hqk
  have hb2 : 2≤b := Fintype.one_lt_card
  have hd2 : 2≤d := by omega
  have hpowfactor : p^(r*(t-1))*δ₀=b^(d-t-1) := by
    change p^(r*(t-1))*b^(d-2*t)=b^(d-t-1)
    rw [show p^(r*(t-1))=(p^r)^(t-1) by rw [←pow_mul],←hb,←pow_add]
    congr 1
    omega
  have hLdomain : ∀x∈S₀,L.eval x=0 := by
    intro x hx
    exact (subspacePolynomial_eval_eq_zero_iff D.toAddSubgroup x).mpr
      (Finset.mem_filter.mp hx).2
  have hLoutside : ∀x∉S,(L.map φ).eval x≠0 := by
    intro x hx hz
    have hxmap : x∈D.toAddSubgroup.map φ.toAddMonoidHom := by
      apply (subspacePolynomial_eval_eq_zero_iff
        (D.toAddSubgroup.map φ.toAddMonoidHom) x).mp
      rw [←map_subspacePolynomial φ D.toAddSubgroup]
      exact hz
    apply hx
    change x∈mappedDomain φ (additiveDomain D.toAddSubgroup)
    rw [mappedDomain_additiveDomain]
    exact (mem_additiveDomain _ x).mpr hxmap
  have hpair : ∀i∈I,∀j∈I,i≠j→
      ((Finset.univ\S).filter fun β => (PF i).eval β=(PF j).eval β).card≤δ := by
    intro i hi j hj hij
    have hPneq : P₀ i≠P₀ j := by
      intro heq
      apply hij
      exact e.injective (Subtype.ext heq)
    apply QuadraticLocatorConversion.card_mapped_locator_collision_le φ p r b (t-1) δ₀
      hb hb2 S₀ L (A i) (A j) (P₀ i) (P₀ j) hLdomain hLoutside
      (hconv i) (hconv j) hPneq
    · rw [hAdeg i]
      positivity
    · rw [hAdeg j]
      positivity
    · intro z hz
      simpa only [pow_mul,←hb] using hsupp i z hz
    · intro z hz
      simpa only [pow_mul,←hb] using hsupp j z hz
    · rw [hpowfactor,hAdeg i]
    · rw [hpowfactor,hAdeg j]
    · exact hAzeros i
  have hKcard : K≤S.card := by
    change b^(d-2)≤(mappedDomain φ S₀).card
    rw [card_mappedDomain,hDcard]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hsL : ∀n∈L.support,∃u : ℕ,n=(p^r)^u := by
    intro z hz
    obtain ⟨u,hu⟩ := FiniteFieldLocator.subspacePolynomial_q_support D z hz
    exact ⟨u,by simpa only [hqk] using hu⟩
  let RF : F→F[X] := fun β => primePowerQuarterNumerator p r (L.map φ) β
  have hmapR : R.map φ=RF 0 := by
    dsimp only [R,RF]
    simpa using map_primePowerQuarterNumerator φ p r hr L 0 hsL
  have hdeg : ∀β∉S,∀i∈I,(PF i-RF β).degree≤K := by
    intro β hβ i hi
    have htail : (RF 0-RF β).natDegree≤0 :=
      primePowerQuarterNumerator_sub_natDegree_le_zero p r hr (L.map φ) 0 β (by
        intro z hz
        obtain ⟨u,hu⟩ := hsL z (by
          rw [mem_support_iff] at hz ⊢
          exact fun hh => hz (by simp only [coeff_map,hh,map_zero]))
        exact ⟨u,hu⟩)
    change ((P₀ i).map φ-RF β).degree≤K
    rw [show (P₀ i).map φ-RF β=(P₀ i-R).map φ+(RF 0-RF β) by
      rw [Polynomial.map_sub φ,hmapR]
      ring]
    apply (degree_add_le _ _).trans
    apply max_le
    · exact (degree_map_le).trans (hcorr i).le
    · exact (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr htail)).trans (by simp [K])
  have hroots : ∀i∈I,T≤(S.filter fun x => (PF i).eval x=0).card := by
    intro i hi
    change T≤((mappedDomain φ S₀).filter fun x => ((P₀ i).map φ).eval x=0).card
    rw [QuadraticLocatorConversion.card_mapped_factor_zeros,hProots i]
  have hp := exists_polePair_of_variableHead_pairwise_collision_bounds I S RF PF K T A₀ δ hgap
    (by change (mappedDomain φ S₀).card<Fintype.card F
        rwa [card_mappedDomain]) hKcard hI
  have hsource' : ∀β∉S,agreementLE S K
      (fun x => (RF β).eval (x:F)*((x:F)-β)⁻¹) A₀ := by
    simpa only [S,S₀,K,RF,L,b] using hsource
  obtain ⟨f,g,hg,hcommon,hf,hbad⟩ := hp hsource' hdeg hroots hpair
  dsimp only
  refine ⟨f,g,hg,hcommon,hf,?_⟩
  simpa only [S,S₀,K,T,δ,δ₀,b,hIcard] using hbad

end BinaryFieldCounterexamples
