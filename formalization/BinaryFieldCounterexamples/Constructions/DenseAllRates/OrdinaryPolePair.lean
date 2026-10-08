/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.OrdinaryAsymptotic
public import BinaryFieldCounterexamples.Constructions.PoleReduction
public import BinaryFieldCounterexamples.Agreement.SourceConversionPair
public import BinaryFieldCounterexamples.Constructions.Gold.FiniteExtensions
/-!
# Received pairs from arbitrary decoding lists

A union bound over pairwise polynomial roots selects a pole preserving every
challenge. Divided differences turn the literal decoding list into exceptional
challenges for one reciprocal pair. A further quadratic extension applies the
proved conversion of Lemma 3.12, making both individual and common agreements
exact while keeping all challenges, including a possible old zero challenge. The
final extension
has the explicit degree twice the chosen pole-field degree.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.DenseConstruction
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
/-- A field larger than the union of all pairwise root sets contains an exterior
pole that separates every polynomial in a finite strict-degree list. -/
theorem exists_separating_pole {F:Type*} [Field F] [Fintype F]
    (S:Finset F) (E:Finset F[X]) (J:ℕ) (hE:∀p∈E,p.degree<J)
    (hq:S.card+J*E.card^2<Fintype.card F) :
    ∃β:F,β∉S ∧ Set.InjOn (fun p:F[X]=>p.eval β) E := by
  let pairs:=(E×ˢE).filter (fun z=>z.1≠z.2)
  let bad:=pairs.biUnion (fun z=>Finset.univ.filter (fun x:F=>z.1.eval x=z.2.eval x))
  have hc:bad.card≤J*E.card^2 := by
    apply le_trans (Finset.card_biUnion_le) _
    calc
      _≤∑_z∈pairs,J := by
        apply Finset.sum_le_sum
        intro z hz
        obtain ⟨hzE,hne⟩:=Finset.mem_filter.mp hz
        obtain ⟨hp,hq⟩:=Finset.mem_product.mp hzE
        have hn:z.1-z.2≠0:=sub_ne_zero.mpr hne
        have hd:(z.1-z.2).degree<J:=
          (degree_sub_le _ _).trans_lt (max_lt (hE _ hp) (hE _ hq))
        have hb:=card_filter_eval_eq_zero_le (Finset.univ:Finset F) (z.1-z.2) hn
        simp only [eval_sub,sub_eq_zero] at hb
        exact hb.trans (le_of_lt ((natDegree_lt_iff_degree_lt hn).mpr hd))
      _≤J*E.card^2 := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        have hh:pairs.card≤E.card^2:=by
          exact (Finset.card_filter_le _ _).trans_eq (by rw [Finset.card_product]; ring)
        nlinarith
  have hcard:(S∪bad).card<Fintype.card F:=
    (Finset.card_union_le _ _).trans_lt (by omega)
  obtain ⟨β,hβuniv,hβ⟩:=Finset.exists_mem_notMem_of_card_lt_card (t:=(Finset.univ:Finset F)) (by simpa only [Finset.card_univ] using hcard)
  have hb:β∉S∪bad:=hβ
  refine ⟨β,fun hx=>hb (Finset.mem_union_left _ hx),?_⟩
  intro p hp q hq he
  by_contra hn
  apply hb
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨(p,q),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩,hn⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩
/-- Any finite decoding list gives one reciprocal pair with every challenge
kept when an exterior pole separates the explaining polynomials. -/
theorem ordinary_family_pole_pair {F:Type*} [Field F] [Fintype F]
    (S:Finset F) (w:S→F) (E:Finset F[X]) (J T:ℕ)
    (hE:∀p∈E,p.degree<J ∧ T≤agreementCount S w p)
    (hJ:J≤S.card) (hq:S.card+J*E.card^2<Fintype.card F) :
    ∃f g:S→F,commonAgreementEQ S J f g J ∧ E.card≤(badChallenges S J f g T).card := by
  obtain ⟨β,hβ,hinj⟩:=exists_separating_pole S E J (fun p hp=>(hE p hp).1) hq
  let w0:F→F:=fun x=>if hx:x∈S then w ⟨x,hx⟩ else 0
  let R:=Lagrange.interpolate S id w0
  have hR (x:F) (hx:x∈S):R.eval x=w0 x :=
    Lagrange.eval_interpolate_at_node w0 Function.injective_id.injOn hx
  have hw:(fun x:S=>w0 x)=w:=by funext x; simp [w0,x.property]
  let f:S→F:=fun x=>R.eval x.val*(x.val-β)⁻¹
  let g:S→F:=fun x=>(x.val-β)⁻¹
  refine ⟨f,g,commonAgreementEQ_reciprocal_right S β hβ J hJ f,?_⟩
  have hsub:E.image (fun p=>(-p).eval β)⊆badChallenges S J f g T := by
    intro z hz
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hz
    apply poleReduction_badChallenge S β hβ R (-p) J T
    · simpa only [degree_neg] using (hE p hp).1.le
    · have he:(S.filter (fun x=>(R+ -p).eval x=0))=
          S.filter (fun x=>p.eval x=w0 x) := by
        ext x
        simp only [Finset.mem_filter,eval_add,eval_neg]
        constructor
        · rintro ⟨hx,hh⟩
          rw [hR x hx] at hh
          exact ⟨hx,by linear_combination -hh⟩
        · rintro ⟨hx,hh⟩
          rw [hR x hx]
          exact ⟨hx,by rw [hh]; ring⟩
      rw [he,←agreementCount_eq_card_filter S w0 p,hw]
      exact (hE p hp).2
  have hc:(E.image (fun p=>(-p).eval β)).card=E.card:=Finset.card_image_iff.mpr (by
    intro p hp q hq he
    apply hinj hp hq
    simpa only [eval_neg,neg_inj] using he)
  rw [←hc]
  exact Finset.card_le_card hsub
/-- Field embeddings preserve a concrete decoding list and every agreement
count, including its exact number of distinct polynomials. -/
theorem ordinary_family_map {B F:Type*} [Field B] [Field F]
    (φ:B→+*F) (S:Finset B) (w:S→B) (E:Finset B[X]) (J T:ℕ)
    (hE:∀p∈E,p.degree<J ∧ T≤agreementCount S w p) :
    ∃(w':mappedDomain φ S→F)(E':Finset F[X]), E'.card=E.card ∧
      ∀p∈E',p.degree<J ∧ T≤agreementCount (mappedDomain φ S) w' p := by
  let w0:B→B:=fun x=>if hx:x∈S then w ⟨x,hx⟩ else 0
  let wF:F→F:=Function.extend φ (φ ∘ w0) 0
  have hw:(fun x:S=>w0 x)=w:=by funext x; simp [w0,x.property]
  have hwF(x:B):wF (φ x)=φ (w0 x):=φ.injective.extend_apply _ _ _
  refine ⟨fun x=>wF x,E.image (Polynomial.map φ),?_,?_⟩
  · exact Finset.card_image_of_injective _ (Polynomial.map_injective φ φ.injective)
  · intro p hp
    obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hp
    refine ⟨?_,?_⟩
    · rw [degree_map_eq_of_injective φ.injective]
      exact (hE q hq).1
    · rw [agreementCount_mappedDomain]
      simp only [hwF,eval_map_apply,φ.injective.eq_iff]
      rw [←agreementCount_eq_card_filter S w0 q,hw]
      exact (hE q hq).2
/-- A sufficiently large finite extension, followed by a quadratic extension,
converts any actual decoding list to a pair with both individual and common
agreements exactly the degree parameter, keeping the entire list count. -/
theorem ordinary_family_extension_pair
    (B:Type) [Field B] [Fintype B] [CharP B 2]
    (S:Finset B) (w:S→B) (E:Finset B[X]) (J T e:ℕ) (he:1≤e)
    (hE:∀p∈E,p.degree<J ∧ T≤agreementCount S w p) (hJ:J≤S.card)
    (hq:S.card+J*E.card^2<(Fintype.card B)^e) :
    ∃(F:Type)(fieldF:Field F)(finiteF:Fintype F),
      let :=fieldF
      let :=finiteF
      ∃φ:B→+*F,Fintype.card F=(Fintype.card B)^(2*e) ∧
      ∃f g:mappedDomain φ S→F,
        agreementEQ (mappedDomain φ S) J f J ∧ agreementEQ (mappedDomain φ S) J g J ∧
        commonAgreementEQ (mappedDomain φ S) J f g J ∧
        E.card≤(nonzeroBadChallenges (mappedDomain φ S) J f g T).card := by
  obtain ⟨F0,field0,finite0,φ,hcard0⟩:=Gold.exists_extension_of_degree B e he
  let :=field0
  let :=finite0
  let : Algebra B F0:=φ.toAlgebra
  let : CharP F0 2:=charP_of_injective_algebraMap' B 2
  obtain ⟨w0,E0,hE0,hprop⟩:=ordinary_family_map φ S w E J T hE
  obtain ⟨f0,g0,hcommon,hcount⟩:=ordinary_family_pole_pair (mappedDomain φ S) w0 E0 J T hprop
    (by simpa only [card_mappedDomain] using hJ)
    (by simpa only [card_mappedDomain,hE0,hcard0] using hq)
  obtain ⟨F,fieldF,finiteF,ψ,hcardF⟩:=Gold.exists_extension_of_degree F0 2 (by omega)
  let :=fieldF
  let :=finiteF
  have hsize:Fintype.card F0<Fintype.card F := by
    rw [hcardF]
    have hh:=Fintype.one_lt_card (α:=F0)
    nlinarith
  obtain ⟨f,g,hf,hg,hfg,hlabels⟩:=exists_converted_pair_of_common_agreement ψ hsize
    (mappedDomain φ S) J J T f0 g0 hcommon
  refine ⟨F,fieldF,finiteF,ψ.comp φ,?_,?_⟩
  · rw [hcardF,hcard0,←pow_mul]
    congr 1
    omega
  · have hmap:mappedDomain (ψ.comp φ) S=mappedDomain ψ (mappedDomain φ S) := by
      simp only [mappedDomain,Finset.image_image,RingHom.coe_comp,Function.comp_def]
    rw [hmap]
    refine ⟨f,g,hf,hg,hfg,?_⟩
    rw [←hE0]
    exact hcount.trans hlabels
end BinaryFieldCounterexamples.DenseConstruction
