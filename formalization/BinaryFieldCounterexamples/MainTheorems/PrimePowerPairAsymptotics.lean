/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.QuadraticForms
public import BinaryFieldCounterexamples.MainTheorems.OrdinaryListAsymptotics
public import Mathlib.FieldTheory.Finite.Extension
/-!
# Main theorem: quasipolynomial exceptional sets at every prime-power base

This is the pair consequence after Theorem 5.22 in Section 5.9. Fixing any
finite scalar field, and choosing `t = floor(n/2)`, gives one received pair
over a sufficiently large finite extension with quasipolynomially many
distinct nonzero exceptional challenges. The Johnson deficit has two-sided
fourth-root bounds. The individual and common agreements are exactly those
of Theorem 5.22; the characteristic is arbitrary.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial OrdinaryListConstruction Filter
open scoped Topology
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The remark after Theorem 5.22, in finite form: every sufficiently large
extension preserves the entire middle-rank locator population as distinct
nonzero challenges, at the stated rate and agreement. -/
theorem primePower_middle_rank_pair_large_extension
    (k B F : Type) [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    [Field F] [Fintype F] (φ : B→+*F) (n : ℕ) (hn : 4≤n)
    (hB : Fintype.card B=(Fintype.card k)^(2*n))
    (hcap : Fintype.card B+Fintype.card k*Fintype.card B*
      (quadraticListCount (Fintype.card k) n 0 (n/2)).choose 2 < Fintype.card F) :
    let b:=Fintype.card k
    let N:=Fintype.card B
    let S:=mappedDomain φ Finset.univ
    let K:=N/b^2
    let T:=b^(2*n-1)-(b-1)*b^(2*n-n/2-1)
    ∃f g:S→F,agreementEQ S K g K ∧ commonAgreementEQ S K f g K ∧
      agreementLE S K f ⌊((b+1:ℚ)*N/(2*b^2)-1)⌋₊ ∧
      ((b+1:ℚ)*N/(2*b^2)-1)<T ∧
      quadraticListCount b n 0 (n/2)≤(nonzeroBadChallenges S K f g T).card := by
  let b:=Fintype.card k
  let N:=Fintype.card B
  let t:=n/2
  let M:=quadraticListCount b n 0 t
  have hb : 2≤b:=Fintype.one_lt_card
  have ht : 2≤t:=by dsimp [t]; omega
  have htn : t≤n:=Nat.div_le_self _ _
  have hN : N=b^(2*n):=hB
  have hD : (Finset.univ.filter (fun x:B=>x∈(⊤:Submodule k B))).card=N := by simp [N]
  have hq : N<Fintype.card F:=by dsimp [N,M,t,b] at *; omega
  have hp := quadratic_forms_near_johnson_sharp k B F φ n 0 t
    (by omega) ht (by simpa using htn) hB ⊤ (by simpa [hD,hN]) (by simpa [hD] using hq)
  have hS : Finset.univ.filter (fun x:B=>x∈(⊤:Submodule k B))=Finset.univ := by simp
  dsimp only at hp
  simp only [Submodule.mem_top,Finset.filter_true,Finset.card_univ,Nat.sub_zero] at hp
  obtain ⟨f,g,hg,hfg,hf,hgap,hbad⟩ := hp
  have hL := quadratic_list_size_eq_natCast b n 0 t hb (by simpa using htn)
  simp only [Nat.sub_zero] at hL
  dsimp only [b,N,t,M] at hL
  rw [hL,Nat.floor_natCast] at hbad
  have hden : (0:ℚ)<(Fintype.card F:ℚ)-(N:ℚ):=by
    have hh : (N:ℚ)<Fintype.card F := by exact_mod_cast hq
    linarith
  have hδ : ((b-1:ℚ)*N/(b:ℚ)^(2*t))≤(b:ℚ)*N := by
    have hb1 : (1:ℚ)≤b:=by exact_mod_cast (by omega : 1≤b)
    calc
      _≤(b-1:ℚ)*N := div_le_self (by positivity) (one_le_pow₀ hb1)
      _≤(b:ℚ)*N := mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) (Nat.cast_nonneg N)
  have hnum : ((b-1:ℚ)*N/(b:ℚ)^(2*t))*(M.choose 2:ℚ)<(Fintype.card F:ℚ)-(N:ℚ) := by
    have hbound : ((b*N*M.choose 2:ℕ):ℚ)<(Fintype.card F:ℚ)-(N:ℚ) := by
      have hh : N+b*N*M.choose 2<Fintype.card F:=hcap
      have hhR : (N:ℚ)+(b*N*M.choose 2:ℕ)<(Fintype.card F:ℚ) := by exact_mod_cast hh
      linarith
    exact (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)).trans_lt
      (by simpa only [Nat.cast_mul] using hbound)
  have hfloor : ⌊(((b-1:ℚ)*N/(b:ℚ)^(2*t))*(M.choose 2:ℚ))/(Fintype.card F-N:ℚ)⌋₊=0 :=
    Nat.floor_eq_zero.mpr ((div_lt_one hden).mpr hnum)
  have hNdiv : N/b=b^(2*n-1) := by
    rw [hN]; simpa only [pow_one] using Nat.pow_div (show 1≤2*n by omega) (by omega : 0<b)
  have hTdiv : (b-1)*N/b^(t+1)=(b-1)*b^(2*n-t-1) := by
    rw [hN,Nat.mul_div_assoc _ (pow_dvd_pow b (by omega : t+1≤2*n)),
      Nat.pow_div (by omega) (by omega : 0<b)]
    simp only [Nat.sub_sub]
  change _ at hbad
  have hbad' : M≤(nonzeroBadChallenges (mappedDomain φ (Finset.univ.filter (fun x:B=>x∈(⊤:Submodule k B))))
      (N/b^2) f g (N/b-(b-1)*N/b^(t+1))).card := by
    change max (M-⌊(((b-1:ℚ)*N/(b:ℚ)^(2*t))*(M.choose 2:ℚ))/(Fintype.card F-N:ℚ)⌋₊) _ ≤ _ at hbad
    rw [hfloor,Nat.sub_zero] at hbad
    exact (le_max_left _ _).trans hbad
  dsimp only
  rw [←hS]
  refine ⟨f,g,hg,hfg,hf,?_,?_⟩
  · change ((b+1:ℚ)*N/(2*b^2)-1)<(b^(2*n-1)-(b-1)*b^(2*n-t-1):ℕ)
    change ((b+1:ℚ)*N/(2*b^2)-1)<(N/b-(b-1)*N/b^(t+1):ℕ) at hgap
    simpa only [hNdiv,hTdiv] using hgap
  · simpa only [hNdiv,hTdiv] using hbad'

/-- The remark after Theorem 5.22 for every fixed prime-power base: one pair
in a sufficiently large finite extension has quasipolynomially many nonzero
exceptional challenges and the two-sided fourth-root Johnson deficit. The
constants depend only on the scalar field and precede every ambient field. -/
theorem primePower_pairs_near_johnson
    (k : Type) [Field k] [Fintype k] :
    ∃ A c C : ℝ, 0<A ∧ 0<c ∧ 0<C ∧ ∃ n0 : ℕ,
      ∀ n : ℕ,n0≤n→∀ (B : Type) [Field B] [Fintype B] [Algebra k B],
        Fintype.card B=(Fintype.card k)^(2*n)→
        let b:=Fintype.card k
        let N:=Fintype.card B
        let K:=N/b^2
        ∃ T : ℕ,
          c*(N:ℝ)^(-(1/4:ℝ))≤1/(b:ℝ)-(T:ℝ)/N ∧
          1/(b:ℝ)-(T:ℝ)/N≤C*(N:ℝ)^(-(1/4:ℝ)) ∧
          ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
            letI:=fieldF
            letI:=finiteF
            ∃φ:B→+*F,∃f g:mappedDomain φ Finset.univ→F,
              agreementEQ (mappedDomain φ Finset.univ) K g K ∧
              commonAgreementEQ (mappedDomain φ Finset.univ) K f g K ∧
              agreementLE (mappedDomain φ Finset.univ) K f
                ⌊((b+1:ℚ)*N/(2*b^2)-1)⌋₊ ∧
              ((b+1:ℚ)*N/(2*b^2)-1)<T ∧
              (N:ℝ)^(A*Real.log N)≤
                (nonzeroBadChallenges (mappedDomain φ Finset.univ) K f g T).card := by
  let b:=Fintype.card k
  have hb : 2≤b:=Fintype.one_lt_card
  have hbR : (1:ℝ)<b:=by exact_mod_cast (by omega : 1<b)
  have hlog : 0<Real.log b:=Real.log_pos hbR
  refine ⟨1/(32*Real.log b),((b:ℝ)-1)/b,(b:ℝ)-1,
    by positivity,by positivity,by linarith,4,?_⟩
  intro n hn B _ _ _ hB
  let N:=Fintype.card B
  have hN : N=b^(2*n):=hB
  let M:=quadraticListCount b n 0 (n/2)
  let T:=b^(2*n-1)-(b-1)*b^(2*n-n/2-1)
  let cap:=N+b*N*M.choose 2
  obtain ⟨p,hchar,r,hprime,hqk⟩:=FiniteField.card' k
  let : CharP k p:=hchar
  let : CharP B p:=charP_of_injective_algebraMap' k p
  let : Fact p.Prime:=⟨hprime⟩
  let e:=cap+1
  let : NeZero e:=⟨by dsimp [e]; omega⟩
  let F:=FiniteField.Extension B p e
  let fieldF : Field F:=inferInstance
  let finiteF : Fintype F:=Fintype.ofFinite F
  let φ : B→+*F:=algebraMap B F
  have hF : Fintype.card F=N^e := by
    rw [←Nat.card_eq_fintype_card]
    exact (FiniteField.natCard_extension B p e).trans (by rw [Nat.card_eq_fintype_card])
  have hcap : cap<Fintype.card F := by
    rw [hF]
    exact (show cap<e by dsimp [e]; omega).trans (Nat.lt_pow_self (Fintype.one_lt_card (α:=B)))
  obtain ⟨f,g,hg,hfg,hf,hgap,hbad⟩:=primePower_middle_rank_pair_large_extension k B F φ n hn hB hcap
  have hfrac:=fullfield_agreement_fraction b n (n/2) hb (by omega) (Nat.div_le_self _ _)
  have hdef:=middle_rank_deficit_bounds b n hb
  have hM : b^(2*(n/2)*(n-n/2))≤M:=quadraticListCount_lower b n (n/2) hb
    (by omega) (Nat.div_le_self _ _)
  have hgrowth:=middle_rank_power_superpolynomial b n hb hn
  have hMR : (b:ℝ)^(2*(n/2)*(n-n/2))≤M:=by exact_mod_cast hM
  dsimp only
  refine ⟨T,?_,?_,F,fieldF,finiteF,φ,f,g,hg,hfg,hf,hgap,?_⟩
  · change (((b:ℝ)-1)/b)*(N:ℝ)^(-(1/4:ℝ))≤1/(b:ℝ)-(T:ℝ)/N
    rw [hN,Nat.cast_pow]
    dsimp only [T]
    rw [hfrac,sub_sub_cancel]
    exact hdef.1
  · change 1/(b:ℝ)-(T:ℝ)/N≤((b:ℝ)-1)*(N:ℝ)^(-(1/4:ℝ))
    rw [hN,Nat.cast_pow]
    dsimp only [T]
    rw [hfrac,sub_sub_cancel]
    exact hdef.2
  · have hbadR : (M:ℝ)≤(nonzeroBadChallenges (mappedDomain φ Finset.univ)
        (N/b^2) f g T).card:=by exact_mod_cast hbad
    have hgrowthN : (N:ℝ)^((1/(32*Real.log b))*Real.log N)≤M := by
      simpa only [N,hB,Nat.cast_pow] using hgrowth.trans hMR
    exact hgrowthN.trans hbadR

/-- The remark after Theorem 5.22: the fractional common-agreement gap is
exactly its limiting constant minus the middle-rank Johnson deficit. -/
theorem primePower_middle_rank_gap_identity (b n : ℕ) (hb : 2≤b) (hn : 2≤n) :
    ((b^(2*n-1)-(b-1)*b^(2*n-n/2-1):ℕ):ℝ)/(b:ℝ)^(2*n)-1/(b:ℝ)^2 =
      ((b:ℝ)-1)/(b:ℝ)^2-((b:ℝ)-1)/(b:ℝ)^(n/2+1) := by
  rw [fullfield_agreement_fraction b n (n/2) hb (by omega) (Nat.div_le_self _ _)]
  have hbpos : (0:ℝ)<b:=by exact_mod_cast (by omega : 0<b)
  field_simp
  ring

/-- The remark after Theorem 5.22: the fractional common-agreement gap
converges to `(b-1)/b²` for every fixed prime-power base, independently of
which sufficiently large extension supplies the received pair. -/
theorem primePower_middle_rank_common_gap_tendsto (b : ℕ) (hb : 2≤b) :
    Tendsto (fun n : ℕ=>
      ((b^(2*n-1)-(b-1)*b^(2*n-n/2-1):ℕ):ℝ)/(b:ℝ)^(2*n)-1/(b:ℝ)^2)
      atTop (𝓝 (((b:ℝ)-1)/(b:ℝ)^2)) := by
  have hbR : (1:ℝ)<b:=by exact_mod_cast (by omega : 1<b)
  have hindex : Tendsto (fun n : ℕ=>n/2+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [eventually_ge_atTop (2*a)] with n hn
    omega
  have hden : Tendsto (fun n : ℕ=>(b:ℝ)^(n/2+1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hbR).comp hindex
  have hdef : Tendsto (fun n : ℕ=>((b:ℝ)-1)/(b:ℝ)^(n/2+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hlim : Tendsto (fun n : ℕ=>((b:ℝ)-1)/(b:ℝ)^2-((b:ℝ)-1)/(b:ℝ)^(n/2+1))
      atTop (𝓝 (((b:ℝ)-1)/(b:ℝ)^2)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hdef
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (primePower_middle_rank_gap_identity b n hb hn).symm

/-- The examples in the remark after Theorem 5.22: bases four and three
have exactly the printed rates and limiting Johnson agreements. -/
theorem primePower_three_four_rate_examples :
    1/(4:ℝ)^2=1/16 ∧ 1/(4:ℝ)=1/4 ∧
    1/(3:ℝ)^2=1/9 ∧ 1/(3:ℝ)=1/3 := by norm_num

end BinaryFieldCounterexamples
