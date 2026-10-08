/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.EllipticType
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Perfect
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.LevelCountArithmetic
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.AffineQuadraticShift
/-!
# Affine quadratic level sets and elliptic zero sets

Supporting the level-set necessity remark after Corollary 5.23, with actual
finite-field quadratic forms and affine quadratic functions.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open Module
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]
/-- The level-set discussion after Corollary 5.23: an anisotropic plane
over a finite field has nondegenerate polar form in every characteristic. -/
theorem anisotropic_plane_polar_ker_bot (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (ha : Q.Anisotropic) (hd : Module.finrank k V=2) :
    Q.polarBilin.ker=⊥ := by
  apply bot_unique
  intro u hu
  change u=0
  by_cases hQu : Q u=0
  · exact ha u hQu
  · have huu : Q.polarBilin u u=0:=congrArg (fun L:V→ₗ[k]k=>L u) hu
    rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self,two_nsmul,←two_mul] at huu
    have htwo : (2:k)=0 := (mul_eq_zero.mp huu).resolve_right hQu
    have hp : p=2 := by
      have hpdiv : p∣2:=(CharP.cast_eq_zero_iff k p 2).mp (by simpa using htwo)
      have hple:=Nat.le_of_dvd (by decide : 0<2) hpdiv
      have hpge:2≤p:=(Fact.out:p.Prime).two_le
      omega
    subst p
    have hall (x:V) : x∈Submodule.span k {u} := by
      obtain ⟨a,ha2⟩:=(frobeniusEquiv k 2).surjective (Q x/Q u)
      change a^2=Q x/Q u at ha2
      have hxu : Q.polarBilin x u=0:=
        (polar_symm Q x u).trans (congrArg (fun L:V→ₗ[k]k=>L x) hu)
      have hz : Q (x-a•u)=0 := by
        rw [sub_eq_add_neg,QuadraticMap.map_add Q,Q.map_neg,Q.map_smul,smul_eq_mul]
        change Q x+(a*a)*Q u+Q.polarBilin x (-(a•u))=0
        simp only [map_neg,map_smul,hxu,smul_zero,neg_zero,add_zero]
        rw [←pow_two,ha2,div_mul_cancel₀ _ hQu]
        have ht : (2:k)=0:=CharP.cast_eq_zero k 2
        linear_combination (Q x)*ht
      have he : x=a•u:=sub_eq_zero.mp (ha _ hz)
      exact Submodule.mem_span_singleton.mpr ⟨a,he.symm⟩
    have hspan : Submodule.span k {u}=⊤:=top_unique (fun x _=>hall x)
    have hu0 : u≠0:=by intro hh; exact hQu (hh ▸ Q.map_zero)
    have hdim:=finrank_span_singleton (K:=k) hu0
    rw [hspan,finrank_top,hd] at hdim
    omega

/-- The level-set discussion after Corollary 5.23: a radical-free quadratic
form of even dimension over a finite field has nondegenerate polar form. -/
theorem polar_ker_bot_of_even_radical_bot (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V) (hQ : Q.radical=⊥) (heven : Even (Module.finrank k V)) :
    Q.polarBilin.ker=⊥ := by
  generalize hd : Module.finrank k V=d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
    by_cases ha : Q.Anisotropic
    · have hdim:=QuadraticCoordinates.anisotropic_finrank_le_two p Q ha
      rw [hd] at hdim
      rw [hd] at heven
      obtain ⟨r,hr⟩:=heven
      have hc : d=0 ∨ d=2:=by omega
      rcases hc with h0|h2
      · have hcV : Fintype.card V=1:=by
          have hcV : Fintype.card V=(Fintype.card k)^(Module.finrank k V):=
            Module.card_eq_pow_finrank (K:=k)
          simpa [hd,h0] using hcV
        obtain ⟨x,hx⟩:=Fintype.card_eq_one_iff.mp hcV
        apply bot_unique
        intro u _
        exact (hx u).trans (hx 0).symm
      · exact anisotropic_plane_polar_ker_bot p Q ha (hd.trans h2)
    · change ¬∀x,Q x=0→x=0 at ha
      push Not at ha
      obtain ⟨x,hx,hne⟩:=ha
      obtain ⟨y,hy,hxy⟩:=exists_hyperbolic_partner Q x hx
        (singular_not_mem_polar_ker_of_radical_bot Q hQ x hx hne)
      let H:=hyperbolicComplement Q x y
      let QH:=Q.comp H.subtype
      have hH : QH.radical=⊥:=hyperbolicComplement_radical_bot Q hQ x y hx hy hxy
      have hdim : d=Module.finrank k H+2:=hd.symm.trans (hyperbolicComplement_finrank Q x y hx hy hxy)
      have heH : Even (Module.finrank k H) := by
        rw [hd] at heven
        obtain ⟨r,hr⟩:=heven
        refine ⟨r-1,?_⟩
        omega
      have hpH : QH.polarBilin.ker=⊥:=ih _ (by omega) QH hH heH rfl
      apply bot_unique
      intro u hu
      have huall (v:V) : Q.polarBilin u v=0:=congrArg (fun L:V→ₗ[k]k=>L v) hu
      have huH : u∈H:=⟨(polar_symm Q x u).trans (huall x),
        (polar_symm Q y u).trans (huall y)⟩
      have huHp : (⟨u,huH⟩:H)∈QH.polarBilin.ker := by
        ext v
        exact huall v
      rw [hpH] at huHp
      exact congrArg Subtype.val huHp

/-- The level-set discussion after Corollary 5.23: positive or zero even
quadratic rank makes the quadratic radical equal the polar kernel over a finite field. -/
theorem radical_eq_polar_ker_of_even_rank (p : ℕ) [Fact p.Prime] [CharP k p]
    (Q : QuadraticForm k V)
    (heven : Even (Module.finrank k V-Module.finrank k Q.radical)) :
    Q.radical=Q.polarBilin.ker := by
  apply le_antisymm QuadraticMap.radical_le_ker_polarBilin
  have heQ : Even (Module.finrank k (V⧸Q.radical)) := by
    rwa [radical_quotient_finrank]
  have hpQ:=polar_ker_bot_of_even_radical_bot p (Q.lift Q.radical le_rfl)
    (radical_lift_radical_eq_bot Q) heQ
  intro u hu
  have huq : (Submodule.Quotient.mk u:V⧸Q.radical)∈
      (Q.lift Q.radical le_rfl).polarBilin.ker := by
    ext v
    exact congrArg (fun L:V→ₗ[k]k=>L v) hu
  rw [hpQ] at huq
  exact (Submodule.Quotient.mk_eq_zero Q.radical).mp huq

/-- The level-set discussion after Corollary 5.23: the literal homogenization
of `Q(x)+L(x)+c`, used to count arbitrary affine quadratic level sets. -/
def affineHomogenizedQuadratic (Q : QuadraticForm k V) (L : V→ₗ[k]k) (c:k) :
    QuadraticForm k (V×k) :=
  Q.comp (LinearMap.fst k V k)+
    QuadraticMap.linMulLin (L.comp (LinearMap.fst k V k)) (LinearMap.snd k V k)+
    c•((QuadraticMap.sq (R:=k)).comp (LinearMap.snd k V k))

/-- The level-set discussion after Corollary 5.23: homogenization has its
actual quadratic-polynomial evaluation, without changing the received function. -/
theorem affineHomogenizedQuadratic_apply (Q : QuadraticForm k V) (L : V→ₗ[k]k)
    (c:k) (x:V) (z:k) :
    affineHomogenizedQuadratic Q L c (x,z)=Q x+L x*z+c*z^2 := by
  simp [affineHomogenizedQuadratic,QuadraticMap.sq,pow_two,smul_eq_mul]

noncomputable def affineHomogenized_nonzero_fiber_equiv
    (Q : QuadraticForm k V) (L : V→ₗ[k]k) (c z:k) (hz:z≠0) :
    {x:V // affineHomogenizedQuadratic Q L c (x,z)=0} ≃
      {y:V // Q y+L y+c=0} := by
  have hscale (x:V) : affineHomogenizedQuadratic Q L c (z•x,z)=
      z^2*(Q x+L x+c) := by
    rw [affineHomogenizedQuadratic_apply,Q.map_smul,L.map_smul]
    simp only [smul_eq_mul]
    ring
  refine { toFun:=fun x=>⟨z⁻¹•x.val,?_⟩
           invFun:=fun y=>⟨z•y.val,?_⟩
           left_inv:=?_
           right_inv:=?_ }
  · have he:=hscale (z⁻¹•x.val)
    rw [smul_inv_smul₀ hz,x.property] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hz)
  · rw [hscale,y.property,mul_zero]
  · intro x
    apply Subtype.ext
    exact smul_inv_smul₀ hz x.val
  · intro y
    apply Subtype.ext
    exact inv_smul_smul₀ hz y.val

/-- The level-set discussion after Corollary 5.23: the zero count of the
literal homogenization equals the old quadratic zeros plus `(b-1)` copies
of the actual affine quadratic zero fiber. -/
theorem affineHomogenizedQuadratic_zero_count (Q : QuadraticForm k V)
    (L : V→ₗ[k]k) (c:k) :
    Fintype.card {w:V×k // affineHomogenizedQuadratic Q L c w=0} =
      Fintype.card {x:V // Q x=0}+
        (Fintype.card k-1)*Fintype.card {x:V // Q x+L x+c=0} := by
  let R:=affineHomogenizedQuadratic Q L c
  let es : {w:V×k // R w=0} ≃ {w:k×V // R (w.2,w.1)=0} :=
    Equiv.subtypeEquiv (Equiv.prodComm V k) (fun _=>Iff.rfl)
  rw [Fintype.card_congr es,Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun z x=>R (x,z)=0)),Fintype.card_sigma]
  have hfiber (z:k) : Fintype.card {x:V // R (x,z)=0} =
      if z=0 then Fintype.card {x:V // Q x=0} else Fintype.card {x:V // Q x+L x+c=0} := by
    by_cases hz:z=0
    · subst z
      simp [R,affineHomogenizedQuadratic_apply]
    · rw [ite_eq_right hz]
      exact Fintype.card_congr (affineHomogenized_nonzero_fiber_equiv Q L c z hz)
  simp_rw [hfiber]
  rw [Finset.sum_ite]
  have heq : Finset.univ.filter (fun z:k=>z=0)={0}:=by ext z; simp
  have hne : Finset.univ.filter (fun z:k=>¬z=0)=Finset.univ.erase 0:=by ext z; simp
  rw [heq,hne]
  simp [Finset.card_erase_of_mem]

theorem homogenized_nonzero_level_radical_bot (Q:QuadraticForm k V)
    (hP:Q.polarBilin.ker=⊥) (a:k) (ha:a≠0) :
    (affineHomogenizedQuadratic Q 0 (-a)).radical=⊥ := by
  apply bot_unique
  rintro ⟨x,z⟩ hw
  have hx : x∈Q.polarBilin.ker := by
    ext y
    have hh:=congrArg (fun L:V×k→ₗ[k]k=>L (y,0)) hw.2
    simpa [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      affineHomogenizedQuadratic_apply] using hh
  rw [hP] at hx
  change x=0 at hx
  subst x
  have hz : z=0 := by
    have hw0:=hw.1
    simp only [affineHomogenizedQuadratic_apply,Q.map_zero,map_zero,zero_mul,
      zero_add,neg_mul,neg_eq_zero] at hw0
    have hz2 : z^2=0:=(mul_eq_zero.mp hw0).resolve_left ha
    exact (pow_eq_zero_iff (by decide : 2≠0)).mp hz2
  exact Prod.ext rfl hz

/-- The level-set discussion after Corollary 5.23: every nonzero level of an
even-dimensional form with nondegenerate polar form satisfies the exact
zero-fiber identity from odd-dimensional homogenization. -/
theorem nonzero_level_count_identity_of_polar_bot (p:ℕ) [Fact p.Prime] [CharP k p]
    (Q:QuadraticForm k V) (hP:Q.polarBilin.ker=⊥)
    (heven:Even (Module.finrank k V)) (a:k) (ha:a≠0) :
    Fintype.card {x:V // Q x=0}+(Fintype.card k-1)*Fintype.card {x:V // Q x=a}=
      (Fintype.card k)^(Module.finrank k V) := by
  let R:=affineHomogenizedQuadratic Q 0 (-a)
  have hR : R.radical=⊥:=homogenized_nonzero_level_radical_bot Q hP a ha
  have hodd : Odd (Module.finrank k (V×k)) := by
    rw [Module.finrank_prod,Module.finrank_self]
    obtain ⟨r,hr⟩:=heven
    refine ⟨r,by omega⟩
  have hz:=zero_card_of_radical_bot_odd p R hR hodd
  have hc:=affineHomogenizedQuadratic_zero_count Q 0 (-a)
  have hfiber : Fintype.card {x:V // Q x+(0:V→ₗ[k]k) x+ -a=0}=
      Fintype.card {x:V // Q x=a} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun x=>by
      simp only [LinearMap.zero_apply,add_zero,←sub_eq_add_neg,sub_eq_zero])
  rw [hfiber] at hc
  change Fintype.card {x:V×k // R x=0}=_ at hc
  rw [Module.finrank_prod,Module.finrank_self,Nat.add_sub_cancel] at hz
  exact hc.symm.trans hz

theorem nonzero_homogeneous_radical_iff (Q:QuadraticForm k V)
    (hP:Q.radical=Q.polarBilin.ker) (a:k) (ha:a≠0) (x:V) (z:k) :
    (x,z)∈(affineHomogenizedQuadratic Q 0 (-a)).radical ↔ x∈Q.radical ∧ z=0 := by
  constructor
  · intro hw
    have hx : x∈Q.polarBilin.ker := by
      ext y
      have hh:=congrArg (fun L:V×k→ₗ[k]k=>L (y,0)) hw.2
      simpa [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
        affineHomogenizedQuadratic_apply] using hh
    rw [←hP] at hx
    have hz:z=0 := by
      have hw0:=hw.1
      simp only [affineHomogenizedQuadratic_apply,hx.1,LinearMap.zero_apply,zero_mul,
        zero_add,neg_mul,neg_eq_zero] at hw0
      exact (pow_eq_zero_iff (by decide : 2≠0)).mp ((mul_eq_zero.mp hw0).resolve_left ha)
    exact ⟨hx,hz⟩
  · rintro ⟨hx,rfl⟩
    refine ⟨?_,?_⟩
    · simp [affineHomogenizedQuadratic_apply,hx.1]
    · apply LinearMap.ext
      intro w
      rcases w with ⟨y,s⟩
      have hh:=congrArg (fun L:V→ₗ[k]k=>L y) hx.2
      simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
        LinearMap.zero_apply] at hh ⊢
      rw [show (x,0)+(y,s)=(x+y,s) by simp]
      simp only [affineHomogenizedQuadratic_apply,add_zero,
        LinearMap.zero_apply,zero_mul,mul_zero,zero_pow (by decide : 2≠0)]
      linear_combination hh

/-- The level-set discussion after Corollary 5.23: any nonzero level of an
actual even-rank quadratic form obeys the exact fiber identity, including
forms with a nontrivial quadratic radical. -/
theorem nonzero_level_count_identity_of_even_rank (p:ℕ) [Fact p.Prime] [CharP k p]
    (Q:QuadraticForm k V) (heven:Even (Module.finrank k V-Module.finrank k Q.radical))
    (a:k) (ha:a≠0) :
    Fintype.card {x:V // Q x=0}+(Fintype.card k-1)*Fintype.card {x:V // Q x=a}=
      (Fintype.card k)^(Module.finrank k V) := by
  let R:=affineHomogenizedQuadratic Q 0 (-a)
  have hP:=radical_eq_polar_ker_of_even_rank p Q heven
  have hcrit:=nonzero_homogeneous_radical_iff Q hP a ha
  let e : R.radical≃ₗ[k]Q.radical :=
    { toFun:=fun w=>⟨w.val.1,(hcrit w.val.1 w.val.2).mp w.property |>.1⟩
      invFun:=fun x=>⟨(x.val,0),(hcrit x.val 0).mpr ⟨x.property,rfl⟩⟩
      left_inv:=by
        intro w
        apply Subtype.ext
        exact Prod.ext rfl ((hcrit w.val.1 w.val.2).mp w.property).2.symm
      right_inv:=by intro x; rfl
      map_add':=by intro x y; rfl
      map_smul':=by intro c x; rfl }
  have hrad : Module.finrank k R.radical=Module.finrank k Q.radical:=e.finrank_eq
  have hrank : Module.finrank k (V×k)-Module.finrank k R.radical =
      (Module.finrank k V-Module.finrank k Q.radical)+1 := by
    rw [hrad,Module.finrank_prod,Module.finrank_self]
    have hle:=Submodule.finrank_le Q.radical
    omega
  have hodd : Odd (Module.finrank k (V×k)-Module.finrank k R.radical) := by
    rw [hrank]
    obtain ⟨s,hs⟩:=heven
    refine ⟨s,by omega⟩
  have hz:=zero_card_of_odd_rank p R hodd
  rw [Nat.card_eq_fintype_card,Module.finrank_prod,Module.finrank_self,Nat.add_sub_cancel] at hz
  have hc:=affineHomogenizedQuadratic_zero_count Q 0 (-a)
  have hfiber : Fintype.card {x:V // Q x+(0:V→ₗ[k]k) x+ -a=0}=
      Fintype.card {x:V // Q x=a} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun x=>by
      simp only [LinearMap.zero_apply,add_zero,←sub_eq_add_neg,sub_eq_zero])
  rw [hfiber] at hc
  change Fintype.card {x:V×k // R x=0}=_ at hc
  exact hc.symm.trans hz

/-- The level-set discussion after Corollary 5.23: the elliptic-size affine
quadratic fiber forces even quadratic rank, in every characteristic and at
any rank compatible with the threshold. -/
theorem even_rank_of_affine_elliptic_level_count (p:ℕ) [Fact p.Prime] [CharP k p]
    (Q:QuadraticForm k V) (L:V→ₗ[k]k) (c:k) (t:ℕ)
    (hb:2<Fintype.card k) (ht:0<t) (htd:2*t≤Module.finrank k V)
    (hcount:Fintype.card {x:V // Q x+L x+c=0} =
      (Fintype.card k)^(Module.finrank k V-1)-
        (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V-t-1)) :
    Even (Module.finrank k V-Module.finrank k Q.radical) := by
  let b:=Fintype.card k
  let d:=Module.finrank k V
  let T:=b^(d-1)-(b-1)*b^(d-t-1)
  have hT:=elliptic_threshold_decomposition b d t hb ht htd
  dsimp only at hT
  obtain ⟨hCpos,hTsum,hTlt,hbase⟩:=hT
  change T+(b-1)*b^(d-t-1)=b^(d-1) at hTsum
  change T<b^(d-1) at hTlt
  rcases Nat.even_or_odd (Module.finrank k V-Module.finrank k Q.radical) with he|ho
  · exact he
  · exfalso
    let R:=affineHomogenizedQuadratic Q L c
    have hQzero:=zero_card_of_odd_rank p Q ho
    rw [Nat.card_eq_fintype_card] at hQzero
    change Fintype.card {x:V // Q x=0}=b^(d-1) at hQzero
    have hhom:=affineHomogenizedQuadratic_zero_count Q L c
    rw [hQzero,hcount] at hhom
    change Fintype.card {x:V×k // R x=0}=b^(d-1)+(b-1)*T at hhom
    have hdim : Module.finrank k (V×k)=d+1:=by simp [d,Module.finrank_prod]
    have hsmall : b^(d-1)+(b-1)*T≤b^d:=by nlinarith
    rcases Nat.even_or_odd (Module.finrank k (V×k)-Module.finrank k R.radical) with heR|hoR
    · obtain ⟨r,hr⟩:=heR
      have hrank : Module.finrank k (V×k)-Module.finrank k R.radical=2*r:=by omega
      by_cases hr0:r=0
      · have hRzero:=zero_card_of_rank_zero p R (by omega)
        rw [Nat.card_eq_fintype_card,hdim] at hRzero
        have hpow : b^d<b^(d+1):=Nat.pow_lt_pow_right (by omega) (by omega)
        change Fintype.card {x:V×k // R x=0}=b^(d+1) at hRzero
        omega
      · have hRzero:=zero_card_of_even_rank p R r (by omega) hrank
        rw [Nat.card_eq_fintype_card,hdim] at hRzero
        have he1:d+1-1=d:=by omega
        have he2:d+1-r-1=d-r:=by omega
        simp only [he1,he2] at hRzero
        change Fintype.card {x:V×k // R x=0}=b^d+(b-1)*b^(d-r) ∨
          Fintype.card {x:V×k // R x=0}=b^d-(b-1)*b^(d-r) at hRzero
        rcases hRzero with hplus|hminus
        · have hpos : 0<(b-1)*b^(d-r):=Nat.mul_pos (by omega) (pow_pos (by omega) _)
          omega
        · have hcorrle:(b-1)*b^(d-r)≤b^d := by
            calc
              _≤b*b^(d-r):=Nat.mul_le_mul_right _ (by omega)
              _=b^(d-r+1):=by rw [pow_succ']
              _≤b^d:=Nat.pow_le_pow_right (by omega) (by dsimp [d] at *; omega)
          have hRsum:Fintype.card {x:V×k // R x=0}+(b-1)*b^(d-r)=b^d := by
            rw [hminus]
            exact Nat.sub_add_cancel hcorrle
          have heq : b^(d-r)=(b-1)*b^(d-t-1) := by
            apply Nat.eq_of_mul_eq_mul_left (by omega : 0<b-1)
            nlinarith [congrArg (fun u:ℕ=>(b-1)*u) hTsum]
          exact power_ne_pred_mul_power b (d-r) (d-t-1) hb heq
    · have hRzero:=zero_card_of_odd_rank p R hoR
      rw [Nat.card_eq_fintype_card,hdim] at hRzero
      change Fintype.card {x:V×k // R x=0}=b^d at hRzero
      have hpred : 0<b-1:=by omega
      nlinarith


theorem elliptic_threshold_pos (b d t:ℕ) (hb:2<b) (ht:0<t) (htd:2*t≤d) :
    0<b^(d-1)-(b-1)*b^(d-t-1) := by
  have he:d-t-1+1≤d-1:=by omega
  have hc : (b-1)*b^(d-t-1)<b^(d-1) := by
    calc
      _<b*b^(d-t-1):=Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega) _)
      _=b^(d-t-1+1):=by rw [pow_succ']
      _≤b^(d-1):=Nat.pow_le_pow_right (by omega) he
  omega

/-- The level-set necessity remark after Corollary 5.23: over a field with
more than two elements, an elliptic-sized fiber of an even-rank quadratic
form is necessarily its zero fiber. -/
theorem elliptic_sized_quadratic_fiber_is_zero (p:ℕ) [Fact p.Prime] [CharP k p]
    (Q:QuadraticForm k V) (a:k) (t:ℕ)
    (hb:2<Fintype.card k) (ht:0<t) (htd:2*t≤Module.finrank k V)
    (heven:Even (Module.finrank k V-Module.finrank k Q.radical))
    (hc:Fintype.card {x:V // Q x=a} =
      (Fintype.card k)^(Module.finrank k V-1)-
        (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V-t-1)) : a=0 := by
  by_contra ha
  let b:=Fintype.card k
  let d:=Module.finrank k V
  let T:=b^(d-1)-(b-1)*b^(d-t-1)
  have hT:=elliptic_threshold_decomposition b d t hb ht htd
  dsimp only at hT
  obtain ⟨hCpos,hTsum,hTlt,hbase⟩:=hT
  change T+(b-1)*b^(d-t-1)=b^(d-1) at hTsum
  change T<b^(d-1) at hTlt
  have hTpos:=elliptic_threshold_pos b d t hb ht htd
  change 0<T at hTpos
  have hid:=nonzero_level_count_identity_of_even_rank p Q heven a ha
  rw [hc] at hid
  change Fintype.card {x:V // Q x=0}+(b-1)*T=b^d at hid
  obtain ⟨r,hr⟩:=heven
  have hrank:Module.finrank k V-Module.finrank k Q.radical=2*r:=by omega
  by_cases hr0:r=0
  · have hz:=zero_card_of_rank_zero p Q (by omega)
    rw [Nat.card_eq_fintype_card] at hz
    change Fintype.card {x:V // Q x=0}=b^d at hz
    have hp:0<(b-1)*T:=Nat.mul_pos (by omega) hTpos
    omega
  · have hz:=zero_card_of_even_rank p Q r (by omega) hrank
    rw [Nat.card_eq_fintype_card] at hz
    change Fintype.card {x:V // Q x=0}=b^(d-1)+(b-1)*b^(d-r-1) ∨
      Fintype.card {x:V // Q x=0}=b^(d-1)-(b-1)*b^(d-r-1) at hz
    rcases hz with hplus|hminus
    · have heq:b^(d-r-1)=(b-1)*b^(d-t-1) := by
        apply Nat.eq_of_mul_eq_mul_left (by omega : 0<b-1)
        nlinarith [congrArg (fun u:ℕ=>(b-1)*u) hTsum]
      exact power_ne_pred_mul_power b (d-r-1) (d-t-1) hb heq
    · have hcorrle:(b-1)*b^(d-r-1)≤b^(d-1) := by
        calc
          _≤b*b^(d-r-1):=Nat.mul_le_mul_right _ (by omega)
          _=b^(d-r-1+1):=by rw [pow_succ']
          _≤b^(d-1):=Nat.pow_le_pow_right (by omega) (by dsimp [d] at *; omega)
      have hsum:Fintype.card {x:V // Q x=0}+(b-1)*b^(d-r-1)=b^(d-1) := by
        rw [hminus]; exact Nat.sub_add_cancel hcorrle
      have hpowpos:0<b^(d-r-1):=pow_pos (by omega) _
      have hpred:0<b-1:=by omega
      nlinarith

/-- The level-set necessity remark after Corollary 5.23: an elliptic-sized
zero fiber forces the actual structural elliptic type, without assuming its
rank in advance. -/
theorem isElliptic_of_elliptic_sized_zero_fiber (p:ℕ) [Fact p.Prime] [CharP k p]
    (Q:QuadraticForm k V) (t:ℕ)
    (hb:2<Fintype.card k) (ht:0<t) (htd:2*t≤Module.finrank k V)
    (heven:Even (Module.finrank k V-Module.finrank k Q.radical))
    (hc:Fintype.card {x:V // Q x=0} =
      (Fintype.card k)^(Module.finrank k V-1)-
        (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V-t-1)) : IsElliptic Q := by
  let b:=Fintype.card k
  let d:=Module.finrank k V
  have hT:=elliptic_threshold_decomposition b d t hb ht htd
  dsimp only at hT
  obtain ⟨_,_,hTlt,_⟩:=hT
  obtain ⟨r,hr⟩:=heven
  have hrank:Module.finrank k V-Module.finrank k Q.radical=2*r:=by omega
  by_cases hr0:r=0
  · have hz:=zero_card_of_rank_zero p Q (by omega)
    rw [Nat.card_eq_fintype_card,hc] at hz
    have hbd:b^(d-1)≤b^d:=Nat.pow_le_pow_right (by omega) (by omega)
    change b^(d-1)-(b-1)*b^(d-t-1)=b^d at hz
    omega
  · have hz:=zero_card_of_even_rank p Q r (by omega) hrank
    rw [Nat.card_eq_fintype_card] at hz
    rcases hz with hplus|hminus
    · rw [hc] at hplus
      change b^(d-1)-(b-1)*b^(d-t-1)=b^(d-1)+(b-1)*b^(d-r-1) at hplus
      omega
    · apply (isElliptic_iff_zero_natCard p Q r (by omega) hrank).mpr
      rwa [Nat.card_eq_fintype_card]

/-- The level-set necessity remark after Corollary 5.23: for every finite
field of size greater than two, any affine quadratic level set of the stated
elliptic size is literally a translate of the zero set of an elliptic form.
The quadratic form and its rank are not replaced or assumed elliptic. -/
theorem affine_elliptic_level_set_is_translate (p:ℕ) [Fact p.Prime] [CharP k p]
    (Q:QuadraticForm k V) (L:V→ₗ[k]k) (c a:k) (t:ℕ)
    (hb:2<Fintype.card k) (ht:0<t) (htd:2*t≤Module.finrank k V)
    (hcount:Fintype.card {x:V // Q x+L x+c=a} =
      (Fintype.card k)^(Module.finrank k V-1)-
        (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V-t-1)) :
    ∃v:V, IsElliptic Q ∧ ∀x:V, (Q x+L x+c=a ↔ Q (x+v)=0) := by
  let b:=Fintype.card k
  let d:=Module.finrank k V
  let T:=b^(d-1)-(b-1)*b^(d-t-1)
  have hT:=elliptic_threshold_decomposition b d t hb ht htd
  dsimp only at hT
  obtain ⟨_,_,hTlt,hbase⟩:=hT
  have hzero:Fintype.card {x:V // Q x+L x+(c-a)=0}=T := by
    calc
      _=Fintype.card {x:V // Q x+L x+c=a}:=by
        apply Fintype.card_congr
        exact Equiv.subtypeEquivRight (fun x=>by constructor <;> intro h <;> linear_combination h)
      _=T:=hcount
  have heven:=even_rank_of_affine_elliptic_level_count p Q L (c-a) t hb ht htd hzero
  have hrad:=radical_eq_polar_ker_of_even_rank p Q heven
  have hL:∀u∈Q.polarBilin.ker,L u=0 := by
    intro u hu
    rw [←hrad] at hu
    by_contra hLu
    have hbalanced:=affineQuadratic_level_card_of_radical_direction Q L c a u hu hLu
    rw [hcount,Module.card_eq_pow_finrank (K:=k) (V:=V)] at hbalanced
    change b*T=b^d at hbalanced
    have hpow:b*b^(d-1)=b^d:=by
      rw [←pow_succ']; congr 1; omega
    nlinarith
  obtain ⟨v,hv⟩:=exists_polar_shift_of_vanishes_kernel Q L hL
  have hf:Fintype.card {x:V // Q x=a-c+Q v}=T := by
    rw [←Fintype.card_congr (affineQuadraticLevelShiftEquiv Q L c a v hv)]
    exact hcount
  have hs:=elliptic_sized_quadratic_fiber_is_zero p Q (a-c+Q v) t hb ht htd heven hf
  rw [hs] at hf
  have hell:=isElliptic_of_elliptic_sized_zero_fiber p Q t hb ht htd heven hf
  refine ⟨v,hell,?_⟩
  intro x
  have hpolar:Q.polarBilin v x=L x:=by rw [hv]
  have hadd:=QuadraticMap.map_add Q x v
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_comm] at hpolar
  constructor
  · intro h
    linear_combination h + hadd + hpolar + hs
  · intro h
    linear_combination h - hadd - hpolar - hs

end BinaryFieldCounterexamples.QuadraticGeometry
