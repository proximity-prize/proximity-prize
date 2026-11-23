import ProximityPrize.SubmissionLower.Z8duOVc
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qX9S3Pd
noncomputable section
open Finset
open P5 (K)
open cu (L FX)
open gT (kM)
open Cu
open E7
open agN (O7 d4p emC
 gDD)
open qBajpRb (CurveRing incl cls incl_cls yq atMark_cls incl_injective)
open scoped WithZero
open private dc8 from ProximityPrize.SubmissionLower.Z3EWiUc
open private projection seed_transcendental from ProximityPrize.SubmissionLower.Z66Jm5b
open private UI.b7z from ProximityPrize.SubmissionLower.ZFFuWqa
open private card_support from ProximityPrize.SubmissionLower.ZBkbQJc
attribute [local instance] gRK
theorem principal {F:Type} [Field F] [Algebra L F] (hF:CurveField L F) :
  axV L F :=
 aFU.of_children bRt.proof bRu.proof _ _ hF
theorem seed_bounds (C₀:sQ) [hC:Fact (Irreducible C₀)] :
    (∃ i,Transcendental L (Wt C₀ i)) ∧
      CurveField L (oO C₀) ∧
      Gb L (oO C₀) (Wt C₀)≤C₀.totalDegree := by
  classical
  let E :=oO C₀
  let s :=Wt C₀
  let e :sQ →ₐ[L] E :=MvPolynomial.aeval s
  have hk :RingHom.ker e.toRingHom=auG C₀:= by
    ext q
    rw [RingHom.mem_ker]
    change MvPolynomial.aeval (Wt C₀) q=0↔q∈auG C₀
    rw [dc8,map_eq_zero_iff _ (IsFractionRing.injective (abz C₀) E),
      Ideal.Quotient.eq_zero_iff_mem]
  have hq:e C₀=0:=RingHom.mem_ker.mp (hk.symm ▸ Ideal.mem_span_singleton_self C₀)
  have hg:IntermediateField.adjoin L (Set.range s) = ⊤ := by
    have hm (a :abz C₀) :
        algebraMap (abz C₀) E a∈IntermediateField.adjoin L (Set.range s) := by
      obtain ⟨q,rfl⟩:=Ideal.Quotient.mk_surjective a
      apply IntermediateField.algebra_adjoin_le_adjoin L (Set.range s)
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨q,dc8 C₀ q⟩
    apply top_unique
    intro x _
    obtain ⟨a,b,_,rfl⟩:=IsFractionRing.div_surjective (abz C₀) x
    exact div_mem (hm a) (hm b)
  obtain ⟨i,hi⟩:=seed_transcendental C₀ hC.out s hk
  have hF:CurveField L E := by
    let a :Fin 2→L:=Pi.single i 1
    have ha :O7 a s=s i:= by
      simp [a,O7]
      rw [Algebra.smul_def,map_one,one_mul]
    exact ⟨s i,hi,ha ▸ (projection C₀ hC.out.ne_zero s hq hg a (ha.symm ▸ hi)).1⟩
  let hdiv :=principal hF
  obtain ⟨a,ha,_⟩:=d4p hdiv s
  have ht:0<Gb L E s :=(emC hF hdiv s).1 ⟨i,hi⟩
  have hh: (∑ᶠ v :CurvePlace L E,poleOrder v.value (O7 a s)) =
      Gb L E s :=finsum_congr ha
  have hz :=gDD (hh.symm ▸ ht)
  refine ⟨⟨i,hi⟩,hF,?_⟩
  change Gb L E s≤_
  rw [← hh,(hdiv _).2.2.2 hz]
  exact (projection C₀ hC.out.ne_zero s hq hg a hz).2
private theorem eval_place {B E :Type} [CommRing B] [Algebra L B] [Field E] [Algebra L E]
   (hF:CurveField L E) (j:B →ₐ[L] E) (hj:Function.Injective j) (φ:B →ₐ[L] L)
   (q:B) (hq:φ q=0) (hq0:j q≠0) :
   ∃ w:CurvePlace L E,∀ q,φ q=0↔w.value (j q)<1 := by
 let s :=algebraMap L B
 have hs :φ.toRingHom.comp s=RingHom.id L:=RingHom.ext φ.commutes
 obtain ⟨V,a,ha,hr⟩:=UI.b7z j.toRingHom φ.toRingHom s
   (fun y hy=> by
     have he :y=0:=hj (hy.trans (j.map_zero).symm)
     simp [he]) hs
 have hal (y :B) : (a y :E)=j y :=RingHom.congr_fun ha y
 have hker (y :B) :φ y=0↔a y∈IsLocalRing.maximalIdeal V:= by
   rw [← IsLocalRing.residue_eq_zero_iff]
   have hh:=RingHom.congr_fun hr y
   change IsLocalRing.residue V (a y)=((IsLocalRing.residue V).comp (a.comp s)) (φ y) at hh
   rw [hh,map_eq_zero_iff _ (RingHom.injective _)]
 have hproper :V ≠ ⊤ := by
   have hn: (a q:E)∈V.nonunits :=V.coe_mem_nonunits_iff.mpr ((hker q).mp hq)
   rw [hal,V.mem_nonunits_iff_or] at hn
   intro hV
   exact (hn.resolve_left hq0) (by rw [hV]; trivial)
 have hconstants (c:L) :algebraMap L E c∈V:= by
   rw [← j.commutes c]
   exact hal (s c) ▸ (a (s c)).property
 obtain ⟨w,hw⟩:=bRv.proof L E hF V hproper hconstants
 subst V
 refine ⟨w,fun y=>(hker y).trans ?_⟩
 rw [← hal y]
 exact w.value.mem_maximalIdeal_iff
variable {C₀:sQ} [Fact (Irreducible C₀)] {J:Ideal kM}
 {g n:ℕ} {R:wJ C₀ J g} (A:yI R n)
private theorem incl_constant (c:L) :
  incl A (algebraMap L (CurveRing A) c)=algebraMap L (oO C₀) c:= by
 change incl A (cls A (MvPolynomial.C c))= _
 rw [incl_cls]
 exact MvPolynomial.eval₂Hom_C _ _ _
private theorem incl_seed (i:Fin 2) :
  incl A (cls A (MvPolynomial.X (Sum.inl i)))=Wt C₀ i:= by
 rw [incl_cls]
 exact MvPolynomial.eval₂Hom_X' (zT C₀) _ (Sum.inl i)
private theorem transcendental_sub_const {E :Type} [Field E] [Algebra L E] {x :E}
  (hx :Transcendental L x) (a :L) :x-algebraMap L E a≠0:= by
 intro h
 have he :=sub_eq_zero.mp h
 rw [he] at hx
 exact hx (isAlgebraic_algebraMap a)
private theorem mark_place (hF:CurveField L (oO C₀)) {i:Fin 2}
   (hi:Transcendental L (Wt C₀ i)) {z :K} {t:Fin n→L}
   (h:aCn z t∈MvPolynomial.zeroLocus FX (EF A)) :
   ∃ w:CurvePlace L (oO C₀),
     ∀ q,yq A z t h q=0↔w.value (incl A q)<1 := by
 let φ:=yq A z t h
 let s :=algebraMap L (CurveRing A)
 have hs :φ.toRingHom.comp s=RingHom.id L:=RingHom.ext φ.commutes
 let x :=cls A (MvPolynomial.X (Sum.inl i))
 let q:=x - s (φ x)
 have hq:φ q=0:= by
   rw [show φ q=φ x-(φ.toRingHom.comp s) (φ x) from φ.map_sub _ _,hs]
   exact sub_self _
 have hq0:incl A q≠0:= by
   change incl A (cls A (MvPolynomial.X (Sum.inl i))-algebraMap L (CurveRing A) (φ x))≠0
   rw [(incl A).map_sub,incl_constant,incl_seed]
   exact transcendental_sub_const (E :=oO C₀) hi (φ x)
 let j:CurveRing A →ₐ[L] oO C₀:=⟨incl A,incl_constant A⟩
 exact eval_place hF j (incl_injective A) φ q hq hq0
theorem bYX (hF:CurveField L (oO C₀)) {i:Fin 2}
   (hi:Transcendental L (Wt C₀ i))
   (V:Finset K) (z :K→K) (t:K→Fin n→L)
   (hV : ∀ γ∈V,aCn (z γ) (t γ)∈MvPolynomial.zeroLocus FX (EF A))
   (hz :Set.InjOn z (V:Set K)) {q:CurveRing A} (hq:q≠0)
   (hcut : ∀ γ (hγ:γ∈V),yq A (z γ) (t γ) (hV γ hγ) q=0) :
   V.card ≤ ∑ᶠ w:CurvePlace L (oO C₀),poleOrder w.value (incl A q) := by
 classical
 let E :=oO C₀
 let φ (γ:V) :=yq A (z γ) (t γ) (hV γ γ.property)
 choose w hw using fun γ:V=>mark_place A hF hi (hV γ γ.property)
 have hinj:Function.Injective w:= by
   intro γ δ he
   let x :=cls A (MvPolynomial.X (Sum.inl (0:Fin 2)))
   let b:=x-algebraMap L (CurveRing A) (φ γ x)
   have hb:φ γ b=0:= by simp [b]
   have hd:φ δ b=0:=(hw δ b).2 (he ▸ (hw γ b).1 hb)
   have hval :φ δ x=φ γ x :=sub_eq_zero.mp (by simpa only [b,map_sub,
     AlgHom.commutes,Algebra.algebraMap_self_apply] using hd)
   have hfirst (η:V) :φ η x=algebraMap K L (z η) := by
     change yq A (z η) (t η) (hV η η.property) (cls A (MvPolynomial.X (Sum.inl 0)))= _
     rw [atMark_cls,MvPolynomial.eval_X]
     rfl
   rw [hfirst,hfirst] at hval
   apply Subtype.ext
   apply hz γ.property δ.property
   apply (algebraMap K L).injective
   exact hval.symm
 have hdiv :=principal hF (incl A q)
 have hn:incl A q≠0:=(incl_injective A).ne (by simpa using hq)
 rw [hdiv.2.2.1]
 simpa using (card_support (univ :Finset V) w (fun v=>KB v.value (incl A q))
   hinj.injOn hdiv.2.1 (fun γ _=> by
     have hlt:=(hw γ q).mp (hcut γ γ.property)
     have hlog:=(WithZero.log_lt_log ((w γ).value.ne_zero_iff.mpr hn) one_ne_zero).mpr hlt
     rw [WithZero.log_one] at hlog
     change 0<(-WithZero.log ((w γ).value (incl A q))).toNat
     omega))
end
end qX9S3Pd
