import ProximityPrize.SubmissionLower.ZpAvArb
import ProximityPrize.SubmissionLower.ZIAMiic
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace qmpFDTd
noncomputable section
open E7 (CurveField CurvePlace poleOrder)
open XX (EO aoG adp)
open aKx
open private cNx from ProximityPrize.SubmissionLower.V

open qBajpRb (yq atMark_cls cls incl CurveRing)
open private mark_place incl_constant from ProximityPrize.SubmissionLower.ZIAMiic
open cu (L)
open P5 (K)
open scoped Polynomial WithZero qvWbALd
private theorem bu6 {k F:Type} [Field k] [IsAlgClosed k] [Field F]
    [Algebra k F] (hF:CurveField k F) (w:CurvePlace k F) {x :F}
    (hx :1<w.value x) :Module.Finite k (EO w) := by
  have ht:Transcendental k x := by
    by_contra h
    obtain ⟨c,rfl⟩:=cNx h
    obtain rfl | hc:=eq_or_ne c 0
    · simp at hx
    · rw [w.on_constants c hc] at hx
      exact (lt_irrefl _ hx)
  have hti:Transcendental k x⁻¹:= fun h=>ht (IsAlgebraic.inv_iff.mp h)
  obtain ⟨t,htt,hft⟩:=hF
  let E :=IntermediateField.adjoin k ({x⁻¹} : Set F)
  let:Algebra k[X] F:=adp x⁻¹
  let:Algebra k[X] E :=bql x⁻¹ hti
  have :IsFractionRing k[X] E :=(bqn hti).1
  have :IsScalarTower k[X] E F:=(bqn hti).2
  have :Module.Finite E F:=b3a htt hft hti
  have hn:=b29 k[X] E F (cch k)
  have hw:poleOrder w.value x≠0:= by
    have h:=(WithZero.log_lt_log one_ne_zero (zero_lt_one.trans hx).ne').2 hx
    rw [WithZero.log_one] at h
    change (WithZero.log (w.value x)).toNat≠0
    omega
  exact (aZc.proof k F x ht (b3a htt hft ht) hn).2.1 w hw
private theorem local_data {k F:Type} [Field k] [IsAlgClosed k] [Field F]
    [Algebra k F] (hF:CurveField k F) (w:CurvePlace k F) :
    ∃ (ρ:w.value.valuationSubring →+* k) (π:w.value.valuationSubring),
      (∀ c,ρ (aoG w c)=c)∧w.value (π:F)=WithZero.exp (-1) ∧
      RingHom.ker ρ=Ideal.span {π} := by
  let v :=w.value
  let A:=v.valuationSubring
  obtain ⟨x,hx⟩:=w.normalized (WithZero.exp 1)
  change v x= _ at hx
  have hpos :1<v x :=hx ▸ (WithZero.one_lt_exp_iff.mpr (by decide : (0:ℤ)<1))
  have :=bu6 hF w hpos
  let e :=RingEquiv.ofBijective (algebraMap k (EO w))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k :=k) (K:=EO w))
  let ρ:=e.symm.toRingHom.comp (IsLocalRing.residue A)
  have hρ (c:k) :ρ (aoG w c)=c:=e.symm_apply_apply c
  have hx' : v x⁻¹=WithZero.exp (-1) := by rw [map_inv₀,hx,WithZero.exp_neg]
  let π:A:=⟨x⁻¹,hx'.trans_le (by simp)⟩
  refine ⟨ρ,π,hρ,hx',?_⟩
  rw [IsLocalRing.ker_eq_maximalIdeal ρ (fun c=>⟨aoG w c,hρ c⟩)]
  apply le_antisymm
  · intro a ha
    have hlt:v (a :F)<1 :=v.mem_maximalIdeal_iff.mp ha
    have hle :v (a :F)≤WithZero.exp (-1) := by
      apply (WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero).mp
      simpa only [← WithZero.exp_add,neg_add_cancel,WithZero.exp_zero] using hlt
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨⟨(a :F)*x,?_⟩,?_⟩
    · change v ((a :F)*x)≤1
      rw [map_mul,hx]
      calc
        _≤WithZero.exp (-1)*WithZero.exp 1 :=mul_le_mul' hle le_rfl
        _ = _:= by rw [← WithZero.exp_add,neg_add_cancel,WithZero.exp_zero]
    · apply Subtype.ext
      change (a :F)*x*x⁻¹=a
      rw [mul_assoc,mul_inv_cancel₀ (v.ne_zero_iff.mp (hx.trans_ne WithZero.exp_ne_zero)),mul_one]
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact v.mem_maximalIdeal_iff.mpr (hx'.trans_lt (by simp))
private theorem evaluations_equal {k B:Type} [Field k] [CommRing B] [Algebra k B]
    {φ ψ:B →ₐ[k] k} (h : ∀ q,φ q=0↔ψ q=0) :φ=ψ:= by
  apply AlgHom.ext
  intro q
  have hq:φ (q-algebraMap k B (φ q))=0:= by simp
  have he :=(h _).mp hq
  have he' : ψ q-φ q=0:= by simpa only [map_sub,AlgHom.commutes,
    Algebra.algebraMap_self_apply] using he
  exact (sub_eq_zero.mp he').symm
private theorem lift_mark {k F B:Type} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    [CommRing B] [Algebra k B] (hF:CurveField k F) (j:B →ₐ[k] F) (φ:B →ₐ[k] k)
    (w:CurvePlace k F) (hw : ∀ q,φ q=0↔w.value (j q)<1) :
    ∃ (lift:B →+* w.value.valuationSubring) (ρ:w.value.valuationSubring →+* k)
      (π:w.value.valuationSubring),
      w.value.valuationSubring.toSubring.subtype.comp lift=j.toRingHom ∧
      ρ.comp lift=φ.toRingHom∧w.value (π:F)=WithZero.exp (-1) ∧
      RingHom.ker ρ=Ideal.span {π} := by
  have hb (q:B) :φ (q-algebraMap k B (φ q))=0:= by simp
  have hle (q:B) :w.value (j q)≤1 := by
    have hs :=(hw _).mp (hb q)
    rw [map_sub,AlgHom.commutes] at hs
    calc
      _=w.value (j q-algebraMap k F (φ q)+algebraMap k F (φ q)) :=
        congrArg w.value (sub_add_cancel _ _).symm
      _≤1 :=w.value.map_add_le hs.le (aoG w (φ q)).property
  let lift:=j.toRingHom.codRestrict w.value.valuationSubring.toSubring hle
  obtain ⟨ρ,π,hρ,hπ,hker⟩:=local_data hF w
  refine ⟨lift,ρ,π,RingHom.ext fun _=>rfl,?_,hπ,hker⟩
  have hr :RingHom.ker ρ=IsLocalRing.maximalIdeal w.value.valuationSubring :=
    IsLocalRing.ker_eq_maximalIdeal _ (fun c=>⟨aoG w c,hρ c⟩)
  apply RingHom.ext
  intro q
  change ρ (lift q)=φ q
  have hc:lift (algebraMap k B (φ q))=aoG w (φ q) :=Subtype.ext (j.commutes _)
  have hn:ρ (lift (q-algebraMap k B (φ q)))=0:= by
    apply RingHom.mem_ker.mp
    rw [hr]
    exact w.value.mem_maximalIdeal_iff.mpr ((hw _).mp (hb q))
  rw [lift.map_sub,ρ.map_sub,hc,hρ] at hn
  exact sub_eq_zero.mp hn
theorem proof :qvWbALd.c2 := by
  classical
  intro C₀ _ J H T z s S hF hz
  let B:=CurveRing S.bY
  let φ (γ:T) :=yq S.bY (z γ) (S.parameter γ) (S.onBase γ γ.property)
  obtain ⟨i,hi⟩:=(qX9S3Pd.seed_bounds C₀).1
  choose w hw using fun γ:T=>mark_place S.bY hF hi (S.onBase γ γ.property)
  have hinj:Function.Injective w:= by
    intro γ δ he
    have hφ:φ γ=φ δ:=evaluations_equal fun q =>
      (hw γ q).trans (he ▸ (hw δ q).symm)
    let q:=cls S.bY (MvPolynomial.X (Sum.inl (0:Fin 2)))
    have hval :φ γ q=φ δ q:=congrArg (fun f :B →ₐ[L] L=>f q) hφ
    have hfirst (η:T) :φ η q=algebraMap K L (z η) := by
      change yq S.bY (z η) (S.parameter η) (S.onBase η η.property)
        (cls S.bY (MvPolynomial.X (Sum.inl 0)))= _
      rw [atMark_cls,MvPolynomial.eval_X]
      rfl
    rw [hfirst,hfirst] at hval
    exact Subtype.ext (hz γ.property δ.property ((algebraMap K L).injective hval))
  let j:B →ₐ[L] Cu.oO C₀:=⟨incl S.bY,incl_constant S.bY⟩
  choose lift ρ π hl hs hp hk using fun γ:T=>lift_mark hF j (φ γ) (w γ) (hw γ)
  exact ⟨⟨w,hinj,lift,hl,ρ,hs,π,hp,hk⟩⟩
end
end qmpFDTd
