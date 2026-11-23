import ProximityPrize.SubmissionLower.Zzjdkoa
import ProximityPrize.SubmissionLower.ZhyMlza
set_option Elab.async false
namespace qJai0ob
noncomputable section
open Polynomial TrivSqZeroExt
open cu (L FX j9)

open P5_7_7 (phys)
open qkgz7gb (rV)
open P5_7_3_5_2 (Sheet atPolynomial)
open qziIa4d (scaledChart slope)
open qb0hmCe (SiteTarget cLN specialize zD)
open q1kuFjb (IntSeries Ua mapTwice map_liftAt)
open scoped WithZero
private abbrev τ:FX:=phys (Polynomial.X:L[X])
private theorem phys_ne {g:L[X]} (h:g≠0) :phys g≠0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).2 h
private theorem scalar_ne {b:L} (h:b≠0) :scalar b≠0:=phys_ne (C_ne_zero.mpr h)
private def center (x :L) :FX ≃+* FX :=
  IsFractionRing.ringEquivOfRingEquiv (taylorEquiv x).toRingEquiv
private theorem center_poly (x :L) (g:L[X]) :center x (phys g)=phys (taylor x g) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (taylorEquiv x).toRingEquiv g
private theorem center_eval (x :L) (f :L[X][X]) (y :L[X]) :
    center x (f.eval₂ phys (phys y)) =
      f.eval₂ (eval₂RingHom scalar (τ+scalar x)) (phys (taylor x y)) := by
  change (center x).toRingHom (f.eval₂ phys (phys y))= _
  rw [hom_eval₂,show (center x).toRingHom (phys y)=phys (taylor x y) from center_poly x y]
  congr 1
  apply ringHom_ext
  · intro c
    change center x (phys (C c))=(C c).eval₂ scalar (τ+scalar x)
    rw [center_poly,taylor_C,eval₂_C]
    rfl
  · change center x τ=(Polynomial.X (R:=L)).eval₂ scalar (τ+scalar x)
    rw [center_poly,taylor_X,map_add,eval₂_X]
    rfl
private def constant:L →+* IntSeries :=
  (LaurentSeries.powerSeriesEquivSubring L).toRingHom.comp PowerSeries.C
private theorem jet_constant (x :L) :seriesJet (constant x)=inl (scalar x) := by
  change seriesJet ((LaurentSeries.powerSeriesEquivSubring L) (PowerSeries.C x))= _
  rw [seriesJet_power,PowerSeries.constantCoeff_C,PowerSeries.coeff_C,ite_eq_right Nat.one_ne_zero,map_zero]
  exact TrivSqZeroExt.ext rfl rfl
private theorem jet_linear (P:PowerSeries L) (a b:L) :
    seriesJet (constant a+constant b*(LaurentSeries.powerSeriesEquivSubring L) P) =
      pair (scalar (a+b*PowerSeries.constantCoeff P)) (scalar (b*PowerSeries.coeff 1 P)) := by
  rw [map_add,map_mul,jet_constant,jet_constant,seriesJet_power]
  apply TrivSqZeroExt.ext <;>
    simp only [fst_add,snd_add,fst_mul,DualNumber.snd_mul,fst_inl,snd_inl,pair_fst,pair_snd,
      map_add,map_mul,zero_mul,add_zero,zero_add]
private theorem lift_equation {E :Type} [Field E] [Algebra L E]
    (η:E →ₐ[L] LaurentSeries L) (f G:E[X][X]) (hf hG)
    (x c a b:E) (x' c' a' b' : IntSeries) (n:ℕ)
    (hx : (x' : LaurentSeries L)=η x) (hc: (c' : LaurentSeries L)=η c)
    (ha : (a' : LaurentSeries L)=η a) (hb: (b' : LaurentSeries L)=η b)
    (h:scaledChart f x c a b=C (Polynomial.X^n)*G) :
    homogeneous f.natDegree (Ua η f hf) x' c' a' b' =
      C (Polynomial.X^n)*Ua η G hG:= by
  let ι:IntSeries →+* LaurentSeries L:=IntSeries.subtype
  apply Polynomial.map_injective (mapRingHom ι) (Polynomial.map_injective ι Subtype.val_injective)
  change mapTwice ι _=mapTwice ι _
  rw [cUQ ι Subtype.val_injective,map_mul,map_liftAt,map_liftAt]
  change homogeneous f.natDegree (mapTwice η.toRingHom f)
      (x' : LaurentSeries L) (c' : LaurentSeries L) (a' : LaurentSeries L) (b' : LaurentSeries L) =
      mapTwice ι (C (Polynomial.X^n))*mapTwice η.toRingHom G
  rw [hx,hc,ha,hb]
  change homogeneous f.natDegree (mapTwice η.toRingHom f)
      (η.toRingHom x) (η.toRingHom c) (η.toRingHom a) (η.toRingHom b)= _
  rw [← cUQ η.toRingHom η.injective]
  have hcX {A B:Type} [CommRing A] [CommRing B] (ψ:A →+* B) :
      mapTwice ψ (C (Polynomial.X^n))=C (Polynomial.X^n) := by
    simp only [mapTwice,coe_mapRingHom,map_C,Polynomial.map_pow,Polynomial.map_X]
  rw [hcX,show homogeneous f.natDegree f x c a b=scaledChart f x c a b from rfl,
    h,map_mul,hcX]
theorem transport:qziIa4d.c2 := by
  intro q Cq z S F V R T γ hγ hh
  let η:=F.atPlace γ (V.Bp hγ)
  let E :=Cq.E
  let z₀:=rV z γ R.coord
  let z₁:=F.direction γ R.coord
  let y :=(j9 (S γ)).eval R.center
  let A₀:=R.a+R.b*z₀
  let B₀:=R.c+R.d*z₀
  let A₁:=R.b*z₁
  let B₁:=R.d*z₁
  let s :=slope F R γ
  have hb:B₀≠0:=hh.1
  have hy :y*B₀=A₀:=hh.2
  have hs :A₁=B₁*y+B₀*s := by
    have hy' : y=A₀/B₀:=(eq_div_iff hb).2 hy
    change R.b*z₁=R.d*z₁*y+B₀*(-(R.det*z₁)/B₀^2)
    rw [hy']
    field_simp [hb]
    dsimp only [SiteTarget.det,A₀,B₀]
    ring
  let P:=taylor R.center (j9 (S γ))
  obtain ⟨H,hH⟩:Polynomial.X∣P - C y :=
    X_dvd_iff.mpr (by simp [P,y,taylor_coeff_zero])
  let Q:=H - C T.c
  have hH0:H.coeff 0=(j9 (S γ)).derivative.eval R.center := by
    have h:=congrArg (fun f :L[X]=>f.coeff 1) hH
    simpa only [P,coeff_sub,coeff_X_mul,taylor_coeff_one,coeff_C,ite_eq_right Nat.one_ne_zero,
      sub_zero] using h.symm
  have hQ:Q.coeff 0≠0:= by
    simpa only [Q,coeff_sub,coeff_C_zero,hH0,sub_ne_zero] using T.avoid γ hγ hh
  have hQv :phys Q≠0:=phys_ne (fun hz=>hQ (by simp [hz]))
  have hτ:τ≠0:=phys_ne X_ne_zero
  have hP:phys P=scalar y+τ*(phys Q+scalar T.c) := by
    have hp:P=C y+Polynomial.X*(Q+C T.c) := by
      dsimp only [Q]
      rw [sub_add_cancel,← hH]
      ring
    simpa only [map_add,map_mul,scalar,RingHom.comp_apply] using congrArg phys hp
  obtain ⟨arc,harc,hZ,_⟩:=F.arc γ (V.Bp hγ)
  have hZ' : PowerSeries.coeff 1 (arc R.coord)=z₁:= by
    dsimp only [z₁]
    rw [Sheet.direction,dite_eq_left (V.Bp hγ)]
    rw [show (F.atPlace γ (V.Bp hγ)) (Cq.seed R.coord) =
      (arc R.coord:LaurentSeries L) from harc _]
    exact (LaurentSeries.coeff_coe_powerSeries (arc R.coord) 1).symm
  let arc' := (LaurentSeries.powerSeriesEquivSubring L) (arc R.coord)
  let A:=constant R.a+constant R.b*arc'
  let B:=constant R.c+constant R.d*arc'
  have hAjet:seriesJet A=pair (scalar B₀*scalar y) (scalar B₁*scalar y+scalar B₀*scalar s) := by
    have ha :seriesJet A=pair (scalar A₀) (scalar A₁) := by
      simpa only [A,arc',A₀,A₁,hZ,hZ'] using jet_linear (arc R.coord) R.a R.b
    rw [ha,← hy,hs]
    simp only [map_add,map_mul,mul_comm (scalar y) (scalar B₀)]
  have hBjet:seriesJet B=pair (scalar B₀) (scalar B₁) := by
    simpa only [B,arc',B₀,B₁,hZ,hZ'] using jet_linear (arc R.coord) R.c R.d
  have hk (x :L) : (constant x :LaurentSeries L)=η (algebraMap L E x) := by
    change (((LaurentSeries.powerSeriesEquivSubring L) (PowerSeries.C x) :IntSeries) :LaurentSeries L)= _
    rw [LaurentSeries.powerSeriesEquivSubring_coe_apply,η.commutes,LaurentSeries.algebraMap_apply,
      PowerSeries.coe_C]
  let A' := algebraMap L E R.a+algebraMap L E R.b*Cq.seed R.coord
  let B' := algebraMap L E R.c+algebraMap L E R.d*Cq.seed R.coord
  have hA: (A:LaurentSeries L)=η A' := by
    simp only [A,A',Subring.coe_add,Subring.coe_mul,map_add,map_mul,hk,arc',
      LaurentSeries.powerSeriesEquivSubring_coe_apply,η,harc]
  have hB: (B:LaurentSeries L)=η B' := by
    simp only [B,B',Subring.coe_add,Subring.coe_mul,map_add,map_mul,hk,arc',
      LaurentSeries.powerSeriesEquivSubring_coe_apply,η,harc]
  have hf i j:=(F.value γ (V.Bp hγ) _).symm.trans_le (F.integral γ (V.Bp hγ) i j)
  have hG i j:=(F.value γ (V.Bp hγ) _).symm.trans_le (T.integral γ hγ hh i j)
  let f' := Ua η F.f hf
  let G' := Ua η T.G hG
  have hchart:homogeneous F.d f' (constant R.center) (constant T.c) A B =
      C (Polynomial.X^T.n)*G' :=
    lift_equation η F.f T.G hf hG _ _ A' B' _ _ _ _ T.n (hk _) (hk _) hA hB T.equation
  have hfdegree :f'.natDegree≤F.d:= by
    have hd₀: (mapTwice IntSeries.subtype f').natDegree=f'.natDegree :=
      natDegree_map_eq_of_injective (f :=mapRingHom IntSeries.subtype)
        (Polynomial.map_injective _ Subtype.val_injective) _
    have hd₁: (mapTwice η.toRingHom F.f).natDegree=F.d :=
      natDegree_map_eq_of_injective (f :=mapRingHom η.toRingHom)
        (Polynomial.map_injective _ η.injective) _
    rw [← hd₀,show mapTwice IntSeries.subtype f' = _ from map_liftAt η F.f hf,hd₁]
  let w:=1/phys Q
  let evF:=eval₂RingHom scalar (τ+scalar R.center)
  let evG:=eval₂RingHom scalar τ
  let J (i:ℤ) :=(cLN η i F.f).eval₂ evF (phys P)
  let I (i:ℤ) :=(cLN η i T.G).eval₂ evG w
  let j:=(cLN η 0 F.f).derivative.eval₂ evF (phys P)
  let i:=(cLN η 0 T.G).derivative.eval₂ evG w
  have hF₀:J 0=0:= by
    have hr :=F.root γ (V.Bp hγ)
    simpa only [atPolynomial,map_zero,center_eval,η,J,evF,P] using congrArg (center R.center) hr
  have hj:j≠0:= by
    have hr :=(center R.center).injective.ne (V.simple γ hγ)
    simpa only [atPolynomial,map_zero,center_eval,η,j,evF,P] using hr
  let φ:=phys (taylor R.center (V.num γ))/phys (taylor R.center (V.den γ))
  have hφ:φ = -(J 1/j) := by
    have hh' := congrArg (center R.center) (V.formula γ hγ)
    simpa only [φ,atPolynomial,map_neg,map_div₀,center_poly,center_eval,η,J,evF,P,j] using hh'
  have he (u:FX) :
      (inl τ:Dual)^T.n*pair (I 0) (I 1+u*i) =
        (seriesJet B*pair w u)^F.d *
          pair (J 0) (J 1+(scalar s-τ*(phys Q)^2*u)*j) := by
    let U:=pair w u
    let W:=pair (phys P) (scalar s-τ*(phys Q)^2*u)
    have hw:seriesJet B*inl τ +
        (seriesJet A+seriesJet B*seriesJet (constant T.c)*inl τ)*U =
        (seriesJet B*U)*W:= by
      rw [hAjet,hBjet,jet_constant]
      simpa only [U,W,w,← hP] using
        parameter_change τ (phys Q) (scalar y) (scalar T.c) (scalar B₀) (scalar B₁) (scalar s) u hQv
    have hv :=congrArg (evalAt seriesJet (inl τ) U) hchart
    rw [homogeneous_eval seriesJet (inl τ) U W F.d f' _ _ _ _ hfdegree hw,
      map_mul,evalAt_C_X_pow,jet_constant,← inl_add] at hv
    rw [show f' = Ua η F.f hf from rfl,show G' = Ua η T.G hG from rfl] at hv
    dsimp only [U,W] at hv
    rw [eval_seriesJet η T.G hG τ w u,eval_seriesJet] at hv
    exact hv.symm
  have hI₀:I 0=0:= by
    have h:=congrArg fst (he 0)
    simp only [fst_mul,fst_pow,fst_inl,pair_fst,hF₀,mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hτ)
  let m:=(scalar B₀*w)^F.d
  have hm:m≠0:=pow_ne_zero _ (mul_ne_zero (scalar_ne hb) (one_div_ne_zero hQv))
  have hsecond (u:FX) :
      τ^T.n*(I 1+u*i)=m*(J 1+(scalar s-τ*(phys Q)^2*u)*j) := by
    have h:=congrArg snd (he u)
    simpa only [← inl_pow,DualNumber.snd_mul,fst_inl,snd_inl,pair_fst,pair_snd,fst_pow,fst_mul,
      hBjet,hF₀,hI₀,mul_zero,zero_mul,add_zero] using h
  have hi_eq :τ^T.n*i = -(m*(τ*(phys Q)^2*j)) := by
    linear_combination hsecond 1 - hsecond 0
  have hi:i≠0:= by
    intro hz
    rw [hz,mul_zero,zero_eq_neg] at hi_eq
    exact mul_ne_zero hm (mul_ne_zero (mul_ne_zero hτ (pow_ne_zero _ hQv)) hj) hi_eq
  have hφ' : J 1 = -(φ*j) := by
    simpa only [neg_mul] using (div_eq_iff hj).mp (neg_eq_iff_eq_neg.mp hφ.symm)
  have htan : -(I 1/i)*(phys Q)^2 = -(φ-scalar s)/τ:= by
    field_simp [hi,hτ]
    apply mul_left_cancel₀ (pow_ne_zero T.n hτ)
    have hs₀:=hsecond 0
    rw [hφ'] at hs₀
    linear_combination -(τ*(phys Q)^2)*hs₀+(φ-scalar s)*hi_eq
  have heval :eval₂RingHom scalar τ=phys := by
    apply ringHom_ext
    · intro r
      exact eval₂_C _ _
    · exact eval₂_X _ _
  refine ⟨Q,hQ,?_,?_,?_⟩
  · simpa only [I,evG,heval,specialize,map_one,w] using hI₀
  · simpa only [i,evG,heval,specialize,map_one,w] using hi
  · simpa only [zD,I,i,evG,heval,specialize,map_one,w,φ,s,scalar,
      RingHom.comp_apply] using htan
end
end qJai0ob
