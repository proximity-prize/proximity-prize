import ProximityPrize.SubmissionLower.Znc9Sbd
import ProximityPrize.SubmissionLower.Z6s7ala
set_option Elab.async false
open _root_ renaming Ideal.span → zye, Nat.cast_mul → z2R, Nat.cast_nonneg → zqJ, Nat.le_of_ble_eq_true → zjC, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.succ_pos → ztH
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace qRNngId
noncomputable section
open P6 (K p)
open P6_7_1 (Input Poles)
open q3rjQGe (AxisSection RectRateOK nativeSlope axisRate marks onCurves)
open cu (L aZ qD jz)
open gT (Ambient aQ)
open qHuUuEa (DescendedMarks persistent linear)
open pI (by6)
open YY (bAG xg Si by9
  aef a9E U7)
open Finset MvPolynomial
open scoped Classical BigOperators
open private cag c2p b1I diE from ProximityPrize.SubmissionLower.G
open private mix mix_zero ePj from ProximityPrize.SubmissionLower.ZzWMDba
open private aXY from ProximityPrize.SubmissionLower.A0
def c1 :Prop :=
  ∀ (q:Ideal Ambient) (f :aZ),bAG q→ Irreducible f →
    xg q=zye {f} → (∀ i,Module.Finite aQ (AxisSection q i)) →
    ∃ g:ℕ,0<g∧aef q=f.totalDegree*g ∧
      ∀ i,f.degreeOf i*g≤axisLength q i
def c2 :Prop :=
  ∀ (f :aZ) (CF:Finset K),Irreducible f →
    ¬ by9 (zye {f})→(∀ z∈CF,qD z f=0) →
    CF.card≤2*f.degreeOf 0*f.degreeOf 1
def c3:Prop :=qHuUuEa.c1
def c4 :Prop :=qHuUuEa.c2
private theorem total_le_axes {F:Type} [Field F] (Q:MvPolynomial (Fin 2) F) :
    Q.totalDegree≤Q.degreeOf 0+Q.degreeOf 1 := by
  apply Finset.sup_le
  intro m hm
  have h (i:Fin 2) :=le_degreeOf_of_mem_support i hm
  rw [aXY]
  exact Nat.add_le_add (h 0) (h 1)
private theorem degree_eq {f :aZ} (hf :f≠0) {Q:MvPolynomial (Fin 2) L}
    (h:zye {f} = zye {map U7 Q}) (i:Fin 2) :
    f.degreeOf i= Q.degreeOf i:= by
  have ha :=Ideal.span_singleton_eq_span_singleton.mp h
  have hQ:map U7 Q≠0:= by
    obtain ⟨u,hu⟩:=ha
    exact fun hz=>mul_ne_zero hf (Units.ne_zero u) (hu.trans hz)
  have mono {A B:aZ} (hAB:A∣B) (hB:B≠0) :A.degreeOf i≤B.degreeOf i:= by
    obtain ⟨S,rfl⟩:=hAB
    rw [degreeOf_mul_eq (left_ne_zero_of_mul hB) (right_ne_zero_of_mul hB)]
    exact Nat.le_add_right _ _
  have hm: (map U7 Q).degreeOf i= Q.degreeOf i:= by
    rw [degreeOf_eq_sup,support_map_of_injective Q U7.injective,degreeOf_eq_sup]
  rw [← hm]
  exact (mono ha.dvd_dvd.1 hQ).antisymm (mono ha.dvd_dvd.2 hf)
private theorem rated_descended (h3:c3) (h4 :c4) {x :Input} (P:Poles x)
    {T:Finset K} {J Q e H} (A:DescendedMarks x T J Q e H) (he :0<e)
    {d D z a b u v :ℚ} (hr :RectRateOK d D z a b)
    (hu:0≤u) (hv :0≤v) (hm: (e :ℚ)*Q.totalDegree≤u+v)
    (hD: (Q.totalDegree :ℚ)≤ min D (2*d))
    (direct : (T.card:ℚ)≤u+axisRate e*v) :
    (T.card:ℚ)≤z*u+a*v+b*H+e := by
  obtain ⟨_,_,_,_,ha,_,hz,hb,menu⟩:=hr
  have hH : (0:ℚ)≤H :=zqJ _
  have heQ: (0:ℚ)≤e :=zqJ _
  have hzu:u≤z*u:= by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1 :ℚ)≤z by linarith) hu
  have hZ:0≤z*u:=hu.trans hzu
  have hdir : (T.card:ℚ)-z*u≤axisRate e*v := by linarith only [direct,hzu]
  by_cases h:a<axisRate e
  · suffices h' : (T.card:ℚ)-z*u≤a*v+b*H+e by linarith only [h']
    have ht {s :ℚ} (hs : (T.card:ℚ)≤ s*H+e) : (T.card:ℚ)-z*u≤ s*H+e :=
      (sub_le_self _ hZ).trans hs
    have hn {s a₀:ℚ} (h₀:0≤a₀) (hza :a₀≤ min z a)
        (hs : (T.card:ℚ)≤a₀*((e :ℚ)*Q.totalDegree)+s*H+e)
        (rate :s*(axisRate e-a)/(axisRate e-a₀)≤b) :
        (T.card:ℚ)-z*u≤a*v+b*H+e := by
      have hx :=mul_le_mul_of_nonneg_left hm h₀
      have hy :=mul_le_mul_of_nonneg_right (hza.trans (min_le_left _ _)) hu
      apply mix (hza.trans (min_le_right _ _)) h hH heQ hdir _ rate
      linarith only [hx,hy,hs]
    rcases menu e he h with hp | ⟨rfl,hl⟩ | ⟨rfl,h₀,hq⟩ | ⟨he₃,g,c,W,M,hok,hs,hnat⟩
    · have heP:=(Nat.le_mul_of_pos_left _ A.plane_pos).trans_lt A.seed_lt
      exact mix_zero ha.le h hH heQ hdir (ht (persistent he heP A)) hp
    · exact mix_zero ha.le h hH heQ hdir (ht (linear A)) hl
    · exact hn (by norm_num) h₀ (h3 x P T J Q H A) hq
    · have hslope :nativeSlope Q.totalDegree e≤nativeSlope (min D (2*d)) e := by
        unfold nativeSlope
        exact add_le_add (add_le_add
          (div_le_div_of_nonneg_right hD (mul_nonneg (by norm_num) heQ)) le_rfl) le_rfl
      have hn0:0≤nativeSlope (min D (2*d)) e := by
        have hmin:=(Nat.cast_nonneg (α:=ℚ) Q.totalDegree).trans hD
        unfold nativeSlope
        positivity
      have hw:=(h4 x P T J Q e H g c W M A he₃ hok).trans
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hslope
          (mul_nonneg heQ (Nat.cast_nonneg _))) le_rfl) le_rfl)
      exact hn hn0 hs hw hnat
  · linarith only [hdir,mul_le_mul_of_nonneg_right (le_of_not_gt h) hv,mul_nonneg hb hH,heQ]
private theorem fTy (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    (x :Input) (P:Poles x) {q:Ideal Ambient} (geom:by6 q)
    (hfinit : ∀ i,Module.Finite aQ (AxisSection q i))
    {d D z a b:ℚ} (hr :RectRateOK d D z a b)
    (hA : ∀ i,(axisLength q i:ℚ)≤d) (hD: (aef q:ℚ)≤D) :
    ((marks x q).card:ℚ) ≤
      z*axisLength q 0+(a+1)*axisLength q 1+b*a9E q+aef q:= by
  let T:=marks x q
  have slice :bAG q:=⟨geom.1,geom.2.1,geom.2.2.1,geom.2.2.2.1⟩
  obtain ⟨f,hf,hproj,hpos,hdeg⟩:=GK.proof q slice
  obtain ⟨g,hg,hplane,haxes⟩:=h1 q f slice hf hproj hfinit
  have haxis (i:Fin 2) :f.degreeOf i≤axisLength q i :=
    (Nat.le_mul_of_pos_right _ hg).trans (haxes i)
  have himg: (T.image x.M.label).card=T.card :=
    card_image_of_injective _ (fun _ _ h=>sub_left_inj.mp h)
  have hroot : ∀ v∈T.image x.M.label,qD v f=0:= by
    intro v hv
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hv
    apply c2p (mem_filter.mp hγ).2
    rw [hproj]
    exact Ideal.mem_span_singleton_self f
  have hr' := hr
  obtain ⟨_,_,hDp,haD,ha,_,hz,hb,_⟩:=hr'
  have hp:aef q<p:= by exact_mod_cast hD.trans_lt hDp
  by_cases hc:by9 (xg q)
  · obtain ⟨Q,hQ,hQproj⟩:=hc
    have hd:=b1I f hf.ne_zero Q (hproj.symm.trans hQproj)
    have heq (i:Fin 2) :=degree_eq hf.ne_zero (hproj.symm.trans hQproj) i
    obtain ⟨e,he,hcurve,heD⟩:=ePj q Q slice geom.2.2.2.2 hQ hQproj
    have A:DescendedMarks x T (Si q) Q e (a9E q) :=
      ⟨filter_subset _ _,hcurve,hQ,hQproj,hd ▸ hpos,heD.trans_lt hp,
        fun _ hγ=>cag (mem_filter.mp hγ).2⟩
    have heg:e≤g:= by
      rw [hplane,hd] at heD
      exact Nat.le_of_mul_le_mul_left heD A.plane_pos
    have hmass (i:Fin 2) : (e :ℚ)*Q.degreeOf i≤axisLength q i:= by
      have hh:=(zBI (f.degreeOf i) heg).trans (haxes i)
      rw [heq i,Nat.mul_comm] at hh
      exact_mod_cast hh
    have hordinary : (Q.totalDegree :ℚ)≤D :=
      (Nat.cast_le.mpr (hd ▸ hdeg)).trans hD
    have htd: (Q.totalDegree :ℚ)≤(Q.degreeOf 0:ℚ)+Q.degreeOf 1 := by
      exact_mod_cast total_le_axes Q
    have hdouble : (Q.totalDegree :ℚ)≤2*d:= by
      have hj (i:Fin 2) : (Q.degreeOf i:ℚ)≤d:= by
        rw [← heq i]
        exact (Nat.cast_le.mpr (haxis i)).trans (hA i)
      linarith only [htd,hj 0,hj 1]
    have hdir :=cu.bqt p (f.degreeOf 0) (f.degreeOf 1)
      (by decide) f hf.ne_zero le_rfl ((f.degreeOf_le_totalDegree 0).trans_lt (hdeg.trans_lt hp))
      le_rfl ((T.image x.M.label).image jz) (by
        intro v hv
        obtain ⟨w,hw,rfl⟩:=mem_image.mp hv
        exact hroot w hw)
    rw [card_image_of_injective _ jz.injective,himg,heq 0,heq 1] at hdir
    have hdq: (T.card:ℚ)≤(Q.degreeOf 0:ℚ)+(p:ℚ)*Q.degreeOf 1 := by exact_mod_cast hdir
    have hes : (e :ℚ)≠0:=Nat.cast_ne_zero.mpr he.ne'
    have hdir' : (T.card:ℚ)≤axisLength q 0+axisRate e*axisLength q 1 := by
      have hle : (Q.degreeOf 0:ℚ)≤axisLength q 0:= by
        rw [← heq 0]
        exact Nat.cast_le.mpr (haxis 0)
      have hrate :0≤axisRate e :=div_nonneg (zqJ _) (zqJ _)
      have hmul :=mul_le_mul_of_nonneg_left (hmass 1) hrate
      rw [← mul_assoc,axisRate,div_mul_cancel₀ _ hes] at hmul
      exact hdq.trans (add_le_add hle hmul)
    have hm: (e :ℚ)*Q.totalDegree≤(axisLength q 0:ℚ)+axisLength q 1 := by
      calc
        _≤(e :ℚ)*((Q.degreeOf 0:ℚ)+Q.degreeOf 1) :=
          mul_le_mul_of_nonneg_left htd (zqJ _)
        _≤_:= by rw [mul_add]; exact add_le_add (hmass 0) (hmass 1)
    have hcount:=rated_descended h3 h4 P A he hr (zqJ _) (zqJ _)
      hm (le_min hordinary hdouble) hdir'
    have heqD: (e :ℚ)≤aef q :=
      Nat.cast_le.mpr ((Nat.le_mul_of_pos_left _ A.plane_pos).trans heD)
    linarith only [hcount,heqD,zqJ (α:=ℚ) (axisLength q 1)]
  · have hc' := h2 f (T.image x.M.label) hf (hproj ▸ hc) hroot
    rw [himg] at hc'
    have hcount: (T.card:ℚ)≤2*(f.degreeOf 0:ℚ)*f.degreeOf 1 := by exact_mod_cast hc'
    have hle :2*(f.degreeOf 0:ℚ)≤a :=
      (mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (haxis 0)).trans (hA 0))
        (by norm_num)).trans haD
    have hm:=mul_le_mul hle (Nat.cast_le.mpr (haxis 1)) (zqJ _) ha.le
    linarith only [hcount,hm,mul_nonneg (show 0≤z by linarith only [hz]) (Nat.cast_nonneg (axisLength q 0)),
      mul_nonneg hb (Nat.cast_nonneg (a9E q)),Nat.cast_nonneg (α:=ℚ) (axisLength q 1),
      Nat.cast_nonneg (α:=ℚ) (aef q)]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :q3rjQGe.c6:= by
  intro x P C d D z a b hr hA hD
  have hs :onCurves x C.toacW=C.qv.biUnion (marks x) := by
    ext γ
    constructor
    · intro h
      obtain ⟨hγ,q,hq,hm⟩:=mem_filter.mp h
      exact mem_biUnion.mpr ⟨q,hq,mem_filter.mpr ⟨hγ,hm⟩⟩
    · intro h
      obtain ⟨q,hq,hm⟩:=mem_biUnion.mp h
      exact mem_filter.mpr ⟨(mem_filter.mp hm).1,q,hq,(mem_filter.mp hm).2⟩
  have sumAxis (i:Fin 2) : ∑ q∈C.qv,axisLength q i=C.kd i:=rfl
  have sumSeed : ∑ q∈C.qv,aef q=C.toacW.cost 0:=rfl
  have sumY : ∑ q∈C.qv,a9E q=C.toacW.cost 1 :=rfl
  rw [hs]
  calc
    _ ≤ ∑ q∈C.qv,((marks x q).card:ℚ) :=diE _ _
    _ ≤ ∑ q∈C.qv,(z*axisLength q 0+(a+1)*axisLength q 1+b*a9E q+aef q) := by
      apply sum_le_sum
      intro q hq
      have hd (i:Fin 2) :axisLength q i≤C.kd i :=
        (sumAxis i) ▸ single_le_sum (f := fun q=>axisLength q i) (fun _ _=>Nat.zero_le _) hq
      have hp:aef q≤C.toacW.cost 0 :=
        sumSeed ▸ single_le_sum (f :=aef) (fun _ _=>Nat.zero_le _) hq
      exact fTy h1 h2 h3 h4 x P (C.geometric q hq) (C.finite_axis q hq) hr
        (fun i=>(Nat.cast_le.mpr (hd i)).trans (hA i)) ((Nat.cast_le.mpr hp).trans hD)
    _ = _:= by simp only [sum_add_distrib,← mul_sum,← Nat.cast_sum,sumAxis,sumSeed,sumY]
end
end qRNngId
end
section
set_option autoImplicit true
namespace qb8DdTc
open P6_7_3 (IntroIndex introCap)
open qUrGXob qtqUEwc
open qehP9ee (mixedCols)
open qJeTDGe (bbD)
open pI (weight)
open Finset
open scoped BigOperators
private structure kB where
  num :ℕ
  den:ℕ
  pos :0<den
private def kB.val (x :kB) :ℚ:=(x.num :ℚ)/(x.den:ℚ)
private def kB.zero :kB:=⟨0,1,Nat.one_pos⟩
private def kB.add (x y :kB) :kB :=
  ⟨x.num*y.den+y.num*x.den,x.den*y.den,Nat.mul_pos x.pos y.pos⟩
private def kB.scale (x :kB) (n:ℕ) :kB:=⟨x.num*n,x.den,x.pos⟩
private def kB.afu (x y :kB) :Prop :=x.num*y.den≤y.num*x.den
private def kB.maximum (x y :kB) :kB :=
  if x.num*y.den≤y.num*x.den then y else x
private theorem kB.val_zero :kB.zero.val=0:= by
  simp only [kB.val,kB.zero,Nat.cast_zero,zero_div]
private theorem kB.val_add (x y :kB) : (x.add y).val=x.val+y.val := by
  have hx : (x.den:ℚ)≠0:=(Nat.cast_pos.mpr x.pos).ne'
  have hy : (y.den:ℚ)≠0:=(Nat.cast_pos.mpr y.pos).ne'
  simp only [kB.val,kB.add,Nat.cast_add,z2R,div_add_div _ _ hx hy]
  rw [mul_comm (y.num :ℚ) (x.den:ℚ)]
private theorem kB.val_scale (x :kB) (n:ℕ) : (x.scale n).val=x.val*(n:ℚ) := by
  simp only [kB.val,kB.scale,z2R,div_mul_eq_mul_div]
private theorem kB.val_ite (p:Prop) [Decidable p] (x y :kB) :
    (if p then x else y).val=if p then x.val else y.val := by
  split <;> rfl
private theorem kB.cross_iff (x y :kB) :x.afu y↔x.val≤y.val := by
  rw [kB.val,kB.val,div_le_div_iff₀ (Nat.cast_pos.mpr x.pos) (Nat.cast_pos.mpr y.pos)]
  simp only [kB.afu,← z2R,Nat.cast_le]
private theorem kB.val_max (x y :kB) : (x.maximum y).val=max x.val y.val := by
  unfold kB.maximum
  split
  · rename_i h
    exact (max_eq_right ((kB.cross_iff x y).mp h)).symm
  · rename_i h
    exact (max_eq_left (le_of_not_ge (fun hxy=>h ((kB.cross_iff x y).mpr hxy)))).symm
private def kB.sumFin {n:ℕ} (f :Fin n→kB) :kB :=
  (List.ofFn f).foldr kB.add kB.zero
private theorem kB.val_sumFin {n:ℕ} (f :Fin n→kB) :
    (kB.sumFin f).val = ∑ i,(f i).val := by
  have h (xs :List kB) : (xs.foldr kB.add kB.zero).val=(xs.map kB.val).sum:= by
    induction xs with
    | nil=>exact kB.val_zero
    | cons x xs ih=>simp only [List.foldr_cons,List.map_cons,List.sum_cons,kB.val_add,ih]
  rw [kB.sumFin,h,← List.ofFn_comp',List.sum_ofFn]
private theorem accStage (s :bAL) (k :Fin 4) :
    bbD stageDual s k =
      (if (10 :bAL)≤ s then stageDual 10 k else 0) +
      (if (11 :bAL)≤ s then stageDual 11 k else 0) := by
  unfold bbD
  calc
    _ = ∑ i:bAL,((if i=10 then if i≤ s then stageDual i k else 0 else 0) +
        (if i=11 then if i≤ s then stageDual i k else 0 else 0)) := by
      apply sum_congr rfl
      intro i _
      by_cases h₁:i=10
      · subst i
        simp only [ite_true,ite_eq_right (show (10 :bAL)≠11 by decide),add_zero]
      by_cases h₂:i=11
      · simp only [ite_eq_right h₁,ite_eq_left h₂,zero_add]
      simp only [ite_eq_right h₁,ite_eq_right h₂,stageDual,Pi.zero_apply,ite_self,add_zero]
    _ = _:= by simp [sum_add_distrib]
private def residue (o:IntroIndex) (k :Fin 4) :kB :=
  ⟨residualN o k,residualD o k+1,ztH _⟩
private def stage10 (k :Fin 4) :kB :=
  if k=0 then ⟨0x6d9abd44445f3,125,by decide⟩ else kB.zero
private def stage11 (k :Fin 4) :kB :=
  if k=0 then ⟨0x5c7620ab2b933,100,by decide⟩ else kB.zero
private def free (o:IntroIndex) (k :Fin 4) :kB :=
  if o=0 then
    ![⟨0xbd57b98b8bff5,250,by decide⟩,⟨0xaae506b9f98,25,by decide⟩,
      ⟨0xed04b4a9275,200,by decide⟩,kB.zero] k
  else kB.zero
private theorem stage10_val (k :Fin 4) : (stage10 k).val=stageDual 10 k := by
  fin_cases k <;> first | rfl | exact kB.val_zero
private theorem stage11_val (k :Fin 4) : (stage11 k).val=stageDual 11 k := by
  fin_cases k <;> first | rfl | exact kB.val_zero
private theorem free_val (o:IntroIndex) (k :Fin 4) : (free o k).val=freeDual o k := by
  by_cases h:o=0
  · subst o
    fin_cases k <;> first | rfl | exact kB.val_zero
  · simp only [free,freeDual,ite_eq_right h,Pi.zero_apply,kB.val_zero]
private def right (o:IntroIndex) (s :bAL) (k :Fin 4) :kB :=
  (((if (10 :bAL)≤ s then stage10 k else kB.zero).add
     (if (11 :bAL)≤ s then stage11 k else kB.zero)).add
     (if moveStart≤ s then free o k else kB.zero)).add (residue o k)
private theorem right_val (o:IntroIndex) (s :bAL) (k :Fin 4) :
    (right o s k).val=envelopePrice o s k := by
  simp only [right,envelopePrice,accStage,kB.val_add,kB.val_ite,kB.val_zero,
    stage10_val,stage11_val,free_val]
  rfl
private def left (o:IntroIndex) (t:Trial) (k :Fin 4) :kB :=
  let d₀:kB:=⟨dN o t,dD o t+1,ztH _⟩
  let g:kB:=⟨P6.p+1,55,by decide⟩
  let b₀:kB:=⟨bN o t,bD o t+1,ztH _⟩
  ((d₀.maximum g).scale (weight (aHp t) 0 k)).add (b₀.scale (weight (aHp t) 1 k))
private theorem left_val (o:IntroIndex) (t:Trial) (k :Fin 4) :
    (left o t k).val=stopPrice a b o t.succ k := by
  simp only [left,kB.val_add,kB.val_max,kB.val_scale]
  rfl
set_option maxHeartbeats 5000000 in
private theorem moveCheck (o:IntroIndex) (t:Trial) (k :Fin 4) :
    (left o t k).afu (right o t.succ k) := by
  fin_cases o <;> fin_cases t <;> fin_cases k <;>
    exact zjC (by with_unfolding_all rfl)
private theorem movingCovered (o:IntroIndex) (t:Trial) (k :Fin 4) :
    stopPrice a b o t.succ k≤envelopePrice o t.succ k := by
  rw [← left_val,← right_val]
  exact (kB.cross_iff _ _).mp (moveCheck o t k)
private def cap (o:IntroIndex) (k :Fin 4) :ℕ :=
  min (mixedNat (introCap o.val) (originShape o) k) (base k)
private theorem cap_val (o:IntroIndex) (k :Fin 4) :
    min (originBox o k) (initialBound k)=(cap o k :ℚ) := by
  rw [cap,Nat.cast_min,mixedNat_cast,initial_values]
  rfl
private abbrev capB (o:IntroIndex) :ℕ:=cap o 2
private abbrev capJ (o:IntroIndex) :ℕ:=min (cap o 1) (capB o)
private theorem capB_pos (o:IntroIndex) :0<capB o:= by
  fin_cases o <;> exact zjC (by with_unfolding_all rfl)
private def rankY (B:ℕ) :kB :=
  (⟨4*262144*133605*B,10*179740,by decide⟩:kB).add ⟨128539,46135,by decide⟩
private theorem rankY_val (B:ℕ) :
    (rankY B).val = 4*((262144 :ℚ)/179740)*133605*B/10+128539/46135:= by
  rw [rankY,kB.val_add]
  simp only [kB.val,z2R,Nat.cast_ofNat]
  ring
private def rankZ (B J:ℕ) (hB:0<B) :kB :=
  (⟨262144*133605*(4*J*B-2*J*J)*9,10*179740*B,Nat.mul_pos (by decide) hB⟩:kB).add
    ⟨B+1,1,Nat.one_pos⟩
private theorem rankZ_val (B J:ℕ) (hB:0<B) (hJ:J≤B) :
    (rankZ B J hB).val=((262144 :ℚ)/179740)*133605*(4*J-2*(J:ℚ)*J/B)*9/10+B+1 := by
  have hn:2*J*J≤4*J*B :=
    (zBI (2*J) hJ).trans (ztf B
      (ztf J (by decide :2≤4)))
  have hq: (B:ℚ)≠0:=(Nat.cast_pos.mpr hB).ne'
  rw [rankZ,kB.val_add]
  simp only [kB.val,z2R,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,Nat.cast_sub hn,div_one]
  field_simp [hq]
  ring
private def rank (o:IntroIndex) (k :Fin 4) :kB :=
  ![kB.zero,rankY (capB o),rankZ (capB o) (capJ o) (capB_pos o),kB.zero] k
private theorem rank_val (o:IntroIndex) (k :Fin 4) : (rank o k).val=rankPrice o k := by
  have hB: (capB o:ℚ)≠0:=(Nat.cast_pos.mpr (capB_pos o)).ne'
  simp only [rankPrice,cap_val,← Nat.cast_min,ite_eq_right hB]
  fin_cases k
  · exact kB.val_zero
  · exact rankY_val _
  · exact rankZ_val _ _ (capB_pos o) (min_le_right _ _)
  · exact kB.val_zero
private theorem rankCheck (o:IntroIndex) (k :Fin 4) : (rank o k).afu (residue o k) := by
  fin_cases o <;> fin_cases k <;> exact zjC (by with_unfolding_all rfl)
private theorem rankCovered (o:IntroIndex) (k :Fin 4) :
    stopPrice a b o 0 k≤envelopePrice o 0 k := by
  simp only [envelopePrice,accStage,ite_eq_right (by decide : ¬ (10 :bAL)≤0),
    ite_eq_right (by decide : ¬ (11 :bAL)≤0),ite_eq_right (by decide : ¬ moveStart≤0),zero_add]
  change rankPrice o k≤(residue o k).val
  rw [← rank_val]
  exact (kB.cross_iff _ _).mp (rankCheck o k)
private def contraction (o:IntroIndex) (j:Fin 3) :kB :=
  kB.sumFin fun k=>(residue o k).scale (mixedCols (originShape o) k j)
private def running (o:IntroIndex) (j:Fin 3) :kB :=
  kB.sumFin fun i =>
    if i≤o then ⟨factorJumpN i j,factorJumpD i j+1,ztH _⟩ else kB.zero
private theorem factorCheck (o:IntroIndex) (j:Fin 3) :
    (contraction o j).afu (running o j) := by
  fin_cases o <;> fin_cases j <;> exact zjC (by with_unfolding_all rfl)
private theorem unitCovered (o:IntroIndex) (j:Fin 3) :unit o j≤bbD factorJump o j:= by
  have h:=(kB.cross_iff _ _).mp (factorCheck o j)
  simp only [contraction,running,kB.val_sumFin,kB.val_scale,kB.val_ite,kB.val_zero] at h
  simpa only [unit,bbD,qtqUEwc.residual,factorJump,residue,kB.val] using h
theorem proof :qtqUEwc.c3 :=
  ⟨fun o s=>Fin.cases (rankCovered o) (movingCovered o) s,unitCovered⟩
end qb8DdTc
end
