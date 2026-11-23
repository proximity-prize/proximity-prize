import ProximityPrize.SubmissionLower.Z6ulMMd
import ProximityPrize.SubmissionLower.Z3lRrWc
import ProximityPrize.SubmissionLower.ZnTmQ9b
import ProximityPrize.SubmissionLower.ZZhU1ja
import ProximityPrize.SubmissionLower.ZJBzH3c
import ProximityPrize.SubmissionLower.Znc9Sbd
import ProximityPrize.SubmissionLower.ZXdt6vc
import ProximityPrize.SubmissionLower.ZDw1jvc
set_option Elab.async false
section
set_option autoImplicit true
set_option exponentiation.threshold 160
namespace qtYJNJe
open P6 (p)
open P6_7_1 (Origin degree terminal)
open q3rjQGe qrT6Ada
open pI (weight)
private abbrev agr :ℕ:=P5_7.midAgreement
private abbrev len:ℕ:=262144
private theorem cTz : (0:ℚ)<gap:= by decide
private theorem axis_pos {e :ℕ} (he :0<e) :0<axisRate e :=
  div_pos (by decide : (0:ℚ)<p) (Nat.cast_pos.mpr he)
private theorem axis_mul {e :ℕ} (he :0<e) : (e :ℚ)*axisRate e=p:= by
  unfold axisRate
  rw [mul_comm,div_mul_cancel₀ _ (Nat.cast_pos.mpr he : (0:ℚ)<e).ne']
private abbrev PriceOK (u n d m a e l:ℕ) :Prop :=
  32*u*n*p+m*d*l≤ m*d*(u*p)+32*u*n*a*e
private theorem jX {u n d m a e l:ℕ} {s :ℚ}
    (he :0<e) (hu:0< u) (hd:0<d) (hs :s<axisRate e)
    (hl: (l:ℚ)=u*e*s) (h:PriceOK u n d m a e l) :
    (n:ℚ)/d*(axisRate e-a)/(axisRate e-s)≤(m:ℚ)/32 := by
  have hq:=(Nat.cast_le (α:=ℚ)).mpr h
  push_cast at hq
  rw [hl] at hq
  have hbase :32*(u:ℚ)*n*((p:ℚ)-a*e)≤(m:ℚ)*d*(u*p-u*e*s) := by
    linear_combination hq
  have hL: (p:ℚ)-a*e=e*(axisRate e-a) := by
    rw [← axis_mul he]
    ring
  have hR: (u:ℚ)*p-u*e*s=u*e*(axisRate e-s) := by
    rw [← axis_mul he]
    ring
  rw [hL,hR] at hbase
  apply (div_le_iff₀ (sub_pos.mpr hs)).2
  rw [div_mul_eq_mul_div₀,div_mul_eq_mul_div₀]
  apply (div_le_div_iff₀ (Nat.cast_pos.mpr hd) (by decide : (0:ℚ)<32)).2
  have huQ: (0:ℚ)< u:=Nat.cast_pos.mpr hu
  have heQ: (0:ℚ)<e :=Nat.cast_pos.mpr he
  apply (mul_le_mul_iff_right₀ (mul_pos huQ heQ)).1
  convert hbase using 1 <;> ring
private theorem price_zero {n d m a e :ℕ}
    (he :0<e) (hd:0<d) (h:PriceOK 1 n d m a e 0) :
    (1-(a :ℚ)/axisRate e)*((n:ℚ)/d)≤(m:ℚ)/32 := by
  have hs :=axis_pos he
  have hx : (axisRate e-(a :ℚ))/axisRate e=1-(a :ℚ)/axisRate e := by
    rw [sub_div,div_self hs.ne']
  rw [← hx,mul_comm,← mul_div_assoc]
  simpa only [sub_zero] using
    jX he Nat.one_pos hd hs (by simp : ((0:ℕ) :ℚ)=(1 :ℕ)*(e :ℚ)*0) h
private abbrev bKq (e :ℕ) :ℕ :=
  (2*e-1)*(agr+2*len*degree)*gap+(len-degree)*agr
private theorem persistent_eq {e :ℕ} (he :0<e) :
    persistentRate e=(bKq e :ℚ)/((agr*gap:ℕ) :ℚ) := by
  have h:1≤2*e := by omega
  have ha : (agr :ℚ)≠0:= by decide
  simp only [bKq,persistentRate,Nat.cast_add,Nat.cast_mul,
    Nat.cast_sub h,Nat.cast_one,Nat.cast_ofNat]
  field_simp [ha,cTz.ne']
private abbrev Offers (d z a m e :ℕ) :Prop :=
  (1-(a :ℚ)/axisRate e)*persistentRate e≤(m:ℚ)/32 ∨
  (e=1∧(1-(a :ℚ)/axisRate e)*linearRate≤(m:ℚ)/32) ∨
  (e=2∧(16:ℚ)≤ min (z :ℚ) a ∧
    quadraticRate*(axisRate e-a)/(axisRate e-16)≤(m:ℚ)/32) ∨
  (3≤e ∧ ∃ g c W M,NativeOK e g c W M ∧
    let s :=nativeSlope ((d:ℚ)/150) e
    s≤ min (z :ℚ) a∧nativeRate e g c W*(axisRate e-a)/(axisRate e-s)≤(m:ℚ)/32)
private theorem degree_lt {a e k :ℕ} (h:p≤k*a) (he :a*e<p) :e<k := by
  by_contra! hk
  rw [Nat.mul_comm k a] at h
  exact (not_lt_of_ge (h.trans (Nat.mul_le_mul_left a hk))) he
private theorem persistent_menu {d z a m:ℕ} (h:p≤9*a)
    (hc : ∀ i:Fin 8,PriceOK 1 (bKq (i.val+1)) (agr*gap) m a (i.val+1) 0)
    {e :ℕ} (he :0<e) (ha :a*e<p) :Offers d z a m e := by
  have h9:=degree_lt h ha
  let i:Fin 8:=⟨e-1,by omega⟩
  have hi:i.val+1=e :=Nat.sub_add_cancel he
  have hr :=hc i
  rw [hi] at hr
  left
  rw [persistent_eq he]
  exact price_zero he (by decide) hr
private def entry (i:Fin 13) :ℕ×ℕ×ℕ :=
  ([ (10,45,476070),(15,55,630807),(24,64,781875),(32,74,930637),
     (39,84,1078044),(46,94,1224518),(60,103,1369867),(68,113,1514305),
     (81,122,1658702),(91,132,1801857),(97,142,1945044),(115,151,2087533),
     (120,161,2230004) ] :List (ℕ×ℕ×ℕ)).get i
private abbrev nativeNum (i:Fin 13) :ℕ :=
  let g:=(entry i).1
  let c:=(entry i).2.1
  let W:=(entry i).2.2
  let e :=i.val+3
  max ((e*(c+1)+e+g)*gap)
    ((7+6*e)*gap+((2*e+1)*len+(6*e-2)*W-3*e*e*degree))
private theorem rate_num (u v w:ℕ) :
    max (u:ℚ) ((v :ℚ)+(w:ℚ)/gap) =
      ((max (u*gap) (v*gap+w) :ℕ) :ℚ)/gap:= by
  rw [Nat.cast_max,← max_div_div_right cTz.le]
  push_cast
  rw [add_div,mul_div_cancel_right₀ _ cTz.ne',mul_div_cancel_right₀ _ cTz.ne']
private theorem witness (i:Fin 13) :
    ∃ g c W M,NativeOK (i.val+3) g c W M ∧
      nativeRate (i.val+3) g c W=(nativeNum i:ℚ)/gap:= by
  let g:=(entry i).1
  let c:=(entry i).2.1
  let W:=(entry i).2.2
  refine ⟨g,c,W,W+1+((g+1)*c/(c+1))*degree,?_,?_⟩
  · unfold NativeOK
    fin_cases i <;> decide
  · exact rate_num _ _ _
private abbrev seedNum (d e :ℕ) :ℕ:=d+1800*e*e+3600*e
private theorem seed_eq {e :ℕ} (d:ℕ) (he :0<e) :
    (seedNum d e :ℚ)=450*(e :ℚ)*nativeSlope ((d:ℚ)/150) e := by
  have h: (e :ℚ)≠0:=(Nat.cast_pos.mpr he : (0:ℚ)<e).ne'
  simp only [seedNum,nativeSlope,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  field_simp [h]
  ring
private theorem slope {d e z :ℕ} (he :0<e)
    (h:seedNum d e≤450*e*z) :nativeSlope ((d:ℚ)/150) e≤(z :ℚ) := by
  have heQ: (0:ℚ)<e :=Nat.cast_pos.mpr he
  apply (mul_le_mul_iff_right₀ (show 0<450*(e :ℚ) by positivity)).1
  rw [← seed_eq d he]
  exact_mod_cast h
private theorem small_cap (u v :ℕ) (h:u*gap+v*len≤100*gap) :
    (u:ℚ)+(v :ℚ)*len/gap≤100:= by
  calc
    _=((u:ℚ)*gap+(v :ℚ)*len)/gap:= by
      rw [add_div,mul_div_cancel_right₀ _ cTz.ne']
    _≤_:=(div_le_iff₀ cTz).2 (by exact_mod_cast h)
private theorem native_menu {d z a m:ℕ} (hb:p≤16*a)
    (hz :16≤z) (hza :z≤a) (hm:3200≤ m)
    (hc : ∀ i:Fin 13,seedNum d (i.val+3)≤450*(i.val+3)*z ∧
      PriceOK 450 (nativeNum i) gap m a (i.val+3) (seedNum d (i.val+3)))
    {e :ℕ} (he :0<e) (ha :a*e<p) (hG: (a :ℚ)<axisRate e) :
    Offers d z a m e := by
  have hzaQ: (z :ℚ)≤a :=Nat.cast_le.mpr hza
  have MV: (16:ℚ)≤z := by exact_mod_cast hz
  have h100: (100:ℚ)≤(m:ℚ)/32 :=
    (le_div_iff₀ (by decide : (0:ℚ)<32)).2 (by exact_mod_cast hm)
  by_cases h1 :e=1
  · subst e
    right
    left
    refine ⟨rfl,?_⟩
    have h:=sub_le_self (1 :ℚ) (div_nonneg (Nat.cast_nonneg a) (axis_pos he).le)
    exact (mul_le_of_le_one_left (by positivity) h).trans
      ((small_cap 1 3 (by decide)).trans h100)
  by_cases h2 :e=2
  · subst e
    right
    right
    left
    refine ⟨rfl,le_min MV (MV.trans hzaQ),?_⟩
    have ha16: (16:ℚ)≤a :=MV.trans hzaQ
    have h:=(div_le_one (sub_pos.mpr (ha16.trans_lt hG))).2 (sub_le_sub_left ha16 _)
    rw [mul_div_assoc]
    exact (mul_le_of_le_one_right (by positivity) h).trans
      ((small_cap 13 8 (by decide)).trans h100)
  have h16e :=degree_lt hb ha
  have h3:3≤e := by omega
  let i:Fin 13:=⟨e-3,by omega⟩
  have hi:i.val+3=e :=Nat.sub_add_cancel h3
  have hrow:=hc i
  obtain ⟨g,c,W,M,hw,hr⟩:=witness i
  rw [hi] at hrow hw hr
  have hs :=slope he hrow.1
  right
  right
  right
  refine ⟨h3,g,c,W,M,hw,le_min hs (hs.trans hzaQ),?_⟩
  rw [hr]
  exact jX he (by decide) (by decide) (hs.trans_lt (hzaQ.trans_lt hG)) (seed_eq d he) hrow.2
private theorem rect_row {x y z a m:ℕ} (hy :y<p*150) (hx :2*x≤a*150)
    (ha :0<a) (hp:a<p) (hz :2≤z)
    (hm : ∀ e :ℕ,0<e→a*e<p→(a :ℚ)<axisRate e→Offers (min y (2*x)) z a m e) :
    RectRateOK ((x :ℚ)/150) ((y :ℚ)/150) z a ((m:ℚ)/32) := by
  refine ⟨by positivity,by positivity,?_,?_,by exact_mod_cast ha,
    by exact_mod_cast hp,by exact_mod_cast hz,by positivity,?_⟩
  · apply (div_lt_iff₀ (by decide : (0:ℚ)<150)).2
    exact_mod_cast hy
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ (by decide : (0:ℚ)<150)).2
    exact_mod_cast hx
  · intro e he h
    have hmin:min ((y :ℚ)/150) (2*((x :ℚ)/150))=(↑(min y (2*x)) :ℚ)/150:= by
      rw [← mul_div_assoc,min_div_div_right (by decide : (0:ℚ)≤150),
        Nat.cast_min,Nat.cast_mul,Nat.cast_ofNat]
    rw [hmin]
    have hq:=(lt_div_iff₀ (Nat.cast_pos.mpr he : (0:ℚ)<e)).1 h
    exact hm e he (by exact_mod_cast hq) h
private abbrev axisNum (o:Origin) :ℕ :=
  weightedNum (![terminal.z,terminal.B-terminal.J,terminal.J,0]) o termStop
private abbrev planeNum (o:Origin) :ℕ :=
  weightedNum (weight (aHp termTrial) 0) o termStop
private theorem axis_cast (o:Origin) :axisCap o=(axisNum o:ℚ)/150 :=
  weighted_cast _ _ _
private theorem plane_cast (o:Origin) :planeCap o=(planeNum o:ℚ)/150 :=
  weighted_cast _ _ _
set_option quotPrecheck false in
local notation "persist!" => fun _ he ha _ =>
  persistent_menu (by decide) (by intro i; fin_cases i <;> decide) he ha
set_option quotPrecheck false in
local notation "native!" => fun _ he ha hG =>
  native_menu (by decide) (by decide) (by decide) (by decide)
    (by intro i; fin_cases i <;> decide) he ha hG
theorem proof :qrT6Ada.c2 := by
  intro o
  rw [axis_cast,plane_cast,z,ar,br]
  apply rect_row
  · simp only [planeNum,weightedNum,Fin.sum_univ_succ,Fin.sum_univ_zero]
    fin_cases o <;> decide
  · simp only [axisNum,weightedNum,Fin.sum_univ_succ,Fin.sum_univ_zero]
    fin_cases o <;> decide
  · fin_cases o <;> decide
  · fin_cases o <;> decide
  · fin_cases o <;> decide
  · simp only [axisNum,planeNum,weightedNum,Fin.sum_univ_succ,Fin.sum_univ_zero]
    fin_cases o
    · exact native!
    · exact persist!
    · exact persist!
    · exact persist!
    · exact persist!
    · exact persist!
    · exact persist!
    · exact persist!
    · exact native!
    · exact native!
    · exact persist!
    · exact persist!
    · exact persist!
end qtYJNJe
end
section
set_option autoImplicit true
namespace q7cr9jd
theorem proof :quQsorc.c1 :=
  qziIa4d.of_children qOj34lc.proof qJ69aaa.proof
    (qnyP9Da.of_children q3zqDZc.proof qJQ0Sxd.proof
      qDhaEec.proof)
    qU1uHGd.proof
end q7cr9jd
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 16000000
namespace qWiDZjb
open qigFtUb
private theorem r0:Prefix .pruned 83 4 := by
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | refine (gradeTest_eq ?_).trans ?_
      · decide
      · (conv=>lhs; congr <;> cbv) <;> rfl
private theorem r1 :Prefix .pruned 87 4 := by
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | refine (gradeTest_eq ?_).trans ?_
      · decide
      · (conv=>lhs; congr <;> cbv) <;> rfl
private theorem r2 :Prefix .pruned 91 4 := by
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | refine (gradeTest_eq ?_).trans ?_
      · decide
      · (conv=>lhs; congr <;> cbv) <;> rfl
private theorem r3:Prefix .pruned 95 5:= by
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | refine (gradeTest_eq ?_).trans ?_
      · decide
      · (conv=>lhs; congr <;> cbv) <;> rfl
theorem Z3:Prefix .pruned 83 17 :=
  prefix_add (prefix_add (prefix_add r0 r1) r2) r3
end qWiDZjb
end
section
set_option autoImplicit true
namespace qWiDZjb
open P6_7_2 qigFtUb
theorem proof :qigFtUb.c1 := by
  intro i hi h hlo hhi
  have hc:check .pruned (Lc i 0) (i.val+1) (seedCap i+1)=true := by
    rcases i with ⟨j,hj⟩
    change 67≤j at hi
    rw [← gradeTest_eq hj]
    have hjmax :j<100:=hj
    have hoff :j-67<33:= by omega
    have hidx :67+(j-67)=j:= by omega
    simpa only [hidx] using prefix_get (prefix_add Wp Z3) hoff
  exact checked .pruned (Lc i 0) _ _ (Nat.succ_pos _) hc h hlo hhi
end qWiDZjb
end
section
set_option autoImplicit true
namespace qAOSsCb
open qigFtUb P6_7_2
theorem proof :qigFtUb.c4 := by
  rintro ⟨j,hj⟩ h hlo hhi
  have hp:Prefix .tailThree 0 75 :=
    prefix_add (prefix_add (prefix_add (prefix_add batchA batchB) batchC) batchD) batchE
  have hc:gradeTest .tailThree j=true := by
    simpa only [Nat.zero_add] using prefix_get hp hj
  rw [gradeTest_eq hj] at hc
  exact checked .tailThree _ _ _ (Nat.succ_pos _) hc h hlo hhi
end qAOSsCb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1200000
namespace qNRjwze
noncomputable section
open Finset
open P6 (p)
open P6_7 (RectTail)
open P6_7_2 (Input)
open P6_7_2_3 (Origin introCap originShape)
open cu (Jet)
open gT (Ambient IZ gk)
open pI (oU dM pN mass a5I F7)
open YX (bQz bjf eHX evL)

open qQ (VN a4N bH5 bH6 bH4
  aJr bNe)
open akZ (ajz btm bKa caQ cfi)
open scoped Classical
open private a8m bYs ddo from ProximityPrize.SubmissionLower.CR
open private b6z from ProximityPrize.SubmissionLower.D7
theorem geometric_cover {b:RectTail} (x :Input b) (D:Finset Jet) (origin :Jet→Origin)
    (cut:Jet→Jet) (hirr : ∀ f∈D,Irreducible f) (hcut : ∀ f∈D,¬ f∣cut f)
    (hcaps : ∀ f∈D,oU (cut f) (originShape b (origin f)))
    (nest : ∀ o j,ajz (D.filter (fun f=>o≤origin f)) j≤ introCap b o j) :
    Nonempty (Parents x D cut) := by
  have each (f :Jet) (hf :f∈D) :
      ∃ S:Finset (Ideal Ambient),bQz f (cut f) S ∧
        (∀ q∈S,q.height=2∧bjf q) ∧
        dM S (fun k=>akZ.aHP (originShape b (origin f)) k f) ∧
        ∀ γ∈x.Γ,Mark x f γ→Mark x (cut f) γ →
          ∃ q∈S,IZ q (x.M.label γ) (x.F.scalar γ) := by
    have hp:=b6z (hirr f hf) (hcut f hf)
    obtain ⟨S,hs,hcover⟩:=aRY.proof _ _ hp
    obtain ⟨hfinite,hfit⟩:=a8m _ _ hp (btm f) (originShape b (origin f))
      (caQ (hirr f hf).ne_zero) (origin_J b _) (bKa f) (hcaps f hf) S hs
    refine ⟨S,hs,?_,fun k=>(hfit k).trans_eq (cfi _ _ (origin_J b _) k),
      fun γ _=>hcover (x.M.label γ) (x.F.scalar γ)⟩
    intro q hq
    obtain ⟨hprime,hd,hrow,hg⟩:=hs q hq
    exact ⟨bYs hp hprime hd hrow hg,hfinite q hq⟩
  let S (f :Jet) :=if h:f∈D then Classical.choose (each f h) else ∅
  have hs (f :Jet) (hf :f∈D) :=Classical.choose_spec (each f hf)
  have hS (f :Jet) (hf :f∈D) :
      S f=Classical.choose (each f hf) :=dite_eq_left hf
  let all:=D.biUnion S
  have hmass :dM all (massCap b) := fun k=> calc
    _ ≤ ∑ f∈D,mass (S f) k :=pI.bhF _ _ _
    _ ≤ ∑ f∈D,akZ.aHP (originShape b (origin f)) k f :=
      sum_le_sum fun f hf=> by rw [hS f hf]; exact (hs f hf).2.2.1 k
    _≤_:=charge b D origin nest k
  have geom (q:Ideal Ambient) (hq:q∈all) :
      q.IsPrime∧ringKrullDim (gk q)=2∧q.height=2∧bjf q:= by
    obtain ⟨f,hf,hq⟩:=mem_biUnion.mp hq
    rw [hS f hf] at hq
    exact ⟨((hs f hf).1 q hq).1,((hs f hf).1 q hq).2.1,(hs f hf).2.1 q hq⟩
  let Kw:=all.filter fun q=>pN q 0=0
  have seedExists (q:Ideal Ambient) (hq:q∈Kw) :
      ∃ C:VN,C.curve.totalDegree≤pN q 2 ∧
        C.points.card≤pN q 3 ∧ ∀ z R,IZ q z R→C.ow z := by
    obtain ⟨hq,hz⟩:=mem_filter.mp hq
    obtain ⟨hprime,hd,_,hf⟩:=geom q hq
    exact ddo q hprime hd hf hz
  let images (q:Ideal Ambient) :VN :=
    if h:q∈Kw then Classical.choose (seedExists q h) else ⟨1,one_ne_zero,∅⟩
  have hi (q:Ideal Ambient) (hq:q∈Kw) :
      (images q).curve.totalDegree≤pN q 2 ∧
      (images q).points.card≤pN q 3 ∧ ∀ z R,IZ q z R→(images q).ow z := by
    simpa only [images,dite_eq_left hq] using Classical.choose_spec (seedExists q hq)
  let cover :=a4N Kw images
  have hc:=(bH5 Kw images).trans
    ((sum_le_sum fun q hq=>(hi q hq).1).trans
      ((a5I (filter_subset _ _) 2).trans (hmass 2)))
  have hp:=(bH6 Kw images).trans
    ((sum_le_sum fun q hq=>(hi q hq).2.1).trans
      ((a5I (filter_subset _ _) 3).trans (hmass 3)))
  let seedPaid :=x.Γ.filter fun γ=>cover.ow (x.M.label γ)
  have hseed :seedPaid.card≤(p+1)*massCap b 2+massCap b 3 :=
    (aJr (T:=seedPaid) (fun _ _ _ _ h=>sub_left_inj.mp h) cover
      (hc.trans_lt (mass_small b 2)) (fun _ hγ=>(mem_filter.mp hγ).2)).trans
      (Nat.add_le_add (Nat.mul_le_mul_left _ hc) hp)
  let dominant (q:Ideal Ambient) :=Function.Injective ((Ideal.Quotient.mk q).comp F7)
  let ord:=all.filter fun q=>0<pN q 0 ∧ ¬ dominant q
  let marks (q:Ideal Ambient) :=x.Γ.filter fun γ=>IZ q (x.M.label γ) (x.F.scalar γ)
  let ordPaid :=ord.biUnion marks
  have hord:ordPaid.card≤ massCap b 0:= by
    refine (card_biUnion_le.trans (sum_le_sum ?_)).trans
      ((a5I (filter_subset _ _) 0).trans (hmass 0))
    intro q hq
    obtain ⟨hq,hpos,hno⟩:=mem_filter.mp hq
    refine (card_le_one.mpr fun y hy z hz => ?_).trans hpos
    obtain ⟨hy,hm⟩:=mem_filter.mp hy
    obtain ⟨hz,hn⟩:=mem_filter.mp hz
    exact x.F.distinct hy hz (bNe (eHX (geom q hq).1 hno hm hn))
  let owner (q:Ideal Ambient) :=if h:q∈all then Classical.choose (mem_biUnion.mp h) else 0
  have owns (q:Ideal Ambient) (h:q∈all) :owner q∈D ∧q∈S (owner q) := by
    simpa only [owner,dite_eq_left h] using Classical.choose_spec (mem_biUnion.mp h)
  let Bp (f :Jet) :=(S f).filter fun q =>
    owner q=f∧0<pN q 0∧dominant q
  refine ⟨⟨Bp,seedPaid∪ordPaid,(card_union_le _ _).trans
    (Nat.add_le_add hseed hord),?_,?_,?_⟩⟩
  · intro f hf q hq
    obtain ⟨hq,_,hpos,hdom⟩:=mem_filter.mp hq
    have hall:q∈all:=mem_biUnion.mpr ⟨f,hf,hq⟩
    obtain ⟨hprime,hd,hh,hfinite⟩:=geom q hall
    have hlim (k :Fin 4) :pN q k<p :=
      ((evL hall k).trans (hmass k)).trans_lt (mass_small b k)
    have hmem:=(hs f hf).1 q (hS f hf ▸ hq)
    exact ⟨⟨hprime,hd,hfinite.Kw,hfinite.jU,hfinite.kK,hfinite.Bo,
      ⟨hpos,hlim 0⟩,hlim 2,hlim 3,hdom⟩,hh,hmem.2.2⟩
  · intro f _ g _ hne
    exact disjoint_left.mpr fun q hf hg=>hne ((mem_filter.mp hf).2.1.symm.trans (mem_filter.mp hg).2.1)
  · intro f hf γ hγ hz hw
    obtain ⟨q,hq,hmark⟩:=(hs f hf).2.2.2 γ hγ hz hw
    have hall:q∈all:=mem_biUnion.mpr ⟨f,hf,(hS f hf).symm ▸ hq⟩
    by_cases hzero :pN q 0=0
    · have hmem:q∈Kw:=mem_filter.mpr ⟨hall,hzero⟩
      exact Or.inl (mem_union_left _ (mem_filter.mpr
        ⟨hγ,bH4 hmem ((hi q hmem).2.2 _ _ hmark)⟩))
    · have hpos :=Nat.pos_of_ne_zero hzero
      by_cases hdom:dominant q
      · obtain ⟨hg,hq⟩:=owns q hall
        exact Or.inr ⟨owner q,hg,q,mem_filter.mpr ⟨hq,rfl,hpos,hdom⟩,hmark⟩
      · exact Or.inl (mem_union_right _ (mem_biUnion.mpr
          ⟨q,mem_filter.mpr ⟨hall,hpos,hdom⟩,mem_filter.mpr ⟨hγ,hmark⟩⟩))
end
end qNRjwze
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 6000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1600000
namespace qNRjwze
noncomputable section
open Polynomial Finset
open P6 (K)
open P6_7 (RectTail)
open P6_7_2
open P6_7_2_3 (Origin last introCap originShape ee3 anZ lineCharge OriginCover)
open cu (Jet)
open DP (U4 d3r)
open gT (IZ)
open pI (oU)
open P5_7_1 (wD)
open akZ (strip aRJ ajz cN5 cVg)
open scoped Classical
def c1 :Prop :=
  ∀ (b:RectTail) (x :Input b) (G:Jet) (D:Finset Jet),aRJ G D →
    (∀ f∈D,f.natDegree=0)→(∀ j,ajz D j≤ introCap b last j) →
    ∃ gH :Finset K,gH.card≤eHB b ∧
      ∀ f∈D,∀ γ∈x.Γ,Mark x f γ→γ∈gH
def c2 :Prop :=
  ∀ (b:RectTail) (x :Input b) (P:Poles x),TopPair x →
    ∀ (R:Reference P) (D:Finset Jet),aRJ (U4 R.raw) D →
    (∀ f∈D,0<f.natDegree)→(∀ j,ajz D j≤ introCap b last j) →
    ∃ gH :Finset K,gH.card≤akj ∧ ∀ f∈D,Nonempty (LastCut x gH f)
private theorem gX {A B:Finset K} {a b:ℕ} (ha :A.card≤a) (hb:B.card≤b) :
    (A∪B).card≤a+b :=
  (card_union_le _ _).trans (Nat.add_le_add ha hb)
private theorem DH (b:RectTail) :
    au1 b+eHB b+akj+projectionFee b≤ee3 b:= by
  cases b <;> decide
private theorem early_of_ne {o:Origin} (ho:o≠last) :o.val<13:= by
  have hh:=o.isLt
  have hn:o.val≠13:= fun h=>ho (Fin.ext h)
  omega
theorem of_children (h1 :c1) (h2 :c2) :P6_7_2_3.c1 := by
  intro b x P pick top
  have hn:=pick.free_ne 0
  have hc:=anchor_caps pick
  obtain ⟨A⟩:=bRI.proof _ _ hn hc
  obtain ⟨a⟩:=strip hn hc A
  obtain ⟨fixed,hfixed,hfa⟩:=stripped_paid x pick A a
  obtain ⟨D,hD,hcap,hroot⟩:=cVg a
  obtain ⟨R,⟨C⟩⟩:=schedule pick hD hcap
  let O:=D.filter fun f=>C.origin f=last∧f.natDegree=0
  let F:=D.filter fun f=>C.origin f=last∧0<f.natDegree
  let T:=D \ O
  have suffix (E :Finset Jet) (hs :E⊆D.filter (fun f=>last≤C.origin f)) (j:Fin 3) :
      ajz E j≤ introCap b last j:=(cN5 hs j).trans (C.nested last j)
  have hO:O⊆D.filter (fun f=>last≤C.origin f) := fun _ hf =>
    let h:=mem_filter.mp hf
    mem_filter.mpr ⟨h.1,h.2.1.ge⟩
  have hF:F⊆D.filter (fun f=>last≤C.origin f) := fun _ hf =>
    let h:=mem_filter.mp hf
    mem_filter.mpr ⟨h.1,h.2.1.ge⟩
  obtain ⟨iy,hordinary,hOrd⟩ :=
    h1 b x (anchorRow pick) O (hD.mono (filter_subset _ _)) (fun _ hf=>(mem_filter.mp hf).2.2) (suffix O hO)
  have href :aRJ (U4 R.raw) F:= by
    refine ⟨?_,hD.pairwise.mono (filter_subset _ _)⟩
    intro f hf
    obtain ⟨hm,he,_⟩:=mem_filter.mp hf
    obtain ⟨hi,_,hu,hs,hr⟩:=hD.factors f hm
    exact ⟨hi,C.last_dvd f hm he,hu,hs,hr⟩
  obtain ⟨singular,hsing,cuts⟩:=h2 b x P top R F href
    (fun _ hf=>(mem_filter.mp hf).2.2) (suffix F hF)
  let be1 (f :Jet) (hf :f∈F) :=Classical.choice (cuts f hf)
  let cut (f :Jet) :=if h: (C.origin f).val<13 then C.cut ⟨_,h⟩
    else if hf :f∈F then (be1 f hf).cut else 0
  let line (f :Jet) :=if hf :f∈F then (be1 f hf).line else false
  let lines (f :Jet) :=if hf :f∈F then
    if (be1 f hf).line then x.Γ.filter (LineRoot x (be1 f hf).row) else ∅ else ∅
  have hT:T⊆D:=sdiff_subset
  have early_no (f :Jet) (h: (C.origin f).val<13) :f∉F :=
    fun hf=>h.not_ge (show 13≤(C.origin f).val from (mem_filter.mp hf).2.1.ge)
  have late_mem (f :Jet) (hf :f∈T) (h : ¬ (C.origin f).val<13) :f∈F:= by
    have he :C.origin f=last := by
      apply Fin.ext
      have hp:=(C.origin f).isLt
      change (C.origin f).val=13
      omega
    refine mem_filter.mpr ⟨hT hf,he,Nat.pos_of_ne_zero ?_⟩
    intro hz
    exact (mem_sdiff.mp hf).2 (mem_filter.mpr ⟨hT hf,he,hz⟩)
  have individual (f :Jet) (hf :f∈F) (j:Fin 3) :wD f j≤ introCap b last j :=
    (single_le_sum (f := fun g=>wD g j) (fun _ _=>Nat.zero_le _) hf).trans (suffix F hF j)
  have proper (f :Jet) (hf :f∈T) : ¬ f∣cut f := by
    by_cases he : (C.origin f).val<13
    · simpa only [cut,dite_eq_left he] using C.proper f (hT hf) ⟨_,he⟩ rfl
    · have hl:=late_mem f hf he
      simpa only [cut,dite_eq_right he,dite_eq_left hl] using (be1 f hl).proper
  have aMw (f :Jet) (hf :f∈T) :oU (cut f) (originShape b (C.origin f)) := by
    by_cases he : (C.origin f).val<13
    · simp only [cut,originShape,dite_eq_left he]
      exact d3r P.crt x.word (C.mem ⟨_,he⟩)
    · have hl:=late_mem f hf he
      have eq :=(mem_filter.mp hl).2.1
      simpa only [cut,dite_eq_right he,dite_eq_left hl,eq] using
        last_enclose (individual f hl) _ (be1 f hl).caps
  have nest (o:Origin) (j:Fin 3) :
      ajz (T.filter (fun f=>o≤C.origin f)) j≤ introCap b o j :=
    (cN5 (filter_subset_filter _ hT) j).trans (C.nested o j)
  obtain ⟨G⟩:=geometric_cover x T C.origin cut (fun f hf=>(hD.factors f (hT hf)).1) proper aMw nest
  let gH :=fixed∪iy∪singular∪G.gH
  refine ⟨({
    factors :=T
    origin :=C.origin
    cut:=cut
    line :=line
    lineMarks :=lines
    parents :=G.parents
    gH :=gH
    paid_bound:=(gX (gX (gX hfixed hordinary) hsing) G.paid_bound).trans (DH b)
    nested:=nest
    proper := fun f hf=>⟨(hD.factors f (hT hf)).1,(hD.factors f (hT hf)).2.1,proper f hf⟩
    distinct := ?_
    cut_caps := ?_
    shared_cut := ?_
    line_pos := ?_
    line_bound := ?_
    geometric:=G.geometric
    disjoint:=G.disjoint
    Eh := ?_ } : OriginCover P pick)⟩
  · intro f hf g hg hne ha
    exact (hD.factors f (hT hf)).1.not_isUnit
      (hD.pairwise (hT hf) (hT hg) hne dvd_rfl ha.dvd)
  · intro f hf
    by_cases he : (C.origin f).val<13
    · simpa only [anZ,line,dite_eq_right (early_no f he),Bool.false_eq_true,ite_false]
        using aMw f hf
    · have hl:=late_mem f hf he
      by_cases hh: (be1 f hl).line=true
      · simp only [anZ,cut,line,dite_eq_right he,dite_eq_left hl,ite_eq_left hh]
        have h:=(be1 f hl).caps
        rw [ite_eq_left hh] at h
        exact h
      · simpa only [anZ,line,dite_eq_left hl,ite_eq_right hh] using aMw f hf
  · intro f _ g _ he eq
    have h:=early_of_ne he
    have hg: (C.origin g).val<13:=eq ▸ h
    simp only [cut,dite_eq_left h,dite_eq_left hg]
    have ev :=congrArg (fun o:Origin=>o.val) eq
    exact congrArg C.cut (Fin.ext ev)
  · intro f _ hp
    by_cases hf :f∈F
    · have hh: (be1 f hf).line=true := by simpa only [line,dite_eq_left hf] using hp
      obtain ⟨_,ho,hj⟩:=mem_filter.mp hf
      exact ⟨ho,hj,(be1 f hf).line_pos hh⟩
    · simp only [line,dite_eq_right hf,Bool.false_eq_true] at hp
  · intro f _
    by_cases hf :f∈F
    · by_cases hh: (be1 f hf).line=true
      · simpa only [lines,line,dite_eq_left hf,ite_eq_left hh,lineCharge] using line_count x f (be1 f hf).row
          (mem_filter.mp hf).2.2 ((be1 f hf).line_pos hh) ((be1 f hf).line_caps hh)
      · simp only [lines,line,dite_eq_left hf,ite_eq_right hh,lineCharge,card_empty,le_refl]
    · simp only [lines,line,dite_eq_right hf,lineCharge,Bool.false_eq_true,ite_false,card_empty,le_refl]
  · intro γ hγ
    have use_pair (f :Jet) (hf :f∈T) (hrow:Mark x f γ) (hcut:Mark x (cut f) γ) :
        γ∈gH ∨ ∃ g∈T,γ∈lines g ∨ ∃ q∈G.parents g,IZ q (x.M.label γ) (x.F.scalar γ) := by
      rcases G.Eh f hf γ hγ hrow hcut with hp | ⟨g,hg,q,hq,hm⟩
      · exact Or.inl (mem_union_right _ hp)
      · exact Or.inr ⟨g,hg,Or.inr ⟨q,hq,hm⟩⟩
    rcases or_assoc.mpr (a.Eh _ _ (anchor_zero pick hγ)) with hh | hz
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (hfa γ hγ hh))))
    obtain ⟨f,hf,hrow⟩:=hroot _ _ hz
    by_cases ho:f∈O
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (hOrd f ho γ hγ hrow))))
    have ht:f∈T:=mem_sdiff.mpr ⟨hf,ho⟩
    by_cases he : (C.origin f).val<13
    · exact use_pair f ht hrow (by simpa only [cut,dite_eq_left he] using aux_zero (C.mem ⟨_,he⟩) hγ)
    have hl:=late_mem f ht he
    rcases (be1 f hl).Eh γ hγ hrow with hp | hcut | ⟨hline,hm⟩
    · exact Or.inl (mem_union_left _ (mem_union_right _ hp))
    · exact use_pair f ht hrow (by simpa only [cut,dite_eq_right he,dite_eq_left hl] using hcut)
    · refine Or.inr ⟨f,ht,Or.inl ?_⟩
      simp only [lines,dite_eq_left hl,ite_eq_left hline]
      exact mem_filter.mpr ⟨hγ,hm⟩
end
end qNRjwze
end
