import ProximityPrize.SubmissionLower.Zt62ONe
import ProximityPrize.SubmissionLower.ZJBzH3c
import ProximityPrize.SubmissionLower.ZnGdvBe
import ProximityPrize.SubmissionLower.Zg1hxlb
import ProximityPrize.SubmissionLower.Z8duOVc
import ProximityPrize.SubmissionLower.ZWpWUpd
import ProximityPrize.SubmissionLower.Za4gQ2b
import ProximityPrize.SubmissionLower.ZpAvArb
import ProximityPrize.SubmissionLower.Z6ulMMd
import ProximityPrize.SubmissionLower.ZKgVGSb
import ProximityPrize.SubmissionLower.ZDbTvLe
import ProximityPrize.SubmissionLower.ZRYXIua
import ProximityPrize.SubmissionLower.ZflC1Fd
import ProximityPrize.SubmissionLower.Z32V4rd
import ProximityPrize.SubmissionLower.ZDw1jvc
import ProximityPrize.SubmissionLower.ZVbskte
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qwvlNBb
noncomputable section
open Finset Polynomial
open cu (L)
open Cu (sQ)
open E7 (CurvePlace)
open qK3TPae (regular)
open qZfVj1b (pivot gRK)
open q1kuFjb (AtSite)
open quN7Z4a (physicalWeight)
open qBajpRb (cls)
open qRoCwuc (dSG)
open qkgz7gb (rV)
open private curve b5S pivot_ne normal_degree normal_monic normal_irreducible at_normal from ProximityPrize.SubmissionLower.ZPaaHRd
open scoped Classical
attribute [local instance] gRK
local notation "normEq" => qZfVj1b.normalize
private theorem weight {Q:sQ} [Fact (Irreducible Q)] {D W:ℕ}
    {f : (Cu.oO Q)[X][X]}
    (hn:f.leadingCoeff.leadingCoeff≠0) (hw:physicalWeight D f≤W) :
    ∀ i,(normEq f).coeff i≠0→((normEq f).coeff i).natDegree+i*D ≤W:= by
  intro i hi
  simp only [qZfVj1b.normalize,coeff_C_mul] at hi ⊢
  rw [natDegree_C_mul (inv_ne_zero hn)]
  exact (Finset.le_sup (f := fun i=>(f.coeff i).natDegree+i*D)
    (mem_support_iff.mpr (right_ne_zero_of_mul hi))).trans hw
theorem proof :qTplN5b.c2 := by
  intro Q _ J T z s e H W S hz he hpe hw
  have hp:Q.totalDegree<P6.p:=(Nat.le_mul_of_pos_right _ he).trans_lt hpe
  obtain ⟨v,hc,hh⟩:=P5_7_1_5Q.c4321 Q hp
  let Cq:=curve hc hh
  let U:=regular Q z T
  have hU:U⊆T:=filter_subset _ _
  let G:=U.filter fun γ=>MvPolynomial.eval (S.parameter γ) (pivot S)≠0
  have hG:G⊆U:=filter_subset _ _
  have hcut: (U \ G).card≤H := by
    have hb:=dSG S hz (pivot S) (pivot_ne S) (U \ G)
      (fun _ hg=>hU (mem_sdiff.mp hg).1) (fun γ hg=> by
        by_contra hn
        exact (mem_sdiff.mp hg).2 (mem_filter.mpr ⟨(mem_sdiff.mp hg).1,hn⟩))
    simpa only [one_mul] using hb.trans (Nat.mul_le_mul_right H (S.bY.degree.2 _ _))
  let lift (γ:P6.K) (hγ:γ∈G) :=
    Classical.choice (quwKLBd.proof S.bY hp hc (z γ) (S.parameter γ)
      (S.onBase γ (hU (hG hγ))))
  let A (γ:P6.K) (hγ:γ∈G) :AtSite Cq (rV z γ) := by
    let B:=lift γ hγ
    refine ⟨B.map,B.place,B.value,?_⟩
    let b (i:Fin 2) :=B.series (cls S.bY (MvPolynomial.X (Sum.inl i)))
    have hb (i:Fin 2) :B.map (Cq.seed i)=(b i:LaurentSeries L) := by
      rw [B.lift_eq,qBajpRb.incl_cls]
      simp [qBajpRb.ek,Cq,curve]
    have hres (i:Fin 2) :PowerSeries.constantCoeff (b i)=rV z γ i:= by
      rw [B.reduce,qBajpRb.atMark_cls,MvPolynomial.eval_X]
      rfl
    exact ⟨b,hb,hres,qyEseja.proof _ hp (S.onSeed γ (hU (hG hγ)))
      (mem_filter.mp (hG hγ)).2 B.place B.map B.value b hb hres⟩
  let place (γ:P6.K) :CurvePlace L Cq.E :=if hγ:γ∈G then (A γ hγ).place else v
  have hplace (γ:P6.K) (hγ:γ∈G) :place γ=(A γ hγ).place :=dite_eq_left hγ
  have hd:=normal_degree S
  let F:P5_7_3_5_2.Sheet Cq z s := {
    f :=normEq S.root.equation
    irreducible :=normal_irreducible S
    positive :=hd.symm ▸ he
    normalized:=normal_monic S
    marks :=G
    atPlace := fun γ hγ=>(A γ hγ).map
    place :=place
    distinct := by
      intro γ hγ δ hδ hh
      rw [hplace γ hγ,hplace δ hδ] at hh
      exact hz (hU (hG hγ)) (hU (hG hδ))
        ((algebraMap P6.K L).injective (congrFun ((A γ hγ).site_eq_of_place (A δ hδ) hh) 0))
    value := fun γ hγ c=>(congrArg (fun w:CurvePlace L Cq.E=>w.value c) (hplace γ hγ)).trans
      ((A γ hγ).value c)
    arc := fun γ hγ=>(A γ hγ).arc
    integral:= fun γ hγ i j=> by
      exact (congrArg (fun w:CurvePlace L Cq.E =>
        w.value (((normEq S.root.equation).coeff i).coeff j)) (hplace γ hγ)).trans_le
          ((at_normal S (hγ:=hU (hG hγ)) (lift γ hγ) (mem_filter.mp hγ).2).1 i j)
    root := fun γ hγ=>(at_normal S (hγ:=hU (hG hγ)) (lift γ hγ) (mem_filter.mp hγ).2).2 }
  exact ⟨Cq,F,hd,P5_7_1_5Q.c4322 S.bY hc S.height,weight (b5S S) hw,hG,hcut⟩
end
end qwvlNBb
end
section
set_option autoImplicit true
namespace qRpGGpd
open Polynomial
open cu (L)
open quN7Z4a (compressionWidth)
open qBajpRb (aia row_count)
open private compress fWf from ProximityPrize.SubmissionLower.Z8duOVc
theorem aIF:q6CrDDe.c2 := by
  intro B _ _ _ V W _ _ D F hD hF hFd hcoeff hrank
  let M:=compressionWidth D 2
  have hM:0<M:= by unfold M compressionWidth; positivity
  have hdim:aia D 2*Module.finrank L (V*W)<M*Module.finrank L V:= by
    have he :aia D 2*4=M:=(Nat.mul_comm _ _).trans (row_count D 2)
    have h:=Nat.mul_lt_mul_of_pos_left hrank (show 0<aia D 2 by omega)
    simpa only [← Nat.mul_assoc,he] using h
  obtain ⟨s,R,hR,hR0⟩:=fWf F hF
  have hc (i a :ℕ) : (R.coeff i).coeff a=(F.coeff i).coeff (a+s) := by
    rw [hR,coeff_C_mul,coeff_X_pow_mul]
  have hd:R.natDegree≤2 :=natDegree_le_iff_coeff_eq_zero.mpr fun i hi =>
    Polynomial.ext fun a=> by
      rw [hc,coeff_eq_zero_of_natDegree_lt (hFd.trans_lt hi),coeff_zero,coeff_zero]
  obtain ⟨A,G,J,hEq,hG0,hGd,hG,hsmall⟩ :=
    compress V W hM R hd (fun i a=>hc i a ▸ hcoeff i (a+s)) hR0 hdim
  refine ⟨G,hG0,hGd,hG,hsmall,?_⟩
  intro Q _ φ u hu hFQ
  let e :=eval₂RingHom (Polynomial.mapRingHom φ) u
  rw [eval_map] at hFQ ⊢
  change e F=0 at hFQ
  change e G=0
  have hx (k :ℕ) :e (Polynomial.C ((Polynomial.X:B[X])^k))=Polynomial.X^k := by
    change (Polynomial.C _).eval₂ (Polynomial.mapRingHom φ) u= _
    rw [eval₂_C,map_pow]
    simp only [coe_mapRingHom,map_X]
  have hRQ:e R=0:= by
    rw [hR,map_mul,hx] at hFQ
    apply Polynomial.ext
    intro a
    rw [coeff_zero,← coeff_X_pow_mul,hFQ,coeff_zero]
  have hEqQ:=congrArg e hEq
  rw [map_mul,hRQ,mul_zero,map_add,map_mul,hx] at hEqQ
  have hlow: (e G).natDegree<M:= by
    apply Nat.lt_of_le_pred hM
    change (G.eval₂ (Polynomial.mapRingHom φ) u).natDegree≤M-1
    rw [eval₂_eq_sum,Polynomial.sum_def]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    have hb:=hsmall i (G.coeff i).natDegree (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))
    exact (natDegree_mul_le_of_le natDegree_map_le (natDegree_pow_le_of_le i hu)).trans
      (Nat.le_pred_of_lt hb)
  by_contra hn
  have hv : (Polynomial.X:Q[X])^M∣e G :=
    ⟨-e J,by rw [mul_neg]; exact eq_neg_of_add_eq_zero_left hEqQ.symm⟩
  exact (leadingCoeff_ne_zero.mpr hn) ((X_pow_dvd_iff.mp hv) _ hlow)
end qRpGGpd
end
section
set_option autoImplicit true
namespace qRpGGpd
def c1 :Prop :=q6CrDDe.c1
def c2 :Prop :=qvWbALd.c1
def c3:Prop :=qvWbALd.c2
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :qRNngId.c3 :=
  qqwac6b.of_children (q6CrDDe.of_children h1 aIF)
    (qvWbALd.of_children h2 h3)
end qRpGGpd
end
section
set_option autoImplicit true
namespace qkdVGRd
def c1 :Prop :=qTplN5b.c1
def c2 :Prop :=qTplN5b.c2
def c3:Prop :=qTplN5b.c3
def c4 :Prop :=qTplN5b.c4
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :qRNngId.c4 :=
  qTplN5b.of_children h1 h2 h3 h4
end qkdVGRd
end
section
set_option autoImplicit true
namespace qWLt7Ib
open P6 (p)
open P6_7_1 (degree)
open q3rjQGe (FreeRateOK NativeOK gap graphRate nativeRate nativeSlope)
open qrT6Ada (freeDegree_le member_cast)
private abbrev q:ℕ:=p+1
private abbrev cap:ℕ:=37000000
private abbrev aN :ℕ:=38740117
private abbrev bN :ℕ:=4640
private def params (i:Fin 52) :ℕ×ℕ :=
  ([(10,45),(15,55),(24,64),(32,74),(39,84),(46,94),(60,103),(68,113),
    (81,122),(91,132),(97,142),(115,151),(120,161),(139,170),(155,179),(163,189),
    (183,198),(186,208),(207,217),(228,226),(229,236),(251,245),(274,254),(292,263),
    (295,273),(318,282),(342,291),(361,300),(361,310),(385,319),(410,328),(435,337),
    (453,346),(451,356),(476,365),(501,374),(527,383),(552,392),(573,401),(566,411),
    (591,420),(617,429),(644,438),(670,447),(698,456),(723,465),(746,474),(769,483),
    (758,493),(784,502),(811,511),(838,520)] :List (ℕ×ℕ)).get i
private abbrev stock (g c:ℕ) :=(g+1)*c
private abbrev shift (g c:ℕ) :=stock g c/(c+1)
private def width (e g c:ℕ) :ℕ :=
  let E :=e+g
  let j:=shift g c
  max (e*degree) (max ((c+1)*(degree*E*(E+1)/2+degree*j*(j+1)/2)/(stock g c)-j*degree)
    ((E-j)*degree))
private abbrev numerator (e g c W:ℕ) :=
  max ((e*(c+1)+e+g)*gap)
    ((7+6*e)*gap+((2*e+1)*262144+(6*e-2)*W-3*e*e*degree))
private abbrev priceOK (e n:ℕ) :Prop :=
  3*n*q+bN*gap*(cap+12*e*e+24*e)≤3*n*aN*e+bN*gap*(3*q)
private theorem row (i:Fin 52) :
    let e :=i.val+3
    let g:=(params i).1
    let c:=(params i).2
    let W:=width e g c
    NativeOK e g c W (W+1+shift g c*degree)∧priceOK e (numerator e g c W) := by
  unfold NativeOK
  fin_cases i <;> decide
private theorem cTz : (0:ℚ)<gap:= by
  exact_mod_cast (show 0<gap by decide)
private theorem rate_num (u v w:ℕ) :
    max (u:ℚ) ((v :ℚ)+(w:ℚ)/gap) =
      ((max (u*gap) (v*gap+w) :ℕ) :ℚ)/gap:= by
  rw [Nat.cast_max,← max_div_div_right cTz.le]
  push_cast
  rw [add_div,mul_div_cancel_right₀ _ cTz.ne',mul_div_cancel_right₀ _ cTz.ne']
private theorem a_ge_graph:graphRate 55≤(aN :ℚ) :=
  (div_le_iff₀ (by norm_num)).2 (by exact_mod_cast (show q≤aN*55 by decide))
private theorem cp0 {d:ℚ} {e :ℕ} (hd:d≤ cap) :
    nativeSlope d e≤nativeSlope (cap:ℚ) e := by
  unfold nativeSlope
  gcongr
private theorem cap_slope {e :ℕ} (he :0<e) (he54 :e≤54) :
    nativeSlope (cap:ℚ) e≤(aN :ℚ) := by
  have heq : (1 :ℚ)≤e := by exact_mod_cast he
  have hu: (e :ℚ)≤54 := by exact_mod_cast he54
  unfold nativeSlope
  have hdiv : (cap:ℚ)/(3*(e :ℚ))≤(cap:ℚ)/3 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith only [heq])
  calc
    _≤(cap:ℚ)/3+4*54+8 :=
      add_le_add (add_le_add hdiv (mul_le_mul_of_nonneg_left hu
        (show (0:ℚ)≤4 by norm_num))) le_rfl
    _≤_:= by
      have h:=(Nat.cast_le (α:=ℚ)).mpr (show cap+(4*54+8)*3≤3*aN by decide)
      push_cast at h
      linear_combination h/3
private theorem native_price {d:ℚ} {e n:ℕ}
    (hc:priceOK e n) (he :0<e) (hd:d≤ cap)
    (h0:nativeSlope (cap:ℚ) e≤(aN :ℚ)) (ha : (aN :ℚ)<graphRate e) :
    (n:ℚ)/gap*(graphRate e-aN)/(graphRate e-nativeSlope d e)≤(bN :ℚ) := by
  have heq : (0:ℚ)<e := by exact_mod_cast he
  have hz : (e :ℚ)*graphRate e=(q:ℚ) := by
    unfold graphRate
    field_simp
  have hL: (q:ℚ)-(aN :ℚ)*e=(e :ℚ)*(graphRate e-aN) := by
    rw [mul_sub,hz,mul_comm (aN :ℚ)]
  have hR:3*(q:ℚ)-cap-12*(e :ℚ)*e-24*e =
      3*(e :ℚ)*(graphRate e-nativeSlope (cap:ℚ) e) := by
    rw [← hz]
    unfold nativeSlope
    field_simp
    ring
  have hcQ:=(Nat.cast_le (α:=ℚ)).mpr hc
  push_cast at hcQ
  have h:3*(n:ℚ)*((q:ℚ)-(aN :ℚ)*e) ≤
      (bN :ℚ)*gap*(3*(q:ℚ)-cap-12*(e :ℚ)*e-24*e) := by
    linear_combination hcQ
  rw [hL,hR] at h
  have hs :nativeSlope d e≤nativeSlope (cap:ℚ) e :=cp0 hd
  apply (div_le_iff₀ (sub_pos.mpr (hs.trans_lt (h0.trans_lt ha)))).2
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sub_le_sub_left hs _) (Nat.cast_nonneg _))
  rw [div_mul_eq_mul_div₀]
  apply (div_le_iff₀ cTz).2
  apply (mul_le_mul_iff_right₀ (show 0<3*(e :ℚ) by positivity)).1
  convert h using 1 <;> ring
private theorem small_cap (u v :ℕ) (h:u*gap+v*262144≤bN*gap) :
    (u:ℚ)+(v :ℚ)*262144/gap≤(bN :ℚ) := by
  calc
    _=((u:ℚ)*gap+(v :ℚ)*262144)/gap:= by
      rw [add_div,mul_div_cancel_right₀ _ cTz.ne']
    _≤_:=(div_le_iff₀ cTz).2 (by exact_mod_cast h)
private theorem free_rate {d:ℚ} (hd0:0≤d) (hd:d≤ cap) :
    FreeRateOK d (aN :ℚ) (bN :ℚ) := by
  have hcp: (cap:ℚ)<p:=Nat.cast_lt.mpr (by decide)
  have hca : (cap:ℚ)≤aN :=Nat.cast_le.mpr (by decide)
  refine ⟨hd0,hd.trans_lt hcp,max_le (hd.trans hca) a_ge_graph,Nat.cast_nonneg _,?_⟩
  intro e he ha
  have he54 :e≤54 := by
    by_contra! hn
    have hx :graphRate e≤graphRate 55 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by exact_mod_cast hn)
    exact (not_lt_of_ge (hx.trans a_ge_graph)) ha
  by_cases h1 :e=1
  · subst e
    refine Or.inr (Or.inl ⟨rfl,?_⟩)
    have hx :1-(aN :ℚ)/graphRate 1≤1 :=
      sub_le_self _ (div_nonneg (Nat.cast_nonneg _) (by positivity))
    exact (mul_le_of_le_one_left (by positivity) hx).trans (small_cap 1 3 (by decide))
  by_cases h2 :e=2
  · subst e
    have MV: (16:ℚ)≤aN := by exact_mod_cast (show 16≤aN by decide)
    refine Or.inr (Or.inr (Or.inl ⟨rfl,MV,?_⟩))
    have hx : (graphRate 2-aN)/(graphRate 2-16)≤1 :=
      (div_le_one (sub_pos.mpr (MV.trans_lt ha))).2 (sub_le_sub_left MV _)
    rw [mul_div_assoc]
    exact (mul_le_of_le_one_right (by positivity) hx).trans (small_cap 13 8 (by decide))
  have he3:3≤e := by omega
  let i:Fin 52 :=⟨e-3,by omega⟩
  have hie :i.val+3=e :=Nat.sub_add_cancel he3
  obtain ⟨hw,hp⟩:=row i
  rw [hie] at hw hp
  have h0:=cap_slope he he54
  refine Or.inr (Or.inr (Or.inr ⟨he3,_,_,_,_,hw,(cp0 hd).trans h0,?_⟩))
  rw [nativeRate,rate_num]
  exact native_price hp he hd h0 ha
theorem proof :qrT6Ada.c1 := by
  intro o i
  apply free_rate ?_ (freeDegree_le o i)
  apply TD.dYm (fun _=>Nat.cast_nonneg _)
  intro k
  rw [member_cast]
  positivity
end qWLt7Ib
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qN36NTb
theorem proof :qTplN5b.c4 := by
  intro Q C z s F e W
  exact q0mTRkc.of_children qTLMB9a.proof qU4m8Td.proof
    q516YUa.proof
    (q9uVqha.of_children qGnKhWc.proof qralmib.proof
      qBMP0Kd.proof qi87Bgb.proof q2ANK6b.proof
      qk9SLHb.proof)
    (qJm9rWb.of_children
      (qHJDQEb.of_children qK8v0ue.proof
        qIPidRd.proof q1XnGpd.proof)
      quQ0Dxa.proof)
    (qZn79Eb.of_children qOHrlse.proof qydrhVa.proof
      qi1t4Ta.proof P5_7_1_5Q.c43464)
    qXARP7c.proof F P6_7_1.degree e W
end qN36NTb
end
section
set_option autoImplicit true
namespace qlVncRd
noncomputable section
open Finset Polynomial
open P6 (K p dw)
open P6_7 (RectTail)
open P6_7_2 (Bs)
open P6_7_2_3 (oldAgreement)
open q6hAhQd (gap quadraticRate)
open qWdRihc (UJ d)
open quN7Z4a (sheet compressionWidth physicalWeight)
open qrsE1ie (geomSquare discriminant)
open gT (aQ abX)
open private bD1 input_degree from ProximityPrize.SubmissionLower.Zzatq8a
open private disc_degree from ProximityPrize.SubmissionLower.ZcErkXc
open private dQt from ProximityPrize.SubmissionLower.Z3swOYa
open scoped Classical
def c1 :Prop :=qrsE1ie.c1
def c2 :Prop :=qrsE1ie.c2
private theorem rate_ge (b:RectTail) : (29:ℚ)≤quadraticRate b:= by
  have hp: (0:ℚ)<(gap b:ℚ) :=Nat.cast_pos.mpr
    (Nat.sub_pos_of_lt ((bD1 b).2.trans_lt (by decide :d<oldAgreement)))
  have hgap:gap b≤48669 :=
    Nat.sub_le_sub_left (Nat.le_add_right 131071 (Bs b).hi) oldAgreement
  have hratio: (16:ℚ)≤8*262144/(gap b:ℚ) := by
    apply (le_div_iff₀ hp).mpr
    exact_mod_cast (show 16*gap b≤8*262144 by omega)
  unfold quadraticRate
  linarith only [hratio]
theorem of_children (h1 :c1) (h2 :c2) :q6hAhQd.c1 := by
  intro b x T J C H hm
  have hz :Set.InjOn x.M.label (T:Set K) := fun _ _ _ _ h=>sub_left_inj.mp h
  have hdeg γ (hγ:γ∈T) : (x.F.scalar γ).natDegree≤d :=
    (input_degree x (hm.subset hγ)).trans (bD1 b).2
  have hrank : ∃ δ:ℕ,Module.finrank aQ (abX J)=δ*2 := by
    obtain ⟨_,C₀,_,_,_,h,_,_⟩:=hm.curve
    exact ⟨C₀.totalDegree,h⟩
  obtain ⟨δ,hδ⟩:=hrank
  obtain ⟨C₀,hC₀,_,⟨S⟩⟩:=sheet (by decide :0<2) hm.curve hδ hm.marks
  let:Fact (Irreducible C₀) :=⟨hC₀⟩
  have hcount:T.card≤29*H+2 := by
    by_cases hw:compressionWidth d 2≤physicalWeight d S.root.equation
    · have hc:=h1 C₀ J T x.M.label x.F.scalar d H S (by decide) hw hz hdeg
      omega
    by_cases hs :geomSquare S.root.equation
    · let W:UJ :=
        ⟨T,algebraMap K cu.L ∘ x.M.label,x.F.scalar,x.M.word,
          fun _ _ _ _ h=>sub_left_inj.mp ((algebraMap K cu.L).injective h),
          x.F.distinct.mono hm.subset,hdeg,
          fun γ hγ =>
            let m:=x.F.mark γ (hm.subset hγ)
            ⟨m.bad.support,(by decide :P5_7_2.A≤dw).trans m.bad.dw,
              m.scalar_hits⟩⟩
      obtain ⟨I⟩:=qPTDwMb.proof C₀ J T x.M.label x.F.scalar x.M.word H S hs hz
      exact dQt W I
    have hd: (discriminant S.root.equation).natDegree<p :=
      (disc_degree d S.root.equation).trans_lt
        ((Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hw) (by decide)).trans
          (by decide :2*compressionWidth d 2<p))
    have hc:=h2 C₀ J T x.M.label x.F.scalar H S hd hs hz
    omega
  have hc: (T.card:ℚ)≤29*H+2 := by exact_mod_cast hcount
  have hr :=mul_le_mul_of_nonneg_right (rate_ge b) (Nat.cast_nonneg (α:=ℚ) H)
  have hmass : (0:ℚ)≤16*(2*(C.totalDegree :ℚ)) := by positivity
  linarith only [hc,hr,hmass]
end
end qlVncRd
end
