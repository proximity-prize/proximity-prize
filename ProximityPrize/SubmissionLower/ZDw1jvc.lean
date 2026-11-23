import ProximityPrize.SubmissionLower.ZWpWUpd
import ProximityPrize.SubmissionLower.Zzatq8a
import ProximityPrize.SubmissionLower.ZPoi06c
set_option Elab.async false
set_option maxHeartbeats 1500000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qNRjwze
noncomputable section
open P6 (K dw)
open P6_7 (RectTail)
open P6_7_2 (Input)
open P6_7_2_3 (degree lineFee)
open P5_7_1 (wD)
open P5_7 (midAgreement)
open qckEfrc (Var Box Regular point)
open qp56ikd (gap errors total top seed kK charged)
open cu (L FX kr)
open Finset MvPolynomial
open scoped Classical
open private e rename_caps from ProximityPrize.SubmissionLower.ZhyMlza
open private OF OF.mk from ProximityPrize.SubmissionLower.ZogIzOe
private theorem rename_root {b:RectTail} {x :Input b} {g:LineRow} {γ:K} (h:LineRoot x g γ) :
    ∃ z :L,Regular (rename e g) z (x.F.scalar γ) := by
  obtain ⟨z,hz⟩:=h
  have hp:point z (x.F.scalar γ) ∘ e =
      ![algebraMap L FX z,kr (x.F.scalar γ),kr (x.F.scalar γ).derivative] := by
    funext i
    fin_cases i <;> rfl
  refine ⟨z,?_⟩
  unfold Regular
  rw [show (some 1 :Var)=e 2 by rfl,pderiv_rename e.injective,eval_rename,eval_rename,hp]
  exact hz
private theorem fixedWord {b:RectTail} (x :Input b) {T:Finset K} (hT:T⊆x.Γ) :
    OF x.M.word T x.F.scalar (degree b) := by
  refine OF.mk (x.F.distinct.mono hT) ?_ ?_
  · intro γ hγ
    exact (P6_7.aic x.F (hT hγ)).trans (Nat.add_le_add_left (emE x) _)
  · intro γ hγ
    let m:=x.F.mark γ (hT hγ)
    exact ⟨m.bad.support,(by decide :midAgreement≤dw).trans m.bad.dw,m.scalar_hits⟩
private theorem bw (r :RectTail) {n b j u:ℕ}
    (h:gap (degree r)*n≤2*errors*kK (degree r) b j u+gap (degree r)*(b+u)) :
    n≤lineFee r b j u:= by
  let a :=total (degree r) b
  let v :=top (degree r) b j
  let U:=seed (degree r) u
  let M:=kK (degree r) b j u
  let C:=u*(2*a+v)+U*(2*b+j)+b*v+j*a+u+b+j
  have hM:M=u*(2*a*v-v*v)+2*U*(b*v+j*(a-v)) := by
    change kK (degree r) b j u= _
    rw [kK,cappedBidegreeMixedVolume_eq (show v≤a from min_le_left _ _)]
    change u*v*(2*a-v)+2*U*(b*v+j*(a-v))= _
    rw [Nat.mul_assoc u v,Nat.mul_sub_left_distrib,mul_comm v (2*a)]
  change n≤(2*errors*((u*(2*a*v-v*v)+2*U*(b*v+j*(a-v)))+C)+gap (degree r)-1)/gap (degree r)+b+u+1
  rw [← hM]
  have hx :gap (degree r)*(n-(b+u))≤2*errors*M:= by
    by_cases hn:n≤b+u
    · simp [Nat.sub_eq_zero_of_le hn]
    · have hh:=congrArg (gap (degree r) * ·) (Nat.sub_add_cancel (show b+u≤n by omega))
      rw [Nat.mul_add] at hh
      change gap (degree r)*n≤2*errors*M+gap (degree r)*(b+u) at h
      omega
  have hnum :2*errors*M≤2*errors*(M+C)+gap (degree r)-1 := by
    have hh:=Nat.mul_le_mul_left (2*errors) (Nat.le_add_right M C)
    have hg:0<gap (degree r) := by cases r <;> decide
    omega
  have hd:=(Nat.le_div_iff_mul_le (by cases r <;> decide :0<gap (degree r))).mpr
    ((mul_comm _ _).trans_le (hx.trans hnum))
  omega
theorem line_count {r :RectTail} (x :Input r) (f :cu.Jet) (g:LineRow)
    (hj:0<wD f 1) (hu:0<wD f 2) (hcaps :LineCaps f g) :
    (x.Γ.filter (LineRoot x g)).card≤lineFee r (wD f 0) (wD f 1) (wD f 2) := by
  classical
  have hf :f≠0:=Polynomial.ne_zero_of_natDegree_gt hj
  have hb:0<wD f 0:=hj.trans_le (akZ.caQ hf)
  let T:=x.Γ.filter (LineRoot x g)
  have hG:rename e g∈Box (wD f 0) (wD f 1) (wD f 2) :=rename_caps hcaps
  have hz (γ:K) : ∃ z :L,γ∈T→Regular (rename e g) z (x.F.scalar γ) := by
    by_cases hγ:γ∈T
    · obtain ⟨z,hz⟩:=rename_root (mem_filter.mp hγ).2
      exact ⟨z,fun _=>hz⟩
    · exact ⟨0,fun hh=>(hγ hh).elim⟩
  choose z hz using hz
  have hw:=fixedWord x (show T⊆x.Γ from filter_subset _ _)
  have h:=charged hw (by cases r <;> decide) (by cases r <;> decide) hb hj hu hG z hz
  apply bw r (n:=T.card) (b:=wD f 0) (j:=wD f 1) (u:=wD f 2)
  exact_mod_cast h
end
end qNRjwze
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 6000
namespace qNRjwze
noncomputable section
open Finset
open P6 (p)
open P6_7 (RectTail)
open P6_7_2 (Aux auxiliary strongWidth auxReserve)
open P6_7_2_3 (Origin last introCap originShape topCut)
open cu (Jet Shape)
open pI (oU)
open P5_7_1 (wD)
open TD (auN arC aIe)
open akZ (ajz btm aHP weightedDegree cs5 bCj)
open scoped Classical
theorem mass_small (b:RectTail) (k :Fin 4) :massCap b k<p:= by
  cases b <;> fin_cases k <;> decide
theorem origin_J (b:RectTail) (o:Origin) : (originShape b o).J≤(originShape b o).B:= by
  cases b <;> fin_cases o <;> decide
theorem last_enclose {b:RectTail} {f c:Jet} (h : ∀ j,wD f j≤ introCap b last j) (l:Bool)
    (hc:oU c (if l then btm f else topCut b (wD f))) :
    oU c (originShape b last) := by
  have e :originShape b last=topCut b (introCap b last) :=rfl
  rw [e]
  apply (bCj _ _).mpr
  intro i
  refine ((bCj _ _).mp hc i).trans ?_
  cases l <;> fin_cases i
  · change 164+19*(wD f 0-1)≤164+19*(introCap b last 0-1)
    gcongr
    exact h 0
  · change 50+19*(wD f 1-1)≤50+19*(introCap b last 1-1)
    gcongr
    exact h 1
  · change strongWidth b+19*wD f 2≤ strongWidth b+19*introCap b last 2
    gcongr
    exact h 2
  · exact (h 0).trans (by cases b <;> decide)
  · exact (h 1).trans (by cases b <;> decide)
  · exact (h 2).trans (by cases b <;> decide)
private def account (b:RectTail) (k :Fin 4) :List (ℕ×Shape)→(Fin 3→ℕ)→(Fin 3→ℕ)→ℕ
  | [],cap,old=>aIe cap old (originShape b last) k
  | (r,s) :: next,cap,old =>
    aIe cap old s k+account b k next
      (fun j=>min (cap j) (auN s j/(r+1)))
      (fun j=>max (old j) (arC s k j))
private abbrev stages (b:RectTail) :=List.ofFn fun i:Aux=>(auxReserve i,auxiliary b i)
private theorem account_cap (b:RectTail) (k :Fin 4) :
    account b k (stages b) (introCap b 0) (fun _=>0)≤ massCap b k := by
  cases b <;> fin_cases k <;> decide
theorem charge (b:RectTail) (D:Finset Jet) (origin :Jet→Origin)
    (nest : ∀ o j,ajz (D.filter (fun f=>o≤origin f)) j≤ introCap b o j)
    (k :Fin 4) :
    (∑ f∈D,aHP (originShape b (origin f)) k f)≤ massCap b k := by
  let tail (n:ℕ) :=D.filter fun f=>n≤(origin f).val
  have bound : ∀ ls (o:Origin),(stages b).drop o.val=ls → ∀ old,
      (∑ f∈tail o.val,aHP (originShape b (origin f)) k f) ≤
        account b k ls (introCap b o) old+weightedDegree old (tail o.val) := by
    intro ls
    induction ls with
    | nil =>
      intro o he old
      have eq :o=last := by
        have hh:=congrArg List.length he
        simp only [List.length_drop,List.length_nil,List.length_ofFn] at hh
        apply Fin.ext
        have ho:=o.isLt
        change o.val=13
        omega
      subst o
      have hbox (f :Jet) (hf :f∈tail last.val) :origin f=last := by
        apply Fin.ext
        have h:=(mem_filter.mp hf).2
        have ho:=(origin f).isLt
        change 13≤(origin f).val at h
        change (origin f).val=13
        omega
      have ht:=cs5 (D:=tail last.val) (T := ∅) (empty_subset _) _
        old (originShape b last) k (nest last)
      simp only [sdiff_empty,weightedDegree,ajz,sum_empty,mul_zero,sum_const_zero,add_zero] at ht
      rw [sum_congr rfl (fun f hf=>congrArg (fun o=>aHP (originShape b o) k f) (hbox f hf))]
      simpa only [account,weightedDegree,ajz,add_comm] using ht
    | cons a ls ih =>
      intro o he old
      have hlt:o.val<13:= by
        have hh:=congrArg List.length he
        simp only [List.length_drop,List.length_cons,List.length_ofFn] at hh
        omega
      let i:Aux :=⟨o.val,hlt⟩
      have hoi:i.castSucc=o:=Fin.ext rfl
      have hi:o.val<(stages b).length:= by simpa using hlt
      rw [List.drop_eq_getElem_cons hi] at he
      obtain ⟨ha,hrest⟩:=List.cons.inj he
      have heq : (stages b)[o.val]=(auxReserve i,auxiliary b i) := by
        simp only [List.getElem_ofFn]
        rfl
      rw [heq] at ha
      subst a
      have hsub:tail i.succ.val⊆tail o.val := fun f hf =>
        let hm:=mem_filter.mp hf
        mem_filter.mpr ⟨hm.1,(Nat.le_succ o.val).trans hm.2⟩
      have hbox (f :Jet) (hf :f∈tail o.val \ tail i.succ.val) :
          originShape b (origin f)=auxiliary b i:= by
        obtain ⟨h₁,h₂⟩:=mem_sdiff.mp hf
        obtain ⟨hD,h₁⟩:=mem_filter.mp h₁
        have hn : ¬ o.val+1≤(origin f).val := fun h=>h₂ (mem_filter.mpr ⟨hD,h⟩)
        have eq : (origin f).val=o.val := by omega
        unfold originShape
        rw [dite_eq_left (eq.symm ▸ hlt)]
        exact congrArg (auxiliary b) (Fin.ext eq)
      let w:= fun j=>max (old j) (arC (auxiliary b i) k j)
      have step:=cs5 hsub (introCap b o) old (auxiliary b i) k (nest o)
      have rest:=ih i.succ hrest w
      rw [show introCap b i.succ=fun j =>
        min (introCap b o j) (auN (auxiliary b i) j/(auxReserve i+1)) from
          funext (fun j=> by rw [intro_succ,hoi])] at rest
      calc
        _=(∑ f∈tail o.val \ tail i.succ.val,aHP (auxiliary b i) k f) +
            ∑ f∈tail i.succ.val,aHP (originShape b (origin f)) k f := by
          rw [← sum_sdiff hsub]
          congr 1
          exact sum_congr rfl fun f hf=>congrArg (fun s=>aHP s k f) (hbox f hf)
        _≤_:= by
          let a := ∑ f∈tail o.val \ tail i.succ.val,aHP (auxiliary b i) k f
          let c:=account b k ls
            (fun j=>min (introCap b o j) (auN (auxiliary b i) j/(auxReserve i+1))) w
          let d:=aIe (introCap b o) old (auxiliary b i) k
          change a+_≤d+c+weightedDegree old (tail o.val)
          calc
            _≤a+(c+weightedDegree w (tail i.succ.val)) :=Nat.add_le_add_left rest _
            _=c+(a+weightedDegree w (tail i.succ.val)) := by ac_rfl
            _≤ c+(weightedDegree old (tail o.val)+d) :=Nat.add_le_add_left step _
            _ = _:= by ac_rfl
  have h:=bound (stages b) 0 rfl (fun _=>0)
  have htail:tail 0=D:=Finset.filter_true_of_mem fun _ _=>Nat.zero_le _
  change (∑ f∈tail 0,aHP (originShape b (origin f)) k f)≤_ at h
  rw [htail] at h
  exact (by simpa [weightedDegree] using h:_≤account b k (stages b) (introCap b 0) _)
    |>.trans (account_cap b k)
end
end qNRjwze
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q6hAhQd
noncomputable section
open Finset
open P6 (p dw)
open P6_7 (RectTail weakenFamily)
open P6_7_2 (Input Bs free)
open P6_7_2_3 (FreeTest freeStage freeStop marks sectionMass MemberFits NativeOK nativeRate FreeOK freeProjection BC memberCap Tl pointWeight freePrice freeAllowance)
open TD (GM FP a3x dYl cK6)
open cu (Shape qD)
open gT (Ambient)
open pI (by6 weight dot)
open YY (bAG xg Si by9 aef a9E)
open private bKS from ProximityPrize.SubmissionLower.ZPoi06c
open private cag c2p c0U ddj b1I diE from ProximityPrize.SubmissionLower.G
open private mix mix_zero ePj from ProximityPrize.SubmissionLower.ZzWMDba
open scoped Classical BigOperators
def c1 :Prop :=
  ∀ {b:RectTail} {x :Input b} {T J C H},DescendedMarks x T J C 2 H →
    (T.card:ℚ)≤16*(2*(C.totalDegree :ℚ))+quadraticRate b*H+2
def c2 :Prop :=
  ∀ {b:RectTail} {x :Input b} {T J C g H},DescendedMarks x T J C g H →
    3≤g → ∀ e c W M,NativeOK (P6_7_2_3.degree b) g e c W M →
      (T.card:ℚ)≤nativeSlope C.totalDegree g*((g:ℚ)*C.totalDegree) +
        nativeRate (P6_7_2_3.degree b) g e c W*H+g
private abbrev graphRate (g:ℕ) :ℚ:=((p+1 :ℕ) :ℚ)/g
private theorem rated_descended (h1 :c1) (h2 :c2)
    {b o i} {x :Input b} {T J C g H} (hm:DescendedMarks x T J C g H) (hg:0<g)
    {a h:ℚ} (rate :FreeOK b o i a h) (hd: (C.totalDegree :ℚ)≤freeProjection b o i)
    (direct : (T.card:ℚ)≤((p+1 :ℕ) :ℚ)*C.totalDegree) :
    (T.card:ℚ)≤a*((g:ℚ)*C.totalDegree)+h*H+g:= by
  obtain ⟨hd0,_,hda,hh,hr⟩:=rate
  have ha :=hd0.trans hda
  have hgQ:0<(g:ℚ) :=Nat.cast_pos.mpr hg
  have hH : (0:ℚ)≤H :=Nat.cast_nonneg _
  have hmass :0≤(g:ℚ)*C.totalDegree :=mul_nonneg hgQ.le (Nat.cast_nonneg _)
  have hdir : (T.card:ℚ)≤graphRate g*((g:ℚ)*C.totalDegree) := by
    rw [← mul_assoc,graphRate,div_mul_cancel₀ _ hgQ.ne']
    exact direct
  by_cases hl:a<graphRate g
  · rcases hr g hg hl with hρ | ⟨rfl,hρ⟩ | ⟨rfl,h₀,hρ⟩ | ⟨hg3,e,c,W,M,hw,h₀,hρ⟩
    · exact mix_zero ha hl hH hgQ.le hdir (persistent hg hm) hρ
    · exact mix_zero ha hl hH hgQ.le hdir (linear hm) hρ
    · exact mix (h₀.trans (min_le_left _ _)) hl hH hgQ.le hdir (h1 hm) hρ
    · have hs :nativeSlope C.totalDegree g≤nativeSlope (freeProjection b o i) g:= by
        unfold nativeSlope
        gcongr
      have hn:=(h2 hm hg3 e c W M hw).trans (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right hs hmass) le_rfl) le_rfl)
      exact mix (h₀.trans (min_le_left _ _)) hl hH hgQ.le hdir hn hρ
  · exact hdir.trans ((mul_le_mul_of_nonneg_right (le_of_not_gt hl) hmass).trans
      ((le_add_of_nonneg_right (mul_nonneg hh hH)).trans (le_add_of_nonneg_right hgQ.le)))
private theorem fTy (h1 :c1) (h2 :c2)
    {b o i} (x :Input b) {I:Ideal Ambient} (geom:by6 I) {a h:ℚ}
    (rate :FreeOK b o i a h) (hdm: (aef I:ℚ)≤freeProjection b o i) :
    ((marks x I).card:ℚ)≤(a+1)*aef I+h*a9E I:= by
  let T:=marks x I
  have ⟨hd0,hdp,hda,hh,_⟩:=rate
  have hp:aef I<p:= by exact_mod_cast hdm.trans_lt hdp
  have ha :=hd0.trans hda
  have slice :bAG I:=⟨geom.1,geom.2.1,geom.2.2.1,geom.2.2.2.1⟩
  obtain ⟨f,hf,he,hpos,hd⟩:=GK.proof I slice
  have hdeg: (f.totalDegree :ℚ)≤aef I:=Nat.cast_le.mpr hd
  have hlabels : ∀ z∈T.image x.M.label,qD z f=0:= by
    intro z hz
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz
    apply c2p (mem_filter.mp hγ).2
    rw [he]
    exact Ideal.mem_span_singleton_self f
  have hcard: (T.image x.M.label).card=T.card :=
    card_image_of_injective _ (fun _ _ h=>sub_left_inj.mp h)
  change (T.card:ℚ)≤(a+1)*aef I+h*a9E I
  suffices bound: (T.card:ℚ)≤a*aef I+h*a9E I+aef I by
    exact bound.trans_eq (by ring)
  by_cases hconst:by9 (xg I)
  · obtain ⟨C,hC,hIC⟩:=hconst
    have heq :=b1I f hf.ne_zero C (he.symm.trans hIC)
    obtain ⟨g,hg,hroot,hmass⟩:=ePj I C slice geom.2.2.2.2 hC hIC
    have hm:DescendedMarks x T (Si I) C g (a9E I) :=
      ⟨filter_subset _ _,hroot,hC,hIC,heq ▸ hpos,hmass.trans_lt hp,
        fun _ hγ=>cag (mem_filter.mp hγ).2⟩
    have hdir :=ddj f hf.ne_zero (hd.trans_lt hp) (T.image x.M.label) hlabels
    rw [hcard,heq] at hdir
    have hdC: (C.totalDegree :ℚ)≤freeProjection b o i:=(heq ▸ hdeg).trans hdm
    have ht:=rated_descended h1 h2 hm hg rate hdC (by exact_mod_cast hdir)
    have hmassQ: (g:ℚ)*C.totalDegree≤aef I:= by
      rw [mul_comm]
      exact_mod_cast hmass
    have hgQ: (g:ℚ)≤aef I :=
      Nat.cast_le.mpr ((Nat.le_mul_of_pos_left g hm.plane_pos).trans hmass)
    exact ht.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hmassQ ha) le_rfl) hgQ)
  · have ht:=c0U p f hf (he ▸ hconst) (T.image x.M.label) hlabels
    rw [hcard] at ht
    calc
      _≤(f.totalDegree :ℚ)^2 := by exact_mod_cast ht
      _≤a*aef I:= by
        rw [pow_two]
        exact mul_le_mul ((hdeg.trans hdm).trans hda) hdeg (Nat.cast_nonneg _) ha
      _≤_:=(le_add_of_nonneg_right (mul_nonneg hh (Nat.cast_nonneg _))).trans
        (le_add_of_nonneg_right (Nat.cast_nonneg _))
private abbrev weightQ (s :Shape) (j:Fin 3) :GM:= fun k=>weight s j k
private theorem caps (b:RectTail) (i:FreeTest) :
    let s :=free b (freeStage i)
    let t:=(Bs b).terminal
    s.J≤ s.B∧s.U≤2*t.U∧s.B-s.J≤t.B-t.J∧s.J≤t.J:= by
  cases b <;> fin_cases i <;> decide
private theorem weight_seed (s :Shape) (hj:s.J≤ s.B) :
    weightQ s 0=Tl s.U s := by
  funext k
  fin_cases k
  · rfl
  · exact Nat.cast_sub hj
  · rfl
  · rfl
private theorem seedBudget {b o i Q} (hQ:MemberFits b o (freeStop i) Q) :
    FP (weightQ (free b (freeStage i)) 0) (sectionMass Q)≤freeProjection b o i:= by
  let s :=free b (freeStage i)
  let t:=(Bs b).terminal
  obtain ⟨hs,hu,hy,hj⟩:=caps b i
  have ht:t.J≤t.B:= by cases b <;> decide
  change FP (weightQ s 0) (sectionMass Q) ≤
    min (FP (Tl (2*t.U) t) (BC b))
      (FP (Tl s.U s) (memberCap b o (freeStop i)))
  let t' : Shape := {t with U:=2*t.U}
  change _≤ min (FP (Tl t'.U t') (BC b)) _
  rw [← weight_seed t' ht,← weight_seed s hs]
  refine le_min ?_ (a3x (fun _=>Nat.cast_nonneg _) hQ)
  have hweight (k :Fin 4) :weightQ s 0 k≤weightQ t' 0 k := by
    fin_cases k
    · exact Nat.cast_le.mpr hu
    · exact Nat.cast_le.mpr hy
    · exact Nat.cast_le.mpr hj
    · exact Nat.cast_le.mpr (Nat.zero_le _)
  exact (dYl (fun k=>Nat.cast_nonneg (pI.pN Q k)) hweight).trans
    (a3x (fun _=>Nat.cast_nonneg _) (fun k=>(hQ k).trans (min_le_right _ _)))
private theorem eNY (b:RectTail) (i:FreeTest) (a h:ℚ) (v :GM) :
    let s :=free b (freeStage i)
    (a+1)*FP (weightQ s 0) v+h*FP (weightQ s 1) v+FP (weightQ s 2) v =
      FP (freePrice b i a h+freeAllowance b i) v := by
  dsimp only
  rw [cK6]
  unfold FP
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  rw [← add_mul]
  congr 1
  have hj:=(caps b i).1
  fin_cases k <;>
    simp [weightQ,weight,freePrice,freeAllowance,pointWeight,Tl,Nat.cast_sub hj,Pi.add_apply] <;> ring
theorem of_children (h1 :c1) (h2 :c2) :P6_7_2_3.c4 := by
  intro b x o i Q hA _ _ hQ G hG hproper hzero a h rate
  let s :=free b (freeStage i)
  let F:=weakenFamily x.F (show P5_7.farAgreement≤dw by decide)
  obtain ⟨C,hC,hcover⟩:=bKS F s (caps b i).1 hA hG hproper
  have hcost (j:Fin 3) : (C.cost j:ℚ)≤FP (weightQ s j) (sectionMass Q) := by
    simpa only [FP,dot,weightQ,sectionMass,Nat.cast_sum,Nat.cast_mul]
      using (Nat.cast_le (α:=ℚ)).mpr (hC j)
  let U:=C.qv.biUnion (marks x)
  have hsub:marks x Q⊆C.direct∪U:= by
    intro γ hγ
    obtain ⟨hΓ,hmark⟩:=mem_filter.mp hγ
    rcases hcover γ hΓ hmark (hzero γ hΓ hmark) with hm | ⟨I,hI,hm⟩
    · exact mem_union_left _ hm
    · exact mem_union_right _ (mem_biUnion.mpr ⟨I,hI,mem_filter.mpr ⟨hΓ,hm⟩⟩)
  have hs : ∑ I∈C.qv,aef I=C.cost 0:=rfl
  have hy : ∑ I∈C.qv,a9E I=C.cost 1 :=rfl
  have hu: (U.card:ℚ)≤(a+1)*C.cost 0+h*C.cost 1 := calc
    _ ≤ ∑ I∈C.qv,((marks x I).card:ℚ) :=diE _ _
    _ ≤ ∑ I∈C.qv,((a+1)*aef I+h*a9E I) := by
      apply sum_le_sum
      intro I hI
      have hd:aef I≤C.cost 0:=hs ▸ single_le_sum (fun _ _=>Nat.zero_le _) hI
      exact fTy h1 h2 x (C.geometric I hI) rate
        ((Nat.cast_le.mpr hd).trans ((hcost 0).trans (seedBudget hQ)))
    _ = _:= by simp only [sum_add_distrib,← mul_sum,← Nat.cast_sum,hs,hy]
  obtain ⟨hd0,_,hda,hh,_⟩:=rate
  have ha :0≤a+1 :=add_nonneg (hd0.trans hda) zero_le_one
  have hsum: (marks x Q).card≤U.card+C.direct.card :=
    (card_le_card hsub).trans ((card_union_le _ _).trans_eq (Nat.add_comm _ _))
  calc
    _≤(U.card:ℚ)+C.cost 2 := by exact_mod_cast hsum
    _≤(a+1)*C.cost 0+h*C.cost 1+C.cost 2 :=add_le_add hu le_rfl
    _≤(a+1)*FP (weightQ s 0) (sectionMass Q)+
        h*FP (weightQ s 1) (sectionMass Q)+FP (weightQ s 2) (sectionMass Q) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hcost 0) ha)
        (mul_le_mul_of_nonneg_left (hcost 1) hh)) (hcost 2)
    _ = _:=eNY b i a h (sectionMass Q)
end
end q6hAhQd
end
