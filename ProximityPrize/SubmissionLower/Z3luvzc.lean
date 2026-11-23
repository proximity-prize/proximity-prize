import ProximityPrize.SubmissionLower.ZCYrWLb
import ProximityPrize.SubmissionLower.ZPNEdXb
import ProximityPrize.SubmissionLower.ZUHlXra
import ProximityPrize.SubmissionLower.Z8SV7eb
import ProximityPrize.SubmissionLower.ZZBDV9b
import ProximityPrize.SubmissionLower.ZAW6pTc
set_option Elab.async false
open _root_ renaming Fin.sum_univ_eq_sum_range → zdx, Finset.sum_congr → zUo, Finset.sum_eq_zero → zYF, Finset.sum_mul → zkq, Function.Injective → zq4, Int.cast_mul → zkl, Nat.choose_eq_descFactorial_div_factorial → zn4, Nat.choose_eq_zero_of_lt → zsx
section
set_option autoImplicit true
namespace qMf4Yhd
open qK9H6va
open qaTCFjd (KC)
open P6_6_2 (oppositeBound)
open xE (Flag)
open akL (ahV KP BU)
open fP (GS lP)
open private rank_le_block opposite from ProximityPrize.SubmissionLower.ZPNEdXb
def flag (r :ℕ) :Flag:=⟨53,-offset r,56,16,Vm 53 (offset r)⟩
private theorem space_eq (r :ℕ) :
    GS (iO 53) (-offset r) 56 16=ahV (flag r) := by
  unfold GS ahV
  apply congrArg (MvPolynomial.restrictSupport _)
  ext m
  change (m.degree=53 ∧ -offset r≤(m.weight lP:ℤ) ∧
    (m.weight lP:ℤ)≤56∧m 3≤16) ↔
    ((m.weight BU:ℤ)=53 ∧ -offset r≤(m.weight lP:ℤ) ∧
      (m.weight lP:ℤ)≤56∧(m 3:ℤ)≤16)
  have hg:m.weight BU=m.degree := by
    change m.weight (fun _:Fin 4=>1)=m.degree
    rw [← Finsupp.degree_eq_weight_one]
  rw [hg]
  constructor <;> rintro ⟨hd,hl,hu,hf⟩ <;> exact ⟨by omega,hl,hu,by omega⟩
private theorem range_eq (r :ℕ) :
    LinearMap.range (auo 53 (offset r))=LinearMap.range (KP (flag r)) := by
  ext Q
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨⟨x.val,space_eq r ▸ x.property⟩,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨⟨x.val,(space_eq r).symm ▸ x.property⟩,rfl⟩
theorem block (r :ℕ) :KC 53 r (oppositeBound (flag r)) := by
  refine (rank_le_block 53 (offset r)).trans ?_
  rw [range_eq]
  exact opposite _ (by change -offset r≤1710; unfold offset; omega)
theorem proof :qtjtNFa.c2 :=
  (block 47).trans (by decide)
end qMf4Yhd
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qJdK9Je
noncomputable section
open Polynomial Finset aR dN BO
open P6 (K)
open P6_6 (gZ)
open P6_6_6 (rH Kq aNk anZ)
open qs56oUd (bbl Li)
open wH (Gh qg)
open lB (bF yy abr afz
  SZ Tn)
open Rl (bkW acp He bpC cM4 bFl)
open aFW (aSw)
open scoped BigOperators
local notation "M" => P6_6.bf
open private TaylorChart TaylorChart.mk TaylorChart.pullback TaylorChart.aWC from ProximityPrize.SubmissionLower.B5
open private fat_chart_chamber from ProximityPrize.SubmissionLower.Z8SV7eb
private theorem eyE {q:af 3} (hq:Gh q Kq.b Kq.j) :
    yy (bC (He q)) Kq:= by
  apply abr
  refine ⟨(MvPolynomial.totalDegree_rename_le _ _).trans hq.1,?_,?_⟩
  · change qE (MvPolynomial.rename Fin.castSucc q)≤Kq.j
    rw [Ex.C6,
      MvPolynomial.weightedTotalDegree_rename_of_injective (Fin.castSucc_injective 3)]
    change q.weightedTotalDegree Fin.val≤Kq.j
    rw [← Ex.C6]
    exact hq.2
  · exact (agP.bZ5 q).le
private theorem bZq {x :Shape} (hh:bF (rH x)) :bF (anZ x) := by
  refine ⟨le_max_right _ _,?_⟩
  change 3*max 1 (rH x).t≤ max (rH x).j (Kq.j+1)
  rw [mul_max]
  have hflow:3≤Kq.j+1 := by
    rw [aNk]
    decide
  exact max_le (le_max_of_le_right hflow) (hh.2.trans (le_max_left _ _))
private abbrev constant:K →+* GeoField :=
  j8.comp ((Polynomial.C:ao →+* ao[X]).comp embed)
private def bXW {f :af 4} (T:Li f) :TaylorChart M :=
  TaylorChart.mk (bC T.denom) (fun i=>bC (T.Fr i))
private def byt {f :af 4} (T:Li f) (x a :K) :GeoJets :=
  TaylorChart.pullback (bXW T) (-constant a,fun i=>constant (x^i.val))
private theorem gKZ {f :af 4} (T:Li f) (x a :K) :
  yy (byt T x a) (rH (shape f)) :=
  TaylorChart.aWC (bXW T)
    ⟨abr T.denom_box,fun i=>abr (T.numer_box i)⟩ _
private theorem cFq {S:ao[X]} {f :af 4} (T:Li f)
    (hd:S.natDegree≤gZ) (hf :cK f S=0) (hr :qg f S) :
    cK T.denom S≠0∧cK T.test S=0 ∧
      ∀ i,cK (T.Fr i) S=cK T.denom S*Polynomial.C (S.coeff i.val) := by
  simpa only [bFl] using T.ar5 ao S hd
    ((bFl _ _).trans hf) (fun hz=>hr ((bFl _ _).symm.trans hz))
private theorem byu {f :af 4} (T:Li f) {S:K[X]}
    (hd:S.natDegree≤gZ) (hf :cK f (extend S)=0)
    (hr :qg f (extend S)) (x a :K) :
    An (extend S) (byt T x a)=0↔S.eval x=a := by
  have h:=cFq T (Polynomial.natDegree_map_le.trans hd) hf hr
  let d:=An (extend S) (bC T.denom)
  have hd0:d≠0:= by
    simpa only [d,afz] using (map_ne_zero_iff _ SZ).mpr h.1
  have hn (i:Fin M) :
      An (extend S) (bC (T.Fr i))=d*constant (S.coeff i.val) := by
    rw [afz,h.2.2 i,map_mul]
    simp only [d,afz,constant,RingHom.comp_apply,Polynomial.coeff_map]
  have hsum: (∑ i:Fin M,constant (S.coeff i.val*x^i.val))=constant (S.eval x) := by
    rw [Polynomial.eval_eq_sum_range' (n:=M) (Nat.lt_succ_of_le hd),← zdx]
    exact (map_sum _ _ _).symm
  have hprod :
      (∑ i:Fin M,constant (x^i.val)*(d*constant (S.coeff i.val))) =
        d*constant (S.eval x) := by
    rw [← hsum,mul_sum]
    apply sum_congr rfl
    intro i _
    rw [map_mul]
    ac_rfl
  have he :An (extend S) (byt T x a)=d*constant (S.eval x-a) := by
    have hc (c:GeoField) :An (extend S) (MvPolynomial.C c)=c:=MvPolynomial.eval_C _
    simp only [byt,TaylorChart.pullback,bXW,map_add,map_sum,map_mul,
      hc,hn,hprod,map_sub]
    change -constant a*d+d*constant (S.eval x)=d*(constant (S.eval x) - constant a)
    ring
  rw [he,mul_eq_zero,or_iff_right hd0,map_eq_zero_iff _ (by
    exact SZ.comp (Polynomial.C_injective.comp embed.injective)),sub_eq_zero]
private theorem gtM:aFW.c1 :=
  bjC.of_children bau.proof
    (bzI.of_children cyK.proof bav.proof)
    cyL.proof
private theorem deZ:aFW.c2 :=
  bzJ.of_children bRo.proof bjz.proof
private def an1 {f :af 4} (q:af 3) (T:Li f) (aI:Ideal GeoJets) :af 4 := by
  classical
  exact if bC T.test∈aI then acp q else T.test
private theorem dTg {f :af 4} {D q:af 3} (hq:bbl f D q)
    (T:Li f) (aI:Ideal GeoJets) :
    yy (bC (an1 q T aI)) (anZ (shape f)) := by
  classical
  apply abr
  unfold an1
  split
  · exact ⟨hq.a4g.1.trans ((le_max_right _ _).trans (le_max_left _ _)),
      hq.a4g.2.1.trans (le_max_right _ _),hq.a4g.2.2.trans (le_max_left _ _)⟩
  · exact ⟨T.aX4.1.trans ((le_max_left _ _).trans (le_max_left _ _)),
      T.aX4.2.1.trans (le_max_left _ _),T.aX4.2.2.trans (le_max_right _ _)⟩
private def bQH {f :af 4} (q:af 3) (T:Li f) (C:Ideal GeoJets) :Prop :=
  ∃ aI,(kC f (He q)).IsMinimalPrime aI ∧
    aSw aI (bC (an1 q T aI)) C ∧
    yy (bC (an1 q T aI)) (anZ (shape f))
private theorem d4r {f :af 4} {D q:af 3} {S:ao[X]}
    (hq:bbl f D q) (T:Li f) (hd:S.natDegree≤gZ)
    (hf :Dd f S) (hr :qg f S) (hm:bkW f q T.test S) :
    ∃ C,bQH q T C∧C≤Ch S:= by
  classical
  obtain ⟨aI,hZ,hZS,hmark⟩:=hm
  have ⟨hP,hvan⟩:bC (an1 q T aI)∉aI ∧
      cK (an1 q T aI) S=0:= by
    by_cases h:bC T.test∈aI
    · have hqZ:bC (He q)∈aI :=
        hZ.minimal.le (Ideal.subset_span (by simp))
      have hqS:cK q S=0:= by
        simpa only [bpC] using Rl.Ue.mp (hZS hqZ)
      exact ⟨by simpa [an1,h] using hmark.resolve_left (not_not_intro h),
        by simpa [an1,h] using cM4 hf.1 hr hqS⟩
    · exact ⟨by simp [an1,h],by simpa [an1,h] using (cFq T hd hf.1 hr).2.1⟩
  obtain ⟨C,hC,hCS⟩:=bsq hZS hvan
  exact ⟨C,⟨aI,hZ.minimal,⟨hZ.minimal.isPrime,(hq.simple aI hZ).1,hP,hC⟩,
    dTg hq T _⟩,hCS⟩
private theorem dR3
    {Γ:Finset K} {s :K→K[X]} {f :af 4} (T:Li f)
    (hh:bF (rH (shape f))) (ht:0<(rH (shape f)).t)
    {aI C:Ideal GeoJets} {P:GeoJets} (hC:aSw aI P C)
    (huniq:Set.InjOn s (Γ:Set K)) (hd : ∀ γ∈Γ,(s γ).natDegree≤gZ)
    (hreg : ∀ γ∈Γ,Dd f (extend (s γ))∧qg f (extend (s γ)))
    (hle : ∀ γ∈Γ,C≤Ch (extend (s γ))) :
    agC Γ s (pN C ((rH (shape f)).scale 6)/6) := by
  classical
  intro x a hmiss
  let g (γ:K) :=vS.JV (extend (s γ))
  let A:=Γ.filter fun γ=>(s γ).eval x=a
  let U:=byt T x a
  have hval (γ:K) (hγ:γ∈Γ) :
      An (extend (s γ)) U=0↔(s γ).eval x=a :=
    byu T (hd γ hγ) (hreg γ hγ).1.1 (hreg γ hγ).2 x a
  have hU:U∉C:= by
    obtain ⟨γ,hγ,hne⟩:=hmiss
    intro hmem
    exact hne ((hval γ hγ).mp (hle γ hγ hmem))
  have hb:=(deZ _ hh ht aI P C hC).2 U (A.image g) (gKZ T x a) hU (by
      intro y hy
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hy
      obtain ⟨hΓ,hvalue⟩:=mem_filter.mp hγ
      exact ⟨hle γ hΓ,(hval γ hΓ).mpr hvalue⟩)
  rw [card_image_of_injOn (by
    intro γ hγ δ hδ he
    exact huniq (mem_filter.mp hγ).1 (mem_filter.mp hδ).1
      (Polynomial.map_injective embed embed.injective (vS.bTT he)))] at hb
  change A.card≤_
  omega
theorem proof :qs56oUd.c1 := by
  classical
  intro Γ s f D q hft hq T huniq hd hreg
  let p:=(shape f).iU
  let h:=rH (shape f)
  let box :=anZ (shape f)
  have hp:=Tn f
  have hqbox :bF Kq:= by
    rw [aNk]
    exact ⟨by decide,by decide⟩
  obtain ⟨hh,hht⟩:=fat_chart_chamber (shape f)
  let Ia :=Γ.filter fun γ=>bkW f q T.test (extend (s γ))
  have hfind (γ:Ia) : ∃ C,bQH q T C∧C≤Ch (extend (s γ)) := by
    obtain ⟨hγ,hm⟩:=mem_filter.mp γ.property
    exact d4r hq T (Polynomial.natDegree_map_le.trans (hd γ hγ))
      (hreg γ hγ).1 (hreg γ hγ).2 hm
  choose chooseCurve hcut hon using hfind
  let qv :=Ia.attach.image chooseCurve
  have hcurves (C:Ideal GeoJets) (hC:C∈qv) :bQH q T C:= by
    obtain ⟨γ,_,rfl⟩:=mem_image.mp hC
    exact hcut γ
  have hbound (a :Shape) (ha :bF a) (hat :0<a.t) :
      32*(∑ C∈qv,pN C (a.scale 6))≤6*iH p Kq box a :=
    gtM p Kq box a hp hqbox (bZq hh) ha hat
      _ _ hq.proper (abr ⟨le_max_left _ _,le_rfl,le_rfl⟩)
      (eyE hq.caps) (fun aI=>bC (an1 q T aI)) qv hcurves
  let part (C:Ideal GeoJets) :=Γ.filter fun γ=>C≤Ch (extend (s γ))
  let d (C:Ideal GeoJets) :=pN C (h.scale 6)/6
  let e :=qv.equivFin.symm
  let B:DA Γ :=
    ⟨qv.card,fun i=>part (e i),fun _=>filter_subset _ _,fun i=>d (e i)⟩
  refine ⟨B,?_,?_,?_,?_⟩
  · intro i
    obtain ⟨aI,_,hC,_⟩:=hcurves (e i) (e i).property
    exact dR3 T hh hht hC
      (huniq.mono (filter_subset _ _))
      (fun _ hγ=>hd _ (filter_subset _ _ hγ))
      (fun _ hγ=>hreg _ (filter_subset _ _ hγ))
      (fun _ hγ=>(mem_filter.mp hγ).2)
  · intro γ hγ hm
    let α:Ia :=⟨γ,mem_filter.mpr ⟨hγ,hm⟩⟩
    have hc:chooseCurve α∈qv :=mem_image.mpr ⟨α,mem_attach _ _,rfl⟩
    let i:=qv.equivFin ⟨chooseCurve α,hc⟩
    refine mem_biUnion.mpr ⟨i,mem_univ i,?_⟩
    change γ∈part (e i)
    rw [show e i=⟨chooseCurve α,hc⟩ from e.apply_symm_apply _]
    exact mem_filter.mpr ⟨hγ,hon α⟩
  · have hs :6*B.total ≤ ∑ C∈qv,pN C (h.scale 6) := by
      change 6*(∑ i,d (e i))≤_
      rw [mul_sum]
      calc
        _ ≤ ∑ i,pN (e i).val (h.scale 6) :=
          sum_le_sum fun i _=>Nat.mul_div_le _ _
        _ = _:= by
          rw [← sum_attach qv (fun C=>pN C (h.scale 6))]
          exact Fintype.sum_equiv e _ _ (fun _=>rfl)
    have hb:=hbound h hh hht
    change 32*B.total≤ iH p Kq box h
    omega
  · have hs :6*B.n ≤ ∑ C∈qv,pN C (p.scale 6) := by
      calc
        _ = ∑ _∈qv,6:= by simp [B,Nat.mul_comm]
        _≤_:=sum_le_sum fun C hc=> by
          obtain ⟨aI,_,hC,_⟩:=hcurves C hc
          exact (deZ p hp hft aI _ C hC).1
    have hb:=hbound p hp hft
    change 32*B.n≤ iH p Kq box p
    omega
end
end qJdK9Je
end
section
set_option autoImplicit true
namespace qHFtXyc
open qK9H6va qaTCFjd
open UO (bAQ)
open fP (Ew cF xH oG)
open private rU OZ from ProximityPrize.SubmissionLower.ZZBDV9b


abbrev cV (s :Bool) :ℕ:=if s then 117 else 116
abbrev h (s :Bool) :ℕ:=if s then 34 else 35
abbrev b (s :Bool) :ℕ:=if s then 17 else 14
abbrev u (s :Bool) :ℕ:=if s then 1 else 3
abbrev cap (s :Bool) :ℕ:=if s then 1037 else 1101
abbrev dG (s :Bool) :=ait (cV s) (offset 4)
abbrev EL (s :Bool) :=XN (cV s) (offset 4)
abbrev F:=ZMod P1.p
abbrev block (s :Bool) :=Gy (cV s) (offset 4)
def U (s :Bool) (z f :ℕ) :Prop :=b s+2*u s≤z∧u s≤f
instance (s :Bool) (z f :ℕ) :Decidable (U s z f) :=
  inferInstanceAs (Decidable (_∧_))
theorem upward (s :Bool) :bAQ (U s) := by
  intro z f z' f' hz _ hf hu
  exact ⟨hu.1.trans hz,hu.2.trans hf⟩
abbrev R (s :Bool) :=ajZ (cV s) 4 (U s)
abbrev C (s :Bool) :=ajY (cV s) 4 (U s)
theorem ab6 (s :Bool) :DV (cV s) 4=h s := by cases s <;> decide
theorem a3q (s :Bool) :iO (cV s)=50:= by cases s <;> decide
theorem params (s :Bool) :2*b s+3 * u s=37∧b s+2*u s+15=h s ∧
    1≤u s∧u s≤3:= by cases s <;> decide
theorem dbZ (s :Bool) (e :dG s) :3*e.val 0+e.val 2+2*e.val 3<h s := by
  simpa only [oG,aq6,ab6] using e.property.2
theorem c7m (s :Bool) (e :dG s) :e.val 0+e.val 1+e.val 2+e.val 3=50:= by
  simpa only [cF,a3q] using e.property.1
theorem cwt (s :Bool) (m:EL s) :
    52≤ m.val 1+2*m.val 2 + 3*m.val 3 ∧
    m.val 1+2*m.val 2 + 3*m.val 3≤56:= by
  have hm:=m.property.2
  simp only [offset,xH] at hm
  omega
theorem support {s :Bool} {e :dG s} {m:EL s} (hn:block s e m≠0) :
    m.val 1≤e.val 1∧m.val 2≤e.val 2∧m.val 3≤e.val 3:= by
  have hl (i:Fin 4) (hi:i=1∨i=2∨i=3) :m.val i≤e.val i:= by
    by_contra! hh
    have hz :=zsx hh
    rcases hi with rfl | rfl | rfl <;> exact hn (by simp [Gy,prefixMatrix,hz])
  exact ⟨hl 1 (by simp),hl 2 (by simp),hl 3 (by simp)⟩
abbrev L:=Σ a :Fin 5,Fin (15-3*a.val)
abbrev J:=Fin 5×Fin 5
abbrev lf (s :Bool) (a x :ℕ) :=50-(a+b s + x+u s)
abbrev rf (j k :ℕ) :=8+k - 2*j
abbrev rb (s :Bool) (j:ℕ) :=b s+5+j
abbrev bs2 (s :Bool) (a x :ℕ) :=50-(a+rb s x+(u s - 1))
noncomputable def lr (s :Bool) (i:L) :dG s := by
  refine ⟨rU i.1 (lf s i.1 i.2) (b s+i.2) (u s),?_⟩
  have hi:=i.2.isLt
  have hp:=params s
  simp only [cF,oG,OZ,a3q,aq6,ab6]
  change i.1.val+lf s i.1 i.2+(b s+i.2.val)+u s=50 ∧
    3*i.1.val+(b s+i.2.val)+2*u s<h s
  unfold lf
  omega
noncomputable def rc (s :Bool) (i:J) :EL s := by
  refine ⟨rU (50-(rf i.1 i.2+rb s i.1+(u s - 1)))
    (rf i.1 i.2) (rb s i.1) (u s - 1),?_⟩
  have h₁:=i.1.isLt
  have h₂:=i.2.isLt
  have hp:=params s
  simp only [Ew,cF,xH,OZ,a3q]
  change 50-(rf i.1 i.2+rb s i.1+(u s - 1))+rf i.1 i.2+rb s i.1 +
    (u s - 1)=50 ∧
    (52 :ℤ)≤((rf i.1 i.2+2*rb s i.1+3*(u s - 1) :ℕ) :ℤ) ∧
    ((rf i.1 i.2+2*rb s i.1+3*(u s - 1) :ℕ) :ℤ)≤56∧u s - 1≤16
  unfold rf rb
  omega
theorem aDO (s :Bool) (i:L) :
    (lr s i).val 0=i.1.val∧(lr s i).val 1=lf s i.1 i.2 ∧
    (lr s i).val 2=b s+i.2.val∧(lr s i).val 3=u s := by simp [lr,OZ]
theorem aPL (s :Bool) (i:J) :
    (rc s i).val 1=rf i.1 i.2∧(rc s i).val 2=rb s i.1 ∧
    (rc s i).val 3=u s - 1 := by simp [rc,OZ]
theorem eyK (s :Bool) :zq4 (lr s) := by
  rintro ⟨a,x⟩ ⟨c,y⟩ hh
  have ha :=congrArg (fun e :dG s=>e.val 0) hh
  have hb:=congrArg (fun e :dG s=>e.val 2) hh
  simp only [(aDO _ _).1] at ha
  simp only [(aDO _ _).2.2.1] at hb
  have hac:a=c:=Fin.ext ha
  subst c
  have hxy :x=y :=Fin.ext (by omega)
  subst y
  rfl
theorem fUd (s :Bool) :zq4 (rc s) := by
  rintro ⟨j,k⟩ ⟨l,m⟩ hh
  have h₁:=congrArg (fun e :EL s=>e.val 1) hh
  have h₂:=congrArg (fun e :EL s=>e.val 2) hh
  simp only [(aPL _ _).1] at h₁
  simp only [(aPL _ _).2.1] at h₂
  have hjl:j=l:=Fin.ext (by unfold rb at h₂; omega)
  subst l
  have hj:=j.isLt
  unfold rf at h₁
  have hkm:k=m:=Fin.ext (by omega)
  subst m
  rfl
end qHFtXyc
end
section
set_option autoImplicit true
namespace qHFtXyc
open qK9H6va qaTCFjd
open axF (aaN)
open fP (qI Qg)
open scoped BigOperators
set_option maxRecDepth 1800
set_option maxHeartbeats 1800000
private def eue :Bool→List ℤ
  | false=>[0x50a21960,0x70e8bcb8,0x7b476bb9,0x55f5935d,0x2f989956,0x277cbda1,0x6eccf93a,0x468c9e6c,0x7da6e4ef,0x28c24594,
      0x44f64e0c,0x72a7e9e2,0x6f9ee62,0xe92fec9,0x4f37db78,0x35b3fc35,0x7b22ea6c,0x38ee864f,0x10020ac5,0x7d38b410,
      0xcb688c5, 54092662,0x4f5b533c,0x308d1928,0x36a5b296,0x428687ef,0x4d304761,0x1d489d8f,0x320c7a30,0xb42e7fa,
      0xaac12c2,0x13ebee16,0x3d566360,0x4272ec44,0x1e3828c1,0x4ee20424,0x23a90693,0x1ea7b533,0x244925ce,0x3bc3c384,
      0x611e1e27,0x4533845c,0x3fd0147e,0x48924918,1]
  | true=>[0x7dc3e4f3,0x4274d50c,0x46c60cd8,0x60aa159b,0x1ed557fa,0x146d6dc4,0x741d5a2,0x26b46ac6,0x54aaaace,0x5ab6db67,
      0x3e071e07,0x7327833c,0x3489aead,0x1c141ca9,0x6f22594b,0x32ddf2bd,0xb44ff64,0x2df2d31f,0x5ab6c93a,0x291fb9b2,
      0x6ed6194e,0x1cb68aba,0x4a155530,0x693a83af,0x30d21e96,0x167181c3,0x45f36737,0x4cf3a000,0x542df839,0x58b2d9c4,
      0x4c332e2f,0x3daf8c4d,0x366db699,0x181848e4,0x283ad511,0x2f80551d,0x7031a76e,0x21990a6d,0x4b425ff0,0x7effffcf,
      0x55e04e0b,0x45d29012,0x72e79eeb,0x5e12f676,1]
private def fRH :Bool→List ℤ
  | false=>[1,0x6cdb6db6,0x6cdb6db9,0x33905c64,0x7667f09b,0x244924b2,0x7effffcf,0x6cdb6dda,0x7efffff5,0x70ad3bae,
      759,0x7efffc23,585,0x7effff4d,24, 22264,0x7effb3e8,8712,0x7efff769,0x2449258e,
      1600225,0x7ef82fb9,128018,0x7effa909,2024]
  | true=>[1,0x4c333332,0x3c286bcc,0x3c286bca,0x22351a28,0x3f800023,0x3f7fffc7,0x19666690,0x5ae7bf45,0x3c286bcd,
      0x32ccd05c,0x7efffb27,0x48924c26,0x659998a2,0x1c12dd1b,29095,0x7eff983c,12420,0x6cdb60e2,0x6cdb6f42,
      2269410,0x7ef4750b,197340,0x7eff73d9,0x366dc435]
private def gM5:Bool→List ℤ
  | false=>[592020,37950,2783,0x122492fe]
  | true=>[0x786dfc23,80730,3795,0x32cccd65]
private def counts :Bool→List ℕ
  | false=>[0,0,2,4,9,12,20,20,25,25,
      30,30,35, 35,40,40,45,45, 50,50,
      55, 55,60,51,55, 55,48,45,42,25,
      26,26,14,14,15]
  | true=>[0,0,2,4,9,12,20,20,25,25,
      30,30,35, 35,40,40,45,45, 50,50,
      55, 55,49,49,53,41,44,42,29,28,
      30,15,16,16]
def lw (s :Bool) (a x :ℕ) :=(eue s)[a*(33-3*a)/2 + x]?.getD 0
def cn3 (s :Bool) (j k :ℕ) :=(fRH s)[5*j+k]?.getD 0
def afu (s :Bool) (a :ℕ) :=(gM5 s)[a]?.getD 0
def ld (s :Bool) (x y :ℕ) :ℤ :=
  ju.total (fun a=>ju.total (fun i=>lw s a i*aaN (lf s a i) (b s+i) x y)
    (15-3*a)) 5
def rd (s :Bool) (x y :ℕ) :ℤ :=
  ju.total (fun j=>ju.total (fun k=>cn3 s j k * aaN x y (rf j k) (rb s j)) 5) 5
theorem eyL (s :Bool) (j k :ℕ) (hj:j<10) (hk :k<5) :
    ld s (15+k - 2*j) (b s+j) % (P1.p:ℤ)=0:= by
  cases s <;> interval_cases j <;> interval_cases k <;> decide
theorem bvT (s :Bool) (a x :ℕ) (ha :a<4) (hx :x<12 - 3*a) :
    rd s (bs2 s a x) (rb s x) % (P1.p:ℤ)=0:= by
  cases s <;> interval_cases a <;> interval_cases x <;> decide
private theorem fUc (s :Bool) (x y :ℕ) (hy :y<b s+5) :rd s x y=0:= by
  simp only [rd,ju.abt]
  refine zYF fun j _=>zYF fun k _ => ?_
  have hj:y< rb s j:= by unfold rb; omega
  simp [aaN,ju.n9,← zn4,
    zsx hj]
def U9 (s :Bool) (a x :ℕ) :ℤ:=if x=14-3*a∧a<4 then afu s a else 0
theorem bn7 (s :Bool) (a x :ℕ) (ha :a<5) (hx :x<15-3*a) :
    rd s (lf s a x) (b s + x) % (P1.p:ℤ)=U9 s a x := by
  unfold U9
  split
  · obtain ⟨rfl,ha'⟩ := ‹x=14-3*a∧a<4›
    cases s <;> interval_cases a <;> decide
  · by_cases hx' : x<5
    · rw [fUc s _ _ (by omega),Int.zero_emod]
    · rw [show lf s a x=bs2 s (a+1) (x-5) by
        have hp:=params s
        unfold lf bs2 rb
        omega,
        show b s + x=rb s (x-5) by unfold rb; omega]
      exact bvT s _ _ (by omega) (by omega)
theorem bn6 (s :Bool) :
    (ju.total (fun a=>ju.total (fun x=>lw s a x*U9 s a x)
      (15-3*a)) 5) % (P1.p:ℤ)=0:= by
  let f (a :ℕ) :=ju.total (fun x=>lw s a x*U9 s a x) (15-3*a)
  have hf (a :ℕ) :f a=if a<4 then lw s a (14-3*a)*afu s a else 0:= by
    dsimp only [f]
    rw [ju.abt]
    by_cases ha :a<4
    · rw [ite_eq_left ha,Finset.sum_eq_single (14-3*a)]
      · simp [U9,ha]
      · intro x _ hx
        simp [U9,hx]
      · intro hn
        exact (hn (Finset.mem_range.mpr (by omega))).elim
    · simp [U9,ha]
  change (0+f 0+f 1+f 2+f 3+f 4) % (P1.p:ℤ)=0
  rw [hf 0,hf 1,hf 2,hf 3,hf 4]
  cases s <;> decide
private def fiber (s :Bool) (z :ℕ) :ℕ :=
  qI (z/2+1) fun c=>if U s z c then aEG 50 (h s) 4 z c else aHb 50 4 z c
private theorem b2X (s :Bool) (z :ℕ) (hz :z<h s) :
    fiber s z=(counts s)[z]?.getD 0:= by
  cases s
  · change z<35 at hz
    interval_cases z <;> decide
  · change z<34 at hz
    interval_cases z <;> decide
theorem dRa (s :Bool) :aht (iO (cV s))
    (DV (cV s) 4) 4 (U s)≤ cap s+2 := by
  rw [a3q,ab6]
  change qI (h s) (fiber s)≤_
  calc
    _=qI (h s) (fun z=>(counts s)[z]?.getD 0) := by
      simp only [Qg]
      exact zUo rfl fun z _=>b2X s z z.isLt
    _≤_:= by cases s <;> decide
end qHFtXyc
end
section
set_option autoImplicit true
namespace qHFtXyc
open qK9H6va qaTCFjd
open axF (aaN)
open private order from ProximityPrize.SubmissionLower.CG
open private XA asf ab7 awG cast_zero from ProximityPrize.SubmissionLower.CG
open scoped Matrix BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private def li:L:=⟨4,⟨2,by decide⟩⟩
private def ri:J:=(0,0)
private def left (s :Bool) :=XA (lr s) fun i=>(lw s i.1 i.2 :F)
private def right (s :Bool) :=XA (rc s) fun i=>(cn3 s i.1 i.2 :F)
private theorem left_apply (s :Bool) (m:EL s) :
    (left s ᵥ* block s) m = ∑ i:L,(lw s i.1 i.2 :F)*block s (lr s i) m :=
  ab7 _ _ _
private theorem right_apply (s :Bool) (e :dG s) :
    (block s *ᵥ right s) e = ∑ i:J,(cn3 s i.1 i.2 :F)*block s e (rc s i) := by
  change (fun m=>block s e m) ⬝ᵥ right s= _
  rw [dotProduct_comm]
  exact ab7 _ _ _
private theorem brE (s :Bool) (m:EL s) (hf :m.val 3=u s) :
    (left s ᵥ* block s) m=(ld s (m.val 1) (m.val 2) :F) := by
  rw [left_apply,ld,← awG,Int.cast_sum]
  apply zUo rfl
  intro i _
  simp only [zkl,aaN,Int.cast_natCast,ju.n9,
    ← zn4,Gy,prefixMatrix,
    aDO,hf,Nat.choose_self,Nat.cast_one,mul_one]
private theorem aJl (s :Bool) (e :dG s) :
    (block s *ᵥ right s) e =
      (rd s (e.val 1) (e.val 2) :F)*(Nat.choose (e.val 3) (u s - 1) :F) := by
  rw [right_apply,Fintype.sum_prod_type,rd,ju.abt,
    ← zdx,Int.cast_sum,zkq]
  refine zUo rfl fun j _ => ?_
  rw [ju.abt,← zdx,Int.cast_sum,zkq]
  refine zUo rfl fun k _ => ?_
  simp only [zkl,aaN,Int.cast_natCast,ju.n9,
    ← zn4,Gy,prefixMatrix,
    aPL,mul_assoc]
private theorem aOu (s :Bool) (m:EL s) (hm : ¬ C s m) :
    (left s ᵥ* block s) m=0:= by
  have hp:=params s
  obtain ⟨hlo,hhi⟩:=cwt s m
  by_cases hs :m.val 3=u s∧b s≤ m.val 2∧m.val 2<b s+10
  · obtain ⟨hf,ha,hc⟩:=hs
    let j:=m.val 2 - b s
    let k :=m.val 1+2*m.val 2 + 3*m.val 3 - 52
    have hj:j<10 := by dsimp [j]; omega
    have hk :k<5:= by dsimp [k]; omega
    have hx :m.val 1=15+k - 2*j:= by dsimp [j,k]; omega
    have hy :m.val 2=b s+j:= by dsimp [j]; omega
    rw [brE s m hf,hx,hy]
    exact cast_zero (eyL s j k hj hk)
  · rw [left_apply]
    refine zYF fun i _=>mul_eq_zero_of_right _ ?_
    by_contra hn
    obtain ⟨_,hb,hc⟩:=support hn
    rw [(aDO s i).2.2.2] at hc
    have hw:=dbZ s (lr s i)
    simp only [aDO] at hw
    simp only [C,ajY,ab6,order,U] at hm
    omega
private theorem aW0 (s :Bool) (e :dG s) (he : ¬ R s e) :
    (block s *ᵥ right s) e=0:= by
  have hp:=params s
  have hd:=c7m s e
  have hw:=dbZ s e
  by_cases hs :e.val 3=u s - 1∧b s+5≤e.val 2
  · obtain ⟨hf,hb⟩:=hs
    let x :=e.val 2 - (b s+5)
    have ha :e.val 0<4 := by omega
    have hx :x<12 - 3*e.val 0:= by dsimp [x]; omega
    have hy :e.val 2=rb s x := by dsimp [x,rb]; omega
    have hz :e.val 1=bs2 s (e.val 0) x := by unfold bs2; omega
    rw [aJl,hz,hy,cast_zero (bvT s _ _ ha hx),zero_mul]
  · rw [right_apply]
    refine zYF fun i _=>mul_eq_zero_of_right _ ?_
    by_contra hn
    have hm:=(cwt s (rc s i)).1
    obtain ⟨hx,hb,hc⟩:=support hn
    simp only [aPL] at hm hx hb hc
    simp only [R,ajZ,a3q,order,U] at he
    unfold rb at hb
    omega
private theorem eJL (s :Bool) : (left s ᵥ* block s) ⬝ᵥ right s=0:= by
  rw [← Matrix.dotProduct_mulVec,left,ab7]
  calc
    _=(∑ i:L,((lw s i.1 i.2*U9 s i.1 i.2 :ℤ) :F)) *
        (Nat.choose (u s) (u s - 1) :F) := by
      rw [zkq]
      refine zUo rfl fun i _ => ?_
      have hm:=bn7 s i.1 i.2 i.1.isLt i.2.isLt
      have hc: (rd s (lf s i.1 i.2) (b s+i.2.val) :F)=(U9 s i.1 i.2 :F) := by
        rw [← ZMod.intCast_mod (rd _ _ _) P1.p,hm]
      rw [aJl,(aDO _ i).2.1,(aDO _ i).2.2.1,
        (aDO _ i).2.2.2,hc,zkl,mul_assoc]
    _=0:= by
      rw [← Int.cast_sum,awG 5 (fun a=>15-3*a)
        (fun a x=>lw s a x*U9 s a x),cast_zero (bn6 s),zero_mul]
private theorem Ig (s :Bool) :R s (lr s li)∧C s (rc s ri) := by
  simp only [R,C,ajZ,ajY,a3q,ab6,order,U,aDO,aPL]
  cases s <;> decide
private theorem bound (s :Bool) :KC (cV s) 4 (cap s) := by
  classical
  have hl:left s (lr s li)=1 :=
    (asf _ _ (eyK s) _).trans (by cases s <;> decide)
  have hr :right s (rc s ri)=1 :=
    (asf _ _ (fUd s) _).trans (by cases s <;> decide)
  have hsave :=a0C.glI (block s) (R s) (C s)
    (aEb _ _ _ (upward s)) _ _ _ _ hl hr (Ig s).1 (Ig s).2
    (aOu s) (aW0 s) (eJL s)
  exact Nat.le_of_add_le_add_right ((hsave.trans (aHj _ _ _)).trans (dRa s))
theorem proof :qaTCFjd.c3:=⟨bound false,bound true⟩
end
end qHFtXyc
end
