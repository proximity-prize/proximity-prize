import ProximityPrize.SubmissionLower.ZkoLWnc
import ProximityPrize.SubmissionLower.ZZr1mWc
set_option Elab.async false
open _root_ renaming Fin.castSucc → z1o, Finset.card_eq_sum_ones → zjG, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sum_filter → zLJ, IsLocalization.Away.algebraMap_isUnit → z4z, IsLocalization.Away.lift_eq → zaz, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.map_C → zpw, Nat.le_succ → zqk, Nat.lt_succ_of_le → zB1
section
set_option autoImplicit true
namespace qQEcrEc
noncomputable section
open Polynomial qAzl5me qCj6p1d
open P6_6 (bf weightedChart)
open aR (af Shape aO shape cK extend)
open dN (bC su separant)
open vS (VE)
open aY3 (bH1 a6c)
open lB (bF afz)
private theorem test_fits {g:af 4} {p:Shape} {n L:ℕ}
    (hp:bF p) (hg:aO (shape g) p) (ht:0<p.t) (hne :p.t≠1)
    (hn:n≤L) :VE (weightedChart L p) (bC (su g n)) := by
  rw [weightedChart,ite_eq_right hne]
  exact a6c (bH1 hg hp ht hn)
theorem proof :qCj6p1d.c1 := by
  intro g p hp hg ht hne
  have htop:0<p.t:=ht.trans_le hg.2.2
  refine ⟨{
    polynomial:=bC (memberTest g)
    fits :=test_fits hp hg htop hne (zqk bf)
    aEA:=⟨0,by rw [pow_zero,one_mul]⟩
    next:=bC (ZV g)
    next_fits :=test_fits hp hg htop hne (zqk (bf+1))
    next_represents :=⟨0,by rw [pow_zero,one_mul]⟩
    values := ?_ }⟩
  intro x a
  have hchar :bf+2≤K1.p:= by decide
  obtain ⟨D,hD,hval⟩:=atq.d40 hchar hg hp htop x a
  refine ⟨D,?_,fun S hd hr => ?_⟩
  · change VE (weightedChart (bf+2) p) D
    rw [weightedChart,ite_eq_right hne]
    exact a6c hD
  · have hdegree :S.natDegree<bf :=zB1 hd
    refine hval S (hdegree.trans_le (Nat.le_add_right _ _)) hr.1 ?_
    intro hz
    change cK (separant g) (extend S)=0 at hz
    exact hr.2 (by rw [afz,hz,map_zero])
end
end qQEcrEc
end
section
set_option autoImplicit true
namespace qBCdrib
noncomputable section
open Polynomial
open P6 (K)
open P6_6 (bf)
open qCj6p1d (ChartRing qR sigma graph yu aJf afU)
open aeM (FH azb aco)
open lB (bF)
open aR (ao af Shape aO shape qE embed extend cK)
open Ex (C6)
open dN (GeoJets GeoField j8 bC An separant
  su arh)
open aA5 (T9 RT ao6 numerator denominator CJ cba)
open aKq (Chart incl S aIf bbo azH q constants W
  zp bel aN3 aVb b5B)
open private cHn from ProximityPrize.SubmissionLower.A1
open private aJI topWeight auY from ProximityPrize.SubmissionLower.A2
open private b60 from ProximityPrize.SubmissionLower.E4
open private iy ajW const asv from ProximityPrize.SubmissionLower.BI
open private bds bix b6Z cWs cWr from ProximityPrize.SubmissionLower.E4
open private bdl from ProximityPrize.SubmissionLower.BI
variable (g:af 4)
@[simp] private theorem cad (a :GeoField) :
    yu g (znf a)=qR g (znf a) := by
  simp [yu]
private def toChart:Chart g →+* ChartRing g :=
  IsLocalization.Away.lift (separant g)
    (g:=(qR g).comp (MvPolynomial.map j8))
    (z4z (sigma g))
@[simp] private theorem toChart_incl (P:af 4) :
    toChart g (incl g P)=qR g (bC P) :=
  zaz _ _ _
private theorem toChart_inv :
    toChart g (aIf g)=IsLocalization.Away.invSelf (sigma g) := by
  apply (z4z (S:=ChartRing g) (sigma g)).mul_left_cancel
  rw [IsLocalization.Away.mul_invSelf]
  have hm:=congrArg (toChart g) (bbo g)
  simpa only [S,map_mul,toChart_incl,map_one,sigma] using hm
private theorem toChart_graph (P:af 5) :
    toChart g (zp g P)=yu g (RT P) := by
  have h: (toChart g).comp (zp g)=(yu g).comp RT:= by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [bel,constants,bC]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hq:j8 (Polynomial.C azH) = -(4 :GeoField)⁻¹:= by
          change (j8.comp Polynomial.C) azH= _
          rw [azH,map_neg,map_inv₀,map_ofNat]
        change toChart g (zp g (z9v (Fin.last 4))) =
          yu g (RT (z9v (Fin.last 4)))
        rw [aVb,MvPolynomial.map_X,yu,MvPolynomial.eval₂Hom_X',
          Fin.lastCases_last]
        simp only [W,q,constants,RingHom.comp_apply,map_mul,toChart_incl,toChart_inv,
          bC,zpw,hq]
      · simp [b5B,bC,yu]
  exact DFunLike.congr_fun h P
private theorem cae (P:af 4) :
    yu g (RT (T9 P))=qR g (bC P) := by
  rw [← toChart_graph,aN3,toChart_incl]
private theorem dWe (k :ℕ) :
    yu g (RT (denominator g k))=qR g (sigma g)^k := by
  simp only [denominator,map_pow,cae,sigma]
private theorem cHo (k :ℕ) :
    yu g (RT (numerator g k))*qR g (sigma g)^(k+8) =
      qR g (bC (su g (k+4))) := by
  have h:=congrArg (toChart g) (cHn g k)
  simpa only [map_mul,map_pow,toChart_graph,S,toChart_incl,sigma] using h
private theorem ef3 :
    RT (ao6 g)=graph g:= by
  simp [ao6,graph,sigma,bC,MvPolynomial.map_rename,map_ofNat]
local notation "wd" => MvPolynomial.weightedTotalDegree
private theorem dIS {p:Shape} (hp:bF p) (hG:aO (shape g) p)
    (ht:1≤p.t) :
    FH (azb p) 1 (graph g) ∧
      ∀ k :ℕ,FH (aco (k+5) p) (k+5) (RT (denominator g k)) ∧
        ∀ i≤k+4,FH (aco (k+5) p) (k+5) (RT (CJ g k i)) := by
  obtain ⟨hjb,htj⟩:=hp
  have hj:3≤p.j:= by omega
  have hb:1≤p.b:= by omega
  change g.totalDegree≤p.b∧qE g≤p.j ∧
    g.degreeOf 3≤p.t at hG
  have hTotal :wd ((1 :Fin 5→ℕ) ∘ z1o) g≤p.b:= by
    change wd (1 :Fin 4→ℕ) g≤p.b
    simpa only [MvPolynomial.weightedTotalDegree_one] using hG.1
  have hIndex :wd ((Fin.val :Fin 5→ℕ) ∘ z1o) g≤p.j:= by
    change wd (Fin.val :Fin 4→ℕ) g≤p.j
    exact C6 g ▸ hG.2.1
  have hTop:wd (topWeight ∘ z1o) g≤p.t:= by
    have hw:topWeight ∘ z1o=(Pi.single (3:Fin 4) 1 :Fin 4→ℕ) := by
      funext i
      simp [topWeight]
    simpa only [hw,MvPolynomial.weightedTotalDegree_piSingle] using hG.2.2
  have hFifth:wd (auY ∘ z1o) g≤0:= by
    have hw:auY ∘ z1o=(0:Fin 4→ℕ) := by
      funext i
      change (Pi.single (Fin.last 4) 1 :Fin 5→ℕ) i.castSucc=0
      rw [Pi.single_apply,ite_eq_right (Fin.castSucc_ne_last i)]
    rw [hw]
    apply Finset.sup_le
    intro m _
    simp [Finsupp.weight_eq_sum]
  have wt:=aJI (1 :Fin 5→ℕ) 0 (fun _=>le_rfl) (by decide)
    (fun _=>le_rfl) hTotal hb
  have wi:=aJI (Fin.val :Fin 5→ℕ) 1 (fun i=> by rfl) (by decide)
    (fun i=>i.isLt.le) hIndex hj
  have ws :=aJI topWeight 1 (fun i=> by fin_cases i <;> decide) (by decide)
    (fun i=> by fin_cases i <;> decide) hTop ht
  have wf :=aJI auY 1 (fun i=> by fin_cases i <;> decide) (by decide)
    (fun i=> by fin_cases i <;> decide) hFifth (by decide)
  constructor
  · rw [← ef3 g]
    apply b60
    · exact (Nat.add_zero _ ▸ wt.1).trans (le_max_left _ _)
    · exact wi.1
    · exact ws.1
    · exact wf.1
  · intro k
    have hJ:p.j-3+1=p.j - 2 := by omega
    have hT:p.t - 1+1=p.t:= by omega
    have wTotal :=wt.2 k
    have wIndex :=wi.2 k
    have wTop:=ws.2 k
    have wFifth:wd auY (denominator g k)≤1+k ∧
        (∀ i≤k+4,wd auY (CJ g k i)≤1+k) := by
      simpa only [show auY (Fin.last 4)=1 by decide,
        show auY ((3:Fin 4).castSucc)=0 by decide,Nat.sub_zero,zero_add,Nat.mul_one]
        using wf.2 k
    simp only [Pi.one_apply,add_zero] at wTotal
    change wd Fin.val (denominator g k)≤4+k*(p.j-3+1)∧_ at wIndex
    change wd topWeight (denominator g k)≤2+k*(p.t - 1+1)∧_ at wTop
    simp only [show (Fin.last 4).val = 4 by rfl,show ((3:Fin 4).castSucc).val=3 by rfl,
      show topWeight (Fin.last 4)=2 by decide,show topWeight ((3:Fin 4).castSucc)=1 by decide,
      hJ,hT] at wIndex wTop
    have box (P:af 5) (h1 :wd 1 P≤1+k*(p.b - 1))
        (h2 :wd Fin.val P≤4+k*(p.j - 2)) (h3:wd topWeight P≤2+k*p.t)
        (h4 :wd auY P≤1+k) :
        FH (aco (k+5) p) (k+5) (RT P) := by
      simpa only [aco,Nat.add_sub_cancel] using
        b60 P (h1.trans (le_max_left _ (4+k*(p.j - 2)))) h2 h3
          (h4.trans (by omega :1+k≤k+5))
    exact ⟨box _ wTotal.1 wIndex.1 wTop.1 wFifth.1,
      fun i hi=>box _ (wTotal.2 i hi) (wIndex.2 i hi) (wTop.2 i hi) (wFifth.2 i hi)⟩
private theorem c1R (k :ℕ) :
    Associated (yu g (RT (numerator g k)))
      (qR g (bC (su g (k+4)))) := by
  rw [← cHo g k]
  exact associated_mul_unit_right _ _ (IsLocalization.Away.algebraMap_pow_isUnit (sigma g) (k+8))
@[simp] private theorem eval_chartMap {T:ao[X]} (hs :An T (sigma g)≠0)
    (P:GeoJets) :aJf g T hs (qR g P)=An T P :=
  zaz _ _ _
private theorem eval_const {T:ao[X]} (hs :An T (sigma g)≠0) (a :GeoField) :
    afU g T hs (znf a)=a := by
  simp [afU,An]
private theorem a3G {T:ao[X]} (hs :An T (sigma g)≠0) (k :ℕ) :
    afU g T hs (RT (denominator g k))=An T (sigma g)^k := by
  simp [afU,dWe]
private theorem d2G {T:ao[X]} (hg:cK g T=0)
    (hs :An T (sigma g)≠0) (k i:ℕ) (hi:i≤k+4) :
    afU g T hs (RT (CJ g k i))=iy T i*An T (sigma g)^k := by
  by_cases hi4 :i<4
  · rw [CJ,dite_eq_left hi4]
    simp only [map_mul,zpw,eval_const,a3G]
    have he :afU g T hs (RT (T9 (z9v ⟨i,hi4⟩))) =
        j8 (hasseDeriv i T) := by
      change aJf g T hs (yu g (RT (T9 (z9v _))))= _
      rw [cae,eval_chartMap]
      simp [bC,An,aR.jet]
    rw [he]
    unfold iy
    rw [ajW,map_mul]
  · rw [CJ,dite_eq_right hi4]
    simp only [map_mul,a3G]
    let j:=i-4
    have hj:j+4=i:= by dsimp only [j]; omega
    have hjk :j≤k := by omega
    let s :=An T (sigma g)
    have he :=congrArg (aJf g T hs) (cHo g j)
    simp only [map_mul,map_pow,eval_chartMap] at he
    change afU g T hs (RT (numerator g j))*s^(j+8) =
      An T (bC (su g (j+4))) at he
    have hEval (P:af 4) :An T (bC P)=j8 (cK P T) :=
      bdl T P
    rw [hEval,arh _ _ hg,map_mul,map_pow,hj] at he
    have hσ:j8 (cK (separant g) T)=s :=(hEval _).symm
    rw [hσ,show 2*i=j+(j+8) by omega,pow_add s j (j+8)] at he
    have hnum :afU g T hs (RT (numerator g j))=iy T i*s^j:= by
      apply mul_right_cancel₀ (pow_ne_zero (j+8) hs)
      exact he.trans (show s^j*s^(j+8)*iy T i =
        (iy T i*s^j)*s^(j+8) by ac_rfl)
    change afU g T hs (RT (numerator g j))*s^(k - j)=iy T i*s^k
    rw [hnum,mul_assoc,← pow_add,Nat.add_sub_of_le hjk]
private theorem gK2 {M:ℕ} (hM:M≤K1.p) (k :ℕ)
    (hk :M≤k+5) (x a :K) (S:K[X]) (hS:S.natDegree<M)
    (hg:cK g (extend S)=0) (hs :An (extend S) (sigma g)≠0) :
    afU g (extend S) hs (bix M g k x a)=0↔S.eval x=a := by
  let e :=afU g (extend S) hs
  let s :=An (extend S) (sigma g)
  have hsum :
      (∑ i∈Finset.range M,
        e (znf (asv (embed x) i)*RT (CJ g k i))) =
        const ((extend S).eval (embed x))*s^k := by
    have hdeg: (extend S).natDegree<M:= by
      rw [Polynomial.natDegree_map]
      exact hS
    rw [← bds hM (extend S) hdeg (embed x),Finset.sum_mul]
    apply zUo rfl
    intro i hi
    have hki:i≤k+4 := by have :=Finset.mem_range.mp hi; omega
    simp only [map_mul,e,eval_const,d2G g hg hs k i hki,s,mul_assoc]
  change e (bix M g k x a)=0↔_
  unfold bix
  rw [map_sub,map_sum,hsum,map_mul,eval_const,a3G]
  change const ((extend S).eval (embed x))*s^k - const (embed a)*s^k=0↔_
  rw [Polynomial.eval_map_apply,← sub_mul,mul_eq_zero,
    or_iff_left (pow_ne_zero k hs),sub_eq_zero]
  exact ⟨fun he=>embed.injective (const.injective he),fun he=>congrArg (const.comp embed) he⟩
theorem proof :qCj6p1d.c3:= by
  intro g p hp hbox _ ht
  obtain ⟨hg,hbox⟩:=dIS g hp hbox (Nat.le_of_lt ht)
  let k :=bf-4
  have hk :k+4=bf :=Nat.sub_add_cancel (by change 4≤133426; decide)
  have hk' : (k+1)+4=bf+1 := by rw [Nat.add_right_comm,hk]
  have hE :=(hbox k).2 (k+4) le_rfl
  have hH :=(hbox (k+1)).2 ((k+1)+4) le_rfl
  have hcap: (k+1)+5=bf+2 :=congrArg (· + 1) hk'
  rw [cba] at hE hH
  change FH (aco ((k+4)+1) p) ((k+4)+1) _ at hE
  rw [hk] at hE
  rw [hcap] at hH
  have hm:=c1R g k
  have hn:=c1R g (k+1)
  rw [hk] at hm
  rw [hk'] at hn
  refine ⟨⟨⟨hg,_,hE,hm⟩,_,hH,hn,?_⟩⟩
  intro x a
  have hM:bf≤K1.p:= by change 133426≤0x7f000001; decide
  have hlen:bf≤(k+1)+4 :=hk'.symm ▸ zqk _
  refine ⟨bix bf g (k+1) x a,?_,?_⟩
  · rw [← hcap]
    unfold bix
    apply cWr
    · apply cWs
      intro i hi
      have hki:i≤(k+1)+4 :=(Finset.mem_range.mp hi).le.trans hlen
      exact b6Z ((hbox (k+1)).2 i hki) _
    · exact b6Z (hbox (k+1)).1 _
  · intro T hT hg' hs
    exact gK2 g hM (k+1) (hlen.trans (zqk _)) x a T (zB1 hT) hg' hs
end
end qBCdrib
end
section
set_option autoImplicit true
namespace qsnQ6jb
noncomputable section
open P6_6 (bf)

open qCj6p1d
open aR (af Shape qP)
open dN (GeoJets bC)
open vS (g9 tC)
open B8 (lS Component TB cylinder qK i9)

def Iu (g:af 4) (P:Ideal GeoJets) :Ideal g9 :=
  (P.map (qR g)).comap (yu g)
structure GraphLaws (g:af 4) :Prop where
  onOld: (yu g).comp qK=qR g
  comap : ∀ (P:Ideal GeoJets),P.IsPrime→sigma g∉P→(Iu g P).comap qK=P
  prime : ∀ (P:Ideal GeoJets),P.IsPrime→sigma g∉P→(Iu g P).IsPrime
  contains : ∀ P,graph g∈Iu g P
  cylinder_le : ∀ P,cylinder P≤Iu g P
  eq_lift : ∀ (J:Ideal g9),J.IsPrime→qK (sigma g)∉J →
    graph g∈J→J=Iu g (J.comap qK)
  component : ∀ (P:Ideal GeoJets),P.IsPrime→sigma g∉P →
    (cylinder P).IsPrime→TB (cylinder P) 3 →
    graph g∉cylinder P∧Component (cylinder P) (graph g) (Iu g P) 1 ∧
      TB (Iu g P) 2
def boxes (q p:Shape) :lS:= fun i =>
  if i=0 then (⟨5,4,1⟩,0) else if i=1 then (q,0) else
  if i=2 then (tC p,1) else
  if i=3 then (qP (bf+1) p,bf+1)
  else (qP (bf+2) p,bf+2)
def aRQ (p:Shape) :Prop :=
  let u:=bf+1
  let v :=bf+2
  3*(p.t+1)≤p.j+1∧2≤p.t+1 ∧
    3*(2+(u - 5)*p.t)≤(qP u p).j ∧
    3*(2+(v - 5)*p.t)≤(qP v p).j ∧
    2*u≤(qP u p).t∧2*v≤(qP v p).t
abbrev a4d (R:af 4) :=i9 ⊥ (qK (bC R))
end
end qsnQ6jb
end
section
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace q6t08kb
noncomputable section
open P6_6 P6_6_7
open aR (af shape extend ceilDiv)
open Ex (X7)
open oR (Wc)
open scoped BigOperators
def c1 :Prop :=
  ∀ (C:Context) R l ell,HigherIndex C R l ell →
    let a :=lowerBody (shape R)
    mV*(singular C R).card ≤
      P6.t*firstMixed (projectionTotal a) (projectionIndex a) +
        mV*(projectionTotal a)^2
def c2 :Prop :=
  ∀ (C:Context) R l ell,HigherIndex C R l ell → ¬ acA R →
    let a :=lowerBody (shape R)
    mV*(regular C R).card ≤
      mV*lowerMixed a+(P6.t+2*mV)*freshBudget a
def c3:Prop :=
  ∀ (C:Context) R l ell,HigherIndex C R l ell→acA R →
    let a :=lowerBody (shape R)
    mV*(regular C R).card≤P6.t*(gZ*a.b)+mV*a.b
def c4 :Prop :=
  ∀ (C:Context) R l ell,HigherIndex C R l ell→0<(X7 R).degreeOf 2 →
    let a :=lowerBody (shape R)
    excessWeight C R (nonzeroFibers C R) ≤
      ceilDiv (P6.t*Wc a a (lowerTaylor a)) mV+3*Wc a a a
def c5:Prop :=
  ∀ (C:Context) R l ell,HigherIndex C R l ell→0<(X7 R).degreeOf 2 →
    (zeroFibers C R).card≤(shape R).b^2
def c6:Prop :=
  ∀ (C:Context) R l ell,HigherIndex C R l ell→(X7 R).degreeOf 2=0 →
    excessWeight C R C.Δ≤(shape R).b^2
private theorem split_order (C:Context) (R:af 4) :
    markedWeight C.Δ C.s R=(roots C R).card+excessWeight C R C.Δ:= by
  classical
  unfold markedWeight roots excessWeight
  rw [zjG,zLJ,← zfW]
  apply zUo rfl
  intro γ _
  change ord C R γ=(if 0<ord C R γ then 1 else 0)+(ord C R γ - 1)
  by_cases h:0<ord C R γ
  · rw [ite_eq_left h]
    omega
  · rw [ite_eq_right h]
    omega
private theorem split_roots (C:Context) (R:af 4) :
    (roots C R).card=(regular C R).card+(singular C R).card:= by
  classical
  unfold regular singular
  simp only [zjG]
  simpa only [not_ne_iff] using (Finset.sum_filter_add_sum_filter_not (roots C R)
    (fun γ=>aR.cK (oR.separant (X7 R)) (extend (C.s γ))≠0)
    (fun _=>(1 :ℕ))).symm
private theorem count_roots (h1 :c1) (h2 :c2) (h3:c3)
    {C:Context} {R:af 4} {l ell:ℕ} (h:HigherIndex C R l ell) :
    (roots C R).card≤lowerHigh (lowerBody (shape R)) := by
  let a :=lowerBody (shape R)
  have hs :46402*(singular C R).card ≤
      82317*firstMixed (projectionTotal a) (projectionIndex a)+46402*(projectionTotal a)^2 := by
    simpa only [d1C,ee8] using h1 C R l ell h
  have hr :46402*(regular C R).card≤46402*lowerMixed a +
      (82317+2*46402)*freshBudget a+82317*(gZ*a.b)+46402*a.b:= by
    by_cases hw:acA R
    · have hh:46402*(regular C R).card≤82317*(gZ*a.b)+46402*a.b:= by
        simpa only [d1C,ee8] using h3 C R l ell h hw
      omega
    · have hh:46402*(regular C R).card ≤
          46402*lowerMixed a+(82317+2*46402)*freshBudget a := by
        simpa only [d1C,ee8] using h2 C R l ell h hw
      omega
  have hfee : (roots C R).card≤lowerMixed a+ceilDiv
    ((82317+2*46402)*freshBudget a+82317 *
      (gZ*a.b+firstMixed (projectionTotal a) (projectionIndex a))) 46402 +
      a.b+(projectionTotal a)^2 := by
    rw [split_roots]
    unfold ceilDiv
    omega
  simpa only [lowerHigh,lowerMixed,firstMixed_eq,freshBudget,
    projectionTotal,projectionIndex,d1C,ee8,Nat.mul_assoc,a] using hfee
private theorem count_excess (h4 :c4) (h5:c5) (h6:c6)
    {C:Context} {R:af 4} {l ell:ℕ} (h:HigherIndex C R l ell) :
    let a :=lowerBody (shape R)
    excessWeight C R C.Δ ≤
      ceilDiv (P6.t*Wc a a (lowerTaylor a)) mV +
        3*Wc a a a+(shape R).b^3:= by
  classical
  dsimp only
  let b:=(shape R).b
  by_cases hp:0<(X7 R).degreeOf 2
  · have he :excessWeight C R C.Δ =
        excessWeight C R (nonzeroFibers C R)+excessWeight C R (zeroFibers C R) := by
      unfold excessWeight nonzeroFibers zeroFibers
      rw [zLJ,zLJ,← zfW]
      apply zUo rfl
      intro γ _
      by_cases hz :aP6 R (extend (C.s γ))=0 <;> simp [hz]
    have hz :excessWeight C R (zeroFibers C R)≤b^3:= calc
      _ ≤ ∑ _γ∈zeroFibers C R,b :=
        Finset.sum_le_sum fun γ _=>(Nat.sub_le _ _).trans (ord_le C R γ)
      _=(zeroFibers C R).card*b:= by simp [Nat.mul_comm]
      _≤b^3:= by rw [pow_succ]; exact Nat.mul_le_mul_right _ (h5 C R l ell h hp)
    rw [he]
    exact add_le_add (h4 C R l ell h hp) hz
  · have hb:0<b:=h.1.2.1.1
    have hpow:b^2≤b^3:= by
      rw [pow_succ b 2]
      exact Nat.le_mul_of_pos_right _ hb
    exact ((h6 C R l ell h (Nat.eq_zero_of_not_pos hp)).trans hpow).trans (Nat.le_add_left _ _)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) :
    P6_6_7.c5:= by
  intro C R l ell hf hg ht hj
  simp only [smallFee,ht,ite_true,ite_eq_right (Nat.ne_of_gt hj)]
  let a :=lowerBody (shape R)
  change _≤ if a.t=0 then eyA a.b a.j+(shape R).b^2 else
    lowerHigh a+ceilDiv (P6.t*Wc a a (lowerTaylor a)) mV +
      3*Wc a a a+(shape R).b^3
  by_cases hi:a.t=0
  · have hj' : (shape R).j=1 := by
      change (shape R).j/2=0 at hi
      omega
    have ha :a.j=1 :=hj'
    rw [ite_eq_left hi,ha]
    exact (first_order C R hf.1 hj').trans (Nat.le_add_right (eyA a.b 1) ((shape R).b^2))
  · have hj' : 2≤(shape R).j:= by
      change (shape R).j/2≠0 at hi
      omega
    let h:HigherIndex C R l ell:=⟨hf,hg,ht,hj'⟩
    rw [ite_eq_right hi,split_order]
    simpa only [Nat.add_assoc] using
      add_le_add (count_roots h1 h2 h3 h) (count_excess h4 h5 h6 h)
end
end q6t08kb
end
