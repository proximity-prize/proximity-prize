import ProximityPrize.SubmissionLower.ZPedZjc
import ProximityPrize.SubmissionLower.ZpWezjb
import ProximityPrize.SubmissionLower.Zsr715c
import ProximityPrize.SubmissionLower.ZeBsWTa
import ProximityPrize.SubmissionLower.ZU4mhUb
set_option Elab.async false
open _root_ renaming Function.iterate_succ_apply' → zLk, Function.iterate_zero_apply → z56, Ideal → znc, Ideal.span → zye, Ideal.subset_span → zCn, MvPolynomial.affineDegree → zHf, MvPolynomial.affineHilbertPolynomial → zIU, MvPolynomial.eval → zY9, Nat.find_spec → zWq, Nat.sub_le → z7J
section
set_option autoImplicit true
set_option Elab.async false
namespace qMiJnMd
noncomputable section
open Polynomial Finset P6_6 P6_6_7
open P6 (K)
open aR (af ao Shape shape aO cK extend jet wU)
open Ex (YN aQU C6)
open dN (GeoJets kC Ch YR bC separant
  An Invariant su)
open BO (Ue bfW)
open Dr (ChamberBox tW AN dimension bEk aQG
  aIc aIT aPQ aCR bHn a9B)
open rW (Yg)
open WI (ctQ)
open lB (bF amo Tn)
open P6_6_7_3 (agr local_weight)
open scoped BigOperators
open private aio from ProximityPrize.SubmissionLower.Zb3VwYd
open private duz from ProximityPrize.SubmissionLower.T
open private orderAt_ord genericOrder_le_ord from ProximityPrize.SubmissionLower.ZfVU1Oc
open private ur bFv bxU from ProximityPrize.SubmissionLower.AF
open private aDq bKk from ProximityPrize.SubmissionLower.BF
open private ceY bnH bnG from ProximityPrize.SubmissionLower.ZPedZjc
open private cGC from ProximityPrize.SubmissionLower.BA
abbrev an1 (C:Context) :af 4 :=factorProd C.f C.S
abbrev cap (R:af 4) :Shape :=(shape R).iU
abbrev memTest (g:af 4) :af 4 :=su g bf
structure Input (C:Context) (R:af 4) :Prop where
  factor :JetFactor R
  positive :0<(shape R).t
  ahD:aO (shape R) Wk
  proper : ¬ R∣an1 C
  H6:aO (shape (an1 C)) (remainingChart C.v)
  cutterWeight:tB (an1 C) aWx
  order : ∀ γ∈C.Δ,wU (an1 C) (extend (C.s γ)) 1
def xN (C:Context) (R:af 4) (γ:K) :Prop :=
  0<ord C R γ∧thirdFiber R (extend (C.s γ))≠0
structure Charts (C:Context) (R:af 4) where
  aI:K→ znc GeoJets
  index :znc GeoJets→ℕ
  valid : ∀ γ∈C.Δ,xN C R γ →
    (kC R (an1 C)).IsMinimalPrime (aI γ) ∧
    aI γ≤Ch (extend (C.s γ))∧YR R (aI γ) (index (aI γ))
abbrev chartAt {C:Context} {R:af 4} (A:Charts C R) (γ:K) :af 4 :=
  (separant^[A.index (A.aI γ)]) R
inductive Stratum | boundary | zD | taylor | fresh deriving DecidableEq
def stratum {C:Context} {R:af 4} (A:Charts C R) (γ:K) :Stratum:= by
  classical
  let g:=chartAt A γ
  exact if cK (separant g) (extend (C.s γ))=0 then .boundary
    else if ¬ Invariant g (A.aI γ) then .zD
    else if bC (memTest g)∈A.aI γ then .fresh else .taylor
def DG {C:Context} {R:af 4} (A:Charts C R) :ℕ:= by
  classical exact ∑ γ∈C.Δ,if xN C R γ then ord C R γ - genericOrder R (A.aI γ) else 0
def weight {C:Context} {R:af 4} (A:Charts C R) (b:Stratum) :ℕ:= by
  classical exact ∑ γ∈C.Δ,if xN C R γ∧stratum A γ=b then genericOrder R (A.aI γ) else 0
theorem cutter_shape (C:Context) :shape (an1 C)=wD (shape ∘ C.f) C.S:= by
  classical
  have h (w:Fin 4→ℕ) :=MvPolynomial.weightedTotalDegree_prod w C.S C.f
    (fun i hi=>(C.marks.factors i hi).1.ne_zero)
  have hb:=h 1; have hj:=h Fin.val; have ht:=h (Pi.single 3 1)
  simp only [MvPolynomial.weightedTotalDegree_one] at hb
  simp only [← C6] at hj
  simp only [MvPolynomial.weightedTotalDegree_piSingle] at ht
  simp only [shape,Ds.wD,Function.comp_apply,an1,factorProd]; rw [hb,hj,ht]
theorem input_of_guard {C:Context} {R:af 4} {l ell:ℕ}
    (hR:JetFactor R) (hg:SmallGuard C R l ell) (ht:0<(shape R).t) :Input C R:= by
  classical
  have hbox :aO (shape (an1 C)) (remainingChart C.v) := by
    have hv :=C.fits; rw [← cutter_shape C] at hv
    rcases hv with ⟨hb,hj,ht'⟩
    change C.v.b+(shape (an1 C)).b≤ m6.b at hb
    change C.v.j+(shape (an1 C)).j≤ m6.j at hj
    change C.v.t+(shape (an1 C)).t≤ m6.t at ht'
    have hb' : (shape (an1 C)).b≤ m6.b - C.v.b:= by omega
    have hJ:=(aDq (an1 C)).2; have hT:=(aDq (an1 C)).1
    have htb: (shape (an1 C)).t≤(shape (an1 C)).b:=MvPolynomial.degreeOf_le_totalDegree _ _
    refine ⟨hb'.trans (le_max_left _ _),le_min (by change _≤ m6.j - C.v.j; omega)
      (hJ.trans (Nat.mul_le_mul_left 3 hb')),?_⟩
    refine le_min (by change _≤ m6.t - C.v.t; omega) (le_min (htb.trans hb')
      ((Nat.le_div_iff_mul_le (by decide :0<3)).mpr ?_))
    rw [Nat.mul_comm]
    exact le_min (by change _≤ m6.j - C.v.j; omega)
      (hT.trans (hJ.trans (Nat.mul_le_mul_left 3 hb')))
  have hwt:tB (an1 C) aWx := by
    have ht' : (wD (shape ∘ C.f) C.S).t≤ m6.t:=C.fits.2.2.trans' (Nat.le_add_left _ _)
    have hc:C.S.card≤16:= calc
      C.S.card = ∑ _i∈C.S,(1 :ℕ) := by simp
      _≤_:=(sum_le_sum fun i hi=>(C.marks.factors i hi).2.1).trans ht'
    let e :=MvPolynomial.optionEquivRight ao (Fin 4)
    let w:Option (Fin 4)→ℕ:= fun v=>v.elim 1 (fun i=>gZ - i.val)
    apply (aio _).mpr
    change (e.symm (factorProd C.f C.S)).weightedTotalDegree w≤aWx
    rw [factorProd,map_prod]
    calc _≤C.S.card*M8:= by
          rw [MvPolynomial.weightedTotalDegree_prod w C.S (fun i=>e.symm (C.f i))
            (fun i hi=>e.symm.map_ne_zero_iff.mpr (C.marks.factors i hi).1.ne_zero)]
          simpa only [sum_const,smul_eq_mul] using
            (sum_le_sum fun i hi=>(aio _).mp (C.marks.factors i hi).2.2.2)
      _≤16*M8:=Nat.mul_le_mul_right _ hc
      _≤aWx := by decide
  refine ⟨hR,ht,⟨hg.2.2.1.1.trans (z7J ..),hg.2.2.1.2.1.trans (z7J ..),
    hg.2.2.1.2.2.trans (z7J ..)⟩,hg.2.2.2.2,hbox,hwt,?_⟩
  intro γ hγ
  have hv :cK (an1 C) (extend (C.s γ))=0:= by
    obtain ⟨i,hi,hz⟩:=C.marks.Eh γ hγ
    change (zY9 _) (factorProd C.f C.S)=0
    rw [factorProd,map_prod]; exact prod_eq_zero hi hz
  rw [duz] at hv
  intro m hm; by_contra! hlt
  have hz :m=0:=Finsupp.ext fun j=> by
    by_contra hne
    have hm0:m j≠0:=hne
    have hs :m j≤ m.sum (fun _ a=>a) :=
      single_le_sum (f := fun i=>m i) (fun _ _=>Nat.zero_le _) (Finsupp.mem_support_iff.mpr hm0)
    omega
  subst m; exact (MvPolynomial.mem_support_iff.mp hm) hv
theorem exists_derivative {R:af 4} {S:ao[X]}
    (ht: (shape R).t<K1.p) (h:thirdFiber R S≠0) :
    ∃ k≤(shape R).t,cK ((separant^[k]) R) S≠0:= by
  let P:=ur S R
  have hP:P≠0:= by
    change Polynomial.map (zY9 (jet S)) (YN R)≠0
    rw [← bKk R S]; exact h
  let k :=P.natDegree
  have hk :k≤(shape R).t:=Polynomial.natDegree_map_le.trans_eq (aQU R)
  have hn: (derivative^[k] P).coeff 0≠0:= by
    rw [coeff_iterate_derivative,Nat.zero_add,Nat.descFactorial_self,nsmul_eq_mul]
    change (k.factorial:ao[X])*P.coeff k≠0
    rw [← map_natCast (Polynomial.C:ao →+* ao[X])]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr (lB.ahA (hk.trans_lt ht)))
      (leadingCoeff_ne_zero.mpr hP)
  have hc:derivative^[k] P=Polynomial.C ((derivative^[k] P).coeff 0) :=
    eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans (Nat.sub_self _).le)
  have he (i:ℕ) :ur S ((separant^[i]) R)=derivative^[i] P:= by
    induction i with
    | zero=>rfl
    | succ i ih =>
      simp only [zLk]
      change (YN (separant ((separant^[i]) R))).map (zY9 (jet S))= _
      rw [bxU,← derivative_map]; exact congrArg derivative ih
  exact ⟨k,hk,by rw [← bFv,he,hc,Polynomial.eval_C]; exact hn⟩
theorem charts_exist {C:Context} {R:af 4} (h:Input C R) :Nonempty (Charts C R) := by
  classical
  have hs (γ) (hγ:γ∈C.Δ∧xN C R γ) :
      ∃ P,(kC R (an1 C)).IsMinimalPrime P∧P≤Ch (extend (C.s γ)) := by
    have hle :kC R (an1 C)≤Ch (extend (C.s γ)) :=
      Ideal.span_le.mpr fun F hF=> by
        rcases (by simpa using hF:F=bC R∨F=bC (an1 C)) with rfl | rfl
        · exact Ue.mpr (bfW hγ.2.1 (orderAt_ord C R γ))
        · exact Ue.mpr (bfW Nat.zero_lt_one (h.order γ hγ.1))
    let: (Ch (extend (C.s γ))).IsPrime :=RingHom.ker_isPrime (An _)
    exact Ideal.exists_minimalPrimes_le hle
  let A (γ:K) :znc GeoJets :=if hγ:γ∈C.Δ∧xN C R γ then (hs γ hγ).choose else ⊥
  let elig (P:znc GeoJets) := ∃ j,bC ((separant^[j]) R)∉P
  let idx (P:znc GeoJets) :=if he :elig P then Nat.find he - 1 else 0
  refine ⟨⟨A,idx,fun γ hγ ha => ?_⟩⟩
  have hA: (kC R (an1 C)).IsMinimalPrime (A γ) ∧
      A γ≤Ch (extend (C.s γ)) := by
    simpa only [A,dite_eq_left (And.intro hγ ha)] using (hs γ ⟨hγ,ha⟩).choose_spec
  obtain ⟨k,hk,hkn⟩:=exists_derivative
    (h.ahD.2.2.trans_lt (show Wk.t<K1.p by decide)) ha.2
  have he :elig (A γ) :=⟨k,fun hm=>hkn (Ue.mp (hA.2 hm))⟩
  let d:=Nat.find he
  have hd:bC ((separant^[d]) R)∉A γ:=zWq he
  have hdt:d≤(shape R).t:=(Nat.find_min' he (fun hm=>hkn (Ue.mp (hA.2 hm)))).trans hk
  have hd0:d≠0:= fun hz=>hd (by
    simpa only [hz,z56] using hA.1.1.2 (zCn (by simp)))
  refine ⟨hA.1,hA.2,?_⟩
  rw [show idx (A γ)=d - 1 by simp only [idx,dite_eq_left he,d]]
  refine ⟨by omega,fun j hj=>by_contra fun hn=>Nat.find_min he (by omega) hn,?_⟩
  rw [← zLk separant (d - 1) R,show (d - 1).succ=d by omega]; exact hd
theorem sum_strata {C:Context} {R:af 4} (A:Charts C R) :
    smallMarks C R false=DG A+weight A .boundary+weight A .zD +
      weight A .taylor+weight A .fresh:= by
  classical
  unfold smallMarks DG weight; simp only [← sum_add_distrib]
  refine sum_congr rfl fun γ hγ => ?_
  by_cases hf :thirdFiber R (extend (C.s γ))=0
  · simp [xN,hf]
  by_cases hz :0<ord C R γ
  · have ha :xN C R γ:=⟨hz,hf⟩
    have hi:=genericOrder_le_ord (R:=R) (A.valid γ hγ ha).2.1
    cases stratum A γ <;> simp [hf,ha,Nat.sub_add_cancel hi]
  · simp [xN,hf,Nat.eq_zero_of_not_pos hz]
theorem first_box (R:af 4) :aO (shape R) (cap R) :=⟨le_max_left _ _,le_rfl,le_rfl⟩
theorem first_chamber {C:Context} {R:af 4} (h:Input C R) :ChamberBox (cap R) :=
  ⟨(Tn R).1,(Tn R).2,h.positive⟩
theorem aM8 {C:Context} {R:af 4} (h:Input C R) :ChamberBox (remainingChart C.v) := by
  obtain ⟨γ,hγ⟩:=C.nonempty; obtain ⟨i,hi,_⟩:=C.marks.Eh γ hγ
  have ht:0<(shape (an1 C)).t:= by
    rw [cutter_shape]
    exact (C.marks.factors i hi).2.1.trans_le
      (single_le_sum (f := fun j=>(shape (C.f j)).t) (fun _ _=>Nat.zero_le _) hi)
  have hc:bF (remainingChart C.v) :=(P6_6_8_3.remaining_fits C.v).2
  exact ⟨hc.1,hc.2,ht.trans_le h.H6.2.2⟩
theorem gH {C:Context} {R:af 4} (h:Input C R) {z :znc GeoJets}
    (hz : (kC R (an1 C)).IsMinimalPrime z) :
    genericOrder R z≤AN (kC R (an1 C)) z ∧
    genericOrder R z≤Yg (kC R (an1 C)) z ∧
    (genericOrder R z :ℕ∞)≤dN.oA (kC R (an1 C)) z hz.isPrime := by
  have hG:an1 C≠0:= fun he=>h.proper (he ▸ dvd_zero R)
  have hg:=q8NBBre.generic_positive hz.isPrime hG
    (hz.le (zCn (by simp)) :bC (an1 C)∈z)
  obtain ⟨v,_,hv,hi⟩:=local_weight h.factor.1 h.proper hz (ell:=1) hg
  rw [one_mul] at hi
  have hl:AN (kC R (an1 C)) z=v :=
    ENat.natCast_inj.mp ((a9B hz).trans hv)
  have hc:Yg (kC R (an1 C)) z=v := by
    rw [Yg,dite_eq_left hz.isPrime,hv,ENat.toNat_natCast]
  exact ⟨hl ▸ hi,hc ▸ hi,hv ▸ ENat.natCast_le_natCast.mpr hi⟩
theorem dRZ {C:Context} {R:af 4} (h:Input C R)
    {T:znc GeoJets} {M:Finset K} (hT:T.IsPrime) (hd:dimension T=1)
    (hM:M⊆C.Δ) (hn:M.Nonempty) (hR:bC R∈T)
    (hon : ∀ γ∈M,T≤Ch (extend (C.s γ)))
    (hf : ∀ γ∈M,thirdFiber R (extend (C.s γ))≠0) :
    let a :=cap R
    (mV:ℚ)*M.card ≤
      (P6.t:ℚ)*tW T [weightedChart bf a] +
      2*(mV:ℚ)*tW T [a] := by
  classical
  obtain ⟨γ,hγ⟩:=hn
  obtain ⟨k,_,hk⟩:=exists_derivative
    (h.ahD.2.2.trans_lt (show Wk.t<K1.p by decide)) (hf γ hγ)
  have he : ∃ j,bC ((separant^[j]) R)∉T:=⟨k,fun hm=>hk (Ue.mp (hon γ hγ hm))⟩
  let d:=Nat.find he
  have hd0:d≠0:= fun hz=>zWq he (by
    change bC ((separant^[d]) R)∈T
    simpa only [hz,z56] using hR)
  have hg:bC ((separant^[d - 1]) R)∈T :=
    by_contra fun hn=>Nat.find_min he (by omega) hn
  have hs :bC (separant ((separant^[d - 1]) R))∉T:= by
    rw [← zLk separant (d - 1) R,show (d - 1).succ=d by omega]
    exact zWq he
  have hfit (i:ℕ) :aO (shape ((separant^[i]) R)) (cap R) :=akM.bc7 R i
  exact ceY hT hd (first_chamber h) (C.messages.mono hM) ⟨γ,hγ⟩ hon (hfit _) hg
    (by rw [← zLk separant (d - 1) R,show (d - 1).succ=d by omega]; exact hfit d) hs
theorem pair_chain {C:Context} {R:af 4} (h:Input C R) {S:Finset (znc GeoJets)}
    {b1 b2 :Shape} (hb1 :ChamberBox b1) (hb2 :ChamberBox b2)
    (hS : ∀ z∈S,(kC R (an1 C)).IsMinimalPrime z) :
    (∑ z∈S,(AN (kC R (an1 C)) z :ℚ)*tW z [b1,b2]) ≤
      tW (⊥ : znc GeoJets) [cap R,remainingChart C.v,b1,b2] := by
  let a :=cap R; let p:=remainingChart C.v
  let H :znc GeoJets :=zye {bC R}
  let J:=kC R (an1 C)
  have ha :=first_chamber h; have hp:=aM8 h
  have hboxes : ∀ q∈[b1,b2],ChamberBox q:= by simp [hb1,hb2]
  have hR:=agr h.factor.1.ne_zero
  have hrel :=amo R (an1 C) h.factor.1 h.proper
  have hregR:IsLeftRegular (Ideal.Quotient.mk (⊥ : znc GeoJets) (bC R)) :=
    aPQ (by infer_instance) (by simpa using hR)
  have hregG:=aIT R (an1 C) hrel
  have hH :dimension H≤3:= by simpa [H,bEk] using aCR hregR
  have hJ:J=H ⊔ zye {bC (an1 C)} := aIc R (an1 C)
  have hdJ:dimension J≤2 := by rw [hJ]; exact (aCR hregG).trans (by change dimension H - 1≤2; omega)
  calc _≤tW J [b1,b2] :=bnG J [b1,b2] hboxes (by simpa using hdJ) S hS
    _≤tW H [p,b1,b2] := by
        rw [hJ]; exact bnH H p [b1,b2] hp hboxes (by simpa using hH) _ (bHn h.H6) hregG
    _≤_:= by
        rw [show H=(⊥ : Ideal GeoJets) ⊔ Ideal.span {bC R} by simp [H]]
        exact bnH ⊥ a [p,b1,b2] ha (by simp [p,hp,hb1,hb2]) (by simp) _
          (bHn (first_box R)) hregR
theorem cycle_budget {C:Context} {R:af 4} (h:Input C R) :
    ∑ P∈(kC R (an1 C)).minimalPrimesFinset,
      (Yg (kC R (an1 C)) P:ℚ)*zHf P ≤
      ((shape R).b:ℚ)*(remainingChart C.v).b:= by
  classical
  let G:=an1 C; let J:=kC R G; let F:=zye {bC R}
  have hR:=agr h.factor.1.ne_zero
  have hrel :=amo R G h.factor.1 h.proper
  have hF:F ≠ ⊤ := fun he=> by
    have hd:=(MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp
      (Ideal.span_singleton_eq_top.mp he)).2
    rw [ctQ] at hd; exact (Nat.ne_of_gt h.factor.2.1.1) hd
  have hd:=MvPolynomial.natDegree_affineHilbertPolynomial_span_singleton_add_one hR hF
  rw [Nat.card_fin] at hd
  have h3: (zIU (zye {bC R})).natDegree=3:= by omega
  have hcoeff :6*(zIU F).leadingCoeff=(shape R).b:= by
    have hdeg:=MvPolynomial.affineDegree_span_singleton hR
    rw [zHf,h3,ctQ] at hdeg; norm_num at hdeg; exact hdeg
  have hc:=MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (aIT R G hrel) (ctQ G).le
  rw [← aIc,h3] at hc; norm_num at hc
  obtain ⟨_,hbudget⟩:=cGC J hc.1
  calc _=2 * ∑ P∈J.minimalPrimesFinset,
          (Yg J P:ℚ)*(MvPolynomial.affineHilbertPolynomial P).coeff 2 := by
        rw [mul_sum]; refine sum_congr rfl fun P hP => ?_
        have hdim:=aQG hR hrel (Ideal.mem_minimalPrimesFinset.mp hP)
        simp only [MvPolynomial.affineDegree,Polynomial.leadingCoeff,hdim]; norm_num; ring
    _≤2*(MvPolynomial.affineHilbertPolynomial J).coeff 2 :=mul_le_mul_of_nonneg_left hbudget (by norm_num)
    _≤((shape R).b:ℚ)*(shape G).b:= by
        change 2*(MvPolynomial.affineHilbertPolynomial J).coeff 2≤(R.totalDegree :ℚ)*G.totalDegree
        change 6*(MvPolynomial.affineHilbertPolynomial F).leadingCoeff=(R.totalDegree :ℚ) at hcoeff
        nlinarith only [hc.2,congrArg (fun x :ℚ=>x*G.totalDegree) hcoeff]
    _≤_:=mul_le_mul_of_nonneg_left (by exact_mod_cast h.H6.1) (by positivity)
end
end qMiJnMd
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qYiv0Ea
open qHde8fc qDoysbd
open qokB5pc (jZ aS amG nG amN bu3)
open private core from ProximityPrize.SubmissionLower.ZeBsWTa
private def tab:ℕ→Array ℕ
  | 84 => #[0xbf0c72cf4d76df8,0x30c72cf4d76df8,0x30c72cf4d76df8,0xc72cf4d76df8,0x32cf4d76df8,0x32cf4d76df8,0xcf4d76df8,0x34d76df8,0x34d76df8,0xd76df8,0x36df8,0x36df8,0xdf8,0x38,0x38]
  | 85 => #[0xbf0c72cf4d76df7,0xbf0c72cf4d76df7,0x30c72cf4d76df8,0xc72cf4d76df8,0xc72cf4d76df8,0x32cf4d76df8,0xcf4d76df8,0xcf4d76df8,0x34d76df8,0xd76df8,0xd76df8,0x36df8,0xdf8,0xdf8,0x38]
  | 86 => #[0x2ebf0c72cf4d76db6,0xbf0c72cf4d76df6,0x30c72cf4d76df7,0x30c72cf4d76df7,0xc72cf4d76df8,0x32cf4d76df8,0x32cf4d76df8,0xcf4d76df8,0x34d76df8,0x34d76df8,0xd76df8,0x36df8,0x36df8,0xdf8,0x38,0x38]
  | 87 => #[0x2ebf0c72cf4d76d75,0xbf0c72cf4d76db5,0xbf0c72cf4d76db6,0x30c72cf4d76df6,0xc72cf4d76df7,0xc72cf4d76df7,0x32cf4d76df8,0xcf4d76df8,0xcf4d76df8,0x34d76df8,0xd76df8,0xd76df8,0x36df8,0xdf8,0xdf8,0x38]
  | 88 => #[0x2ebf0c72cf4d75d34,0x2ebf0c72cf4d75d74,0xbf0c72cf4d76d75,0x30c72cf4d76db5,0x30c72cf4d76db6,0xc72cf4d76df6,0x32cf4d76df7,0x32cf4d76df7,0xcf4d76df8,0x34d76df8,0x34d76df8,0xd76df8,0x36df8,0x36df8,0xdf8,0x38,0x38]
  | 89 => #[0xb6ebf0c72cf4d34cf3,0x2ebf0c72cf4d74d33,0xbf0c72cf4d75d34,0xbf0c72cf4d75d74,0x30c72cf4d76d75,0xc72cf4d76db5,0xc72cf4d76db6,0x32cf4d76df6,0xcf4d76df7,0xcf4d76df7,0x34d76df8,0xd76df8,0xd76df8,0x36df8,0xdf8,0xdf8,0x38]
  | 90 => #[0xb6ebf0c72cf4cf3cb2,0x2ebf0c72cf4d33cf2,0x2ebf0c72cf4d34cf3,0xbf0c72cf4d74d33,0x30c72cf4d75d34,0x30c72cf4d75d74,0xc72cf4d76d75,0x32cf4d76db5,0x32cf4d76db6,0xcf4d76df6,0x34d76df7,0x34d76df7,0xd76df8,0x36df8,0x36df8,0xdf8,0x38,0x37]
  | 91 => #[0xb6ebf0c72cf3cb2c71,0xb6ebf0c72cf3cf2cb1,0x2ebf0c72cf4cf3cb2,0xbf0c72cf4d33cf2,0xbf0c72cf4d34cf3,0x30c72cf4d74d33,0xc72cf4d75d34,0xc72cf4d75d74,0x32cf4d76d75,0xcf4d76db5,0xcf4d76db6,0x34d76df6,0xd76df7,0xd76df7,0x36df8,0xdf8,0xdb8,0x37]
  | 92 => #[0x2cb6ebf0c72cb2c71c30,0xb6ebf0c72cf2cb1c70,0x2ebf0c72cf3cb2c71,0x2ebf0c72cf3cf2cb1,0xbf0c72cf4cf3cb2,0x30c72cf4d33cf2,0x30c72cf4d34cf3,0xc72cf4d74d33,0x32cf4d75d34,0x32cf4d75d74,0xcf4d76d75,0x34d76db5,0x34d76db6,0xd76df6,0x36df7,0x35df7,0xdb8,0x37,0x36]
  | 93 => #[0x2cb6ebf0c72c71c30bef,0xb6ebf0c72cb1c70c2f,0xb6ebf0c72cb2c71c30,0x2ebf0c72cf2cb1c70,0xbf0c72cf3cb2c71,0xbf0c72cf3cf2cb1,0x30c72cf4cf3cb2,0xc72cf4d33cf2,0xc72cf4d34cf3,0x32cf4d74d33,0xcf4d75d34,0xcf4d75d74,0x34d76d75,0xd76db5,0xd36db6,0x35df6,0xdb7,0xd76,0x36]
  | 94 => #[0x2cb6ebf0c71c30befbae,0x2cb6ebf0c71c70c2fbee,0xb6ebf0c72c71c30bef,0x2ebf0c72cb1c70c2f,0x2ebf0c72cb2c71c30,0xbf0c72cf2cb1c70,0x30c72cf3cb2c71,0x30c72cf3cf2cb1,0xc72cf4cf3cb2,0x32cf4d33cf2,0x32cf4d34cf3,0xcf4d74d33,0x34d75d34,0x33d75d74,0xd36d75,0x35db5,0x34d76,0xd75,0x35,0x34]
  | 95 => #[0xaecb6ebf0c30befbaeb6d,0x2cb6ebf0c70c2fbeebad,0xb6ebf0c71c30befbae,0xb6ebf0c71c70c2fbee,0x2ebf0c72c71c30bef,0xbf0c72cb1c70c2f,0xbf0c72cb2c71c30,0x30c72cf2cb1c70,0xc72cf3cb2c71,0xc72cf3cf2cb1,0x32cf4cf3cb2,0xcf4d33cf2,0xcb4d34cf3,0x33d74d33,0xd35d34,0xcf4d74,0x34d35,0xd34,0xcf3,0x32]
  | 96 => #[0xaecb6ebf0befbaeb6db2c,0x2cb6ebf0c2fbeebadb6c,0x2cb6ebf0c30befbaeb6d,0xb6ebf0c70c2fbeebad,0x2ebf0c71c30befbae,0x2ebf0c71c70c2fbee,0xbf0c72c71c30bef,0x30c72cb1c70c2f,0x30c72cb2c71c30,0xc72cf2cb1c70,0x32cf3cb2c71,0x31cf3cf2cb1,0xcb4cf3cb2,0x33d33cf2,0x32cf4cf3,0xcf3d33,0x33cf4,0x32cb3,0xc72,0x31,0x30]
  | 97 => #[0xaecb6ebefbaeb6db2caeb,0xaecb6ebefbeebadb6cb2b,0x2cb6ebf0befbaeb6db2c,0xb6ebf0c2fbeebadb6c,0xb6ebf0c30befbaeb6d,0x2ebf0c70c2fbeebad,0xbf0c71c30befbae,0xbf0c71c70c2fbee,0x30c72c71c30bef,0xc72cb1c70c2f,0xc32cb2c71c30,0x31cf2cb1c70,0xcb3cb2c71,0xc72cf2cb1,0x32cb3cb2,0xcb2cf2,0xc71cb1,0x30c70,0xc2f,0xbee,0x2d]
  | 98 => #[0x2aaecb6ebaeb6db2caebaaa,0xaecb6ebeebadb6cb2baea,0x2cb6ebefbaeb6db2caeb,0x2cb6ebefbeebadb6cb2b,0xb6ebf0befbaeb6db2c,0x2ebf0c2fbeebadb6c,0x2ebf0c30befbaeb6d,0xbf0c70c2fbeebad,0x30c71c30befbae,0x2fc71c70c2fbee,0xc32c71c30bef,0x31cb1c70c2f,0x30c72c71c30,0xc71cb1c70,0x31c72c71,0x30c31c30,0xbf0bef,0x2fbae,0x2eb6d,0xb2c,0x2b,0x2a]
  | 99 => #[0x2aaecb6eb6db2caebaaaa69,0xaecb6ebadb6cb2baeaaa9,0xaecb6ebaeb6db2caebaaa,0x2cb6ebeebadb6cb2baea,0xb6ebefbaeb6db2caeb,0xb6ebefbeebadb6cb2b,0x2ebf0befbaeb6db2c,0xbf0c2fbeebadb6c,0xbb0c30befbaeb6d,0x2fc70c2fbeebad,0xc31c30befbae,0xbf0c70c2fbee,0x30c31c30bef,0xc30c70c2f,0xbefc2fbee,0x2ebeebad,0xbadb6c,0xb6cb2b,0x2baea,0xaa9,0xa68,0x27]
  | 100 => #[0x2aaecb6db2caebaaaa69a28,0x2aaecb6db6cb2baeaaa9a68,0xaecb6eb6db2caebaaaa69,0x2cb6ebadb6cb2baeaaa9,0x2cb6ebaeb6db2caebaaa,0xb6ebeebadb6cb2baea,0x2ebefbaeb6db2caeb,0x2dbefbeebadb6cb2b,0xbb0befbaeb6db2c,0x2fc2fbeebadb6c,0x2ebf0befbaeb6d,0xbefc2fbeebad,0x2fbf0befbae,0x2ebafbaeb6d,0xb6eb6db2c,0x2db2caeb,0x2caebaaa,0xaaaa69,0x29a28,0x289e7,0x9a6,0x25,0x24]
  | 101 => #[0xa6aaecb2caebaaaa69a289e7,0x2aaecb6cb2baeaaa9a68a27,0xaecb6db2caebaaaa69a28,0xaecb6db6cb2baeaaa9a68,0x2cb6eb6db2caebaaaa69,0xb6ebadb6cb2baeaaa9,0xb2ebaeb6db2caebaaa,0x2dbeebadb6cb2baea,0xbafbaeb6db2caeb,0xb6ebeebadb6cb2b,0x2ebafbaeb6db2c,0xbaebeebadb6c,0xb6dbadb6cb2b,0x2cb6cb2baea,0xb2baeaaa9,0xaeaaa9a68,0x29a68a27,0xa279e6,0x9e69a5,0x25964,0x923,0x8e2,0x21]
  | 102 => #[0xa6aaecaebaaaa69a289e79a6,0x2aaecb2baeaaa9a68a279e6,0x2aaecb2caebaaaa69a289e7,0xaecb6cb2baeaaa9a68a27,0x2cb6db2caebaaaa69a28,0x2bb6db6cb2baeaaa9a68,0xb2eb6db2caebaaaa69,0x2dbadb6cb2baeaaa9,0x2cb6eb6db2caebaaa,0xb6dbadb6cb2baea,0x2db6eb6db2caeb,0x2cb2db2caebaaa,0xaecaebaaaa69,0x2baaaa69a28,0x2aa69a289e7,0xa289e79a6,0x279a6965,0x26965924,0x9248e3,0x238a2,0x22861,0x820,0x1f,0x1e]
  | 103 => #[0xa6aaebaaaa69a289e79a6965,0xa6aaebaeaaa9a68a279e69a5,0x2aaecaebaaaa69a289e79a6,0xaecb2baeaaa9a68a279e6,0xaacb2caebaaaa69a289e7,0x2bb6cb2baeaaa9a68a27,0xb2db2caebaaaa69a28,0xaecb6cb2baeaaa9a68,0x2cb2db2caebaaaa69,0xb2cb6cb2baeaaa9,0xaebb2baeaaa9a68,0x2aaeaaa9a68a27,0xaa9a68a279e6,0xa68a279e69a5,0x279e69a5964,0x9a5964923,0x9649238e2,0x238e28a1,0x8a1860,0x86081f,0x1f7de,0x79d,0x75c,0x1b]
  | 104 => #[0x28a6aaaaa69a289e79a6965924,0xa6aaeaaa9a68a279e69a5964,0x2aaebaaaa69a289e79a6965,0x29aebaeaaa9a68a279e69a5,0xaacaebaaaa69a289e79a6,0x2bb2baeaaa9a68a279e6,0x2aaecaebaaaa69a289e7,0xaebb2baeaaa9a68a27,0x2baecaebaaaa69a28,0x2aaabaaaa69a289e7,0xa6aa69a289e79a6,0x29a289e79a6965,0x289e79a6965924,0x9a69659248e3,0x259248e38a2,0x248e38a2861,0x8a2861820,0x218207df,0x207df79e,0x79e75d,0x1d71c,0x1c6db,0x69a,0x19,0x18]
  | 105 => #[0x28a6aa69a289e79a69659248e3,0xa6aaa9a68a279e69a5964923,0xa2aaaaa69a289e79a6965924,0x29aeaaa9a68a279e69a5964,0xaabaaaa69a289e79a6965,0xa6aaeaaa9a68a279e69a5,0x2aaabaaaa69a289e79a6,0xaaaaeaaa9a68a279e6,0xa69aa9a68a279e69a5,0x28a68a279e69a5964,0xa279e69a5964923,0x9e69a59649238e2,0x259649238e28a1,0x9238e28a1860,0x8e28a186081f,0x2186081f7de,0x81f7de79d,0x7de79d75c,0x1d75c71b,0x71b6da,0x6da699,0x19658,0x617,0x5d6,0x15]
  | 106 => #[0x28a69a289e79a69659248e38a2,0x27a69a68a279e69a59649238e2,0xa2aa69a289e79a69659248e3,0x29aa9a68a279e69a5964923,0x28a6aa69a289e79a6965924,0xa69aa9a68a279e69a5964,0x29a6aa69a289e79a6965,0x28a29a289e79a6965924,0x9e89e79a69659248e3,0x279a69659248e38a2,0x269659248e38a2861,0x9248e38a2861820,0x238a28618207df,0x228618207df79e,0x8207df79e75d,0x1f79e75d71c,0x1e75d71c6db,0x71c6db69a,0x1b69a659,0x1a659618,0x6185d7,0x17596,0x16555,0x514,0x13,0x12]
  | 107 => #[0x28a289e79a69659248e38a2861,0x27a68a279e69a59649238e28a1,0xa29a289e79a69659248e38a2,0x9e8a68a279e69a59649238e2,0x28a29a289e79a69659248e3,0xa28a68a279e69a5964923,0x9e7a279e69a59649238e2,0x269e69a59649238e28a1,0x9a59649238e28a1860,0x9649238e28a186081f,0x238e28a186081f7de,0x8a186081f7de79d,0x86081f7de79d75c,0x1f7de79d75c71b,0x79d75c71b6da,0x75c71b6da699,0x1b6da699658,0x699658617,0x6586175d6,0x175d6595,0x595554,0x554513,0x134d2,0x491,0x450,0xf]
  | 108 => #[0x289e79a69659248e38a2861820,0x27a279e69a59649238e28a1860,0x269e89e79a69659248e38a2861,0x9e7a279e69a59649238e28a1,0x279e89e79a69659248e38a2,0x269a79a69659248e38a2861,0x9669659248e38a2861820,0x259248e38a28618207df,0x248e38a28618207df79e,0x8a28618207df79e75d,0x218207df79e75d71c,0x207df79e75d71c6db,0x79e75d71c6db69a,0x1d71c6db69a659,0x1c6db69a659618,0x69a6596185d7,0x196185d7596,0x185d7596555,0x596555514,0x155144d3,0x144d3492,0x492451,0x11410,0x103cf,0x38e,0xd,0xc]
  | 109 => #[0x279a69659248e38a28618207df,0x269e69a59649238e28a186081f,0x269a79a69659248e38a2861820,0x9a69e69a59649238e28a1860,0x9659a59649238e28a186081f,0x249649238e28a186081f7de,0x9238e28a186081f7de79d,0x8e28a186081f7de79d75c,0x2186081f7de79d75c71b,0x81f7de79d75c71b6da,0x7de79d75c71b6da699,0x1d75c71b6da699658,0x71b6da699658617,0x6da6996586175d6,0x196586175d6595,0x6175d6595554,0x5d6595554513,0x155545134d2,0x5134d2491,0x4d2491450,0x1145040f,0x40f3ce,0x3ce38d,0xd34c,0x30b,0x2ff,0x3f]
  | 110 => #[0x269659248e38a28618207df79e,0x259a59649238e28a186081f7de,0x259669659248e38a28618207df,0x249259248e38a28618207df79e,0x8e48e38a28618207df79e75d,0x238a28618207df79e75d71c,0x228618207df79e75d71c6db,0x8207df79e75d71c6db69a,0x1f79e75d71c6db69a659,0x1e75d71c6db69a659618,0x71c6db69a6596185d7,0x1b69a6596185d7596,0x1a6596185d7596555,0x6185d7596555514,0x175965555144d3,0x165555144d3492,0x5144d3492451,0x13492451410,0x124514103cf,0x4103cf38e,0xf38e34d,0xe34d30c,0x30cfff,0x3ffff,0x3ffff,0xfff,0x3f,0x3f]
  | 111 => #[0x259248e38a28618207df79e75d,0x249649238e28a186081f7de79d,0x239238e28a186081f7de79d75c,0x228e28a186081f7de79d75c71b,0x8a186081f7de79d75c71b6da,0x86081f7de79d75c71b6da699,0x1f7de79d75c71b6da699658,0x79d75c71b6da699658617,0x75c71b6da6996586175d6,0x1b6da6996586175d6595,0x6996586175d6595554,0x6586175d6595554513,0x175d65955545134d2,0x5955545134d2491,0x5545134d2491450,0x134d249145040f,0x49145040f3ce,0x45040f3ce38d,0xf3ce38d37f,0x38d37ffff,0x37fffffff,0x3fffffff,0xffffff,0xffffff,0x3ffff,0xfff,0xfff,0x3f]
  | 112 => #[0x248e38a28618207df79e75d71c,0x238a28618207df79e75d71c6db,0x228618207df79e75d71c6db69a,0x218207df79e75d71c6db69a659,0x207df79e75d71c6db69a659618,0x79e75d71c6db69a6596185d7,0x1d71c6db69a6596185d7596,0x1c6db69a6596185d7596555,0x69a6596185d7596555514,0x196185d75965555144d3,0x185d75965555144d3492,0x5965555144d3492451,0x155144d3492451410,0x144d34924514103cf,0x4924514103cf38e,0x114103cf38efff,0x103cf38effffff,0x38efffffffff,0x3ffffffffff,0x3ffffffffff,0xfffffffff,0x3fffffff,0x3fffffff,0xffffff,0x3ffff,0x3ffff,0xfff,0x3f,0x3f]
  | _ => #[]
def piv (w f a :ℕ) :ℕ:=((tab w)[f]?.getD 0 >>> (6*a)) % 64
def cutOf (w f a :ℕ) :ℕ:=if piv w f a=63 then w-98 else piv w f a+1
def AddrOK (w f a :ℕ) :Bool :=
  decide (0<cutOf w f a∧w≤112) &&
    (piv w f a == 63 || decide (piv w f a<57∧piv w f a≤w∧w - piv w f a<99) &&
      (List.range (groupCount (w - piv w f a) (piv w f a))).any
        fun j=>decide (ZX (w - piv w f a) (piv w f a) j=aS w f a))
def Easy (w f a :ℕ) :Bool :=
  decide (3*(57 - cutOf w f a)+(w - 56-3*a - 2*f)+2*min f 16≤w - 56+2) ||
    decide (3*(112 - w)+2*a+(w - 56-3*a - 2*f)/2<cutOf w f a)
def Ok (w f a :ℕ) :Prop :=
  ∀ e :aY,cP (aD e.val)=w→e.val 3=f→e.val 0=a→bk1 e
theorem addr_pos {w f a :ℕ} (h:AddrOK w f a=true) :0<cutOf w f a∧w≤112 :=
  of_decide_eq_true ((Bool.and_eq_true _ _).mp h).1
theorem ok_of_span {w f a :ℕ} (hA:AddrOK w f a=true)
    (hs : ∀ e :aY,cP (aD e.val)=w→e.val 3=f→e.val 0=a →
      cE (cutOf w f a) (aD e.val)∈jZ e (cutOf w f a)) :Ok w f a := by
  intro e he hf ha
  refine ⟨cutOf w f a,?_,hs e he hf ha⟩
  have h2 :=((Bool.and_eq_true _ _).mp hA).2
  by_cases h63:piv w f a=63
  · left
    rw [he]
    unfold cutOf
    rw [if_pos h63]
  · right
    rcases (Bool.or_eq_true _ _).mp h2 with h | h
    · exact absurd (beq_iff_eq.mp h) h63
    obtain ⟨h3,h4⟩:=(Bool.and_eq_true _ _).mp h
    obtain ⟨hi,hiw,hg⟩:=of_decide_eq_true h3
    obtain ⟨j,hj,hp⟩:=List.any_eq_true.mp h4
    refine ⟨⟨⟨w - piv w f a,hg⟩,⟨piv w f a,hi⟩,⟨j,List.mem_range.mp hj⟩⟩,?_,?_,?_⟩
    · change ZX _ _ _ = _
      rw [of_decide_eq_true hp,amG e he,hf,ha]
    · change w - piv w f a+piv w f a= _
      omega
    · change ((cutOf w f a :ℕ) :ℤ)≤(piv w f a :ℤ)+1
      unfold cutOf
      rw [if_neg h63]
      push_cast
      omega
theorem okE {w f a :ℕ} (h: (AddrOK w f a && Easy w f a)=true) :Ok w f a := by
  obtain ⟨hA,hE⟩:=(Bool.and_eq_true _ _).mp h
  obtain ⟨hpos,hw⟩:=addr_pos hA
  refine ok_of_span hA fun e he hf ha => ?_
  have hc:=nG e
  rcases (Bool.or_eq_true _ _).mp hE with h | h
  · have h' := of_decide_eq_true h
    apply amN e (s :=w - 56) (by omega) (by omega)
    apply bu3
    change 3*(57 - cutOf w f a)+e.val 2+2*min (e.val 3) 16≤w - 56+2
    rw [hf]
    omega
  · have h' := of_decide_eq_true h
    have ho:GN.ord e.val=3*e.val 0+e.val 2+2*e.val 3:=rfl
    obtain ⟨P,hP,hsep⟩:=qhonTAe.interpolate e (by omega)
    refine qhonTAe.Ae e _ hpos P
      (MvPolynomial.restrictWeightedDegree_mono _ ?_ hP) hsep
    unfold qhonTAe.cutBudget
    omega
theorem okD {w f a n code :ℕ} (hA:AddrOK w f a=true)
    (hf :dM (112 - w) (cutOf w f a) n code) (hh:Head (112 - w) a f n code)
    (hl : ∀ t≤112 - w,lK (112 - w) a f n code t) :Ok w f a :=
  ok_of_span hA fun e he hef hea=>core (addr_pos hA).1 (addr_pos hA).2 hf hh hl e he hef hea
theorem kc {lo hi:ℕ} (h : ∀ w f a,lo≤w→w≤hi→3*a+2*f+56≤w→Ok w f a) :
    aGq lo hi:= by
  intro e hlo hhi
  have hc:=nG e
  exact h _ (e.val 3) (e.val 0) hlo hhi (by omega) e rfl rfl rfl
end qYiv0Ea
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qQCYsrb

open P6_6 P6_6_8 q2w4Sxc
open private g11 g15 g16 g18 g19 g4 from ProximityPrize.SubmissionLower.ZBG70hc
local notation "m!" n "," x "," w =>
  segment (len:=n) (cost:=x) (word:=w) rfl rfl
local notation "o!" g "," h=>strict g (by decide) h rfl (by decide)
local notation "z!" h =>
  transport ⟨by decide,by decide,by decide⟩ ⟨by decide,by decide,by decide⟩ (by decide) h
local notation "b!" m "," x "," y=>Certificate.splitB m (Certificate.trim x) (Certificate.trim y)
local notation "j!" m "," x "," y=>Certificate.rK m (Certificate.trim x) (Certificate.trim y)
local notation "t!" m "," x "," y=>Certificate.splitT m (Certificate.trim x) (Certificate.trim y)
local notation "p!" vk "," vf "," h "," hc =>
  regular (k :=vk) (f :=vf) (by decide) h (by decide) (by decide) hc rfl (by decide)
private theorem r1 :Order 12 49 1 3 1 :=o! g4,(joinTail (m! 50,0x4167f676ae8,0x807070606060505) (m! 92,0xec2c625c39,0x2615120807))
private theorem r2 :Order 12 92 1 11 1 :=o! g11,(joinTail (m! 24,0x12913505628,0x403030303030302) (m! 41,0x4315b9a93d,0x100a080403))
private theorem q12_1 :Lw ⟨12,6,1⟩=⟨0xfb47c268c425,0x5a661ee76e923,0xbe736425dc9⟩:=rfl
private theorem q12_2 :Lw ⟨12,6,2⟩=⟨0xfabfeccb7cd8,0x59b6b3605e257,0x23d84ab0fb65⟩:=rfl
theorem s12 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨12,6,t⟩ ⟨1,3,1⟩ (cap ⟨12,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (j! 10,(t! 1,(p! 26,0x11de9292646a9b,(.inl (z! r1)),q12_1),(p! 45,0x235d1802238049,(.inl (z! r1)),q12_1)),(Certificate.prune (z! r2)))
  · exact .trim (j! 10,(t! 1,(p! 26,0x11de9292646a9b,(.inl (z! r1)),q12_2),(p! 45,0x235d1802238049,(.inl (z! r1)),q12_2)),(Certificate.prune (z! r2)))
private theorem q13_1 :Lw ⟨13,6,1⟩=⟨0xe7bb27967c02,0x51c8c3762a2a8,0xaa2f5545ce0⟩:=rfl
private theorem q13_2 :Lw ⟨13,6,2⟩=⟨0xe7375b392049,0x51294083f05d5,0x2006ef176776⟩:=rfl
theorem s13 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨13,6,t⟩ ⟨1,3,1⟩ (cap ⟨13,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (j! 10,(t! 1,(p! 29,0xfc6043d88ca98,(.inl (z! r1)),q13_1),(p! 49,0x1fbd706a98920e,(.inl (z! r1)),q13_1)),(Certificate.prune (z! r2)))
  · exact .trim (j! 10,(t! 1,(p! 29,0xfc6043d88ca98,(.inl (z! r1)),q13_2),(p! 49,0x1fbd706a98920e,(.inl (z! r1)),q13_2)),(Certificate.prune (z! r2)))
private theorem r3:Order 14 99 1 10 1 :=o! g15,(m! 60,0xf02f9dab2c,0x180e0c0a)
private theorem q14_1 :Lw ⟨14,6,1⟩=⟨0xcfa633f8d068,0x47b553b86488b,0x92bac57a4f1⟩:=rfl
private theorem q14_2 :Lw ⟨14,6,2⟩=⟨0xcf27503234c2,0x472833a47b1ac,0x1b9bc2770585⟩:=rfl
theorem s14 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨14,6,t⟩ ⟨1,3,1⟩ (cap ⟨14,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (j! 9,(t! 1,(p! 26,0xdd66586c51f01,(.inl (z! r1)),q14_1),(p! 43,0x1c5d50f65f8705,(.inl (z! r1)),q14_1)),(Certificate.prune r3))
  · exact .trim (j! 9,(t! 1,(p! 26,0xdd66586c51f01,(.inl (z! r1)),q14_2),(p! 43,0x1c5d50f65f8705,(.inl (z! r1)),q14_2)),(Certificate.prune (bO4 r3)))
private theorem r4 :Order 15 62 2 6 2 :=o! g16,(m! 60,0x1078507d298,0x3c)
private theorem r5:Order 15 109 1 11 1 :=o! g18,(m! 42,0x56b5e9ea3d,0x1b0f)
private theorem q15_1 :Lw ⟨15,6,1⟩=⟨0xb290868f10f4,0x3c0baaafc0c1b,0x77c5cb6fd27⟩:=rfl
private theorem q15_2 :Lw ⟨15,6,2⟩=⟨0xb2187bc7d540,0x3b9403bad66e0,0x1687e4d17974⟩:=rfl
theorem s15 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨15,6,t⟩ ⟨1,3,1⟩ (cap ⟨15,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (j! 10,(t! 1,(p! 37,0xbe800ac23cf83,(.inl (z! r1)),q15_1),(p! 62,0x17744867dce7be,(.inl r4),q15_1)),(Certificate.prune r5))
  · exact .trim (j! 10,(t! 1,(p! 37,0xbe800ac23cf83,(.inl (z! r1)),q15_2),(p! 62,0x17744867dce7be,(.inl (bO4 r4)),q15_2)),(Certificate.prune (bO4 r5)))
private theorem r6:Order 16 132 1 3 1 :=o! g19,(joinTail (m! 31,0x5a0247ff12,0x504040404030403) (m! 61,0x11bd3c0e1b,0x1a0e06060504))
theorem s16 (t:ℕ) (h:t=1∨t=2) :Certificate ⟨16,6,t⟩ ⟨1,3,1⟩ (cap ⟨16,6,t⟩) := by
  rcases h with rfl | rfl
  · exact .trim (Certificate.prune r6)
  · exact .trim (Certificate.prune (bO4 r6))
end qQCYsrb
end
