import ProximityPrize.SubmissionLower.RelativeRectangleCount6815
import ProximityPrize.SubmissionLower.RelativeWideRows
namespace ProximityPrize.SubmissionLower.RelativeCertificate6815
open RelativeCertificate6814
open scoped BigOperators
open MvPolynomial RCN100 RCN119 RCN122 RCN260 RelativeBounded6814 ContactOrderBridge
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 20000

def hiRect (d : Rectangle) : Rectangle := {d with lo := d.hi}

def cutAt (b : Band) (d : Rectangle) (nu : ℕ) : ℕ :=
  d.alpha*181245-d.beta*min (nu-131071+1) ((b.B+b.R-1)*181245)

def tanK (b : Band) (d : Rectangle) : ℕ := cutAt b d d.lo-cutoff b d
def tanE (b : Band) (d : Rectangle) : ℕ := cutAt b d d.lo-d.lo

def tanLower (b : Band) (d : Rectangle) (T : ℕ) : ℕ :=
  max ((cutoff b d+1)/131071+1) (T+tanE b d/131071+1)

def tanRowGood (b : Band) (d : Rectangle) (mu : ℕ) : Prop :=
  let m := d.alpha-d.beta*(mu-1)
  let a := tanMarginA (cutoff b d) (tanK b d) (tanE b d) d.s b.R m mu
  let v := tanMarginB (tanE b d) d.s b.R m mu
  let c := tanMarginC (cutoff b d) (tanK b d) (tanE b d) d.s b.R m mu
  max 0 (-a)<a*d.L0+v*b.T0+c ∧ max 0 (-a)<a*d.L1+v*b.T1+c

instance tanRowGoodDecidable (b : Band) (d : Rectangle) (mu : ℕ) : Decidable (tanRowGood b d mu) := by
  unfold tanRowGood
  infer_instance

def checkTanRows (b : Band) (d : Rectangle) : ℕ → Bool
  | 0 => true
  | n+1 => checkTanRows b d n && decide (tanRowGood b d n)

theorem checkTanRows_spec (b : Band) (d : Rectangle) (n : ℕ) (hc : checkTanRows b d n=true) :
    ∀ mu<n, tanRowGood b d mu := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [checkTanRows,Bool.and_eq_true,decide_eq_true_eq] at hc
    intro mu hmu
    rcases Nat.lt_or_eq_of_le (show mu≤n by omega) with h | h
    · exact ih hc.1 mu h
    · simpa only [h] using hc.2

def WideShape (b : Band) (d : Rectangle) : Prop :=
  Shape b (hiRect d) ∧ 131071≤d.lo ∧ d.lo≤d.hi ∧ d.hi<cutoff b d ∧
  d.s≤(cutoff b d+1)/131071 ∧ d.s-b.R≤tanE b d/131071 ∧
  tanLower b d b.T0≤d.L0 ∧ tanLower b d b.T1≤d.L1

instance wideShapeDecidable (b : Band) (d : Rectangle) : Decidable (WideShape b d) := by
  unfold WideShape Shape
  infer_instance

theorem cutoff_hiRect (b : Band) (d : Rectangle) : cutoff b (hiRect d)=cutoff b d := rfl
theorem total_hiRect (b : Band) (d : Rectangle) (T : ℕ) : total b (hiRect d) T=total b d T := rfl

theorem tan_total_lower (b : Band) (d : Rectangle) (T : ℕ) (hshape : WideShape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) : tanLower b d T≤total b d T := by
  rcases hshape with ⟨hs,_,_,_,_,_,hL0,hL1⟩
  have h01 := hs.1
  unfold total
  split_ifs with he
  · have ht : T=b.T0 := by omega
    simpa only [ht] using hL0
  · have hstrict : b.T0<b.T1 := by omega
    simp only [tanLower,max_le_iff] at hL0 hL1 ⊢
    refine ⟨?_,?_⟩
    · exact ceilBlend_const_lower _ _ _ _ _ _ hstrict hT0 hT1 hL0.1 hL1.1
    · simpa only [Nat.add_assoc] using ceilBlend_affine_lower b.T0 b.T1 d.L0 d.L1 T
        (tanE b d/131071+1) hstrict hT0 hT1 (by omega) (by omega)

theorem tan_margin_positive (b : Band) (d : Rectangle) (T mu : ℕ) (hshape : WideShape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hgood : tanRowGood b d mu) :
    0<tanMarginA (cutoff b d) (tanK b d) (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu*total b d T+
      tanMarginB (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu*T+
      tanMarginC (cutoff b d) (tanK b d) (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu := by
  unfold tanRowGood at hgood
  unfold total
  split_ifs with he
  · have ht : T=b.T0 := by omega
    rw [ht]
    exact lt_of_le_of_lt (le_max_left _ _) hgood.1
  · have hstrict : b.T0<b.T1 := by have := hshape.1.1; omega
    let p := b.T1-T
    let q := T-b.T0
    have hsum : p+q=b.T1-b.T0 := by dsimp [p,q]; omega
    have ht : (p+q)*T=p*b.T0+q*b.T1 := by
      rw [hsum]
      exact total_blend_identity _ _ _ hT0 hT1
    have hb := ceilBlend_bounds b.T0 b.T1 d.L0 d.L1 T hstrict hT0 hT1
    apply rounded_affine_positive (p : ℤ) (q : ℤ) d.L0 d.L1 b.T0 b.T1
      (ceilBlend b.T0 b.T1 d.L0 d.L1 T) T _ _ _
      (by exact_mod_cast Nat.zero_le p) (by exact_mod_cast Nat.zero_le q)
      (by exact_mod_cast (show 0<p+q by omega)) (by exact_mod_cast ht) ?_ ?_ hgood.1 hgood.2
    · exact_mod_cast (show p*d.L0+q*d.L1≤(p+q)*ceilBlend b.T0 b.T1 d.L0 d.L1 T by simpa only [hsum] using hb.1)
    · exact_mod_cast (show (p+q)*ceilBlend b.T0 b.T1 d.L0 d.L1 T≤p*d.L0+q*d.L1+(p+q) by simpa only [hsum] using hb.2.le)

theorem cutAt_affine (b : Band) (d : Rectangle) (nu : ℕ) (hshape : WideShape b d)
    (hlo : d.lo≤nu) (hhi : nu≤d.hi) :
    cutAt b d nu=cutoff b d+d.beta*(d.hi-nu) := by
  have htail : d.hi≤tail b := hshape.1.2.2.2.2.2.1
  have hDh : d.hi<cutoff b d := hshape.2.2.2.1
  have hw : 131071≤d.lo := hshape.2.1
  unfold cutAt
  unfold cutoff at hDh ⊢
  unfold tail at htail
  have hm1 : min (nu-131071+1) ((b.B+b.R-1)*181245)=nu-131071+1 := min_eq_left (by omega)
  have hm2 : min (d.hi-131071+1) ((b.B+b.R-1)*181245)=d.hi-131071+1 := min_eq_left (by omega)
  rw [hm1]
  rw [hm2] at hDh ⊢
  have hsplit : d.beta*(d.hi-131071+1)=d.beta*(nu-131071+1)+d.beta*(d.hi-nu) := by
    have hx : d.hi-131071+1=(nu-131071+1)+(d.hi-nu) := by omega
    rw [hx, Nat.mul_add]
  rw [hsplit] at hDh ⊢
  generalize d.beta*(nu-131071+1)=P at hDh ⊢
  generalize d.beta*(d.hi-nu)=Q at hDh ⊢
  omega

theorem tanK_eq (b : Band) (d : Rectangle) (hshape : WideShape b d) :
    tanK b d=d.beta*(d.hi-d.lo) := by
  unfold tanK
  rw [cutAt_affine b d d.lo hshape le_rfl hshape.2.2.1]
  omega

theorem tanE_eq (b : Band) (d : Rectangle) (hshape : WideShape b d) :
    tanE b d=(cutoff b d-d.hi)+(d.beta+1)*(d.hi-d.lo) := by
  have hDh := hshape.2.2.2.1
  have hlh := hshape.2.2.1
  unfold tanE
  rw [cutAt_affine b d d.lo hshape le_rfl hlh]
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem wide_rows (b : Band) (d : Rectangle) (T nu : ℕ) (hshape : WideShape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1)
    (hcheck : checkRows b (hiRect d) (b.B+b.R+1)=true)
    (htan : checkTanRows b d (b.B+b.R+1)=true)
    (hlo : d.lo≤nu) (hhi : nu≤d.hi) :
    ∀ mu≤b.B+b.R, coefficientCount (cutAt b d nu-nu) 131071 (total b d T-T) (d.s-b.R)+
      262144*profileRowRank d.alpha d.beta (total b d T) d.s T b.R mu <
        coefficientCount (cutAt b d nu) 131071 (total b d T) d.s := by
  intro mu hmu
  have hcut := cutAt_affine b d nu hshape hlo hhi
  have hDh : d.hi<cutoff b d := hshape.2.2.2.1
  have hshape' := hshape
  rcases hshape' with ⟨hS,hw,hlh,_,hsq1,hsqE,_,_⟩
  have hR : b.R≤d.s := hS.2.1
  have hs : d.s<131071 := hS.2.2.1
  have hsq : d.s≤cutoff b d/131071 := hS.2.2.2.2.2.2.2.1
  have hl := total_lower b (hiRect d) T hS hT0 hT1
  have hLa : T+d.alpha+d.s≤total b d T := (le_max_left _ _).trans hl
  have htl := tan_total_lower b d T hshape hT0 hT1
  have hLt1 : (cutoff b d+1)/131071+1≤total b d T := (le_max_left _ _).trans htl
  have hLt2 : T+tanE b d/131071+1≤total b d T := (le_max_right _ _).trans htl
  set m := d.alpha-d.beta*(mu-1) with hmdef
  set L := total b d T with hLdef
  have hTL : T≤L := by omega
  have hmL : m≤d.alpha := Nat.sub_le _ _
  by_cases hr : RCN119.localRankBound (m-mu) (L-T) (d.s-b.R) ≤ RCN119.localRankBound m L d.s
  · have hHi : coefficientCount (cutoff b d-d.hi) 131071 (L-T) (d.s-b.R)+
        262144*(RCN119.localRankBound m L d.s-RCN119.localRankBound (m-mu) (L-T) (d.s-b.R)) <
        coefficientCount (cutoff b d) 131071 L d.s :=
      rectangle_rows b (hiRect d) T hS hT0 hT1 hcheck mu hmu
    have hLo := tan_row_test_of_margin (cutoff b d) (tanK b d) (tanE b d) L d.s T b.R m mu
      hs hR hTL hsq hsq1 hsqE hLt1 (by omega) (by omega) (by omega)
      (tan_margin_positive b d T mu hshape hT0 hT1 (checkTanRows_spec _ _ _ htan mu (by omega))) hr
    rw [tanK_eq b d hshape, tanE_eq b d hshape] at hLo
    have hE : cutAt b d nu-nu=(cutoff b d-d.hi)+(d.beta+1)*(d.hi-nu) := by
      rw [hcut, Nat.add_mul, Nat.one_mul]; omega
    show coefficientCount (cutAt b d nu-nu) 131071 (L-T) (d.s-b.R)+
        262144*(RCN119.localRankBound m L d.s-RCN119.localRankBound (m-mu) (L-T) (d.s-b.R)) <
        coefficientCount (cutAt b d nu) 131071 L d.s
    rw [hE, hcut]
    exact wide_rows_core 131071 L d.s T b.R _ d.beta (cutoff b d) (cutoff b d-d.hi) (d.hi-d.lo)
      (d.hi-nu) (by omega) hHi hLo
  · show coefficientCount (cutAt b d nu-nu) 131071 (L-T) (d.s-b.R)+
        262144*(RCN119.localRankBound m L d.s-RCN119.localRankBound (m-mu) (L-T) (d.s-b.R)) <
        coefficientCount (cutAt b d nu) 131071 L d.s
    have hzero : RCN119.localRankBound m L d.s-RCN119.localRankBound (m-mu) (L-T) (d.s-b.R)=0 := by
      omega
    rw [hzero, Nat.mul_zero, Nat.add_zero]
    have hpos : 0<cutAt b d nu := by rw [hcut]; omega
    exact multiple_count_lt_source (cutAt b d nu) 131071 L d.s nu T b.R hpos (by omega)

def WideValid (b : Band) (d : Rectangle) : Prop :=
  WideShape b d ∧ 1≤b.R ∧ b.B<2130706433 ∧ b.R<2130706433 ∧ b.T1<2130706433 ∧
  cutAt b d d.lo≤131071*(d.U+1) ∧
  (pair b d).mixedCost.y<2130706433 ∧ (pair b d).mixedCost.r<2130706433 ∧
  (pair b d).mixedCost.z<2130706433 ∧
  AsymmetricHelper.leftRegularCountCap (pair b d)≤b.count ∧
  checkRows b (hiRect d) (b.B+b.R+1)=true ∧ checkTanRows b d (b.B+b.R+1)=true

instance wideValidDecidable (b : Band) (d : Rectangle) : Decidable (WideValid b d) := by
  unfold WideValid
  infer_instance

theorem wide_rows_all (b : Band) (d : Rectangle) (T nu : ℕ) (hshape : WideShape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1)
    (hcheck : checkRows b (hiRect d) (b.B+b.R+1)=true)
    (htan : checkTanRows b d (b.B+b.R+1)=true)
    (hlo : d.lo≤nu) (hhi : min nu (tail b)≤d.hi) :
    ∀ mu≤b.B+b.R, coefficientCount (cutAt b d nu-nu) 131071 (total b d T-T) (d.s-b.R)+
      262144*profileRowRank d.alpha d.beta (total b d T) d.s T b.R mu <
        coefficientCount (cutAt b d nu) 131071 (total b d T) d.s := by
  by_cases hn : nu≤d.hi
  · exact wide_rows b d T nu hshape hT0 hT1 hcheck htan hlo hn
  · have htail : d.hi≤tail b := hshape.1.2.2.2.2.2.1
    have hht : tail b≤d.hi := by
      have : min nu (tail b)=tail b := min_eq_right (by omega)
      omega
    have heq : cutAt b d nu=cutAt b d d.hi := by
      unfold cutAt
      unfold tail at htail hht
      rw [min_eq_right (show (b.B+b.R-1)*181245≤nu-131071+1 by omega),
        min_eq_right (show (b.B+b.R-1)*181245≤d.hi-131071+1 by omega)]
    have hrows := wide_rows b d T d.hi hshape hT0 hT1 hcheck htan hshape.2.2.1 le_rfl
    rw [heq]
    exact profile_rows_mono_weight (by omega) hrows

variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance wideRectDecEqK : DecidableEq K := Classical.decEq K

theorem regular_count_of_wide_rectangle (b : Band) (d : Rectangle) (hvalid : WideValid b d)
    {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T b.R)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : b.R≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤b.B)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hlo : d.lo≤nu) (hhi : min nu (tail b)≤d.hi)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤b.count := by
  classical
  rcases hvalid with ⟨hshape,hRpos,hBchar,hRchar,hTchar,hU,hgY,hgR,hgZ,hprice,hcheck,htan⟩
  have hF := RCN167.positiveRFactors_spec H F.val F.property
  let Delta := RCN140.regularSeeds H selected Gamma F
  have hsub : Delta⊆Gamma := RCN140.regularSeeds_subset H selected Gamma F
  have hsol : ∀ gamma∈Delta, specialization K (selected gamma) gamma F.val=0 := by
    intro gamma hg
    exact (Finset.mem_filter.mp hg).2.1
  have hreg : ∀ gamma∈Delta, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F.val)≠0 := by
    intro gamma hg
    exact (Finset.mem_filter.mp hg).2.2
  have hrows := wide_rows_all b d T nu hshape hT0 hT1 hcheck htan hlo hhi
  have hS := hshape.1
  have hRs : b.R≤d.s := hS.2.1
  have hw : 131071≤d.lo := hshape.2.1
  have hl := total_lower b (hiRect d) T hS hT0 hT1
  have hLa : T+d.alpha+d.s≤total b d T := (le_max_left _ _).trans hl
  have hTL : T≤total b d T := by omega
  have hupper : total b d T≤max d.L0 d.L1 := total_upper b (hiRect d) T hS hT0 hT1
  have hDle : cutAt b d nu≤cutAt b d d.lo :=
    clipped_cutoff_antitone d.alpha d.beta 131071 b.B b.R 181245 hlo
  have hDpos : 0<cutAt b d nu := by
    by_cases hn : nu≤d.hi
    · rw [cutAt_affine b d nu hshape hlo hn]; have := hshape.2.2.2.1; omega
    · have htail : d.hi≤tail b := hS.2.2.2.2.2.1
      have hht : tail b≤d.hi := by
        have : min nu (tail b)=tail b := min_eq_right (by omega)
        omega
      have heq : cutAt b d nu=cutAt b d d.hi := by
        unfold cutAt
        unfold tail at htail hht
        rw [min_eq_right (show (b.B+b.R-1)*181245≤nu-131071+1 by omega),
          min_eq_right (show (b.B+b.R-1)*181245≤d.hi-131071+1 by omega)]
      rw [heq, cutAt_affine b d d.hi hshape hshape.2.2.1 le_rfl]; have := hshape.2.2.2.1; omega
  obtain ⟨Q,hQ,hrel,hzero⟩ := exists_profile_helper K
    (D:=cutAt b d nu) (L:=total b d T) (s:=d.s) (nu:=nu) (B:=b.B)
    F.val hF.1 hF.2.2 hbox hTL hRs hcode htotal hslope hB nodes u0 u1 d.alpha d.beta 181245
    (by omega) hDpos le_rfl
    (by simpa only [hcard] using hrows)
    selected Delta (fun gamma hg => hdegree gamma (hsub hg)) hsol hreg
    (fun gamma hg => hagreement gamma (hsub hg))
  have hFY : F.val.degreeOf 1≤b.B := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights he).trans hB
    rw [RCN081.weight_fin4] at hw
    simp [RCN156.residualYSWeights] at hw
    omega
  have hFR : F.val.degreeOf 2≤b.R := MvPolynomial.degreeOf_le_iff.mpr (fun e he => (hbox he).2.1)
  have hFZ : F.val.degreeOf 3≤b.T1 := MvPolynomial.degreeOf_le_iff.mpr
    (fun e he => by have := (hbox he).1; omega)
  have hQY : Q.degreeOf 1≤d.U := MvPolynomial.degreeOf_le_iff.mpr
    (fun e he => by have := (hQ he).2.2; omega)
  have hQR : Q.degreeOf 2≤d.s := MvPolynomial.degreeOf_le_iff.mpr (fun e he => (hQ he).2.1)
  have hQZ : Q.degreeOf 3≤max d.L0 d.L1 := MvPolynomial.degreeOf_le_iff.mpr
    (fun e he => by have := (hQ he).1; omega)
  apply le_trans ?_ hprice
  exact AsymmetricHelper.regularSeeds_count_le_left_intersection
    (pair b d) H Q F hrel 2130706433 hFY hFR hFZ hQY hQR hQZ
    hRpos hBchar hRchar hTchar hgY hgR hgZ
    selected Gamma (Finset.univ : Finset I) nodes u0 u1 nodes.injective.injOn
    (by simpa only [pair,Finset.card_univ] using hcard)
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    hdegree hagreement (by simpa only [pair,UnequalParameters.errors,Nat.reduceSub] using hno) hzero

end
end ProximityPrize.SubmissionLower.RelativeCertificate6815
