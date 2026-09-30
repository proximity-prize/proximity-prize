import ProximityPrize.SubmissionLower.RelativeFastRecordCover6815
import ProximityPrize.SubmissionLower.RelativeWideCover6815
namespace ProximityPrize.SubmissionLower.RelativeCertificate6815
open RelativeCertificate6814
open RCN100 ClosedRank RelativeBounded6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000

def tanMarginPolynomial (b : Band) (d : Rectangle) (T L : ℕ) : Cubic :=
  let p := rankPolynomial ((d.alpha : ℤ)+d.beta) d.beta L d.s
  let q := rankPolynomial ((d.alpha : ℤ)+d.beta) ((d.beta : ℤ)+1) ((L : ℤ)-T) ((d.s : ℤ)-b.R)
  let c := 12*((countSlope (cutoff b d) d.s+
        (tanK b d : ℤ)*(countSlope (cutoff b d+1) d.s-countSlope (cutoff b d) d.s)-
        countSlope (tanE b d) (d.s-b.R))*L+
      countSlope (tanE b d) (d.s-b.R)*T+
      countIntercept (cutoff b d) d.s+
        (tanK b d : ℤ)*(countIntercept (cutoff b d+1) d.s-countIntercept (cutoff b d) d.s)-
      countIntercept (tanE b d) (d.s-b.R))
  ⟨c-262144*(p.c0-q.c0),-262144*(p.c1-q.c1),-262144*(p.c2-q.c2),-262144*(p.c3-q.c3)⟩

theorem tanMarginPolynomial_eval (b : Band) (d : Rectangle) (T L mu : ℕ)
    (hmu : 1≤mu) (hR : b.R≤d.s)
    (hmmu : mu≤d.alpha-d.beta*(mu-1))
    (hs : 2*d.s≤d.alpha-d.beta*(mu-1))
    (hs' : 2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu) :
    (tanMarginPolynomial b d T L).eval mu=
      tanMarginA (cutoff b d) (tanK b d) (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu*L+
      tanMarginB (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu*T+
      tanMarginC (cutoff b d) (tanK b d) (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu := by
  let m := d.alpha-d.beta*(mu-1)
  have hmcast : (m : ℤ)=(d.alpha : ℤ)+d.beta-(d.beta : ℤ)*mu := by
    have hle : d.beta*(mu-1)≤d.alpha := by omega
    have hh : (m : ℤ)+(d.beta : ℤ)*(mu-1 : ℕ)=d.alpha := by
      exact_mod_cast Nat.sub_add_cancel hle
    rw [Nat.cast_sub hmu,Nat.cast_one] at hh
    nlinarith only [hh]
  have hinner : (d.alpha : ℤ)+d.beta-((d.beta : ℤ)+1)*mu=(m-mu : ℕ) := by
    rw [Nat.cast_sub hmmu]
    nlinarith only [hmcast]
  have hk : min d.s (m/2)=d.s := min_eq_left (by omega)
  have hk' : min (d.s-b.R) ((m-mu)/2)=d.s-b.R := min_eq_left (by omega)
  have ho := rankAffine_eq m d.s L
  have hi := rankAffine_eq (m-mu) (d.s-b.R) ((L : ℤ)-T)
  simp only [rankAffine,hk,hk'] at ho hi
  have he : (tanMarginPolynomial b d T L).eval mu=
      12*((countSlope (cutoff b d) d.s+
          (tanK b d : ℤ)*(countSlope (cutoff b d+1) d.s-countSlope (cutoff b d) d.s)-
          countSlope (tanE b d) (d.s-b.R))*L+
        countSlope (tanE b d) (d.s-b.R)*T+
        countIntercept (cutoff b d) d.s+
          (tanK b d : ℤ)*(countIntercept (cutoff b d+1) d.s-countIntercept (cutoff b d) d.s)-
        countIntercept (tanE b d) (d.s-b.R))-
      262144*((rankPolynomial ((d.alpha : ℤ)+d.beta) d.beta L d.s).eval mu-
        (rankPolynomial ((d.alpha : ℤ)+d.beta) ((d.beta : ℤ)+1) ((L : ℤ)-T) ((d.s : ℤ)-b.R)).eval mu) := by
    unfold tanMarginPolynomial Cubic.eval
    ring
  rw [he,rankPolynomial_eval,rankPolynomial_eval,←hmcast,hinner,←Nat.cast_sub hR,ho,hi]
  unfold tanMarginA tanMarginB tanMarginC
  dsimp only [m] at *
  ring

def tanCorners (b : Band) (d : Rectangle) (a z : ℕ) : Prop :=
  (tanMarginPolynomial b d b.T0 d.L0).Check a z ∧
  (tanMarginPolynomial b d b.T0 (d.L0+1)).Check a z ∧
  (tanMarginPolynomial b d b.T1 d.L1).Check a z ∧
  (tanMarginPolynomial b d b.T1 (d.L1+1)).Check a z

instance tanCornersDecidable (b : Band) (d : Rectangle) (a z : ℕ) : Decidable (tanCorners b d a z) := by
  unfold tanCorners
  infer_instance

theorem tanRowGood_of_corners (b : Band) (d : Rectangle) (a z mu : ℕ)
    (hR : b.R≤d.s) (hc : tanCorners b d a z) (ha : a≤mu) (hz : mu≤z) (hmu : 1≤mu)
    (hm : mu≤d.alpha-d.beta*(mu-1))
    (hs : 2*d.s≤d.alpha-d.beta*(mu-1))
    (hs' : 2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu) : tanRowGood b d mu := by
  have h0 := Cubic.check_positive _ _ _ mu hc.1 ha hz
  have h0' := Cubic.check_positive _ _ _ mu hc.2.1 ha hz
  have h1 := Cubic.check_positive _ _ _ mu hc.2.2.1 ha hz
  have h1' := Cubic.check_positive _ _ _ mu hc.2.2.2 ha hz
  rw [tanMarginPolynomial_eval b d b.T0 d.L0 mu hmu hR hm hs hs'] at h0
  rw [tanMarginPolynomial_eval b d b.T0 (d.L0+1) mu hmu hR hm hs hs'] at h0'
  rw [tanMarginPolynomial_eval b d b.T1 d.L1 mu hmu hR hm hs hs'] at h1
  rw [tanMarginPolynomial_eval b d b.T1 (d.L1+1) mu hmu hR hm hs hs'] at h1'
  simp only [Nat.cast_add,Nat.cast_one] at h0' h1'
  unfold tanRowGood
  constructor
  · exact max_lt h0 (by nlinarith only [h0'])
  · exact max_lt h1 (by nlinarith only [h1'])

def checkTanRange (b : Band) (d : Rectangle) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => checkTanRange b d start n && decide (tanRowGood b d (start+n))

theorem checkTanRange_spec (b : Band) (d : Rectangle) (start n : ℕ)
    (hc : checkTanRange b d start n=true) (mu : ℕ) (h0 : start≤mu) (h1 : mu<start+n) :
    tanRowGood b d mu := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [checkTanRange,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases hmu : mu<start+n
    · exact ih hc.1 hmu
    · have he : mu=start+n := by omega
      simpa only [he] using hc.2

def TanFastRows (b : Band) (d : Rectangle) (w : FastWitness) : Prop :=
  1≤w.firstExact ∧ w.firstExact≤w.lastExact ∧ w.lastExact≤w.normalEnd ∧ w.normalEnd≤b.B+b.R ∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1) ∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1) ∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd ∧
  tanCorners b d 1 (w.firstExact-1) ∧ tanCorners b d (w.lastExact+1) w.normalEnd ∧
  tanRowGood b d 0 ∧ checkTanRange b d w.firstExact (w.lastExact+1-w.firstExact)=true ∧
  checkTanRange b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true

instance tanFastRowsDecidable (b : Band) (d : Rectangle) (w : FastWitness) :
    Decidable (TanFastRows b d w) := by
  unfold TanFastRows
  infer_instance

theorem checkTanRows_of_all (b : Band) (d : Rectangle) (n : ℕ)
    (h : ∀ mu<n, tanRowGood b d mu) : checkTanRows b d n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [checkTanRows,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨ih (fun mu hm => h mu (by omega)),h n (by omega)⟩

theorem tanFastRows_sound (b : Band) (d : Rectangle) (w : FastWitness)
    (hR : b.R≤d.s) (h : TanFastRows b d w) : checkTanRows b d (b.B+b.R+1)=true := by
  rcases h with ⟨hfirst,hlast,hend,hmax,hlevel,hs,hs',hleft,hright,hzero,hcenter,htail⟩
  apply checkTanRows_of_all
  intro mu hmu
  by_cases hz : mu=0
  · simpa only [hz] using hzero
  have hmu1 : 1≤mu := by omega
  by_cases hn : mu≤w.normalEnd
  · have hmono : d.alpha-d.beta*(w.normalEnd-1)≤d.alpha-d.beta*(mu-1) :=
      Nat.sub_le_sub_left (Nat.mul_le_mul_left d.beta (Nat.sub_le_sub_right hn 1)) d.alpha
    have hm : mu≤d.alpha-d.beta*(mu-1) := by omega
    have hms : 2*d.s≤d.alpha-d.beta*(mu-1) := by omega
    have hms' : 2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu := by omega
    by_cases hbefore : mu<w.firstExact
    · exact tanRowGood_of_corners b d 1 (w.firstExact-1) mu hR hleft hmu1 (by omega) hmu1 hm hms hms'
    by_cases hwithin : mu≤w.lastExact
    · exact checkTanRange_spec _ _ _ _ hcenter mu (by omega) (by omega)
    · exact tanRowGood_of_corners b d (w.lastExact+1) w.normalEnd mu hR hright (by omega) hn hmu1 hm hms hms'
  · exact checkTanRange_spec _ _ _ _ htail mu (by omega) (by omega)

def WideHeader (b : Band) (d : Rectangle) : Prop :=
  WideShape b d ∧ 1≤b.R ∧ b.B<2130706433 ∧ b.R<2130706433 ∧ b.T1<2130706433 ∧
  cutAt b d d.lo≤131071*(d.U+1) ∧
  (pair b d).mixedCost.y<2130706433 ∧ (pair b d).mixedCost.r<2130706433 ∧
  (pair b d).mixedCost.z<2130706433 ∧ AsymmetricHelper.leftRegularCountCap (pair b d)≤b.count

structure WideRow where
  rect : Rectangle
  hiW : FastWitness
  tanW : FastWitness

def WideFastValid (b : Band) (x : WideRow) : Prop :=
  WideHeader b x.rect ∧ FastRows b (hiRect x.rect) x.hiW ∧ TanFastRows b x.rect x.tanW

instance wideFastValidDecidable (b : Band) (x : WideRow) : Decidable (WideFastValid b x) := by
  unfold WideFastValid WideHeader
  infer_instance

theorem wideFastValid_sound (b : Band) (x : WideRow) (h : WideFastValid b x) : WideValid b x.rect := by
  rcases h with ⟨⟨hs,hR,hB,hRc,hTc,hU,hgY,hgR,hgZ,hprice⟩,hhi,htan⟩
  have hRs : b.R≤x.rect.s := hs.1.2.1
  exact ⟨hs,hR,hB,hRc,hTc,hU,hgY,hgR,hgZ,hprice,
    fastRows_sound b (hiRect x.rect) x.hiW hRs hhi, tanFastRows_sound b x.rect x.tanW hRs htan⟩

def wideFastCheckList (b : Band) : List WideRow → Bool
  | [] => true
  | d::ds => decide (WideFastValid b d) && wideFastCheckList b ds

theorem wideFastCheckList_append_of (b : Band) (xs ys : List WideRow)
    (hx : wideFastCheckList b xs=true) (hy : wideFastCheckList b ys=true) :
    wideFastCheckList b (xs++ys)=true := by
  induction xs with
  | nil => simpa using hy
  | cons x xs ih =>
    simp only [wideFastCheckList,Bool.and_eq_true,decide_eq_true_eq] at hx
    simp only [List.cons_append,wideFastCheckList,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hx.1,ih hx.2⟩

theorem wideFastCheckList_sound (b : Band) (xs : List WideRow)
    (hc : wideFastCheckList b xs=true) : wideCheckList b (xs.map WideRow.rect)=true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [wideFastCheckList,Bool.and_eq_true,decide_eq_true_eq] at hc
    simp only [List.map_cons,wideCheckList,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨wideFastValid_sound b x hc.1,ih hc.2⟩

end
end ProximityPrize.SubmissionLower.RelativeCertificate6815
