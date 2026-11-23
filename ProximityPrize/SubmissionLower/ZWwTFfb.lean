import ProximityPrize.SubmissionLower.ZZZM2Ya
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 50000
set_option maxRecDepth 256
namespace P6_6_8_3
open aR (Shape aO ceilDiv)
open yi (bF)
open nZ (Jg)
open P6_6
open private bhj from ProximityPrize.SubmissionLower.CH


open private chartFits chartLe join_fits join_le mixed_le from ProximityPrize.SubmissionLower.Zsr715c
open private L den upperNum from ProximityPrize.SubmissionLower.Zsx1Iye
open private top_pay linear_pay from ProximityPrize.SubmissionLower.ZMoN2Pa
open private ceiling_mono positiveRates zero_le from ProximityPrize.SubmissionLower.ZZZM2Ya
private theorem spend_rate (r :Shape) (b j t z :ℕ) (ht:3*r.t≤ r.j) :
    r.iU.b*b+r.j*j+r.t*t+r.b*z ≤
      (b+z)*r.b+(b+j+ceilDiv t 3)*r.j+0*r.t:= by
  have hb:b*r.iU.b≤b*(r.b+r.j) :=
    Nat.mul_le_mul_left _ (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
  have ht:=top_pay (m:=t) ht
  calc
    _=b*r.iU.b+j*r.j+t*r.t+z*r.b:= by ac_rfl
    _≤b*(r.b+r.j)+j*r.j+ceilDiv t 3*r.j+z*r.b :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right hb _) ht) _
    _ = _:= by
      simp only [Nat.add_mul,Nat.mul_add,Nat.zero_mul,Nat.add_zero]
      ac_rfl
private theorem pos_bound {p r A:Shape} (hs :JetShape r) (ht:0< r.t)
    (hp:aO p m6) (hpc:bF p) (hac:bF A) (hr :aO r.iU A)
    (hmode :r.t=1↔A.t=1) :smallFee p r≤dot (positiveRates A) r := by
  let a :=r.iU
  let P:=m6
  have ha :bF a :=Jg r hs.2.1
  have hP:bF P:=⟨by decide,by decide⟩
  have hchart (l:ℕ) :=chartLe l hr hmode
  have mix {q s Q S:Shape} (hq:aO q Q) (hz :aO s S)
      (hqc:bF q) (hzc:bF s) (hQc:bF Q) (hSc:bF S) :=
    mixed_le a ha hp hq hz hpc hqc hzc hP hQc hSc
  have hpair :pair32 false a a p≤pair32 false A a P :=
    mix (hchart (L+1)) (hchart (L+2))
      (chartFits _ _) (chartFits _ _) (chartFits _ _) (chartFits _ _)
  have hcurve {w W:Shape} (h:aO w W) (hw:bF w) (hW:bF W) :
      curve32 a a p w≤ curve32 A a P W:= by
    unfold curve32
    exact add_le_add (mul_le_mul_of_nonneg_left
      (mix h (hchart L) hw (chartFits _ _) hW (chartFits _ _)) (by positivity))
      (mul_le_mul_of_nonneg_left (mix h hr hw ha hW hac) (by positivity))
  have hE :0≤ curve32 A a P A:= by
    unfold curve32
    rw [← bhj a P A (weightedChart L A) hP hac (chartFits _ _),
      ← bhj a P A A hP hac hac]
    positivity
  have hm:min (pair32 false a a p) (pair32 true a a p)≤pair32 false A a P :=
    (min_le_left _ _).trans hpair
  have hA:=hcurve hr ha hac
  have hW:=hcurve (join_le hr hp) (join_fits ha hpc) (join_fits hac hP)
  have hM:=mix hr hr ha ha hac hac
  have hb:r.b≤a.b:=le_max_left _ _
  simp only [smallFee,ite_eq_right (Nat.ne_of_gt ht)]
  have hnum :
      (mV:ℤ)*min (pair32 false a a p) (pair32 true a a p) +
        32*((P6.t:ℤ)+2*mV)*a.b*p.b*(weightedChart (L+1) a).b +
        (2+2*(r.t:ℤ))*curve32 a a p a+curve32 a a p (joinBody a p) +
        mV*wP a p a a+64*(mV:ℤ)*gZ*r.b*p.b ≤
      upperNum A a := by
    have hpb: (p.b:ℤ)≤P.b:=Int.ofNat_le.mpr hp.1
    have hhb: ((weightedChart (L+1) a).b:ℤ)≤(weightedChart (L+1) A).b :=
      Int.ofNat_le.mpr (hchart (L+1)).1
    have hAb: (r.b:ℤ)≤a.b:=Int.ofNat_le.mpr hb
    have hAt: (r.t:ℤ)≤A.t:=Int.ofNat_le.mpr hr.2.2
    have hcoef :2+2*(r.t:ℤ)≤2+2*(A.t:ℤ) := by omega
    have hterm :=(mul_le_mul_of_nonneg_left hA
      (show 0≤2+2*(r.t:ℤ) by positivity)).trans
      (mul_le_mul_of_nonneg_right hcoef hE)
    have hg:=Int.natCast_nonneg mV
    let c:ℤ:=32*((P6.t:ℤ)+2*mV)*a.b
    have hc₀:0≤ c:= by
      change 0≤32*((P6.t:ℤ)+2*mV)*a.b
      exact mul_nonneg (mul_nonneg (by decide)
        (add_nonneg (Int.natCast_nonneg _) (mul_nonneg (by decide) hg))) (Int.natCast_nonneg _)
    have hc:c*p.b*(weightedChart (L+1) a).b ≤
        c*P.b*(weightedChart (L+1) A).b :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpb hc₀) hhb
        (Int.natCast_nonneg _) (mul_nonneg hc₀ (Int.natCast_nonneg _))
    let f :ℤ:=64*(mV:ℤ)*gZ
    have hf₀:0≤f :=mul_nonneg (mul_nonneg (by decide) hg) (Int.natCast_nonneg _)
    have hf :f*r.b*p.b≤f*a.b*P.b :=
      mul_le_mul (mul_le_mul_of_nonneg_left hAb hf₀) hpb
        (Int.natCast_nonneg _) (mul_nonneg hf₀ (Int.natCast_nonneg _))
    exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hm hg) hc) hterm) hW)
      (mul_le_mul_of_nonneg_left hM hg)) hf
  have hn:=(ceiling_mono (d:=den) (Int.toNat_le_toNat hnum)).trans (linear_pay A a)
  have hz :=zero_le hs ht (hb.trans hr.1) hr.2.1
  exact (Nat.add_le_add hn (Nat.mul_le_mul_left r.b hz)).trans
    (spend_rate r _ _ _ _ hs.2.1)
end P6_6_8_3
