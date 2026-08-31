import ProximityPrize.SubmissionLower.LocatorFactorAggregate
namespace ProximityPrize.SubmissionLower.LocatorRateCover
open RCN095 LocatorFactorAggregate
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
private abbrev cost (t YS r:ℕ):ℕ :=
  paddedCost 131072 131073 (cap t YS r)
private abbrev limitedCost (t YS r:ℕ):ℕ:=cost t (min YS t) r
private def rawCost (t y r v g s:ℤ):ℤ :=
  (2*(s - 1)*262145+4*(s - 1)*(2*g - s - 1)*17180000256)*t +
  8*(s - 1)*(v - g)*17180000256*y +
  (1+2*(v - s)*262145+4*(g - s)*(2*v - g - s)*17180000256)*r
private theorem cost_normal_form (t YS r:ℕ) (hry:r ≤ YS) (hyt:YS ≤ t) :
    (cost t YS r:ℤ)=rawCost t YS r
      (max t (max YS (max r 2+1)):ℕ)
      (max YS (max r 2+1):ℕ) (max r 2:ℕ):=by
  have hc:=cap_cumulative t YS r hry hyt
  have hps:padS (cap t YS r)=max r 2:=rfl
  have hpy:padY (cap t YS r)=max YS (max r 2+1):=by
    simp only [padY,hc.2.1,hps]
  have hpt:padT (cap t YS r)=max t (max YS (max r 2+1)):=by
    simp only [padT,hc.2.2,hpy]
  have hs1:1 ≤ max r 2:=by have:=le_max_right r 2; omega
  have hsg:max r 2 ≤ max YS (max r 2+1) :=
    (Nat.le_succ _).trans (le_max_right _ _)
  have hgv:max YS (max r 2+1) ≤ max t (max YS (max r 2+1)) :=
    le_max_right _ _
  simp only [cost,paddedCost,paddedTail,hps,hpy,hpt,mixed_expansion,
    hc.1,hc.2.1,hc.2.2]
  push_cast [Nat.cast_sub hgv,Nat.cast_sub hsg,Nat.cast_sub hs1,Nat.cast_max]
  unfold rawCost
  ring
private def smallA (s:ℤ):ℤ :=
  2*(s - 1)*262145+4*(s*s - 1)*17180000256
private def smallB:ℤ:=1+2*262145+4*17180000256
private theorem small_formula (t YS r:ℕ) (hry:r ≤ YS) (hrt:r ≤ t)
    (ht:t ≤ max r 2+1) :
    (limitedCost t YS r:ℤ)=smallA (max r 2:ℕ)*t+smallB*r:=by
  have hmin:min YS t ≤ max r 2+1:=(Nat.min_le_right _ _).trans ht
  rw [cost_normal_form t (min YS t) r (le_min hry hrt) (Nat.min_le_right _ _),
    max_eq_right hmin,max_eq_right ht]
  unfold rawCost smallA smallB
  push_cast
  ring
private theorem small_ratio (t YS r:ℕ) (hry:r ≤ YS) (hrt:r ≤ t)
    (ht:t ≤ max r 2+1) :
    r*limitedCost t YS r ≤ t*cost r r r:=by
  have hbottom:(cost r r r:ℤ)=smallA (max r 2:ℕ)*r+smallB*r:=by
    simpa only [limitedCost,Nat.min_self] using
      small_formula r r r (le_refl _) (le_refl _)
        ((le_max_left _ _).trans (Nat.le_succ _))
  have hrt':(r:ℤ) ≤ t:=by exact_mod_cast hrt
  have htr:0 ≤ (t:ℤ) - r:=sub_nonneg.mpr hrt'
  have hnonneg:0 ≤ ((t:ℤ) - r)*r*smallB:=by
    unfold smallB
    positivity
  have hcross:(r:ℤ)*limitedCost t YS r ≤ (t:ℤ)*cost r r r:=by
    rw [small_formula t YS r hry hrt ht,hbottom]
    nlinarith only [hnonneg]
  exact_mod_cast hcross
private def farSlope (y r g s:ℤ):ℤ :=
  2*(s - 1)*262145+4*(s - 1)*(2*g - s - 1)*17180000256 +
  8*(s - 1)*y*17180000256+2*r*262145 +
  8*r*(g - s)*17180000256
private def farDeficit (y r g s:ℤ):ℤ :=
  8*g*(s - 1)*y*17180000256 +
  r*(2*s*262145+4*(g - s)*(g+s)*17180000256 - 1)
private theorem far_formula (t YS r:ℕ) (hry:r ≤ YS)
    (ht:max YS (max r 2+1) ≤ t) :
    (cost t YS r:ℤ)+farDeficit YS r (max YS (max r 2+1):ℕ) (max r 2:ℕ) =
      farSlope YS r (max YS (max r 2+1):ℕ) (max r 2:ℕ)*t:=by
  rw [cost_normal_form t YS r hry ((le_max_left _ _).trans ht),max_eq_left ht]
  unfold rawCost farDeficit farSlope
  ring
private theorem farDeficit_nonneg (YS r:ℕ) :
    0 ≤ farDeficit YS r (max YS (max r 2+1):ℕ) (max r 2:ℕ):=by
  let s:=max r 2
  let g:=max YS (s+1)
  change 0 ≤ farDeficit YS r g s
  have hsN:2 ≤ s:=le_max_right _ _
  have hsgN:s ≤ g:=(Nat.le_succ _).trans (le_max_right _ _)
  have hs:(2:ℤ) ≤ s:=by exact_mod_cast hsN
  have hsg:(s:ℤ) ≤ g:=by exact_mod_cast hsgN
  have hs1:0 ≤ (s:ℤ) - 1:=by omega
  have hgs:0 ≤ (g:ℤ) - s:=sub_nonneg.mpr hsg
  have hquad:0 ≤ 4*((g:ℤ) - s)*((g:ℤ)+s)*17180000256:=by positivity
  have hcoeff:0 ≤ 2*(s:ℤ)*262145 +
      4*((g:ℤ) - s)*((g:ℤ)+s)*17180000256 - 1:=by
    nlinarith only [hs,hquad]
  unfold farDeficit
  exact add_nonneg (by positivity) (mul_nonneg (Int.natCast_nonneg _) hcoeff)
private theorem far_ratio (x z YS r:ℕ) (hry:r ≤ YS)
    (hx:max YS (max r 2+1) ≤ x) (hxz:x ≤ z) :
    z*cost x YS r ≤ x*cost z YS r:=by
  have fx:=far_formula x YS r hry hx
  have fz:=far_formula z YS r hry (hx.trans hxz)
  have hxz':(x:ℤ) ≤ z:=by exact_mod_cast hxz
  have hd:=farDeficit_nonneg YS r
  have hprod:0 ≤ ((z:ℤ) - x) *
      farDeficit YS r (max YS (max r 2+1):ℕ) (max r 2:ℕ) :=
    mul_nonneg (sub_nonneg.mpr hxz') hd
  have fx':=congrArg (fun v:ℤ => (z:ℤ)*v) fx
  have fz':=congrArg (fun v:ℤ => (x:ℤ)*v) fz
  have hcross:(z:ℤ)*cost x YS r ≤ (x:ℤ)*cost z YS r:=by
    nlinarith only [fx',fz',hprod]
  exact_mod_cast hcross
private def diagA (s r:ℤ):ℤ:=4*(2*s - 2+r)*17180000256
private def diagB (s r:ℤ):ℤ :=
  2*(s - 1+r)*262145 - 4*(s*s - 1+2*r*s)*17180000256
private def diagC (s r:ℤ):ℤ:=r*(1 - 2*s*262145+4*s*s*17180000256)
private theorem diagonal_formula (t r:ℕ) (ht:max r 2+1 ≤ t) :
    (cost t t r:ℤ)=diagA (max r 2:ℕ) r*t*t +
      diagB (max r 2:ℕ) r*t+diagC (max r 2:ℕ) r:=by
  have hrt:r ≤ t:=((le_max_left _ _).trans (Nat.le_succ _)).trans ht
  rw [cost_normal_form t t r hrt (le_refl _),max_eq_left ht,max_self]
  unfold rawCost diagA diagB diagC
  ring
private theorem diagonal_ratio (x z r:ℕ) (hx:max r 2+1 ≤ x) (hxz:x ≤ z) :
    z*cost x x r ≤ x*cost z z r:=by
  let s:=max r 2
  have hsN:2 ≤ s:=le_max_right _ _
  have hsxN:s ≤ x:=(Nat.le_succ _).trans hx
  have hszN:s ≤ z:=hsxN.trans hxz
  have hs:(2:ℤ) ≤ s:=by exact_mod_cast hsN
  have hs1:0 ≤ (s:ℤ) - 1:=by omega
  have hprod_le:(s:ℤ)*s ≤ (x:ℤ)*z:=by
    exact_mod_cast Nat.mul_le_mul hsxN hszN
  have hprod:0 ≤ (x:ℤ)*z - (s:ℤ)*s:=sub_nonneg.mpr hprod_le
  have hsmall:0 ≤ 2*(s:ℤ)*262145 - 1:=by omega
  have hgap:0 ≤ diagA s r*x*z - diagC s r:=by
    calc
      _=4*17180000256 *
          (2*((s:ℤ) - 1)*x*z+(r:ℤ)*((x:ℤ)*z - (s:ℤ)*s)) +
          (r:ℤ)*(2*(s:ℤ)*262145 - 1):=by
        unfold diagA diagC
        ring
      _ ≥ 0:=by positivity
  have hxz':(x:ℤ) ≤ z:=by exact_mod_cast hxz
  have hnonneg:0 ≤ ((z:ℤ) - x)*(diagA s r*x*z - diagC s r) :=
    mul_nonneg (sub_nonneg.mpr hxz') hgap
  have hcross:(z:ℤ)*cost x x r ≤ (x:ℤ)*cost z z r:=by
    rw [diagonal_formula x r hx,diagonal_formula z r (hx.trans hxz)]
    change (z:ℤ)*(diagA s r*x*x+diagB s r*x+diagC s r) ≤
      (x:ℤ)*(diagA s r*z*z+diagB s r*z+diagC s r)
    nlinarith only [hnonneg]
  exact_mod_cast hcross
private theorem ratio_trans {a b c A B C:ℕ} (hb:0<b)
    (h₁:b*A ≤ a*B) (h₂:c*B ≤ b*C):c*A ≤ a*C:=by
  have hscaled:b*(c*A) ≤ b*(a*C):=by
    calc
      _=c*(b*A):=by ring
      _ ≤ c*(a*B):=Nat.mul_le_mul_left c h₁
      _=a*(c*B):=by ring
      _ ≤ a*(b*C):=Nat.mul_le_mul_left a h₂
      _=_:=by ring
  exact Nat.le_of_mul_le_mul_left hscaled hb
private theorem above_ratio (x z YS r:ℕ) (hry:r ≤ YS)
    (hx:max r 2+1 ≤ x) (hxz:x ≤ z) :
    z*limitedCost x YS r ≤ x*limitedCost z YS r:=by
  by_cases hyx:YS ≤ x
  · have hyz:=hyx.trans hxz
    simpa only [limitedCost,Nat.min_eq_left hyx,Nat.min_eq_left hyz] using
      far_ratio x z YS r hry (max_le hyx hx) hxz
  · have hxy:x ≤ YS:=by omega
    by_cases hzy:z ≤ YS
    · simpa only [limitedCost,Nat.min_eq_right hxy,Nat.min_eq_right hzy] using
        diagonal_ratio x z r hx hxz
    · have hyz:YS ≤ z:=by omega
      have hypos:0<YS:=by have:=le_max_right r 2; omega
      have h₁:=diagonal_ratio x YS r hx hxy
      have h₂:=far_ratio YS z YS r hry (max_le (le_refl _) (hx.trans hxy)) hyz
      simpa only [limitedCost,Nat.min_eq_right hxy,Nat.min_eq_left hyz] using
        ratio_trans hypos h₁ h₂
theorem global_rate_of_endpoints (p:FlagDegree) (T YS r bound:ℕ)
    (hr:0<r) (hpr:p.all=r) (hy:middle p ≤ YS)
    (hYS:YS ≤ T) (ht:total p ≤ T)
    (hsmall:T*paddedCost 131072 131073 (cap r r r) ≤ bound*r)
    (htop:paddedCost 131072 131073 (cap T YS r) ≤ bound) :
    T*paddedCost 131072 131073 p ≤ bound*total p:=by
  have hrt:r ≤ total p:=by simpa only [hpr] using all_le_total p
  have hry:r ≤ YS:=by simpa only [hpr] using (all_le_middle p).trans hy
  have hc:paddedCost 131072 131073 p ≤ limitedCost (total p) YS r :=
    paddedCost_mono 131072 131073
      (below_cap_of_bounds p (total p) (min YS (total p)) r (le_min hry hrt)
        (Nat.min_le_right _ _) hpr.le (le_min hy (middle_le_total p)) (le_refl _))
  have hcanon:T*limitedCost (total p) YS r ≤ bound*total p:=by
    by_cases hpad:total p ≤ max r 2+1
    · have h₁:=small_ratio (total p) YS r hry hrt hpad
      have h₂:T*cost r r r ≤ r*bound:=by simpa only [Nat.mul_comm] using hsmall
      calc
        _ ≤ total p*bound:=ratio_trans hr h₁ h₂
        _=_:=by ring
    · have hstart:max r 2+1 ≤ total p:=by omega
      have hratio:=above_ratio (total p) T YS r hry hstart ht
      have hbound:limitedCost T YS r ≤ bound:=by
        simpa only [limitedCost,Nat.min_eq_left hYS] using htop
      calc
        _ ≤ total p*limitedCost T YS r:=hratio
        _ ≤ total p*bound:=Nat.mul_le_mul_left (total p) hbound
        _=_:=by ring
  exact (Nat.mul_le_mul_left T hc).trans hcanon
end ProximityPrize.SubmissionLower.LocatorRateCover
