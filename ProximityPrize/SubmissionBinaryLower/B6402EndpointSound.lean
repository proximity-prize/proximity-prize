import ProximityPrize.SubmissionBinaryLower.B6402EndpointBudget

namespace ProximityPrize.SubmissionBinaryLower.B6402EndpointSound
open B6401Params B6401ContactKerD B6402ProfileBudget B6402ProfileCosts B6402OrderProfile
open B6402InterpolationPrice B6402DimensionBudget B6402EndpointBudget
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000

private theorem clear_units (n m2 : ℚ) (hn : 0<n) (hm : 0<m2)
    (a0 a1 a2 a3 e v r f0 f1 f2 f3 inc reg bad c lo vl tilt layers cofactor : ℚ) (partition : r+v=a2)
    (h : (a0/n)*(f0/m2)+(a1/n)*(f1/m2)+(a2/n)*((f2+reg)/m2)+(a3/n)*(f3/m2)+
      (e/n)*(inc/m2)-c*(tilt*layers)+(v/n)*((bad-reg)/m2) < (vl-tilt*lo)*layers+cofactor/(n*m2)) :
    a0*f0+a1*f1+a2*f2+a3*f3+e*inc+r*reg+v*bad <
      (vl+tilt*(c-lo))*(n*m2)*layers+cofactor := by
  have hp := mul_pos (sub_pos.mpr h) (mul_pos hn hm)
  have eq : ((vl-tilt*lo)*layers+cofactor/(n*m2)-
      ((a0/n)*(f0/m2)+(a1/n)*(f1/m2)+(a2/n)*((f2+reg)/m2)+(a3/n)*(f3/m2)+
        (e/n)*(inc/m2)-c*(tilt*layers)+(v/n)*((bad-reg)/m2)))*(n*m2)=
      (vl+tilt*(c-lo))*(n*m2)*layers+cofactor-
        (a0*f0+a1*f1+a2*f2+a3*f3+e*inc+r*reg+v*bad) := by
    rw [←partition]; field_simp [hn.ne',hm.ne']; ring
  exact sub_pos.mp (eq ▸ hp)

theorem paid {I : Type*} [Fintype I] (p : Plan) (k : I → ℕ) (WF H T nr nb : ℕ)
    (hm : 0<p.m) (capEq : T+p.s*H=p.cap) (height : H≤T) (hw : WF≤p.W) (endWF : WF≤p.WFhi)
    (hparts : nr+nb=count k 2) (c : ℚ) (cWF : c*wY≤WF) (clo : p.lo≤c) (chi : c≤p.hi) (proper : p.lo<p.hi)
    (h : lhs p H ((count k 0:ℚ)/N) ((count k 1:ℚ)/N) ((count k 2:ℚ)/N)
      ((count k 3:ℚ)/N) ((totalExcess k:ℚ)/N) c ((nb:ℚ)/N) < rhs p H) :
    (∑ i,fee (primaryOrder p.m p.b (k i)) p.s p.q T H (k i))+
      (nr:ℤ)*(regularCost p.J p.s p.m p.b*(T+p.s*H+1):ℕ)+
      (nb:ℤ)*(exceptionalCost p.s p.b*(T+1+(p.J+16*p.b+2)*H):ℕ) <
      sourceSize wY p.W p.s p.q T-sourceSize wY (p.W-WF) (p.s-1) p.q (T-H) := by
  let gm : ℚ := H*varsKerDExact wY (p.W-p.WFhi) (p.s-1) -
     (p.q:ℚ)*((gMoment wY p.W p.s:ℚ)-gMoment wY (p.W-p.WFhi) (p.s-1))
  have tt : (p.cap:ℚ)-(p.s:ℚ)*H=T := by
    have he : (T:ℚ)+(p.s:ℚ)*H=p.cap := by exact_mod_cast capEq
    linarith only [he]
  have hn : (0:ℚ)<N := by decide
  have hmQ : (0:ℚ)<p.m := by exact_mod_cast hm
  unfold lhs rhs at h
  dsimp only at h
  rw [tt] at h
  have h0 := clear_units (N:ℚ) ((p.m:ℚ)*p.m) hn (mul_pos hmQ hmQ)
    (count k 0) (count k 1) (count k 2) (count k 3) (totalExcess k) nb nr
    (cost p T H 0) (cost p T H 1) (cost p T H 2) (cost p T H 3)
    (excess p T) (regCost p T H) (badCost p T H) c p.lo
    (B6402ProfileSecant.vquotLbQ p.W 1 p.m p.s p.lo) (slope p) ((T:ℚ)+1) gm
    (by exact_mod_cast hparts) (by simpa only [mul_assoc,gm] using h)
  have gap := gap_from_endpoints p.W WF p.m p.s hm hw p.lo p.hi c clo chi proper cWF
  have src := source_budget wY p.W WF p.WFhi p.s p.q T H (by decide) height endWF _ gap
  have f := sum_fees k p.m p.b p.s p.q T H height
  rw [cost_nat _ _ _ _ height,cost_nat _ _ _ _ height,cost_nat _ _ _ _ height,cost_nat _ _ _ _ height] at h0
  have t0 : primaryOrder p.m p.b 0=p.m-p.b := rfl
  have t1 : primaryOrder p.m p.b 1=p.m-p.b := rfl
  have t2 : primaryOrder p.m p.b 2=p.m := rfl
  have t3 : primaryOrder p.m p.b 3=p.m-p.b := rfl
  simp only [t0,t1,t2,t3] at h0
  have hc : excess p T=(inc (p.m-p.b) p.s T:ℚ) := by unfold excess inc; push_cast; rfl
  rw [hc] at h0
  change _ ≤ (sourceSize wY p.W p.s p.q T:ℚ) - _ at src
  unfold secant at src
  dsimp only at src
  unfold B6402EndpointBudget.slope regCost badCost gm at h0
  have fQ := (Int.cast_le (R:=ℚ)).mpr f
  apply (Int.cast_lt (R:=ℚ)).mp
  push_cast at fQ ⊢
  push_cast at h0
  nlinarith only [fQ,h0,src]

#print axioms paid
end ProximityPrize.SubmissionBinaryLower.B6402EndpointSound
