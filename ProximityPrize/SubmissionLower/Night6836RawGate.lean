/- Apache-2.0. Each sparse identity axis is paid by an affine lower bound on
   the first-tail mixed charge and, for the all axis, one ordinary moving term. -/
import ProximityPrize.SubmissionLower.Night6836RawFiber
namespace ProximityPrize.SubmissionLower.Raw6836
open scoped Classical
open RCN095 K6833Residual
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

private theorem first_z (q n : FlagDegree) (hn : 262148 ≤ n.all) :
    q.all * 262148 + q.yz * 262148 ≤ flagMixed ⟨1,0,0⟩ q n := by
  have ha := Nat.mul_le_mul_left q.all hn
  have hb := Nat.mul_le_mul_left q.yz hn
  apply (Nat.add_le_add ha hb).trans
  simp only [flagMixed, Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  omega

private theorem first_yz (q n : FlagDegree)
    (hn : 262148 ≤ n.all) (hm : 131076 ≤ n.yz) (hq : 524289 ≤ q.yz) :
    q.all * 262148 + q.all * 131076 + n.all * 524289 ≤ flagMixed ⟨0,1,0⟩ q n := by
  have ha := Nat.mul_le_mul_left q.all hn
  have hb := Nat.mul_le_mul_left q.all hm
  have hc := Nat.mul_le_mul_left n.all hq
  apply (Nat.add_le_add (Nat.add_le_add ha hb) hc).trans
  simp only [flagMixed, Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.mul_one, Nat.zero_add, Nat.add_zero]
  omega

private theorem first_all (q n : FlagDegree)
    (hn : 262148 ≤ n.all) (hm : 131076 ≤ n.yz) (hq : 524289 ≤ q.yz) :
    q.all * 262148 + q.zOnly * 262148 + q.yz * 262148 +
      131076 * q.all + 524289 * n.yz ≤ flagMixed ⟨0,0,1⟩ q n := by
  have ha := Nat.mul_le_mul_left q.all hn
  have hb := Nat.mul_le_mul_left q.zOnly hn
  have hc := Nat.mul_le_mul_left q.yz hn
  have hd := Nat.mul_le_mul_right q.all hm
  have he := Nat.mul_le_mul_right n.yz hq
  apply (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ha hb) hc) hd) he).trans
  simp only [flagMixed, Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.mul_one, Nat.zero_add, Nat.add_zero]
  omega

private theorem moving_all (q n : FlagDegree) (hn : 393221 ≤ n.all) :
    q.all * 393221 ≤ flagMixed ⟨0,0,1⟩ q n := by
  have ha := Nat.mul_le_mul_left q.all hn
  apply ha.trans
  simp only [flagMixed, Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.mul_one, Nat.zero_add, Nat.add_zero]
  omega

private theorem unit_0 : unit (0 : Fin 3) = ⟨1,0,0⟩ := rfl
private theorem axis_0 (u : FlagDegree) : byAxis u (0 : Fin 3) = u.zOnly := rfl

private theorem unit_1 : unit (1 : Fin 3) = ⟨0,1,0⟩ := rfl
private theorem axis_1 (u : FlagDegree) : byAxis u (1 : Fin 3) = u.yz := rfl

private theorem unit_2 : unit (2 : Fin 3) = ⟨0,0,1⟩ := rfl
private theorem axis_2 (u : FlagDegree) : byAxis u (2 : Fin 3) = u.all := rfl

private theorem gate_shift (a b c:ℕ) :
    rawGate (⟨a+3, a+3+(b+2), a+3+(b+2)+c⟩:Envelope)=true := by
  let f : Envelope := ⟨a+3,a+3+(b+2),a+3+(b+2)+c⟩
  change rawGate f=true
  have d1 : f.total-f.middle=c := by dsimp [f]; omega
  have d2 : f.middle-f.slope=b+2 := by dsimp [f]; omega
  have d3 : f.slope-1=a+2 := by dsimp [f]
  have d4 : f.slope-2=a+1 := by dsimp [f]; omega
  have d5 : f.middle-f.slope-1=b+1 := by dsimp [f]; omega
  have fo : f.slope=a+3 := rfl
  have fst : firstTail f=⟨262144*c,1+262144*(b+2),262144*(a+2)⟩ := by
    change (⟨262144*(f.total-f.middle),1+262144*(f.middle-f.slope),262144*(f.slope-1)⟩:FlagDegree)=_
    rw [d1,d2,d3]
  have nrm : normalTail 0 f=⟨131074*c,131074*b+131076,131074*(a+2)⟩ := by
    change (⟨131074*(f.total-f.middle),131074*(f.middle-f.slope)-131072+0,131074*(f.slope-1)-0⟩:FlagDegree)=_
    rw [d1,d2,d3,show 131074*(b+2)-131072+0=131074*b+131076 by omega,Nat.sub_zero]
  have mv : movingFiber f=⟨c,b+2,a+4⟩ := by
    unfold movingFiber; rw [d1,d2,fo]
  have ord : ordinaryMovingTail f=⟨131074*c,131074*(b+2),131074*a+393221⟩ := by
    change (⟨131074*(f.total-f.middle),131074*(f.middle-f.slope),131074*f.slope-1⟩:FlagDegree)=_
    rw [d1,d2,fo,show 131074*(a+3)-1=131074*a+393221 by omega]
  have iden : identityRaw f=⟨393219+262146*(a+1),786438+524292*(a+1),
    1048586+262146*c+524292*(b+1)+524292*(a+1)⟩ := by unfold identityRaw;rw [d1,d4,d5]
  apply List.all_eq_true.mpr
  intro j _
  apply decide_eq_true
  unfold rawChargeWithCorrections
  simp only [TailCorrections.original,ite_true,iden,fst,nrm,mv,ord]
  have cases_j : j=0 ∨ j=1 ∨ j=2 := by omega
  let q : FlagDegree := ⟨262144*c, 1+262144*(b+2), 262144*(a+2)⟩
  let n : FlagDegree := ⟨131074*c, 131074*b+131076, 131074*(a+2)⟩
  let m : FlagDegree := ⟨c,b+2,a+4⟩
  let o : FlagDegree := ⟨131074*c, 131074*(b+2), 131074*a+393221⟩
  have hn : 262148 ≤ n.all := by dsimp [n]; omega
  have hm : 131076 ≤ n.yz := by dsimp [n]; omega
  have hq : 524289 ≤ q.yz := by dsimp [q]; omega
  have ho : 393221 ≤ o.all := by dsimp [o]; omega
  rcases cases_j with rfl|rfl|rfl
  · rw [unit_0,axis_0]
    change 131073*81106*(393219+262146*(a+1)) ≤ 49968*(flagMixed ⟨1,0,0⟩ q n + 65539*flagMixed ⟨1,0,0⟩ m o)
    have hprice : 131073*81106*(393219+262146*(a+1)) ≤ 49968*(q.all * 262148 + q.yz * 262148) := by
      dsimp [q,n,m]
      omega
    apply hprice.trans
    apply Nat.mul_le_mul_left 49968
    exact (first_z q n hn).trans (Nat.le_add_right _ _)
  · rw [unit_1,axis_1]
    change 131073*81106*(786438+524292*(a+1)) ≤ 49968*(flagMixed ⟨0,1,0⟩ q n + 65539*flagMixed ⟨0,1,0⟩ m o)
    have hprice : 131073*81106*(786438+524292*(a+1)) ≤ 49968*(q.all * 262148 + q.all * 131076 + n.all * 524289) := by
      dsimp [q,n,m]
      omega
    apply hprice.trans
    apply Nat.mul_le_mul_left 49968
    exact (first_yz q n hn hm hq).trans (Nat.le_add_right _ _)
  · rw [unit_2,axis_2]
    change 131073*81106*(1048586+262146*c+524292*(b+1)+524292*(a+1)) ≤ 49968*(flagMixed ⟨0,0,1⟩ q n + 65539*flagMixed ⟨0,0,1⟩ m o)
    have hprice : 131073*81106*(1048586+262146*c+524292*(b+1)+524292*(a+1)) ≤ 49968*(q.all * 262148 + q.zOnly * 262148 + q.yz * 262148 + 131076 * q.all + 524289 * n.yz + 65539 * (m.all * 393221)) := by
      dsimp [q,n,m]
      omega
    apply hprice.trans
    apply Nat.mul_le_mul_left 49968
    exact Nat.add_le_add (first_all q n hn hm hq) (Nat.mul_le_mul_left 65539 (moving_all m o ho))

theorem pad_gate (f:Envelope) : rawGate (f.pad 0)=true := by
  let e := f.pad 0
  have r : 3≤e.slope := by simp [e,Envelope.pad]
  have y : e.slope+2≤e.middle := by simp [e,Envelope.pad]
  have t : e.middle≤e.total := by simp [e,Envelope.pad]
  have shape : e=⟨(e.slope-3)+3,(e.slope-3)+3+(e.middle-e.slope-2+2),
    (e.slope-3)+3+(e.middle-e.slope-2+2)+(e.total-e.middle)⟩ := by
    calc e = ⟨e.slope,e.middle,e.total⟩ := rfl
         _ = _ := by congr 1 <;> omega
  change rawGate e=true
  conv_lhs => rw [shape]
  apply gate_shift
end ProximityPrize.SubmissionLower.Raw6836
#print axioms ProximityPrize.SubmissionLower.Raw6836.pad_gate
