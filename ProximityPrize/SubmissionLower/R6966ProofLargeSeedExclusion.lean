import ProximityPrize.SubmissionLower.R6966ProofSpreadCatalogue
import ProximityPrize.SubmissionLower.R6966ProofPadeResidualBank

set_option Elab.async false

-- merged module R6966ProofLargeSeedBudget
section Merged_R6966ProofLargeSeedBudget

namespace Research6966.LargeSeedExclusion
open Finset Module
open K1_14 (FX L Shape Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedClosure SeedField)
open SpreadCatalogue (shape box nodes moment)
open KoalaRect (area rectDebit rectCapacity rectPower rectEvaluated)
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 24000
set_option backward.isDefEq.respectTransparency false

abbrev A := 179769
abbrev N := 4000*A
abbrev last := 2499
abbrev maxK := 1200+5585/19+1
def endBox (k:ℕ) := SpreadInterval.upperBox 5585 1200 N last k
def cost (k:ℕ) :=
  let b:=endBox k
  let t:=Pade.layers 5 17 b 1200 k
  min (SpreadWindow.lex b 1200 19 k * area box)
    (5586*1201*255001*(255001-t*1024))
def costSum:=HelperWindowGrouping.sumCount (fun i=>cost (i+1)) maxK
theorem cost_value : costSum=215909605791421060804 := by decide +kernel

theorem raw_value {h:ℕ} (small:h≤2499) :
    SpreadBucket.raw shape A h=HelperWindowPrefix.volume N 5585 1200 (131071-h) := by
  have eq : (fun q j:ℕ=>N+j-q*(131071-h))=(fun q j:ℕ=>N+j-(131071-h)*q) := by
    funext q j;rw [Nat.mul_comm q]
  change K1_14.shapeSum shape (fun q j:ℕ=>N+j-q*(131071-h))=_
  rw [eq]
  exact (HelperWindowPrefix.volume_eq_shapeSum shape N (131071-h) (by change 1200<131071-h;omega)).symm

private theorem raw_first : SpreadBucket.raw shape A 2330=1931171093984595 :=
  (raw_value (by decide : 2330≤2499)).trans (by decide +kernel)
private theorem raw_last : SpreadBucket.raw shape A 2499=1934288516167340 :=
  (raw_value (by decide : 2499≤2499)).trans (by decide +kernel)

theorem root_cost (h:ℕ) (lo:2330≤h) (hi:h≤2499) :
    rectDebit h nodes moment box+2*h*costSum<area box*SpreadBucket.raw shape A h := by
  let c:=(box 0+box 1+2)*moment+2*costSum
  have charge (t:ℕ) : rectDebit t nodes moment box+2*t*costSum=area box*nodes+t*c := by
    unfold rectDebit c;ring
  have supply (t:ℕ) (l:2330≤t) (r:t≤2499) :
      area box*SpreadBucket.raw shape A t=area box*SpreadBucket.raw shape A 2330+
        (t-2330)*(area box*SpreadBucket.slope shape) := by
    rw [SpreadBucket.raw_affine l (by omega) (by decide)];ring
  have first:rectDebit 2330 nodes moment box+2*2330*costSum<area box*SpreadBucket.raw shape A 2330 := by
    exact ((congrArg (fun v=>rectDebit 2330 nodes moment box+2*2330*v) cost_value).trans_lt
      (by decide +kernel : _<area box*1931171093984595)).trans_eq (congrArg (area box*·) raw_first.symm)
  have last0:rectDebit 2499 nodes moment box+2*2499*costSum<area box*SpreadBucket.raw shape A 2499 := by
    exact ((congrArg (fun v=>rectDebit 2499 nodes moment box+2*2499*v) cost_value).trans_lt
      (by decide +kernel : _<area box*1934288516167340)).trans_eq (congrArg (area box*·) raw_last.symm)
  rw [charge] at first
  rw [charge,supply 2499 (by decide) le_rfl] at last0
  rw [charge,supply h lo hi]
  exact SpreadBucket.affine_pos lo hi first last0

end
end Research6966.LargeSeedExclusion

end Merged_R6966ProofLargeSeedBudget

-- merged module R6966ProofLargeSeedExclusion
section Merged_R6966ProofLargeSeedExclusion

namespace Research6966.LargeSeedExclusion
open Finset Module
open K1_14 (FX L Shape Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedClosure SeedField)
open SpreadCatalogue (shape box nodes moment)
open KoalaRect (area rectDebit rectCapacity rectPower rectEvaluated)
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

private theorem quotient_cost (step W k t wt:ℕ) (v:Fin 2→ℕ) (large:1024≤v 1) :
    PadeResidualBank.cost step W 5585 1200 19 k t 5 wt box v≤
      5586*1201*255001*(255001-t*1024) := by
  unfold PadeResidualBank.cost
  split
  · rename_i room
    have paid:=room.2.2.2 1
    have y:t*v 1≤255000:=paid
    have y0:t*1024≤t*v 1:=Nat.mul_le_mul_left _ large
    have axis0:255000-t*v 0+1≤255001:=by omega
    have axis1:255000-t*v 1+1≤255001-t*1024:=by omega
    have slots:area (fun z=>box z-t*v z)≤255001*(255001-t*1024) :=
      Nat.mul_le_mul axis0 axis1
    have per (j:ℕ) : K1_14_4.gradeWidth step (5585-t*5) (W-t*wt) j-(k-t-j)*19≤5586 := by
      unfold K1_14_4.gradeWidth
      omega
    calc
      _ ≤ ∑ _∈range (1200-t+1),5586*(255001*(255001-t*1024)) := sum_le_sum fun j _=>Nat.mul_le_mul (per j) slots
      _ ≤ 1201*(5586*(255001*(255001-t*1024))) := by
        simp only [sum_const,card_range,nsmul_eq_mul]
        exact Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.sub_le 1200 t))
      _ = _ := by ring
  · exact Nat.zero_le _

theorem excluded {h:ℕ} (lo:2330≤h) (hi:h≤2499) {D:PoleData h} (Crt:CRTLift D)
    (word:K1.I→L) {E:Shape} (fits:TerminalBanks.inside shape E)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents, TerminalBanks.Pass Crt word A E q)
    {f:Equation} (pr:ProjectedProduct parents f) (degree:19≤f.natDegree)
    {G:Pade.Row SeedField} (gp:G.primitive) (grade:G.graphDegree=5)
    (native:PadeNativeQuotient.Native G) (large:1024≤PadeNativeQuotient.axis native.poly 1)
    (ys:Finset SeedClosure) (v:SeedClosure→SeedClosure) (num:ys.card=17)
    (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧
      (G.map (algebraMap SeedField SeedClosure)).err v y=0) : False := by
  classical
  obtain ⟨M⟩:=PadeConcentration.exists_model Crt gp
  let F:=fun W=>finrank FX (rectEvaluated Crt word shape W box)
  have hp:0<h:=by omega
  have hl:h≤131070:=by omega
  have wp:0<131071-h:=by omega
  have basis:K1_14_1.rawWidthCond h shape (N-1):=by
    intro q hq j _
    apply (Nat.mul_le_mul_right (131071-h) hq).trans
    change 5585*(131071-h)≤719076000+j;omega
  have floor:=KoalaRect.rectRankFloor hp hl (hi.trans_lt (by decide : 2499<K1.p)) Crt word shape (N-1) box
    (by decide) (by decide) basis SpreadCatalogue.node_eq.le SpreadCatalogue.pole_cap
  rw [show N-1+1=N by decide] at floor
  have lexical (W:ℕ) (hw:W<N) : F W≤rectCapacity A h shape 19 box (fun _=>0) W := by
    apply KoalaRect.rectCutoff_finrank_le _ _ _ _ _ _ _ _ pr.primitive.ne_zero degree
      (by omega) (by decide : 0<19)
    · intro P hP;exact K1_14_1.evaluated_shape Crt word (KoalaRect.rectEvaluated_le Crt word shape W box hP)
    · intro P hP;exact KoalaRect.rectEvaluated_axis Crt word hP
    · intro P hP hn;exact P0_10_1.leading_bound hp hl Crt word shape W P (KoalaRect.rectEvaluated_le Crt word shape W box hP) hn
    · intro P hP hn
      exact KoalaRect.rectDivides hp Crt word A shape box (by decide) geo (fun q hq=>pass q hq shape fits) pr hw hP hn
    · intro z
      simpa [KoalaRect.rectSlots,area] using
        KoalaRect.rectSlots_antitone box (KoalaRect.axisDegree f) (Nat.zero_le z)
  have live (W:ℕ) (hw:W<N) (low:rectPower A h shape W≤maxK) : F W≤cost (rectPower A h shape W) := by
    let k:=rectPower A h shape W
    let r:=(N-1-W)/(2*h)
    have kr:k=r+1:=Nat.add_comm .. 
    have order:r*(2*h)≤N-1-W:=Nat.div_mul_le_self .. 
    have issued:W+2*h*r<N:=by rw [Nat.mul_comm (2*h) r];omega
    have within:W+2*h*(k-1)<N:=by simpa [kr] using issued
    have rich:2*131071*k<N:=(Nat.mul_le_mul_left _ low).trans_lt (by decide : 2*131071*maxK<N)
    have head:∀ j≤shape.J,K1_14_4.gradeWidth (131071-h) shape.B W j≤endBox k+1-j :=
      SpreadInterval.grade_upper rich (by decide) hi within
    apply le_min ((lexical W hw).trans (SpreadWindow.rect_lex A h 19 k W _ shape box wp (by decide) rfl head))
    let b:=min shape.B ((W+shape.J)/(131071-h))
    have bound:b≤endBox k := by
      have fit:b*(131071-h)≤W+shape.J:=(Nat.le_div_iff_mul_le wp).mp (min_le_right ..)
      have next:=SpreadInterval.cash_bound rich (by decide) hi within fit
      exact le_min (min_le_left ..) ((Nat.le_div_iff_mul_le (by decide : 0<131071-2499)).mpr next)
    have small:r+1<K1.p:=by
      have le:r≤N-1-W:=Nat.div_le_self .. 
      have room:N<K1.p:=by decide
      omega
    have many:2*G.graphDegree-1<ys.card:=by omega
    have rank:=PadeResidualBank.concentration_rank hp hl Crt word box fits small issued geo pass pr degree
      gp M native ys v sheets many (endBox k) bound
    rw [grade,num,←kr] at rank
    exact rank.trans (quotient_cost _ _ _ _ _ _ large)
  have tail (W:ℕ) (hw:W<N) (large:maxK<rectPower A h shape W) : F W=0 :=
    Nat.eq_zero_of_le_zero ((lexical W hw).trans_eq (SpreadWindow.rect_zero A h 19 W shape box wp (by decide) large))
  have sum:=SpreadBucket.sum_by_order (scale:=1) hp F cost
    (fun W hw valid=>by simpa only [one_mul] using live W hw valid) tail
  have cm : (∑ k∈range maxK,cost (k+1))=costSum := (HelperWindowGrouping.sumCount_eq ..).symm
  rw [one_mul,cm] at sum
  change area box*SpreadBucket.raw shape A h≤rectDebit h nodes moment box+∑ W∈range N,F W at floor
  have pay:=root_cost h lo hi
  exact Nat.not_lt_of_ge (floor.trans (Nat.add_le_add_left sum _)) pay

end
end Research6966.LargeSeedExclusion

end Merged_R6966ProofLargeSeedExclusion
