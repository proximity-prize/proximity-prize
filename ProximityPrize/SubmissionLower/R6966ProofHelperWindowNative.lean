import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate
import ProximityPrize.SubmissionLower.R6966ProofNativeWitnessBank

set_option Elab.async false

namespace Research6966.HelperWindowNative
open Polynomial Finset
open HelperWindowCertificate
open HelperWindowIntervals (box axis)
open HelperAvoidance (debitAt rectSlots)
open K1_14 (Equation L Shape)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (SeedField Surface Parent)
open PadeNativeQuotient (Native)
open scoped Polynomial
set_option maxHeartbeats 900000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false


private theorem top_pos {b : Witness} (checked : Verified b) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) : 0 < b.top h := by
  by_cases nz : b.B = 0
  · have res := checked.caps.2.2.2.2
    have zero : b.reserve = 0 := by omega
    change 0 < b.m*agreement-2*h*b.reserve
    rw [zero, Nat.mul_zero, Nat.sub_zero]
    exact Nat.mul_pos checked.caps.2.2.2.1 (by decide)
  · have narrow : 0 < 131071-h := by have last : lastHeight = 2499 := rfl; omega
    exact (Nat.mul_pos (Nat.pos_of_ne_zero nz) narrow).trans_le
      (weight_room b lo hi checked.caps.2.2.2.2 checked.width_at_first)

def orient (narrow : Fin 2) (f : Fin 2 → ℕ) (z : Fin 2) : ℕ :=
  if z = narrow then f 1 else f 0

private theorem area_orient (narrow : Fin 2) (U : Fin 2 → ℕ) :
    KoalaRect.area (orient narrow U) = KoalaRect.area U := by
  fin_cases narrow
  · change (U 1+1)*(U 0+1) = (U 0+1)*(U 1+1)
    exact Nat.mul_comm _ _
  · rfl

private theorem sum_orient (narrow : Fin 2) (U : Fin 2 → ℕ) :
    orient narrow U 0+orient narrow U 1 = U 0+U 1 := by
  fin_cases narrow
  · change U 1+U 0=U 0+U 1
    exact Nat.add_comm _ _
  · rfl

private theorem slots_orient (narrow : Fin 2) (U d : Fin 2 → ℕ) :
    rectSlots (orient narrow U) (orient narrow d) = rectSlots U d := by
  funext k
  have fit : (∀ z,k*orient narrow d z ≤ orient narrow U z) ↔ (∀ z,k*d z ≤ U z) := by
    fin_cases narrow
    · constructor <;> intro h z <;> fin_cases z
      · exact h 1
      · exact h 0
      · exact h 1
      · exact h 0
    · constructor <;> intro h z <;> fin_cases z
      · exact h 0
      · exact h 1
      · exact h 0
      · exact h 1
  unfold rectSlots
  by_cases room : ∀ z,k*d z ≤ U z
  · rw [ite_eq_left (fit.mpr room),ite_eq_left room]
    have eq : (fun z => orient narrow U z-k*orient narrow d z) =
        orient narrow (fun z => U z-k*d z) := by
      funext z
      by_cases same : z=narrow <;> simp only [orient,same,ite_true,ite_false]
    rw [eq,area_orient]
  · rw [ite_eq_right (fun h => room (fit.mp h)),ite_eq_right room]

private theorem rectangle_orient {b : Witness} (checked : Verified b) (rect : b.rect = true) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) (narrow : Fin 2) :
    KoalaRect.rectDebit h b.nodes b.pole (orient narrow (box seedCap b.v))+
        (∑ W ∈ range (b.top h), debitAt b.shape h (b.top h) W b.degree 1 b.weight
          (rectSlots (orient narrow (box seedCap b.v)) (orient narrow (axis b.lower)))) <
      KoalaRect.area (orient narrow (box seedCap b.v))*
        K1_14.shapeSum b.shape (fun q j => b.top h+j-q*(131071-h)) := by
  rw [KoalaRect.rectDebit,area_orient,slots_orient,sum_orient]
  exact checked.rectangle rect lo hi

/-- A catalogue bank bounds the projected product on the actual native
graph. The buffered avoiding row exists in the stated CRT source and
retains the required order at every terminal parent. -/
theorem projected_bounds {b : Witness} (checked : Verified b) {h : ℕ} {D : PoleData h}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) (Crt : CRTLift D) (word : K1.I → L)
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive) (phys : HelperPhysicalModel.Model Crt N.poly)
    (degree : G.graphDegree = b.degree) (seeded : K1_14_2.UsesSeed N.poly)
    {parents : Finset Surface} {H : Equation} (chosen : NativeWitnessBank.witnessed N parents H)
    {E : Shape} (fits : TerminalBanks.inside b.shape E) (width : Fin 2 → ℕ) (narrow : Fin 2)
    (axisHigh : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z)
    (axisLow : if b.rect then b.lower ≤ PadeNativeQuotient.axis N.poly narrow else b.lower ≤ seedDegree N.poly)
    (geo : ∀ q ∈ parents, Parent q) (pass : ∀ q ∈ parents, TerminalBanks.Pass Crt word agreement E q) :
    (b.reserve+1)*H.natDegree ≤ b.shape.B+(G.graphDegree-1)*b.shape.J ∧
      ∀ z, (b.reserve+1)*KoalaRect.axisDegree H z ≤
        (if b.rect then orient narrow (box seedCap b.v) z else b.v)+b.shape.J*width z := by
  have hp : 0 < h := (show 0 < firstHeight by decide).trans_le lo
  have hl : h ≤ 131070 := hi.trans (by decide)
  have wide : b.shape.B*(131071-h) ≤ b.top h := weight_room b lo hi checked.caps.2.2.2.2 checked.width_at_first
  have nt := top_pos checked lo hi
  have cut := cutoff_order b nt
  have char : b.shape.U < K1.p := by
    apply lt_of_le_of_lt _ (show seedCap < K1.p by decide)
    change (if b.rect then seedCap else b.v) ≤ seedCap
    split
    · exact le_rfl
    · exact checked.caps.2.2.1
  have charB : b.shape.B < K1.p := checked.caps.1.trans_lt (by decide)
  have reserve : b.reserve+1 < K1.p := by
    have cap := checked.caps.2.2.2.2.trans checked.caps.1
    exact (show b.reserve+1 ≤ 5586 by omega).trans_lt (by decide)
  have available := HelperWeightCap.weight_lower phys N.primitive.ne_zero (131071-h) (by omega)
  rw [HelperWeightCap.native_degree N gp, degree, NativeGraphMarks.slope_degree N gp] at available
  have spent := Nat.mul_le_mul_right b.degree (Nat.sub_le_sub_left hi 131071)
  rw [Nat.mul_comm (131071-lastHeight) b.degree] at spent
  have lCap : b.weight ≤ RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw := by
    change b.degree*(131071-lastHeight)-1 ≤ _
    omega
  cases tag : b.rect
  · have positive := checked.triangle tag lo hi
    rw [← degree] at positive
    have low : b.lower ≤ seedDegree N.poly := by simpa only [tag,Bool.false_eq_true,ite_false] using axisLow
    have seedU : b.bank.shape.U = b.v := by
      simp only [Witness.bank,Witness.shape,tag,Bool.false_eq_true,ite_false]
    have shapeEq : b.bank.shape = b.shape := rfl
    have result := NativeWitnessBank.triangular hp hl Crt word N gp phys chosen b.bank width seeded char charB
      lCap low axisHigh wide nt checked.node_eq checked.pole_ge (by rw [seedU, shapeEq]; exact positive)
      cut fits reserve geo pass
    simpa only [tag,Bool.false_eq_true,ite_false,Witness.bank,Witness.shape] using result
  · have positive := rectangle_orient checked tag lo hi narrow
    rw [← degree] at positive
    have low (z : Fin 2) : orient narrow (axis b.lower) z ≤ PadeNativeQuotient.axis N.poly z := by
      by_cases same : z = narrow
      · subst z
        rw [orient,ite_eq_left rfl]
        change b.lower ≤ PadeNativeQuotient.axis N.poly narrow
        simpa only [tag,ite_true] using axisLow
      · rw [orient,ite_eq_right same]
        change 0 ≤ PadeNativeQuotient.axis N.poly z
        exact Nat.zero_le _
    have boxSum : orient narrow (box seedCap b.v) 0+orient narrow (box seedCap b.v) 1 ≤ b.shape.U := by
      rw [sum_orient]
      change seedCap-b.v+b.v ≤ (if b.rect then seedCap else b.v)
      rw [tag, ite_eq_left rfl, Nat.sub_add_cancel checked.caps.2.2.1]
    have result := NativeWitnessBank.rectangle hp hl Crt word N gp phys chosen (orient narrow (box seedCap b.v))
      (orient narrow (axis b.lower)) width seeded char charB lCap low axisHigh boxSum wide nt checked.node_eq.le checked.pole_ge
      positive cut fits reserve geo pass
    simpa only [tag,ite_true] using result

end Research6966.HelperWindowNative
