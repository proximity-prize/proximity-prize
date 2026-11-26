import ProximityPrize.SubmissionLower.R6966ProofHelperWindowPrefix
import ProximityPrize.SubmissionLower.R6966ProofHelperWeightCap
import ProximityPrize.SubmissionLower.R6960PrefixReceipt

set_option Elab.async false

namespace Research6966.HelperKnownPrime
open Polynomial Finset
open K1_14 (Jet L triangle shapeSum)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2_2_2_1 (jetDegree seedDegree jetDegree_mul seedDegree_mul)
open Lower6960.PrefixRows (Common)
open HelperAvoidance (debitAt triSlots)
noncomputable section

private theorem slope_le {f:Jet} (nz:f≠0) : f.natDegree≤jetDegree f := by
  have coef : (f.coeff f.natDegree).coeff f.leadingCoeff.natDegree ≠ 0 := by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have bound:=(K1_14_2_2_2_1.jetDegree_le f _).1 le_rfl _ _ coef
  omega

/-- Given a known common prime, pay the buffered source for the product
with any other coprime common prime. Both factors spend their pole weight. -/
theorem not_coprime {h N:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (bank:P1_7.Bank) {G H:Jet}
    (g:Common (evaluated Crt word bank.shape (N-1)) G)
    (other:Common (evaluated Crt word bank.shape (N-1)) H) (cop:IsRelPrime G H)
    (M:HelperPhysicalModel.Model Crt G) {a L0 u Lother:ℕ} (secondWeight:Lother≤131071-h-1)
    (degree:a≤jetDegree G) (wt:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (width:u≤seedDegree G) (seedChar:bank.shape.U<K1.p) (small:bank.shape.B<K1.p)
    (nz:0<N) (wide:bank.shape.B*(131071-h)≤N) (node:P1_7_1.nodeRows bank.shape=bank.nodeRows)
    (pole:P1_7_1.groupedPoleMoment bank.shape.B bank.shape.J≤bank.poleMoment)
    (positive:P1_7.debit h bank+∑ W∈range N,
      debitAt bank.shape h N W (a+1) 2 (L0+Lother) (triSlots bank.shape.U (u+1)) <
      triangle bank.shape.U*shapeSum bank.shape (fun q j=>N+j-q*(131071-h))) : False := by
  classical
  obtain ⟨T⟩:=HelperPhysicalModel.exists_model Crt other.1 other.2.1
  have slope:=slope_le other.1.ne_zero
  have sj:1≤jetDegree H:=other.2.1.trans_le slope
  have us:1≤seedDegree H:=by
    obtain ⟨j,i,seed⟩:=other.2.2.1
    have b:=(K1_14_2_2_2_1.seedDegree_le H _).1 le_rfl j i
    omega
  let w:=131071-h
  have wp:0<w:=by dsimp [w];omega
  have rhs:=HelperWeightCap.weight_lower T other.1.ne_zero w wp
  have wh : w-1≤RawPhysicalDegree.weight w (w-1) T.raw := by
    have prod:(w-1)*jetDegree H+jetDegree H=w*jetDegree H := by
      rw [←Nat.succ_mul,show (w-1).succ=w by omega]
    have ge:=Nat.mul_le_mul_left (w-1) sj
    omega
  have dg : a+1≤jetDegree (G*H) := by rw [jetDegree_mul g.1.ne_zero other.1.ne_zero];omega
  have ds : 2≤(G*H).natDegree := by rw [natDegree_mul g.1.ne_zero other.1.ne_zero];have := g.2.1;have := other.2.1;omega
  have du : u+1≤seedDegree (G*H) := by rw [seedDegree_mul g.1.ne_zero other.1.ne_zero];omega
  have dw : L0+Lother≤RawPhysicalDegree.weight w (w-1) (M.mul T).raw := by
    change _≤RawPhysicalDegree.weight w (w-1) (M.raw*T.raw)
    rw [RawPhysicalDegree.weight_product _ _ M.primitive.ne_zero T.primitive.ne_zero]
    exact Nat.add_le_add wt (secondWeight.trans wh)
  apply HelperAvoidance.triangle_contradiction hp hl Crt word bank (M.mul T)
    (mul_ne_zero g.1.ne_zero other.1.ne_zero) dg ds dw du small nz wide node pole positive
  intro W hw P inside
  apply Lower6960.HelperPrefix.product_power cop
  · apply RectangularHelperShift.common_power hp hw Crt word bank.shape _ g.1 g.2.1 g.2.2.1 seedChar _ P inside
    rw [RectangularHelperShift.all_axes]
    exact g.2.2.2
  · apply RectangularHelperShift.common_power hp hw Crt word bank.shape _ other.1 other.2.1 other.2.2.1 seedChar _ P inside
    rw [RectangularHelperShift.all_axes]
    exact other.2.2.2

theorem unique_from_known {V:Submodule K1_14.FX Jet} {G:Jet} (g:Common V G)
    (pinned:∀ H,Common V H → IsRelPrime G H → False) :
    ∀ N H, Common V N → Common V H → IsRelPrime N H → False := by
  intro N H n h cop
  by_cases dv:G∣N
  · have assoc:=g.1.associated_of_dvd n.1 dv
    exact pinned H h (fun d hd dh => cop (hd.trans assoc.dvd) dh)
  · exact pinned N n (g.1.isRelPrime_iff_not_dvd.mpr dv)

end
end Research6966.HelperKnownPrime
