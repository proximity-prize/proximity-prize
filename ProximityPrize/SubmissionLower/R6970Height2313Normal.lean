import ProximityPrize.SubmissionLower.R6970Height2311NormalPacket
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0829
set_option autoImplicit true
namespace Research6969.TransitionPacket.NormalCatalogue
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14 (Equation)
open K1_14_3 (ProjectedProduct SeedField)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Research6966
open _root_.Research6969.TransitionPacket (Pair)
open _root_.Lower6960.Far6969RescueGeometry (Model Family word)
open scoped Classical
set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

theorem small_bill (i : Fin 18) :
    ∀ j k : Fin 22, j.val+k.val ≤ 21 →
      JointLedger.Pass (mainBook i) (rescueBook i) (JointRouted.seedWeight 133384 (seed i))
      (JointRouted.ordWeight 133384 1) 274779381266040419 j.val k.val := by
  fin_cases i
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill1
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill2
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill3
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill4
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill5
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill6
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill7
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill8
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill9
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill10
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill11
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill12
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill13
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill14
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill15
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill16
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill17
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))
  · intro j k h
    exact Research6970.Height2313.Research6969.ExtendedJointBills.bill18
      ⟨j.val,j.isLt.trans_le (by decide)⟩ ⟨k.val,k.isLt.trans_le (by decide)⟩ (h.trans (by decide))

theorem reduce {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet}
    (i : Fin 18) (P : Pair F Crt G (mainBook i) (rescueBook i))
    (lo : 2308 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (prime : Prime G) (slope : G.natDegree = 1) (degree : 2 ≤ jetDegree G)
    (caps : RowCaps G (Prefix6969Rescue.graphShape 2 (seed i))) :
    Γ.card≤274779381266040419 ∨ ∃ (f : Equation) (H : Pade.Row SeedField),
      ProjectedProduct (P.main∪P.rescue) f ∧ 22≤f.natDegree ∧ H.primitive ∧
      H.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band f.natDegree) ∧
      Pade.Controls (H.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (P.main∪P.rescue))
        (TransitionClassification.content (TransitionClassification.band f.natDegree)) := by
  have equal : jetDegree G = 2 := Nat.le_antisymm
    ((K1_14_2_2_2_1.jetDegree_le G 2).mpr fun j k hn => (caps j k hn).1) degree
  have width (j k : ℕ) : ((G.coeff j).coeff k).totalDegree ≤ seed i := by
    by_cases zero : (G.coeff j).coeff k = 0
    · simp [zero]
    · exact (caps j k zero).2.2
  have phys : 131071+M.overhead ≤ (133384 : ℤ) := by omega
  have msmall : 41*(mainBook i).seedMass < K1.p := by fin_cases i <;> decide +kernel
  have rsmall : 41*(rescueBook i).seedMass < K1.p := by fin_cases i <;> decide +kernel
  have table : ∀ j k : Fin 22, j.val+k.val ≤ 21 →
      JointLedger.Pass (mainBook i) (rescueBook i) (JointRouted.seedWeight 133384 (seed i))
      (JointRouted.ordWeight 133384 (jetDegree G-1)) 274779381266040419 j.val k.val := by
    simpa only [equal, show 2-1=1 by decide] using small_bill i
  exact Research6970.Height2313.Research6969.TransitionPacket.reduce_singleton P lo (hi.trans (by decide)) prime slope degree (Nat.succ_pos i.val) width
    (by decide : 0<133384) phys (by decide) (by decide) msmall rsmall table



end
end Research6969.TransitionPacket.NormalCatalogue
end Z6969Source0829

end Research6970.Height2313
