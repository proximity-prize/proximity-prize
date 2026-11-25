import ProximityPrize.SubmissionLower.Final54W0
import ProximityPrize.SubmissionLower.R6960Low6960WeightedRow
import ProximityPrize.SubmissionLower.R6960Low6960VariableSelect
import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960RetainedCount
import ProximityPrize.SubmissionLower.R6960Low6960RetainedPrimary
import ProximityPrize.SubmissionLower.R6960Low6960Leading
import ProximityPrize.SubmissionLower.R6960Low6960FatCount

-- merged module FarCharge0
section Merged_FarCharge0

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace KoalaFarBridge.FarCharge0
open FadicGate (Entry)

def gate : GateRate := ⟨4886433,26118015,6676780,1966580209,1000000000,10,106,48,4⟩

abbrev boxes := FadicGate.Final54W0.boxes
abbrev plainT := FadicGate.Final54W0.plainT

def adicD : ℕ → List ℕ
  | 1 => [0]
  | 2 => [0, 10]
  | 3 => [0, 7, 10]
  | 4 => [0, 5, 21, 10]
  | 5 => [0, 3, 10, 21, 10]
  | 6 => [0, 2, 13, 32, 21, 10]
  | 7 => [0, 2, 7, 19, 32, 21, 10]
  | 8 => [0, 1, 9, 16, 43, 32, 21, 10]
  | 9 => [0, 1, 5, 19, 30, 43, 32, 21, 10]
  | 10 => [0, 1, 6, 11, 19, 54, 43, 32, 21, 10]
  | 11 => [0, 0, 4, 12, 23, 40, 54, 43, 32, 21, 10]
  | 12 => [0, 0, 4, 13, 26, 27, 64, 54, 43, 32, 21, 10]
  | 13 => [0, 0, 3, 8, 17, 26, 51, 64, 54, 43, 32, 21, 10]
  | 14 => [0, 0, 3, 8, 14, 29, 38, 75, 64, 54, 43, 32, 21, 10]
  | 15 => [0, 0, 2, 9, 16, 32, 29, 62, 75, 64, 54, 43, 32, 21, 10]
  | 16 => [0, 0, 2, 6, 17, 23, 32, 49, 86, 75, 64, 54, 43, 32, 21, 10]
  | 17 => [0, 0, 1, 6, 11, 17, 35, 36, 73, 86, 75, 64, 54, 43, 32, 21, 10]
  | 18 => [0, 0, 2, 6, 11, 19, 39, 35, 60, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 19 => [0, 0, 1, 4, 11, 20, 30, 39, 46, 84, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 20 => [0, 0, 1, 4, 12, 21, 21, 42, 39, 70, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 21 => [0, 0, 0, 5, 7, 15, 21, 45, 42, 57, 94, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 22 => [0, 0, 0, 3, 8, 13, 23, 36, 45, 44, 81, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 23 => [0, 0, 0, 3, 8, 13, 24, 27, 48, 45, 68, 105, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 24 => [0, 0, 0, 3, 8, 14, 26, 24, 51, 48, 55, 92, 129, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 25 => [0, 0, 0, 2, 5, 15, 19, 26, 43, 51, 48, 79, 116, 129, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 26 => [0, 0, 0, 2, 6, 10, 15, 27, 34, 55, 51, 66, 103, 140, 129, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 27 => [0, 0, 0, 2, 6, 9, 16, 28, 27, 58, 55, 52, 90, 127, 140, 129, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 28 => [0, 0, 0, 1, 6, 10, 16, 30, 28, 49, 58, 55, 76, 114, 151, 140, 129, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 29 => [0, 0, 0, 1, 4, 10, 17, 23, 30, 40, 61, 58, 63, 100, 138, 151, 140, 129, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 30 => [0, 0, 0, 1, 4, 10, 18, 17, 31, 31, 64, 61, 58, 87, 124, 162, 151, 140, 129, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 31 => [0, 0, 0, 0, 4, 6, 12, 18, 33, 31, 55, 64, 61, 74, 111, 148, 162, 151, 140, 129, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21, 10]
  | 32 => [0, 0, 0, 0, 4, 7, 11, 18, 34, 33, 47, 67, 64, 61, 98, 135, 172, 162, 151, 140, 129, 118, 108, 97, 86, 75, 64, 54, 43, 32, 21]
  | 33 => [0, 0, 0, 0, 2, 7, 11, 19, 27, 34, 38, 71, 67, 64, 85, 122, 159, 172, 162, 151, 140, 129, 118, 108, 97, 86, 75, 64, 54, 43, 32]
  | 34 => [0, 0, 0, 0, 2, 7, 12, 20, 21, 35, 34, 62, 71, 67, 72, 109, 146, 183, 172, 162, 151, 140, 129, 118, 108, 97, 86, 75, 64, 54, 43]
  | 35 => [0, 0, 0, 0, 3, 7, 12, 21, 20, 37, 35, 53, 74, 71, 67, 96, 133, 170, 183, 172, 162, 151, 140, 129, 118, 108, 97, 86, 75, 64, 54]
  | 36 => [0, 0, 0, 0, 3, 4, 12, 15, 21, 38, 37, 44, 77, 74, 71, 82, 120, 157, 194, 183, 172, 162, 151, 140, 129, 118, 108, 97, 86, 75, 64]
  | 37 => [0, 0, 0, 0, 1, 5, 8, 12, 21, 32, 38, 37, 68, 77, 74, 71, 106, 144, 181, 194, 183, 172, 162, 151, 140, 129, 118, 108, 97, 86, 75]
  | 38 => [0, 0, 0, 0, 1, 5, 8, 13, 22, 25, 40, 38, 59, 80, 77, 74, 93, 130, 168, 205, 194, 183, 172, 162, 151, 140, 129, 118, 108, 97, 86]
  | 39 => [0, 0, 0, 0, 1, 5, 8, 13, 23, 22, 41, 40, 51, 83, 80, 77, 80, 117, 154, 192, 205, 194, 183, 172, 162, 151, 140, 129, 118, 108, 97]
  | 40 => [0, 0, 0, 0, 1, 5, 8, 14, 23, 23, 42, 41, 42, 75, 83, 80, 77, 104, 141, 178, 216, 205, 194, 183, 172, 162, 151, 140, 129, 118, 108]
  | 41 => [0, 0, 0, 0, 0, 3, 8, 14, 18, 23, 36, 42, 41, 66, 87, 83, 80, 91, 128, 165, 202, 216, 205, 194, 183, 172, 162, 151, 140, 129, 118]
  | 42 => [0, 0, 0, 0, 0, 3, 9, 14, 14, 24, 29, 44, 42, 57, 90, 87, 83, 80, 115, 152, 189, 226, 216, 205, 194, 183, 172, 162, 151, 140, 129]
  | 43 => [0, 0, 0, 0, 0, 3, 5, 10, 14, 25, 24, 45, 44, 48, 81, 90, 87, 83, 102, 139, 176, 213, 226, 216, 205, 194, 183, 172, 162, 151, 140]
  | 44 => [0, 0, 0, 0, 0, 3, 5, 9, 15, 26, 25, 47, 45, 44, 72, 93, 90, 87, 88, 126, 163, 200, 237, 226, 216, 205, 194, 183, 172, 162, 151]
  | 45 => [0, 0, 0, 0, 0, 3, 6, 9, 15, 26, 26, 40, 47, 45, 63, 96, 93, 90, 87, 112, 150, 187, 224, 237, 226, 216, 205, 194, 183, 172, 162]
  | 46 => [0, 0, 0, 0, 0, 2, 6, 9, 16, 21, 26, 33, 48, 47, 55, 87, 96, 93, 90, 99, 136, 174, 211, 248, 237, 226, 216, 205, 194, 183, 172]
  | 47 => [0, 0, 0, 0, 0, 2, 6, 10, 16, 16, 27, 27, 49, 48, 47, 79, 99, 96, 93, 90, 123, 160, 198, 235, 248, 237, 226, 216, 205, 194, 183]
  | 48 => [0, 0, 0, 0, 0, 2, 6, 10, 16, 16, 28, 27, 51, 49, 48, 70, 103, 99, 96, 93, 110, 147, 184, 222, 259, 248, 237, 226, 216, 205, 194]
  | 49 => [0, 0, 0, 0, 0, 2, 3, 10, 12, 16, 29, 28, 44, 51, 49, 61, 94, 103, 99, 96, 97, 134, 171, 208, 246, 259, 248, 237, 226, 216, 205]
  | 50 => [0, 0, 0, 0, 0, 2, 3, 6, 10, 17, 29, 29, 38, 52, 51, 52, 85, 106, 103, 99, 96, 121, 158, 195, 232, 270, 259, 248, 237, 226, 216]
  | 51 => [0, 0, 0, 0, 0, 0, 3, 6, 10, 17, 24, 29, 31, 54, 52, 51, 76, 109, 106, 103, 99, 108, 145, 182, 219, 256, 270, 259, 248, 237, 226]
  | 52 => [0, 0, 0, 0, 0, 0, 4, 6, 11, 18, 19, 30, 29, 55, 54, 52, 67, 100, 109, 106, 103, 99, 132, 169, 206, 243, 280, 270, 259, 248, 237]
  | 53 => [0, 0, 0, 0, 0, 0, 4, 6, 11, 18, 18, 31, 30, 48, 55, 54, 59, 91, 112, 109, 106, 103, 118, 156, 193, 230, 267, 280, 270, 259, 248]
  | 54 => [0, 0, 0, 0, 0, 0, 4, 7, 11, 18, 18, 31, 31, 42, 56, 55, 54, 83, 115, 112, 109, 106, 105, 142, 180, 217, 254, 291, 280, 270, 259]
  | 55 => [0, 0, 0, 0, 0, 0, 2, 7, 11, 14, 18, 32, 31, 35, 58, 56, 55, 74, 107, 115, 112, 109, 106, 129, 166, 204, 241, 278, 291, 280, 270]
  | 56 => [0, 0, 0, 0, 0, 0, 2, 7, 11, 11, 19, 27, 32, 31, 59, 58, 56, 65, 98, 119, 115, 112, 109, 116, 153, 190, 228, 265, 302, 291, 280]
  | 57 => [0, 0, 0, 0, 0, 0, 2, 4, 8, 11, 19, 22, 33, 32, 53, 59, 58, 56, 89, 122, 119, 115, 112, 109, 140, 177, 214, 252, 289, 302, 291]
  | 58 => [0, 0, 0, 0, 0, 0, 2, 4, 7, 12, 20, 19, 34, 33, 46, 61, 59, 58, 80, 113, 122, 119, 115, 112, 127, 164, 201, 238, 276, 313, 302]
  | 59 => [0, 0, 0, 0, 0, 0, 2, 4, 7, 12, 20, 20, 34, 34, 39, 62, 61, 59, 71, 104, 125, 122, 119, 115, 114, 151, 188, 225, 262, 300, 313]
  | 60 => [0, 0, 0, 0, 0, 0, 2, 4, 7, 12, 20, 20, 35, 34, 34, 63, 62, 61, 63, 95, 128, 125, 122, 119, 115, 138, 175, 212, 249, 286, 324]
  | 61 => [0, 0, 0, 0, 0, 0, 0, 4, 7, 12, 16, 20, 30, 35, 34, 57, 63, 62, 61, 87, 119, 128, 125, 122, 119, 124, 162, 199, 236, 273, 310]
  | 62 => [0, 0, 0, 0, 0, 0, 0, 4, 7, 13, 12, 21, 24, 36, 35, 50, 65, 63, 62, 78, 111, 131, 128, 125, 122, 119, 148, 186, 223, 260, 297]
  | 63 => [0, 0, 0, 0, 0, 0, 0, 4, 8, 13, 13, 21, 21, 36, 36, 44, 66, 65, 63, 69, 102, 135, 131, 128, 125, 122, 135, 172, 210, 247, 284]
  | 64 => [0, 0, 0, 0, 0, 0, 0, 2, 8, 9, 13, 22, 21, 37, 36, 37, 68, 66, 65, 63, 93, 126, 135, 131, 128, 125, 122, 159, 196, 234, 271]
  | _ => []

def plainD : ℕ → List ℕ
  | 65 => [0, 0, 0, 0, 0, 0, 0, 2, 4, 8, 13, 22, 22, 38, 37, 36, 61, 68, 66, 65, 84, 117, 138, 135, 131, 128, 125, 146, 183, 220, 258, 295, 332, 345, 334]
  | 66 => [0, 0, 0, 0, 0, 0, 0, 2, 4, 8, 13, 22, 22, 33, 38, 37, 54, 69, 68, 66, 75, 108, 141, 138, 135, 131, 128, 133, 170, 207, 244, 282, 319, 356]
  | _ => []

abbrev terminal := FadicGate.Final54W0.terminal
def terminalD : List ℕ := [0, 0, 0, 0, 0, 0, 0, 2, 4, 8, 14, 18, 22, 27, 39, 38, 48, 70, 69, 68, 67, 99, 132, 141, 138, 135, 131, 128, 157, 194, 231, 268, 306, 343, 356]

def fitsAt (r : ℕ) : Bool := rowCheck gate r (boxes r) (adicD r) (plainT r) (plainD r)

private theorem checks : (List.range 66).all (fun i => fitsAt (i+1)) = true := by decide +kernel

theorem fits {r : ℕ} (hr : 0 < r) (hR : r < terminal) : fitsAt r = true := by
  change r < 67 at hR
  have hi : r-1 ∈ List.range 66 := List.mem_range.mpr (by omega)
  have hv := List.all_eq_true.mp checks (r-1) hi
  simpa only [Nat.sub_add_cancel hr] using hv

theorem tail : plainCheck gate terminal (4012,1650,550) terminalD = true := by decide +kernel

#print axioms fits
#print axioms tail
end KoalaFarBridge.FarCharge0

end Merged_FarCharge0

-- merged module R6960Low6960WeightedProof
section Merged_R6960Low6960WeightedProof

set_option Elab.async false
set_option maxRecDepth 18000

namespace Low6960WeightedProof
noncomputable section
open P3 (K)
open K1_13 (Row shape)
open K1_13_6 (GenericField GeoJets)
open FadicGate (Entry varGateDim taperBox slopeBox)
open KoalaFarBridge (FeeBox rowCheck plainCheck)
open Low6960WeightedRate (Envelope Pays first)
open Low6960WeightedRow (rate)
open Low6960SharedPrice (Rate)
open Low6960Prices (Messages SmallFactor ActiveFits ProperCut layerNeed symbolCount)
open MvPolynomial
open scoped BigOperators Polynomial

structure Receipt (p : Envelope) where
  terminal : ℕ
  plain : ℕ → FeeBox
  boxes : ℕ → List Entry
  depthPower : ℕ → List ℕ
  plainPower : ℕ → List ℕ
  endPower : List ℕ
  loss : ℕ
  size : 0 < p.widthLow ∧ 0 < p.indexLow ∧ 0 < p.topLow
  hLoss : loss < layerNeed
  dimensions : ∀ N, ∑ i ∈ Finset.range N,
    max 0 ((symbolCount : ℤ) - varGateDim symbolCount p.widthLow p.widthHigh p.indexLow p.indexHigh
      p.topLow p.taperLow p.taperHigh terminal plain (fun r => (boxes r).length)
      (fun r a => (boxes r).getD a none) (i+1)) ≤ (loss : ℤ)
  prices : ∀ r, 0 < r → r < terminal → rowCheck (rate p) r (boxes r) (depthPower r) (plain r) (plainPower r) = true
  tail : plainCheck (rate p) terminal (4012,1650,550) endPower = true

private def firstReceipt : Receipt first :=
  ⟨FadicGate.Final54W0.terminal, FadicGate.Final54W0.plainT, FadicGate.Final54W0.boxes,
    KoalaFarBridge.FarCharge0.adicD, KoalaFarBridge.FarCharge0.plainD, KoalaFarBridge.FarCharge0.terminalD,
    20130931984877, by decide, by decide, FadicGate.Final54W0.loss,
    fun _ h h' => KoalaFarBridge.FarCharge0.fits h h', KoalaFarBridge.FarCharge0.tail⟩

private theorem cut {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f) (hact : ActiveFits f 171)
    {p : Envelope} (d : Receipt p) (u : Rate) (hu : Pays p (shape f) u) :
    Low6960WeightedTally.Cut (Γ := Γ) (s := s) f u (Low6960WeightedCut.order f (u.split+1)) := by
  intro P hP hs
  obtain ⟨r, hr, v, hv, hsource, hcontact, hrow⟩ := Low6960VariableSelect.select hm P hP f hf.1.ne_zero
    p hu.1 hact d.terminal d.plain d.boxes d.loss d.dimensions d.hLoss
  by_cases ht : d.terminal ≤ r
  · have hV : v ∈ restrictSupport GenericField (slopeBox 4012 1650 550) := by
      exact restrictSupport_mono _ (by simpa only [one_mul] using (FadicGate.source_subset_slopeBox
        (σb := 4012) (σj := 1650) (σt := 550) (r := 1) (by decide))) hsource
    exact Low6960WeightedRow.plain hf hu d.size _ d.endPower ht d.tail hv hV P hs hcontact
  · obtain hplain | ⟨a,B,J,T,c,h,ha,hbox,_,hEq,_,hproper,hC⟩ := hrow.resolve_left ht
    · have hd := (Bool.and_eq_true_iff.mp (d.prices r hr (lt_of_not_ge ht))).2
      have hsub : taperBox (min (d.plain r).1 4012) (min (d.plain r).2.1 1650) (d.plain r).2.2 131312 ⊆
          slopeBox (d.plain r).1 (d.plain r).2.1 (d.plain r).2.2 := by
        intro m hm
        change _ ∧ _ ∧ _
        exact ⟨hm.1.trans (min_le_left _ _), hm.2.1.trans (min_le_left _ _), hm.2.2.1⟩
      have hV := restrictSupport_mono GenericField hsub hplain
      exact Low6960WeightedRow.plain hf hu d.size _ (d.plainPower r) le_rfl hd hv hV P hs hcontact
    · have hd := (Bool.and_eq_true_iff.mp (d.prices r hr (lt_of_not_ge ht))).1
      exact Low6960WeightedRow.adic hf hu (B,J,T) ((d.depthPower r).getD a 0)
        (KoalaFarBridge.depth_at _ hd ha hbox) hEq hproper
        (restrictSupport_mono _ (FadicGate.taperBox_subset_slopeBox _ _ _ _) hC) P hs hcontact

theorem count {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f) (hact : ActiveFits f 171)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (l : ℕ) (hl : 0 < l) (hcut : ProperCut f Γ s l)
    (u : Rate) (hu : Low6960WeightedRate.Allowed (shape f) u) (hn : ¬ Low6960SharedPrice.RateFits (shape f) u) :
    Γ.card ≤ Low6960SharedPrice.price (shape f) l 171 u := by
  have h (p : Envelope) (d : Receipt p) (paid : Pays p (shape f) u) :
      Γ.card ≤ Low6960SharedPrice.price (shape f) l 171 u := by
    apply Low6960WeightedTally.count hm f hf 171 hact hon l hl hcut u paid.2.1 paid.2.2.2.2.1
      (Low6960WeightedCut.order f (u.split+1))
    · intro q hq hmem
      exact (Low6960WeightedCut.order_spec f _ (by omega) q hq hmem).2
    · exact cut hm f hf hact d u paid
  exact h first firstReceipt (hu.resolve_left hn)

#print axioms count
end
end Low6960WeightedProof

end Merged_R6960Low6960WeightedProof

-- merged module R6960Low6960CountCore
section Merged_R6960Low6960CountCore

set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6960.Low
noncomputable section
open Finset Polynomial
open P3 (K)
open K1_13 (Row Shape shape extend OnFactor atJet)
open Low6960Prices (ActiveFits)
open Low6960Allocation (Band Receipt budget GateTable start)
open Low6960Gate (floorShape Gated)
open Low6960AllocTotal (retainedShape)
open Low6960RetainedCut (Bank)
open scoped BigOperators Polynomial

private theorem start_floor (k : Band) (hk : k.val < 10) : floorShape k.val = start k := by
  fin_cases k <;> first | (exfalso; revert hk; decide) | decide +kernel

private theorem allocation (receipts : ∀ k : Band, Receipt k) {G : Shape → ℕ}
    (htab : GateTable (fun k => (receipts k).orders) G) :
    Low6960RetainedCut.Allocation budget 171 G := by
  intro w Γ s hmsg top htop E d
  let f := d.f
  let l := d.orders
  let parts := d.pieces
  have hz : d.zeros = Finset.univ.filter (fun i => l i = 0) := by
    ext i
    simp [d.zero_iff,l]
  have hr : Low6960RetainedCut.sumShape d.zeros (fun i=>shape (f i)) =
      retainedShape (fun i=>shape (f i)) l := by
    rw [hz]
    rfl
  have active (i : Fin d.n) : ActiveFits (f i) 171 := (Final50GeoCover.activeFits_iff _ _).mpr
    ((Finset.single_le_sum (fun j _=>Nat.zero_le (Final50GeoCover.activeDegree (f j)))
      (Finset.mem_univ i)).trans d.active_budget)
  have count : (∑ i,(parts i).card)≤Low6960Allocation.factorCap top := by
    apply Low6960AllocTotal.total receipts G htab top htop d.n (fun i=>shape (f i)) l (fun i=>(parts i).card)
      d.fits d.layers
    · intro i m hm hml k hk
      have hi : 0<l i := hm.trans_le hml
      have hn : i∉d.zeros := fun h=>(Nat.ne_of_gt hi) ((d.zero_iff i).mp h)
      have floor : K1_13.InBox (Low6960Allocation.start k)
          (Low6960RetainedCut.sumShape d.zeros (fun j=>shape (f j))) :=
        hr.symm ▸ Low6960Allocation.admits_floor hk
      exact d.contracted i hn m hm hml 171 (active i) _ floor
    · intro i m u hm hml allowed
      obtain ⟨Q,proper,box,weight,ha,horder⟩ := d.proper i (hm.trans_le hml)
      have cut : ProperCut (f i) (parts i) s m :=
        ⟨Q,proper,box,weight,ha,fun γ hγ e he=>hml.trans (horder γ (d.subset i hγ) e he)⟩
      by_cases stock : Low6960SharedPrice.RateFits (shape (f i)) u
      · exact Low6960SharedCount.proof w (parts i) s (hmsg.mono (d.subset i)) (f i)
          (d.small i) 171 (active i) (d.on_factor i) m hm cut u stock
      · exact Low6960WeightedProof.count (hmsg.mono (d.subset i)) (f i) (d.small i)
          (active i) (d.on_factor i) m hm cut u allowed stock
    · intro i m hm hml k hk hg
      have hi : 0<l i := hm.trans_le hml
      have hn : i∉d.zeros := fun h=>(Nat.ne_of_gt hi) ((d.zero_iff i).mp h)
      have floor : K1_13.InBox (Low6960Allocation.start k)
          (Low6960RetainedCut.sumShape d.zeros (fun j=>shape (f j))) :=
        hr.symm ▸ Low6960Allocation.admits_floor hk
      exact d.gated i hn m hm hml 171 (active i) k.val
        (by rw [start_floor k hg.1]; exact floor) hg
    · intro i eligible
      exact Low6960FatCount.proof w (parts i) s (hmsg.mono (d.subset i)) (f i) (d.small i)
        (d.on_factor i) eligible E (d.fat i)
  have low : Low6960Prices.lowerCap top ≤ budget := by interval_cases top <;> decide +kernel
  change (∑ i,(parts i).card)≤budget-Low6960Prices.lowerCap top at count
  change Low6960Prices.lowerCap top+(∑ i,(parts i).card)≤budget
  omega

/-- Native low count from the finite group certificates, with the actual
analytic pricing theorems supplied by the guarded 69.60 modules. -/
theorem count_with_receipts (receipts : ∀ k : Band, Receipt k) {G : Shape → ℕ}
    (htab : GateTable (fun k => (receipts k).orders) G) (gate : Low6960RetainedCut.GateBank G)
    {cap u del Γ}
    (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179808 M Γ)
    (lo : 1≤M.overhead) (hi : M.overhead≤2359) :
    Γ.card≤265963255385514628 := by
  have messages := Low6960Order.messages_of_family M F hi
  obtain ⟨P,nz,box,active,weight,zero⟩ := Low6960Anchor.anchor_of_family M F hi
  have hw : TrueWeightLE P anchorCutoff := by
    apply (trueWeight_iff P).mpr
    rw [←differentialWeight_eq,←PolynomialDifferential.differentialWeightedDegree]
    exact weight
  obtain ⟨book,E,booked,fat⟩ := fat_of_family M F lo hi
  exact Low6960RetainedCut.count_of_data gate (allocation receipts htab) messages
    (Bank.of_messages messages) (Bank.of_messages_ranked messages)
    P nz box hw active zero (fun _ ht=>Low6960Leading.lower_count ht) book E booked fat

#print axioms count_with_receipts
end
end Lower6960.Low

end Merged_R6960Low6960CountCore
