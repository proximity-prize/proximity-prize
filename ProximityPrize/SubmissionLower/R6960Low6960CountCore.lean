import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdB6
import ProximityPrize.SubmissionLower.Final54W0
import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
import ProximityPrize.SubmissionLower.R6960LineEulerPolynomial
import ProximityPrize.SubmissionLower.R6960Low6960FatCount
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960Low6960Gates
import ProximityPrize.SubmissionLower.R6960Low6960Leading
import ProximityPrize.SubmissionLower.R6960Low6960Rectangle
import ProximityPrize.SubmissionLower.R6960Low6960RetainedAssembly
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0
import ProximityPrize.SubmissionLower.R6960Low6960WeightedRow
import ProximityPrize.SubmissionLower.R6966ProofPadeResidualBank

section Merged6967_R6960Low6960CountCore
set_option Elab.async false








set_option Elab.async false

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

private theorem cut {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f) (hact : ActiveFits f 169)
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

theorem count {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f) (hact : ActiveFits f 169)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (l : ℕ) (hl : 0 < l) (hcut : ProperCut f Γ s l)
    (u : Rate) (hu : Low6960WeightedRate.Allowed (shape f) u) (hn : ¬ Low6960SharedPrice.RateFits (shape f) u) :
    Γ.card ≤ Low6960SharedPrice.price (shape f) l 169 u := by
  have h (p : Envelope) (d : Receipt p) (paid : Pays p (shape f) u) :
      Γ.card ≤ Low6960SharedPrice.price (shape f) l 169 u := by
    apply Low6960WeightedTally.count hm f hf 169 hact hon l hl hcut u paid.2.1 paid.2.2.2.2.1
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

private theorem start_floor (k : Band) (hk : k.val < 6) : floorShape k.val = start k := by
  fin_cases k <;> first | (exfalso; revert hk; decide) | decide +kernel

private theorem allocation (receipts : ∀ k : Band, Receipt k) {G : Shape → ℕ}
    (htab : GateTable (fun k => (receipts k).orders) G) :
    Low6960RetainedCut.Allocation budget 169 G := by
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
  have active (i : Fin d.n) : ActiveFits (f i) 169 := (Final50GeoCover.activeFits_iff _ _).mpr
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
      exact d.contracted i hn m hm hml 169 (active i) _ floor
    · intro i m u hm hml allowed
      obtain ⟨Q,proper,box,weight,ha,horder⟩ := d.proper i (hm.trans_le hml)
      have cut : ProperCut (f i) (parts i) s m :=
        ⟨Q,proper,box,weight,ha,fun γ hγ e he=>hml.trans (horder γ (d.subset i hγ) e he)⟩
      by_cases stock : Low6960SharedPrice.RateFits (shape (f i)) u
      · exact Low6960SharedCount.proof w (parts i) s (hmsg.mono (d.subset i)) (f i)
          (d.small i) 169 (active i) (d.on_factor i) m hm cut u stock
      · exact Low6960WeightedProof.count (hmsg.mono (d.subset i)) (f i) (d.small i)
          (active i) (d.on_factor i) m hm cut u allowed stock
    · intro i m hm hml k hk hg
      have hi : 0<l i := hm.trans_le hml
      have hn : i∉d.zeros := fun h=>(Nat.ne_of_gt hi) ((d.zero_iff i).mp h)
      have floor : K1_13.InBox (Low6960Allocation.start k)
          (Low6960RetainedCut.sumShape d.zeros (fun j=>shape (f j))) :=
        hr.symm ▸ Low6960Allocation.admits_floor hk
      exact d.gated i hn m hm hml 169 (active i) k.val
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
    (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179818 M Γ)
    (lo : 1≤M.overhead) (hi : M.overhead≤2358) :
    Γ.card≤266228295297719504 := by
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

end Merged6967_R6960Low6960CountCore

section Merged6967_R6960MarkedEvaluationLedger
set_option Elab.async false




set_option Elab.async false

-- merged module R6960Front6960PoleChart
section Merged_R6960Front6960PoleChart

set_option Elab.async false
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.FrontPoleChart
noncomputable section
open Polynomial
open P1 (K I node twist p)
open K1_14 (L liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open RescueGeometry (Model Family)
open scoped Polynomial

private def AdjacentChart {u del} (M : Model u del) {Γ} (F : Family M Γ)
    (H : (Polynomial L)) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ
private theorem adjacent_chart {u del} (M : Model u del) {Γ} (F : Family M Γ) :
    ∃ H, AdjacentChart M F H := by
  let φ := algebraMap K L
  let σ := frobenius L p
  have hsmall : M.overhead.toNat ≤ (liftPoly M.E).natDegree := by
    rw [liftPoly, natDegree_map]
    unfold P1.ModelAt.overhead
    omega
  obtain ⟨H, hm, hdeg, hd⟩ := K1_14.trim _ _ hsmall
  have hd' : H.map σ ∣ liftPoly (M.E.map twist) := by
    change H.map σ ∣ liftPoly (M.E.map K1.twist)
    rw [K1_14.twist_lift]
    exact Polynomial.map_dvd σ hd
  have hcop : IsCoprime H (H.map σ) := by
    have ha := M.adjacent_coprime.map (Polynomial.mapRingHom φ)
    exact (ha.of_isCoprime_of_dvd_left hd).of_isCoprime_of_dvd_right hd'
  have hunit : IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H :=
    (((M.offset_reduced.mul_left M.coprime_factor.symm).mul_left M.first_amplitude_unit).map
      (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
  refine ⟨H, hm, hdeg, hd, hm.map σ, (natDegree_map σ).trans hdeg, hd', hcop, ?_,
    hunit, hunit.map (Polynomial.mapRingHom σ), ?_⟩
  · intro i
    have h₀ : H.eval (φ (node i)) ≠ 0 := by
      intro hz
      have hb : (liftPoly M.E).eval (φ (node i)) = 0 := by
        obtain ⟨J, hj⟩ := hd
        simp [hj, eval_mul, hz]
      exact M.E_nodes i (φ.injective (by simpa [liftPoly, φ] using hb))
    have hx : σ (φ (node i)) = φ (node i) := by
      change φ (node i) ^ p = _
      rw [← map_pow, FrobeniusLocator.Native.native_domain_fixed]
    refine ⟨h₀, ?_⟩
    rw [← hx, eval_map_apply]
    exact (map_ne_zero σ).mpr h₀
  · intro γ hγ
    let z := M.label γ
    let B := F.mark γ hγ
    have ha : IsCoprime (liftPoly (M.factor * M.amplitude γ)) H :=
      ((M.coprime_factor.symm.mul_left B.pole_unit).map
        (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
    have hid : M.E ∣ (M.factor * M.amplitude γ) * F.scalar γ + C z * M.Q :=
      ⟨M.decoder B.bad, by rw [← B.identity]; ring⟩
    have hres : H ∣ liftPoly (M.factor * M.amplitude γ) * liftPoly (F.scalar γ) +
        C (φ z) * liftPoly M.Q := by
      simpa only [liftPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        using hd.trans (Polynomial.map_dvd φ hid)
    have hfix : (liftPoly (F.scalar γ)).map σ = liftPoly (F.scalar γ) := by
      rw [← K1_14.twist_lift]
      exact congrArg liftPoly B.scalar_fixed
    refine ⟨ha, ha.map (Polynomial.mapRingHom σ), hres, ?_⟩
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hfix,
      σ, frobenius_def] using (Polynomial.map_dvd σ hres)
private theorem chart_poles {u del} (M : Model u del) {Γ} (F : Family M Γ)
    (H : (Polynomial L)) (hH : AdjacentChart M F H) :
    ∃ D : PoleData M.overhead.toNat,
      K1_14_1.poleProduct D = H * H.map (frobenius L p) ∧
      (∀ i k, (D.block i).eval (nodeL k) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  let σ := frobenius L p
  rcases hH with ⟨hm, hd, _, hm', hd', _, hcop, hnode, hdet, hdet', hmarks⟩
  let A := liftPoly (M.factor * M.A₀)
  let B := liftPoly (M.factor * M.A₁)
  let Q := liftPoly M.Q
  have hdet0 : IsCoprime (Q * A) H := by
    simpa [Q, A, liftPoly, mul_assoc] using hdet
  have hdet1 : IsCoprime (Q.map σ * A.map σ) (H.map σ) := by
    simpa [Q, A, liftPoly, mul_assoc, σ, Polynomial.map_mul] using hdet'
  let D : PoleData M.overhead.toNat :=
    ⟨![H, H.map σ], ![Q, Q.map σ], ![A, A.map σ], ![B, B.map σ],
      Fin.forall_fin_two.mpr ⟨hm, hm'⟩,
      Fin.forall_fin_two.mpr ⟨hd, hd'⟩,
      hcop, Fin.forall_fin_two.mpr ⟨hdet0, hdet1⟩⟩
  refine ⟨D, rfl, ?_, ?_⟩
  · intro i k
    fin_cases i
    · exact (hnode k).1
    · exact (hnode k).2
  · intro γ hγ i
    let z := algebraMap K L (M.label γ)
    have hz : liftPoly (M.factor * M.amplitude γ) = A + (@Polynomial.C L _) z * B := by
      simp [A, B, z, P1.ModelAt.amplitude, liftPoly, mul_add, mul_left_comm]
    obtain ⟨h₀, h₁, hr₀, hr₁⟩ := hmarks γ hγ
    fin_cases i
    · change IsCoprime (A + (@Polynomial.C L _) z * B) H ∧
        H ∣ (A + (@Polynomial.C L _) z * B) * liftPoly (F.scalar γ) + (@Polynomial.C L _) z * Q
      rw [← hz]
      exact ⟨h₀, hr₀⟩
    · have hσ : (liftPoly (M.factor * M.amplitude γ)).map σ =
          A.map σ + (@Polynomial.C L _) (z^p) * B.map σ := by
        rw [hz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) (H.map σ) ∧
        H.map σ ∣ (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) * liftPoly (F.scalar γ) +
          (@Polynomial.C L _) (z^p) * Q.map σ
      rw [← hσ]
      exact ⟨h₁, hr₁⟩
/-- The actual 69.60 family supplies both coprime pole blocks and all residues
for the same CRT lift used by the high interpolation banks. -/
theorem of_family {u del} (M : Model u del) {Γ} (F : Family M Γ) :
    ∃ D : PoleData M.overhead.toNat, Nonempty (CRTLift D) ∧
      (∀ j i, (D.block j).eval (nodeL i) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  obtain ⟨H, chart⟩ := adjacent_chart M F
  obtain ⟨D, _, regular, residues⟩ := chart_poles M F H chart
  exact ⟨D, P0_10_1.crt_lift D, regular, residues⟩

#print axioms of_family
end
end Lower6960.FrontPoleChart

end Merged_R6960Front6960PoleChart

-- merged module R6960Front6960HighCount
section Merged_R6960Front6960HighCount

set_option Elab.async false
namespace Lower6960
open Polynomial
open K1 (K)
open K1_14 (Equation atMark)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open KoalaRect (axisDegree)
open RescueGeometry (Model Family)
open scoped Polynomial

abbrev retainedCap : ℕ := 30359056712357701

/-- A bound for the actual family of simple marked sheets left by the high prefix. -/
def RetainedCount : Prop :=
  ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (_lo : 2359 ≤ M.overhead.toNat) (_hi : M.overhead.toNat ≤ 33579)
    {D : PoleData M.overhead.toNat} (_Crt : CRTLift D)
    (_regular : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (_residues : ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (T : Finset K) (f : Equation), T ⊆ Γ →
      3 ≤ f.natDegree → f.natDegree < 48 → axisDegree f 0 + axisDegree f 1 ≤ 2400 →
      (∀ j : Fin 2, axisDegree f j < (TerminalReceipts.witness f.natDegree).order 1) →
      (∀ γ ∈ T, TerminalMarked.simpleSheet f (M.label γ) (F.scalar γ) ∧
        ∃ q : Equation, Irreducible q ∧ q ∣ f ∧ 3 ≤ q.natDegree ∧
          atMark q (M.label γ) (F.scalar γ) = 0) →
      T.card ≤ retainedCap

theorem high_count_of_retained (retained : RetainedCount)
    {u deleted} (M : Model u deleted) {Γ} (F : Family M Γ)
    (lo : 2359 ≤ M.overhead) (hi : M.overhead ≤ 33579) :
    Γ.card ≤ 266228295297719504 := by
  have hlo : 2359 ≤ M.overhead.toNat := by omega
  have hhi : M.overhead.toNat ≤ 33579 := by omega
  obtain ⟨D, ⟨Crt⟩, regular, residues⟩ := FrontPoleChart.of_family M F
  rcases TerminalMarked.good_remainder F Crt hlo hhi regular residues with
    paid | ⟨T, f, sub, paid, degree, small, axes, grade, marks⟩
  · exact paid.trans (by decide +kernel)
  · exact (paid.trans (Nat.add_le_add_left
      (retained F hlo hhi Crt regular residues T f sub degree small axes grade marks) _)).trans_eq
      (by decide +kernel)

#print axioms high_count_of_retained
end Lower6960

end Merged_R6960Front6960HighCount

-- merged module R6960RetainedCompressionFactors
section Merged_R6960RetainedCompressionFactors
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1700000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K p)
open K1_14 (L FX Equation graphEval atX liftPoly)
open CurvatureSquares (Ordinate zView zView_inj ordEval)
open KoalaRect (axisDegree)
open RescueGeometry (Model Family)
open RetainedShortening (Word)
open scoped Polynomial
structure MarkedFiber (P : Ordinate) (z : L) (S : (Polynomial L)) : Prop where
  full : (specialize P z).natDegree=P.natDegree
  separable : ((specialize P z).map incl).Separable
  root : (specialize P z).eval S=0
abbrev scalar {u deleted} (M : Model u deleted) (γ : K) : L := algebraMap K L (M.label γ)
theorem scalar_injective {u deleted} (M : Model u deleted) : Function.Injective (scalar M) :=
  (algebraMap K L).injective.comp (RescueGeometry.label_injective M)
theorem marked_projection {u deleted} {M : Model u deleted} {Γ T : Finset K}
    (F : Family M Γ) (f : Equation) (sub : T⊆Γ)
    (degree : 3≤f.natDegree) (axes : axisDegree f 0+axisDegree f 1≤2400)
    (hi : M.overhead.toNat≤33579)
    (marks : ∀ γ∈T, TerminalMarked.simpleSheet f (M.label γ) (F.scalar γ)) :
    Word 179818 164650 M.word F.scalar T ∧
    ∃ P : Ordinate, P≠0 ∧ P.natDegree=f.natDegree ∧
      (zView P).natDegree≤axisDegree f 0+p*axisDegree f 1 ∧
      ∀ γ∈T, MarkedFiber P (scalar M γ) (liftPoly (F.scalar γ)) := by
  have nz : f≠0 := by intro h; simp [h] at degree
  have small : axisDegree f 0<p := by change _<2130706433; omega
  obtain ⟨D,P,dn,pn,deg,cap,called⟩ := integral_project f nz small
  refine ⟨⟨F.distinct.mono sub,?_,?_⟩,P,pn,deg,cap,?_⟩
  · intro γ hγ
    rcases (F.mark γ (sub hγ)).scalar_degree with z | bound
    · simp [z]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      have hh : M.overhead≤(33579 : ℤ) := by omega
      omega
  · intro γ hγ
    let mark := F.mark γ (sub hγ)
    exact ⟨mark.bad.support,mark.bad.agreement,mark.scalar_hits⟩
  · intro γ hγ
    have eq := called (M.label γ)
    have dnon : incl D≠0 := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) FX)).mpr dn
    have native := marks γ hγ
    change (f.map (graphEval (M.label γ))).natDegree=f.natDegree ∧
      (f.map (graphEval (M.label γ))).Separable ∧ _ at native
    obtain ⟨full,sep,H,Q,fac,_⟩ := native
    have root : (f.map (graphEval (M.label γ))).eval (atX (F.scalar γ))=0 := by
      rw [fac,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul]
    have smap : ((specialize P (scalar M γ)).map incl).natDegree =
        (specialize P (scalar M γ)).natDegree :=
      natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial L) FX) _
    refine ⟨?_,?_,?_⟩
    · rw [← smap,eq,natDegree_C_mul dnon,full,deg]
    · rw [eq]
      exact sep.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr dnon))
    · apply (IsFractionRing.injective (Polynomial L) FX)
      rw [← Polynomial.eval_map_apply,eq, map_zero,eval_mul,eval_C]
      exact mul_eq_zero.mpr (Or.inr root)
theorem split_fibre {P Q : Ordinate} {z : L} {S : (Polynomial L)}
    (pn : P≠0) (qn : Q≠0) (H : MarkedFiber (P*Q) z S) :
    MarkedFiber P z S ∨ MarkedFiber Q z S := by
  have eq : specialize (P*Q) z=specialize P z*specialize Q z := by simp [specialize]
  have pair : ((specialize P z).map incl*(specialize Q z).map incl).Separable := by
    simpa only [eq,Polynomial.map_mul] using H.separable
  have left := pair.of_mul_left
  have right := pair.of_mul_right
  have pz : specialize P z≠0 := fun h => left.ne_zero (by rw [h,Polynomial.map_zero])
  have qz : specialize Q z≠0 := fun h => right.ne_zero (by rw [h,Polynomial.map_zero])
  have sum := H.full
  rw [eq,natDegree_mul pn qn,natDegree_mul pz qz] at sum
  have pl : (specialize P z).natDegree≤P.natDegree := natDegree_map_le
  have ql : (specialize Q z).natDegree≤Q.natDegree := natDegree_map_le
  have zr := H.root
  rw [eq,eval_mul,mul_eq_zero] at zr
  exact zr.imp (fun root => ⟨by omega,left,root⟩) (fun root => ⟨by omega,right,root⟩)
theorem aggregate {ι : Type*} (P : Ordinate) (T : Finset ι) (z : ι → L) (S : ι → Polynomial L)
    (rate additive : ℕ) (nz : P≠0)
    (marks : ∀ γ∈T, MarkedFiber P (z γ) (S γ))
    (price : ∀ Q : Ordinate, Irreducible Q → Q∣P → ∀ U⊆T,
      (∀ γ∈U, MarkedFiber Q (z γ) (S γ)) →
      U.card≤rate*(zView Q).natDegree+additive*Q.natDegree) :
    T.card≤rate*(zView P).natDegree+additive*P.natDegree := by
  classical
  induction P using WfDvdMonoid.induction_on_irreducible generalizing T with
  | zero => exact (nz rfl).elim
  | unit P unit =>
    have empty : T=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      have units : IsUnit (specialize P (z γ)) :=
        unit.map (mapRingHom (mapRingHom (evalRingHom (z γ))))
      exact (units.map (evalRingHom (S γ))).ne_zero (marks γ hγ).root
    simp [empty]
  | mul Q P qn irr ih =>
    let U := T.filter (fun γ => MarkedFiber Q (z γ) (S γ))
    let V := T\U
    have us : U⊆T := filter_subset _ _
    have vs : V⊆T := sdiff_subset
    have pU := ih _ qn (fun γ hγ => (mem_filter.mp hγ).2)
      (fun f hI hD R hR hM => price f hI (hD.trans (show Q ∣ P*Q from ⟨P, mul_comm P Q⟩)) R (hR.trans us) hM)
    have pV := price P irr (show P ∣ P*Q from ⟨Q,rfl⟩) V vs (by
      intro γ hγ
      exact (split_fibre irr.ne_zero qn (marks γ (vs hγ))).resolve_right
        (fun h => (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨vs hγ,h⟩)))
    change U.card≤rate*(zView Q).natDegree+additive*Q.natDegree at pU
    have sum := card_sdiff_add_card_eq_card us
    change V.card+U.card=T.card at sum
    rw [map_mul,natDegree_mul ((map_ne_zero_iff _ zView_inj).mpr irr.ne_zero)
      ((map_ne_zero_iff _ zView_inj).mpr qn),natDegree_mul irr.ne_zero qn]
    simp only [Nat.mul_add]
    omega
theorem no_zero_degree {P : Ordinate} {z : L} {S : (Polynomial L)}
    (H : MarkedFiber P z S) : 0<P.natDegree := by
  by_contra! hm
  have hz : (specialize P z).natDegree=0 := H.full.trans (Nat.eq_zero_of_le_zero hm)
  have eq := eq_C_of_natDegree_eq_zero hz
  have h := H.root
  rw [eq,eval_C] at h
  exact H.separable.ne_zero (by rw [eq,h,C_0,Polynomial.map_zero])
private theorem specialize_constant {P : Ordinate} (zero : (zView P).natDegree=0) (z : L) :
    specialize P z=specialize P 0 := by
  apply Polynomial.map_injective incl (IsFractionRing.injective (Polynomial L) FX)
  rw [← specialize_into,← specialize_into]
  ext i
  have coeffz : (Bivariate.swap (P.coeff i)).natDegree=0 :=
    Nat.eq_zero_of_le_zero ((CurvatureSquares.coeff_caps P i).2.trans (zero.le))
  have eq : (intoFraction P).coeff i=C (incl ((Bivariate.swap (P.coeff i)).coeff 0)) := by
    simp only [intoFraction,coeff_map,RingHom.comp_apply,coe_mapRingHom]
    change (Bivariate.swap (P.coeff i)).map incl = _
    conv_lhs => rw [eq_C_of_natDegree_eq_zero coeffz]
    rw [Polynomial.map_C]
  simp only [coeff_map,coe_evalRingHom,eq,eval_C]
theorem constant_price {ι : Type*} (P : Ordinate) (T : Finset ι)
    (z : ι → L) (S : ι → Polynomial L) (inj : Set.InjOn S (T:Set ι))
    (zero : (zView P).natDegree=0) (marks : ∀ γ∈T, MarkedFiber P (z γ) (S γ)) :
    T.card≤P.natDegree := by
  classical
  rcases T.eq_empty_or_nonempty with em | ⟨γ,hγ⟩
  · simp [em]
  let Q := specialize P 0
  have qn : Q≠0 := by
    intro ne
    have h := (marks γ hγ).separable.ne_zero
    rw [specialize_constant zero,show specialize P 0=0 from ne,Polynomial.map_zero] at h
    exact h rfl
  have D : Q.natDegree=P.natDegree := by
    simpa only [specialize_constant zero (z γ),Q] using (marks γ hγ).full
  rw [← D, ← card_image_of_injOn inj]
  apply Polynomial.card_le_degree_of_subset_roots (p:=Q)
  intro v hv
  obtain ⟨η,hη,rfl⟩ := mem_image.mp hv
  exact (Polynomial.mem_roots qn).mpr (by
    simpa only [Polynomial.IsRoot,specialize_constant zero (z η),Q] using (marks η hη).root)
theorem graded_budget (e a b : ℕ) (lo : 3≤e) (hi : e<48)
    (axes : a+b≤2400) (bmax : b<(TerminalReceipts.witness e).order 1) :
    MarkedSheet.rate e*(a+p*b)+(e-1)*e≤retainedCap := by
  have numeric (i : Fin 48) : (3 ≤ i.val) →
      MarkedSheet.rate i.val*(2400+p*((TerminalReceipts.witness i.val).order 1-1))+
        (i.val-1)*i.val≤retainedCap := by
    fin_cases i <;> decide +kernel
  have hb : b≤(TerminalReceipts.witness e).order 1-1 := by omega
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add
    (by omega : a≤2400) (Nat.mul_le_mul_left _ hb))) _).trans (numeric ⟨e,hi⟩ lo)
#print axioms marked_projection
#print axioms aggregate
#print axioms constant_price
#print axioms graded_budget
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionFactors

-- merged module R6960MarkedEvaluationLedger
section Merged_R6960MarkedEvaluationLedger
set_option Elab.async false
namespace Lower6960.MarkedEvaluation
open RetainedCompression
def rate (e:ℕ) := (9*e+2)*(e-1)+2*e-1
theorem price {N e s t loss obstructions ordinary meromorphic rank pole : ℕ}
    (positive : 0<s) (ep : 0<e) (rank_bound : rank+s≤e*s)
    (collision : loss≤8*s*t) (surface : obstructions≤s+s*t) (constants : s≤ordinary)
    (lift : N*s+ordinary≤loss+obstructions+meromorphic)
    (generated : meromorphic≤rank+pole) (orbit : e*pole≤N*rank) :
    N≤9*e*t+e*(e-1) := by
  have before : N*s+ordinary ≤ 8*s*t+(s+s*t)+(rank+pole) :=
    lift.trans (Nat.add_le_add (Nat.add_le_add collision surface) generated)
  have cancel : N*s ≤ 8*s*t+s*t+rank+pole := by omega
  have scaled := Nat.mul_le_mul_left e cancel
  have share := Nat.mul_le_mul_left N rank_bound
  have rankCost:=Nat.mul_le_mul_left e rank_bound
  have first : (N*s)*e ≤ (8*s*t+s*t)*e+e*rank+N*rank := by
    calc _ = e*(N*s) := Nat.mul_comm ..
         _ ≤ _ := scaled.trans (by nlinarith only [orbit])
  have paid : N*s+s*e≤9*e*t*s+(e*e)*s := by nlinarith only [first,share,rankCost]
  have equal : 9*e*t*s+(e*e)*s=(9*e*t+e*(e-1))*s+s*e := by
    obtain ⟨k,eq⟩:=Nat.exists_eq_succ_of_ne_zero ep.ne'
    rw [eq,Nat.succ_sub_one,Nat.succ_eq_add_one]; ring
  rw [equal] at paid
  exact Nat.le_of_mul_le_mul_right (Nat.le_of_add_le_add_right paid) positive
theorem live_maximum (e : Fin 48) (lo:3≤e.val) :
    rate e.val * (2400+K1.p*((TerminalReceipts.witness e.val).order 1-1))+
      (e.val-1)*e.val ≤ 27833294590898808 := by
  fin_cases e <;> decide +kernel
theorem maximum_at_42 : rate 42 * (2400+K1.p*((TerminalReceipts.witness 42).order 1-1))+
    41*42=27833294590898808 ∧
    27833294590898808+2525762121458893=retainedCap := by decide +kernel
theorem budget (e a b : ℕ) (lo:3≤e) (hi:e<48) (axes:a+b≤2400)
    (bound:b<(TerminalReceipts.witness e).order 1) : rate e*(a+K1.p*b)+(e-1)*e≤retainedCap := by
  have fit:=live_maximum ⟨e,hi⟩ lo
  have bnd : b≤(TerminalReceipts.witness e).order 1-1 := by omega
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add
    (show a≤2400 by omega) (Nat.mul_le_mul_left _ bnd))) _).trans
    (fit.trans (by decide))
#print axioms price
#print axioms budget
end Lower6960.MarkedEvaluation

end Merged_R6960MarkedEvaluationLedger

end Merged6967_R6960MarkedEvaluationLedger

section Merged6967_R6966ProofCRTChartSpecialization
set_option Elab.async false



set_option Elab.async false

namespace Research6966.CRTChartSpecialization
open Finset Polynomial
open K1_14 (L FX Jet Seeds)
open K1_14_1 (SeedPoly PoleData CRTLift Source RawSource rawBlock crtPolynomial poleProduct jetConstant)
open K1_14_1_2 (RegularRing localLift includeGeneric specialize map_localLift specialize_localLift markedLift)
open K1_14_1_4 (evalRaw doubleMap specialized centerBase)
open PhysicalPrimitiveCoeffs (R rawCoeff)
open PhysicalChartAtMark (AtSeeds Chart H into genericMap direct atNode atLine atSeeds)
open RegularPhysicalChart (transform)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 850000
set_option maxSynthPendingDepth 24
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

private abbrev B:=K1_14_3.SeedField
private abbrev inc {h} (D:PoleData h) (t:Fin 2→L):=algebraMap (AtSeeds t) (Chart D t)
def diag {h} (D:PoleData h) (t:Fin 2→L) : (Chart D t)ˣ:=
  (IsLocalization.Away.algebraMap_isUnit (S:=Chart D t) (H D t)).unit
def crtMap {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L)
    (ok:∀i,(Crt.denominator i).eval (t i)≠0) :=
  transform (↑(diag D t):Chart D t) (inc D t (localLift Crt t ok)) (inc D t (H D t).derivative)
    (inc D t (localLift Crt t ok).derivative)

private theorem model_coeffs {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L)
    (ok:∀i,(Crt.denominator i).eval (t i)≠0) :
    genericMap D t (diag D t)=evalRaw (rawBlock D) ∧
    genericMap D t (inc D t (localLift Crt t ok))=evalRaw (crtPolynomial Crt) ∧
    genericMap D t (inc D t (H D t).derivative)=evalRaw (rawBlock D).derivative ∧
    genericMap D t (inc D t (localLift Crt t ok).derivative)=evalRaw (crtPolynomial Crt).derivative := by
  have header:(↑(diag D t):Chart D t)=inc D t (H D t):=IsUnit.unit_spec _
  have hmap:(H D t).map (includeGeneric t)=rawBlock D:=PhysicalChartAtMark.generic_H D t
  have lift:=map_localLift Crt t ok
  rw [header]
  simp only [inc,PhysicalChartAtMark.generic_atBase]
  change evalRaw ((H D t).map _) = _ ∧
    evalRaw ((localLift Crt t ok).map _) = _ ∧ evalRaw ((H D t).derivative.map _) = _ ∧
    evalRaw ((localLift Crt t ok).derivative.map _) = _
  rw [←derivative_map,←derivative_map,hmap,lift]
  exact ⟨rfl,rfl,rfl,rfl⟩

private theorem dcomp {U V W:Type*} [CommRing U] [CommRing V] [CommRing W]
    (f:U→+*V) (g:V→+*W) (N:U[X][X]) : doubleMap g (doubleMap f N)=doubleMap (g.comp f) N := by
  ext j i;simp [doubleMap]

private theorem send {U V:Type*} [CommRing U] [CommRing V] (f:U→+*V) (a b u d:U) (P:U[X][X]) :
    doubleMap f (transform a b u d P)=transform (f a) (f b) (f u) (f d) (doubleMap f P) :=
  RingHom.congr_fun (RegularPhysicalChart.maps f a b u d) P

private theorem from_native {U V:Type*} [CommRing U] [CommRing V] (f:U→+*V) (a b u d:V) (P:U[X][X]) :
    transform a b u d (doubleMap f P)=K1_14_1_4.substitute f (C (C a*Polynomial.X+C b))
      (C (C a)*Polynomial.X+C (C u*Polynomial.X+C d)) P := by
  change ((K1_14_1_4.substitute (RingHom.id V) _ _).comp (doubleMap f)) P=_
  rw [K1_14_1_4.substitute_map,RingHom.id_comp]
  simp [jetConstant,RegularPhysicalChart.yVar,RegularPhysicalChart.vVar,map_add,map_mul,add_assoc]

private theorem forward_eq {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L)
    (ok:∀i,(Crt.denominator i).eval (t i)≠0) (P:Source) :
    doubleMap (genericMap D t) (crtMap Crt t ok (doubleMap (into D t) P))=
      specialized Crt (doubleMap K1_14_1_4.centerBase P) := by
  obtain ⟨a,b,u,d⟩:=model_coeffs Crt t ok
  unfold crtMap
  rw [send,dcomp,PhysicalChartAtMark.generic_atSource,a,b,u,d]
  let native:=doubleMap K1_14_1_4.centerBase P
  have lift:doubleMap direct P=doubleMap (algebraMap Seeds B) native:=
    (dcomp centerBase (algebraMap Seeds B) P).symm
  rw [lift,from_native]
  exact (RingHom.congr_fun (K1_14_1_4.specialized_formula Crt) native).symm

private theorem raw_at_generic {h} (D:PoleData h) (t:Fin 2→L) (Q:Source) :
    doubleMap (genericMap D t) (doubleMap (into D t) Q)=doubleMap evalRaw (doubleMap rawCoeff Q) := by
  calc
    _ = doubleMap ((genericMap D t).comp (into D t)) Q := dcomp (into D t) (genericMap D t) Q
    _ = doubleMap direct Q := congrArg (fun g:R→+*B=>doubleMap g Q) (PhysicalChartAtMark.generic_atSource D t)
    _ = doubleMap (evalRaw.comp rawCoeff) Q := congrArg (fun g:R→+*B=>doubleMap g Q) PhysicalChartAtMark.direct_eq.symm
    _ = _ := (dcomp rawCoeff evalRaw Q).symm

private theorem native_raw_associated {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet}
    (M:HelperPhysicalModel.Model Crt N) : Associated (specialized Crt N) (doubleMap evalRaw M.raw) := by
  rw [M.eq]
  apply Associated.symm
  exact associated_unit_mul_left _ _ (isUnit_C.mpr (isUnit_C.mpr M.unit_c.isUnit))

private theorem generic_pair {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L)
    (ok:∀i,(Crt.denominator i).eval (t i)≠0) {N:Jet} (M:HelperPhysicalModel.Model Crt N) {P Q:Source}
    (np:Associated (doubleMap centerBase P) N) (rq:Associated (doubleMap rawCoeff Q) M.raw) :
    Associated (doubleMap (genericMap D t) (crtMap Crt t ok (doubleMap (into D t) P)))
      (doubleMap (genericMap D t) (doubleMap (into D t) Q)) := by
  rw [forward_eq Crt t ok P,raw_at_generic D t Q]
  have hp:Associated (specialized Crt (doubleMap centerBase P)) (specialized Crt N):=np.map (specialized Crt).toRingHom
  have hq:Associated (doubleMap evalRaw (doubleMap rawCoeff Q)) (doubleMap evalRaw M.raw):=rq.map (doubleMap evalRaw)
  exact hp.trans ((native_raw_associated M).trans hq.symm)

set_option maxHeartbeats 1500000 in
/-- The two global integral models differ by a unit at each admissible
label after inverting the pole block. Consequently the same comparison
can be specialized at every allowed node and at the generic abscissa. -/
theorem chart_unit {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L)
    (ok:∀i,(Crt.denominator i).eval (t i)≠0) {N:Jet} (M:HelperPhysicalModel.Model Crt N)
    {P Q:Source} (pp:Prime P) (qp:Prime Q) (ps:0<P.natDegree) (qs:0<Q.natDegree)
    (np:Associated (doubleMap K1_14_1_4.centerBase P) N) (rq:Associated (doubleMap rawCoeff Q) M.raw) :
    ∃ c:Chart D t,IsUnit c ∧ crtMap Crt t ok (doubleMap (into D t) P)=jetConstant c*doubleMap (into D t) Q := by
  exact RegularPhysicalChart.comparison (R:=R) (S:=Chart D t) (F:=B) (into D t) (PhysicalChartAtMark.into_injective D t)
    (PhysicalChartAtMark.into_clears D t) (genericMap D t) (PhysicalChartAtMark.generic_injective D t)
    (PhysicalChartAtMark.generic_clears D t) (diag D t) (inc D t (localLift Crt t ok))
    (inc D t (H D t).derivative) (inc D t (localLift Crt t ok).derivative) pp qp ps qs
    (generic_pair Crt t ok M np rq)

#print axioms chart_unit
end
end Research6966.CRTChartSpecialization

end Merged6967_R6966ProofCRTChartSpecialization

section Merged6967_R6966ProofHelperBankRank
set_option Elab.async false




set_option Elab.async false

namespace Research6966.HelperBankRank
open Polynomial Finset Module
open K1_14 (FX L Seeds Jet Equation Shape)
open K1_14_1 (PoleData CRTLift centerEval evaluated_shape evaluated_mono)
open K1_14_2_2_2_1 (jetDegree seedDegree jetDegree_le seedDegree_le jetDegree_mul seedDegree_mul)
open KoalaRect (rectEvaluated rectComplete area)
open scoped Polynomial
noncomputable section
set_option maxSynthPendingDepth 18
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private theorem read_positions (P:Finset (ℕ×ℕ)) (V:Submodule FX Jet)
    (slots:Submodule FX Seeds) [FiniteDimensional FX slots]
    (fits:∀ Q∈V,∀ j i,(Q.coeff j).coeff i∈slots)
    (lead:∀ Q∈V,Q≠0 → (Q.natDegree,Q.leadingCoeff.natDegree)∈P) :
    finrank FX V≤P.card*finrank FX slots := by
  let coord (t:P):↥V→ₗ[FX]Seeds:=(((lcoeff Seeds t.val.2).restrictScalars FX).comp
    ((lcoeff Equation t.val.1).restrictScalars FX)).comp V.subtype
  let read:↥V→ₗ[FX](P→slots):=LinearMap.pi (fun t=>(coord t).codRestrict _ (fun Q=>fits Q.val Q.property ..))
  have inj:Function.Injective read:=by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro q h
    apply Subtype.ext
    by_contra ne
    have nz:q.val≠0:=ne
    let t:P:=⟨(q.val.natDegree,q.val.leadingCoeff.natDegree),lead q.val q.property nz⟩
    have test:=congrArg (fun v:P→slots=>(v t).val) (LinearMap.mem_ker.mp h)
    change (q.val.coeff q.val.natDegree).coeff q.val.leadingCoeff.natDegree=0 at test
    rw [coeff_natDegree,coeff_natDegree] at test
    exact (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)) test
  letI freeSlots : Module.Free FX ↥slots := Module.Free.of_divisionRing FX ↥slots
  letI : ∀ _ : ↥P, Module.Free FX ↥slots := fun _ => freeSlots
  have out:=LinearMap.finrank_le_finrank_of_injective inj
  rw [Module.finrank_pi_fintype,sum_const,card_univ,Fintype.card_coe,smul_eq_mul] at out
  exact out

def cells (s:Shape) (h W t a b wt:ℕ) : Finset (ℕ×ℕ) :=
  if t*a≤s.B ∧ t*b≤s.J ∧ t*wt≤W then
    PadeFiltered.physicalWindow (s.B-t*a) (s.J-t*b) (131071-h) (W-t*wt) else ∅

private theorem power_jet {N:Jet} (nz:N≠0) (t:ℕ) : jetDegree (N^t)=t*jetDegree N := by
  induction t with
  | zero=>simp [jetDegree]
  | succ t ih=>rw [pow_succ,jetDegree_mul (pow_ne_zero _ nz) nz,ih,Nat.succ_mul]

private theorem power_seed {N:Jet} (nz:N≠0) (t:ℕ) : seedDegree (N^t)=t*seedDegree N := by
  induction t with
  | zero=>simp [seedDegree]
  | succ t ih=>rw [pow_succ,seedDegree_mul (pow_ne_zero _ nz) nz,ih,Nat.succ_mul]

/-- Both seed geometries use the same physical position set. This theorem
also applies when the common divisor is a product of distinct primes. -/
theorem bank_rank {h W t:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    (s:Shape) (U:Fin 2→ℕ) {N:Jet} (M:HelperPhysicalModel.Model Crt N) (nn:N≠0)
    (force:∀ P∈rectComplete Crt word s W U,N^t∣centerEval P) :
    let wt:=RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw
    let count:=(cells s h W t (jetDegree N) N.natDegree wt).card
    finrank FX (rectEvaluated Crt word s W U)≤count*
      (if ∀ z,t*PadeNativeQuotient.axis N z≤U z then area (fun z=>U z-t*PadeNativeQuotient.axis N z) else 0) ∧
    finrank FX (rectEvaluated Crt word s W U)≤count*
      (if t*seedDegree N≤s.U then K1_14.triangle (s.U-t*seedDegree N) else 0) := by
  classical
  dsimp only
  let step:=131071-h
  let wt:=RawPhysicalDegree.weight step (step-1) M.raw
  let V:=PadeResidualBank.residual Crt word s W U N t
  let pts:=cells s h W t (jetDegree N) N.natDegree wt
  have restored:=PadeResidualBank.restore Crt word s W U N t force
  let Lmul:=Algebra.lmul FX Jet (N^t)
  have inj:Function.Injective Lmul:=fun _ _ eq=>mul_left_cancel₀ (pow_ne_zero t nn) eq
  have same:finrank FX (rectEvaluated Crt word s W U)=finrank FX V := by
    rw [←restored]
    exact (Submodule.equivMapOfInjective Lmul inj V).finrank_eq.symm
  have src {q:Jet} (mem:q∈V):N^t*q∈rectEvaluated Crt word s W U:=restored ▸ (show
    Lmul q∈V.map Lmul from ⟨q,mem,rfl⟩)
  have totals {Q:Jet} (mem:Q∈V) (nz:Q≠0):t*seedDegree N+seedDegree Q≤s.U := by
    have source:=KoalaRect.rectEvaluated_le Crt word s W U (src mem)
    have deg:seedDegree (N^t*Q)≤s.U:= (seedDegree_le ..).mpr (by
      intro j i
      by_cases z:((N^t*Q).coeff j).coeff i=0
      · simp [z]
      · exact (evaluated_shape Crt word source j i z).2.2)
    rwa [seedDegree_mul (pow_ne_zero _ nn) nz,power_seed nn] at deg
  have axes {Q:Jet} (mem:Q∈V) (nz:Q≠0) (z:Fin 2):
      t*PadeNativeQuotient.axis N z+PadeNativeQuotient.axis Q z≤U z := by
    have cap: PadeNativeQuotient.axis (N^t*Q) z≤U z:=(PadeNativeQuotient.axis_le ..).mpr
      (fun j i=>KoalaRect.rectEvaluated_axis Crt word (src mem) j i z)
    rwa [PadeNativeQuotient.axis_mul (pow_ne_zero _ nn) nz,PadeNativeQuotient.axis_pow nn] at cap
  have leading (Q:Jet) (mem:Q∈V) (nz:Q≠0):(Q.natDegree,Q.leadingCoeff.natDegree)∈pts := by
    let j:=Q.natDegree
    let i:=Q.leadingCoeff.natDegree
    have a:=KoalaRect.rectEvaluated_le Crt word s W U (src mem)
    have jc:jetDegree (N^t*Q)≤s.B:=(jetDegree_le ..).mpr (fun j i ne=>(evaluated_shape Crt word a j i ne).1)
    have sn:=mul_ne_zero (pow_ne_zero t nn) nz
    have top:((N^t*Q).coeff (N^t*Q).natDegree).coeff (N^t*Q).leadingCoeff.natDegree≠0 := by
      rw [coeff_natDegree,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr sn)
    have lim: (N^t*Q).natDegree≤s.J := (evaluated_shape Crt word a _ _ top).2.1
    rw [jetDegree_mul (pow_ne_zero _ nn) nz,power_jet nn] at jc
    rw [natDegree_mul (pow_ne_zero _ nn) nz,natDegree_pow] at lim
    have total:i+j≤jetDegree Q:=(jetDegree_le ..).mp le_rfl j i (by
      dsimp only [i,j];rw [coeff_natDegree,coeff_natDegree];exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz))
    have nonzero:K1_14_1_4.rawPosition Crt j i Q≠0 := by
      have top:=K1_14_1_4.specialized_leading Crt nz
      change (((K1_14_1_4.specialized Crt Q).coeff j).coeff i)≠0
      rw [show j=(K1_14_1_4.specialized Crt Q).natDegree from top.1.symm,coeff_natDegree,
        show i=(K1_14_1_4.specialized Crt Q).leadingCoeff.natDegree from top.2.1.symm,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr top.2.2)
    have paid:step*i+(step-1)*j+t*wt≤W := by
      by_contra no
      have bound:V≤(K1_14_1_4.rawPosition Crt j i).ker := by
        apply Submodule.span_le.mpr
        rintro S ⟨P,inSource,id⟩
        by_contra ne
        exact no (M.physical_support hp hl word inSource.1 id j i ne)
      exact nonzero (bound mem)
    change (j,i)∈cells s h W t (jetDegree N) N.natDegree wt
    rw [cells,ite_eq_left (by omega)]
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · change (j,i)∈PadeRank.positions (s.B-t*jetDegree N+1) (s.J-t*N.natDegree+1)
      change t*N.natDegree+j≤s.J at lim
      simp [PadeRank.positions];omega
    · exact Nat.le_sub_of_add_le paid
  rw [same]
  constructor
  · split
    · let U':=fun z=>U z-t*PadeNativeQuotient.axis N z
      have bound:=read_positions pts V (WordSurfaceInterpolation.rect (Fin 2) FX U') (by
        intro Q mem j i
        apply WordSurfaceInterpolation.in_rect.mpr
        intro z
        by_cases zero:Q=0
        · simp [zero]
        · exact (PadeNativeQuotient.axis_le ..).mp (by
            have p:=axes mem zero z
            change PadeNativeQuotient.axis Q z≤U z-t*PadeNativeQuotient.axis N z;omega) j i) leading
      rw [WordSurfaceInterpolation.rectangle_dimension,Fin.prod_univ_two] at bound
      exact bound
    · rename_i no
      have bot:V=⊥:=le_antisymm (by
        intro Q mem;by_contra n;exact no (fun z=>(Nat.le_add_right _ _).trans (axes mem n z))) bot_le
      rw [bot,finrank_bot,mul_zero]
  · split
    · have bound:=read_positions pts V (MvPolynomial.restrictTotalDegree (Fin 2) FX (s.U-t*seedDegree N)) (by
        intro Q mem j i
        apply (MvPolynomial.mem_restrictTotalDegree ..).mpr
        by_cases zero:Q=0
        · simp [zero]
        · have s:=totals mem zero
          exact (seedDegree_le ..).mp (by omega : seedDegree Q≤_ ) j i) leading
      rw [K1_14_2_1_2.seed_finrank] at bound
      exact bound
    · rename_i no
      have bot:V=⊥:=le_antisymm (by
        intro Q mem;by_contra n;exact no ((Nat.le_add_right _ _).trans (totals mem n))) bot_le
      rw [bot,finrank_bot,mul_zero]

#print axioms bank_rank
end
end Research6966.HelperBankRank

end Merged6967_R6966ProofHelperBankRank

section Merged6967_R6966ProofNativeAffineRows
set_option Elab.async false




set_option Elab.async false

namespace Research6966.NativeAffineRows
open Polynomial Finset
open K1 (K I p)
open K1_14 (L FX Seeds Equation atX jetAt graphEval liftPoly seedEmbedding)
open K1_14_3 (SeedField Surface ProjectedProduct)
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open scoped Polynomial Differential Classical
attribute [local instance] GenericPhysicalCentre.physical
noncomputable section
set_option maxHeartbeats 950000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 18

abbrev leading {G : Pade.Row SeedField} (N : Native G) := (den N).coeff 0
abbrev linear {G : Pade.Row SeedField} (N : Native G) := (rhs N).coeff 1
abbrev constant {G : Pade.Row SeedField} (N : Native G) := (rhs N).coeff 0

theorem den_eq {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive)
    (affine : G.graphDegree = 1) : den N = C (leading N) := by
  have cap := (NativeGraphMarks.equation_degrees N gp).1
  change (den N).natDegree ≤ G.graphDegree-1 at cap
  exact eq_C_of_natDegree_eq_zero (by omega)

theorem rhs_eq {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive)
    (affine : G.graphDegree = 1) : rhs N = C (linear N)*Polynomial.X+C (constant N) := by
  apply Polynomial.eq_X_add_C_of_natDegree_le_one
  have cap := (NativeGraphMarks.equation_degrees N gp).2
  rwa [affine] at cap

def seedPoint (z : K) : Fin 2 → FX := ![seedEmbedding z, seedEmbedding z^p]

private theorem constant_power {R : Type*} [Field R] [Differential R]
    (x : R) (fixed : Differential.deriv x = 0) (n : ℕ) :
    Differential.deriv (x^n) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Derivation.leibniz, fixed, ih, smul_zero, smul_zero, add_zero]

private theorem constant_pair {R : Type*} [Field R] [Differential R] (x : R) (n : ℕ)
    (hx : Differential.deriv x = 0) (i : Fin 2) :
    Differential.deriv ((![x,x^n] : Fin 2 → R) i) = 0 := by
  fin_cases i
  · exact hx
  · exact constant_power _ hx _

private theorem fixed (z : K) (j : Fin 2) : Differential.deriv (seedPoint z j) = 0 := by
  apply constant_pair (seedEmbedding z) p _ j
  change Differential.deriv (algebraMap L[X] FX (C (algebraMap K L z))) = 0
  rw [GenericPhysicalCentre.physical_poly, derivative_C, map_zero]

theorem label_inj {u deleted maxHeight} (M : P1.ModelAt maxHeight u deleted) :
    Function.Injective M.label := by
  intro x y same
  exact sub_left_injective (b := M.shift) same

def val {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ : Finset K}
    (F : P1.FamilyAt a M Γ) (z : K) (Q : Equation) : FX :=
  Q.eval₂ (graphEval (M.label z)) (atX (F.scalar z))

def bad {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ : Finset K}
    (F : P1.FamilyAt a M Γ) (T : Finset K) {G : Pade.Row SeedField} (N : Native G) : Finset K :=
  T.filter (fun z => val F z (den N) = 0)

def good {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ : Finset K}
    (F : P1.FamilyAt a M Γ) (T : Finset K) {G : Pade.Row SeedField} (N : Native G) : Finset K :=
  T \ bad F T N

theorem good_subset {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {G : Pade.Row SeedField} (N : Native G) : good F T N ⊆ T :=
  sdiff_subset

theorem sizes {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {G : Pade.Row SeedField} (N : Native G) :
    (good F T N).card+(bad F T N).card = T.card :=
  card_sdiff_add_card_eq_card (filter_subset _ _)

def Owned {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ : Finset K}
    (F : P1.FamilyAt a M Γ) (T : Finset K) (parents : Finset Surface) {G : Pade.Row SeedField}
    (N : Native G) : Prop :=
  ∀ z ∈ T, ∃ q ∈ parents, N.poly ∈ q.asIdeal ∧
    ∀ P ∈ q.asIdeal, jetAt P (M.label z) (F.scalar z) = 0

private theorem law {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (owners : Owned F T parents N) (z : K) (mem : z ∈ T) :
    val F z (den N)*atX (F.scalar z).derivative = val F z (rhs N) := by
  obtain ⟨q, _, own, mark⟩ := owners z mem
  exact NativeGraphMarks.mark_law N gp own mark

theorem fee {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z)
    (small : width 0 < p) (owners : Owned F T parents N) :
    (bad F T N).card ≤ width 0+p*width 1 := by
  have count := NativeGraphExceptional.singular_count N gp width axes (by simpa [affine] using small)
    (bad F T N) M.label (label_inj M).injOn (fun z => atX (F.scalar z))
    (fun z mem => (mem_filter.mp mem).2) (by
      intro z mem
      obtain ⟨ht, hz⟩ := mem_filter.mp mem
      have eq := law F N gp owners z ht
      change val F z (den N) = 0 at hz
      rw [hz, zero_mul] at eq
      exact eq.symm)
  simpa only [affine, show 2*1-1=1 by decide, one_mul] using count

def point {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ : Finset K}
    (F : P1.FamilyAt a M Γ) (z : K) : Fin 3 → FX :=
  Fin.cons (atX (F.scalar z)) (seedPoint (M.label z))

private abbrev scalar := algebraMap L FX

def equation {u deleted maxHeight} (M : P1.ModelAt maxHeight u deleted)
    {G : Pade.Row SeedField} (N : Native G) (d : ℕ) (i : I) : Equation :=
  AffineMarkRows.row (leading N) (linear N) (constant N) d
    (algebraMap L[X] FX Polynomial.X) (scalar (algebraMap K L (K1.node i)))
    (scalar (algebraMap K L (M.word i)))

def rows {u deleted maxHeight} (M : P1.ModelAt maxHeight u deleted)
    {G : Pade.Row SeedField} (N : Native G) (d : ℕ) (i : I) : MvPolynomial (Fin 3) FX :=
  OdeSurfaceBridge.coordinates (equation M N d i)

theorem seed_cap {G : Pade.Row SeedField} (N : Native G) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z) (z : Fin 2) :
    (leading N) ∈ MvPolynomial.restrictWeightAtMost (Pi.single z 1) (width z) ∧
    (linear N) ∈ MvPolynomial.restrictWeightAtMost (Pi.single z 1) (width z) ∧
    (constant N) ∈ MvPolynomial.restrictWeightAtMost (Pi.single z 1) (width z) := by
  simp only [MvPolynomial.mem_restrictWeightAtMost, Finsupp.weight_single_one_apply,
    ← MvPolynomial.degreeOf_le_iff]
  exact ⟨axes 1 0 z, by simpa [linear, rhs, coeff_neg] using axes 0 1 z,
    by simpa [constant, rhs, coeff_neg] using axes 0 0 z⟩

theorem row_caps {u deleted maxHeight} (M : P1.ModelAt maxHeight u deleted) {G : Pade.Row SeedField}
    (N : Native G) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z) (d : ℕ) :
    ∀ i j, (rows M N d i).degreeOf j ≤ Fin.cons (α := fun _ : Fin 3 => ℕ) 1 (fun z => d*width z) j := by
  intro i
  apply OdeSurfaceBridge.degrees (equation M N d i) 1 _ (AffineMarkRows.row_degree ..)
  intro z
  obtain ⟨hA, hB, hC⟩ := seed_cap N width axes z
  exact AffineMarkRows.row_cap _ _ _ _ _ _ hA hB hC _ _ _

theorem nodal_count_hypotheses {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1)
    (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (owners : Owned F T parents N) :
    (∀ z : ↥(good F T N), a ≤ (WordSurfaceMarks.hits (point F z.val) (rows M N d)).card) ∧
    (∀ (x y : ↥(good F T N)), x ≠ y →
      ((WordSurfaceMarks.hits (point F x.val) (rows M N d)) ∩
        (WordSurfaceMarks.hits (point F y.val) (rows M N d))).card ≤ d) := by
  classical
  let S := good F T N
  let words (z : ↥S) := liftPoly (F.scalar z.val)
  let nodes (i : I) : FX := scalar (algebraMap K L (K1.node i))
  let recv (i : I) : FX := scalar (algebraMap K L (M.word i))
  have marks (z : ↥S) := F.mark z.val (sub (good_subset F N z.property))
  have degree (z : ↥S) : (words z).natDegree ≤ d := by
    change ((F.scalar z.val).map (algebraMap K L)).natDegree ≤ d
    rw [natDegree_map_eq_of_injective (algebraMap K L).injective]
    rcases (marks z).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar z.val).natDegree : ℤ) ≤ 131071+M.overhead at bound
      omega
  have unique : Function.Injective words := fun x z eq => Subtype.ext (F.distinct
    (sub (good_subset F N x.property)) (sub (good_subset F N z.property))
    ((map_injective _ (algebraMap K L).injective) eq))
  have detect (z : ↥S) (i : I) :
      MvPolynomial.eval (point F z.val) (rows M N d i) = 0 ↔ ((words z).map scalar).eval (nodes i) = recv i := by
    rw [show MvPolynomial.eval (point F z.val) (rows M N d i) =
      NonlinearMarkRows.evaluate (seedPoint (M.label z.val)) (atX (F.scalar z.val)) (equation M N d i)
        from OdeSurfaceBridge.read ..]
    have den0 := den_eq N gp affine
    have rhs1 := rhs_eq N gp affine
    have nz : val F z.val (den N) ≠ 0 := fun zero =>
      (mem_sdiff.mp z.property).2 (mem_filter.mpr ⟨good_subset F N z.property, zero⟩)
    have eq := law F N gp owners z.val (good_subset F N z.property)
    unfold val at nz eq
    rw [den0, eval₂_C] at nz eq
    rw [rhs1, eval₂_add, eval₂_mul, eval₂_C, eval₂_C, eval₂_X] at eq
    change MvPolynomial.eval (seedPoint (M.label z.val)) (leading N) ≠ 0 at nz
    have law' : MvPolynomial.eval (seedPoint (M.label z.val)) (leading N)*
        algebraMap L[X] FX (words z).derivative =
      MvPolynomial.eval (seedPoint (M.label z.val)) (linear N)*atX (F.scalar z.val)+
        MvPolynomial.eval (seedPoint (M.label z.val)) (constant N) := by
      simpa only [words, liftPoly, derivative_map, atX, graphEval, seedPoint] using eq
    exact AffineMarkRows.detects _ (fixed (M.label z.val)) _ _ _ (words z) d (degree z)
      (fun j hj => K1_14_2_4_2.factorial_ne_zero (hj.trans_lt dp)) _ _ law' nz
  refine ⟨?_, WordSurfacePrice.word_overlap (fun z : ↥S => point F z.val) (rows M N d) nodes
    (scalar.injective.comp ((algebraMap K L).injective.comp ProximityPrize.Benchmark.IRSProfile.domain.injective))
    recv (fun z => (words z).map scalar) ((map_injective _ scalar.injective).comp unique) d
    (fun z => natDegree_map_le.trans (degree z)) detect⟩
  intro z
  exact (marks z).bad.agreement.trans (card_le_card (fun i hi => WordSurfaceMarks.hit.mpr
    ((detect z i).mpr ((Polynomial.eval_map_apply scalar _).trans
      (congrArg scalar ((Polynomial.eval_map_apply (algebraMap K L) _).trans
        (congrArg (algebraMap K L) ((marks z).scalar_hits i hi))))))))

#print axioms nodal_count_hypotheses
#print axioms fee
end
end Research6966.NativeAffineRows

end Merged6967_R6966ProofNativeAffineRows

section Merged6967_R6966ProofNativeProjectedWitness
set_option Elab.async false



set_option Elab.async false

namespace Research6966.NativeProjectedWitness
open Polynomial Finset
open K1_14 (Jet Equation Seeds)
open K1_14_3 (SeedField SeedClosure Surface Parent OrderAt ProjectedProduct OnSeedFibre fibreRow)
open K1_14_1_4 (doubleMap)
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open TerminalProjection (cleared)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

private abbrev E:=SeedClosure
private abbrev φ:=K1_14_3.seedGeneric
private theorem inj:Function.Injective φ:=(algebraMap SeedField E).injective.comp (IsFractionRing.injective Seeds SeedField)

theorem graph_eq {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) :
    C (den N)*Polynomial.X-C (rhs N)=N.poly := by
  simpa only [den,rhs,map_neg,sub_neg_eq_add] using
    (Polynomial.eq_X_add_C_of_natDegree_le_one (NativeGraphMarks.slope_degree N gp).le).symm

private theorem map_clear (A B:Equation) (Q:Jet) (J:ℕ) (cap:Q.natDegree≤J) :
    (cleared A B Q J).map φ=cleared (A.map φ) (B.map φ) (fibreRow Q) J := by
  have top:(fibreRow Q).natDegree≤J:=by
    change (Q.map (mapRingHom φ)).natDegree≤J;exact natDegree_map_le.trans cap
  rw [cleared,cleared,Q.sum_over_range' (fun _=>by simp) (J+1) (by omega),
    (fibreRow Q).sum_over_range' (fun _=>by simp) (J+1) (by omega),Polynomial.map_sum]
  apply sum_congr rfl
  intro j _
  simp only [Polynomial.map_mul,Polynomial.map_pow,fibreRow,coeff_map,coe_mapRingHom]

/-- Fix the actual projected product once. Every avoiding row, including
one from a differently shaped bank, bounds this same native equation. -/
theorem projected_factor {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
    (parents:Finset Surface) (nonempty:parents.Nonempty) (geo:∀ q∈parents,Parent q)
    (onGraph:∀ q∈parents,N.poly∈q.asIdeal) :
    ∃ H:Equation,ProjectedProduct parents H ∧ ∀ (Q:Jet) (J k:ℕ),Q.natDegree≤J →
      (∀ q∈parents,OrderAt q Q k) → H^k ∣ cleared (den N) (rhs N) Q J := by
  obtain ⟨H,T,v,proj,card,sheets⟩:=Pade.Native.projected_sheets parents nonempty geo
  let emb:Pade.Native.Sep→+*E:=(separableClosure SeedField E).val.toRingHom
  let ys:=T.image emb
  let vel (y:E):=if eq:∃ x∈T,emb x=y then emb (v eq.choose) else 0
  have velocity x (mem:x∈T):vel (emb x)=emb (v x) := by
    have yes:∃ z∈T,emb z=emb x:=⟨x,mem,rfl⟩
    simp only [vel,dite_eq_left yes,emb.injective yes.choose_spec.2]
  have root (y:E) (hy:y∈ys):∃ q∈parents,OnSeedFibre q y (vel y) := by
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hy
    rw [velocity x hx]
    exact (Pade.Native.sheets_iff ..).mp (sheets x hx)
  let D:E[X]:=∏y∈ys,(Polynomial.X-C y)
  have cardD:D.natDegree=H.natDegree := by
    dsimp only [D]
    rw [natDegree_prod ys (fun y=>Polynomial.X-C y) (fun y _=>X_sub_C_ne_zero y)]
    simpa only [natDegree_X_sub_C,sum_const,smul_eq_mul,mul_one,ys,card_image_of_injective _ emb.injective] using card
  have hn:H.map φ≠0:=(map_ne_zero_iff (mapRingHom φ) (map_injective φ inj)).mpr proj.primitive.ne_zero
  have divides:D∣H.map φ := by
    apply prod_dvd_of_coprime
    · intro x hx y hy ne;exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ne).isUnit
    · intro y hy
      obtain ⟨q,mem,onq⟩:=root y hy
      have zero:=proj.vanishes q mem
      rw [←onq,RingHom.mem_ker] at zero
      apply dvd_iff_isRoot.mpr
      change (H.map φ).eval y=0
      rw [eval_map]
      simpa only [K1_14_3.seedFibreEval,coe_eval₂RingHom,eval₂_C] using zero
  obtain ⟨a,eq⟩:=divides
  have da:D≠0:=left_ne_zero_of_mul (eq ▸ hn)
  have an:a≠0:=right_ne_zero_of_mul (eq ▸ hn)
  have total: (H.map φ).natDegree = D.natDegree+a.natDegree := by rw [eq,natDegree_mul da an]
  rw [natDegree_map_eq_of_injective inj,cardD] at total
  have const:a=C (a.coeff 0):=eq_C_of_natDegree_eq_zero (by omega)
  have cn:a.coeff 0≠0:=by intro z;apply an;rw [const,z,map_zero]
  have unit:IsUnit a:=const ▸ isUnit_C.mpr cn.isUnit
  have assoc:Associated (H.map φ) D:=eq ▸ associated_mul_unit_left _ _ unit
  refine ⟨H,proj,?_⟩
  intro Q J k cap order
  have projQ:=TerminalProjection.all_sheets ((den N).map φ) ((rhs N).map φ) (fibreRow Q) ys vel J k
    (natDegree_map_le.trans cap) (by
      intro y hy
      obtain ⟨q,mem,onq⟩:=root y hy
      have zero:=onGraph q mem
      rw [←onq,RingHom.mem_ker] at zero
      rw [←graph_eq N gp] at zero
      have hit:((den N).map φ).eval y*vel y=((rhs N).map φ).eval y := by
        simp only [K1_14_3.seedFibreEval,coe_eval₂RingHom,eval₂_sub,eval₂_mul,eval₂_C,eval₂_X] at zero
        simpa only [eval_map] using sub_eq_zero.mp zero
      have nz:((den N).map φ).eval y≠0:=by
        intro z
        obtain ⟨l,w,id⟩:=NativeGraphExceptional.coprime_generic N gp
        have bad:=congrArg (eval y) id
        simp [←hit,z] at bad
      exact ⟨nz,hit,order q mem y (vel y) onq⟩)
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Seeds)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid Seeds
  have prim (i:ℕ) : (H^i).IsPrimitive := by
    induction i with
    | zero=>simp
    | succ i ih=>rw [pow_succ];exact ih.mul proj.primitive
  apply PadeRawField.primitive_divides φ inj (prim k)
  rw [Polynomial.map_pow,map_clear _ _ _ _ cap]
  exact (pow_dvd_pow_of_dvd assoc.dvd k).trans projQ

theorem axis_clear {G:Pade.Row SeedField} (N:Native G) (Q:Jet) (z:Fin 2) (J U u:ℕ)
    (cap:Q.natDegree≤J) (Qaxis:∀ j i,((Q.coeff j).coeff i).degreeOf z≤U)
    (Naxis:∀ j i,((N.poly.coeff j).coeff i).degreeOf z≤u) :
    KoalaRect.axisDegree (cleared (den N) (rhs N) Q J) z ≤ U+J*u := by
  let view:=K1_14_4.seedView
  have a:KoalaRect.axisDegree (den N) z≤u:=(KoalaRect.axisDegree_le_iff ..).mpr (Naxis 1)
  have b:KoalaRect.axisDegree (rhs N) z≤u:=(KoalaRect.axisDegree_le_iff ..).mpr (fun i=>by simpa [rhs] using Naxis 0 i)
  change (view (cleared (den N) (rhs N) Q J)).degreeOf z≤_
  rw [cleared,Polynomial.sum_def,map_sum]
  apply (MvPolynomial.degreeOf_sum_le ..).trans (Finset.sup_le _)
  intro j hj
  have jJ: j≤J:=(le_natDegree_of_mem_supp j hj).trans cap
  have q:KoalaRect.axisDegree (Q.coeff j) z≤U:=(KoalaRect.axisDegree_le_iff ..).mpr (Qaxis j)
  rw [map_mul,map_mul,map_pow,map_pow]
  calc
    _ ≤ (U+j*u)+(J-j)*u := (MvPolynomial.degreeOf_mul_le ..).trans (Nat.add_le_add
      ((MvPolynomial.degreeOf_mul_le ..).trans (Nat.add_le_add q
        ((MvPolynomial.degreeOf_pow_le ..).trans (Nat.mul_le_mul_left j b))))
      ((MvPolynomial.degreeOf_pow_le ..).trans (Nat.mul_le_mul_left (J-j) a)))
    _ = _ := by rw [Nat.add_assoc,←Nat.add_mul,Nat.add_sub_of_le jJ]

theorem avoiding_widths {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
    {H:Equation} (hn:H≠0) (Q:Jet) (k J B:ℕ) (U u:Fin 2→ℕ)
    (notDiv:¬N.poly∣Q) (cap:Q.natDegree≤J) (joint:∀ j∈Q.support,(Q.coeff j).natDegree+j≤B)
    (Qa:∀ j i z,((Q.coeff j).coeff i).degreeOf z≤U z)
    (Na:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤u z)
    (divides:H^k∣cleared (den N) (rhs N) Q J) :
    k*H.natDegree≤B+(G.graphDegree-1)*J ∧ ∀ z,k*KoalaRect.axisDegree H z≤U z+J*u z := by
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Equation)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid Equation
  have eq:=graph_eq N gp
  have nz:=TerminalProjection.integral_nonzero_of_avoids (den N) (rhs N) Q J cap
    (NativeGraphExceptional.den_ne N gp) (eq ▸ N.primitive) (eq ▸ notDiv)
  have deg:=NativeGraphMarks.equation_degrees N gp
  have y:=TerminalProjection.ordinate_width (den N) (rhs N) Q J G.graphDegree B cap
    (by unfold Pade.Row.graphDegree;omega) deg.1 deg.2 joint
  have lower:=natDegree_le_of_dvd divides nz
  rw [natDegree_pow] at lower
  refine ⟨lower.trans y,?_⟩
  intro z
  obtain ⟨D,eq⟩:=divides
  have dn:=right_ne_zero_of_mul (eq ▸ nz)
  have axis:=axis_clear N Q z J (U z) (u z) cap (fun j i=>Qa j i z) (fun j i=>Na j i z)
  rw [eq,KoalaRect.axisDegree_mul (pow_ne_zero _ hn) dn,KoalaRect.axisDegree_pow hn] at axis
  omega

#print axioms projected_factor
#print axioms avoiding_widths
end
end Research6966.NativeProjectedWitness

end Merged6967_R6966ProofNativeProjectedWitness
