import ProximityPrize.SubmissionLower.BoundaryTailOrdinary
import ProximityPrize.SubmissionLower.BoundaryTailRefinedCap

namespace ProximityPrize.SubmissionLower.BoundaryTailBase

open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open LocatorHybridCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def Active (p : FlagDegree) : Prop :=
  3 ≤ p.all ∧ 2 ≤ p.yz ∧ 2 ≤ p.zOnly ∧ 2340 < p.all+p.yz+p.zOnly

instance (p : FlagDegree) : Decidable (Active p) := by
  unfold Active
  infer_instance

/-- The sole profile refinement of the new ordinary singleton cost. -/
def cap (p : FlagDegree) : ℕ :=
  if Active p then
    min (BoundaryTailOrdinary.rawCost p)
      (BoundaryTailRefinedCap.profile p.all p.yz p.zOnly)
  else BoundaryTailOrdinary.rawCost p

theorem cap_le_raw (p : FlagDegree) : cap p ≤ BoundaryTailOrdinary.rawCost p := by
  unfold cap
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem cap_le_profile (p : FlagDegree) (h : Active p) :
    cap p ≤ BoundaryTailRefinedCap.profile p.all p.yz p.zOnly := by
  rw [cap, if_pos h]
  exact min_le_right _ _

section Carrier
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

/-- Build the retained-profile context from the carrier's actual cumulative
weights, restricting neither the source box nor the selected solution set. -/
def ofCarrier (D L s : ℕ) (F : MvPolynomial (Fin 4) K)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hF : Irreducible F) (hrdegree : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w L s)
    (ht : wt residualTotalWeights F ≤ 7501) (hy : wt residualYSWeights F ≤ 142)
    (hr : wt residualSWeights F ≤ 31)
    (h3 : 3 ≤ wt residualSWeights F)
    (hry : wt residualSWeights F+2 ≤ wt residualYSWeights F)
    (hyt : wt residualYSWeights F+2 ≤ wt residualTotalWeights F)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ seeds, 181333 ≤
      (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0)
    (hregular : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0)
    (hno : NoLargeSelectedPencil selected seeds w 80811) :
    BoundaryTailRegularData.Data nodes u0 u1 where
  D := D
  t := wt residualTotalWeights F
  y := wt residualYSWeights F
  r := wt residualSWeights F
  Dlow := hDlow
  Dchar := hDchar
  tbound := ht
  ybound := hy
  rbound := hr
  rpos := h3
  ry := hry
  yt := hyt
  F := F
  irreducible := hF
  rdegree := hrdegree
  box := by
    intro e he
    have hs := MvPolynomial.le_weightedTotalDegree residualSWeights he
    have ht := MvPolynomial.le_weightedTotalDegree residualTotalWeights he
    simp only [RCN081.weight_fin4,residualSWeights,residualTotalWeights,Fin.isValue,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Nat.mul_zero,Nat.mul_one,
      Nat.zero_add,Nat.add_zero] at hs ht
    change e 1+e 2+e 3 ≤ wt residualTotalWeights F at ht
    exact ⟨by omega,hs,(hbox he).2.2⟩
  support := by
    constructor <;> dsimp only [cellSupport,RCN198.support,cellA,cellB,cellS] <;> omega
  selected := selected
  seeds := seeds
  degree := hdegree
  agreement := hagreement
  solution := hsolution
  regular := hregular
  noPencil := hno

theorem carrier_count_le_profile (D L s : ℕ) (F : MvPolynomial (Fin 4) K)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hF : Irreducible F) (hrdegree : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w L s)
    (ht : wt residualTotalWeights F ≤ 7501) (hy : wt residualYSWeights F ≤ 142)
    (hr : wt residualSWeights F ≤ 31)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ seeds, 181333 ≤
      (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0)
    (hregular : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0)
    (hno : NoLargeSelectedPencil selected seeds w 80811)
    (hI : Fintype.card I=262144)
    (ha : Active (originalCumulativeFlag F)) :
    seeds.card ≤ BoundaryTailRefinedCap.profile
      (originalCumulativeFlag F).all (originalCumulativeFlag F).yz
      (originalCumulativeFlag F).zOnly := by
  let p := originalCumulativeFlag F
  have ha' : 3 ≤ p.all ∧ 2 ≤ p.yz ∧ 2 ≤ p.zOnly ∧
      2340 < p.all+p.yz+p.zOnly := ha
  have h3 : 3 ≤ wt residualSWeights F := ha'.1
  have hry : wt residualSWeights F+2 ≤ wt residualYSWeights F := by
    have hv : 2 ≤ wt residualYSWeights F-wt residualSWeights F := ha'.2.1
    omega
  have hyt : wt residualYSWeights F+2 ≤ wt residualTotalWeights F := by
    have hz : 2 ≤ wt residualTotalWeights F-wt residualYSWeights F := ha'.2.2.1
    omega
  have htotal : p.all+p.yz+p.zOnly = wt residualTotalWeights F := by
    change wt residualSWeights F+(wt residualYSWeights F-wt residualSWeights F)+
      (wt residualTotalWeights F-wt residualYSWeights F) = wt residualTotalWeights F
    omega
  let S := ofCarrier D L s F hDlow hDchar hF hrdegree hbox ht hy hr h3 hry hyt
    selected seeds hdegree hagreement hsolution hregular hno
  have hown : BoundaryTailOwnShape.Own S := rfl
  have hL : 2340 < S.t := by
    change 2340 < wt residualTotalWeights F
    rw [← htotal]
    exact ha'.2.2.2
  have hb := BoundaryTailProfileCount.count_116 S hI hown hL
  change seeds.card ≤ BoundaryTailAsymmetric.numericBound p.all p.yz p.zOnly
    47 157 2340 21 5 7 at hb
  exact hb.trans (BoundaryTailRefinedCap.numericBound_le_profile p.all p.yz p.zOnly
    (by omega) (by unfold BoundaryTailRefinedCap.start; omega))

end Carrier

section Benchmark
open ProximityPrize.Benchmark
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- The semantic base cap for every actual regular factor. Ordinary counting,
profile interpolation, retained geometry and exceptional events are supplied
by proved construction theorems, not assumptions on an external provider. -/
theorem regular_factor_count
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hS : P.s ≤ 31) (hY : P.ys ≤ 142) (hT : P.total ≤ 7501)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (HQ : ResidualSupportData P Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181333 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i+gamma*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80811)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤ cap (regularCumulativeFlag Q R) := by
  have hold := BoundaryTailOrdinary.regular_factor_count_raw D P hDlow hDchar
    hS hY hT Q hQ hbox HQ selected Gamma u0 u1 hdegree hagreement hno R
  unfold cap
  split_ifs with ha
  · apply le_min hold
    have hRdata := directFactor_data Q R.1 hQ D 131071 P.total P.s hbox R.2
    have hRsupport := BoundaryTailOrdinary.factor_support Q hQ HQ R
    have hsub := regularSeeds_subset Q selected Gamma R
    exact carrier_count_le_profile (nodes := IRSProfile.domain) (u0 := u0) (u1 := u1)
      D P.total P.s R.1 hDlow hDchar hRdata.1 hRdata.2.1 hRdata.2.2
      (hRsupport.total_weight.trans hT) (hRsupport.ys_weight.trans hY)
      (hRsupport.s_weight.trans hS)
      selected (regularSeeds Q selected Gamma R)
      (fun gamma hg => hdegree gamma (hsub hg))
      (fun gamma hg => hagreement gamma (hsub hg))
      (fun gamma hg => (Finset.mem_filter.mp hg).2.1)
      (fun gamma hg => (Finset.mem_filter.mp hg).2.2)
      (noLargeSelectedPencil_mono selected Gamma _ 131071 80811 hsub hno)
      (by norm_num [I, IRSProfile.Index]) ha
  · exact hold

end Benchmark
end
end ProximityPrize.SubmissionLower.BoundaryTailBase
