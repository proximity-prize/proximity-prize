import ProximityPrize.SubmissionLower.HigherRootOwnAssembly6810P3

namespace ProximityPrize.SubmissionLower.HigherRootCarrier6810P3

open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open LocatorHybridCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def Active (p : FlagDegree) : Prop :=
  3 ≤ p.all ∧ 2 ≤ p.yz ∧ 3 ≤ p.zOnly ∧ 2695 < p.all+p.yz+p.zOnly

def ledgerCap (p : FlagDegree) : ℕ :=
  HigherRootArithmetic6810.P3.roundedCap (p.all-3) (p.yz-2) p.zOnly

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
    (hagreement : ∀ gamma ∈ seeds, 181294 ≤
      (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0)
    (hregular : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0)
    (hno : NoLargeSelectedPencil selected seeds w 80850) :
    HigherRootRegularData6810P3.Data nodes u0 u1 where
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

theorem carrier_count_le_ledger (D L s : ℕ) (F : MvPolynomial (Fin 4) K)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hF : Irreducible F) (hrdegree : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w L s)
    (ht : wt residualTotalWeights F ≤ 7501) (hy : wt residualYSWeights F ≤ 142)
    (hr : wt residualSWeights F ≤ 31)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ seeds, 181294 ≤
      (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0)
    (hregular : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0)
    (hno : NoLargeSelectedPencil selected seeds w 80850)
    (hI : Fintype.card I=262144)
    (ha : Active (originalCumulativeFlag F)) :
    seeds.card ≤ ledgerCap (originalCumulativeFlag F) := by
  let p := originalCumulativeFlag F
  have ha' : 3 ≤ p.all ∧ 2 ≤ p.yz ∧ 3 ≤ p.zOnly ∧
      2695 < p.all+p.yz+p.zOnly := ha
  have h3 : 3 ≤ wt residualSWeights F := ha'.1
  have hry : wt residualSWeights F+2 ≤ wt residualYSWeights F := by
    have hv : 2 ≤ wt residualYSWeights F-wt residualSWeights F := ha'.2.1
    omega
  have hyt : wt residualYSWeights F+2 ≤ wt residualTotalWeights F := by
    have hz : 3 ≤ wt residualTotalWeights F-wt residualYSWeights F := ha'.2.2.1
    omega
  have htotal : p.all+p.yz+p.zOnly = wt residualTotalWeights F := by
    change wt residualSWeights F+(wt residualYSWeights F-wt residualSWeights F)+
      (wt residualTotalWeights F-wt residualYSWeights F) = wt residualTotalWeights F
    omega
  let S := ofCarrier D L s F hDlow hDchar hF hrdegree hbox ht hy hr h3 hry hyt
    selected seeds hdegree hagreement hsolution hregular hno
  have hown : HigherRootOwnShape6810P3.Own S := rfl
  have hL : 2695 < S.t := by
    change 2695 < wt residualTotalWeights F
    rw [← htotal]
    exact ha'.2.2.2
  exact HigherRootOwnAssembly6810P3.count_profile_le_full_rounded S hI hown hL


end Carrier
end
end ProximityPrize.SubmissionLower.HigherRootCarrier6810P3
