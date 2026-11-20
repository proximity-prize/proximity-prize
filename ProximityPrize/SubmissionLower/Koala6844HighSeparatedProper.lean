import ProximityPrize.SubmissionLower.Koala6831IntrinsicLongProper
import ProximityPrize.SubmissionLower.Koala6831IntrinsicSelectedComponents


namespace ProximityPrize.SubmissionLower.Koala6844HighSeparated

open Koala6831Intrinsic RCN135 RCN136 RCN234 RCN264
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {K : Type} [Field K] [CharP K 2130706433]

local notation "Ω" => GenericField K
local notation "φ" => polynomialEmbedding K

def Persistent (F : Carrier K) (w : ℕ) (C : Ideal (MvPolynomial (Fin 3) Ω)) : Prop :=
  ∀ j, surfaceMap φ (tailNumerator F (w + j)) ∈ C

theorem nonpersistent_selected_price
    (F : Carrier K) (hp : Nat.Prime 2130706433) (hF : Irreducible F)
    (hY : wt ![0, 1, 0, 0] F ≤ 22)
    (hT : wt ![0, 1, 1, 0] F ≤ 200)
    (hZ : wt ![0, 0, 0, 1] F ≤ 162)
    (G : MvPolynomial (Fin 3) Ω) (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hproper : ¬ G ∣ surfaceMap φ (tailNumerator F 131071))
    (gy gt gz : ℕ) (hyt : gy ≤ gt) (hy : gy ≤ 22) (ht : gt ≤ 200) (hz : gz ≤ 162)
    (hGy : G.degreeOf 0 ≤ gy) (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ gt)
    (hGz : G.degreeOf 2 ≤ gz)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ 2130706433) F = 0)
    (hreg : ∀ g ∈ seeds,
      graphSpecialize (selected g) g (g ^ 2130706433) (implicitRegularity F) ≠ 0) :
    (∑ C : {C : FirstTailComponent F 131071 G // ¬ Persistent F 131071 C.1},
      (selectedComponentPoints F 131071 2130706433 G seeds selected C.1).card) ≤
        longProperCurveCost gy gt gz := by
  classical
  let Components := {C : FirstTailComponent F 131071 G // ¬ Persistent F 131071 C.1}
  let points (C : Components) := selectedComponentPoints F 131071 2130706433 G seeds selected C.1
  have spec (C : Components) (v : Fin 3 → Ω) (hv : v ∈ points C) :=
    selectedComponentPoints_spec F 131071 2130706433 G seeds selected C.1 hdegree hroot hreg v hv
  exact long_proper_selected_count F hp hF hY hT hZ G hG hdiv
    hproper gy gt gz hyt hy ht hz hGy hGt hGz
    (fun C : Components => C.1) Subtype.val_injective (fun C => C.2) points
    (fun C v hv => (spec C v hv).1) (fun C v hv => (spec C v hv).2.1)
    (fun C v hv => (spec C v hv).2.2)

end

end ProximityPrize.SubmissionLower.Koala6844HighSeparated
