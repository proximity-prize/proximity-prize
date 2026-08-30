import ProximityPrize.SubmissionLower.ContactFactoredFlagCount

namespace ProximityPrize.SubmissionLower.ContactMovingPositiveLedger
open scoped Classical BigOperators
open ContactFlagBezout ContactFactoredFlagCount
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def surfaceFlag (a b s : ℕ) : FlagDegree := ⟨a,b+1,s+2⟩
def fiberFlag (a b s : ℕ) : FlagDegree := ⟨a,b+1,s+3⟩
def normalFlag (a b s : ℕ) : FlagDegree := ⟨a,b,s⟩
def directionFlag (a b s : ℕ) : FlagDegree := ⟨2*a,2*b+1,2*s+3⟩
def centreFlag (a b s : ℕ) : FlagDegree := unitYZFlag+directionFlag a b s

def weightedMixed (p q r : FlagDegree) : ℕ :=
  r.zOnly*flagMixed p q unitZFlag+r.yz*flagMixed p q unitYZFlag+r.all*flagMixed p q unitAllFlag

theorem weightedMixed_eq (p q r : FlagDegree) : weightedMixed p q r=flagMixed p q r := by
  simp only [weightedMixed,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
  ring

section Cumulative
variable {I : Type*} [Fintype I] (flags : I → FlagDegree) (p : FlagDegree)
variable (hs : (∑ i,(flags i).all) ≤ p.all)
variable (hm : (∑ i,((flags i).yz+(flags i).all)) ≤ p.yz+p.all)
variable (ht : (∑ i,((flags i).zOnly+(flags i).yz+(flags i).all)) ≤ p.zOnly+p.yz+p.all)
include hs hm ht

end Cumulative

end
end ProximityPrize.SubmissionLower.ContactMovingPositiveLedger
