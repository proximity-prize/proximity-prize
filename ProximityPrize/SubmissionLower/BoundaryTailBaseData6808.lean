import ProximityPrize.SubmissionLower.AffineRateData6808

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseData6808
open LocatorPhase6800Oracle
set_option autoImplicit false
set_option maxRecDepth 100000

def defaultRow : BaseRow := ⟨0,0,0,0,0,[]⟩
def lookup (r v : ℕ) : BaseRow :=
  if 1≤r ∧ r≤32 ∧ r+v≤149 then
    let b := r*AffineRateData6808.rate r v
    ⟨r,v,b,b+AffineSingleton6808.slope,b+2*AffineSingleton6808.slope,
      [⟨3,b+3*AffineSingleton6808.slope,AffineSingleton6808.slope⟩]⟩
  else defaultRow
def cap (p : RCN095.FlagDegree) : ℕ := (lookup p.all p.yz).evalAt p.zOnly

end ProximityPrize.SubmissionLower.BoundaryTailBaseData6808
