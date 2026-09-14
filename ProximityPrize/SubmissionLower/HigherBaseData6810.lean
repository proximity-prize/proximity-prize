import ProximityPrize.SubmissionLower.HigherAffineRateData6810

namespace ProximityPrize.SubmissionLower.HigherBaseData6810
open LocatorPhase6800Oracle
set_option autoImplicit false
set_option maxRecDepth 100000

def defaultRow : BaseRow := ⟨0,0,0,0,0,[]⟩
def lookup (r v : ℕ) : BaseRow :=
  if 1≤r ∧ r≤34 ∧ r+v≤156 then
    let b := r*HigherAffineRateData6810.rate r v
    ⟨r,v,b,b+HigherAffineSingleton6810.slope,b+2*HigherAffineSingleton6810.slope,
      [⟨3,b+3*HigherAffineSingleton6810.slope,HigherAffineSingleton6810.slope⟩]⟩
  else defaultRow
def cap (p : RCN095.FlagDegree) : ℕ := (lookup p.all p.yz).evalAt p.zOnly

end ProximityPrize.SubmissionLower.HigherBaseData6810
