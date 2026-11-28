import ProximityPrize.SubmissionLower.Z6970CompanionRegistry

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

def rule0 : Rule := ⟨0,⟨123,5,1⟩,false,13908324562457638⟩

def rule1 : Rule := ⟨0,⟨54,15,1⟩,false,22940588105726584⟩

def rule2 : Rule := ⟨0,⟨124,10,3⟩,false,25261884590037539⟩

def rule3 : Rule := ⟨0,⟨52,4,1⟩,false,7277877017449032⟩

def rule4 : Rule := ⟨0,⟨7,10,1⟩,false,16028451824349056⟩

def rule5 : Rule := ⟨0,⟨49,16,2⟩,false,25261884590037539⟩

def rule6 : Rule := ⟨0,⟨7,18,4⟩,true,6572347837558208⟩

def rule7 : Rule := ⟨0,⟨58,14,1⟩,false,22940588105726584⟩

def rule8 : Rule := ⟨0,⟨62,13,1⟩,false,22940588105726584⟩

def rule9 : Rule := ⟨0,⟨10,15,2⟩,false,22064481967072149⟩

def rule10 : Rule := ⟨0,⟨38,18,2⟩,false,25261884590037539⟩

def rule11 : Rule := ⟨0,⟨125,10,2⟩,false,25261884590037539⟩

def rule12 : Rule := ⟨2,⟨19,13,1⟩,false,3570788005668000⟩

def rule13 : Rule := ⟨2,⟨4,10,2⟩,false,2865653131914797⟩

def rule14 : Rule := ⟨3,⟨18,13,1⟩,false,3285684089007720⟩

def rule15 : Rule := ⟨3,⟨3,8,2⟩,false,2865635836600980⟩

def rule16 : Rule := ⟨4,⟨15,13,1⟩,false,3000588283283676⟩

def rule17 : Rule := ⟨5,⟨12,13,1⟩,false,2865635836600980⟩

def rule18 : Rule := ⟨6,⟨9,13,1⟩,false,2865618541287163⟩

def rule19 : Rule := ⟨7,⟨8,13,1⟩,false,2167821865059093⟩

def rule20 : Rule := ⟨8,⟨5,11,1⟩,false,1430783657172211⟩

def rule21 : Rule := ⟨9,⟨2,5,1⟩,false,1005118269738545⟩

def rule22 : Rule := ⟨10,⟨9,12,1⟩,false,1668452430029632⟩

def rule23 : Rule := ⟨11,⟨6,12,1⟩,false,1668445592710835⟩

def rule24 : Rule := ⟨12,⟨2,5,1⟩,false,1005118269738545⟩

def rule25 : Rule := ⟨13,⟨6,12,1⟩,false,1589275447697825⟩

def rule26 : Rule := ⟨14,⟨2,5,1⟩,false,1005118269738545⟩

def rule27 : Rule := ⟨17,⟨1,3,1⟩,false,145518067411104⟩

def rule28 : Rule := ⟨20,⟨4,9,1⟩,false,574383712170791⟩

def rules : List Rule := [rule0,rule1,rule2,rule3,rule4,rule5,rule6,rule7,rule8,rule9,rule10,rule11,rule12,rule13,rule14,rule15,rule16,rule17,rule18,rule19,rule20,rule21,rule22,rule23,rule24,rule25,rule26,rule27,rule28]

def book (k : ℕ) (r : Shape) : Option ℕ := fromRules k r rules

end Height2307Companion
