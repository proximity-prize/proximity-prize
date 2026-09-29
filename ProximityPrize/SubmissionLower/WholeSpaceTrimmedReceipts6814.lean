import ProximityPrize.SubmissionLower.WholeSpaceTrimmedPowerBox6814

/-! Six explicit quotient-dimension receipts needed at the 270e15
threshold. Each receipt evaluates <=16 small (S,R) slices, not the
coefficient space. Exhaustive native-failure coverage is separate. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceTrimmedReceipts6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 15000
open WholeSpacePowerBox6814 WholeSpaceTrimmedPowerBox6814

def box0 : Box := ⟨1,25,25,73,879⟩
def box1 : Box := ⟨1,25,25,74,810⟩
def box2 : Box := ⟨1,25,25,75,740⟩
def box3 : Box := ⟨1,26,26,71,750⟩
def box4 : Box := ⟨1,26,26,72,680⟩
def box5 : Box := ⟨1,26,26,73,611⟩

def Good (a : Box) : Prop :=
  131071*a.U+131069≤a.C ∧ trimReceipt a<2*627003341034

theorem box0_good : Good box0 ∧ trimReceipt box0=2*588477955884 := by unfold Good; decide +kernel
theorem box1_good : Good box1 ∧ trimReceipt box1=2*589985205975 := by unfold Good; decide +kernel
theorem box2_good : Good box2 ∧ trimReceipt box2=2*586698826104 := by unfold Good; decide +kernel
theorem box3_good : Good box3 ∧ trimReceipt box3=2*592656174012 := by unfold Good; decide +kernel
theorem box4_good : Good box4 ∧ trimReceipt box4=2*591875977851 := by unfold Good; decide +kernel
theorem box5_good : Good box5 ∧ trimReceipt box5=2*586185325180 := by unfold Good; decide +kernel

#print axioms box0_good
#print axioms box1_good
#print axioms box2_good
#print axioms box3_good
#print axioms box4_good
#print axioms box5_good
end
end ProximityPrize.SubmissionLower.WholeSpaceTrimmedReceipts6814
