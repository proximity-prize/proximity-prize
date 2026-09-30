import ProximityPrize.SubmissionLower.MovingSourcePairStageWithLeading6814
namespace ProximityPrize.SubmissionLower.MovingSourcePairEnvelope6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN084 RCN095

def CumulativeLe (p q : FlagDegree) : Prop :=
  p.all≤q.all ∧ p.yz+p.all≤q.yz+q.all ∧ p.zOnly+p.yz+p.all≤q.zOnly+q.yz+q.all

theorem mixed_mono_left (p p' q r : FlagDegree) (h : CumulativeLe p p') :
    flagMixed p q r≤flagMixed p' q r := by
  have hh := sum_flagMixed_le_of_cumulative (fun _ : Fin 1 => p) p' q r
    (by simpa using h.1) (by simpa using h.2.1) (by simpa using h.2.2)
  simpa using hh

theorem mixed_swap_left (p q r : FlagDegree) : flagMixed p q r=flagMixed q p r := by
  simp only [flagMixed]
  ring

theorem mixed_mono_pair (p q p' q' r : FlagDegree)
    (hp : CumulativeLe p p') (hq : CumulativeLe q q') :
    flagMixed p q r≤flagMixed p' q' r := by
  apply (mixed_mono_left p p' q r hp).trans
  rw [mixed_swap_left p' q r,mixed_swap_left p' q' r]
  exact mixed_mono_left q q' p' r hq

end
end ProximityPrize.SubmissionLower.MovingSourcePairEnvelope6814
