import ProximityPrize.SubmissionLower.MovingSourcePairStageWithLeading6814

/-! Scalar mixed-degree bounds for the actual cofactor degree charges.
The half-size arm uses its coupled budget, not independent full caps. -/
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

private theorem half_yz (a b z v : ℕ) (ha : a≤15)
    (hr : a+b≤31) (hl : a+z≤504) (ht : a+b+z+v≤1714) :
    a*b+z*b+v*a≤25974 := by
  have h1 := Nat.mul_le_mul_left a ht
  have h2 := Nat.mul_le_mul_left z hr
  have h3 := Nat.mul_le_mul_left (31-2*a) hl
  have hc : 31-2*a+2*a=31 := by omega
  have he : (31-2*a)*(a+z)+2*a*(a+z)=31*(a+z) := by rw [←Nat.add_mul,hc]
  nlinarith [Nat.mul_le_mul ha ha]

private theorem half_all (a b z v : ℕ) (ha : a≤56)
    (hr : a+b≤112) (hl : a+z≤504) (ht : a+b+z+v≤1714) :
    a*b+z*b+v*a≤92848 := by
  have h1 := Nat.mul_le_mul_left a ht
  have h2 := Nat.mul_le_mul_left z hr
  have h3 := Nat.mul_le_mul_left (112-2*a) hl
  have hc : 112-2*a+2*a=112 := by omega
  have he : (112-2*a)*(a+z)+2*a*(a+z)=112*(a+z) := by rw [←Nat.add_mul,hc]
  nlinarith [Nat.mul_le_mul ha ha]

theorem half_pair_bounds (p q : FlagDegree)
    (hpR : p.all≤15) (hpY : p.yz+p.all≤56) (hpT : p.zOnly+p.yz+p.all≤504)
    (hR : p.all+q.all≤31)
    (hY : p.yz+p.all+q.yz+q.all≤112)
    (hT : p.zOnly+p.yz+p.all+q.zOnly+q.yz+q.all≤1714) :
    flagMixed p q unitYZFlag≤25974 ∧ flagMixed p q unitAllFlag≤92848 := by
  have hy := half_yz p.all q.all (p.zOnly+p.yz) (q.zOnly+q.yz) hpR hR (by omega) (by omega)
  have ha := half_all (p.yz+p.all) (q.yz+q.all) p.zOnly q.zOnly hpY (by omega) (by omega) (by omega)
  constructor
  · convert hy using 1 <;> simp only [flagMixed,unitYZFlag] <;> ring
  · convert ha using 1 <;> simp only [flagMixed,unitAllFlag] <;> ring

#print axioms half_pair_bounds
end
end ProximityPrize.SubmissionLower.MovingSourcePairEnvelope6814
