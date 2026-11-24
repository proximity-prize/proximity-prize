import ProximityPrize.SubmissionLower.R6961RetainedCompressionFactors

set_option Elab.async false
namespace Lower6961.MarkedEvaluation
open RetainedCompression

/-- Charge for counting a single determinant evaluated at multiple abscissas.
The extra eight scalar-degree units per complementary sheet fit the live rectangles. -/
def rate (e:ℕ) := (9*e+2)*(e-1)+2*e-1

/-- At twist s-1, the generic vertical section rank is at most e*s-s.
A marked sheet contributes s residues before its normalization-index loss.
The shared determinant can spend one e-th of a pole per evaluation row. -/
theorem price {N e s t loss obstructions ordinary meromorphic rank pole : ℕ}
    (positive : 0<s) (ep : 0<e) (rank_bound : rank+s≤e*s)
    (collision : loss≤8*s*t) (surface : obstructions≤s+s*t) (constants : s≤ordinary)
    (lift : N*s+ordinary≤loss+obstructions+meromorphic)
    (generated : meromorphic≤rank+pole) (orbit : e*pole≤N*rank) :
    N≤9*e*t+e*(e-1) := by
  have before : N*s+ordinary ≤ 8*s*t+(s+s*t)+(rank+pole) :=
    lift.trans (Nat.add_le_add (Nat.add_le_add collision surface) generated)
  have cancel : N*s ≤ 8*s*t+s*t+rank+pole := by omega
  have scaled := Nat.mul_le_mul_left e cancel
  have share := Nat.mul_le_mul_left N rank_bound
  have rankCost:=Nat.mul_le_mul_left e rank_bound
  have first : (N*s)*e ≤ (8*s*t+s*t)*e+e*rank+N*rank := by
    calc _ = e*(N*s) := Nat.mul_comm ..
         _ ≤ _ := scaled.trans (by nlinarith only [orbit])
  have paid : N*s+s*e≤9*e*t*s+(e*e)*s := by nlinarith only [first,share,rankCost]
  have equal : 9*e*t*s+(e*e)*s=(9*e*t+e*(e-1))*s+s*e := by
    obtain ⟨k,eq⟩:=Nat.exists_eq_succ_of_ne_zero ep.ne'
    rw [eq,Nat.succ_sub_one,Nat.succ_eq_add_one]; ring
  rw [equal] at paid
  exact Nat.le_of_mul_le_mul_right (Nat.le_of_add_le_add_right paid) positive

#print axioms price
end Lower6961.MarkedEvaluation
