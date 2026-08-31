import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactNestedFiveCapCoefficientBox6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredOneFamilySelector6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactNestedFiveCapChannelBridge6750Research

open scoped Classical BigOperators
open ContactNestedFiveCapCoefficientBox6750Research
open ContactAnchoredOneFamilySelector6750Research

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 
abbrev NestedChannelIndex (T YS S : Nat) :=
  (y : Fin (min T YS + 1)) ×
    (r : Fin (min S (min (T - y.val) (YS - y.val)) + 1)) ×
      Fin (T + 1 - y.val - r.val)

 

abbrev GroupedChannelIndex (T YS S : Nat) :=
  (u : Fin (min T YS + 1)) ×
    Fin (min S u.val + 1) × Fin (T - u.val + 1)

 


@[ext] structure ChannelWitness (T YS S : Nat) where
  y : Nat
  r : Nat
  u : Nat
  z : Nat
  u_eq : u = y + r
  u_le_T : u ≤ T
  u_le_YS : u ≤ YS
  r_le_S : r ≤ S
  z_lt : z < T - u + 1

 

def nestedChannelEquivWitness (T YS S : Nat) :
    NestedChannelIndex T YS S ≃ ChannelWitness T YS S where
  toFun a := by
    rcases a with ⟨y, r, z⟩
    have hy : y.val ≤ min T YS := Nat.le_of_lt_succ y.isLt
    have hr : r.val ≤ min S (min (T - y.val) (YS - y.val)) :=
      Nat.le_of_lt_succ r.isLt
    refine ⟨y.val, r.val, y.val + r.val, z.val, rfl, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · exact hr.trans (min_le_left _ _)
    · omega
  invFun a := by
    have hu := a.u_eq
    have hT := a.u_le_T
    have hYS := a.u_le_YS
    have hS := a.r_le_S
    have hz := a.z_lt
    let y : Fin (min T YS + 1) := by
      refine ⟨a.y, Nat.lt_succ_iff.mpr ?_⟩
      apply le_min <;> omega
    let r : Fin (min S (min (T - y.val) (YS - y.val)) + 1) := by
      refine ⟨a.r, Nat.lt_succ_iff.mpr ?_⟩
      apply le_min
      · exact a.r_le_S
      · apply le_min <;> dsimp only [y] <;> omega
    let z : Fin (T + 1 - y.val - r.val) := by
      refine ⟨a.z, ?_⟩
      dsimp only [y, r]
      omega
    exact ⟨y, r, z⟩
  left_inv a := by
    rcases a with ⟨y, r, z⟩
    ext <;> rfl
  right_inv a := by
    rcases a with ⟨y, r, u, z, hu, hT, hYS, hS, hz⟩
    ext <;> simp only <;> omega

 

def groupedChannelEquivWitness (T YS S : Nat) :
    GroupedChannelIndex T YS S ≃ ChannelWitness T YS S where
  toFun a := by
    rcases a with ⟨u, r, z⟩
    have hu : u.val ≤ min T YS := Nat.le_of_lt_succ u.isLt
    have hr : r.val ≤ min S u.val := Nat.le_of_lt_succ r.isLt
    refine ⟨u.val - r.val, r.val, u.val, z.val, ?_, ?_, ?_, ?_, z.isLt⟩
    · exact (Nat.sub_add_cancel (hr.trans (min_le_right _ _))).symm
    · exact hu.trans (min_le_left _ _)
    · exact hu.trans (min_le_right _ _)
    · exact hr.trans (min_le_left _ _)
  invFun a := by
    have hu := a.u_eq
    have hT := a.u_le_T
    have hYS := a.u_le_YS
    have hS := a.r_le_S
    have hz := a.z_lt
    let u : Fin (min T YS + 1) :=
      ⟨a.u, Nat.lt_succ_iff.mpr (le_min a.u_le_T a.u_le_YS)⟩
    let r : Fin (min S u.val + 1) := by
      refine ⟨a.r, Nat.lt_succ_iff.mpr ?_⟩
      apply le_min
      · exact a.r_le_S
      · dsimp only [u]
        omega
    let z : Fin (T - u.val + 1) := by
      refine ⟨a.z, ?_⟩
      simpa only [u] using a.z_lt
    exact ⟨u, r, z⟩
  left_inv a := by
    rcases a with ⟨u, r, z⟩
    ext <;> rfl
  right_inv a := by
    rcases a with ⟨y, r, u, z, hu, hT, hYS, hS, hz⟩
    have hru : r ≤ u := by omega
    ext <;> simp only <;> omega

 
def nestedChannelEquivGroupedChannel (T YS S : Nat) :
    NestedChannelIndex T YS S ≃ GroupedChannelIndex T YS S :=
  (nestedChannelEquivWitness T YS S).trans
    (groupedChannelEquivWitness T YS S).symm

theorem nestedFiveCapChannelCount_eq_channelCount (T YS S : Nat) :
    nestedFiveCapChannelCount T YS S = channelCount T YS S := by
  calc
    nestedFiveCapChannelCount T YS S =
        Fintype.card (NestedChannelIndex T YS S) := by
      rw [nestedFiveCapChannelCount, Finset.sum_range]
      simp_rw [Finset.sum_range]
      simp [NestedChannelIndex, Fintype.card_sigma]
    _ = Fintype.card (GroupedChannelIndex T YS S) :=
      Fintype.card_congr (nestedChannelEquivGroupedChannel T YS S)
    _ = channelCount T YS S := by
      rw [channelCount, Finset.sum_range]
      simp [GroupedChannelIndex, Fintype.card_sigma]

end ContactNestedFiveCapChannelBridge6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapChannelBridge6750Research.nestedFiveCapChannelCount_eq_channelCount
