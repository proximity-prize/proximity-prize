import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastZero04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr8p64:∀ i ∈ List.range 1,ZeroCheckAt 8 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 64:=by decide +kernel
  exact zeroAtFast_sound 8 64 hfast

theorem zr8p65:∀ i ∈ List.range 1,ZeroCheckAt 8 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 65:=by decide +kernel
  exact zeroAtFast_sound 8 65 hfast

theorem zr8p66:∀ i ∈ List.range 1,ZeroCheckAt 8 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 66:=by decide +kernel
  exact zeroAtFast_sound 8 66 hfast

theorem zr8p67:∀ i ∈ List.range 1,ZeroCheckAt 8 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 67:=by decide +kernel
  exact zeroAtFast_sound 8 67 hfast

theorem zr8p68:∀ i ∈ List.range 1,ZeroCheckAt 8 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 68:=by decide +kernel
  exact zeroAtFast_sound 8 68 hfast

theorem zr8p69:∀ i ∈ List.range 1,ZeroCheckAt 8 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 69:=by decide +kernel
  exact zeroAtFast_sound 8 69 hfast

theorem zr8p70:∀ i ∈ List.range 1,ZeroCheckAt 8 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 70:=by decide +kernel
  exact zeroAtFast_sound 8 70 hfast

theorem zr8p71:∀ i ∈ List.range 1,ZeroCheckAt 8 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 71:=by decide +kernel
  exact zeroAtFast_sound 8 71 hfast

theorem zr8p72:∀ i ∈ List.range 1,ZeroCheckAt 8 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 72:=by decide +kernel
  exact zeroAtFast_sound 8 72 hfast

theorem zr8p73:∀ i ∈ List.range 1,ZeroCheckAt 8 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 73:=by decide +kernel
  exact zeroAtFast_sound 8 73 hfast

theorem zr8p74:∀ i ∈ List.range 1,ZeroCheckAt 8 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 74:=by decide +kernel
  exact zeroAtFast_sound 8 74 hfast

theorem zr8p75:∀ i ∈ List.range 1,ZeroCheckAt 8 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 75:=by decide +kernel
  exact zeroAtFast_sound 8 75 hfast

theorem zr8p76:∀ i ∈ List.range 1,ZeroCheckAt 8 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 76:=by decide +kernel
  exact zeroAtFast_sound 8 76 hfast

theorem zr8p77:∀ i ∈ List.range 1,ZeroCheckAt 8 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 77:=by decide +kernel
  exact zeroAtFast_sound 8 77 hfast

theorem zr8p78:∀ i ∈ List.range 1,ZeroCheckAt 8 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 78:=by decide +kernel
  exact zeroAtFast_sound 8 78 hfast

theorem zr8p79:∀ i ∈ List.range 1,ZeroCheckAt 8 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 79:=by decide +kernel
  exact zeroAtFast_sound 8 79 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
