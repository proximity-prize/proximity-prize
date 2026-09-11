import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastZero04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr20p64:∀ i ∈ List.range 1,ZeroCheckAt 20 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 64:=by decide +kernel
  exact zeroAtFast_sound 20 64 hfast

theorem zr20p65:∀ i ∈ List.range 1,ZeroCheckAt 20 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 65:=by decide +kernel
  exact zeroAtFast_sound 20 65 hfast

theorem zr20p66:∀ i ∈ List.range 1,ZeroCheckAt 20 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 66:=by decide +kernel
  exact zeroAtFast_sound 20 66 hfast

theorem zr20p67:∀ i ∈ List.range 1,ZeroCheckAt 20 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 67:=by decide +kernel
  exact zeroAtFast_sound 20 67 hfast

theorem zr20p68:∀ i ∈ List.range 1,ZeroCheckAt 20 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 68:=by decide +kernel
  exact zeroAtFast_sound 20 68 hfast

theorem zr20p69:∀ i ∈ List.range 1,ZeroCheckAt 20 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 69:=by decide +kernel
  exact zeroAtFast_sound 20 69 hfast

theorem zr20p70:∀ i ∈ List.range 1,ZeroCheckAt 20 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 70:=by decide +kernel
  exact zeroAtFast_sound 20 70 hfast

theorem zr20p71:∀ i ∈ List.range 1,ZeroCheckAt 20 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 71:=by decide +kernel
  exact zeroAtFast_sound 20 71 hfast

theorem zr20p72:∀ i ∈ List.range 1,ZeroCheckAt 20 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 72:=by decide +kernel
  exact zeroAtFast_sound 20 72 hfast

theorem zr20p73:∀ i ∈ List.range 1,ZeroCheckAt 20 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 73:=by decide +kernel
  exact zeroAtFast_sound 20 73 hfast

theorem zr20p74:∀ i ∈ List.range 1,ZeroCheckAt 20 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 74:=by decide +kernel
  exact zeroAtFast_sound 20 74 hfast

theorem zr20p75:∀ i ∈ List.range 1,ZeroCheckAt 20 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 75:=by decide +kernel
  exact zeroAtFast_sound 20 75 hfast

theorem zr20p76:∀ i ∈ List.range 1,ZeroCheckAt 20 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 76:=by decide +kernel
  exact zeroAtFast_sound 20 76 hfast

theorem zr20p77:∀ i ∈ List.range 1,ZeroCheckAt 20 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 77:=by decide +kernel
  exact zeroAtFast_sound 20 77 hfast

theorem zr20p78:∀ i ∈ List.range 1,ZeroCheckAt 20 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 78:=by decide +kernel
  exact zeroAtFast_sound 20 78 hfast

theorem zr20p79:∀ i ∈ List.range 1,ZeroCheckAt 20 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 79:=by decide +kernel
  exact zeroAtFast_sound 20 79 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
