import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastZero04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr30p64:∀ i ∈ List.range 1,ZeroCheckAt 30 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 64:=by decide +kernel
  exact zeroAtFast_sound 30 64 hfast

theorem zr30p65:∀ i ∈ List.range 1,ZeroCheckAt 30 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 65:=by decide +kernel
  exact zeroAtFast_sound 30 65 hfast

theorem zr30p66:∀ i ∈ List.range 1,ZeroCheckAt 30 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 66:=by decide +kernel
  exact zeroAtFast_sound 30 66 hfast

theorem zr30p67:∀ i ∈ List.range 1,ZeroCheckAt 30 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 67:=by decide +kernel
  exact zeroAtFast_sound 30 67 hfast

theorem zr30p68:∀ i ∈ List.range 1,ZeroCheckAt 30 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 68:=by decide +kernel
  exact zeroAtFast_sound 30 68 hfast

theorem zr30p69:∀ i ∈ List.range 1,ZeroCheckAt 30 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 69:=by decide +kernel
  exact zeroAtFast_sound 30 69 hfast

theorem zr30p70:∀ i ∈ List.range 1,ZeroCheckAt 30 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 70:=by decide +kernel
  exact zeroAtFast_sound 30 70 hfast

theorem zr30p71:∀ i ∈ List.range 1,ZeroCheckAt 30 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 71:=by decide +kernel
  exact zeroAtFast_sound 30 71 hfast

theorem zr30p72:∀ i ∈ List.range 1,ZeroCheckAt 30 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 72:=by decide +kernel
  exact zeroAtFast_sound 30 72 hfast

theorem zr30p73:∀ i ∈ List.range 1,ZeroCheckAt 30 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 73:=by decide +kernel
  exact zeroAtFast_sound 30 73 hfast

theorem zr30p74:∀ i ∈ List.range 1,ZeroCheckAt 30 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 74:=by decide +kernel
  exact zeroAtFast_sound 30 74 hfast

theorem zr30p75:∀ i ∈ List.range 1,ZeroCheckAt 30 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 75:=by decide +kernel
  exact zeroAtFast_sound 30 75 hfast

theorem zr30p76:∀ i ∈ List.range 1,ZeroCheckAt 30 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 76:=by decide +kernel
  exact zeroAtFast_sound 30 76 hfast

theorem zr30p77:∀ i ∈ List.range 1,ZeroCheckAt 30 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 77:=by decide +kernel
  exact zeroAtFast_sound 30 77 hfast

theorem zr30p78:∀ i ∈ List.range 1,ZeroCheckAt 30 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 78:=by decide +kernel
  exact zeroAtFast_sound 30 78 hfast

theorem zr30p79:∀ i ∈ List.range 1,ZeroCheckAt 30 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 79:=by decide +kernel
  exact zeroAtFast_sound 30 79 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
