import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastZero04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr25p64:∀ i ∈ List.range 1,ZeroCheckAt 25 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 64:=by decide +kernel
  exact zeroAtFast_sound 25 64 hfast

theorem zr25p65:∀ i ∈ List.range 1,ZeroCheckAt 25 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 65:=by decide +kernel
  exact zeroAtFast_sound 25 65 hfast

theorem zr25p66:∀ i ∈ List.range 1,ZeroCheckAt 25 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 66:=by decide +kernel
  exact zeroAtFast_sound 25 66 hfast

theorem zr25p67:∀ i ∈ List.range 1,ZeroCheckAt 25 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 67:=by decide +kernel
  exact zeroAtFast_sound 25 67 hfast

theorem zr25p68:∀ i ∈ List.range 1,ZeroCheckAt 25 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 68:=by decide +kernel
  exact zeroAtFast_sound 25 68 hfast

theorem zr25p69:∀ i ∈ List.range 1,ZeroCheckAt 25 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 69:=by decide +kernel
  exact zeroAtFast_sound 25 69 hfast

theorem zr25p70:∀ i ∈ List.range 1,ZeroCheckAt 25 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 70:=by decide +kernel
  exact zeroAtFast_sound 25 70 hfast

theorem zr25p71:∀ i ∈ List.range 1,ZeroCheckAt 25 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 71:=by decide +kernel
  exact zeroAtFast_sound 25 71 hfast

theorem zr25p72:∀ i ∈ List.range 1,ZeroCheckAt 25 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 72:=by decide +kernel
  exact zeroAtFast_sound 25 72 hfast

theorem zr25p73:∀ i ∈ List.range 1,ZeroCheckAt 25 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 73:=by decide +kernel
  exact zeroAtFast_sound 25 73 hfast

theorem zr25p74:∀ i ∈ List.range 1,ZeroCheckAt 25 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 74:=by decide +kernel
  exact zeroAtFast_sound 25 74 hfast

theorem zr25p75:∀ i ∈ List.range 1,ZeroCheckAt 25 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 75:=by decide +kernel
  exact zeroAtFast_sound 25 75 hfast

theorem zr25p76:∀ i ∈ List.range 1,ZeroCheckAt 25 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 76:=by decide +kernel
  exact zeroAtFast_sound 25 76 hfast

theorem zr25p77:∀ i ∈ List.range 1,ZeroCheckAt 25 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 77:=by decide +kernel
  exact zeroAtFast_sound 25 77 hfast

theorem zr25p78:∀ i ∈ List.range 1,ZeroCheckAt 25 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 78:=by decide +kernel
  exact zeroAtFast_sound 25 78 hfast

theorem zr25p79:∀ i ∈ List.range 1,ZeroCheckAt 25 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 79:=by decide +kernel
  exact zeroAtFast_sound 25 79 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
