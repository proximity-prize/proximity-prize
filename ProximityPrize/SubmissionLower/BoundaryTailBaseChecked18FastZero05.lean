import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastZero04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr18p64:∀ i ∈ List.range 1,ZeroCheckAt 18 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 64:=by decide +kernel
  exact zeroAtFast_sound 18 64 hfast

theorem zr18p65:∀ i ∈ List.range 1,ZeroCheckAt 18 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 65:=by decide +kernel
  exact zeroAtFast_sound 18 65 hfast

theorem zr18p66:∀ i ∈ List.range 1,ZeroCheckAt 18 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 66:=by decide +kernel
  exact zeroAtFast_sound 18 66 hfast

theorem zr18p67:∀ i ∈ List.range 1,ZeroCheckAt 18 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 67:=by decide +kernel
  exact zeroAtFast_sound 18 67 hfast

theorem zr18p68:∀ i ∈ List.range 1,ZeroCheckAt 18 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 68:=by decide +kernel
  exact zeroAtFast_sound 18 68 hfast

theorem zr18p69:∀ i ∈ List.range 1,ZeroCheckAt 18 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 69:=by decide +kernel
  exact zeroAtFast_sound 18 69 hfast

theorem zr18p70:∀ i ∈ List.range 1,ZeroCheckAt 18 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 70:=by decide +kernel
  exact zeroAtFast_sound 18 70 hfast

theorem zr18p71:∀ i ∈ List.range 1,ZeroCheckAt 18 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 71:=by decide +kernel
  exact zeroAtFast_sound 18 71 hfast

theorem zr18p72:∀ i ∈ List.range 1,ZeroCheckAt 18 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 72:=by decide +kernel
  exact zeroAtFast_sound 18 72 hfast

theorem zr18p73:∀ i ∈ List.range 1,ZeroCheckAt 18 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 73:=by decide +kernel
  exact zeroAtFast_sound 18 73 hfast

theorem zr18p74:∀ i ∈ List.range 1,ZeroCheckAt 18 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 74:=by decide +kernel
  exact zeroAtFast_sound 18 74 hfast

theorem zr18p75:∀ i ∈ List.range 1,ZeroCheckAt 18 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 75:=by decide +kernel
  exact zeroAtFast_sound 18 75 hfast

theorem zr18p76:∀ i ∈ List.range 1,ZeroCheckAt 18 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 76:=by decide +kernel
  exact zeroAtFast_sound 18 76 hfast

theorem zr18p77:∀ i ∈ List.range 1,ZeroCheckAt 18 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 77:=by decide +kernel
  exact zeroAtFast_sound 18 77 hfast

theorem zr18p78:∀ i ∈ List.range 1,ZeroCheckAt 18 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 78:=by decide +kernel
  exact zeroAtFast_sound 18 78 hfast

theorem zr18p79:∀ i ∈ List.range 1,ZeroCheckAt 18 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 79:=by decide +kernel
  exact zeroAtFast_sound 18 79 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
