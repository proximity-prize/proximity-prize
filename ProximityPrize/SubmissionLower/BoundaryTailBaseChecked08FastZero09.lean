import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastZero08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr8p128:∀ i ∈ List.range 1,ZeroCheckAt 8 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 128:=by decide +kernel
  exact zeroAtFast_sound 8 128 hfast

theorem zr8p129:∀ i ∈ List.range 1,ZeroCheckAt 8 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 129:=by decide +kernel
  exact zeroAtFast_sound 8 129 hfast

theorem zr8p130:∀ i ∈ List.range 1,ZeroCheckAt 8 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 130:=by decide +kernel
  exact zeroAtFast_sound 8 130 hfast

theorem zr8p131:∀ i ∈ List.range 1,ZeroCheckAt 8 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 131:=by decide +kernel
  exact zeroAtFast_sound 8 131 hfast

theorem zr8p132:∀ i ∈ List.range 1,ZeroCheckAt 8 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 132:=by decide +kernel
  exact zeroAtFast_sound 8 132 hfast

theorem zr8p133:∀ i ∈ List.range 1,ZeroCheckAt 8 (133+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 133:=by decide +kernel
  exact zeroAtFast_sound 8 133 hfast

theorem zr8p134:∀ i ∈ List.range 1,ZeroCheckAt 8 (134+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 134:=by decide +kernel
  exact zeroAtFast_sound 8 134 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
