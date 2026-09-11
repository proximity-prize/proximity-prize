import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastZero08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr7p128:∀ i ∈ List.range 1,ZeroCheckAt 7 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 128:=by decide +kernel
  exact zeroAtFast_sound 7 128 hfast

theorem zr7p129:∀ i ∈ List.range 1,ZeroCheckAt 7 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 129:=by decide +kernel
  exact zeroAtFast_sound 7 129 hfast

theorem zr7p130:∀ i ∈ List.range 1,ZeroCheckAt 7 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 130:=by decide +kernel
  exact zeroAtFast_sound 7 130 hfast

theorem zr7p131:∀ i ∈ List.range 1,ZeroCheckAt 7 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 131:=by decide +kernel
  exact zeroAtFast_sound 7 131 hfast

theorem zr7p132:∀ i ∈ List.range 1,ZeroCheckAt 7 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 132:=by decide +kernel
  exact zeroAtFast_sound 7 132 hfast

theorem zr7p133:∀ i ∈ List.range 1,ZeroCheckAt 7 (133+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 133:=by decide +kernel
  exact zeroAtFast_sound 7 133 hfast

theorem zr7p134:∀ i ∈ List.range 1,ZeroCheckAt 7 (134+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 134:=by decide +kernel
  exact zeroAtFast_sound 7 134 hfast

theorem zr7p135:∀ i ∈ List.range 1,ZeroCheckAt 7 (135+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 135:=by decide +kernel
  exact zeroAtFast_sound 7 135 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
