import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr21p112:∀ i ∈ List.range 1,StrictCheckAt 21 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 112 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 112) 21 112:=by decide +kernel
  exact strictAtFast_sound (row 21 112) 21 112 hvalid hfast

theorem sr21p113:∀ i ∈ List.range 1,StrictCheckAt 21 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 113 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 113) 21 113:=by decide +kernel
  exact strictAtFast_sound (row 21 113) 21 113 hvalid hfast

theorem sr21p114:∀ i ∈ List.range 1,StrictCheckAt 21 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 114 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 114) 21 114:=by decide +kernel
  exact strictAtFast_sound (row 21 114) 21 114 hvalid hfast

theorem sr21p115:∀ i ∈ List.range 1,StrictCheckAt 21 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 115 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 115) 21 115:=by decide +kernel
  exact strictAtFast_sound (row 21 115) 21 115 hvalid hfast

theorem sr21p116:∀ i ∈ List.range 1,StrictCheckAt 21 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 116 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 116) 21 116:=by decide +kernel
  exact strictAtFast_sound (row 21 116) 21 116 hvalid hfast

theorem sr21p117:∀ i ∈ List.range 1,StrictCheckAt 21 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 117 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 117) 21 117:=by decide +kernel
  exact strictAtFast_sound (row 21 117) 21 117 hvalid hfast

theorem sr21p118:∀ i ∈ List.range 1,StrictCheckAt 21 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 118 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 118) 21 118:=by decide +kernel
  exact strictAtFast_sound (row 21 118) 21 118 hvalid hfast

theorem sr21p119:∀ i ∈ List.range 1,StrictCheckAt 21 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 119 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 119) 21 119:=by decide +kernel
  exact strictAtFast_sound (row 21 119) 21 119 hvalid hfast

theorem sr21p120:∀ i ∈ List.range 1,StrictCheckAt 21 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 120 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 120) 21 120:=by decide +kernel
  exact strictAtFast_sound (row 21 120) 21 120 hvalid hfast

theorem sr21p121:∀ i ∈ List.range 1,StrictCheckAt 21 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 121 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 121) 21 121:=by decide +kernel
  exact strictAtFast_sound (row 21 121) 21 121 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
