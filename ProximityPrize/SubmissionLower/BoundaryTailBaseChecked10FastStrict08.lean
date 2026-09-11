import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr10p112:∀ i ∈ List.range 1,StrictCheckAt 10 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 112 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 112) 10 112:=by decide +kernel
  exact strictAtFast_sound (row 10 112) 10 112 hvalid hfast

theorem sr10p113:∀ i ∈ List.range 1,StrictCheckAt 10 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 113 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 113) 10 113:=by decide +kernel
  exact strictAtFast_sound (row 10 113) 10 113 hvalid hfast

theorem sr10p114:∀ i ∈ List.range 1,StrictCheckAt 10 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 114 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 114) 10 114:=by decide +kernel
  exact strictAtFast_sound (row 10 114) 10 114 hvalid hfast

theorem sr10p115:∀ i ∈ List.range 1,StrictCheckAt 10 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 115 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 115) 10 115:=by decide +kernel
  exact strictAtFast_sound (row 10 115) 10 115 hvalid hfast

theorem sr10p116:∀ i ∈ List.range 1,StrictCheckAt 10 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 116 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 116) 10 116:=by decide +kernel
  exact strictAtFast_sound (row 10 116) 10 116 hvalid hfast

theorem sr10p117:∀ i ∈ List.range 1,StrictCheckAt 10 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 117 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 117) 10 117:=by decide +kernel
  exact strictAtFast_sound (row 10 117) 10 117 hvalid hfast

theorem sr10p118:∀ i ∈ List.range 1,StrictCheckAt 10 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 118 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 118) 10 118:=by decide +kernel
  exact strictAtFast_sound (row 10 118) 10 118 hvalid hfast

theorem sr10p119:∀ i ∈ List.range 1,StrictCheckAt 10 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 119 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 119) 10 119:=by decide +kernel
  exact strictAtFast_sound (row 10 119) 10 119 hvalid hfast

theorem sr10p120:∀ i ∈ List.range 1,StrictCheckAt 10 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 120 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 120) 10 120:=by decide +kernel
  exact strictAtFast_sound (row 10 120) 10 120 hvalid hfast

theorem sr10p121:∀ i ∈ List.range 1,StrictCheckAt 10 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 121 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 121) 10 121:=by decide +kernel
  exact strictAtFast_sound (row 10 121) 10 121 hvalid hfast

theorem sr10p122:∀ i ∈ List.range 1,StrictCheckAt 10 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 122 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 122) 10 122:=by decide +kernel
  exact strictAtFast_sound (row 10 122) 10 122 hvalid hfast

theorem sr10p123:∀ i ∈ List.range 1,StrictCheckAt 10 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 123 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 123) 10 123:=by decide +kernel
  exact strictAtFast_sound (row 10 123) 10 123 hvalid hfast

theorem sr10p124:∀ i ∈ List.range 1,StrictCheckAt 10 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 124 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 124) 10 124:=by decide +kernel
  exact strictAtFast_sound (row 10 124) 10 124 hvalid hfast

theorem sr10p125:∀ i ∈ List.range 1,StrictCheckAt 10 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 125 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 125) 10 125:=by decide +kernel
  exact strictAtFast_sound (row 10 125) 10 125 hvalid hfast

theorem sr10p126:∀ i ∈ List.range 1,StrictCheckAt 10 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 126 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 126) 10 126:=by decide +kernel
  exact strictAtFast_sound (row 10 126) 10 126 hvalid hfast

theorem sr10p127:∀ i ∈ List.range 1,StrictCheckAt 10 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 127 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 127) 10 127:=by decide +kernel
  exact strictAtFast_sound (row 10 127) 10 127 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
