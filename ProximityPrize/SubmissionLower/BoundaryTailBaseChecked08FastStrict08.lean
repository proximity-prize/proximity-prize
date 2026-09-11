import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr8p112:∀ i ∈ List.range 1,StrictCheckAt 8 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 112 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 112) 8 112:=by decide +kernel
  exact strictAtFast_sound (row 8 112) 8 112 hvalid hfast

theorem sr8p113:∀ i ∈ List.range 1,StrictCheckAt 8 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 113 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 113) 8 113:=by decide +kernel
  exact strictAtFast_sound (row 8 113) 8 113 hvalid hfast

theorem sr8p114:∀ i ∈ List.range 1,StrictCheckAt 8 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 114 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 114) 8 114:=by decide +kernel
  exact strictAtFast_sound (row 8 114) 8 114 hvalid hfast

theorem sr8p115:∀ i ∈ List.range 1,StrictCheckAt 8 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 115 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 115) 8 115:=by decide +kernel
  exact strictAtFast_sound (row 8 115) 8 115 hvalid hfast

theorem sr8p116:∀ i ∈ List.range 1,StrictCheckAt 8 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 116 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 116) 8 116:=by decide +kernel
  exact strictAtFast_sound (row 8 116) 8 116 hvalid hfast

theorem sr8p117:∀ i ∈ List.range 1,StrictCheckAt 8 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 117 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 117) 8 117:=by decide +kernel
  exact strictAtFast_sound (row 8 117) 8 117 hvalid hfast

theorem sr8p118:∀ i ∈ List.range 1,StrictCheckAt 8 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 118 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 118) 8 118:=by decide +kernel
  exact strictAtFast_sound (row 8 118) 8 118 hvalid hfast

theorem sr8p119:∀ i ∈ List.range 1,StrictCheckAt 8 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 119 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 119) 8 119:=by decide +kernel
  exact strictAtFast_sound (row 8 119) 8 119 hvalid hfast

theorem sr8p120:∀ i ∈ List.range 1,StrictCheckAt 8 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 120 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 120) 8 120:=by decide +kernel
  exact strictAtFast_sound (row 8 120) 8 120 hvalid hfast

theorem sr8p121:∀ i ∈ List.range 1,StrictCheckAt 8 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 121 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 121) 8 121:=by decide +kernel
  exact strictAtFast_sound (row 8 121) 8 121 hvalid hfast

theorem sr8p122:∀ i ∈ List.range 1,StrictCheckAt 8 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 122 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 122) 8 122:=by decide +kernel
  exact strictAtFast_sound (row 8 122) 8 122 hvalid hfast

theorem sr8p123:∀ i ∈ List.range 1,StrictCheckAt 8 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 123 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 123) 8 123:=by decide +kernel
  exact strictAtFast_sound (row 8 123) 8 123 hvalid hfast

theorem sr8p124:∀ i ∈ List.range 1,StrictCheckAt 8 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 124 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 124) 8 124:=by decide +kernel
  exact strictAtFast_sound (row 8 124) 8 124 hvalid hfast

theorem sr8p125:∀ i ∈ List.range 1,StrictCheckAt 8 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 125 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 125) 8 125:=by decide +kernel
  exact strictAtFast_sound (row 8 125) 8 125 hvalid hfast

theorem sr8p126:∀ i ∈ List.range 1,StrictCheckAt 8 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 126 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 126) 8 126:=by decide +kernel
  exact strictAtFast_sound (row 8 126) 8 126 hvalid hfast

theorem sr8p127:∀ i ∈ List.range 1,StrictCheckAt 8 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 127 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 127) 8 127:=by decide +kernel
  exact strictAtFast_sound (row 8 127) 8 127 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
