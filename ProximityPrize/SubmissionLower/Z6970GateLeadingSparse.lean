import ProximityPrize.SubmissionLower.Z6970GateLeadingActual
import ProximityPrize.SubmissionLower.Z6970GateTailHoles

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000

namespace Gate6970Leading
open Gate6966Cell
open ExpandedGate6970.H2307Numeric (defaultRow)

def sparseCount (n u c : ℕ) : ℤ :=
  let lo := min n u
  let hi := min n 3514
  let prefixCap := fun m => capPrefix («prefix» stairs) m u c
  prefixCap lo + ((hi-lo : ℕ) : ℤ)*cappedN u u c +
    if n ≤ 3514 then 0 else tailSum (fun q => cappedN q u c) prefixCap (n-3514)

theorem sparseCount_eq (n u c : ℕ) (hn : n ≤ 4025) (hu : u ≤ 1679) :
    sparseCount n u c = count («prefix» stairs) n u c := by
  by_cases h : n ≤ 3514
  · simp [sparseCount,count,h,min_eq_left h,sumUpTo]
  · have cut : min n 3514 = 3514 := min_eq_right (by omega)
    have tail := tailSum_eq (fun q => cappedN q u c)
      (fun m => capPrefix («prefix» stairs) m u c)
      (fun m => capPrefix_eq _ (prefix_eq stairs stairs_checked) m u c hu)
      (n-3514) (show n-3514 ≤ 511 by omega)
    simp only [sparseCount,count,cut,ite_eq_right h,tail]

def sparseAmbient (b j t : ℕ) : ℤ :=
  bif Nat.ble 4024 b && Nat.ble 1679 j && Nat.ble 500 t then 427286700047
  else sparseCount (min 4025 (b+1)) (min j 1679) (min t 500)

theorem sparseAmbient_eq (b j t : ℕ) :
    sparseAmbient b j t = ambient («prefix» stairs) b j t := by
  simp only [sparseAmbient,ambient,sparseCount_eq _ _ _ (min_le_left _ _) (min_le_right _ _)]

def sparseLoss (lv : Lv) (i : ℕ) : ℤ :=
  let (b,j,t,w) := lv.getD i defaultRow
  427286700047 - sparseAmbient b j t + w

theorem sparseLoss_eq (lv : Lv) (i : ℕ) : sparseLoss lv i = loss («prefix» stairs) lv i := by
  simp only [sparseLoss,loss,sparseAmbient_eq]

def sparseMass (lv : Lv) (lo n : ℕ) : ℤ := sumUpTo (fun i => sparseLoss lv (lo+i)) n

theorem sparseMass_eq (lv : Lv) (lo n : ℕ) :
    sparseMass lv lo n = ExpandedGate6970.H2307Numeric.mass lv lo n := by
  rw [← actual_mass]
  simp only [sparseMass,mass,sparseLoss_eq]

end Gate6970Leading
