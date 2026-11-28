import ProximityPrize.SubmissionLower.Gate6966Assm

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ExpandedGate6970.H2307Slope
open Gate6966Cell

def gradeCap (q : ℕ) : ℕ :=
  min q (if q < 3514 then 1679 else (131312 - 26*q)/25)

def dimLower (r : ℕ) : ℤ :=
  let b := min 4025 (r*62+1)
  let j := min 1679 (r*28)
  let t := min 500 (r*7)
  sumUpTo (fun k =>
    let a := 16*k
    let z := min b (16*(k+1))
    ((z-a : ℕ) : ℤ) * cappedN (min (gradeCap a) (gradeCap (z-1))) j t)
    ((b+15)/16)

def rowLoss (i : ℕ) : ℤ := 427286700047 - dimLower (i+1)

def mass (lo len : ℕ) : ℤ := sumUpTo (fun i => rowLoss (lo+i)) len

theorem mass_add (lo a b : ℕ) : mass lo (a+b) = mass lo a + mass (lo+a) b := by
  induction b with
  | zero => simp [mass, sumUpTo]
  | succ b ih =>
      change mass lo (a+b) + rowLoss (lo+(a+b)) =
        mass lo a + (mass (lo+a) b + rowLoss (lo+a+b))
      rw [ih, Nat.add_assoc lo a b, add_assoc]

private theorem piece0 : mass 0 3 = 1281856955751 := by decide +kernel
private theorem piece3 : mass 3 3 = 1281793020463 := by decide +kernel
private theorem piece6 : mass 6 3 = 1281463739997 := by decide +kernel
private theorem piece9 : mass 9 3 = 1280493033411 := by decide +kernel
private theorem piece12 : mass 12 3 = 1278332840296 := by decide +kernel
private theorem piece15 : mass 15 3 = 1274263137980 := by decide +kernel
private theorem piece18 : mass 18 3 = 1267391933096 := by decide +kernel
private theorem piece21 : mass 21 3 = 1256655255290 := by decide +kernel
private theorem piece24 : mass 24 3 = 1240817176317 := by decide +kernel
private theorem piece27 : mass 27 3 = 1218469787981 := by decide +kernel
private theorem piece30 : mass 30 3 = 1188033214823 := by decide +kernel
private theorem piece33 : mass 33 3 = 1147755617365 := by decide +kernel
private theorem piece36 : mass 36 3 = 1095713176838 := by decide +kernel
private theorem piece39 : mass 39 3 = 1029810110994 := by decide +kernel
private theorem piece42 : mass 42 3 = 947778669146 := by decide +kernel
private theorem piece45 : mass 45 3 = 847179121604 := by decide +kernel
private theorem piece48 : mass 48 3 = 725399781587 := by decide +kernel
private theorem piece51 : mass 51 3 = 579656982251 := by decide +kernel
private theorem piece54 : mass 54 3 = 406995101222 := by decide +kernel
private theorem piece57 : mass 57 3 = 205094808407 := by decide +kernel
private theorem piece60 : mass 60 3 = 81089076056 := by decide +kernel
private theorem piece63 : mass 63 3 = 17067050514 := by decide +kernel
private theorem piece66 : mass 66 3 = 6353110548 := by decide +kernel
private theorem piece69 : mass 69 2 = 2680744354 := by decide +kernel

theorem exactMass : mass 0 71 = 20942143446291 := by
  have h0 : mass 0 0 = 0 := rfl
  have h3 : mass 0 3 = 1281856955751 := by
    rw [show (3 : ℕ) = 0+3 by rfl, mass_add, h0]
    change _ + mass 0 3 = _
    rw [piece0]
    rfl
  have h6 : mass 0 6 = 2563649976214 := by
    rw [show (6 : ℕ) = 3+3 by rfl, mass_add, h3]
    change _ + mass 3 3 = _
    rw [piece3]
    rfl
  have h9 : mass 0 9 = 3845113716211 := by
    rw [show (9 : ℕ) = 6+3 by rfl, mass_add, h6]
    change _ + mass 6 3 = _
    rw [piece6]
    rfl
  have h12 : mass 0 12 = 5125606749622 := by
    rw [show (12 : ℕ) = 9+3 by rfl, mass_add, h9]
    change _ + mass 9 3 = _
    rw [piece9]
    rfl
  have h15 : mass 0 15 = 6403939589918 := by
    rw [show (15 : ℕ) = 12+3 by rfl, mass_add, h12]
    change _ + mass 12 3 = _
    rw [piece12]
    rfl
  have h18 : mass 0 18 = 7678202727898 := by
    rw [show (18 : ℕ) = 15+3 by rfl, mass_add, h15]
    change _ + mass 15 3 = _
    rw [piece15]
    rfl
  have h21 : mass 0 21 = 8945594660994 := by
    rw [show (21 : ℕ) = 18+3 by rfl, mass_add, h18]
    change _ + mass 18 3 = _
    rw [piece18]
    rfl
  have h24 : mass 0 24 = 10202249916284 := by
    rw [show (24 : ℕ) = 21+3 by rfl, mass_add, h21]
    change _ + mass 21 3 = _
    rw [piece21]
    rfl
  have h27 : mass 0 27 = 11443067092601 := by
    rw [show (27 : ℕ) = 24+3 by rfl, mass_add, h24]
    change _ + mass 24 3 = _
    rw [piece24]
    rfl
  have h30 : mass 0 30 = 12661536880582 := by
    rw [show (30 : ℕ) = 27+3 by rfl, mass_add, h27]
    change _ + mass 27 3 = _
    rw [piece27]
    rfl
  have h33 : mass 0 33 = 13849570095405 := by
    rw [show (33 : ℕ) = 30+3 by rfl, mass_add, h30]
    change _ + mass 30 3 = _
    rw [piece30]
    rfl
  have h36 : mass 0 36 = 14997325712770 := by
    rw [show (36 : ℕ) = 33+3 by rfl, mass_add, h33]
    change _ + mass 33 3 = _
    rw [piece33]
    rfl
  have h39 : mass 0 39 = 16093038889608 := by
    rw [show (39 : ℕ) = 36+3 by rfl, mass_add, h36]
    change _ + mass 36 3 = _
    rw [piece36]
    rfl
  have h42 : mass 0 42 = 17122849000602 := by
    rw [show (42 : ℕ) = 39+3 by rfl, mass_add, h39]
    change _ + mass 39 3 = _
    rw [piece39]
    rfl
  have h45 : mass 0 45 = 18070627669748 := by
    rw [show (45 : ℕ) = 42+3 by rfl, mass_add, h42]
    change _ + mass 42 3 = _
    rw [piece42]
    rfl
  have h48 : mass 0 48 = 18917806791352 := by
    rw [show (48 : ℕ) = 45+3 by rfl, mass_add, h45]
    change _ + mass 45 3 = _
    rw [piece45]
    rfl
  have h51 : mass 0 51 = 19643206572939 := by
    rw [show (51 : ℕ) = 48+3 by rfl, mass_add, h48]
    change _ + mass 48 3 = _
    rw [piece48]
    rfl
  have h54 : mass 0 54 = 20222863555190 := by
    rw [show (54 : ℕ) = 51+3 by rfl, mass_add, h51]
    change _ + mass 51 3 = _
    rw [piece51]
    rfl
  have h57 : mass 0 57 = 20629858656412 := by
    rw [show (57 : ℕ) = 54+3 by rfl, mass_add, h54]
    change _ + mass 54 3 = _
    rw [piece54]
    rfl
  have h60 : mass 0 60 = 20834953464819 := by
    rw [show (60 : ℕ) = 57+3 by rfl, mass_add, h57]
    change _ + mass 57 3 = _
    rw [piece57]
    rfl
  have h63 : mass 0 63 = 20916042540875 := by
    rw [show (63 : ℕ) = 60+3 by rfl, mass_add, h60]
    change _ + mass 60 3 = _
    rw [piece60]
    rfl
  have h66 : mass 0 66 = 20933109591389 := by
    rw [show (66 : ℕ) = 63+3 by rfl, mass_add, h63]
    change _ + mass 63 3 = _
    rw [piece63]
    rfl
  have h69 : mass 0 69 = 20939462701937 := by
    rw [show (69 : ℕ) = 66+3 by rfl, mass_add, h66]
    change _ + mass 66 3 = _
    rw [piece66]
    rfl
  have h71 : mass 0 71 = 20942143446291 := by
    rw [show (71 : ℕ) = 69+2 by rfl, mass_add, h69]
    change _ + mass 69 2 = _
    rw [piece69]
    rfl
  exact h71

end ExpandedGate6970.H2307Slope
