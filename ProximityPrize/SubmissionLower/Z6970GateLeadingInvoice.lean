import ProximityPrize.SubmissionLower.Z6970GateLeadingCapped
import ProximityPrize.SubmissionLower.Z6970H2307GateAmbientFast

set_option Elab.async false
set_option autoImplicit false

namespace Gate6970Leading

open Gate6966Cell
open ExpandedGate6970.H2307Numeric (cap defaultRow)

def count (F : ℕ → ℕ → ℤ) (n u c : ℕ) : ℤ :=
  let lo := min n u
  let hi := min n 3514
  capPrefix F lo u c +
    ((hi - lo : ℕ) : ℤ) * cappedN u u c +
    sumUpTo (fun q => cappedN (cap (hi + q)) u c) (n - hi)

theorem count_eq (F : ℕ → ℕ → ℤ)
    (hF : ∀ n u, u ≤ 1679 → F n u = sumUpTo (fun q => (cumP q u : ℤ) - cumQ q u) n)
    (n u c : ℕ) (hu : u ≤ 1679) :
    count F n u c = ExpandedGate6970.H2307Numeric.fastCount n u c := by
  simp only [count, ExpandedGate6970.H2307Numeric.fastCount, capPrefix_eq F hF _ _ _ hu]

def ambient (F : ℕ → ℕ → ℤ) (b j t : ℕ) : ℤ :=
  bif Nat.ble 4024 b && Nat.ble 1679 j && Nat.ble 500 t then 427286700047
  else count F (min 4025 (b + 1)) (min j 1679) (min t 500)

theorem ambient_eq (F : ℕ → ℕ → ℤ)
    (hF : ∀ n u, u ≤ 1679 → F n u = sumUpTo (fun q => (cumP q u : ℤ) - cumQ q u) n)
    (b j t : ℕ) : ambient F b j t = ExpandedGate6970.H2307Numeric.ambient b j t := by
  rw [← ExpandedGate6970.H2307Numeric.ambientFast_eq]
  simp only [ambient, ExpandedGate6970.H2307Numeric.ambientFast, count_eq F hF _ _ _ (min_le_right j 1679)]

def loss (F : ℕ → ℕ → ℤ) (lv : Lv) (i : ℕ) : ℤ :=
  let (b,j,t,w) := lv.getD i defaultRow
  427286700047 - ambient F b j t + w

theorem loss_eq (F : ℕ → ℕ → ℤ)
    (hF : ∀ n u, u ≤ 1679 → F n u = sumUpTo (fun q => (cumP q u : ℤ) - cumQ q u) n)
    (lv : Lv) (i : ℕ) : loss F lv i = ExpandedGate6970.H2307Numeric.loss lv i := by
  simp only [loss, ExpandedGate6970.H2307Numeric.loss, ambient_eq F hF]

def mass (F : ℕ → ℕ → ℤ) (lv : Lv) (lo n : ℕ) : ℤ :=
  sumUpTo (fun i => loss F lv (lo + i)) n

theorem mass_eq (F : ℕ → ℕ → ℤ)
    (hF : ∀ n u, u ≤ 1679 → F n u = sumUpTo (fun q => (cumP q u : ℤ) - cumQ q u) n)
    (lv : Lv) (lo n : ℕ) : mass F lv lo n = ExpandedGate6970.H2307Numeric.mass lv lo n := by
  simp only [mass, ExpandedGate6970.H2307Numeric.mass, loss_eq F hF]

end Gate6970Leading
