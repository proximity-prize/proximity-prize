import ProximityPrize.SubmissionLower.Gate6966Assm

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedGate6970.H2307Numeric

open Gate6966Cell

def defaultRow : ℕ × ℕ × ℕ × ℕ := (4024, 1679, 500, 0)

def checked (G : Gt) (ws : List ℕ) (lv : Lv) (lo n : ℕ) : Bool :=
  (List.range n).all fun d =>
    let i := lo + d
    let (b,j,t,w) := lv.getD i defaultRow
    levelOKF G (i + 1) w b j t 80 (fun a => some (Gate6966CertCF.cvOf 1 ws (i + 1) a))

theorem checked_add (G : Gt) (ws : List ℕ) (lv : Lv) (lo n m : ℕ)
    (h₁ : checked G ws lv lo n = true) (h₂ : checked G ws lv (lo+n) m = true) :
    checked G ws lv lo (n+m) = true := by
  unfold checked at *
  rw [List.range_add]
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at *
  exact ⟨h₁, by simpa [Function.comp_def, Nat.add_assoc] using h₂⟩

def cap (q : ℕ) : ℕ :=
  min q (bif Nat.blt q 3514 then 1679 else (131312 - 26*q)/25)

def ambient (b j t : ℕ) : ℤ :=
  bif Nat.ble 4024 b && Nat.ble 1679 j && Nat.ble 500 t then 427286700047
  else sumUpTo (fun q => cappedN (cap q) (min j 1679) (min t 500)) (min 4025 (b+1))

def loss (lv : Lv) (i : ℕ) : ℤ :=
  let (b,j,t,w) := lv.getD i defaultRow
  427286700047 - ambient b j t + w

def mass (lv : Lv) (lo n : ℕ) : ℤ := sumUpTo (fun i => loss lv (lo+i)) n

theorem mass_add (lv : Lv) (lo n m : ℕ) : mass lv lo (n+m) = mass lv lo n + mass lv (lo+n) m := by
  induction m with
  | zero => simp [mass, sumUpTo]
  | succ m ih =>
    change mass lv lo (n+m) + loss lv (lo+(n+m)) = mass lv lo n + (mass lv (lo+n) m + loss lv (lo+n+m))
    rw [ih, Nat.add_assoc lo n m, add_assoc]

theorem mass_eq (lv : Lv) (n : ℕ) : mass lv 0 n = ∑ i ∈ Finset.range n, loss lv i := by
  simpa [mass] using sumUpTo_eq (loss lv) n

end ExpandedGate6970.H2307Numeric
