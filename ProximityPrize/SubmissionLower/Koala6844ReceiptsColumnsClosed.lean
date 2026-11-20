import ProximityPrize.SubmissionLower.Koala6844ReceiptsArithmeticFast

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxRecDepth 10000

def colPolyPrefix (A B C : Int) (n : Nat) : Int :=
  let x := (n : Int)
  6 * A * x + 3 * B * x * (x - 1) + C * x * (x - 1) * (2*x - 1)

theorem colPolyPrefix_succ (A B C : Int) (n : Nat) :
    colPolyPrefix A B C (n + 1) =
      colPolyPrefix A B C n + 6 * (A + B*(n : Int) + C*(n : Int)*(n : Int)) := by
  unfold colPolyPrefix
  simp only [Int.natCast_add, Int.cast_ofNat_Int]
  grind

theorem colPolyPrefix_window_mul (f : Nat → Nat) (A B C : Int) (start n : Nat)
    (h : ∀ r, start ≤ r → r < start + n →
      2 * (f r : Int) = A + B*(r : Int) + C*(r : Int)*(r : Int)) :
    12 * (recSum (fun i => f (start + i)) n : Int) =
      colPolyPrefix A B C (start+n) - colPolyPrefix A B C start := by
  induction n with
  | zero => simp [recSum]
  | succ n ih =>
    have h₁ := ih (fun r hr hr' => h r hr (by omega))
    have h₂ := h (start+n) (by omega) (by omega)
    rw [← Nat.add_assoc start n 1, colPolyPrefix_succ]
    simp only [recSum, Int.natCast_add] at h₂ ⊢ 
    omega

def colPolyWindow (A B C : Int) (start n : Nat) : Nat :=
  ((colPolyPrefix A B C (start+n) - colPolyPrefix A B C start) / 12).toNat

theorem colPolyWindow_eq (f : Nat → Nat) (A B C : Int) (start n : Nat)
    (h : ∀ r, start ≤ r → r < start+n →
      2 * (f r : Int) = A + B*(r : Int) + C*(r : Int)*(r : Int)) :
    colPolyWindow A B C start n = recSum (fun i => f (start+i)) n := by
  unfold colPolyWindow
  rw [← colPolyPrefix_window_mul _ _ _ _ _ _ h]
  omega

def colQuadSum (Y D g : Int) (n : Nat) : Nat :=
  let v := (n : Int) - 1
  let a := Y * (2 * D - g * (Y - 1))
  let b := 2 * (Y - D) - g
  (((n : Int) * (6 * a + v * (3 * b + (g - 2) * (2 * (n : Int) - 1)))) / 12).toNat

theorem colQuadSum_eq (f : Nat → Nat) (Y D g : Int) (n : Nat)
    (h : ∀ r : Nat, r < n →
      2 * (f r : Int) = 2 * (Y-(r : Int)) * (D-(g-1)*(r : Int)) -
        g * (Y-(r : Int)) * (Y-(r : Int)-1)) :
    colQuadSum Y D g n = recSum f n := by
  let a := Y * (2 * D - g * (Y - 1))
  let b := 2 * (Y - D) - g
  let c := g - 2
  have hw := colPolyWindow_eq f a b c 0 n (by
    intro r _ hr
    rw [h r (by omega)]
    dsimp [a,b,c]
    grind)
  simp only [Nat.zero_add] at hw
  rw [← hw]
  unfold colQuadSum colPolyWindow colPolyPrefix
  dsimp [a,b,c]
  congr 2 <;> grind

theorem colRow_twice (g y D : Nat) (hd : g * (y-1) ≤ D) :
    2 * ((y * D - g * chooseTwo y : Nat) : Int) =
      2 * (y : Int) * (D : Int) - (g : Int) * (y : Int) * ((y : Int)-1) := by
  cases y with
  | zero => simp [chooseTwo]
  | succ y =>
    have hmod : ((y+1)*y) % 2 = 0 := by
      rw [Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one y with h|h <;> simp [Nat.add_mod,h]
    have he : 2 * chooseTwo (y+1) = (y+1)*y := by
      simp only [chooseTwo, Nat.add_sub_cancel] 
      omega
    have hg : 2 * (g * chooseTwo (y+1)) = g * ((y+1)*y) := by
      rw [← he]
      grind
    simp only [Nat.add_sub_cancel] at hd
    have hle : g * chooseTwo (y+1) ≤ (y+1)*D := by
      have hmul := Nat.mul_le_mul_left (y+1) hd
      have hgg : g * ((y+1)*y) = (y+1)*(g*y) := by grind
      omega
    rw [Int.natCast_sub hle]
    push_cast
    have hi := congrArg Int.ofNat he
    push_cast at hi
    grind

theorem colRow_twice_of_le (g y D : Nat) (hy : y ≤ (D+g-1)/g) :
    2 * ((y * D - g * chooseTwo y : Nat) : Int) =
      2 * (y : Int) * (D : Int) - (g : Int) * (y : Int) * ((y : Int)-1) := by
  apply colRow_twice
  cases y with
  | zero => simp
  | succ y =>
    have hmul := Nat.mul_le_mul_right g hy
    have hdiv := Nat.div_mul_le_self (D+g-1) g
    rw [Nat.add_mul] at hmul
    rw [Nat.mul_comm g]
    simp only [Nat.add_sub_cancel, Nat.one_mul] at *
    omega

def colQuadNat (Y D : Nat) : Nat → Nat
  | 0 => 0
  | n+1 =>
    let pos := 6 * Y * (2*D + degree) +
      n * (6*Y + (degree - 2)*(2*n + 1))
    let neg := (6*degree) * Y * Y + n * (6*D + 3*degree)
    (n+1) * (pos-neg) / 12

private theorem colClip_eq (k p q : Nat) :
    k * (p-q) / 12 =
      (((k : Int) * ((p : Int)-(q : Int))) / 12).toNat := by
  by_cases h : q ≤ p
  · rw [← Int.natCast_sub h]
    rfl
  · have hzero : p-q = 0 := by omega
    rw [hzero, Nat.mul_zero]
    have hmul : (k : Int) * ((p : Int)-(q : Int)) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    omega

theorem colQuadNat_eq (Y D n : Nat) :
    colQuadNat Y D n = colQuadSum Y D degree n := by
  cases n with
  | zero => simp [colQuadNat,colQuadSum]
  | succ n =>
    unfold colQuadNat colQuadSum
    dsimp
    rw [colClip_eq]
    congr 2
    have hg : 2 ≤ degree := by decide
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_sub hg, Int.cast_ofNat_Int]
    grind

def colY (D H r : Nat) : Nat :=
  min ((D - (degree - 1)*r + degree - 1)/degree) (H-r)

def colRow (D H r : Nat) : Nat :=
  colY D H r * (D - (degree-1)*r) - degree * chooseTwo (colY D H r)

def colHead (D H : Nat) : Nat :=
  min ((D+degree-1)/degree) H

def colLength (D H n : Nat) : Nat :=
  let y := colHead D H
  min n (min y (if y = H then n else degree - ((D+degree-1)%degree)))

theorem colY_linear (D H n r : Nat) (hr : r < colLength D H n) :
    colY D H r = colHead D H - r ∧
    (degree-1)*r ≤ D ∧ r < colHead D H ∧
    degree * (colY D H r - 1) ≤ D - (degree-1)*r := by
  let M := (D+131070)/131071
  let Y := min M H
  have hY : Y ≤ M := Nat.min_le_left _ _
  have hH : Y ≤ H := Nat.min_le_right _ _
  have hlim := Nat.lt_of_lt_of_le hr (Nat.min_le_right _ _)
  have hyr := Nat.lt_of_lt_of_le hlim (Nat.min_le_left _ _)
  change r < Y at hyr
  have hrem := Nat.lt_of_lt_of_le hlim (Nat.min_le_right _ _)
  change r < (if Y = H then n else 131071 - ((D+131070)%131071)) at hrem
  have hlow : Y-r ≤ (D-131070*r+131070)/131071 := by dsimp [M] at hY; omega
  have hy' : min ((D-131070*r+131070)/131071) (H-r) = Y-r := by
    apply Nat.le_antisymm
    · by_cases he : Y = H
      · rw [he]; exact Nat.min_le_right _ _
      · rw [if_neg he] at hrem
        have hh : Y = M := by dsimp [Y]; omega
        apply Nat.le_trans (Nat.min_le_left _ _)
        rw [hh]
        dsimp [M] at *
        omega
    · exact Nat.le_min.mpr ⟨hlow, Nat.sub_le_sub_right hH _⟩
  have hy : colY D H r = Y-r := by
    unfold colY degree
    rw [Nat.add_sub_assoc (by decide : 1 ≤ 131071)]
    exact hy'
  change colY D H r = Y-r ∧ 131070*r ≤ D ∧ r < Y ∧
      131071*(colY D H r-1) ≤ D-131070*r
  rw [hy]
  dsimp [M] at hY
  omega

theorem colQuad_eq (D H n : Nat) :
    colQuadSum (colHead D H) D degree (colLength D H n) =
        recSum (colRow D H) (colLength D H n) := by
  apply colQuadSum_eq
  intro r hr
  obtain ⟨hy, hd, hpos, hdim⟩ := colY_linear D H n r hr
  unfold colRow
  rw [colRow_twice _ _ _ hdim, hy,
    Int.natCast_sub (Nat.le_of_lt hpos), Int.natCast_sub hd, Int.natCast_mul]
  rfl

theorem colLength_le (D H n : Nat) : colLength D H n ≤ n := by
  unfold colLength
  exact Nat.min_le_left _ _

theorem colRow_shift (D H a i : Nat) :
    colRow D H (a+i) = colRow (D-(degree-1)*a) (H-a) i := by
  simp only [colRow, colY, Nat.mul_add, Nat.sub_sub]

theorem colRec_add (f : Nat → Nat) (a b : Nat) :
    recSum f (a+b) = recSum f a + recSum (fun i => f (a+i)) b := by
  simp only [recSum_eq, sumRange_add]

theorem colRec_zero (f : Nat → Nat) (n : Nat) (hf : ∀ i, f i = 0) :
    recSum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [recSum, ih, hf]

def colStep (tail : Nat → Nat → Nat → Nat) (D H n : Nat) : Nat :=
  if n = 0 ∨ D = 0 ∨ H = 0 then 0
  else
    let a := colLength D H n
    colQuadNat (colHead D H) D a +
      tail (D-(degree-1)*a) (H-a) (n-a)

theorem colStep_eq (tail : Nat → Nat → Nat → Nat)
    (ht : ∀ D H n, tail D H n = recSum (colRow D H) n)
    (D H n : Nat) :
    colStep tail D H n = recSum (colRow D H) n := by
  unfold colStep
  split
  next h =>
    rcases h with h | h | h
    · subst n; rfl
    · subst D
      exact (colRec_zero _ _ (by intro i; simp [colRow, colY, degree])).symm
    · subst H
      exact (colRec_zero _ _ (by intro i; simp [colRow, colY, degree])).symm
  next _ =>
    dsimp only
    let a := colLength D H n
    have he : a + (n-a) = n := by have := colLength_le D H n; dsimp [a]; omega
    calc
      _ = recSum (colRow D H) a +
          recSum (fun i => colRow D H (a+i)) (n-a) := by simp only [a, colQuadNat_eq, colQuad_eq, ht, colRow_shift]
      _ = _ := by rw [← colRec_add, he]

def colFastInner : Nat → Nat → Nat → Nat :=
  colStep (colStep (fun D H n => recSum (colRow D H) n))

def colFast (src : SourceShape) (j : Nat) : Nat :=
  recSum (fun h =>
    let D := sourceCutoff src h - (degree+poleWidth)*j - (degree-2)*h
    let H := src.U-j+1-h
    colFastInner D H (src.B-2*h+1)) (src.s+1)

theorem colFast_eq (src : SourceShape) (j : Nat) :
    colFast src j = auxColumnsRec src j := by
  unfold colFast auxColumnsRec
  congr 1
  funext h
  simp only [colFastInner, colStep_eq _ (fun D H n => colStep_eq _ (by intros; rfl) D H n) _ _ _]
  rfl

theorem contactColumnsWindow_fast (src : SourceShape) (start len value : Nat)
    (h : recSum (fun i => colFast src (start+i+1)) len = value) :
    sumRange len (fun i => auxiliaryColumnSlice src (start+i+1)) = value := by
  apply contactColumnsWindow_of_rec
  simpa only [colFast_eq] using h

end ProximityPrize.SubmissionLower.Koala6844Receipts
