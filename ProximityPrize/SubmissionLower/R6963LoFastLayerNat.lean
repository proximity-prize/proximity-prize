import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6963.Lo.FastLayerNat
open Lower6960.RescueSource (triangularWidth layerWidth fastLayer fastPhase phaseBlock phase_of_block)
open P1_7_6 (Quad intervalProduct prefixProduct)
open K1_14 (Shape slots)

def pP (C D U x : ℕ) : ℕ :=
  60 * x * (U * (2 * C - D * (U - 1))) + 10 * (x * (x - 1) * (2 * x - 1)) * (D - 2)
def pM (C D U x : ℕ) : ℕ := 30 * (x * (x - 1)) * (2 * C + D - 2 * U)

def twG (C D L H U : ℕ) : Bool :=
  decide (L < min H U → 2 ≤ D ∧ D * (U - 1) ≤ 2 * C ∧ 2 * U ≤ 2 * C + D ∧
    pP C D U L + pM C D U (min H U) ≤ pP C D U (min H U) + pM C D U L)

def twN (C D L H U : ℕ) : ℕ :=
  if L < min H U then (pP C D U (min H U) + pM C D U L) - (pP C D U L + pM C D U (min H U)) else 0

theorem prefix_cast (C D U x : ℕ) (hD : 2 ≤ D) (hU : 1 ≤ U) (hz : D * (U - 1) ≤ 2 * C)
    (hq : 2 * U ≤ 2 * C + D) :
    prefixProduct (Quad.ofLines (U : ℤ) (-1) (2 * (C : ℤ) - D * ((U : ℤ) - 1)) (2 - (D : ℤ)))
      ⟨1, 0, 0⟩ x = (pP C D U x : ℤ) - (pM C D U x : ℤ) := by
  have e1 : ((2 * C - D * (U - 1) : ℕ) : ℤ) = 2 * (C : ℤ) - D * ((U : ℤ) - 1) := by
    rw [Nat.cast_sub hz]; push_cast
    rw [Nat.cast_sub hU]; push_cast; ring
  have e2 : ((2 * C + D - 2 * U : ℕ) : ℤ) = 2 * (C : ℤ) + D - 2 * U := by
    rw [Nat.cast_sub hq]; push_cast; ring
  have e3 : ((D - 2 : ℕ) : ℤ) = (D : ℤ) - 2 := by rw [Nat.cast_sub hD]; push_cast; ring
  rcases x with _ | y
  · simp [pP, pM, prefixProduct]
  · have e4 : y + 1 - 1 = y := rfl
    have e5 : 2 * (y + 1) - 1 = 2 * y + 1 := by omega
    simp only [pP, pM, e4, e5]
    simp only [prefixProduct, Quad.ofLines]
    push_cast
    rw [e1, e2, e3]
    ring

theorem tw_cast (C D L H U : ℕ) (h : twG C D L H U = true) :
    triangularWidth C D L H U = (twN C D L H U : ℤ) := by
  unfold triangularWidth intervalProduct twN
  by_cases hl : L < min H U
  · obtain ⟨hD, hz, hq, hle⟩ := of_decide_eq_true h hl
    have hU : 1 ≤ U := by have := min_le_right H U; omega
    rw [if_pos hl, if_pos hl, prefix_cast C D U _ hD hU hz hq, prefix_cast C D U _ hD hU hz hq,
      Nat.cast_sub hle]
    push_cast; ring
  · rw [if_neg hl, if_neg hl]; rfl



def lwG (C D L H R : ℕ) : Bool :=
  twG C D L (min H (D - (C - 1) % D)) (min R ((C - 1) / D + 1)) &&
    twG C D (max L (D - (C - 1) % D)) H (min R ((C - 1) / D + 1 + 1))

def lwN (C D L H R : ℕ) : ℕ :=
  twN C D L (min H (D - (C - 1) % D)) (min R ((C - 1) / D + 1)) +
    twN C D (max L (D - (C - 1) % D)) H (min R ((C - 1) / D + 1 + 1))

theorem lw_cast (C D L H R : ℕ) (h : lwG C D L H R = true) :
    layerWidth C D L H R = (lwN C D L H R : ℤ) := by
  unfold lwG at h
  rw [Bool.and_eq_true] at h
  unfold layerWidth lwN
  simp only []
  rw [tw_cast _ _ _ _ _ h.1, tw_cast _ _ _ _ _ h.2]
  push_cast; rfl

def fastLayerN (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  if lwG (s.m * A - 2 * h * (r + i)) (131071 - h) ((i + δ) * d) (s.J + 1) (s.B + 1 - (i + δ) * c)
  then slots s.U ((i + δ) * v) *
    (lwN (s.m * A - 2 * h * (r + i)) (131071 - h) ((i + δ) * d) (s.J + 1) (s.B + 1 - (i + δ) * c) / 120)
  else fastLayer s A h r d c v δ i

theorem fastLayerN_eq (s : Shape) (A h r d c v δ i : ℕ) :
    fastLayerN s A h r d c v δ i = fastLayer s A h r d c v δ i := by
  unfold fastLayerN
  split
  · next hg =>
    unfold fastLayer
    rw [lw_cast _ _ _ _ _ hg, Int.toNat_natCast]
  · rfl



def mn (a b : ℕ) : ℕ := bif Nat.ble a b then a else b
def mx (a b : ℕ) : ℕ := bif Nat.ble a b then b else a

def pPf (C D U x : ℕ) : ℕ :=
  Nat.add (Nat.mul (Nat.mul 60 x) (Nat.mul U (Nat.sub (Nat.mul 2 C) (Nat.mul D (Nat.sub U 1)))))
    (Nat.mul (Nat.mul 10 (Nat.mul (Nat.mul x (Nat.sub x 1)) (Nat.sub (Nat.mul 2 x) 1))) (Nat.sub D 2))
def pMf (C D U x : ℕ) : ℕ :=
  Nat.mul (Nat.mul 30 (Nat.mul x (Nat.sub x 1))) (Nat.sub (Nat.add (Nat.mul 2 C) D) (Nat.mul 2 U))
theorem pPf_eq : pPf = pP := rfl
theorem pMf_eq : pMf = pM := rfl
theorem mn_eq (a b : ℕ) : mn a b = min a b := by
  unfold mn; by_cases h : a ≤ b <;> simp [h, Nat.ble_eq] <;> omega
theorem mx_eq (a b : ℕ) : mx a b = max a b := by
  unfold mx; by_cases h : a ≤ b <;> simp [h, Nat.ble_eq] <;> omega

def twB (C D L H U : ℕ) : ℕ :=
  let R := mn H U
  bif Nat.blt L R then Nat.sub (Nat.add (pPf C D U R) (pMf C D U L)) (Nat.add (pPf C D U L) (pMf C D U R)) else 0
def lwB (C D L H R : ℕ) : ℕ :=
  let T := Nat.sub D (Nat.mod (Nat.sub C 1) D)
  let a := Nat.add (Nat.div (Nat.sub C 1) D) 1
  Nat.add (twB C D L (mn H T) (mn R a)) (twB C D (mx L T) H (mn R (Nat.add a 1)))
def fastLayerB (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  slots s.U ((i + δ) * v) *
    (Nat.div (lwB (s.m * A - 2 * h * (r + i)) (131071 - h) ((i + δ) * d) (s.J + 1) (s.B + 1 - (i + δ) * c)) 120)


def twGf (C D L H U : ℕ) : Bool :=
  let R := mn H U
  Nat.ble R L || (Nat.ble 2 D && Nat.ble (Nat.mul D (Nat.sub U 1)) (Nat.mul 2 C) &&
    Nat.ble (Nat.mul 2 U) (Nat.add (Nat.mul 2 C) D) &&
    Nat.ble (Nat.add (pPf C D U L) (pMf C D U R)) (Nat.add (pPf C D U R) (pMf C D U L)))
def lwGf (C D L H R : ℕ) : Bool :=
  let T := Nat.sub D (Nat.mod (Nat.sub C 1) D)
  let a := Nat.add (Nat.div (Nat.sub C 1) D) 1
  twGf C D L (mn H T) (mn R a) && twGf C D (mx L T) H (mn R (Nat.add a 1))
def fastLayerG0 (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  if lwGf (s.m * A - 2 * h * (r + i)) (131071 - h) ((i + δ) * d) (s.J + 1) (s.B + 1 - (i + δ) * c)
  then fastLayerB s A h r d c v δ i else fastLayer s A h r d c v δ i


theorem twGf_eq : twGf = twG := by
  funext C D L H U
  apply Bool.eq_iff_iff.mpr
  simp only [twGf, twG, mn_eq, pPf_eq, pMf_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq,
    decide_eq_true_eq]
  by_cases h : L < min H U
  · simp [h, Nat.not_le.mpr h, and_assoc]
  · simp [h, Nat.not_lt.mp h]

theorem twB_eq : twB = twN := by
  funext C D L H U
  unfold twB twN
  simp only [mn_eq, pPf_eq, pMf_eq]
  by_cases h : L < min H U
  · simp [Nat.blt_eq, h]
  · simp [Nat.blt_eq, h]

theorem lwGf_eq : lwGf = lwG := by
  funext C D L H R
  unfold lwGf lwG
  simp only [twGf_eq, mn_eq, mx_eq]
  rfl

theorem lwB_eq : lwB = lwN := by
  funext C D L H R
  unfold lwB lwN
  simp only [twB_eq, mn_eq, mx_eq]
  rfl

theorem fastLayerG0_eq (s : Shape) (A h r d c v δ i : ℕ) :
    fastLayerG0 s A h r d c v δ i = fastLayer s A h r d c v δ i := by
  rw [← fastLayerN_eq s A h r d c v δ i]
  unfold fastLayerG0 fastLayerN fastLayerB
  simp only [lwGf_eq, lwB_eq]
  rfl


def fastLayerG (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  bif Nat.beq (slots s.U (Nat.mul (Nat.add i δ) v)) 0 then 0 else fastLayerG0 s A h r d c v δ i

theorem fastLayerG_eq (s : Shape) (A h r d c v δ i : ℕ) :
    fastLayerG s A h r d c v δ i = fastLayer s A h r d c v δ i := by
  unfold fastLayerG
  by_cases hs : slots s.U ((i + δ) * v) = 0
  · have : Nat.beq (slots s.U (Nat.mul (Nat.add i δ) v)) 0 = true := by
      show Nat.beq (slots s.U ((i + δ) * v)) 0 = true
      rw [hs]; rfl
    rw [this]
    show 0 = _
    unfold fastLayer
    rw [hs, Nat.zero_mul]
  · have : Nat.beq (slots s.U (Nat.mul (Nat.add i δ) v)) 0 = false := by
      show Nat.beq (slots s.U ((i + δ) * v)) 0 = false
      rw [Bool.eq_false_iff]
      intro hb
      exact hs (Nat.eq_of_beq_eq_true hb)
    rw [this]
    exact fastLayerG0_eq s A h r d c v δ i

theorem phase_of_blockG {s : Shape} {A h r d c v δ n z : ℕ}
    (len : s.J / d + 1 = n) (block : phaseBlock (fastLayerG s A h r d c v δ) 0 n = z) :
    fastPhase s A h r d c v δ = z := by
  have e : fastLayerG s A h r d c v δ = fastLayer s A h r d c v δ :=
    funext (fastLayerG_eq s A h r d c v δ)
  rw [e] at block
  exact phase_of_block len block

end Lower6963.Lo.FastLayerNat
