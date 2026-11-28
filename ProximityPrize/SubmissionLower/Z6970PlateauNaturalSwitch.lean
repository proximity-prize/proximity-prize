import ProximityPrize.SubmissionLower.Z6970PlateauNatural

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedPlateauNatural6970

def signed (l : Ray) : KoalaPiecewiseTriangle.Line :=
  ⟨(l.base : ℤ) - 10000, (l.slope : ℤ)⟩

/-- Integer ceiling followed by truncation at zero equals the natural ceiling
of the truncated numerator. -/
theorem ceiling_eq (a b d : ℕ) (hd : 0 < d) :
    ceiling (a - b) d = (-(((b : ℤ) - a) / (d : ℤ))).toNat := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  by_cases hab : a ≤ b
  · have hn : (0 : ℤ) ≤ (b : ℤ) - a := by omega
    have hq := Int.ediv_nonneg hn hd'.le
    rw [Int.toNat_of_nonpos (neg_nonpos.mpr hq)]
    simp only [ceiling, Nat.sub_eq_zero_of_le hab, zero_add]
    exact Nat.div_eq_of_lt (by omega)
  · have ba : b ≤ a := by omega
    have one : 1 ≤ d := by omega
    let q : ℤ := ((b : ℤ) - a) / (d : ℤ)
    have bounds : q * (d : ℤ) ≤ (b : ℤ) - a ∧
        (b : ℤ) - a < q * (d : ℤ) + d :=
      (Int.ediv_eq_iff_of_pos hd').mp rfl
    have inv : (((a : ℤ) - b) + ((d : ℤ) - 1)) / (d : ℤ) = -q := by
      apply (Int.ediv_eq_iff_of_pos hd').mpr
      rw [neg_mul]
      omega
    have cast : (ceiling (a - b) d : ℤ) = -q := by
      unfold ceiling
      rw [Int.natCast_ediv, Nat.cast_add, Nat.cast_sub ba, Nat.cast_sub one, Nat.cast_one]
      exact inv
    simpa only [Int.toNat_natCast] using congrArg Int.toNat cast

private theorem cross_eq (l k : Ray) (ord : l.slope < k.slope) :
    ceiling (l.base - k.base) (k.slope - l.slope) =
      (ExpandedPlateauEnvelope6970.cross (signed l) (signed k)).toNat := by
  have base : ((k.base : ℤ) - 10000) - ((l.base : ℤ) - 10000) = (k.base : ℤ) - l.base := by ring
  unfold ExpandedPlateauEnvelope6970.cross signed
  dsimp only
  rw [base, ← Nat.cast_sub ord.le]
  exact ceiling_eq l.base k.base _ (by omega)

private theorem min_toNat (a b : ℤ) :
    (min a b).toNat = min a.toNat b.toNat := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (Int.toNat_le_toNat h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [min_eq_right h', min_eq_right (Int.toNat_le_toNat h')]

theorem stop_eq (hi : ℕ) (l : Ray) (ls : List Ray)
    (ord : ∀ k ∈ ls, l.slope < k.slope) :
    stop hi l ls =
      (ExpandedPlateauEnvelope6970.switchAt (hi : ℤ) (signed l) (ls.map signed)).toNat := by
  induction ls with
  | nil => simp [stop, ExpandedPlateauEnvelope6970.switchAt]
  | cons k ks ih =>
    have first := ord k List.mem_cons_self
    have later := ih (fun j hj => ord j (List.mem_cons_of_mem k hj))
    simp only [stop, List.map_cons, ExpandedPlateauEnvelope6970.switchAt, min_toNat]
    rw [cross_eq l k first, later]

end ExpandedPlateauNatural6970
