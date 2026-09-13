import ProximityPrize.SubmissionLower.BoundaryTailCarrier6808

namespace ProximityPrize.SubmissionLower.BoundaryTailAffineRounding6808
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- An integer-affine upper envelope for a nonnegative rational-affine floor. -/
def upper (a b d z : ℕ) : ℕ := (a / d + 1) * z + (b / d + 1)

theorem floor_le_upper (a b d z : ℕ) (hd : 0 < d) :
    (a*z+b)/d ≤ upper a b d z := by
  have ha := Nat.mod_lt a hd
  have hb := Nat.mod_lt b hd
  have hea := Nat.mod_add_div a d
  have heb := Nat.mod_add_div b d
  have haz := Nat.mul_le_mul_right z (Nat.le_of_lt ha)
  have heaz := congrArg (fun x : ℕ => x*z) hea
  have hlt : a*z+b < d*upper a b d z := by
    unfold upper
    nlinarith
  exact (Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [Nat.mul_comm] using hlt) |>.le

theorem upper_le_floor_add (a b d z : ℕ) (hd : 0 < d) :
    upper a b d z ≤ (a*z+b)/d + z + 1 := by
  have ha := Nat.div_mul_le_self a d
  have hb := Nat.div_mul_le_self b d
  have haz := Nat.mul_le_mul_right z ha
  have hbase : a/d*z+b/d ≤ (a*z+b)/d := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    nlinarith
  unfold upper
  nlinarith

/-- The envelope loses at most one unit per z step plus one at the origin. -/
theorem rounding_error_le (a b d z maxZ : ℕ) (hd : 0 < d) (hz : z ≤ maxZ) :
    upper a b d z ≤ (a*z+b)/d + maxZ + 1 := by
  exact (upper_le_floor_add a b d z hd).trans (by omega)

open RCN095 RCN146

def slopeNumerator (a b : ℕ) : ℕ :=
    93222280598677596*a^2 + 186444561197355192*a*b + 3496456548794713058*a + 1180960945979680456*b + 15865592863136259350

def interceptNumerator (a b : ℕ) : ℕ :=
    31074093532892532*a^3 + 93222280598677596*a^2*b + 14338159986076996693*a^2 + 93222280598677596*a*b^2 + 28671421647852536426*a*b + 381980542961811353439*a + 590547268321223732*b^2 + 147325400949900121454*b + 1140793940893489645748

theorem ledger_affine (a b z : ℕ) :
    BoundaryTailCarrier6808.ledgerCap ⟨z,b+2,a+3⟩ =
      (slopeNumerator a b*z+interceptNumerator a b)/1808748 := by
  have hr : a+3-1 = a+2 := by omega
  have hv : 131074*(b+2)-131072 = 131074*b+131076 := by omega
  have hn : BoundaryTailAlgebra.normalFlag 131071 (a+3) (b+2) z =
      (⟨131074*z,131074*b+131076,131074*(a+2)⟩ : FlagDegree) := by
    change (⟨131074*z,131074*(b+2)-131072,131074*(a+3-1)⟩ : FlagDegree) = _
    rw [hr,hv]
  have he : BoundaryTailOwnArithmetic6808.ownPolynomial a b z +
      50243 * flagMixed (⟨z,b+2,a+3⟩ : FlagDegree) ⟨z,b+2,a+3⟩
        (6 • BoundaryTailAlgebra.normalFlag 131071 (a+3) (b+2) z +
          65539 • (⟨1620,133,52⟩ : FlagDegree)) =
        slopeNumerator a b*z+interceptNumerator a b := by
    rw [hn]
    simp only [flagMixed, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all,
      BoundaryTailOwnArithmetic6808.ownPolynomial, slopeNumerator, interceptNumerator]
    ring
  simpa only [BoundaryTailCarrier6808.ledgerCap, Nat.add_sub_cancel] using
    congrArg (fun n : ℕ => n / 1808748) he

def rootUpper (r v z : ℕ) : ℕ :=
  upper (slopeNumerator (r-3) (v-2)) (interceptNumerator (r-3) (v-2)) 1808748 z

theorem ledger_le_rootUpper (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    BoundaryTailCarrier6808.ledgerCap ⟨z,v,r⟩ ≤ rootUpper r v z := by
  obtain ⟨a,rfl⟩ : ∃ a, r=a+3 := ⟨r-3,by omega⟩
  obtain ⟨b,rfl⟩ : ∃ b, v=b+2 := ⟨v-2,by omega⟩
  rw [ledger_affine]
  simpa only [rootUpper, Nat.add_sub_cancel] using
    floor_le_upper (slopeNumerator a b) (interceptNumerator a b) 1808748 z (by decide)

end ProximityPrize.SubmissionLower.BoundaryTailAffineRounding6808
