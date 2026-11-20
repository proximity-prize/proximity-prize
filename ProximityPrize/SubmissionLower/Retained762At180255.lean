import ProximityPrize.SubmissionLower.Fast051
set_option Elab.async false

/-! Retained branch r = ⟨7,6,2⟩ for the 6916 radius (A = 180255, e = 81889, D = A - 133671 = 46584).

At A = 180255 the exclusion `zeroMass 7 6 < need` (Fast051 `retained_exclusions`) fails, so
⟨7,6,2⟩ enters the retained box. This file certifies the replacement accounting for that branch:
* the only tariff for retained factors is `fatPrice`; the largest decomposition is the single
  factor ⟨7,6,2⟩ (two t=1 factors ⟨b,3,1⟩ cost less);
* the Bellman start q = r = ⟨7,6,2⟩ certifies order 198 against every valid x (worst x = ⟨1,3,1⟩);
* every positive factor a ≤ ⟨113,42,8⟩ pays at most `rate762 * a.j` at order 198.
UNBUILT. The A-dependent literals of `physicalPrice`/`fatPrice` are exposed as `e D`; the `rfl`
lemmas tie the copies to the official definitions at 69.15. -/

section PackSource_K1_13_8_R762
set_option autoImplicit true
namespace K1_13_8_R762

open K1_13 K1_13_8

def physicalPriceAt (e D : ℕ) (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q : Shape := ⟨4013, 1650, 550⟩
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((e + 2*D) * x.b * q.b * (chart (taylorLength+1) p).b) D
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2*x.t*mixed32 p p p h
  let points := mixed32 p q auxBox p + 2*x.t*mixed32 p p p p
  ceilDiv numerator l + 2*133671*x.b*q.b + ceilDiv (e*curves + 2*D*points) (32*D)

def fatPriceAt (e D : ℕ) (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := ⟨952630000, 322000000, 0⟩
  let big : Shape := ⟨35007, 12106, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j+1)), max h.j (big.j+1), max 1 h.t⟩
  let divisors := ceilDiv (e * mixed32 p big cut h) (32*D) +
    ceilDiv (mixed32 p big cut p) 32 + 20*p.b*h.b^2 + 5*133671*p.b*h.b + 1
  let singular := if 1 < x.t then ceilDiv (4*x.t*mixed32 p p h h) 32 + x.t*x.b^2+1 else 0
  let curves := ceilDiv (e*mixed32 p q q h + D*mixed32 p q q p) (32*D*293711590)
  let isolated := ceilDiv (3*q.j^2*(2*q.b - q.j)) (4*41481*(41481 - 33184 + 1)*1037)
  divisors + singular + curves + isolated

theorem physicalPriceAt_official (x : Shape) (l : ℕ) :
    physicalPriceAt 81879 46594 x l = physicalPrice x l := rfl

theorem fatPriceAt_official (x : Shape) : fatPriceAt 81879 46594 x = fatPrice x := rfl

/-- `need` at A = 180255 after the c3 savings (block sum ≤ 344119327909215). -/
def need6916 : ℕ := 25902203913876

def rate762 : ℕ := 1160212916592198

section
set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem exclusion_lost : need6916 ≤ zeroMass 7 6 := by decide +kernel

theorem order_test :
    availableMass ⟨7, 6, 2⟩ ⟨1, 3, 1⟩ 197 < need6916 ∧
      need6916 ≤ availableMass ⟨7, 6, 2⟩ ⟨1, 3, 1⟩ 198 := by
  constructor <;> decide +kernel

theorem retained_single : fatPriceAt 81889 46584 ⟨7, 6, 2⟩ = 110268880437040260 := by
  decide +kernel

theorem retained_pairs : ∀ (b₁ b₂ : Fin 7), 1 ≤ b₁.val → 1 ≤ b₂.val → b₁.val + b₂.val ≤ 7 →
    fatPriceAt 81889 46584 ⟨b₁.val, 3, 1⟩ + fatPriceAt 81889 46584 ⟨b₂.val, 3, 1⟩ ≤
      110268880437040260 := by
  decide +kernel

theorem prices_at_order : ∀ (j : Fin 43) (t : Fin 9), 0 < t.val → 3 * t.val ≤ j.val →
    physicalPriceAt 81889 46584 ⟨113, j.val, t.val⟩ 198 ≤ rate762 * j.val := by
  decide +kernel

end

theorem branch_total : 110268880437040260 + 42 * rate762 ≤ 224404613477777444 := by decide

end K1_13_8_R762
end PackSource_K1_13_8_R762
