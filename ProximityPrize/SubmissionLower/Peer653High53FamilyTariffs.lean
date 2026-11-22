import ProximityPrize.SubmissionLower.Peer653High53FamilyCore

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
open Peer653High53 (Band agreement p blockLength)
abbrev degreeAt := P1_7.degreeAt
abbrev quotientOrder := P1_7.quotientOrder
def gap (hi : ℕ) := agreement - degreeAt hi
def scale (hi : ℕ) := agreement * gap hi
def muNum (hi : ℕ) := agreement * (blockLength - degreeAt hi)
def lambdaNum (hi : ℕ) := blockLength * gap hi
abbrev ceilRatio := P1_7.ceilRatio
abbrev singularDegree := P1_7.singularDegree
abbrev singularFee := P1_7.singularFee
def persistentFee (lo hi e v : ℕ) : ℕ :=
  let t := lambdaNum hi * quotientOrder lo
  let a := muNum hi + 2 * t * (e - 1)
  let b := 2 * hi * muNum hi + 2 * t * v
  ceilRatio (e * b^2 + 2 * v * a * b) ((scale hi)^2) + e
def properFee (lo hi e v : ℕ) : ℕ :=
  let bc := quotientOrder lo + 1
  let ac := 1 + bc * (e - 1)
  let cc := bc * v + 2 * hi
  let bn := lambdaNum hi * quotientOrder lo
  let an := muNum hi + bn * (e - 1)
  let cn := bn * v + 2 * hi * muNum hi
  ceilRatio (e * cc * cn +
    v * (cn * ((2*e-2)*bc + ac) + cc * ((2*e-2)*bn + an)) +
    v^2 * ((ac - 2*bc) * bn + an * bc)) (scale hi)
def flatFee (hi v : ℕ) : ℕ := ceilRatio (Peer653High53.t * (p+1) * v) (gap hi)
def tangentFee (lo hi e v : ℕ) : ℕ := properFee lo hi e v + flatFee hi v + e
def wholePrice (lo hi e v : ℕ) : ℕ :=
  if v = 0 then e else singularFee e v +
    if e ≤ 2 then persistentFee lo hi e v else tangentFee lo hi e v
structure GradeOK (lo hi fullU cap e : ℕ) (g : Grade) : Prop where
  sub : g.slots ≤ fullU
  separant : singularDegree e g.seedCap < p
  flat : e * degreeAt hi + g.seedCap < p
  fee : wholePrice lo hi e g.seedCap ≤ cap
def AllGrades (lo hi fullU cap : ℕ) : ℕ → List Grade → Prop
  | _, [] => True
  | e, g :: gs => GradeOK lo hi fullU cap e g ∧ AllGrades lo hi fullU cap (e+1) gs
theorem get_grade {lo hi fullU cap : ℕ} (gs : List Grade) (e : ℕ)
    (hall : AllGrades lo hi fullU cap e gs) (i : Fin gs.length) :
    GradeOK lo hi fullU cap (i.val + e) (gs.get i) := by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j, hj⟩
    · change GradeOK lo hi fullU cap (0+e) g
      simpa only [Nat.zero_add] using hall.1
    · have h := ih (e+1) hall.2 ⟨j, by simpa using hj⟩
      simpa only [List.get_cons_succ, Nat.succ_add, Nat.add_succ] using h
theorem grade_of_literals {lo hi fullU cap e v U D m price : ℕ}
    (hU : U ≤ fullU) (hD : singularDegree e v = D) (hDp : D < p)
    (hm : e * degreeAt hi + v = m) (hmp : m < p)
    (hprice : wholePrice lo hi e v = price) (hle : price ≤ cap) :
    GradeOK lo hi fullU cap e ⟨v,U⟩ :=
  ⟨hU, hD.le.trans_lt hDp, hm.le.trans_lt hmp, hprice.le.trans hle⟩
theorem sheets_le_price (lo hi e v : ℕ) : e ≤ wholePrice lo hi e v := by
  unfold wholePrice
  split
  · exact le_rfl
  · split
    · dsimp only [persistentFee]
      omega
    · unfold tangentFee
      omega
end Peer653High53
end
