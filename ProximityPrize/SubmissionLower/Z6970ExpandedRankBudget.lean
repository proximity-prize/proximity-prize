import ProximityPrize.SubmissionLower.Z6970ExpandedPivotCore

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedTaper6970
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2_3 (Powers)

def cap (q : ℕ) : ℕ := if q < 3514 then 1679 else (131312-26*q)/25

theorem cap_antitone : Antitone cap := by
  intro a b hab
  unfold cap
  split <;> split <;> omega

def power (i : BlockIndex) : Fin 11 → ℕ :=
  let d := residualDegree (cap i.1.val) i
  let p := if 3514 ≤ i.1.val then min d (3000 + d - (i.1.val + 4*i.2.val)) else 0
  (⟨p,0,0⟩ : Powers).expand

def debit (i : BlockIndex) : ℕ :=
  let k := cap i.1.val
  let old := bound k i (power i)
  if residualDegree k i = 1679 then
    min old (∑ q, ExpandedPivotOpt6970.charge (k := k) i q)
  else old

theorem block_rank (i : BlockIndex) :
    Module.finrank Geom (LinearMap.range (originBlock (cap i.1.val) i)) ≤ debit i := by
  have h := origin_block_rank_bound (cap i.1.val) K1_13_2_2_2.proof
    K1_13_2_2_3.proof K1_13_2_2_4.proof K1_13_2_2_5.proof i (power i)
  unfold debit
  dsimp
  split
  · rename_i hh
    exact le_min h (ExpandedPivotOpt6970.block_le_charge i hh)
  · exact h

theorem local_rank (x y : Geom) :
    Module.finrank Geom (LinearMap.range
      ((localConstraintAt 3000 x y).domRestrict (space cap))) ≤ ∑ i : BlockIndex, debit i :=
  rank_le_of_blocks cap_antitone x y debit block_rank

end ExpandedTaper6970
