import ProximityPrize.SubmissionLower.Z6970CompanionValue
import ProximityPrize.SubmissionLower.Z6969Pack0836

set_option autoImplicit false
set_option Elab.async false

namespace Height2307Companion
open K1_13 (Shape InBox)
open Low6969Prices (physicalPriceOld)

theorem old_antitone (x : Shape) {m n : ℕ} (hp : 0<m) (hm : m≤n) :
    physicalPriceOld x n ≤ physicalPriceOld x m := by
  unfold physicalPriceOld
  dsimp only
  exact Nat.add_le_add_right (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hp hm) _) _

theorem ordinary_tile {x y : Shape} {l m : ℕ}
    (hi : InBox x y) (hx : 3*x.t ≤ x.j) (hy : 3*y.t ≤ y.j)
    (hp : 0<m) (hm : m≤l) :
    physicalPriceOld x l ≤ physicalPriceOld y m :=
  (old_antitone x hp hm).trans (Low6969Monotone.physical_mono hi hx hy m)

theorem physical_corners (ord : ℕ → ℕ → ℕ)
    (mono : ∀ {b j B J}, b ≤ B → j ≤ J → ord b j ≤ ord B J) :
    Corners ord (fun x => physicalPriceOld x (ord x.b x.j)) := by
  intro x y m b j hx hfit hy hb hj hp hm
  have h := ordinary_tile hfit hx.2.1 hy hp (hm.trans (mono hb hj))
  exact h

end Height2307Companion
