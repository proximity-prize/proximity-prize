import ProximityPrize.SubmissionLower.A6966FinalRankBlocks

set_option Elab.async false
set_option autoImplicit false

namespace RankFactor6970

/-- Budgets for the leading monomial, index increase, and top degree increase. -/
structure Budget where
  value : ℕ
  first : ℕ
  second : ℕ
  index : ℕ
  top : ℕ

private def cost (i : Fin 9) : Budget :=
  ![⟨1,0,0,1,0⟩, ⟨1,0,0,2,0⟩, ⟨1,0,0,3,1⟩,
    ⟨1,1,0,1,0⟩, ⟨1,1,0,2,1⟩, ⟨1,0,1,2,1⟩,
    ⟨2,0,1,1,1⟩, ⟨1,3,0,1,1⟩, ⟨2,3,0,3,2⟩] i

private def gain (i : Fin 9) : ℕ := ![1,2,3,2,3,3,2,3,6] i

private def constrain (bound available expense : ℕ) : ℕ :=
  if expense = 0 then bound else min bound (available / expense)

private def collect : List (Fin 9) → Budget → ℕ × List A6966Rows.Factor
  | [], _ => (0,[])
  | i :: order, available =>
    let c := cost i
    let n := constrain (constrain (constrain (constrain
      (available.value / c.value) available.first c.first)
      available.second c.second) available.index c.index) available.top c.top
    let remain := collect order
      ⟨available.value - n*c.value, available.first - n*c.first,
        available.second - n*c.second, available.index - n*c.index, available.top - n*c.top⟩
    (n * gain i + remain.1, if n = 0 then remain.2 else (i,n) :: remain.2)

private def better (a b : ℕ × List A6966Rows.Factor) : ℕ × List A6966Rows.Factor :=
  if b.1 ≤ a.1 then a else b

/-- Try three deterministic orders for the certified contact factors.
The consuming receipt checks the resulting monomials and their exact charge. -/
def schedule (b : Budget) : List A6966Rows.Factor :=
  let a := collect [8,7,5,2,3,1,4,6,0] b
  let c := collect [7,3,4,6,2,5,0,1,8] b
  let d := collect [6,5,8,3,1,0,2,4,7] b
  (better (better a c) d).2

end RankFactor6970
