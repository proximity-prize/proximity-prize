import ProximityPrize.SubmissionLower.PortfolioRamifiedBoxes6815
namespace ProximityPrize.SubmissionLower.SharedTreeCheck6815
open PortfolioRamifiedBoxes6815 PortfolioCost6815
set_option autoImplicit false

def choiceOf (j : ℕ) : Choice := ⟨⟨j/2%3,Nat.mod_lt _ (by decide)⟩,j%2=1⟩

def axisOf (x : ℕ) : Fin 3 := ⟨x/2%4%3,Nat.mod_lt _ (by decide)⟩

def run (fixed : Degrees) (low t y r cap : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0,_,_ => none
  | f+1,code,a =>
    let b := normalize 4 a
    let x := code%65536
    if x%2=0 then
      (if check (choiceOf (x/2)) fixed b low t y r cap then some (code/65536) else none)
    else
      match run fixed low t y r cap f (code/65536) (lower b (axisOf x) (x/8)) with
      | none => none
      | some c => run fixed low t y r cap f c (upper b (axisOf x) (x/8))

theorem run_sound (fixed : Degrees) (low t y r cap : ℕ) :
    ∀ f code a c, run fixed low t y r cap f code a=some c → Covered (Valid fixed low t y r cap) a := by
  intro f
  induction f with
  | zero => intro code a c h; simp [run] at h
  | succ f ih =>
    intro code a c h
    apply covered_normalize _ a (normalize 4 a) rfl
    simp only [run] at h
    split at h
    · split at h
      · exact covered_leaf _ _ ⟨_,by assumption⟩
      · simp at h
    · split at h
      · simp at h
      · rename_i c1 h1
        exact covered_split _ _ _ _ (ih _ _ _ h1) (ih _ _ _ h)

theorem covered_of_run (fixed : Degrees) (low t y r cap f code : ℕ) (a : Box)
    (h : (run fixed low t y r cap f code a).isSome=true) : Covered (Valid fixed low t y r cap) a := by
  cases hc : run fixed low t y r cap f code a with
  | none => simp [hc] at h
  | some c => exact run_sound fixed low t y r cap f code a c hc

end ProximityPrize.SubmissionLower.SharedTreeCheck6815
