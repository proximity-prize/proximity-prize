import ProximityPrize.SubmissionLower.PortfolioBoxCover6815
namespace ProximityPrize.SubmissionLower.OwnerTreeCheck6815
open PortfolioBoxes6815 PortfolioBoxCover6815 PortfolioChoice6815 PortfolioCost6815
set_option autoImplicit false

def choiceOf (j : ℕ) : Choice :=
  if j=0 then .native else if j=1 then .derivative false else if j=2 then .derivative true
  else .auxiliary ((j-3)%2=1) ⟨(j-3)/2%75,Nat.mod_lt _ (by decide)⟩

def axisOf (x : ℕ) : Fin 4 := ⟨x/2%4,Nat.mod_lt _ (by decide)⟩

def run (fixed : Degrees) (m low t y r cap : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0,_,_ => none
  | f+1,code,a =>
    let b := normalize m 8 a
    let x := code%65536
    if x%2=0 then
      (if PortfolioBoxCheck6815.check (choiceOf (x/2)) fixed b m low t y r cap then some (code/65536) else none)
    else
      match run fixed m low t y r cap f (code/65536) (lower b (axisOf x) (x/8)) with
      | none => none
      | some c => run fixed m low t y r cap f c (upper b (axisOf x) (x/8))

theorem run_sound (fixed : Degrees) (m low t y r cap : ℕ) :
    ∀ f code a c, run fixed m low t y r cap f code a=some c → Covered m (Valid fixed m low t y r cap) a := by
  intro f
  induction f with
  | zero => intro code a c h; simp [run] at h
  | succ f ih =>
    intro code a c h
    apply covered_normalize m _ a (normalize m 8 a) rfl
    simp only [run] at h
    split at h
    · split at h
      · exact covered_leaf m _ _ ⟨_,by assumption⟩
      · simp at h
    · split at h
      · simp at h
      · rename_i c1 h1
        exact covered_split m _ _ _ _ (ih _ _ _ h1) (ih _ _ _ h)

theorem covered_of_run (fixed : Degrees) (m low t y r cap f code : ℕ) (a : Box)
    (h : (run fixed m low t y r cap f code a).isSome=true) : Covered m (Valid fixed m low t y r cap) a := by
  cases hc : run fixed m low t y r cap f code a with
  | none => simp [hc] at h
  | some c => exact run_sound fixed m low t y r cap f code a c hc

end ProximityPrize.SubmissionLower.OwnerTreeCheck6815
