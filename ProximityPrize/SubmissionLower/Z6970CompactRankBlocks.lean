import ProximityPrize.SubmissionLower.KoalaRectPoleBalance

set_option Elab.async false
set_option autoImplicit false

namespace CompactRank6970

open P1_7_1_3 (evaluate evaluate_append)

def Checked (f : ℕ → ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | start, (length, subtotal) :: rest =>
    evaluate (fun i => f (start+i)) length = subtotal ∧ Checked f (start+length) rest

private theorem sum_checked (f : ℕ → ℕ) (blocks : List (ℕ × ℕ)) (start : ℕ)
    (checked : Checked f start blocks) :
    evaluate (fun i => f (start+i)) (blocks.map Prod.fst).sum = (blocks.map Prod.snd).sum := by
  induction blocks generalizing start with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨length,total⟩ := head
    have tail : evaluate (fun i => f (start+(length+i))) (rest.map Prod.fst).sum =
        (rest.map Prod.snd).sum := by
      simpa only [Nat.add_assoc] using ih (start+length) checked.2
    change evaluate (fun i => f (start+i)) (length+(rest.map Prod.fst).sum) =
      total+(rest.map Prod.snd).sum
    exact evaluate_append checked.1 tail rfl rfl

theorem from_blocks {f : ℕ → ℕ} {start length total : ℕ} (blocks : List (ℕ × ℕ))
    (checked : Checked f start blocks)
    (size : (blocks.map Prod.fst).sum = length)
    (amount : (blocks.map Prod.snd).sum = total) :
    evaluate (fun i => f (start+i)) length = total := by
  rw [← size, ← amount]
  exact sum_checked f blocks start checked

end CompactRank6970
