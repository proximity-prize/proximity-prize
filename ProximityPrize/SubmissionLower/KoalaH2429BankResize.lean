import ProximityPrize.SubmissionLower.HighBankCore
import ProximityPrize.SubmissionLower.KoalaH2429Banks

set_option autoImplicit false

namespace KoalaH2429Banks

/-- The existing node and pole-moment receipts depend on the skeleton, not the seed width. -/
theorem resize_ok {t : P1_7.Bank} (h : P3_7_1.BankOK t) (U : ℕ) :
    P3_7_1.BankOK (resize t U) :=
  ⟨h.nodes, h.moment⟩

theorem resize_stages_ok (ws : List (ℕ × ℕ)) (ss : List P1_7.Stage)
    (h : ∀ s ∈ ss, P3_7_1.BankOK s.free ∧ P3_7_1.BankOK s.moving) :
    ∀ s ∈ List.zipWith (fun (u : ℕ × ℕ) t => resizeStage t u.1 u.2) ws ss,
      P3_7_1.BankOK s.free ∧ P3_7_1.BankOK s.moving := by
  induction ws generalizing ss with
  | nil => simp
  | cons uv ws ih =>
      cases ss with
      | nil => simp
      | cons t ts =>
          have ht := List.forall_mem_cons.mp h
          exact List.forall_mem_cons.mpr
            ⟨⟨resize_ok ht.1.1 uv.1, resize_ok ht.1.2 uv.2⟩, ih ts ht.2⟩

end KoalaH2429Banks
