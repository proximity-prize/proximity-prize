/- Apache-2.0. 68.36 degree-interval receipts by Bome2017 over the BitWonka and Lucieno physical bounds. -/
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.Night6836OfferAtoms
namespace Koala6835.Offers
set_option autoImplicit false
def stepOK (bank : ℕ → Offer) (raw : ℕ → ℕ → ℕ → ℕ) (r e lo hi cap id : ℕ) : Bool :=
  if id = 0 then decide (raw r e (hi-(r+e)) ≤ cap)
  else let w := bank (id-1); decide (valid w r e lo hi ∧ w.fee ≤ cap)

def check (bank : ℕ → Offer) (raw : ℕ → ℕ → ℕ → ℕ) (r e hi cap : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0,lo,_ => decide (hi < lo)
  | fuel+1,lo,code =>
    if hi < lo then true else
      let stop := min hi (lo + code % 16777216 / 1024)
      stepOK bank raw r e lo stop cap (code % 1024) &&
        check bank raw r e hi cap fuel (stop+1) (code/16777216)

theorem price (bank : ℕ → Offer) (raw : ℕ → ℕ → ℕ → ℕ)
    (mono : ∀ r e a b, a≤b → raw r e a≤raw r e b)
    (r e t population : ℕ) (hraw : population ≤ raw r e (t-(r+e)))
    (hpacket : ∀ i, valid (bank i) r e t t → population ≤ (bank i).fee)
    (hi cap fuel lo code : ℕ) (ok : check bank raw r e hi cap fuel lo code = true)
    (lb : lo ≤ t) (ub : t ≤ hi) : population ≤ cap := by
  induction fuel generalizing lo code with
  | zero => simp only [check,decide_eq_true_eq] at ok; omega
  | succ n ih =>
    have ha : ¬hi<lo := by omega
    rw [check,if_neg ha,Bool.and_eq_true] at ok
    let stop := min hi (lo + code % 16777216 / 1024)
    by_cases hs : t ≤ stop
    · have v := ok.1
      change stepOK bank raw r e lo stop cap (code%1024) = true at v
      unfold stepOK at v
      split at v
      · exact hraw.trans ((mono r e _ _ (Nat.sub_le_sub_right hs _)).trans (of_decide_eq_true v))
      · have hv := of_decide_eq_true v
        apply (hpacket _ ?_).trans hv.2
        obtain ⟨hr,hy,hl,hh⟩ := hv.1
        exact ⟨hr,hy,hl.trans lb,hs.trans hh⟩
    · exact ih (stop+1) _ ok.2 (by omega)
#print axioms price
end Koala6835.Offers
