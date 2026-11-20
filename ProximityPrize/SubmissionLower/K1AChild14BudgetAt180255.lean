import ProximityPrize.SubmissionLower.K1AAssembly6916
import ProximityPrize.SubmissionLower.C14BandsAt180255
import ProximityPrize.SubmissionLower.Fast029
set_option Elab.async false

/-! K1A.c14 at A' = 180255: prefix ledgers, budget and the reduction of `K1A.c14 Bg6916`
to the A' high-branch statement `K1A_14.c14A`. UNBUILT.

* Bridge band (w ≤ 3554): the A' ledger directPrice + fixedTotal + movingPrice ≤ highPrefixA is
  `K1A_14_2.ledger` (K1AC23_Fast029; movingPrice 86966099356717748, ratio 81889/45630).
* Paired bands (K1_14_3 endpoint fees Fast029.lean:1504-1513) with odePrice at A' and the bandNew
  endpoints (last 32700) stay below the official highPrefix values (c14_paired_ledger_check.json).
* With highRetainedNew (C14BandsAt180255) every band fits Bg6916.high = 242917318055663462. -/

section PackSource_K1A_14Budget
set_option autoImplicit true
namespace K1A_14
noncomputable section
open K1_14

def highPrefixA (w : ℤ) : ℕ :=
  if w ≤ 3554 then 132143966177788304
  else if w ≤ 8249 then 152632406338780469
  else if w ≤ 23999 then 173266420414027995
  else 200365480316570496

/-- `K1_14_3.odePrice` at A' (gap = 180255 - d). -/
def odePriceA (d b j : ℕ) : ℕ :=
  let T := 2*d - 3
  let a := 1 + T*(b-1)
  let v := min a (T*(j-1)+d)
  let gap := 180255-d
  ((262144-d)*((b-j)*v+j*a) + (gap-1))/gap + b*(b-1)+b

theorem paired_endpoint_fees (w : ℤ) (hlo : 3555 ≤ w) :
    (K1.p+1)*(381269+812+2907) + 3019828 + 2891 +
      odePriceA (131071 + (K1_14_At.bandNew w).endpoint) 381269 60998 +
      odePriceA (131071 + (K1_14_At.bandNew w).endpoint) 63 14 +
      odePriceA (131071 + (K1_14_At.bandNew w).endpoint) 118 24 +
      ((K1.p+1)*54375137 + 26769366519) ≤ highPrefixA w := by
  have hnot : ¬ w ≤ 3554 := by omega
  unfold K1_14_At.bandNew highPrefixA
  simp only [hnot, ite_false]
  split_ifs <;> decide

/-- Every band fits the 6916 high budget (`Bg6916.high`). -/
theorem high_budget (w : ℤ) (hlo : 2601 ≤ w) (hhi : w ≤ 32700) :
    highPrefixA w + K1_14_At.highRetainedNew w ≤ 242917318055663462 := by
  unfold highPrefixA K1_14_At.highRetainedNew
  split_ifs <;> decide

/-- The A' high branch (overhead 2601..32700): the remaining mathematical obligation of the
6916 candidate, to be proved by porting the K1_14 tree (c1..c6) onto the K1A anchors. -/
def c14A : Prop :=
  ∀ u deleted (M : K1A.AnchorModel u deleted) Γ, K1A.AnchoredFamily M Γ →
    2601 ≤ M.overhead → M.overhead ≤ 32700 →
    Γ.card ≤ highPrefixA M.overhead + K1_14_At.highRetainedNew M.overhead

theorem c14_6916_of (h : c14A) : K1A.c14 K1A_6916.Bg6916 :=
  fun u d M Γ F lo hi => (h u d M Γ F lo hi).trans (high_budget _ lo hi)

end
end K1A_14
end PackSource_K1A_14Budget
