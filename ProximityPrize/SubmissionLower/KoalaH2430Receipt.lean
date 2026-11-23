import ProximityPrize.SubmissionLower.KoalaTwoSectionPrice
import ProximityPrize.SubmissionLower.HighCore82258Family
import ProximityPrize.SubmissionLower.KoalaH2430TerminalData
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace KoalaH2430Receipt

open P1_7 (ceilRatio quotientOrder singularDegree singularFee degreeAt)

abbrev cap : ℕ := 273115485059352112
abbrev h : ℕ := 2430

abbrev paidCap := KoalaH2430Terminal.paidCap

def prefixFee2430 (e : ℕ) : ℕ :=
  if e = 16 then 109219137712556257 else
  if e = 17 then 109096694551937043 else 111259522915138880

def charge (e a b : ℕ) : ℕ :=
  KoalaTwoSectionPrice.charge 179876 h h e a b

theorem guards {e : ℕ} (he : 1 ≤ e) (hu : e < 23) :
    singularDegree e (paidCap e) < P1.p ∧ e * degreeAt h + paidCap e < P1.p := by
  interval_cases e <;> decide

theorem fixed_budget {e : ℕ} (he : e < 23) : prefixFee2430 e + e ≤ cap := by
  interval_cases e <;> decide

theorem small_paid {e : ℕ} (he : 1 ≤ e) (hu : e ≤ 2) :
    prefixFee2430 e + (singularFee e (paidCap e) +
      HighCore82258.persistentFee h h e (paidCap e)) ≤ cap := by
  interval_cases e <;> decide

private def OrdinaryCheck (e : ℕ) : Prop :=
  ∀ a : Fin (paidCap e + 1), prefixFee2430 e + charge e a.val (paidCap e - a.val) ≤ cap

private instance (e : ℕ) : Decidable (OrdinaryCheck e) :=
  inferInstanceAs (Decidable (∀ _a : Fin (paidCap e+1), _ ≤ _))

private theorem paid3 : OrdinaryCheck 3 := by decide +kernel
private theorem paid4 : OrdinaryCheck 4 := by decide +kernel
private theorem paid5 : OrdinaryCheck 5 := by decide +kernel
private theorem paid6 : OrdinaryCheck 6 := by decide +kernel
private theorem paid7 : OrdinaryCheck 7 := by decide +kernel
private theorem paid8 : OrdinaryCheck 8 := by decide +kernel
private theorem paid9 : OrdinaryCheck 9 := by decide +kernel
private theorem paid10 : OrdinaryCheck 10 := by decide +kernel
private theorem paid11 : OrdinaryCheck 11 := by decide +kernel
private theorem paid12 : OrdinaryCheck 12 := by decide +kernel
private theorem paid13 : OrdinaryCheck 13 := by decide +kernel
private theorem paid14 : OrdinaryCheck 14 := by decide +kernel
private theorem paid15 : OrdinaryCheck 15 := by decide +kernel
private theorem paid16 : OrdinaryCheck 16 := by decide +kernel
private theorem paid17 : OrdinaryCheck 17 := by decide +kernel
private theorem paid18 : OrdinaryCheck 18 := by decide +kernel
private theorem paid19 : OrdinaryCheck 19 := by decide +kernel
private theorem paid20 : OrdinaryCheck 20 := by decide +kernel
private theorem paid21 : OrdinaryCheck 21 := by decide +kernel
private theorem paid22 : OrdinaryCheck 22 := by decide +kernel

theorem ordinary_paid {e a b : ℕ} (he : 3 ≤ e) (hu : e < 23)
    (hab : a+b = paidCap e) :
    prefixFee2430 e + charge e a b ≤ cap := by
  have hc : OrdinaryCheck e := by
    interval_cases e <;>
      first | exact paid3 | exact paid4 | exact paid5 | exact paid6 | exact paid7 | exact paid8 | exact paid9 | exact paid10 | exact paid11 | exact paid12 | exact paid13 | exact paid14 | exact paid15 | exact paid16 | exact paid17 | exact paid18 | exact paid19 | exact paid20 | exact paid21 | exact paid22
  let j : Fin (paidCap e+1) := ⟨a, by omega⟩
  have hb : paidCap e - a = b := by omega
  simpa only [j,hb] using hc j

#print axioms ordinary_paid
#print axioms small_paid

end KoalaH2430Receipt
