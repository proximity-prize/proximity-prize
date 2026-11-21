import ProximityPrize.SubmissionLower.Rect52RegularResolved

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

namespace Rect52WindowPrice
open P1_7 (ceilRatio degreeAt)
open High52 (agreement singularFee singularDegree flatFee wholePrice p)
open Rect52Regular (wholeFee seedSum)

abbrev retained : ℕ := 170000000000000000

def seedCap (e : ℕ) : ℕ :=
  [414,410,406,402,396,392,386,382,376,370,365,360,353,346,334,322,290,243,191,136,77,14][e-1]?.getD 0

private theorem ratio_mono {n n' d : ℕ} (h : n ≤ n') : ceilRatio n d ≤ ceilRatio n' d :=
  Nat.div_le_div_right (Nat.add_le_add_right h _)

private theorem ceilRatio_anti (n : ℕ) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    ceilRatio n b ≤ ceilRatio n a := by
  have hb : 0 < b := ha.trans_le hab
  have ht : n ≤ ceilRatio n a * a := by
    unfold ceilRatio
    have h := Nat.mod_add_div (n+(a-1)) a
    have hr := Nat.mod_lt (n+(a-1)) ha
    rw [Nat.mul_comm a] at h
    omega
  change (n+(b-1))/b ≤ ceilRatio n a
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hb).mpr
  have h := ht.trans (Nat.mul_le_mul_left _ hab)
  rw [Nat.succ_mul]
  omega

private theorem graph_le {e v₀ v₁ : ℕ} (he : 2 ≤ e) :
    Rect51Fee.graphDegree e v₀ v₁ (max 1 v₀) (max 1 v₁) ≤
      2 * (9*e-10) * (max 1 v₀ * max 1 v₁) := by
  let b := max 1 v₀
  let c := max 1 v₁
  have hb : v₀≤b := le_max_right _ _
  have hc : v₁≤c := le_max_right _ _
  have h₁ : v₀*c+v₁*b≤2*(b*c) := by
    have h := Nat.add_le_add (Nat.mul_le_mul_right c hb) (Nat.mul_le_mul_right b hc)
    simpa only [two_mul,Nat.mul_comm c b] using h
  have h₂ := Nat.mul_le_mul hb hc
  have addition : e+2*(3*e-3)+(2*e-4)=9*e-10 := by omega
  calc
    _ ≤ 2*(e*(b*c)+(2*(b*c))*(3*e-3)+(b*c)*(2*e-4)) := by
      unfold Rect51Fee.graphDegree
      exact Nat.mul_le_mul_left _ (Nat.add_le_add
        (Nat.add_le_add (by rw [Nat.mul_assoc]) (Nat.mul_le_mul_right _ h₁))
        (Nat.mul_le_mul_right _ h₂))
    _ = 2*(9*e-10)*(b*c) := by rw [← addition]; ring

private def properEnvelope (e V n : ℕ) : ℕ :=
  let L := 131071-2391
  let d := 131071+2451
  let g := agreement-d
  let k := max 1 (ceilRatio (2*2451) n)
  ceilRatio (2*(9*e-10)*(n*(V+1-n))*(L+1+k)*(262144*g*L+agreement*(262144-d)*k))
    (agreement*g)

private def envelope (e V n : ℕ) : ℕ :=
  singularFee e V + (properEnvelope e V n + flatFee 2451 V + e)

private theorem rect_fee_le {e V : ℕ} {v : Fin 2 → ℕ}
    (he : 2 ≤ e) (hV : seedSum v ≤ V) (hV' : 1 ≤ V) :
    let n := min (max 1 (v 0)) (max 1 (v 1))
    wholeFee 2391 2451 e v ≤ envelope e V n := by
  let b := max 1 (v 0)
  let c := max 1 (v 1)
  let n := min b c
  have hsum : b+c ≤ V+1 := by
    change v 0 + v 1 ≤ V at hV
    dsimp [b,c]
    omega
  have hprod : b*c ≤ n*(V+1-n) := by
    rcases le_total b c with h | h
    · rw [show n = b from min_eq_left h]
      exact Nat.mul_le_mul_left _ (by omega)
    · rw [show n = c from min_eq_right h, Nat.mul_comm b c]
      exact Nat.mul_le_mul_left _ (by omega)
  have hn : 0 < n := lt_min (Nat.zero_lt_one.trans_le (le_max_left 1 (v 0)))
    (Nat.zero_lt_one.trans_le (le_max_left 1 (v 1)))
  have hκ : Rect51Proper.kappa 2451 (v 0) (v 1) ≤ max 1 (ceilRatio (2*2451) n) :=
    max_le (le_max_left _ _) (max_le
      ((ceilRatio_anti _ hn (min_le_left b c)).trans (le_max_right _ _))
      ((ceilRatio_anti _ hn (min_le_right b c)).trans (le_max_right _ _)))
  have hG := (graph_le (v₀ := v 0) (v₁ := v 1) he).trans (Nat.mul_le_mul_left _ hprod)
  have hsing : singularFee e (seedSum v) ≤ singularFee e V := by
    unfold High52.singularFee P1_7.singularFee P1_7.singularDegree
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hV)
  have hflat : flatFee 2451 (seedSum v) ≤ flatFee 2451 V := by
    unfold flatFee
    exact ratio_mono (Nat.mul_le_mul_left _ hV)
  have hproper : Rect51Proper.properFee agreement 2391 2451 e (v 0) (v 1) ≤
      properEnvelope e V n := by
    unfold Rect51Proper.properFee properEnvelope
    apply ratio_mono
    exact Nat.mul_le_mul
      (Nat.mul_le_mul hG (Nat.add_le_add_left hκ _))
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ hκ) _)
  unfold wholeFee Rect52Regular.regularFee envelope
  exact Nat.add_le_add hsing (Nat.add_le_add_right (Nat.add_le_add hproper hflat) _)

theorem guards {e V : ℕ} (h₁ : 1 ≤ e) (h₂ : e ≤ 22) (hV : V ≤ seedCap e) :
    singularDegree e V < p ∧ e*degreeAt 2451+V < p := by
  have h : singularDegree e (seedCap e)<p ∧ e*degreeAt 2451+seedCap e<p := by
    interval_cases e <;> decide
  exact ⟨(Nat.mul_le_mul_left _ hV).trans_lt h.1,(Nat.add_le_add_left hV _).trans_lt h.2⟩

private theorem envelope_bound {e : ℕ} (he₁ : 4 ≤ e) (he₂ : e ≤ 22) :
    ∀ n : Fin ((seedCap e+1)/2+1), envelope e (seedCap e) n ≤ retained := by
  interval_cases e <;> decide +kernel

theorem rect_retained {e : ℕ} (he₁ : 4 ≤ e) (he₂ : e ≤ 22) {v : Fin 2→ℕ}
    (hV : seedSum v ≤ seedCap e) : wholeFee 2391 2451 e v ≤ retained := by
  have hpos : 1 ≤ seedCap e := by interval_cases e <;> decide
  let n := min (max 1 (v 0)) (max 1 (v 1))
  have hsum : max 1 (v 0) + max 1 (v 1) ≤ seedCap e+1 := by
    change v 0 + v 1 ≤ seedCap e at hV
    omega
  have hsmall : n < (seedCap e+1)/2+1 := by
    have h₀ := min_le_left (max 1 (v 0)) (max 1 (v 1))
    have h₁ := min_le_right (max 1 (v 0)) (max 1 (v 1))
    omega
  exact (rect_fee_le (by omega) hV hpos).trans (envelope_bound he₁ he₂ ⟨n,hsmall⟩)

theorem stock_retained {e : ℕ} (he₁ : 1 ≤ e) (he₂ : e ≤ 3) :
    wholePrice 2391 2451 e (seedCap e) ≤ retained := by
  interval_cases e <;> decide

#print axioms rect_retained
#print axioms stock_retained
end Rect52WindowPrice
