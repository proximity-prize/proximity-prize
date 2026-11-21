import ProximityPrize.SubmissionLower.HighPrices82180
import ProximityPrize.SubmissionLower.GoldBranch7N3

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace HighLoss82180

open P3 (HighBand p)
open P3_7 (degreeAt fees)
open P3_7_3 (history cutWeight lossWeight laterCount seedLimit pointLimit)
open P1_7_4 (Mass dotQ running weightedBill)
open HighBanks82180 (start)
open HighPrices82180 (finish)
open scoped BigOperators

abbrev factor : ℚ := 101 / 100
private theorem one_le : (1 : ℚ) ≤ factor := by norm_num [factor]
private theorem positive : (0 : ℚ) ≤ factor := by norm_num [factor]

private def alpha (A h : ℕ) : ℚ := 1 + 2 * ((262144 : ℚ)/A) * degreeAt h
private def mu (A h : ℕ) : ℚ := ((262144 - degreeAt h : ℕ) : ℚ) / (A - degreeAt h : ℕ)

def curve (A h g : ℕ) : ℚ := (2*(g : ℚ)-1)*alpha A h + mu A h

private theorem old_curve (h g : ℕ) : curve 179983 h g = P3_7.curveUnit h g := rfl

theorem curve_le (b : HighBand) {g : ℕ} (hg : 0 < g) :
    curve 179964 (finish b) g ≤ factor * P3_7.curveUnit b.row.hi g := by
  have h₁ : alpha 179964 (finish b) ≤ factor * alpha 179983 b.row.hi := by
    cases b <;> decide +kernel
  have h₂ : mu 179964 (finish b) ≤ factor * mu 179983 b.row.hi := by
    cases b <;> decide +kernel
  have hpos : (1 : ℚ) ≤ g := by exact_mod_cast hg
  rw [← old_curve]
  unfold curve
  calc
    _ ≤ (2*(g:ℚ)-1)*(factor*alpha 179983 b.row.hi) + factor*mu 179983 b.row.hi :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ (by linarith)) h₂
    _ = _ := by ring

structure Rate (b : HighBand) (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ) / 81 ≤ a
  height : 0 ≤ h
  interpolation : ∀ g : ℕ, 0 < g → g ≤ 80 →
    max 0 (1-a*g/((p+1 : ℕ) : ℚ)) * curve 179964 (finish b) g ≤ h

private theorem lift_rate (b : HighBand) {a h : ℚ} (r : P3_7_3.RateOK b.row.hi a h) :
    Rate b (factor*a) (factor*h) := by
  have ha : 0 ≤ a := (by positivity : (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ) / 81).trans r.degree
  have hscale : a ≤ factor*a := by simpa only [one_mul] using mul_le_mul_of_nonneg_right one_le ha
  refine ⟨r.degree.trans hscale, mul_nonneg positive r.height, ?_⟩
  intro g hg hu
  let Q : ℚ := (p+1 : ℕ)
  let small := max 0 (1-(factor*a)*g/Q)
  let large := max 0 (1-a*g/Q)
  have hcomp : small ≤ large := by
    apply max_le_max_left
    exact sub_le_sub_left (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg g)) (by dsimp [Q]; positivity)) _
  have hu₀ : 0 ≤ P3_7.curveUnit b.row.hi g := by
    rw [← old_curve]
    unfold curve alpha mu
    have hge : (1 : ℚ) ≤ g := by exact_mod_cast hg
    have hn : (0 : ℚ) ≤ 2*(g:ℚ)-1 := by linarith
    positivity
  calc
    _ ≤ small * (factor * P3_7.curveUnit b.row.hi g) :=
      mul_le_mul_of_nonneg_left (curve_le b hg) (le_max_left _ _)
    _ ≤ large * (factor * P3_7.curveUnit b.row.hi g) :=
      mul_le_mul_of_nonneg_right hcomp (mul_nonneg positive hu₀)
    _ = factor * (large * P3_7.curveUnit b.row.hi g) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (r.interpolation g hg hu) positive

private theorem fold_nonneg {α : Type*} (f : ℚ → α → ℚ)
    (hf : ∀ a i, 0 ≤ a → 0 ≤ f a i) (xs : List α) (a : ℚ) (ha : 0 ≤ a) :
    0 ≤ xs.foldl f a := by
  induction xs generalizing a with
  | nil => exact ha
  | cons i xs ih => exact ih _ (hf _ i ha)

private theorem history_nonneg (b : HighBand) (i : ℕ) (k : Fin 4) : 0 ≤ history b i k := by
  have corner (s t : K1_14.Shape) (r m : ℕ) (v : Bool) : 0 ≤ P1_7_4.cornerBound s t r m v k := by
    unfold P1_7_4.cornerBound
    exact fold_nonneg max (fun a x h => h.trans (le_max_left a x)) _ 0 le_rfl
  induction i with
  | zero => exact Nat.cast_nonneg _
  | succ i ih =>
    apply le_min ih
    unfold P3_7_3.stageCap P1_7_4.pairedCap
    exact fold_nonneg _ (fun a j ha => le_min ha (corner _ _ _ _ _)) _ _ (corner _ _ _ _ _)

private theorem seed_nonneg (b : HighBand) : 0 ≤ seedLimit b :=
  Finset.sum_nonneg fun i _ => P1_7_4.dotQ_nonneg (fun _ => sub_nonneg.mpr (le_max_left _ _))
    (history_nonneg b i)

private theorem scale_running (v : ℕ → Mass) (n : ℕ) (k : Fin 4) :
    running (fun i j => factor*v i j) n k = factor*running v n k := by
  induction n with
  | zero => simp [running]
  | succ n ih => change max _ _ = _ * max _ _; rw [ih, mul_max_of_nonneg _ _ positive]

private theorem scale_bill (n : ℕ) (v hist : ℕ → Mass) :
    weightedBill n (fun i k => factor*v i k) hist = factor * weightedBill n v hist := by
  unfold weightedBill
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [dotQ, scale_running, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem old_discount (b : HighBand) : start b < 7773 → b.row.lo < 7773 := by
  cases b <;> decide +kernel

private theorem old_direct (b : HighBand) : 7773 ≤ start b → 7773 ≤ b.row.lo := by
  cases b <;> decide +kernel

private theorem rescale_cost {x y z : ℚ} (hc : x+y ≤ z) (hy : y ≤ factor*y) :
    factor*x+y ≤ factor*z := by
  calc
    _ ≤ factor*x + factor*y := add_le_add le_rfl hy
    _ = factor*(x+y) := (mul_add _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hc positive

/-- The discounted loss bounds at the new agreement for the first two height intervals. -/
theorem discounted (b : HighBand) (hb : start b < 7773) :
    ∃ a h : ℕ → ℚ,
      (∀ i ≤ laterCount b, Rate b (a i) (h i) ∧
        min (seedLimit b) (dotQ (cutWeight b 0 i) (history b i)) ≤ a i) ∧
      weightedBill (laterCount b+1) (lossWeight b a h) (history b) + seedLimit b ≤
        factor * ((fees b).loss : ℚ) := by
  have ho : b.row.lo < 7773 := old_discount b hb
  obtain ⟨a,h,good,cost⟩ := (P3_7_3_4.proof b).discount ho
  refine ⟨fun i => factor*a i, fun i => factor*h i, ?_, ?_⟩
  · intro i hi
    obtain ⟨r,hm⟩ := good i hi
    have ha : 0 ≤ a i := (by positivity : (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81).trans r.degree
    exact ⟨lift_rate b r, hm.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right one_le ha)⟩
  · have same : lossWeight b (fun i => factor*a i) (fun i => factor*h i) =
        fun i k => factor * lossWeight b a h i k := by
      funext i k
      unfold lossWeight
      ring
    rw [same, scale_bill]
    have hs : seedLimit b ≤ factor * seedLimit b := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right one_le (seed_nonneg b)
    exact rescale_cost cost hs

theorem direct (b : HighBand) (hb : 7773 ≤ start b) :
    ((p+1 : ℕ) : ℚ)*seedLimit b ≤ ((fees b).loss : ℚ) :=
  (P3_7_3_4.proof b).direct (old_direct b hb)

theorem points (b : HighBand) : pointLimit b ≤ ((fees b).point : ℚ) := (P3_7_3_4.proof b).points

#print axioms discounted
end HighLoss82180
