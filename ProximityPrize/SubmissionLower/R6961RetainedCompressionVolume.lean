import ProximityPrize.SubmissionLower.R6960HeightCompression
import ProximityPrize.SubmissionLower.R6960QuadraticProjection

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

namespace Lower6961.RetainedCompression
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators Polynomial Matrix

abbrev Slots (a b : ℕ) := Fin (a+1) × Fin (b+1)

def columnWeight {a b : ℕ} (d : ℕ) (m : Slots a b) : ℕ := d*m.1.val

private theorem twice_width_sum (a b d W : ℕ) (hW : d*a≤W) :
    2*(∑ m : Slots a b, (W - columnWeight d m))+d*(b+1)*a*(a+1) =
      2*((a+1)*(b+1))*W := by
  have split : (∑ m : Slots a b, (W - columnWeight d m)) +
      (∑ m : Slots a b, columnWeight d m) = ((a+1)*(b+1))*W := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : Slots a b, W := Finset.sum_congr rfl (fun m _ => Nat.sub_add_cancel
        ((Nat.mul_le_mul_left d (Nat.le_of_lt_succ m.1.isLt)).trans hW))
      _ = _ := by simp
  have weight : 2*(∑ m : Slots a b, columnWeight d m)=d*(b+1)*a*(a+1) := by
    rw [Fintype.sum_prod_type]
    simp only [columnWeight, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    simp only [← mul_assoc, ← Finset.mul_sum]
    have sum : (∑ i : Fin (a+1), i.val) = ∑ i∈range (a+1), i :=
      Fin.sum_univ_eq_sum_range (fun i => i) (a+1)
    rw [sum]
    calc
      _ = d*(b+1)*((∑ i∈range (a+1), i)*2) := by ring
      _ = _ := by rw [Finset.sum_range_id_mul_two,Nat.add_sub_cancel]; ring
  calc
    _ = 2*((∑ m : Slots a b, (W - columnWeight d m)) +
        (∑ m : Slots a b, columnWeight d m)) := by rw [← weight, ← Nat.mul_add]
    _ = _ := by rw [split]; ring

def paddedSeed (v : ℕ) : ℕ := 10*v
def quotientSeed (v : ℕ) : ℕ := 9*v
def boxOrdinate (e : ℕ) : ℕ := 2*e
/-- Unified compressed height cutoff `(7e - 3) * (d / 4)` serving BOTH `High_lo` (`e < 58, d = 133520`)
and `High_hi` (`e < 48, d = 164652`) with `12e` proper-cut pricing unchanged! -/
def heightCap (e d : ℕ) : ℕ := (7*e-3)*(d/4)
def width (e d : ℕ) : ℕ := heightCap e d + e*d + 1
def quotientWidth (e d : ℕ) : ℕ := e*d+1

abbrev Rect (e v : ℕ) := Slots (boxOrdinate e) (paddedSeed v)
abbrev QuotRect (e v : ℕ) := Slots e (quotientSeed v)

private theorem count_comparison (e v d : ℕ) (he : 2≤e) (hd : 0<d) (hd4 : 4 ∣ d) :
    (Fintype.card (Rect e v)-Fintype.card (QuotRect e v))*width e d +
      (∑ m : QuotRect e v, (quotientWidth e d - columnWeight d m)) <
      ∑ m : Rect e v, (width e d - columnWeight d m) := by
  obtain ⟨d₀, hd₀⟩ := hd4
  have hd₀_pos : 0 < d₀ := by omega
  have hdiv : d / 4 = d₀ := by rw [hd₀]; exact Nat.mul_div_cancel_left d₀ (by decide)
  let N := (2*e+1)*(10*v+1)
  let K := (e+1)*(9*v+1)
  have kN : K≤N := Nat.mul_le_mul (by omega) (by omega)
  have large : d*(2*e)≤width e d := by
    unfold width heightCap
    rw [hdiv, hd₀]
    have : 4 * d₀ * (2 * e) = 8 * e * d₀ := by ring
    have : (7 * e - 3) * d₀ + e * (4 * d₀) = (11 * e - 3) * d₀ := by
      have h1 : e * (4 * d₀) = (4 * e) * d₀ := by ring
      rw [h1, ← Nat.add_mul]
      congr 1; omega
    have hle : 8 * e ≤ 11 * e - 3 := by omega
    have hmul := Nat.mul_le_mul_right d₀ hle
    omega
  have small : d*e≤e*d+1 := by rw [Nat.mul_comm d e]; omega
  let src := ∑ m : Rect e v, (width e d - columnWeight d m)
  let qt := ∑ m : QuotRect e v, (quotientWidth e d - columnWeight d m)
  have dl : 2*src+d*(10*v+1)*(2*e)*(2*e+1)=2*N*width e d :=
    twice_width_sum (2*e) (10*v) d (width e d) large
  have ds : 2*qt+d*(9*v+1)*e*(e+1)=2*K*quotientWidth e d :=
    twice_width_sum e (9*v) d (quotientWidth e d) small
  have total : 2*N*width e d=2*((N-K)*width e d)+2*K*width e d := by
    calc
      _ = 2*(N-K+K)*width e d := by rw [Nat.sub_add_cancel kN]
      _ = _ := by ring
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le he
  have diff : d*(9*v+1)*e*(e+1)+2*K*width e d =
      d*(10*v+1)*(2*e)*(2*e+1)+2*K*quotientWidth e d+
        d₀*(v*(2*u^2+36*u+10)+2*u^2+12*u+10) := by
    dsimp only [K,width,heightCap,quotientWidth]
    rw [hdiv, hd₀, hu, show 7*(2+u)-3=7*u+11 by omega]
    ring
  have positive : 0<d₀*(v*(2*u^2+36*u+10)+2*u^2+12*u+10) := by positivity
  have cards : Fintype.card (Rect e v)=N ∧ Fintype.card (QuotRect e v)=K := by
    constructor
    · change Fintype.card (Fin (2*e+1) × Fin (10*v+1))=(2*e+1)*(10*v+1)
      rw [Fintype.card_prod, Fintype.card_fin,Fintype.card_fin]
    · change Fintype.card (Fin (e+1) × Fin (9*v+1))=(e+1)*(9*v+1)
      rw [Fintype.card_prod, Fintype.card_fin,Fintype.card_fin]
  rw [cards.1,cards.2]
  change (N-K)*width e d+qt<src
  omega

theorem relation_space_gt {F : Type*} [Field F] {α : Type*} [Finite α]
    {e v d : ℕ} (he : 2≤e) (hd : 0<d) (hd4 : 4 ∣ d) (A : Matrix α (Rect e v) (Polynomial F))
    (columns : ∀ i j,(A i j).natDegree≤columnWeight d j)
    (ker : Fintype.card (QuotRect e v) ≤ Module.finrank (FractionRing (Polynomial F))
      (LinearMap.ker (A.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).mulVecLin)) :
    Module.finrank F (Lower6960.HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) <
      Module.finrank F (LinearMap.ker (Lower6960.HeightCompression.evaluation A
        (columnWeight d) (width e d))) := by
  have lower := Lower6960.HeightCompression.weighted_kernel A (columnWeight d) (width e d)
    columns (Fintype.card (QuotRect e v)) ker
  have large := count_comparison e v d he hd hd4
  have dim : Module.finrank F (Lower6960.HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) =
      ∑ j : QuotRect e v, (quotientWidth e d - columnWeight d j) := by
    simp [Lower6960.HeightCompression.Coeffs,Module.finrank_pi_fintype,(degreeLTEquiv F _).finrank_eq]
  rw [dim]
  omega

/-- Band parameters shared across the entire MarkedEvaluation / MonicChart / Retained pipeline. -/
structure MarkedBand where
  wordDegree : ℕ
  maxOrd : ℕ
  pos_d : 0 < wordDegree
  dvd4 : 4 ∣ wordDegree
  lt_A : wordDegree < 179818
  small_E : maxOrd < K1.p
  vote_scale : CurvatureVotes.VoteScale 179818 wordDegree 18
  deg2_tame : 2 * heightCap 2 wordDegree < K1.p
  room : ∀ e < maxOrd, 3 ≤ e → 2 * ((10 * e ^ 2 - 13 * e + 3) * (wordDegree / 4)) < K1.p
  vert : ∀ e < maxOrd, 3 ≤ e → 2 * ((e - 1) * heightCap e wordDegree) < K1.p

def bandHi : MarkedBand where
  wordDegree := 164652
  maxOrd := 48
  pos_d := by decide
  dvd4 := ⟨41163, by decide⟩
  lt_A := by decide
  small_E := by decide
  vote_scale := Or.inl (by decide +kernel)
  deg2_tame := by unfold heightCap; decide +kernel
  room := fun e he _ =>
    (by decide +kernel : ∀ i : Fin 48, 2 * ((10 * i.val ^ 2 - 13 * i.val + 3) * (164652 / 4)) < K1.p) ⟨e, he⟩
  vert := fun e he _ =>
    (by decide +kernel : ∀ i : Fin 48, 2 * ((i.val - 1) * heightCap i.val 164652) < K1.p) ⟨e, he⟩

def bandLo : MarkedBand where
  wordDegree := 133520
  maxOrd := 58
  pos_d := by decide
  dvd4 := ⟨33380, by decide⟩
  lt_A := by decide
  small_E := by decide
  vote_scale := Or.inl (by decide +kernel)
  deg2_tame := by unfold heightCap; decide +kernel
  room := fun e he _ =>
    (by decide +kernel : ∀ i : Fin 58, 2 * ((10 * i.val ^ 2 - 13 * i.val + 3) * (133520 / 4)) < K1.p) ⟨e, he⟩
  vert := fun e he _ =>
    (by decide +kernel : ∀ i : Fin 58, 2 * ((i.val - 1) * heightCap i.val 133520) < K1.p) ⟨e, he⟩

end
end Lower6961.RetainedCompression
