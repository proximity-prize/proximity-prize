import ProximityPrize.SubmissionLower.R6960HeightCompression

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

namespace Lower6960.RetainedCompression
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
def heightCap (e d : ℕ) : ℕ := (2*e-1)*d
def width (e d : ℕ) : ℕ := (3*e-1)*d+1
def quotientWidth (e d : ℕ) : ℕ := e*d+1

abbrev Rect (e v : ℕ) := Slots (boxOrdinate e) (paddedSeed v)
abbrev QuotRect (e v : ℕ) := Slots e (quotientSeed v)

private theorem count_comparison (e v d : ℕ) (he : 2≤e) (hd : 0<d) :
    (Fintype.card (Rect e v)-Fintype.card (QuotRect e v))*width e d +
      (∑ m : QuotRect e v, (quotientWidth e d - columnWeight d m)) <
      ∑ m : Rect e v, (width e d - columnWeight d m) := by
  let N := (2*e+1)*(10*v+1)
  let K := (e+1)*(9*v+1)
  have kN : K≤N := Nat.mul_le_mul (by omega) (by omega)
  have large : d*(2*e)≤(3*e-1)*d+1 := by
    exact (Nat.mul_comm d (2*e)).le.trans ((Nat.mul_le_mul_right d (by omega)).trans (Nat.le_add_right ..))
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
        d*(v*(5*u^2+27*u+16)+u^2+5*u+4) := by
    dsimp only [K,width,quotientWidth]
    rw [hu,show 3*(2+u)-1=3*u+5 by omega]
    ring
  have positive : 0<d*(v*(5*u^2+27*u+16)+u^2+5*u+4) := by positivity
  have cards : Fintype.card (Rect e v)=N ∧ Fintype.card (QuotRect e v)=K := by
    constructor
    · change Fintype.card (Fin (2*e+1) × Fin (10*v+1))=(2*e+1)*(10*v+1)
      rw [Fintype.card_prod, Fintype.card_fin,Fintype.card_fin]
    · change Fintype.card (Fin (e+1) × Fin (9*v+1))=(e+1)*(9*v+1)
      rw [Fintype.card_prod, Fintype.card_fin,Fintype.card_fin]
  rw [cards.1,cards.2]
  change (N-K)*width e d+qt<src
  omega

/-- The actual weighted kernel is strictly larger than the entire quotient
box when the compressible factor has weight above `heightCap e d`. -/
theorem relation_space_gt {F : Type*} [Field F] {α : Type*} [Finite α]
    {e v d : ℕ} (he : 2≤e) (hd : 0<d) (A : Matrix α (Rect e v) (Polynomial F))
    (columns : ∀ i j,(A i j).natDegree≤columnWeight d j)
    (ker : Fintype.card (QuotRect e v) ≤ Module.finrank (FractionRing (Polynomial F))
      (LinearMap.ker (A.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).mulVecLin)) :
    Module.finrank F (HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) <
      Module.finrank F (LinearMap.ker (HeightCompression.evaluation A
        (columnWeight d) (width e d))) := by
  have lower := HeightCompression.weighted_kernel A (columnWeight d) (width e d)
    columns (Fintype.card (QuotRect e v)) ker
  have large := count_comparison e v d he hd
  have dim : Module.finrank F (HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) =
      ∑ j : QuotRect e v, (quotientWidth e d - columnWeight d j) := by
    simp [HeightCompression.Coeffs,Module.finrank_pi_fintype,(degreeLTEquiv F _).finrank_eq]
  rw [dim]
  omega

/-- Twice the raw discriminant bound, including the contribution at infinity,
is smaller than the characteristic throughout the retained range. -/
theorem tame_height {e d : ℕ} (he : e≤47) (hd : d≤164632) :
    2*((3*e-2)*(e-1)*d+(e-1))<2130706433 :=
  (Nat.mul_le_mul_left 2 (Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 he) 2)
      (Nat.sub_le_sub_right he 1)) hd)
    (Nat.sub_le_sub_right he 1))).trans_lt (by decide +kernel)

#print axioms relation_space_gt
end
end Lower6960.RetainedCompression
