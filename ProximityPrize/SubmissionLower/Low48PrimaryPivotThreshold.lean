import ProximityPrize.SubmissionLower.Low48PrimaryPivotAggregate
import ProximityPrize.SubmissionLower.KoalaLinearWindow

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Low48PrimaryPivot
open K1_13_2_3 KoalaLinearWindow KoalaPiecewiseTriangle Finset
open scoped BigOperators
open private contactExpr contactExpr_eq from ProximityPrize.SubmissionLower.Low48PrimaryPivotAggregate

/-- For a fixed derivative index, the retained contact region is a triangle
cut by four integer half-spaces in the last two exponents. -/
theorem contact_ge_iff (p : Triple) (q : ℤ) (h : p.index ≤ 1650) :
    q ≤ (p.contact : ℤ) ↔
      (p.f : ℤ) ≤ 1650-q ∧
      (p.c : ℤ)+3*(p.f : ℤ) ≥ 3*q-9900+5*(p.index : ℤ) ∧
      (p.c : ℤ)+2*(p.f : ℤ) ≥ q-4950+3*(p.index : ℤ) ∧
      (p.c : ℤ)+(p.f : ℤ) ≥ 2*q-4950+2*(p.index : ℤ) := by
  rcases p with ⟨b,c,f⟩
  let r := b%3
  let t := b/3
  have hr : r < 3 := Nat.mod_lt _ (by decide)
  have hbt : 3*t+r = b := by dsimp [r,t]; omega
  have he := contactExpr_eq c f r t hr (by rwa [hbt])
  rw [hbt] at he
  rw [← he]
  simp only [contactExpr, Expr.at, Expr.const, Line.at, zero_mul, add_zero, le_min_iff]
  simp only [Triple.index, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at *
  have hbt' : (b : ℤ) = 3*(t : ℤ)+(r : ℤ) := by omega
  omega

/-- Positive integers in an inclusive section at the fixed index. -/
def sectionWidth (j f : ℕ) : ℤ := ((j : ℤ)-3*(f : ℤ))/2+1

def sectionFloor (j f : ℕ) (q : ℤ) : ℤ :=
  max 0 (max
    (3*q-9900+5*(j : ℤ)-3*(f : ℤ))
    (max (q-4950+3*(j : ℤ)-2*(f : ℤ)) (2*q-4950+2*(j : ℤ)-(f : ℤ))))

theorem section_count (j f : ℕ) (q : ℤ) (hf : (f : ℤ) ≤ 1650-q) (hj : j ≤ 1650)
    (h : 3*f ≤ j) :
    (((Ico (0 : ℤ) (sectionWidth j f)).filter fun c =>
        q ≤ (((Triple.mk (j-2*c.toNat-3*f) c.toNat f).contact) : ℤ)).card : ℤ) =
      max 0 (sectionWidth j f-sectionFloor j f q) := by
  have hset : ((Ico (0 : ℤ) (sectionWidth j f)).filter fun c =>
        q ≤ (((Triple.mk (j-2*c.toNat-3*f) c.toNat f).contact) : ℤ)) =
      Ico (sectionFloor j f q) (sectionWidth j f) := by
    ext c
    simp only [mem_filter,mem_Ico,sectionFloor,max_le_iff]
    constructor
    · rintro ⟨⟨hc,hu⟩,hq⟩
      have hidx : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index = j := by
        simp only [Triple.index]
        dsimp [sectionWidth] at hu
        omega
      have hh : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index ≤ 1650 := by rw [hidx]; exact hj
      rw [contact_ge_iff _ _ hh,hidx] at hq
      dsimp only at hq
      simp only [Int.toNat_of_nonneg hc] at hq
      omega
    · rintro ⟨⟨hc,h₁,h₂,h₃⟩,hu⟩
      refine ⟨⟨hc,hu⟩,?_⟩
      have hidx : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index = j := by
        simp only [Triple.index]
        dsimp [sectionWidth] at hu
        omega
      have hh : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index ≤ 1650 := by rw [hidx]; exact hj
      rw [contact_ge_iff _ _ hh,hidx]
      dsimp only
      simp only [Int.toNat_of_nonneg hc]
      omega
  rw [hset,Int.card_Ico]
  omega

#print axioms contact_ge_iff
#print axioms section_count
end Low48PrimaryPivot
