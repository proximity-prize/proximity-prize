import ProximityPrize.SubmissionLower.KoalaRectReceipts

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace KoalaDiagonalPrice
open HighCore82209 (agreement start finish retainedCap)
open P1 (blockLength p)
open P1_7 (ceilRatio degreeAt quotientOrder singularDegree singularFee)
open KoalaRectReceipts (paidCap)

def liftIndex (hi v₀ v₁ : ℕ) : ℕ :=
  max 1 (max (ceilRatio (2*hi) (max 1 v₀)) (ceilRatio (2*hi) (max 1 v₁)))

private theorem le_mul_ceilRatio (n d : ℕ) (hd : 0 < d) :
    n ≤ d * ceilRatio n d := by
  have he := Nat.div_add_mod (n + (d-1)) d
  have hr := Nat.mod_lt (n + (d-1)) hd
  change n ≤ d * ((n + (d-1)) / d)
  omega

theorem liftIndex_spec (hi v₀ v₁ : ℕ) :
    0 < liftIndex hi v₀ v₁ ∧
    2*hi ≤ max 1 v₀ * liftIndex hi v₀ v₁ ∧
    2*hi ≤ max 1 v₁ * liftIndex hi v₀ v₁ := by
  refine ⟨lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..), ?_, ?_⟩
  · exact (le_mul_ceilRatio _ _ (lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..))).trans
      (Nat.mul_le_mul_left _ ((le_max_left ..).trans (le_max_right ..)))
  · exact (le_mul_ceilRatio _ _ (lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..))).trans
      (Nat.mul_le_mul_left _ ((le_max_right ..).trans (le_max_right ..)))

def surfaceDegree (e v₀ v₁ : ℕ) : ℕ :=
  let b := max 1 v₀
  let c := max 1 v₁
  2*(e*b*c + v₀*(e-1)*c + v₁*(e-1)*b)

def properBudget (A lo hi e v₀ v₁ : ℕ) : ℕ :=
  let d := degreeAt hi
  let ell := quotientOrder lo
  let k := liftIndex hi v₀ v₁
  surfaceDegree e v₀ v₁ * (2*ell+1+k) *
    (2*blockLength*(A-d)*ell + A*(blockLength-d)*k)

def charge (A lo hi e v₀ v₁ : ℕ) : ℕ :=
  let g := A - degreeAt hi
  ceilRatio (properBudget A lo hi e v₀ v₁) (A*g) +
    ceilRatio ((blockLength-A)*(p+1)*(v₀+v₁)) g + singularFee e (v₀+v₁) + e

private def GradeCheck (e : ℕ) : Prop :=
  ∀ a : Fin (paidCap e + 1),
    charge agreement (start .h2367) (finish .h2367) e a.val (paidCap e - a.val) ≤
      retainedCap .h2367

private instance (e : ℕ) : Decidable (GradeCheck e) := inferInstanceAs (Decidable (∀ a : Fin (paidCap e + 1), _ ≤ _))

private theorem grade3 : GradeCheck 3 := by decide +kernel
private theorem grade4 : GradeCheck 4 := by decide +kernel
private theorem grade5 : GradeCheck 5 := by decide +kernel
private theorem grade6 : GradeCheck 6 := by decide +kernel
private theorem grade7 : GradeCheck 7 := by decide +kernel
private theorem grade8 : GradeCheck 8 := by decide +kernel
private theorem grade9 : GradeCheck 9 := by decide +kernel
private theorem grade10 : GradeCheck 10 := by decide +kernel
private theorem grade11 : GradeCheck 11 := by decide +kernel
private theorem grade12 : GradeCheck 12 := by decide +kernel
private theorem grade13 : GradeCheck 13 := by decide +kernel
private theorem grade14 : GradeCheck 14 := by decide +kernel
private theorem grade15 : GradeCheck 15 := by decide +kernel
private theorem grade16 : GradeCheck 16 := by decide +kernel
private theorem grade17 : GradeCheck 17 := by decide +kernel
private theorem grade18 : GradeCheck 18 := by decide +kernel
private theorem grade19 : GradeCheck 19 := by decide +kernel
private theorem grade20 : GradeCheck 20 := by decide +kernel
private theorem grade21 : GradeCheck 21 := by decide +kernel
private theorem grade22 : GradeCheck 22 := by decide +kernel
private theorem grade23 : GradeCheck 23 := by decide +kernel
private theorem grade24 : GradeCheck 24 := by decide +kernel

theorem charge_le {e v₀ v₁ : ℕ} (hel : 3 ≤ e) (heu : e < 25)
    (hsum : v₀+v₁ = paidCap e) :
    charge agreement (start .h2367) (finish .h2367) e v₀ v₁ ≤ retainedCap .h2367 := by
  have hcheck : GradeCheck e := by
    interval_cases e <;> first | exact grade3 | exact grade4 | exact grade5 | exact grade6 | exact grade7 | exact grade8 | exact grade9 | exact grade10 | exact grade11 | exact grade12 | exact grade13 | exact grade14 | exact grade15 | exact grade16 | exact grade17 | exact grade18 | exact grade19 | exact grade20 | exact grade21 | exact grade22 | exact grade23 | exact grade24
  let a : Fin (paidCap e + 1) := ⟨v₀, by omega⟩
  have hv : paidCap e - v₀ = v₁ := by omega
  simpa only [a, hv] using hcheck a

theorem guards {e : ℕ} (hel : 3 ≤ e) (heu : e < 25) :
    singularDegree e (paidCap e) < p ∧ e * degreeAt (finish .h2367) + paidCap e < p := by
  interval_cases e <;> decide +kernel

#print axioms charge_le
#print axioms guards
end KoalaDiagonalPrice
