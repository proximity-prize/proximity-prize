import ProximityPrize.SubmissionLower.ZNjr9pa
import ProximityPrize.SubmissionLower.ZcG5Ygd
set_option Elab.async false
set_option autoImplicit true
namespace dnZ
open MvPolynomial

open P1_6_1_3_2 (adjacent shell shell_coeff shell_bind_adjacent)
open private JE from ProximityPrize.SubmissionLower.ZzNTDEa


open fP (lP m9)
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private def step (k :ℕ) :Poly →ₗ[F] Poly :=
  JE.toLinearMap-(k :F)•LinearMap.id
private theorem step_eq (k :ℕ) (P:Poly) :
    step k P=shell P+((49:F)-(k :F))•P:= by
  change JE P-(k :F)•P= _
  rw [shell,sub_smul]
  abel
private theorem step_coeff (k :ℕ) (e m:Exp)
    (h:m.weight lP≤e.weight lP∨e.weight lP+3< m.weight lP) :
    (step k (monomial e 1)).coeff m=if e=m then (e.weight lP:F) - k else 0:= by
  rw [step_eq]
  change (shell (monomial e (1 :F))).coeff m +
    (((49:F)-(k :F))•monomial e (1 :F)).coeff m= _
  rw [coeff_smul,shell_coeff e m h,coeff_monomial]
  by_cases he :e=m <;> simp [he,smul_eq_mul]
private theorem step_adjacent (k :ℕ) (e :Exp) :
    step k (bind₁ adjacent (monomial e 1)) =
      ((e.weight m9:F) - k)•bind₁ adjacent (monomial e 1) := by
  rw [step_eq,shell_bind_adjacent]
  simp only [mul_one,← add_smul]
  congr 1
  ring
end
end dnZ
