import ProximityPrize.SubmissionLower.MergedInfra6815_3
namespace ProximityPrize.SubmissionLower.TriangularKernel6815
open TriangularAffine6815
set_option autoImplicit false
set_option maxHeartbeats 2000000

def endpoint (cc cs clo chi charge slope pc ps plo z : ℕ) : Bool :=
  Nat.ble (left cc cs clo charge slope clo z) (right pc ps plo z) &&
    Nat.ble (left cc cs clo charge slope (min chi z) z) (right pc ps plo z)

theorem endpoint_iff (cc cs clo chi charge slope pc ps plo z : ℕ) :
    endpoint cc cs clo chi charge slope pc ps plo z=true ↔
      EndAt cc cs clo chi charge slope pc ps plo z := by
  simp only [endpoint,EndAt,Bool.and_eq_true,Nat.ble_eq]

def triangle (cc cs clo chi charge slope pc ps plo phi : ℕ) : Bool :=
  Bool.rec true
    (endpoint cc cs clo chi charge slope pc ps plo (max plo clo) &&
      endpoint cc cs clo chi charge slope pc ps plo phi &&
      endpoint cc cs clo chi charge slope pc ps plo (min phi (max (max plo clo) chi)))
    (Nat.ble clo chi && Nat.ble (max plo clo) phi)

theorem triangle_iff (cc cs clo chi charge slope pc ps plo phi : ℕ) :
    triangle cc cs clo chi charge slope pc ps plo phi=true ↔
      check cc cs clo chi charge slope pc ps plo phi=true := by
  by_cases h : clo≤chi ∧ max plo clo≤phi
  · have hg : (Nat.ble clo chi && Nat.ble (max plo clo) phi)=true := by
      simpa only [Bool.and_eq_true,Nat.ble_eq] using h
    simp only [triangle,hg,check,if_pos h,Bool.and_eq_true,decide_eq_true_eq,endpoint_iff]
    tauto
  · have hg : (Nat.ble clo chi && Nat.ble (max plo clo) phi)=false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      apply h
      simpa only [Bool.and_eq_true,Nat.ble_eq] using hb
    simp only [triangle,hg,check,if_neg h]

theorem triangle_eq (cc cs clo chi charge slope pc ps plo phi : ℕ) :
    triangle cc cs clo chi charge slope pc ps plo phi=check cc cs clo chi charge slope pc ps plo phi := by
  have h := triangle_iff cc cs clo chi charge slope pc ps plo phi
  cases h1 : triangle cc cs clo chi charge slope pc ps plo phi <;>
    cases h2 : check cc cs clo chi charge slope pc ps plo phi <;> simp_all

end ProximityPrize.SubmissionLower.TriangularKernel6815
