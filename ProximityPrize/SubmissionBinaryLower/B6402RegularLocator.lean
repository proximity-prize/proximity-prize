import ProximityPrize.SubmissionBinaryLower.B6402MissedFibres
import ProximityPrize.SubmissionBinaryLower.B6402RegularSystem
import ProximityPrize.SubmissionBinaryLower.B6401FactorBound
import ProximityPrize.SubmissionBinaryLower.P64C7Auxiliary

/-! Lift the checked even slices to the whole regular-fibre locator over K[Z],
before any seed specialization. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402RegularLocator
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6401FactorBound
open B6402MissedFibres B6402SeedCoordinates B6402QuotientSpace B6402PrimarySystem
open B6402RegularSystem P64LineOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {K : Type*} [Field K] [CharP K 2]

private theorem shift_dvd_iff (x : K) (y : K[X]) (n : ℕ) (p : BiPoly (Polynomial K)) :
    C (Polynomial.X : (Polynomial K)[X])^n ∣ lineShiftHom x y p ↔
    C ((Polynomial.X : (Polynomial K)[X])-C (C x))^n ∣ p := by
  let inv := P64C6Coordinates.shiftHom (-(C x)) (-y)
  have unshift (f : BiPoly (Polynomial K)) : inv (lineShiftHom x y f)=f := by
    change P64C6Coordinates.shiftHom _ _ (P64C6Coordinates.shiftHom (C x) y f)=f
    simpa using P64C6Weights.shiftHom_inverse (-(C x)) (-y) f
  have xi : inv (C (Polynomial.X : (Polynomial K)[X])) = C (Polynomial.X-C (C x)) := by
    simp [inv,P64C6Coordinates.shiftHom,Polynomial.taylor_apply,sub_eq_add_neg]
  have xj : lineShiftHom x y (C ((Polynomial.X : (Polynomial K)[X])-C (C x)))=C Polynomial.X := by
    rw [map_sub,map_sub,lineShiftHom_CX,lineShiftHom_CC,←map_sub,add_sub_cancel_right]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨inv a,?_⟩
    have h := congrArg inv ha
    simpa only [unshift,map_mul,map_pow,xi] using h
  · rintro ⟨a,ha⟩
    rw [ha,map_mul,map_pow,xj]
    exact dvd_mul_right _ _

theorem regular_locator (F G : ContactPoly (Polynomial K)) (x : K) (y : K[X]) (m b s J : ℕ)
    (hF : F.natDegree≤1) (hG : G.natDegree≤s) (dF : contactDeriv F=0) (dG : contactDeriv G=0)
    (hreg : ¬C ((Polynomial.X : (Polynomial K)[X])-C (C x)) ∣ F.coeff 1)
    (hdeg : (resultant F G 1 s).natDegree≤J+4*s)
    (hord : OrdGE (resultant F G 1 s) x y (2*m+3*s))
    (htest : ∀ i<b, ∀ j, 2*m+3*s≤2*i+j → j≤J+4*s →
        (((lineShiftHom x y (resultant F G 1 s)).coeff j).coeff (2*i))=0) :
    C ((Polynomial.X : (Polynomial K)[X])-C (C x))^(2*b) ∣ resultant F G 1 s := by
  let r := resultant F G 1 s
  let p := lineShiftHom x y r
  have hcap : p.natDegree≤J+4*s := (P64C7Auxiliary.lineShift_degree_le r x y).trans hdeg
  have step (i : ℕ) (hi : i<b) (ih : C (Polynomial.X : (Polynomial K)[X])^(2*i) ∣ p) :
      C (Polynomial.X : (Polynomial K)[X])^(2*(i+1)) ∣ p := by
    have middle : C (Polynomial.X : (Polynomial K)[X])^(2*i+1) ∣ p := by
      rw [←map_pow,C_dvd_iff_dvd_coeff] at ih ⊢
      intro j
      rw [X_pow_dvd_iff]
      intro n hn
      rcases lt_or_eq_of_le (show n≤2*i by omega) with lt|rfl
      · exact X_pow_dvd_iff.mp (ih j) n lt
      by_cases high : J+4*s<j
      · simp only [coeff_eq_zero_of_natDegree_lt (hcap.trans_lt high),coeff_zero]
      by_cases low : 2*i+j<2*m+3*s
      · exact hord (2*i) j low
      · exact htest i hi j (by omega) (by omega)
    have un := (shift_dvd_iff x y _ r).mp middle
    have hnext := regular_fibre_next F G (C x) s i hF hG dF dG hreg un
    apply (shift_dvd_iff x y _ r).mpr
    simpa only [Nat.mul_add,Nat.mul_one] using hnext
  apply (shift_dvd_iff x y _ r).mp
  have all (j : ℕ) (hj : j≤b) : C (Polynomial.X : (Polynomial K)[X])^(2*j) ∣ p := by
    induction j with
    | zero => simp
    | succ j ih => exact step j (by omega) (ih (by omega))
  exact all b le_rfl

theorem ordinate_cap {w W s J : ℕ} (hw : 1<w) (hJ : W/(w-1)≤J)
    (F G : ContactPoly (Polynomial K)) (gW : wdeg w G≤W)
    (h0 : (F.coeff 0).natDegree≤5) (h1 : (F.coeff 1).natDegree≤4) :
    (resultant F G 1 s).natDegree≤J+4*s := by
  apply resultant_ordinate_degree F G s J h0 h1
  intro j _ hn
  apply le_trans _ hJ
  apply (Nat.le_div_iff_mul_le (by omega : 0<w-1)).mpr
  have e := wdegBiDom_coeff_le_of_wdeg gW j hn
  have a := wdegBiDom_ge_natDegree_mul w (G.coeff j) hn
  have t := Nat.mul_le_mul_left (G.coeff j).natDegree (Nat.sub_le w 1)
  rw [Nat.add_mul]; omega

#print axioms regular_locator
#print axioms ordinate_cap
end ProximityPrize.SubmissionBinaryLower.B6402RegularLocator
