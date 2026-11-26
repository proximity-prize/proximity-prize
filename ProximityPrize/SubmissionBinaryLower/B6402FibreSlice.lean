import ProximityPrize.SubmissionBinaryLower.B6402ExceptionalQuartic
import ProximityPrize.SubmissionBinaryLower.B6402RegularLocator

/-! The zero spatial slice in invariant coordinates agrees with ordinary
evaluation X=x and translation Y=y+w. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402FibreSlice
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6402PrimarySystem
open B6402ExceptionalSystem B6402ExceptionalSupport P64LineOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {K : Type*} [Field K] [CharP K 2]
noncomputable local instance : CommRing (Polynomial K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial K)) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Fibre K) := AddMonoidAlgebra.commRing

local notation "A" => Polynomial K

noncomputable def ordinateHom (x : K) (y : A) : BiPoly A →+* Polynomial A :=
  (compRingHom (Polynomial.X+C y)).comp (mapRingHom (evalRingHom (C x)))

noncomputable def fibreHom (x : K) (y : A) : ContactPoly A →+* Fibre K :=
  eval₂RingHom ((mapRingHom (C : A →+* Polynomial A)).comp (ordinateHom x y)) (C Polynomial.X)

private theorem onC (x : K) (y u : A) : fibreHom x y (cC u)=C (C u) := by
  simp [fibreHom,ordinateHom,cC]
private theorem onX (x : K) (y : A) : fibreHom x y cX=C (C (C x)) := by
  simp [fibreHom,ordinateHom,cX]
private theorem onY (x : K) (y : A) : fibreHom x y cY=Polynomial.X+C (C y) := by
  simp [fibreHom,ordinateHom,cY]
private theorem onR (x : K) (y : A) : fibreHom x y cR=C Polynomial.X := by
  simp [fibreHom,cR]

theorem basis_slice (x : K) (y : A) (e : ℕ×ℕ×ℕ×ℕ) :
    (kerDLocalPoly (C x) y e).coeff 0 = fibreHom x y (kerDBasisPoly e) := by
  rw [coeff_zero_eq_eval_zero]
  unfold kerDLocalPoly kerDBasisPoly localU
  simp only [locC,locR,locW,locT,eval_mul,eval_add,eval_pow,eval_C,eval_X,zero_mul,add_zero,
    map_mul,map_add,map_pow,onX,onY,onR]
  have htwo : (2 : Fibre K)=0 := CharP.cast_eq_zero _ 2
  have hsq : (Polynomial.X+C (C y) : Fibre K)^2=Polynomial.X^2+C (C y)^2 := by
    rw [add_sq,htwo,zero_mul,zero_mul,add_zero]
  simp only [hsq,add_assoc,add_left_comm,add_comm,map_pow]

theorem localized_slice {w W s : ℕ} (x : K) (y : A) (fc : KerDIdx w W s → A) :
    (localized x y fc).coeff 0 = fibreHom x y (∑ e,cC (fc e)*kerDBasisPoly e.1) := by
  unfold localized
  rw [finsetSum_coeff,map_sum]
  apply Finset.sum_congr rfl; intro e _
  rw [map_mul,onC,show locC (fc e) = C (C (C (fc e))) from rfl,coeff_C_mul,basis_slice]

theorem linear_slice (x : K) (y : A) (F : ContactPoly A) (hs : F.natDegree≤1) :
    fibreHom x y F=(ordinateHom x y (F.coeff 0)).map C+
       (ordinateHom x y (F.coeff 1)).map C*C Polynomial.X := by
  unfold fibreHom
  rw [coe_eval₂RingHom,Polynomial.eval₂_eq_sum_range' _ (show F.natDegree<2 by omega)]
  simp [Finset.sum_range_succ]

theorem ordinate_coeff (x : K) (y : A) (f : BiPoly A) (j : ℕ) :
    (ordinateHom x y f).coeff j=((lineShiftHom x y f).coeff j).coeff 0 :=
  (lineShift_coeff_zero f x y j).symm

theorem nonzero_slice (x : K) (y : A) (F : ContactPoly A) (hirr : Irreducible F)
    (hs : F.natDegree=1) (bad : evalXAt (F.coeff 1) x=0) : ordinateHom x y (F.coeff 0)≠0 := by
  intro hf
  have hzero0 : evalXAt (F.coeff 0) x=0 := by
    change taylor y (evalXAt (F.coeff 0) x)=0 at hf
    exact (taylor_eq_zero _ _).mp hf
  have div : C (C ((Polynomial.X : Polynomial A)-C (C x))) ∣ F := by
    rw [C_dvd_iff_dvd_coeff]; intro j
    rw [C_dvd_iff_dvd_coeff]; intro k
    have hzero : evalXAt (F.coeff j) x=0 := by
      rcases j with _|(_|j)
      · exact hzero0
      · exact bad
      · simp [coeff_eq_zero_of_natDegree_lt (by omega : F.natDegree<j+2),evalXAt]
    apply dvd_iff_isRoot.mpr
    have hh := congrArg (fun p : Polynomial A => p.coeff k) hzero
    simpa [evalXAt,coeff_map,IsRoot.def] using hh
  obtain ⟨h,eq⟩ := div
  obtain hu|hu := hirr.isUnit_or_isUnit eq
  · exact not_isUnit_X_sub_C _ (isUnit_C.mp (isUnit_C.mp hu))
  · have hn : h≠0 := hu.ne_zero
    have hl : (C (C ((Polynomial.X : Polynomial A)-C (C x))) : ContactPoly A)≠0 :=
      C_ne_zero.mpr (C_ne_zero.mpr (X_sub_C_ne_zero _))
    have hh := congrArg Polynomial.natDegree eq
    rw [natDegree_mul hl hn,natDegree_C,natDegree_eq_zero_of_isUnit hu] at hh
    omega

#print axioms localized_slice
#print axioms nonzero_slice
end ProximityPrize.SubmissionBinaryLower.B6402FibreSlice
