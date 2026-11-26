import ProximityPrize.SubmissionBinaryLower.B6401FactorBound
import ProximityPrize.SubmissionBinaryLower.B6402MixedDegree

namespace ProximityPrize.SubmissionBinaryLower.B6402ScalarLift
open Polynomial B6401ContactKerD B6401QuotInterp B6401FactorBound
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
set_option autoImplicit false
set_option maxHeartbeats 1600000
local notation "K" => BinaryIRSProfile.Field

noncomputable def lift : ContactPoly K →+* ContactPoly (Polynomial K) :=
  mapRingHom (mapRingHom (mapRingHom C))
noncomputable def spec (z : K) : ContactPoly (Polynomial K) →+* ContactPoly K :=
  mapRingHom (mapRingHom (mapRingHom (evalRingHom z)))

theorem left (f : ContactPoly K) (z : K) : spec z (lift f)=f := by
  apply Polynomial.ext; intro k
  apply Polynomial.ext; intro j
  apply Polynomial.ext; intro i
  simp [spec,lift,coeff_map]

theorem constant_height (f : ContactPoly K) : wYZ 0 (lift f)=0 := by
  apply Nat.eq_zero_of_le_zero; rw [wYZ_le_iff]; intro k j i _
  simp [lift,coeff_map]

theorem seed_constant (f : ContactPoly (Polynomial K)) (h : wYZ 0 f≤0) : lift (spec 0 f)=f := by
  apply Polynomial.ext; intro k
  apply Polynomial.ext; intro j
  apply Polynomial.ext; intro i
  simp only [lift,spec,coe_mapRingHom,coeff_map,coe_evalRingHom]
  let p := ((f.coeff k).coeff j).coeff i
  have hp : p.natDegree≤0 := natDegree_Z_le_of_wYZ h k j i
  change C (p.eval 0)=p
  rw [←coeff_zero_eq_eval_zero]
  exact (eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hp)).symm

theorem irreducible (f : ContactPoly K) (hi : Irreducible f) : Irreducible (cLiftZ f) := by
  change Irreducible (lift f)
  have hn : lift f≠0 := fun hz => hi.ne_zero (by rw [←left f 0,hz,map_zero])
  constructor
  · intro hu; exact hi.not_isUnit (left f 0 ▸ hu.map (spec 0))
  · intro a b he
    have hne := he ▸ hn
    have ha := left_ne_zero_of_mul hne
    have hb := right_ne_zero_of_mul hne
    have total := wYZ_mul 0 ha hb
    rw [←he,constant_height] at total
    have aa := seed_constant a (by omega)
    have bb := seed_constant b (by omega)
    have hh : f=spec 0 a*spec 0 b := by rw [←map_mul,←he,left]
    rcases hi.isUnit_or_isUnit hh with ua|ub
    · exact Or.inl (aa ▸ ua.map lift)
    · exact Or.inr (bb ▸ ub.map lift)

#print axioms irreducible
end ProximityPrize.SubmissionBinaryLower.B6402ScalarLift
