import ProximityPrize.SubmissionBinaryLower.B6402ExceptionalInterpolation

/-! Every seed label satisfying the factor equation receives the missed-site
roots from the exceptional local system, with its own witness polynomial. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402MissWitness
open Polynomial B6401ContactKerD B6401QuotInterp B6402PrimarySystem
open B6402ExceptionalSystem B6402ExceptionalFibres
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K] [CharP K 2]

noncomputable def evAt (x : K) (y : K[X]) (z : K) (P : K[X]) :
    LocalPoly (Polynomial K) →+* K[X] :=
  (evalLocal x (y.eval z) P).comp
    (mapRingHom (mapRingHom (mapRingHom (evalRingHom z))))

theorem ev_localized {w W s : ℕ} (x : K) (y : K[X]) (z : K) (P : K[X]) (fc : KerDIdx w W s → K[X]) :
    evAt x y z P (localized x y fc)=
      evalContact (evalZContact (∑ e,cC (fc e)*kerDBasisPoly e.1) z) P := by
  have hZ : ∀ f g : ContactPoly (Polynomial K), evalZContact (f*g) z=evalZContact f z*evalZContact g z := by
    intro f g; unfold evalZContact; rw [Polynomial.map_mul]
  rw [show evalZContact (∑ e : KerDIdx w W s,cC (fc e)*kerDBasisPoly e.1) z =
       ∑ e : KerDIdx w W s,evalZContact (cC (fc e)*kerDBasisPoly e.1) z by
       unfold evalZContact; rw [Polynomial.map_sum],evalContact_sum]
  unfold localized
  rw [map_sum]; apply Finset.sum_congr rfl; intro e _
  change evalLocal x (y.eval z) P (evalZLocal _ z)=_
  rw [evalZLocal_mul,evalZLocal_locC,evalZLocal_kerDLocalPoly,map_mul,evalLocal_locC,evalLocal_kerDLocalPoly,
    hZ,evalZContact_cC,evalZContact_kerDBasisPoly,evalContact_mul,evalContact_cC]

theorem exceptional_miss {w WF W s d : ℕ} (x : K) (y : K[X]) (z : K) (P : K[X])
    (fc : KerDIdx w WF d → K[X]) (gc : KerDIdx w W s → K[X]) (h b : ℕ) (L : Fibre K)
    (hF : (localized x y fc).coeff 0=(Polynomial.X : Fibre K)^h * L)
    (rows : remainderConditions (localized x y fc) ((Polynomial.X : Fibre K)^h) L b (localized x y gc))
    (onF : evalContact (evalZContact (∑ e,cC (fc e)*kerDBasisPoly e.1) z) P=0)
    (miss : P.eval x ≠ y.eval z) :
    ((Polynomial.X : K[X])-C x)^(2*b) ∣ evalContact (evalZContact (∑ e,cC (gc e)*kerDBasisPoly e.1) z) P := by
  let ev := evAt x y z P
  have hw : ev locW=P-C (y.eval z)-(Polynomial.X-C x)*P.derivative := by
    change evalLocal x (y.eval z) P (evalZLocal locW z)=_
    rw [evalZLocal_locW,evalLocal_locW]
  have he : ev (Polynomial.X : (Fibre K)[X])=(Polynomial.X-C x)^2 := by
    change evalLocal x (y.eval z) P (evalZLocal locT z)=_
    rw [evalZLocal_locT,evalLocal_locT]
  have hunit : IsCoprime ((Polynomial.X : K[X])-C x) (ev locW) := by
    apply (irreducible_X_sub_C x).coprime_iff_not_dvd.mpr
    intro hd
    have hz := dvd_iff_isRoot.mp hd
    change (ev locW).eval x=0 at hz
    rw [hw] at hz
    exact miss (by simpa [sub_eq_zero] using hz)
  have hpow : ev (C ((Polynomial.X : Fibre K)^h))=(ev locW)^h := by
    calc _ = ev ((C (Polynomial.X : Fibre K))^h) := congrArg ev (map_pow _ _ _)
         _ = _ := map_pow ev _ _
  rw [←ev_localized x y z P gc]
  exact miss_dvd ev _ _ _ ((Polynomial.X : Fibre K)^h) L hF b rows
    ((ev_localized x y z P fc).trans onF) he (hpow ▸ hunit.pow_right)

#print axioms exceptional_miss
end ProximityPrize.SubmissionBinaryLower.B6402MissWitness
