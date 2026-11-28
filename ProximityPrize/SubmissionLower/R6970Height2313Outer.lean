import ProximityPrize.SubmissionLower.R6970Height2312Wide7
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0677
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969NearOuter
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

/-- Split using the actual outer prefix, and derive the native physical
baseline of every nontrivial exception at the near endpoint. -/
theorem split {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2305 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ R : Research6970.Height2313.Lower6960.Prefix6969Wide.Rows F Crt, R.out.exception = 1 ∨
      ∃ phys : HelperPhysicalModel.Model Crt R.out.exception,
        PrefixRows.Common (evaluated Crt (word M) Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank.shape
          (Research6970.Height2313.Lower6960.Prefix6969Helper.helperCutoff M.overhead.toNat)) R.out.exception ∧
        R.out.exception.natDegree = 1 ∧
        1 ≤ jetDegree R.out.exception ∧ jetDegree R.out.exception ≤ 7 ∧
        1 ≤ seedDegree R.out.exception ∧ seedDegree R.out.exception ≤ 56 ∧
        (2 ≤ jetDegree R.out.exception → seedDegree R.out.exception ≤ 56) ∧
        jetDegree R.out.exception * 128758 - 1 ≤ RawPhysicalDegree.weight
          (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw := by
  obtain ⟨R⟩ := Research6970.Height2313.Lower6960.Prefix6969Wide.rows F Crt lo (hi.trans (by decide)) noPole residues
  refine ⟨R, ?_⟩
  rcases R.out.kind with unit | common
  · exact Or.inl unit
  have hiAll : M.overhead.toNat ≤ 33755 := hi.trans (by decide)
  obtain ⟨line, jd, jmax, sd, smax, nonlinear⟩ :=
    Research6970.Height2313.Lower6960.Prefix6969Helper.helper_common_caps Crt (word M) lo hiAll
      common.1 common.2.2.1 common.2.1 common.2.2.2
  obtain ⟨phys⟩ := HelperPhysicalModel.exists_model Crt common.1 common.2.1
  have hraw : 0 < 131071-M.overhead.toNat := by omega
  have lower := HelperWeightCap.weight_lower phys common.1.ne_zero _ hraw
  have endpoint : 128758 ≤ 131071-M.overhead.toNat := by omega
  have m := Nat.mul_le_mul_left (jetDegree R.out.exception) endpoint
  rw [Nat.mul_comm (jetDegree R.out.exception) (131071-M.overhead.toNat)] at m
  rw [line] at lower
  exact Or.inr ⟨phys, common, line, jd, jmax, sd, smax, nonlinear, by omega⟩

end
end Lower6960.Prefix6969NearOuter
end Z6969Source0677


end Research6970.Height2313
