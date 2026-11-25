import ProximityPrize.SubmissionLower.R6966ProofNativeMarkedTariff
import ProximityPrize.SubmissionLower.R6966ProofFarFactorPrice

set_option Elab.async false

namespace Research6966.NearMarkedCount
open Polynomial Finset
open K1 (K p)
open K1_14 (Equation FX Seeds atX liftPoly graphEval)
open K1_14_2 (SeedField)
open Lower6960.MarkedEvaluation (rate)
open KoalaRect (axisDegree)
noncomputable section
set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false

theorem count {u deleted maxHeight} {M:P1.ModelAt maxHeight u deleted} {Γ T:Finset K}
    (F:P1.FamilyAt 179769 M Γ) (sub:T⊆Γ) (hi:M.overhead.toNat≤2499)
    {f:Equation} (pos:0<f.natDegree) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (n d x y:ℕ) (big:3≤n) (legal:n<48) (deg:f.natDegree≤n)
    (total:∀ i,(f.coeff i).totalDegree≤d)
    (xcap:axisDegree f 0≤x) (ycap:axisDegree f 1≤y)
    (small:(2*f.natDegree-1)*axisDegree f 0<p)
    (root:∀γ∈T,(f.map (graphEval (M.label γ))).eval (atX (F.scalar γ))=0) :
    T.card≤(rate n+2*f.natDegree-1)*NativeMarkedTariff.width d x y+
      (n-1)*f.natDegree := by
  classical
  have label_inj : Function.Injective M.label := fun _ _ h=>sub_left_inj.mp h
  obtain ⟨S,P,Ssub,pn,pe,wide,marks,split⟩:=NativeMarkedTariff.split M.label F.scalar
    label_inj.injOn pos sep (NativeMarkedTariff.coeff_cap total xcap ycap) small root
  have inside:S⊆Γ:=Ssub.trans sub
  have words : RetainedShortening.Word 179769 164748 M.word F.scalar S := by
    refine ⟨F.distinct.mono inside,?_,?_⟩
    · intro γ hγ
      rcases (F.mark γ (inside hγ)).scalar_degree with z|b
      · simp [z]
      · change ((F.scalar γ).natDegree:ℤ)≤131071+M.overhead at b
        omega
    · intro γ hγ
      let B:=F.mark γ (inside hγ)
      exact ⟨B.bad.support,B.bad.agreement,B.scalar_hits⟩
  have marked:=FarFactorPrice.price words (fun γ => algebraMap K K1_14.L (M.label γ))
    ((algebraMap K K1_14.L).injective.comp label_inj) P pn n _ big legal (pe.le.trans deg) wide marks
  rw [pe] at marked
  apply split.trans
  calc
    _ ≤ (2*f.natDegree-1)*NativeMarkedTariff.width d x y+
        (rate n*NativeMarkedTariff.width d x y+(n-1)*f.natDegree) := Nat.add_le_add_left marked _
    _ = _ := by
      rw [show rate n+2*f.natDegree-1=rate n+(2*f.natDegree-1) by omega,Nat.add_mul]
      omega

#print axioms count
end
end Research6966.NearMarkedCount
