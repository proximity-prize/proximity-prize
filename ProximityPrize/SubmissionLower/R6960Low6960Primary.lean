import ProximityPrize.SubmissionLower.Final50Order
import ProximityPrize.SubmissionLower.ModelExactPole

noncomputable section
set_option Elab.async false
namespace Lower6960.Low
open P3 (I K node)
open K1_13 (Row Geom Shape shape InBox Contact)
open Wide50EulerPrimary (primary_family sourceRank layerNeed)
open scoped Polynomial

abbrev agreement : ℕ := 179827
abbrev physicalDegree : ℕ := 133409
abbrev primaryCutoff : ℕ := 3000*agreement-1
abbrev primaryRank : ℕ := sourceRank agreement physicalDegree
abbrev need : ℕ := layerNeed agreement physicalDegree

theorem certified_layers : need = 21406065569736 := by decide +kernel

/-- The common endpoint supplies all physical degree and agreement data
for every actual low-height mark. -/
theorem messages_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179827 M Γ) (hi : M.overhead ≤ 2338) :
    Set.InjOn F.scalar (Γ : Set K) ∧
      (∀ γ∈Γ,(F.scalar γ).natDegree≤physicalDegree) ∧
      ∀ γ∈Γ,∃ T : Finset I,agreement≤T.card ∧ ∀ i∈T,(F.scalar γ).eval (node i)=M.word i := by
  refine ⟨F.distinct,?_,?_⟩
  · intro γ hγ
    rcases (F.mark γ hγ).scalar_degree with zero | deg
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at deg
      change (F.scalar γ).natDegree≤133409
      omega
  · intro γ hγ
    let Mγ := F.mark γ hγ
    exact ⟨Mγ.bad.support,Mγ.bad.agreement,Mγ.scalar_hits⟩

/-- The native generic primary producer instantiated at the concrete 69.60
low endpoint. -/
theorem primary_at_endpoint (word : I→K) :
    ∃ e : Fin primaryRank→Row 4,LinearIndependent Geom e ∧
      ∀ i,InBox (shape (e i)) PrimaryTaper.primaryBox ∧
        PrimaryTaper.TrueWeightLE physicalDegree (e i) primaryCutoff ∧
        PrimaryTaper.JetsBounded (e i) ∧ Contact word (e i) :=
  primary_family agreement physicalDegree (by decide) (by decide) (by decide +kernel) word le_rfl

#print axioms certified_layers
#print axioms primary_at_endpoint
end Lower6960.Low
