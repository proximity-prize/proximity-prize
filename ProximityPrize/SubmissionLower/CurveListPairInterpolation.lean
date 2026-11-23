import ProximityPrize.SubmissionLower.CurveListCornerSource

set_option Elab.async false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace CurveListPairInterpolation
open CJ0 CJ0_3 MvPolynomial PolynomialDifferential CurveListJointWeight ReedSolomon.HiddenDerivative
open scoped Polynomial

noncomputable section

private abbrev jetView:=MvPolynomial.optionEquivRight K (Fin 3)

private theorem jet_degree (P : DifferentialPolynomial K 2) :
    (jetView P).totalDegree=jetTotalDegree P:=by
  rw [MvPolynomial.totalDegree_optionEquivRight]
  unfold jetTotalDegree
  congr 1
  funext v
  cases v <;> simp [jetDegreeWeight]

private theorem jet_mul {P Q : DifferentialPolynomial K 2} (hp : P ≠ 0) (hq : Q ≠ 0) :
    jetTotalDegree (P*Q)=jetTotalDegree P+jetTotalDegree Q:=by
  simp only [← jet_degree,map_mul]
  exact totalDegree_mul_of_isDomain (fun h => hp (jetView.injective (h.trans jetView.map_zero.symm)))
    (fun h => hq (jetView.injective (h.trans jetView.map_zero.symm)))

private theorem column_jet_injective {A : ℕ} {s : Source} {i k : ColumnIndex A s}
    (h:(column A s i).exponent.some=(column A s k).exponent.some):i.1=k.1:=by
  apply Subtype.ext
  rcases i with ⟨⟨⟨c,b,a⟩,hi⟩,i⟩
  rcases k with ⟨⟨⟨d,e,f⟩,hk⟩,k⟩
  have h₀:=congrArg (fun x:Fin 3 →₀ ℕ => x 0) h
  have h₁:=congrArg (fun x:Fin 3 →₀ ℕ => x 1) h
  have h₂:=congrArg (fun x:Fin 3 →₀ ℕ => x 2) h
  simp only [Finsupp.some_apply] at h₀ h₁ h₂
  have h₀' : a=f:=by simpa [column,Jet.a] using h₀
  change (column A s _).exponent (some ((0 : Fin 2).succ)) =
    (column A s _).exponent (some ((0:Fin 2).succ)) at h₁
  rw [SourceColumn.exponent_succ,SourceColumn.exponent_succ] at h₁
  have h₁' : b=e:=h₁
  change (column A s _).exponent (some ((1 : Fin 2).succ)) =
    (column A s _).exponent (some ((1:Fin 2).succ)) at h₂
  rw [SourceColumn.exponent_succ,SourceColumn.exponent_succ] at h₂
  have h₂' : c=d:=h₂
  subst d; subst e; subst f
  rfl

end
end CurveListPairInterpolation
