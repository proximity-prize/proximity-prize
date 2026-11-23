import ProximityPrize.SubmissionLower.KoalaLow6954
import ProximityPrize.SubmissionLower.SmallAnchor6960
import ProximityPrize.SubmissionLower.Final50GeoCover

set_option Elab.async false

namespace KoalaAnchor2428Transport
noncomputable section
open K1_13 (Geom Row shape InBox)
open P3 (K)
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped Polynomial
open private coeff_flatten from ProximityPrize.SubmissionLower.Fast040

private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0*w 0+m 1*w 1+m 2*w 2+m 3*w 3 := by
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul,add_assoc]

private theorem weight_step (u : JetVariable 3 →₀ ℕ) :
    u.weight (differentialWeight 133500) =
        u.weight (differentialWeight 133499) + u.some.degree := by
  have hOld : differentialWeight (d := 3) 133499 =
      fun i => i.elim 1 (fun k => 133499 - k.val) := by
    funext i
    cases i <;> rfl
  have hNew : differentialWeight (d := 3) 133500 =
      fun i => i.elim 1 (fun k => 133500 - k.val) := by
    funext i
    cases i <;> rfl
  conv_lhs => rw [← Finsupp.optionElim_some u, hNew, Finsupp.weight_optionElim, one_mul]
  conv_rhs => enter [1]; rw [← Finsupp.optionElim_some u, hOld, Finsupp.weight_optionElim, one_mul]
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight, jet_weight]
  change u none + (u.some 0*133500 + u.some 1*133499 + u.some 2*133498 + u.some 3*133497) =
    (u none + (u.some 0*133499 + u.some 1*133498 + u.some 2*133497 + u.some 3*133496)) +
      (u.some 0*1 + u.some 1*1 + u.some 2*1 + u.some 3*1)
  omega

theorem weight_le (P : Row 4) (hbox : InBox (shape P) ⟨137,56,14⟩)
    (h : differentialWeightedDegree 133499
      ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) ≤ 102*179876 - 1+56) :
    Final50Price.TrueWeightLE P Final50Price.anchorCutoff := by
  classical
  apply (Final50GeoCover.trueWeight_iff P).mpr
  rw [← Final50GeoCover.differentialWeight_eq]
  change ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P).weightedTotalDegree
      (differentialWeight 133500) ≤ (102*179876 - 1+56)+137
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff] at h
  intro u hu
  have hcoeff : (P.coeff u.some).coeff (u none) ≠ 0 := by
    rw [← coeff_flatten,Finsupp.optionElim_some]
    exact MvPolynomial.mem_support_iff.mp hu
  have hm : u.some ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr (fun hz => hcoeff (by simp [hz]))
  have hb : P.totalDegree ≤ 137 := hbox.1
  have hd : u.some.degree ≤ 137 := (MvPolynomial.le_totalDegree hm).trans hb
  rw [weight_step]
  exact Nat.add_le_add (h u hu) hd

theorem anchor {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179876 M Γ)
    (hi : M.overhead ≤ 2428) : KoalaLow6954.Anchor Γ F.scalar := by
  obtain ⟨P,hP,hbox,hactive,hweight,hzero⟩ := SmallAnchor6960.exists_anchor M.word
  refine ⟨P,hP,hbox,hactive,weight_le P hbox hweight,?_⟩
  intro γ hγ
  let m := F.mark γ hγ
  have hd : (F.scalar γ).natDegree ≤ 133499 := by
    rcases m.scalar_degree with hzero | hdegree
    · simp [hzero]
    · change ((F.scalar γ).natDegree : ℤ) ≤ 131072-1+M.overhead at hdegree
      omega
  exact hzero _ m.bad.support hd m.bad.agreement m.scalar_hits

#print axioms weight_le
#print axioms anchor
end
end KoalaAnchor2428Transport
