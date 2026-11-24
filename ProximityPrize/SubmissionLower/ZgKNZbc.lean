import ProximityPrize.SubmissionLower.ZkEPT8b
set_option Elab.async false
namespace qGWTmVd
noncomputable section
open Polynomial Finset qQ9yWTb qb0hmCe q1kuFjb


open scoped Classical
variable {E :Type} [Field E]
private def expand:E[X][X] ≃+* MvPolynomial (Option Unit) E :=
 (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv E Unit).toRingEquiv.symm).trans
   (MvPolynomial.optionEquivLeft E Unit).toRingEquiv.symm
private theorem coeff_expand (g:E[X][X]) (d:Option Unit →₀ ℕ) :
   (expand g).coeff d=(g.coeff (d none)).coeff (d.some ()) := by
 have h:MvPolynomial.optionEquivLeft E Unit (expand g) =
     g.map (MvPolynomial.uniqueAlgEquiv E Unit).symm.toRingHom :=
   (MvPolynomial.optionEquivLeft E Unit).apply_symm_apply _
 rw [← MvPolynomial.optionEquivLeft_coeff_some_coeff_none E Unit,h,coeff_map]
 exact MvPolynomial.coeff_uniqueAlgEquiv_symm E _ _
private def weights (s :ℕ) :Option Unit→ℕ:= fun o=>o.elim s fun _=>1
private theorem c0Q (s :ℕ) (d:Option Unit →₀ ℕ) :
  Finsupp.weight (weights s) d=d.some ()+d none*s := by
 rw [Finsupp.weight_eq_sum,Fintype.sum_option]
 simp [weights,smul_eq_mul,Finsupp.some_apply,Nat.add_comm]
private def wdeg (s :ℕ) (g:E[X][X]) :ℕ:=(expand g).weightedTotalDegree (weights s)
private theorem le_wdeg {s :ℕ} {g:E[X][X]} {i j:ℕ}
  (h: (g.coeff i).coeff j≠0) :j+i*s≤wdeg s g:= by
 let d:=(Finsupp.single () j).optionElim i
 have hi:d none=i:=Finsupp.optionElim_apply_none ..
 have hj:d.some ()=j:= by
  change ((Finsupp.single () j).optionElim i).some ()=j
  rw [Finsupp.some_optionElim,Finsupp.single_eq_same]
 have hn: (expand g).coeff d≠0:= by rwa [coeff_expand,hi,hj]
 simpa only [wdeg,c0Q,hi,hj] using
  MvPolynomial.le_weightedTotalDegree (weights s) (MvPolynomial.mem_support_iff.mpr hn)
private theorem raw_factor {q:Curve} (B:CurveModel q) (F:Raw)
   (hF:restrict B F≠0) (g:B.E[X][X]) (hg:Irreducible g) (hd:g∣restrict B F) :
   ∃ R:Raw,Irreducible R∧R∣F∧g∣restrict B R:= by
 revert hF hd
 induction F using WfDvdMonoid.induction_on_irreducible with
 | zero=>simp only [map_zero,ne_eq,not_true_eq_false,false_implies]
 | unit F hF =>
   intro _ hd
   exact (hg.not_isUnit (isUnit_of_dvd_unit hd (hF.map (restrict B)))).elim
 | mul A R _ hr ih =>
   intro hn hd
   rw [map_mul] at hn hd
   rcases hg.prime.dvd_mul.mp hd with h | h
   · exact ⟨R,hr,dvd_mul_right _ _,h⟩
   · obtain ⟨F,hf,hd,h⟩:=ih (right_ne_zero_of_mul hn) h
     exact ⟨F,hf,hd.trans (dvd_mul_left _ _),h⟩
end
end qGWTmVd
