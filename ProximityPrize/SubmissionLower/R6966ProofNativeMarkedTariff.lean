import ProximityPrize.SubmissionLower.R6966ProofNativeSeedDegree
import ProximityPrize.SubmissionLower.R6960MarkedEvaluationLedger

set_option Elab.async false

namespace Research6966.NativeMarkedTariff
open Finset Polynomial
open K1 (K p)
open K1_14 (FX L Seeds Equation liftPoly atX graphEval seedEmbedding)
open K1_14_2 (SeedField)
open KoalaRect (axisDegree axisDegree_le_iff)
open Lower6960.TerminalMarked (determinant det_axis)
open Lower6960.RetainedCompression (project incl specialize MarkedFiber integral_project_with_width)
open CurvatureSquares (Ordinate zView)
noncomputable section
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

def width (total u v:ℕ) := min (p*total) (u+p*v)
private abbrev graph : Seeds→+*FX[X] := (K1_14.frobeniusGraph (F:=FX) p).toRingHom

private theorem frob_total (Q:Seeds) : (graph Q).natDegree≤p*Q.totalDegree := by
  apply (MvPolynomial.natDegree_aeval_le_weightedTotalDegree ![Polynomial.X,Polynomial.X^p] Q).trans
  apply Finset.sup_le
  intro m hm
  have bound:=MvPolynomial.le_totalDegree hm
  rw [Finsupp.sum_fintype _ _ (fun _=>rfl)] at bound
  simp only [Fin.sum_univ_two] at bound
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  change m 0+m 1*2130706433 ≤ 2130706433*Q.totalDegree
  omega

theorem coeff_cap {f:Equation} {total u v:ℕ} (t:∀i,(f.coeff i).totalDegree≤total)
    (h0:axisDegree f 0≤u) (h1:axisDegree f 1≤v) (i:ℕ) :
    ((project f).coeff i).natDegree≤width total u v := by
  change ((f.map graph).coeff i).natDegree≤_
  rw [coeff_map]
  exact le_min ((frob_total _).trans (Nat.mul_le_mul_left _ (t i)))
    (K1_14.frobeniusGraph_degree p u v _ ((axisDegree_le_iff ..).mp h0 i) ((axisDegree_le_iff ..).mp h1 i))

private theorem determinant_degree {f:Equation} (pos:0<f.natDegree) {w:ℕ}
    (cap:∀i,((project f).coeff i).natDegree≤w) :
    (graph (determinant f)).natDegree≤(2*f.natDegree-1)*w := by
  unfold determinant
  rw [←resultant_map_map]
  have hd j : ((f.derivative.map graph).coeff j).natDegree≤w := by
    rw [coeff_map,coeff_derivative,map_mul]
    have c:=cap (j+1)
    change ((f.map graph).coeff (j+1)).natDegree≤w at c
    rw [coeff_map] at c
    calc
      _ ≤ (graph (f.coeff (j+1))).natDegree+(graph ((j:Seeds)+1)).natDegree := natDegree_mul_le
      _ ≤ w+0 := Nat.add_le_add c (by simp)
      _ = _ := Nat.add_zero _
  have bh : ∀ j,((f.map graph).coeff j).natDegree≤w := cap
  apply (Polynomial.natDegree_resultant_le_of_coeff_natDegree_le _ _ _ _ w w bh hd).trans
  rw [←Nat.add_mul]
  exact Nat.mul_le_mul_right _ (by omega)

private theorem graph_eval (Q:Seeds) (z:K) : (graph Q).eval (seedEmbedding z)=graphEval z Q := by
  have eh : (evalRingHom (seedEmbedding z)).comp graph=graphEval z := by
    apply MvPolynomial.ringHom_ext
    · intro c;simp [graph,K1_14.frobeniusGraph,graphEval]
    · intro i;fin_cases i <;> simp [graph,K1_14.frobeniusGraph,graphEval]
  exact DFunLike.congr_fun eh Q

/-- The same physical parameter width pays for the determinant and the
good-label factor tariff. It can be certified either by the seeded
ordinate section or by the two separate rectangular witness bounds. -/
theorem split {T:Finset K} (label:K→K) (s:K→K[X]) (inj:Set.InjOn label (T:Set K))
    {f:Equation} (pos:0<f.natDegree) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    {w:ℕ} (cap:∀i,((project f).coeff i).natDegree≤w)
    (small:(2*f.natDegree-1)*axisDegree f 0<p)
    (roots:∀γ∈T,(f.map (graphEval (label γ))).eval (atX (s γ))=0) :
    ∃ (S:Finset K) (P:Ordinate), S⊆T ∧ P≠0 ∧ P.natDegree=f.natDegree ∧
      (zView P).natDegree≤w ∧
      (∀γ∈S,MarkedFiber P (algebraMap K L (label γ)) (liftPoly (s γ))) ∧
      T.card≤(2*f.natDegree-1)*w+S.card := by
  classical
  let B:=T.filter (fun γ=>graphEval (label γ) (determinant f)=0)
  let S:=T\B
  have nz:determinant f≠0:=resultant_derivative_ne_zero_of_separable_map_fractionField f sep
  have ne:graph (determinant f)≠0:=K1_14.frobeniusGraph_ne_zero p (by decide) _ nz
    ((det_axis f 0).trans_lt small)
  have eq:(B.image (fun γ=>seedEmbedding (label γ))).card=B.card :=
    card_image_of_injOn (fun x hx y hy h=>inj (mem_filter.mp hx).1 (mem_filter.mp hy).1 (seedEmbedding.injective h))
  have bad:B.card≤(2*f.natDegree-1)*w:=by
    rw [←eq]
    apply le_trans _ (determinant_degree pos cap)
    apply Polynomial.card_le_degree_of_subset_roots
    rintro _ hz
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz
    exact (mem_roots ne).mpr ((graph_eval _ _).trans (mem_filter.mp hγ).2)
  have axisSmall:axisDegree f 0<p:=
    (Nat.le_mul_of_pos_left _ (by omega : 0<2*f.natDegree-1)).trans_lt small
  have fn:f≠0:=by intro eq;simp [eq] at pos
  obtain ⟨d,P,dn,pn,de,wd,called⟩:=integral_project_with_width f fn axisSmall w cap
  refine ⟨S,P,sdiff_subset,pn,de,wd,?_,?_⟩
  · intro γ hγ
    have hT:γ∈T:=(mem_sdiff.mp hγ).1
    have safe:graphEval (label γ) (determinant f)≠0 := fun zero=>(mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨hT,zero⟩)
    have full:=natDegree_map_eq_of_resultant_derivative_padded_ne_zero _ _ le_rfl safe
    have sg:=separable_map_of_resultant_derivative_padded_ne_zero _ _ le_rfl (by omega) safe
    have nz':incl d≠0:=(map_ne_zero_iff incl (IsFractionRing.injective (Polynomial L) FX)).mpr dn
    have eq:=called (label γ)
    refine ⟨?_,?_,?_⟩
    · rw [←natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial L) FX),eq,natDegree_C_mul nz',full,de]
    · rw [eq];exact sg.unit_mul (isUnit_C.mpr nz'.isUnit)
    · apply (IsFractionRing.injective (Polynomial L) FX)
      rw [← Polynomial.eval_map_apply,eq,map_zero,eval_mul,eval_C]
      exact mul_eq_zero.mpr (Or.inr (roots γ hT))
  · have partition:=card_sdiff_add_card_eq_card (show B⊆T from filter_subset ..)
    change T.card≤_+(T\B).card
    omega

end
end Research6966.NativeMarkedTariff
