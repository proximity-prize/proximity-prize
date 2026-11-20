import ProximityPrize.SubmissionLower.Koala6844VirtualShortSourceReceipts
import ProximityPrize.SubmissionLower.Koala6844VirtualShortCarrier


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetSpecialize SecondJetCoefficients SecondJetCoefficientSpecialization
open SecondJetClearedHelper SecondJetHelperWeights
open RCN095 RCN156 RCN234
open MovingFiberThreeSources6811 Koala6844Receipts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option Elab.async false
set_option maxRecDepth 30000

variable {K : Type} [Field K]

def badLeadingSeeds (P : Poly (K := K)) (selected : K → Polynomial K) (seeds : Finset K) : Finset K := by
  classical
  exact seeds.filter fun g => coefficientSpecialize (selected g) g (asS P).leadingCoeff = 0

theorem mem_badLeadingSeeds {P : Poly (K := K)} {selected : K → Polynomial K}
    {seeds : Finset K} {g : K} : g ∈ badLeadingSeeds P selected seeds ↔
      g ∈ seeds ∧ coefficientSpecialize (selected g) g (asS P).leadingCoeff = 0 := by
  classical
  unfold badLeadingSeeds
  exact Finset.mem_filter

theorem terminal_source_for_regular
    {I : Type} [DecidableEq I] [DecidableEq K] [Fintype I]
    {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : Koala6844Normalization.CenteredVirtualData x domain σ degree agreements errors excess)
    (hSize : Fintype.card I ≤ Koala6844Receipts.nodes)
    (hPole : data.d0.natDegree + Koala6844Normalization.affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (hFact : ∀ d < prime, (d.factorial : K) ≠ 0)
    (src : SourceShape) (hForm : sourceWellFormed src = true) (hMargin : sourceMargin src)
    (H : MvPolynomial (Fin 4) K) (F : RCN266.RegularIndex H)
    (seeds : Finset K) (hsub : seeds ⊆ RCN140.regularSeeds H data.selected data.seeds F)
    (r y t : ℕ) (hr : 1 ≤ r) (hy : 1 ≤ y) (ht : 1 ≤ t)
    (hFflag : wt residualSWeights F.val ≤ r ∧ wt residualYSWeights F.val ≤ y ∧ wt residualTotalWeights F.val ≤ t)
    (hFT : src.L+src.q < wt residualTotalWeights F.val) :
    (∃ Q, ProperCut F.val Q (src.B+src.s*(r-1)) (src.U+src.s*(y-1))
      (src.L+src.q+src.s*(t-1)) seeds data.selected) ∨
    ∃ source : Source F.val, source.d = src.k+1 ∧
      source.flag = ⟨src.graphIncrement.total,src.graphIncrement.middle,src.graphIncrement.slope⟩ ∧
      source.B = src.B ∧ source.U = src.U ∧ source.T = src.L+src.q ∧ source.P ≠ 0 ∧
      ProperCut F.val (asS source.P).leadingCoeff src.B src.U (src.L+src.q)
        (badLeadingSeeds source.P data.selected seeds) data.selected := by
  classical
  obtain ⟨P,hP,hflag,hpartials,hlead⟩ := exists_physical_source_of_receipt data hSize hPole hLead
    hFact src hForm hMargin
  have hfamily : seeds ⊆ data.seeds := fun _ hg => RCN140.regularSeeds_subset H data.selected data.seeds F (hsub hg)
  have hsolution (g : K) (hg : g ∈ seeds) : RCN319.specialization K (data.selected g) g F.val = 0 := by
    have hreg := hsub hg
    change g ∈ data.seeds.filter (fun z => RCN286.RegularSolution F.val (data.selected z) z) at hreg
    exact (Finset.mem_filter.mp hreg).2.1
  have hF := (RCN167.positiveRFactors_spec H F.val F.property).1
  have hm : 2*src.s ≤ src.B ∧ src.B ≤ src.m ∧ src.m+src.s ≤ src.U ∧ src.U ≤ src.L ∧
      src.k ≤ src.s ∧ src.s < src.m ∧ src.k+1 ≤ src.n0 ∧ 2*(src.n0-src.k-1) ≤ src.B ∧
      src.s < prime ∧ src.q ≤ src.U := of_decide_eq_true ((Bool.and_eq_true_iff.mp hForm).1)
  obtain ⟨hsB,hBm,hmsU,hUL,hks,_,hdn,hnB,_,_⟩ := hm
  obtain hcut | ⟨source,hsource,hd,hf,hB,hU,hT⟩ := proper_cut_or_graph_source F.val P src r y t
    hF hP hFT hsB (by omega) hUL hks hdn (by omega) hr hy ht hFflag hflag seeds data.selected hsolution
    (fun g hg => hpartials g (hfamily hg)) (fun hs g hg => hlead hs g (hfamily hg))
  · exact Or.inl hcut
  · right
    refine ⟨source,hd,hf,hB,hU,hT,(fun hz => hP (hsource.symm.trans hz)),?_⟩
    rw [hsource]
    exact leading_properCut F.val P src.B src.U (src.L+src.q) hF hP hFT
      (fun e he => ⟨(hflag e he).1,(hflag e he).2.2.1,(hflag e he).2.2.2⟩)
      (badLeadingSeeds P data.selected seeds) data.selected (fun g hg => (mem_badLeadingSeeds.mp hg).2)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
