import ProximityPrize.SubmissionLower.R6970Height2312Wide6

open _root_.Lower6960 _root_.Research6969
set_option autoImplicit true
set_option Elab.async false

namespace Research6970.Height2313.Lower6960.Prefix6969NearOuter
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (toJet)
open K1_14_2_2 (Active mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open Far6969RescueGeometry (Model Family OnSurface word)
open Research6969 Research6966
open scoped Classical BigOperators Differential

abbrev affineFee : ℕ :=
  p*56+(3*(133482*56)^2*(262144-133482)^3)/(179730-133482)^3

private theorem affine_roots {u deleted} {M : Model u deleted} {Γ T : Finset K}
    (F : Family M Γ) (sub : T⊆Γ) (hi : M.overhead.toNat≤2411)
    {G : Jet} (prime : Prime G) (slope : G.natDegree=1) (affine : jetDegree G=1)
    (width : seedDegree G≤56) (roots : ∀γ∈T,jetAt G (M.label γ) (F.scalar γ)=0) :
    T.card≤affineFee := by
  obtain ⟨graph,N,gp,eq,deg⟩ := HelperGraph.of_prime prime slope
  let ev (γ : K) := eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
    (atX (F.scalar γ).derivative)
  let q (γ : K) : Surface := ⟨RingHom.ker (ev γ), RingHom.ker_isPrime _⟩
  have own : NativeAffineRows.Owned F T (T.image q) N := by
    intro z hz
    refine ⟨q z,mem_image.mpr ⟨z,hz,rfl⟩,?_,fun _ h=>h⟩
    rw [eq]
    exact roots z hz
  have cap j i : (N.poly.coeff j).coeff i ∈ MvPolynomial.restrictWeightAtMost (fun _=>1) 56 := by
    rw [eq]
    apply MvPolynomial.mem_restrictWeightAtMost.mpr
    intro m hm
    rw [←Finsupp.degree_eq_weight_one]
    exact (MvPolynomial.le_totalDegree hm).trans ((K1_14_2_2_2_1.seedDegree_le G 56).mp width j i)
  exact NativeAffineTariff.price_floor F sub N gp (deg.trans affine) 56 (by decide) cap
    (by decide) 133482 (by omega) (by decide) (by decide) (by decide) (by decide) own

/-- The refitted actual main packet transfers when the outer exception is
a unit or its affine zero marks have been paid. -/
theorem ordinary {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    (R : Research6970.Height2313.Lower6960.Prefix6969Wide.Rows F Crt)
    (hi : M.overhead.toNat≤2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (mode : R.out.exception=1 ∨ Prime R.out.exception ∧ R.out.exception.natDegree=1 ∧
      jetDegree R.out.exception=1 ∧ seedDegree R.out.exception≤56) :
    Nonempty (Prefix6969Early.Packet F Crt 234329630343844473 133994566145700 1590006772040 351 6143) := by
  obtain ⟨J,C,A,pay,ms,mg,mo,covered⟩:=R.main_prefix hi noPole residues
  let T := Γ.filter (fun γ=>jetAt R.out.exception (M.label γ) (F.scalar γ)=0)
  have affinePay : T.card≤affineFee := by
    rcases mode with unit | ⟨prime,slope,affine,width⟩
    · have empty : T=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro γ mem
        have root := (mem_filter.mp mem).2
        simpa [unit,jetAt] using root
      simp [empty]
    · exact affine_roots F (filter_subset _ _) hi prime slope affine width
        (fun _ h=>(mem_filter.mp h).2)
  have ma (P) (mem : P∈J.final) : Active P := (J.kept_geom (mem_filter.mp mem).1).1
  obtain ⟨f,project⟩ := JointProjection.exists_product A (fun q h => (mg q h).1)
  have measures := JointProjection.measures project J.final ma mo
  have md : mass J.final 0≤338 := by
    apply Nat.le_of_lt_succ
    have q := ms 0
    change (mass J.final 0:ℚ)≤462882/1369 at q
    exact_mod_cast q.trans_lt (by decide +kernel : (462882:ℚ)/1369<339)
  have mv : mass J.final 1≤6110 := by
    apply Nat.le_of_lt_succ
    have q := ms 1
    change (mass J.final 1:ℚ)≤16730567/2738 at q
    exact_mod_cast q.trans_lt (by decide +kernel : (16730567:ℚ)/2738<6111)
  let ordCredit : ℕ := 133994566145700
  let seedCredit : ℕ := 1590006772040
  let w := Research6970.Height2313.Lower6960.Prefix6969Wide.retainedCredit
  let adjust := (ordCredit-w 0)*338+(seedCredit-w 1)*6110
  have adj : ordCredit*f.natDegree+seedCredit*K1_14_4.seedDegree f ≤
      Research6970.Height2313.Lower6960.Prefix6969Wide.retainedCharge J.final+adjust := by
    have cov0 := Prefix6969Early.compensate ordCredit (w 0) (mass J.final 0) 338 md
    have cov1 := Prefix6969Early.compensate seedCredit (w 1) (mass J.final 1) 6110 mv
    have pr0 := Nat.mul_le_mul_left ordCredit measures.1
    have pr1 := Nat.mul_le_mul_left seedCredit measures.2
    unfold Research6970.Height2313.Lower6960.Prefix6969Wide.retainedCharge adjust
    change _ ≤ (∑k,w k*mass J.final k)+_
    simp only [Fin.sum_univ_four]
    omega
  have total : Research6970.Height2313.Lower6960.Prefix6969Wide.prefixCap+adjust+affineFee≤234329630343844473 := by decide +kernel
  refine ⟨⟨C.paid∪T,A,f,project,fun q h=>(mg q h).1,fun q h=>(mg q h).2,
    (measures.1.trans md).trans (by decide),(measures.2.trans mv).trans (by decide),?_,?_⟩⟩
  · have union := card_union_le C.paid T
    change (C.paid∪T).card+ordCredit*f.natDegree+seedCredit*K1_14_4.seedDegree f≤234329630343844473
    omega
  · intro γ mem
    by_cases root : jetAt R.out.exception (M.label γ) (F.scalar γ)=0
    · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem,root⟩))
    · rcases covered γ (mem_filter.mpr ⟨mem,root⟩) with paid | surface
      · exact Or.inl (mem_union_left _ paid)
      · exact Or.inr surface

end
end Research6970.Height2313.Lower6960.Prefix6969NearOuter

