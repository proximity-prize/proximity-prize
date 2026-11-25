import ProximityPrize.SubmissionLower.R6966ProofNearTerminalFacts
import ProximityPrize.SubmissionLower.R6966ProofLargeSeedExclusion

set_option Elab.async false

namespace Research6966.NearTerminal
open Finset Polynomial
open K1 (p I)
open K1_14 (Jet Equation L)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree seedDegree_le)
open K1_14_3 (Surface Parent ProjectedProduct SeedField SeedClosure)
open PadeNativeQuotient (Native axis axis_le)
open NearLedger
open NearBook
open Lower6960.Rescue6966 (terminalShape)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 6500000
set_option maxRecDepth 6500
set_option backward.isDefEq.respectTransparency false

theorem axis_seed (P : Jet) (z : Fin 2) : axis P z≤seedDegree P :=
  (axis_le ..).mpr (fun j i=>
    (MvPolynomial.degreeOf_le_totalDegree ..).trans ((seedDegree_le P _).mp le_rfl j i))

theorem seeded_of_positive {P : Jet} (pos : 0<seedDegree P) : K1_14_2.UsesSeed P := by
  unfold K1_14_2.UsesSeed
  by_contra! none
  exact (Nat.not_le_of_lt pos) ((seedDegree_le P 0).mpr none)

private theorem catalogue_lower (k : Fin 39) : 0<(HelperWindowCatalogue.ordinary k).lower := by
  fin_cases k <;> decide

theorem quotient_bound {h : ℕ} (lo : 2330≤h) (hi : h≤2499) {D : PoleData h}
    (Crt : CRTLift D) (word : I→L)
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive)
    (phys : HelperPhysicalModel.Model Crt N.poly)
    {S : Finset Surface} {H : Equation} (witness : NativeWitnessBank.witnessed N S H)
    (geo : ∀ q∈S,Parent q) (pass : ∀ q∈S,TerminalBanks.Pass Crt word agreement terminalShape q)
    {i j : Fin 23} (bin₀ : InBin i (axis N.poly 0)) (bin₁ : InBin j (axis N.poly 1))
    (pick : Pick) (legal : pick.Valid G.graphDegree i j) :
    (pick.bank.reserve+1)*H.natDegree≤pick.bank.B+(G.graphDegree-1)*pick.bank.J ∧
      ∀ z u, upper (binAt i j z)=some u →
        (pick.bank.reserve+1)*KoalaRect.axisDegree H z≤pick.seedBudget z+pick.bank.J*u := by
  have bins (z : Fin 2) : InBin (binAt i j z) (axis N.poly z) := by
    fin_cases z
    · exact bin₀
    · exact bin₁
  have lower : if pick.bank.rect then pick.bank.lower≤axis N.poly pick.narrow
      else pick.bank.lower≤seedDegree N.poly := by
    have admission := legal.2
    cases tag : pick.bank.rect
    · simp only [tag,Bool.false_eq_true,ite_false] at admission ⊢
      exact admission.trans (max_le (bin₀.1.trans (axis_seed ..)) (bin₁.1.trans (axis_seed ..)))
    · simp only [tag,ite_true] at admission ⊢
      exact admission.trans (bins pick.narrow).1
  have seed : pick.bank.lower≤seedDegree N.poly := by
    split at lower
    · exact lower.trans (axis_seed ..)
    · exact lower
  have seeded := seeded_of_positive ((catalogue_lower pick.index).trans_le seed)
  have fits : TerminalBanks.inside pick.bank.shape terminalShape :=
    HelperWindowNative.shape_inside pick.verified terminalShape (by decide) (by decide) (by decide)
  have est := HelperWindowNative.projected_bounds pick.verified lo hi Crt word N gp phys legal.1.symm seeded
    witness fits (axis N.poly) pick.narrow
    (fun j i z => (axis_le ..).mp le_rfl j i) lower geo pass
  refine ⟨est.1,fun z u hu => (est.2 z).trans ?_⟩
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ((bins z).2 u hu)) _

/-- A witness of high second-axis degree on a degree-five graph forces
17 distinct actual on-graph ordinates into the physical exclusion. -/
theorem large_graph {h : ℕ} (lo : 2330≤h) (hi : h≤2499) {D : PoleData h} (Crt : CRTLift D)
    (word : I→L) {S : Finset Surface} (has : S.Nonempty) (geo : ∀ q∈S,Parent q)
    (pass : ∀ q∈S,TerminalBanks.Pass Crt word agreement terminalShape q)
    {f : Equation} (full : ProjectedProduct S f) (degree : 19≤f.natDegree)
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive)
    (graphDegree : G.graphDegree=5) (large : 1024≤axis N.poly 1)
    (control : Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 7) :
    False := by
  classical
  obtain ⟨f',T,v,pr,size,sheets⟩:=Pade.Native.projected_sheets S has geo
  let on := T.filter (fun y=>(G.map (algebraMap SeedField Pade.Native.Sep)).err v y=0)
  let off := T\on
  have miss := control off v (by
    intro y hy
    obtain ⟨mem,bad⟩:=mem_sdiff.mp hy
    exact ⟨sheets y mem,fun zero=>bad (mem_filter.mpr ⟨mem,zero⟩)⟩)
  rw [Pade.Row.degree_map,graphDegree] at miss
  have total : on.card+off.card=T.card := by
    rw [Nat.add_comm]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have many : 19≤T.card := degree.trans_eq ((same_degree full pr).trans size.symm)
  obtain ⟨kept,subset,keepSize⟩:=exists_subset_card_eq (show 17≤on.card by omega)
  let emb : Pade.Native.Sep→+*SeedClosure := (separableClosure SeedField SeedClosure).val.toRingHom
  let pts := kept.image emb
  let slope (z : SeedClosure) := if H:∃y∈kept,emb y=z then emb (v H.choose) else 0
  have atPoint (y : Pade.Native.Sep) (hy : y∈kept) : slope (emb y)=emb (v y) := by
    have H : ∃ z∈kept,emb z=emb y := ⟨y,hy,rfl⟩
    simp only [slope,dite_eq_left H,emb.injective H.choose_spec.2]
  have n : pts.card=17 := (card_image_of_injective _ emb.injective).trans keepSize
  have fit : TerminalBanks.inside SpreadCatalogue.shape terminalShape := by unfold TerminalBanks.inside; decide
  refine LargeSeedExclusion.excluded lo hi Crt word fit geo pass full degree gp graphDegree N large pts slope n ?_
  intro y hy
  obtain ⟨z,hz,rfl⟩:=mem_image.mp hy
  have picked : z∈on := subset hz
  obtain ⟨tz,ok⟩:=mem_filter.mp picked
  rw [atPoint z hz]
  refine ⟨(Pade.Native.sheets_iff S z (v z)).mp (sheets z tz),?_⟩
  change (G.a.map (algebraMap SeedField SeedClosure)).eval (emb z)*slope (emb z)-
    (G.b.map (algebraMap SeedField SeedClosure)).eval (emb z)=0
  rw [atPoint z hz]
  have lifted (Q : SeedField[X]) :
      emb ((Q.map (algebraMap SeedField Pade.Native.Sep)).eval z)=
        (Q.map (algebraMap SeedField SeedClosure)).eval (emb z) := by
    rw [eval_map,eval_map]
    exact (Polynomial.aeval_algHom_apply (separableClosure SeedField SeedClosure).val z Q).symm
  have law := congrArg emb ok
  simp only [Pade.Row.err,Pade.Row.map,map_sub,map_mul,map_zero] at law
  rwa [lifted,lifted] at law

#print axioms quotient_bound
#print axioms large_graph
end
end Research6966.NearTerminal
