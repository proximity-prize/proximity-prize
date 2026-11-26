import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6966ProofNearCases
import ProximityPrize.SubmissionLower.R6966ProofNearTerminalFacts
set_option Elab.async false



set_option Elab.async false

namespace Research6966.NearTerminal
open Finset Polynomial
open K1 (K)
open K1_14 (Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2 (mass)
open K1_14_3 (Surface ProjectedProduct SeedField)
open KoalaRect (axisDegree)
open PadeNativeQuotient (Native axis)
open Lower6960.Rescue6966 (Model Family word terminalShape OnSurface)
open NearLedger NearBook
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

private theorem density_mono {e g : ℕ} (h : e≤g) : density e≤density g :=
  Nat.mul_le_mul_right prime (rate_mono h)

private theorem round_le {e g top : ℕ} (h₀ : e≤top) (h₁ : g≤top) (ht : 3≤top) :
    (max 3 g-1)*e≤top^2 := by
  rw [pow_two]
  exact Nat.mul_le_mul ((Nat.sub_le _ _).trans (max_le ht h₁)) h₀

private theorem grade_cap (q : Quote) (b : Band) (a : ℕ) : q.degreeCap b a≤b.high := by
  unfold Quote.degreeCap
  split
  · exact le_rfl
  · exact min_le_left _ _

private theorem content_at19 (b : Fin 7) : (band b).low=19 → (band b).content=8 := by
  fin_cases b <;> decide

private theorem content_at21 (b : Fin 7) : (band b).low=21 → (band b).content=8 := by
  fin_cases b <;> decide

private theorem high_seven (b : Fin 7) : 7≤(band b).high := by fin_cases b <;> decide

/-- A concentrated graph is charged with the exact method selected by
the verified quote. The off-graph source mass is charged separately. -/
private theorem graph_count {u deleted} {M : Model u deleted} {Γ T : Finset K} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2317≤M.overhead.toNat) (hi : M.overhead.toNat≤2522)
    (P Q : Packet M Crt) (r : Fin 58) (bill : Invoice (branch r))
    (main_mass : bill.primaryMass=mass P.sources 1) (rescue_mass : bill.rescueMass=mass Q.sources 1)
    (sub : T⊆Γ) (marks : ∀ γ∈T,∃ q∈parents P Q,OnSurface F q γ)
    {f : Equation} (full : ProjectedProduct (parents P Q) f) (nonempty : (parents P Q).Nonempty)
    (b : Fin 7) (lower : (band b).low≤f.natDegree) (upper : f.natDegree≤(band b).high)
    {G : Pade.Row SeedField} (gp : G.primitive) (bounded : G.graphDegree≤(band b).maxGraph)
    (control : Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep))
      (Pade.Native.sheets (parents P Q)) (band b).content) : bill.paid+T.card≤core := by
  let bnd := band b
  let a := G.graphDegree
  have a0 : 1≤a := by unfold a Pade.Row.graphDegree; omega
  obtain ⟨N⟩:=PadeNativeQuotient.exists_native gp
  have parent (q : _) (h : q∈parents P Q) := (parents_geo P Q h).1
  have pass (q : _) (h : q∈parents P Q) := (parents_geo P Q h).2
  have heavy : bnd.content<f.natDegree := (Nat.le_mul_of_pos_left _ (by decide : 0<2)).trans_lt
    ((band_props b).2.1.trans_le lower)
  obtain ⟨H,J,witness,other,jDegree,fDegree⟩:=partition parent full bnd.content heavy N gp control
  let onParents := owning N.poly (parents P Q)
  let offParents := outside N.poly (parents P Q)
  let U := T.filter (fun γ=>∃ q∈onParents,OnSurface F q γ)
  let V := T\U
  have part : V.card+U.card=T.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have on_marks (γ : K) (mem : γ∈U) : ∃q∈onParents,OnSurface F q γ := (mem_filter.mp mem).2
  have off_marks (γ : K) (mem : γ∈V) : ∃q∈offParents,OnSurface F q γ := by
    obtain ⟨yes,no⟩:=mem_sdiff.mp mem
    obtain ⟨q,hq,mark⟩:=marks γ yes
    have out : N.poly∉q.asIdeal := fun belongs=>
      no (mem_filter.mpr ⟨yes,q,mem_filter.mpr ⟨hq,belongs⟩,mark⟩)
    exact ⟨q,mem_filter.mpr ⟨hq,out⟩,mark⟩
  have Usub : U⊆Γ := (filter_subset _ _).trans sub
  have Vsub : V⊆Γ := sdiff_subset.trans sub
  have owned : NativeAffineRows.Owned F U onParents N := by
    intro γ hγ
    obtain ⟨q,mem,hq⟩:=on_marks γ hγ
    exact ⟨q,mem,(mem_filter.mp mem).2,hq⟩
  let UMass := mass (ownerSources N.poly (sources P Q)) 1
  let VMass := mass (otherSources N.poly (sources P Q)) 1
  have combined : UMass+VMass≤bill.mass := by
    have sum := split_mass N.poly (sources P Q) 1
    have many := mass_union P Q 1
    change UMass+VMass=mass (sources P Q) 1 at sum
    rw [←main_mass,←rescue_mass] at many
    exact sum.le.trans many
  have smallU : UMass≤massCap := ((Nat.le_add_right _ _).trans combined).trans bill.mass_le
  have smallV : VMass≤massCap := ((Nat.le_add_left _ _).trans combined).trans bill.mass_le
  have degH : H.natDegree≤bnd.high :=
    (subset_degree (filter_subset _ _) witness.1 full).trans upper
  have feeV : V.card≤density (bnd.off a)*VMass+bnd.high^2 := by
    rcases other with pr | ⟨empty,_⟩
    · have below : bnd.off a≤7 := by
        have limited : bnd.content≤8 := (band_props b).2.2.1
        unfold Band.off
        omega
      have count := (small_degree_count F Vsub hi pr (bnd.off a) VMass (by omega)
        jDegree smallV (outside_cap P Q N.poly pr) off_marks).1
      have enough := below.trans (high_seven b)
      exact count.trans (Nat.add_le_add_left (round_le (jDegree.trans enough) enough (band_props b).2.2.2) _)
    · have zero : V=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro γ mem
        obtain ⟨q,hq,_⟩:=off_marks γ mem
        have mem' : q∈outside N.poly (parents P Q) := hq
        rw [empty] at mem'
        exact notMem_empty _ mem'
      rw [zero,card_empty]
      exact Nat.zero_le _
  let i := seedBin (axis N.poly 0)
  let j := seedBin (axis N.poly 1)
  have in₀ : InBin i (axis N.poly 0) := seedBin_valid _
  have in₁ : InBin j (axis N.poly 1) := seedBin_valid _
  obtain ⟨phys⟩:=HelperPhysicalModel.exists_model Crt (NativeWitnessBank.irreducible N gp)
    (by rw [NativeGraphMarks.slope_degree N gp];decide)
  let geom : GraphEvidence bnd a i j :=
    ⟨H.natDegree,J.natDegree,axisDegree H,UMass,VMass,lower.trans fDegree,degH,jDegree,
      fun z=>axis_total (owner_cap P Q N.poly witness.1) z,
      fun pick legal=>quotient_bound lo hi Crt (word M) N gp phys witness
        (fun q h=>parent q (mem_filter.mp h).1) (fun q h=>pass q (mem_filter.mp h).1)
        in₀ in₁ pick legal⟩
  let q:=quote b a i j
  have valid : q.Valid bnd a i j := quote_valid b a a0 bounded i j
  obtain ⟨cap,axes⟩:=q.bounds valid geom smallU
  let g := q.degreeCap bnd a
  have gcap : g≤bnd.high := grade_cap q bnd a
  have feeU (small : g<48) : U.card≤density g*UMass+bnd.high^2 ∧
      U.card≤rate g*(axisDegree H 0+prime*axisDegree H 1)+bnd.high^2 := by
    obtain ⟨native,axis⟩:=small_degree_count F Usub hi witness.1 g UMass small cap smallU
      (owner_cap P Q N.poly witness.1) on_marks
    have pad := round_le degH gcap (band_props b).2.2.2
    exact ⟨native.trans (Nat.add_le_add_left pad _),axis.trans (Nat.add_le_add_left pad _)⟩
  have physical : (131071:ℤ)+M.overhead≤wordDegree := by
    change (131071:ℤ)+M.overhead≤133593
    omega
  have wordPrice (which : q.method=.surface ∨ q.method=.affine ∨ q.method=.single ∨ q.method=.fixed) :
      T.card≤q.wordPrice bnd a i j+density (bnd.off a)*VMass+bnd.additive := by
    have words := word_price F Usub physical N gp owned witness.1 q bnd in₀ in₁ valid.2.2.2
      cap (axes 0) (axes 1) which
    change U.card≤q.wordPrice bnd a i j at words
    rw [←part]
    have all := Nat.add_le_add feeV words
    unfold Band.additive
    omega
  apply Quote.finish bill valid geom combined T.card
  have pay := valid.2.2.2
  cases mode : q.method
  · simp only [Quote.Demand,mode]
  · simp only [Quote.Paid,mode] at pay
    simp only [Quote.Demand,mode]
    let both := max g (bnd.off a)
    have gsmall : g<48 := (le_max_left _ _).trans_lt pay.1
    have u := (feeU gsmall).1
    have flex₀ := Nat.mul_le_mul_right UMass (density_mono (show g≤both from le_max_left ..))
    have flex₁ := Nat.mul_le_mul_right VMass (density_mono (show bnd.off a≤both from le_max_right ..))
    have whole := Nat.mul_le_mul_left (density both) combined
    rw [Nat.mul_add] at whole
    change T.card≤density both*bill.mass+bnd.additive
    unfold Band.additive
    omega
  · simp only [Quote.Paid,mode] at pay
    simp only [Quote.Demand,mode]
    have u := (feeU pay.1).2
    change T.card≤rate g*(axisDegree H 0+prime*axisDegree H 1)+density (bnd.off a)*VMass+bnd.additive
    unfold Band.additive
    omega
  · simpa only [Quote.Demand,mode] using wordPrice (Or.inl mode)
  · simpa only [Quote.Demand,mode] using wordPrice (Or.inr (Or.inl mode))
  · simpa only [Quote.Demand,mode] using wordPrice (Or.inr (Or.inr (Or.inl mode)))
  · simpa only [Quote.Demand,mode] using wordPrice (Or.inr (Or.inr (Or.inr mode)))
  · simp only [Quote.Paid,mode] at pay
    simp only [Quote.Demand,mode]
    rcases pay with p0 | p1 | p2
    · obtain ⟨low,grade,axis⟩ := p0
      have degree : 19≤f.natDegree := low ▸ lower
      have content : (band b).content=8 := content_at19 b low
      rw [content] at control
      exact large_graph19g5 lo hi Crt (word M) nonempty parent pass full degree N gp grade (axis.trans in₁.1) control
    · obtain ⟨low,grade,axis⟩ := p1
      have degree : 19≤f.natDegree := low ▸ lower
      have content : (band b).content=8 := content_at19 b low
      rw [content] at control
      exact large_graph19g6 lo hi Crt (word M) nonempty parent pass full degree N gp grade (axis.trans in₁.1) control
    · obtain ⟨low,grade,axis⟩ := p2
      have degree : 21≤f.natDegree := low ▸ lower
      have content : (band b).content=8 := content_at21 b low
      rw [content] at control
      exact large_graph21g5 lo hi Crt (word M) nonempty parent pass full degree N gp grade (axis.trans in₁.1) control

/-- The retained marks of the actual near packets, together with both
prefix invoices, fit the 69.66 budget at every transition height. -/
theorem count {u deleted} {M : Model u deleted} {Γ T : Finset K} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2317≤M.overhead.toNat) (hi : M.overhead.toNat≤2522)
    (b c : NearBook.Packet M Crt) (r : Fin 58) (I : NearLedger.Invoice (NearLedger.branch r))
    (m₀ : I.primaryMass=mass b.sources 1) (m₁ : I.rescueMass=mass c.sources 1)
    (d₀ : mass b.sources 0≤(branch r).primary.grade) (d₁ : mass c.sources 0≤(branch r).rescue.grade)
    (sub : T⊆Γ) (marks : ∀ γ∈T,∃ q∈parents b c,OnSurface F q γ) :
    I.paid+T.card≤NearLedger.core := by
  classical
  by_cases live : (parents b c).Nonempty
  · obtain ⟨f,project⟩:=K1_14_3_7.proof (parents b c) live (fun q h=>(parents_geo b c h).1)
    have maximum : f.natDegree≤graphCap :=
      ((projected_cap b c Subset.rfl project).trans (Nat.add_le_add d₀ d₁)).trans (branch_base r).2.2.2.2
    by_cases low : f.natDegree≤18
    · have wide : mass (sources b c) 1≤I.mass := by
        rw [Invoice.mass,m₀,m₁]
        exact mass_union b c 1
      have coefficients (i : ℕ) : (f.coeff i).totalDegree≤I.mass :=
        (NativeSeedDegree.projected_seed project (sources b c) (fun _ h=>sources_active b c h)
          (fun _ h=>origin b c h) i).trans wide
      exact small r I f.natDegree T.card low
        (small_degree_count F sub hi project f.natDegree I.mass (by omega) le_rfl I.mass_le coefficients marks).1
    · let bandIndex:=bandFor f.natDegree
      obtain ⟨lower,upper⟩:=bandFor_bounds (show 19≤f.natDegree by omega) maximum
      obtain ⟨G,gp,grade,control⟩:=classify Crt lo hi bandIndex b c live project lower
      exact graph_count F Crt lo hi b c r I m₀ m₁ sub marks project live bandIndex lower upper gp grade control
  · have no : T=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      obtain ⟨p,hp,_⟩:=marks γ hγ
      exact live ⟨p,hp⟩
    rw [no,card_empty,Nat.add_zero]
    have paid := I.paid_credit
    have floor := (branch_base r).1
    omega

#print axioms count
end
end Research6966.NearTerminal
