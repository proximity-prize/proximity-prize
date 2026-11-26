import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960ChartGlobalTests
import ProximityPrize.SubmissionLower.R6960MarkedScalarPlace
import ProximityPrize.SubmissionLower.R6960RetainedCrossingLift
import ProximityPrize.SubmissionLower.R6966ProofFarTerminalCount
import ProximityPrize.SubmissionLower.R6966ProofNativeSurfaceTariff
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable0_1

section Merged6967_R6966ProofNearTerminalFacts
set_option Elab.async false





set_option Elab.async false

namespace Research6966.NearTerminal
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedField)
open Lower6960.Rescue6966 (Model Family word terminalShape OnSurface)
open NearLedger
open NearBook
open KoalaRect (axisDegree)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false

theorem same_degree {S : Finset Surface} {f g : Equation}
    (fpr : ProjectedProduct S f) (gpr : ProjectedProduct S g) : f.natDegree=g.natDegree :=
  Nat.le_antisymm
    (natDegree_le_of_dvd (NativeOrdinateMass.divides_of_member fpr gpr.vanishes) gpr.primitive.ne_zero)
    (natDegree_le_of_dvd (NativeOrdinateMass.divides_of_member gpr fpr.vanishes) fpr.primitive.ne_zero)

theorem subset_degree {S R : Finset Surface} {f g : Equation}
    (sub : S⊆R) (fpr : ProjectedProduct S f) (gpr : ProjectedProduct R g) :
    f.natDegree≤g.natDegree :=
  natDegree_le_of_dvd (NativeOrdinateMass.divides_of_member fpr (fun q h=>gpr.vanishes q (sub h)))
    gpr.primitive.ne_zero

theorem small_degree_count {u deleted} {M : Model u deleted} {Γ T : Finset K} (F : Family M Γ)
    (sub : T⊆Γ) (hi : M.overhead.toNat≤2522) {S : Finset Surface} {f : Equation}
    (pr : ProjectedProduct S f) (g d : ℕ) (gSmall : g<48) (deg : f.natDegree≤g) (dSmall : d≤massCap)
    (coeffs : ∀ i, (f.coeff i).totalDegree≤d) (marks : ∀ γ∈T, ∃ q∈S, OnSurface F q γ) :
    T.card≤density g*d+(max 3 g-1)*f.natDegree ∧
      T.card≤rate g*(axisDegree f 0+prime*axisDegree f 1)+(max 3 g-1)*f.natDegree := by
  let n:=max 3 g
  have tame : (2*f.natDegree-1)*axisDegree f 0<p := by
    have cap₀ := (axis_total coeffs 0).trans dSmall
    apply (Nat.mul_le_mul (show 2*f.natDegree-1≤93 by omega) cap₀).trans_lt
    decide
  have fit : n<48:=max_lt (by decide) gSmall
  have counted := NearMarkedCount.count F sub hi pr.positive pr.separable n d (axisDegree f 0) (axisDegree f 1)
    (le_max_left _ _) fit (deg.trans (le_max_right _ _)) coeffs le_rfl le_rfl tame
    (marks_roots F pr marks)
  have rate_le : Lower6960.MarkedEvaluation.rate n+2*f.natDegree-1≤rate g :=
    Nat.sub_le_sub_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 deg) _) _
  have native := counted.trans (Nat.add_le_add_right
    (Nat.mul_le_mul rate_le (min_le_left (p*d) _)) ((n-1)*f.natDegree))
  have axes := counted.trans (Nat.add_le_add_right
    (Nat.mul_le_mul rate_le (min_le_right (p*d) _)) ((n-1)*f.natDegree))
  exact ⟨by simpa only [density,Nat.mul_assoc] using native,axes⟩

theorem band_props (b : Fin 7) :
    2≤(band b).low ∧ 2*(band b).content<(band b).low ∧ (band b).content≤8 ∧ 3≤(band b).high := by
  fin_cases b <;> decide

theorem spread_prices (b : Fin 7) {h : ℕ} (lo : 2317≤h) (hi : h≤2522) :
    (∀ a, (band b).maxGraph<a → a≤(band b).content →
      PadeCutoff.excluded agreement h (band b).low a ((band b).low-(band b).content+a)
        SpreadCatalogue.shape SpreadCatalogue.box SpreadCatalogue.nodes SpreadCatalogue.moment) ∧
    (∀ a, (band b).low+1-((band b).low+1)/2≤a → a≤(band b).low-(band b).content →
      PadeCutoff.excluded agreement h (band b).low a (band b).low
        SpreadCatalogue.shape SpreadCatalogue.box SpreadCatalogue.nodes SpreadCatalogue.moment) := by
  fin_cases b
  · exact ⟨fun _=>SpreadCatalogue.partial19 lo hi,fun _=>SpreadCatalogue.full19 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial21 lo hi,fun _=>SpreadCatalogue.full21 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial24 lo hi,fun _=>SpreadCatalogue.full24 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial25 lo hi,fun _=>SpreadCatalogue.full25 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial29 lo hi,fun _=>SpreadCatalogue.full29 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial41 lo hi,fun _=>SpreadCatalogue.full41 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial43 lo hi,fun _=>SpreadCatalogue.full43 lo hi⟩

theorem classify {u deleted} {M : Model u deleted} {D : PoleData M.overhead.toNat}
    (Crt : CRTLift D) (lo : 2317≤M.overhead.toNat) (hi : M.overhead.toNat≤2522)
    (b : Fin 7) (P Q : Packet M Crt) (nonempty : (parents P Q).Nonempty)
    {f : Equation} (full : ProjectedProduct (parents P Q) f) (degree : (band b).low≤f.natDegree) :
    ∃ G : Pade.Row SeedField, G.primitive ∧ G.graphDegree≤(band b).maxGraph ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (parents P Q)) (band b).content := by
  have hp : 0<M.overhead.toNat := by omega
  have hl : M.overhead.toNat≤131070:=hi.trans (by decide)
  have hc : M.overhead.toNat<p := hi.trans_lt (by decide)
  have fit : TerminalBanks.inside SpreadCatalogue.shape terminalShape := by unfold TerminalBanks.inside; decide
  have width : SpreadCatalogue.shape.B*(131071-M.overhead.toNat)≤SpreadCatalogue.shape.m*agreement :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lo _)).trans (by decide)
  obtain ⟨leftPrices,rightPrices⟩:=spread_prices b lo hi
  obtain ⟨f',project,small|existsGraph⟩:=PadeCutoff.counted_packet hp hl hc Crt (word M)
    SpreadCatalogue.box fit (by decide) (by decide) (by decide) (by decide) width
    SpreadCatalogue.node_eq.le SpreadCatalogue.pole_cap (parents P Q) nonempty
    (fun q h=>(parents_geo P Q h).1) (fun q h=>(parents_geo P Q h).2)
    (band_props b).1 (band_props b).2.1 leftPrices rightPrices
  · exact (Nat.not_lt_of_ge (degree.trans_eq (same_degree full project)) small).elim
  · exact existsGraph

/-- The on-graph projection and an ordinate equation for the off-graph
parents. Empty off-graph support is represented by the unit polynomial. -/
theorem partition {S : Finset Surface} (geo : ∀ q∈S, Parent q)
    {f : Equation} (full : ProjectedProduct S f) (c : ℕ) (large : c<f.natDegree)
    {G : Pade.Row SeedField} (N : PadeNativeQuotient.Native G) (gp : G.primitive)
    (control : Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) c) :
    ∃ H J : Equation,
      NativeWitnessBank.witnessed N (owning N.poly S) H ∧
      (ProjectedProduct (outside N.poly S) J ∨ outside N.poly S=∅ ∧ J=1) ∧
      J.natDegree≤c-G.graphDegree ∧ f.natDegree≤H.natDegree+J.natDegree := by
  classical
  have costa : G.graphDegree≤c := by
    have ctl := control ∅ (fun _=>0) (by simp)
    simpa only [card_empty,zero_add,Pade.Row.degree_map] using ctl
  obtain ⟨J,part,bound⟩ :
      ∃ J : Equation, (ProjectedProduct (outside N.poly S) J ∨ outside N.poly S=∅ ∧ J=1) ∧
        J.natDegree≤c-G.graphDegree := by
    by_cases there : (outside N.poly S).Nonempty
    · obtain ⟨J,proj,cap⟩ := NativeGraphMarks.off_owner N geo control there
      exact ⟨J,Or.inl proj,Nat.le_sub_of_add_le cap⟩
    · exact ⟨1,Or.inr ⟨not_nonempty_iff_eq_empty.mp there,rfl⟩,by simp⟩
  have vanish (q : Surface) (mem : q∈outside N.poly S) : C J∈q.asIdeal := by
    rcases part with proj | ⟨empty,_⟩
    · exact proj.vanishes q mem
    · rw [empty] at mem; exact (notMem_empty q mem).elim
  have jne : J≠0 := by rcases part with proj | ⟨_,rfl⟩; exacts [proj.primitive.ne_zero,one_ne_zero]
  have on : (owning N.poly S).Nonempty := by
    by_contra none
    have div := NativeOrdinateMass.divides_of_member full (D:=J) (by
      intro q mem
      by_cases g : N.poly∈q.asIdeal
      · exact (none ⟨q,mem_filter.mpr ⟨mem,g⟩⟩).elim
      · exact vanish q (mem_filter.mpr ⟨mem,g⟩))
    have d := natDegree_le_of_dvd div jne
    omega
  obtain ⟨H,witness⟩ := NativeWitnessBank.exists_witnessed N gp on
    (fun q mem=>geo q (mem_filter.mp mem).1) (fun q mem=>(mem_filter.mp mem).2)
  have div := NativeOrdinateMass.divides_of_member full (D:=H*J) (by
    intro q mem
    rw [map_mul]
    by_cases g : N.poly∈q.asIdeal
    · exact Ideal.mul_mem_right _ _ (witness.1.vanishes q (mem_filter.mpr ⟨mem,g⟩))
    · exact Ideal.mul_mem_left _ _ (vanish q (mem_filter.mpr ⟨mem,g⟩)))
  have hne := witness.1.primitive.ne_zero
  have deg := natDegree_le_of_dvd div (mul_ne_zero hne jne)
  rw [natDegree_mul hne jne] at deg
  exact ⟨H,J,witness,part,bound,deg⟩

#print axioms classify
#print axioms partition
#print axioms small_degree_count
end
end Research6966.NearTerminal

end Merged6967_R6966ProofNearTerminalFacts

section Merged6967_R6966ProofNearTerminalWords
set_option Elab.async false






set_option Elab.async false

namespace Research6966.NearTerminal
open Finset
open K1 (p K I)
open K1_14 (Equation)
open K1_14_3 (Surface ProjectedProduct SeedField)
open PadeNativeQuotient (Native axis axis_le)
open NearLedger
open Lower6960.Rescue6966 (Model Family)
open NativeAffineRows (Owned)
set_option maxHeartbeats 1400000
set_option maxRecDepth 6500
set_option backward.isDefEq.respectTransparency false

private def widths (i j : Fin 55) (z : Fin 2) : ℕ := inCap (binAt i j z)

private theorem closed_widths {G : Pade.Row SeedField} (N : Native G) {i j : Fin 55}
    (bin₀ : InBin i (axis N.poly 0)) (bin₁ : InBin j (axis N.poly 1))
    (legal : repairFits G.graphDegree i j) :
    (∀ j' i' z, ((N.poly.coeff j').coeff i').degreeOf z≤widths i j z) ∧
      (2*G.graphDegree-1)*widths i j 0<p := by
  refine ⟨?_,legal.2.2⟩
  intro j' i' z
  have witness : axis N.poly z≤widths i j z := by
    fin_cases z
    · exact bin₀.le_cap legal.1
    · exact bin₁.le_cap legal.2.1
  exact (axis_le ..).mp witness j' i'

private theorem graph_positive (G : Pade.Row SeedField) : 1≤G.graphDegree := by
  unfold Pade.Row.graphDegree
  omega

/-- Translate the four actual word interpolation arguments into the
exact integer quote used by the terminal ledger. -/
theorem word_price {u deleted} {M : Model u deleted} {Γ T : Finset K} (F : Family M Γ)
    (sub : T⊆Γ) (physical : (131071:ℤ)+M.overhead≤wordDegree) {S : Finset Surface}
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive) (owners : Owned F T S N)
    {H : Equation} (proj : ProjectedProduct S H)
    (q : Quote) (b : Band) {i j : Fin 55}
    (bin₀ : InBin i (axis N.poly 0)) (bin₁ : InBin j (axis N.poly 1))
    (paid : q.Paid b G.graphDegree i j)
    (g : H.natDegree≤q.degreeCap b G.graphDegree)
    (v₀ : KoalaRect.axisDegree H 0≤q.axisCap i j 0)
    (v₁ : KoalaRect.axisDegree H 1≤q.axisCap i j 1)
    (kind : q.method=.surface ∨ q.method=.affine ∨ q.method=.single ∨ q.method=.fixed) :
    T.card≤q.wordPrice b G.graphDegree i j := by
  let width := widths i j
  rcases kind with selected | selected | selected | selected
  · simp only [Quote.Paid,selected] at paid
    obtain ⟨axes,small⟩:=closed_widths N bin₀ bin₁ paid.1
    by_cases one : G.graphDegree=1
    · have count := NativeAffineTariff.projected F sub proj N gp one width axes
        (by simpa only [one,show 2*1-1=1 by decide,Nat.one_mul] using small)
        wordDegree physical (by decide) (by decide) owners
      apply q.surface_of_scaled b G.graphDegree i j selected g v₀ v₁ (h₀:=wordDegree*inCap i) (h₁:=wordDegree*inCap j)
      · simpa only [seedHeight,one,ite_true] using le_max_right 1 (wordDegree*inCap i)
      · simpa only [seedHeight,one,ite_true] using le_max_right 1 (wordDegree*inCap j)
      · simpa [singular,one,width,widths,binAt,side,WordSurfacePrice.side,yHeight,
          NearLedger.gap,NearLedger.nodes,NearLedger.agreement,NearLedger.prime,
          ProximityPrize.Benchmark.IRSProfile.card_index] using count
    · have nonlinear : 2≤G.graphDegree := by
        have := graph_positive G
        omega
      have count := NativeSurfaceTariff.price F sub proj N gp nonlinear width axes small wordDegree
        physical (by decide) (by decide) owners
      apply q.surface_of_scaled b G.graphDegree i j selected g v₀ v₁ le_rfl le_rfl
      simpa [singular,width,widths,binAt,side,WordSurfacePrice.side,yHeight,seedHeight,one,
        NearLedger.gap,NearLedger.nodes,NearLedger.agreement,NearLedger.prime,
        ProximityPrize.Benchmark.IRSProfile.card_index] using count
  · simp only [Quote.Paid,selected] at paid
    have one := paid.1
    obtain ⟨axes,small⟩:=closed_widths N bin₀ bin₁ paid.2.1
    have count := NativeAffineTariff.rectangular F sub N gp one width axes
      (by simpa only [one,show 2*1-1=1 by decide,Nat.one_mul] using small)
      wordDegree physical (by decide) (by decide) owners
    rw [one]
    apply q.affine_of_scaled b i j selected
    simpa [singular,width,widths,binAt,side,WordSurfacePrice.side,
      NearLedger.gap,NearLedger.nodes,NearLedger.agreement,NearLedger.prime,
      ProximityPrize.Benchmark.IRSProfile.card_index] using count
  · simp only [Quote.Paid,selected] at paid
    obtain ⟨axes,small⟩:=closed_widths N bin₀ bin₁ paid.1
    obtain ⟨active,inactive⟩ : ∃ active : Fin 2, ∀ z, z≠active→width z=0 := by
      by_cases left : inCap i=0
      · refine ⟨1,?_⟩
        intro z different
        fin_cases z
        · exact left
        · exact (different rfl).elim
      · have right : inCap j=0 := by have w:=paid.2.1;omega
        refine ⟨0,?_⟩
        intro z different
        fin_cases z
        · exact (different rfl).elim
        · exact right
    by_cases one : G.graphDegree=1
    · have count := NativeAffineTariff.single_seed F sub N gp one width axes
        (by simpa only [one,show 2*1-1=1 by decide,Nat.one_mul] using small)
        active inactive wordDegree physical (by decide) (by decide) owners
      have maxWidth : width active≤max (inCap i) (inCap j) := by
        fin_cases active
        · exact le_max_left _ _
        · exact le_max_right _ _
      rw [one]
      apply q.single_affine_of_scaled b i j selected maxWidth
      simpa [singular,width,widths,binAt,side,WordSurfacePrice.side,
        NearLedger.gap,NearLedger.nodes,NearLedger.agreement,NearLedger.prime,
        ProximityPrize.Benchmark.IRSProfile.card_index] using count
    · have nonlinear : 2≤G.graphDegree := by
        have := graph_positive G
        omega
      have count := NearLedgerWordMethods.single F sub N gp nonlinear width axes small active inactive physical owners
      simpa [Quote.wordPrice,selected,singular,width,widths,binAt] using count
  · simp only [Quote.Paid,selected] at paid
    have axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z≤0 := by
      intro j' i' z
      apply (axis_le ..).mp _ j' i'
      fin_cases z
      · exact bin₀.2 0 paid.1
      · exact bin₁.2 0 paid.2.1
    by_cases one : G.graphDegree=1
    · have count := NativeAffineTariff.fixed F sub N gp one axes wordDegree physical
        (by decide) (by decide) owners
      change T.card*(agreement-wordDegree)≤WordSurfacePrice.side (Fintype.card I) agreement wordDegree 1 at count
      rw [ProximityPrize.Benchmark.IRSProfile.card_index] at count
      have price := NativeAffineLedger.fixed_floor (n:=nodes) (a:=agreement) (d:=wordDegree)
        (by decide) (by decide) count
      rw [one]
      simp only [Quote.wordPrice,selected,yHeight,Nat.sub_self,Nat.mul_zero,Nat.zero_add,Nat.one_mul]
      exact price.trans (Nat.le_succ _)
    · have nonlinear : 2≤G.graphDegree := by
        have := graph_positive G
        omega
      simpa only [Quote.wordPrice,selected] using
        (NearLedgerWordMethods.fixed F sub N gp nonlinear axes physical owners).trans (Nat.le_succ _)

#print axioms word_price
end Research6966.NearTerminal

end Merged6967_R6966ProofNearTerminalWords
