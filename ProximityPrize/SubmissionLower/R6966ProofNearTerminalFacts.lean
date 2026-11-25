import ProximityPrize.SubmissionLower.R6966ProofNearBook
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerCatalogue
import ProximityPrize.SubmissionLower.R6966ProofSpreadCatalogue

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
    (sub : T⊆Γ) (hi : M.overhead.toNat≤2499) {S : Finset Surface} {f : Equation}
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

theorem band_props (b : Fin 4) :
    2≤(band b).low ∧ 2*(band b).content<(band b).low ∧ (band b).content≤7 ∧ 3≤(band b).high := by
  fin_cases b <;> decide

theorem spread_prices (b : Fin 4) {h : ℕ} (lo : 2330≤h) (hi : h≤2499) :
    (∀ a, (band b).maxGraph<a → a≤(band b).content →
      PadeCutoff.excluded agreement h (band b).low a ((band b).low-(band b).content+a)
        SpreadCatalogue.shape SpreadCatalogue.box SpreadCatalogue.nodes SpreadCatalogue.moment) ∧
    (∀ a, (band b).low+1-((band b).low+1)/2≤a → a≤(band b).low-(band b).content →
      PadeCutoff.excluded agreement h (band b).low a (band b).low
        SpreadCatalogue.shape SpreadCatalogue.box SpreadCatalogue.nodes SpreadCatalogue.moment) := by
  fin_cases b
  · exact ⟨fun _=>SpreadCatalogue.partial19 lo hi,fun _=>SpreadCatalogue.full19 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial21 lo hi,fun _=>SpreadCatalogue.full21 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial25 lo hi,fun _=>SpreadCatalogue.full25 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial34 lo hi,fun _=>SpreadCatalogue.full34 lo hi⟩

theorem classify {u deleted} {M : Model u deleted} {D : PoleData M.overhead.toNat}
    (Crt : CRTLift D) (lo : 2330≤M.overhead.toNat) (hi : M.overhead.toNat≤2499)
    (b : Fin 4) (P Q : Packet M Crt) (nonempty : (parents P Q).Nonempty)
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
