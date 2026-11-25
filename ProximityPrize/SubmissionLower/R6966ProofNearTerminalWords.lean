import ProximityPrize.SubmissionLower.R6966ProofNearLedgerNormalize
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerWordMethods
import ProximityPrize.SubmissionLower.R6966ProofNativeAffineTariff
import ProximityPrize.SubmissionLower.R6966ProofNativeSurfaceTariff
import ProximityPrize.SubmissionLower.R6966ProofNearBook

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

private def widths (i j : Fin 23) (z : Fin 2) : ℕ := inCap (binAt i j z)

private theorem closed_widths {G : Pade.Row SeedField} (N : Native G) {i j : Fin 23}
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
    (q : Quote) (b : Band) {i j : Fin 23}
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
