import ProximityPrize.SubmissionLower.KoalaH2429TerminalBProduction
import ProximityPrize.SubmissionLower.KoalaH2429TerminalBArithmetic
import ProximityPrize.SubmissionLower.TwoTerminal
import ProximityPrize.SubmissionLower.KoalaRectQuotient

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KoalaH2429TerminalB
noncomputable section

open Polynomial Finset
open HighCore82258 (AnchorModel AnchoredFamily agreement crtWord)
open K1_14 (Equation SeedBound atMark)
open KoalaRect (axisDegree rectSlots rectGain rectDebit seedBound_of_axis)

theorem retained_roots {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ}
    (T : RetainedTrace M F) :
    ∀ γ ∈ T.marks, atMark T.equation (M.label γ) (F.scalar γ) = 0 := by
  intro γ hγ
  obtain ⟨q,hq,hm⟩ := T.covers γ hγ
  have hz := RingHom.mem_ker.mp (hm (T.projected.vanishes q hq))
  simpa only [coe_eval₂RingHom, eval₂_C, atMark] using hz

private theorem reject {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ}
    (T : RetainedTrace M F) {f : Equation} (hf : f ≠ 0) (hdiv : f ∣ T.equation)
    {E : ℕ} (hE : E ≤ f.natDegree) (he : 0 < E)
    (U d : Fin 2 → ℕ) (hbox : U 0 + U 1 ≤ terminal.shape.U)
    (hslots : ∀ r, rectSlots U (axisDegree f) r ≤ rectSlots U d r)
    (hstrict : rectDebit 2429 terminal.nodeRows terminal.poleMoment U <
      rectGain agreement 2429 terminal.shape E U d) : False := by
  have hcut := KoalaTwoTerminal.rectLoss_of_dvd (h := 2429)
    (by decide) (by decide) (by decide) T.crt (crtWord M) agreement terminal.shape U d
    (by decide) (by decide) hbox terminal_ok.moment.2 (by decide)
    terminal_ok.nodes.le terminal_ok.moment.1 he T.geometric T.terminal_pass
    hf hE T.projected hdiv hslots
  exact (not_le_of_gt hstrict) hcut

theorem degree_lt_23 {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ}
    (T : RetainedTrace M F) : T.equation.natDegree < 23 := by
  by_contra! he
  let W := rectWitness 23
  have hnonzero : T.equation ≠ 0 := by
    intro hz
    simp [hz] at he
  refine reject T hnonzero (dvd_refl _) he (by decide) W.U W.order
    (witness_guards (by decide : 0 < 23) (by decide)).2 ?_
    (rect_bounds (by decide : 0 < 23) (by decide))
  intro r
  have h0 : W.order 0 = 0 := by decide
  have h1 : W.order 1 = 0 := by decide
  simp only [rectSlots,h0,h1,Nat.mul_zero,Nat.sub_zero]
  exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)

/-- Bank B bounds the sum of both seed axes of any positive-degree divisor. -/
theorem axis_sum_le_of_dvd {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ}
    (T : RetainedTrace M F) {f : Equation} (hf : 0 < f.natDegree)
    (hE : f.natDegree < 23) (hdiv : f ∣ T.equation) :
    axisDegree f 0 + axisDegree f 1 ≤ paidCap f.natDegree := by
  have hnonzero : f ≠ 0 := by
    intro hz
    simp [hz] at hf
  obtain ⟨hside,hbox⟩ := witness_guards hf hE.le
  obtain ⟨hlo,hhi,hsum⟩ := witness_order hf hE
  exact KoalaTwoTerminal.oriented_axis_cap (actual := axisDegree f)
    hside hlo hhi hsum hbox (rect_bounds hf hE.le) (reject T hnonzero hdiv le_rfl hf)

theorem resultant_inputs {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ}
    (T : RetainedTrace M F) : T.equation.natDegree < 23 ∧ SeedBound T.equation 474 := by
  have h := degree_lt_23 T
  have he := T.projected.positive
  exact ⟨h, seedBound_of_axis ((axis_sum_le_of_dvd T he h (dvd_refl _)).trans (paidCap_le he h))⟩

theorem axis16_of_dvd {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ}
    (T : RetainedTrace M F) {f : Equation} (he : f.natDegree = 16)
    (hdiv : f ∣ T.equation) : axisDegree f 0 + axisDegree f 1 ≤ 380 := by
  have h := axis_sum_le_of_dvd T (by omega : 0 < f.natDegree) (by omega) hdiv
  rwa [he, paidCap16] at h

theorem axis17_of_dvd {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ}
    (T : RetainedTrace M F) {f : Equation} (he : f.natDegree = 17)
    (hdiv : f ∣ T.equation) : axisDegree f 0 + axisDegree f 1 ≤ 369 := by
  have h := axis_sum_le_of_dvd T (by omega : 0 < f.natDegree) (by omega) hdiv
  rwa [he, paidCap17] at h

theorem resultant_budget {a e j : ℕ} (ha : a ≤ 116000000000000000)
    (he : e ≤ 17) (hj : j < 23) :
    (e+j)*474 < K1.p ∧
      a + prefixFee + (K1.p+1)*((e+j)*474) ≤ 273115485059352112 := by
  change (e+j)*474 < 2130706433 ∧
    a + 121295101706637002 + 2130706434*((e+j)*474) ≤ 273115485059352112
  omega

end
end KoalaH2429TerminalB
