import ProximityPrize.SubmissionLower.H2429TerminalBudget
import ProximityPrize.SubmissionLower.KoalaH2429TerminalA
import ProximityPrize.SubmissionLower.KoalaH2429TerminalBForTwoTerminal

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace H2429NormalCount
noncomputable section
open Polynomial Finset HighCore82258
open K1_14 (Equation SeedBound atMark)
open K1_14_3 (SeedField)
open KoalaRect (axisDegree seedBound_of_axis)
open H2429AffineInventory (Framed fee)
open H2429TerminalBudget (cap)
open private K1_14_3_7.toSeed K1_14_3_7.seedGCD from ProximityPrize.SubmissionLower.Fast053
open K1_14_3_7 (toSeed seedGCD)
open scoped BigOperators

private theorem count_on_axes {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ}
    (hw : effectiveHeight M = 2429) (hshift : M.shift ∉ Γ) {f : Equation} (hf : Reduced f)
    (he : f.natDegree < 23) {T : Finset K} (hT : T ⊆ Γ)
    (hroots : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0)
    {v : ℕ} (hv : axisDegree f 0 + axisDegree f 1 ≤ v) (hwidth : v ≤ 476)
    (hcompress : ¬ KoalaTwoSectionPrice.singleCut f.natDegree → v ≤ 448)
    (hprice : ∀ a b, a+b=v → fee f.natDegree + H2429TerminalCount.rootFee f.natDegree a b ≤ cap) :
    T.card + fee f.natDegree ≤ cap := by
  let a := axisDegree f 0
  let b := v-a
  have hs : a+b=v := by dsimp [a,b]; omega
  have hb : axisDegree f 1 ≤ b := by dsimp [a,b]; omega
  have hc := H2429TerminalCount.roots M F hw hshift hf (by omega) hT hroots
    (show axisDegree f 0 ≤ a from le_rfl) hb (hs ▸ hwidth)
    (fun h => hs ▸ hcompress h)
  have h := hprice a b hs
  omega

/-- Use A for the prefix and ordinary grades. Bank B strengthens the two
hard irreducible grades or pays their common marks with a resultant. -/
theorem count {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (hw : effectiveHeight M = 2429) (hshift : M.shift ∉ Γ) (frame : Framed F) :
    Γ.card + 1 ≤ cap := by
  classical
  have hd : InBand .h2429 (effectiveHeight M) := by
    rw [hw]
    exact ⟨le_rfl,le_rfl⟩
  obtain ⟨H,hH⟩ := FrontCore82258.adjacent_chart M F
  obtain ⟨C⟩ := HighCore82258BankProof.interpolation_sources_for_crt .h2429 u del M Γ F hd hshift H hH
  let rows := C.rows
  have src : Source .h2429 M F rows := C.source
  obtain ⟨pairs⟩ := buffered_pairs .h2429 M F hd src
  obtain ⟨Q⟩ := H2429AffineInventory.produce M F hd frame rows src pairs
  let T := Q.marks
  let f := Q.equation
  let e := f.natDegree
  have hp : (Γ \ T).card + 1 ≤ fee e := Q.prefix_paid
  have hpay := H2429TerminalBudget.prefix_le e
  have hc := card_sdiff_add_card_eq_card Q.marks_sub
  have finish (h : T.card + fee e ≤ cap) : Γ.card + 1 ≤ cap := by
    change (Γ \ T).card + T.card = Γ.card at hc
    omega
  by_cases hn : Q.parents.Nonempty
  · have hprod := Q.projected hn
    have hred : Reduced f := ⟨hprod.positive,hprod.primitive,hprod.separable⟩
    have hroots (γ : K) (hγ : γ ∈ T) : atMark f (M.label γ) (F.scalar γ)=0 := by
      obtain ⟨q,hq,hm⟩ := Q.covers γ hγ
      have hz := RingHom.mem_ker.mp (hm (hprod.vanishes q hq))
      simpa only [coe_eval₂RingHom,eval₂_C,atMark] using hz
    have ht : ∀ q ∈ Q.parents, BankPass rows KoalaH2429Banks.terminal.shape q := Q.terminal_pass
    obtain ⟨D,crt,hjet⟩ := KoalaH2429TerminalB.transport_terminal (by simp [hw])
      C.poles C.crt Q.parents ht
    obtain ⟨he,ha⟩ := KoalaH2429TerminalA.paid_degrees M crt Q.geometric hjet hprod
    change axisDegree f 0 + axisDegree f 1 ≤ KoalaH2429TerminalA.paidCap f.natDegree at ha
    by_cases hard : e=16 ∨ e=17
    · by_cases hi : Irreducible f
      · let := seedGCD
        have hirr : Irreducible (f.map toSeed) :=
          (hred.2.1.irreducible_iff_irreducible_map_fraction_map (K := SeedField)).mp hi
        have hseed : SeedBound f 474 := KoalaH2429TerminalA.hard_seed_bound hard ha
        refine KoalaTwoTerminal.count_of_two_traces F (cap := cap) (reserve := 1) (aBill := fee e)
          (bBill := KoalaH2429TerminalB.prefixFee) (v := 474) hred.2.1 hred.1 hirr hseed Q.marks_sub
          hp hroots ?_ (by decide)
        rcases KoalaH2429TerminalB.retained M F hw hshift with h | hB
        · exact Or.inl h
        obtain ⟨B⟩ := hB
        obtain ⟨hB,hseedB⟩ := KoalaH2429TerminalB.resultant_inputs B
        have he17 : e ≤ 17 := by rcases hard with h | h <;> omega
        obtain ⟨hdegree,hbill⟩ := KoalaH2429TerminalB.resultant_budget hpay he17 hB
        refine Or.inr ⟨B.equation,B.marks,hseedB,
          (Nat.le_add_right _ 1).trans B.prefix_paid,KoalaH2429TerminalB.retained_roots B,
          ?_,hdegree,hbill⟩
        intro hdiv
        let v := if e=16 then 380 else 369
        have hv : axisDegree f 0+axisDegree f 1 ≤ v := by
          rcases hard with h | h
          · simpa only [v,h,if_true] using KoalaH2429TerminalB.axis16_of_dvd B h hdiv
          · simpa only [v,h,show ¬(17 : ℕ)=16 by decide,if_false] using
              KoalaH2429TerminalB.axis17_of_dvd B h hdiv
        have hsmall : v ≤ 448 := by dsimp [v]; split <;> decide
        exact count_on_axes hw hshift hred he Q.marks_sub hroots hv (hsmall.trans (by decide))
          (fun _ => hsmall) (fun _ _ h => H2429TerminalBudget.from_wider_bank hard h)
      · apply finish
        have hbound := H2429TerminalCount.reducible_roots M F hw hshift hred hi Q.marks_sub hroots
          hard (fun h => by simpa only [h,KoalaH2429TerminalA.paidCap16] using ha)
          (fun h => by simpa only [h,KoalaH2429TerminalA.paidCap17] using ha)
        exact (Nat.add_le_add_right hbound _).trans (by
          rw [Nat.add_comm]
          exact H2429TerminalBudget.from_split hard)
    · apply finish
      exact count_on_axes hw hshift hred he Q.marks_sub hroots ha
        (KoalaH2429TerminalA.paidCap_le hred.1 he) H2429TerminalBudget.compress_width
        (fun _ _ h => H2429TerminalBudget.ordinary hred.1 he
          (fun h => hard (Or.inl h)) (fun h => hard (Or.inr h)) h)
  · have hT : T = ∅ := not_nonempty_iff_eq_empty.mp fun ⟨γ,hγ⟩ => by
      obtain ⟨q,hq,_⟩ := Q.covers γ hγ
      exact hn ⟨q,hq⟩
    exact finish (by rw [hT,card_empty,zero_add]; exact hpay.trans (by decide))

end
end H2429NormalCount
