import ProximityPrize.SubmissionLower.Koala6844VirtualShortCenteredAdaptive
import ProximityPrize.SubmissionLower.Koala6831MovingSchedule


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped Classical
open RCN095 RCN130 RCN266 LocatorBatchProductRoute LocatorLowQuotient
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (SourceNumbers)
open Koala6844Normalization
open Koala6844Receipts (geometricGate geometricGate_mono)
open Koala6831MovingAdaptive (aggregateFlag aggregateFlag_mono aggregateFlag_pos exhaust_finset_stage)

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1900000

variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}

structure CenteredAdaptiveSource (data : CenteredVirtualData x nodes σ w a errors excess)
    (p : ℕ) where
  D : ℕ → ℕ
  wQ : ℕ
  m : ℕ
  L : ℕ
  B : ℕ
  U : ℕ
  q : ℕ
  gap : ℕ
  multiplicity_pos : 0 < m
  slope_lt_char : B < p
  middle_le_total : U ≤ L
  lift_le_middle : q ≤ U
  cutoff_le_agreement : D 0 ≤ m*a
  middle_le_cutoff : U ≤ (D 0+B-1)/w
  evaluated_degree : w+data.d0.natDegree ≤ affineDegree data.A0+wQ
  dimension : gap ≤ Fintype.card (NormalizedIndex D w wQ L B 0 U q) -
    nodes.card * normalizedRankBudget D w m L B 0 U q

variable {data : CenteredVirtualData x nodes σ w a errors excess} {p : ℕ}

def CenteredAdaptiveSource.numbers (s : CenteredAdaptiveSource data p) : SourceNumbers :=
  ⟨s.L+s.q,s.U,s.B,s.gap⟩

def AdaptiveSourceFits (s : SourceNumbers) (f : FlagDegree) : Prop :=
  f.all ≤ s.slopeCap ∧ middle f ≤ s.middleCap ∧ total f ≤ s.totalCap

private theorem fits_of_smaller {s : SourceNumbers} {f g : FlagDegree}
    (h : Below f g) (fit : AdaptiveSourceFits s g) : AdaptiveSourceFits s f :=
  ⟨h.1.trans fit.1, h.2.1.trans fit.2.1, h.2.2.trans fit.2.2⟩

private theorem fuel_pos_of_fits (s : SourceNumbers) (f : FlagDegree)
    (hpos : 0 < f.all) (fit : AdaptiveSourceFits s f) : 0 < s.fuel f := by
  have hmid : 0 < middle f := by unfold middle; omega
  have htot : 0 < total f := by unfold total; omega
  unfold LocatorPhase6800Oracle.SourceNumbers.fuel
  apply Nat.lt_of_succ_le
  apply le_min
  · exact (Nat.le_div_iff_mul_le htot).2 (by simpa only [Nat.one_mul] using fit.2.2)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hmid).2 (by simpa only [Nat.one_mul] using fit.2.1)
    · exact (Nat.le_div_iff_mul_le hpos).2 (by simpa only [Nat.one_mul] using fit.1)

structure CenteredAdaptivePass (s : CenteredAdaptiveSource data p) (δ : ℕ)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H)) where
  residue : Finset (RegularIndex H)
  subset_incoming : residue ⊆ A
  stopped : residue = ∅ ∨ ¬ geometricGate (2*δ) s.numbers (aggregateFlag H residue)
  started : (A \ residue).Nonempty → geometricGate (2*δ) s.numbers (aggregateFlag H A)
  partners : ∀ F ∈ A \ residue, ∃ Q : MvPolynomial (Fin 4) K,
    Q ∈ nestedCoefficientBox K (s.m*a+s.q*affineDegree data.A0) w (s.L+s.q+s.B) s.U s.B ∧
    (∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g Q = 0) ∧
    IsRelPrime F.val Q

theorem exists_centered_adaptive_pass [CharP K p]
    (s : CenteredAdaptiveSource data p) (δ : ℕ) (hw : 0 < w) (ha : 0 < a)
    (hδ : 0 < δ) (hWidth : data.d0.natDegree + affineDegree data.A0 ≤ δ)
    (hLead : ∀ i ∈ nodes, (data.A0 1).eval (x i) ≠ 0)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (hField : A.card < ENat.card K) (fit : AdaptiveSourceFits s.numbers (aggregateFlag H A))
    (hTrans : ∀ F ∈ A, ¬ F.val ∣ (centeredFlow data).flow F.val) :
    Nonempty (CenteredAdaptivePass s δ H A) := by
  classical
  let active (S : Finset (RegularIndex H)) := geometricGate (2*δ) s.numbers (aggregateFlag H S)
  let covered (F : RegularIndex H) := ∃ Q : MvPolynomial (Fin 4) K,
    Q ∈ nestedCoefficientBox K (s.m*a+s.q*affineDegree data.A0) w (s.L+s.q+s.B) s.U s.B ∧
    (∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g Q = 0) ∧
    IsRelPrime F.val Q
  by_cases hstarted : active A
  · obtain ⟨U, hsub, hstop, hpays⟩ := exhaust_finset_stage A active covered
      (fun S hSA hS hactive => by
        have hFieldS : S.card < ENat.card K := by
          exact (by exact_mod_cast Finset.card_le_card hSA : (S.card : ENat) ≤ A.card).trans_lt hField
        have hpos := aggregateFlag_pos H hS
        have hfuel := fuel_pos_of_fits s.numbers _ hpos (fits_of_smaller (aggregateFlag_mono H hSA) fit)
        obtain ⟨U, hU, Q, hQ, hzero, hrel⟩ := exists_centered_adaptive_partner data
          s.D s.wQ δ s.m s.L s.B s.U s.q s.gap hw ha hδ s.multiplicity_pos s.slope_lt_char
          s.middle_le_total s.lift_le_middle s.cutoff_le_agreement s.middle_le_cutoff
          hWidth s.evaluated_degree hLead s.dimension H S hS hFieldS hpos hfuel hactive
          (fun F hFS => hTrans F (hSA hFS))
        exact ⟨U, hU, fun f hf => ⟨Q, hQ, hzero, hrel f hf⟩⟩)
    exact ⟨⟨U, hsub, hstop, fun _ => hstarted, hpays⟩⟩
  · refine ⟨⟨A, (fun _ h => h), Or.inr hstarted, ?_, ?_⟩⟩
    · intro h
      obtain ⟨F, hF⟩ := h
      exact ((Finset.mem_sdiff.mp hF).2 (Finset.mem_sdiff.mp hF).1).elim
    · intro F hF
      exact ((Finset.mem_sdiff.mp hF).2 (Finset.mem_sdiff.mp hF).1).elim

private theorem gate_fails_on_subset (s : CenteredAdaptiveSource data p) (δ : ℕ)
    (H : MvPolynomial (Fin 4) K) {A B : Finset (RegularIndex H)}
    (hsub : B ⊆ A) (hnonempty : B.Nonempty)
    (hstopped : A = ∅ ∨ ¬ geometricGate (2*δ) s.numbers (aggregateFlag H A)) :
    ¬ geometricGate (2*δ) s.numbers (aggregateFlag H B) := by
  intro gate
  rcases hstopped with hempty | hfail
  · simpa only [hempty, Finset.not_nonempty_empty] using hnonempty.mono hsub
  · exact hfail (geometricGate_mono (2*δ) s.numbers (aggregateFlag_mono H hsub)
      (aggregateFlag_pos H hnonempty) gate)

theorem exists_two_centered_adaptive_passes [CharP K p]
    (first second : CenteredAdaptiveSource data p) (δ : ℕ) (hw : 0 < w) (ha : 0 < a)
    (hδ : 0 < δ) (hWidth : data.d0.natDegree + affineDegree data.A0 ≤ δ)
    (hLead : ∀ i ∈ nodes, (data.A0 1).eval (x i) ≠ 0)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (hField : A.card < ENat.card K)
    (fit₁ : AdaptiveSourceFits first.numbers (aggregateFlag H A))
    (fit₂ : AdaptiveSourceFits second.numbers (aggregateFlag H A))
    (hTrans : ∀ F ∈ A, ¬ F.val ∣ (centeredFlow data).flow F.val) :
    ∃ pass₁ : CenteredAdaptivePass first δ H A,
    ∃ pass₂ : CenteredAdaptivePass second δ H pass₁.residue,
      pass₂.residue = ∅ ∨
        ¬ geometricGate (2*δ) first.numbers (aggregateFlag H pass₂.residue) ∧
        ¬ geometricGate (2*δ) second.numbers (aggregateFlag H pass₂.residue) := by
  obtain ⟨pass₁⟩ := exists_centered_adaptive_pass first δ hw ha hδ hWidth hLead H A hField fit₁ hTrans
  have hField₁ : pass₁.residue.card < ENat.card K := by
    exact (by exact_mod_cast Finset.card_le_card pass₁.subset_incoming :
      (pass₁.residue.card : ENat) ≤ A.card).trans_lt hField
  obtain ⟨pass₂⟩ := exists_centered_adaptive_pass second δ hw ha hδ hWidth hLead H pass₁.residue hField₁
    (fits_of_smaller (aggregateFlag_mono H pass₁.subset_incoming) fit₂)
    (fun F hF => hTrans F (pass₁.subset_incoming hF))
  refine ⟨pass₁, pass₂, ?_⟩
  rcases pass₂.stopped with hempty | hfail
  · exact Or.inl hempty
  · by_cases empty : pass₂.residue = ∅
    · exact Or.inl empty
    · exact Or.inr ⟨gate_fails_on_subset first δ H pass₂.subset_incoming
        (Finset.nonempty_iff_ne_empty.mpr empty) pass₁.stopped, hfail⟩

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort

