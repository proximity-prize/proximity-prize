import ProximityPrize.SubmissionLower.PrimaryTaper

set_option Elab.async false
set_option maxRecDepth 12000

namespace PuncturedCompactPrimary

noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13 (Geom Row shape InBox embed)
open K1_13_2 (Local toRow)
open P3 (I K node)
open TaperColumns (Source)
open ProximityPrize.Benchmark
open scoped BigOperators
open private map_independent_family pointContact from ProximityPrize.SubmissionLower.PortLowBase
open private node_rank from ProximityPrize.SubmissionLower.PrimaryTaperFamily

def kept (deleted : Finset I) : Finset I := Finset.univ \ deleted

theorem kept_card (deleted : Finset I) : (kept deleted).card = 262144 - deleted.card := by
  rw [kept, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, IRSProfile.card_index]

def Contact (w : I → K) (deleted : Finset I) (P : Row 4) : Prop :=
  ∀ i ∉ deleted, ∀ S : Geom[X], S.eval (embed (node i)) = embed (w i) →
    (Polynomial.X - Polynomial.C (embed (node i))) ^ 3000 ∣ K1_13.atJet P S

def wordMap (A D : ℕ) (w : I → K) (deleted : Finset I) :
    Source A D →ₗ[Geom] (kept deleted → Local) :=
  LinearMap.pi fun i => PrimaryTaper.nodeMap (embed (node i.val)) (embed (w i.val))

theorem word_rank (A D : ℕ) (hD : 3 < D) (w : I → K) (deleted : Finset I) :
    Module.finrank Geom (LinearMap.range (wordMap A D w deleted)) ≤
      (262144 - deleted.card) * 343903138965692 := by
  letI : Fact (3 < D) := ⟨hD⟩
  apply (LinearMap.finrank_range_pi_le_sum _).trans
  calc
    _ ≤ ∑ _ : kept deleted, (343903138965692 : ℕ) :=
      Finset.sum_le_sum fun i _ => node_rank TaperBudget.tapered_rank _ _
    _ = _ := by simp [kept_card]

private theorem contact_of_word_kernel {A D : ℕ} (w : I → K) (deleted : Finset I)
    (Q : Source A D) (hQ : wordMap A D w deleted Q = 0) :
    Contact w deleted (toRow Q.1) := by
  intro i hi S hS
  rw [K1_13_2.atJet_toRow]
  let j : kept deleted := ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hlocal : SatisfiesLocalConstraints (d := 3) 3000 (embed (node i)) (embed (w i)) Q.1 :=
    congrFun hQ j
  with_reducible exact pointContact (embed (node i)) (embed (w i)) Q.1 S hS hlocal

def sourceRank (A D R : ℕ) : ℕ :=
  TaperColumns.compactCount A D - (262144 - R) * 343903138965692

theorem primary_family (A D R : ℕ) (hA : 0 < A) (hD : 3 < D)
    (hBudget : D * 4012 ≤ 3000 * A) (w : I → K) (deleted : Finset I)
    (hdeleted : R ≤ deleted.card) {n : ℕ} (hn : n ≤ sourceRank A D R) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) PrimaryTaper.primaryBox ∧
        PrimaryTaper.TrueWeightLE D (e i) (3000 * A - 1) ∧
        PrimaryTaper.JetsBounded (e i) ∧ Contact w deleted (e i) := by
  letI : Fact (3 < D) := ⟨hD⟩
  let W := wordMap A D w deleted
  let lift : LinearMap.ker W →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp ((Source A D).subtype.comp (LinearMap.ker W).subtype)
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  have hdim := W.finrank_range_add_finrank_ker
  have hcols := (TaperColumns.finrank_source A D hD).trans
    (TaperColumns.exact_columns A D hA hD hBudget)
  have hr : Module.finrank Geom (LinearMap.range W) ≤ (262144 - R) * 343903138965692 :=
    (word_rank A D hD w deleted).trans
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hdeleted _))
  have hker : n ≤ Module.finrank Geom (LinearMap.ker W) := by
    unfold sourceRank at hn
    omega
  let admissible (P : Row 4) :=
    InBox (shape P) PrimaryTaper.primaryBox ∧ PrimaryTaper.TrueWeightLE D P (3000 * A - 1) ∧
      PrimaryTaper.JetsBounded P ∧ Contact w deleted P
  refine map_independent_family (V := LinearMap.ker W) (W := Row 4)
    (n := n) lift hinj admissible ?_ hker
  intro Q
  obtain ⟨hbox, hweight, hjets⟩ := PrimaryTaper.row_bounds Q.1
  exact ⟨hbox, hweight, hjets, contact_of_word_kernel w deleted Q.1 (LinearMap.mem_ker.mp Q.2)⟩

#print axioms primary_family

end
end PuncturedCompactPrimary
