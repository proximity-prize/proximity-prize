import ProximityPrize.SubmissionLower.Low53At2389Order
import ProximityPrize.SubmissionLower.PrimaryTaperFamily

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace Low53At2389Primary
noncomputable section
open K1_13 (Geom Row Shape shape InBox Contact embed)
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P3 (I K node)
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open TaperColumns PrimaryTaper
open TaperBudget (cap)
open scoped BigOperators

open private local_range_finite
  from ProximityPrize.SubmissionLower.PrimaryTaperFamily
open private map_independent_family from ProximityPrize.SubmissionLower.PortLowBase

abbrev LocalRankBound : Prop :=
  ∀ x y : Geom, Module.finrank Geom
    (LinearMap.range ((localConstraintAt 3000 x y).domRestrict (TaperNormalize.space cap))) ≤ 343765691757628

private theorem node_rank (hLoc : LocalRankBound) {A D : ℕ} (x y : Geom) :
    Module.finrank Geom (LinearMap.range (nodeMap (A:=A) (D:=D) x y)) ≤ 343765691757628 := by
  letI := local_range_finite x y
  apply (Submodule.finrank_mono ?_).trans (hLoc x y)
  rintro _ ⟨Q, rfl⟩
  exact ⟨⟨Q.1, fun e he => (Q.2 he).1⟩, rfl⟩

theorem word_rank_of_local (hLoc : LocalRankBound) (A D : ℕ) (hD : 3<D) (w : I → K) :
    Module.finrank Geom (LinearMap.range (wordMap A D w)) ≤ 262144 * 343765691757628 := by
  letI : Fact (3<D) := ⟨hD⟩
  let nmap (i : I) := nodeMap (A:=A) (D:=D) (embed (node i)) (embed (w i))
  let B (i : I) := LinearMap.range (nmap i)
  let f : Source A D →ₗ[Geom] (∀ i, B i) := LinearMap.pi fun i => (nmap i).rangeRestrict
  let g : (∀ i, B i) →ₗ[Geom] (I → Local) :=
    LinearMap.pi fun i => (B i).subtype.comp (LinearMap.proj i)
  have hw : wordMap A D w = g.comp f := rfl
  rw [hw]
  calc
    _ ≤ Module.finrank Geom (LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range f g)
    _ ≤ Module.finrank Geom (∀ i, B i) := g.finrank_range_le
    _ = ∑ i, Module.finrank Geom (B i) := Module.finrank_pi_fintype Geom
    _ ≤ ∑ _ : I, 343765691757628 := Finset.sum_le_sum fun i _ => node_rank hLoc _ _
    _ = _ := by simp [I, FrobeniusLocator.Native.I, ProximityPrize.Benchmark.IRSProfile.Index]

def sourceRank (A D : ℕ) : ℕ := compactCount A D - 262144 * 343765691757628

theorem primary_family_of_local (hLoc : LocalRankBound) (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4012 ≤ 3000*A)
    (w : I → K) {n : ℕ} (hn : n ≤ sourceRank A D) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE D (e i) (3000*A-1) ∧
        JetsBounded (e i) ∧ Contact w (e i) := by
  letI : Fact (3<D) := ⟨hD⟩
  let lift : LinearMap.ker (wordMap A D w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp ((Source A D).subtype.comp (LinearMap.ker (wordMap A D w)).subtype)
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  have hdim := (wordMap A D w).finrank_range_add_finrank_ker
  have hcols := (finrank_source A D hD).trans (exact_columns A D hA hD hBudget)
  have hr := word_rank_of_local hLoc A D hD w
  have hker : n ≤ Module.finrank Geom (LinearMap.ker (wordMap A D w)) := by
    unfold sourceRank at hn
    omega
  let admissible (P : Row 4) :=
    InBox (shape P) primaryBox ∧ TrueWeightLE D P (3000*A-1) ∧ JetsBounded P ∧ Contact w P
  refine map_independent_family (V := LinearMap.ker (wordMap A D w)) (W := Row 4)
    (n := n) lift hinj admissible ?_ hker
  intro Q
  obtain ⟨hbox,hweight,hJets⟩ := row_bounds Q.1
  exact ⟨hbox,hweight,hJets,contact_of_word_kernel w Q.1 (LinearMap.mem_ker.mp Q.2)⟩



theorem primary_rank (hLoc : LocalRankBound) (w : I → K) : Low53At2389Order.PrimaryRank w :=
  primary_family_of_local hLoc 179896 133460 (by decide) (by decide)
    (by decide) w (n := Low53At2389Order.sourceRank) (by decide)

#print axioms primary_rank
end
end Low53At2389Primary
