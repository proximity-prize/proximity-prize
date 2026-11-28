import ProximityPrize.SubmissionLower.Z6969Pack0836
import ProximityPrize.SubmissionLower.Z6969Pack0837
import ProximityPrize.SubmissionLower.FrontBranch3
import ProximityPrize.SubmissionLower.Z6969Pack0832
import ProximityPrize.SubmissionLower.Z6969Pack0850
import ProximityPrize.SubmissionLower.Z6969Pack0851
import ProximityPrize.SubmissionLower.Z6969Pack0795
import ProximityPrize.SubmissionLower.Z6969Pack0838
import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import ArkLib.Data.MvPolynomial.WeightedDegree.Products
import ArkLib.Data.MvPolynomial.WeightAtMost
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969GateTilted
section Z6969Source2413
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969GateComparison
section Merged_Low6969GateComparison

set_option autoImplicit false
set_option Elab.async false

namespace Low6969Gate
noncomputable section

open K1_13 (Row)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (sectionIdeal cylinder oldEmbedding OfDim LengthAt)
open K1_13_6_2_4_4 (cylinder_regular cylinder_dimension cylinder_minimal cylinder_length)

theorem pair_regular₂ {F G : GeoJets} (hrel : IsRelPrime F G) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {F}) G) := by
  apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
  intro x hx
  obtain ⟨D, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (hrel.dvd_of_dvd_mul_left hx))

theorem cylinder_comparison₂ (f Q : Row 4) (hF : toGeneric f ≠ 0)
    (hrel : IsRelPrime (toGeneric f) (toGeneric Q)) :
    let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
    let J := sectionIdeal A (oldEmbedding (toGeneric Q))
    IsLeftRegular (Ideal.Quotient.mk A (oldEmbedding (toGeneric Q))) ∧
    ∀ P : Ideal GeoJets, ∀ h : (intersectionIdeal f Q).IsMinimalPrime P,
      OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P),
          cycleLength (intersectionIdeal f Q) P h.isPrime ≤ LengthAt J (cylinder P) hc.isPrime := by
  let F : Ideal GeoJets := Ideal.span {toGeneric f}
  have hA : sectionIdeal ⊥ (oldEmbedding (toGeneric f)) = cylinder F := by
    simp [sectionIdeal, cylinder, F, Ideal.map_span]
  have hJ : sectionIdeal (sectionIdeal ⊥ (oldEmbedding (toGeneric f))) (oldEmbedding (toGeneric Q)) =
      cylinder (intersectionIdeal f Q) := by
    rw [hA, intersectionIdeal, Ideal.span_insert]
    simp [sectionIdeal, cylinder, F, Ideal.map_sup, Ideal.map_span]
  have hreg := pair_regular₂ hrel
  dsimp only
  constructor
  · exact (congrArg (fun I : Ideal GeoJets5 =>
      IsLeftRegular (Ideal.Quotient.mk I (oldEmbedding (toGeneric Q)))) hA).mpr
      (cylinder_regular hreg)
  · intro P hP
    refine ⟨cylinder_dimension (K1_13_6_1_4.pair_dimension hF hrel hP), ?_⟩
    apply (congrArg (fun I : Ideal GeoJets5 => ∃ hc : I.IsMinimalPrime (cylinder P),
      cycleLength (intersectionIdeal f Q) P hP.isPrime ≤ LengthAt I (cylinder P) hc.isPrime) hJ).mpr
    exact ⟨cylinder_minimal hP, (cylinder_length (intersectionIdeal f Q) P hP.isPrime).le⟩

end
end Low6969Gate

end Merged_Low6969GateComparison

-- merged module Low6969GateTilted
section Merged_Low6969GateTilted

set_option autoImplicit false
set_option Elab.async false

namespace Low6969Gate
noncomputable section

open Low48BentCycle (Family mixedDegree properCut cycleComparison divisorBound diagonalExponents
  rawFamily capFamily capSum ambient_cap integral)
open Low48BentLattice (Cap Allowed Chamber latticePoints)
open Low48BentSupport (graph lifted)
open Low6969Prices (SmallFactor taylorLength)
open Low6969GeometryCut_2 (Branch)
open Low6969GeometryCut_2_3 (graphLift chart_index_eq graphLift_same_chart
  membership_same_chart graphLift_comap member_proper_on_graph)
open K1_13 (Row Shape shape)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5)
open K1_13_6_2_4 (Exponent Component DimLE OfDim LengthAt ambient_dim cylinder cylinder_injective
  dim_le_after_section oldEmbedding pointIdeal sectionIdeal)
open K1_13_6_2_4_1 (positiveDiagonal)
open Low6969ActiveCycle (Section Doubled Slice Chart)
open MvPolynomial
open scoped BigOperators Pointwise
open Low6969ActiveCycle (square_support bound_marks)
open Low48BentCycle (slots ambient_list)

def caps₂ (p q₁ q₂ : Shape) : Fin 5 → Cap :=
  ![(q₁, 0), (q₂, 0), graph p, lifted p (taylorLength - 4), lifted p (taylorLength - 3)]

theorem caps₂_chamber {p q₁ q₂ : Shape} (hb : p.j ≤ p.b) (ht : 1 ≤ p.t) (hj : 3 * p.t + 3 ≤ p.j)
    (hq₁ : Chamber (q₁, 0)) (hq₂ : Chamber (q₂, 0)) :
    ∀ i, Chamber (caps₂ p q₁ q₂ i) := by
  intro i
  fin_cases i
  · exact hq₁
  · exact hq₂
  · exact Low48BentSupport.graph_chamber ht hj
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 4)
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 3)

private theorem last_allowed₂ {p q₁ q₂ : Shape}
    (v : Fin 5) : Allowed (caps₂ p q₁ q₂ 4) (Finsupp.single v 1) := by
  let k := taylorLength - 3
  have hb' : 1 ≤ 1 + k * (p.b - 1) := by omega
  have hj' : 4 ≤ 4 + k * (p.j - 2) := by omega
  have ht' : 2 ≤ 2 + k * p.t := by omega
  have hd' : 1 ≤ min (1 + k) ((2 + k * p.t) / 2) := by omega
  fin_cases v <;> simp [caps₂, lifted, Allowed, ← show k = taylorLength - 3 from rfl] <;> omega

theorem ordinary_doubled₂ {p q₁ q₂ : Shape} :
    Doubled (rawFamily (caps₂ p q₁ q₂)) (capFamily (caps₂ p q₁ q₂)) where
  zero_mem i := by simp [rawFamily, Allowed]
  pair_mem _ _ ha _ hb := Low48BentSupport.raw_add ha hb
  last_coordinate := last_allowed₂

def tiltedPair (p q₁ q₂ : Shape) : ℕ :=
  Low6969Prices.ambientMix [(q₁, 0), (q₂, 0), Low6969Prices.bentGraph p,
    Low6969Prices.bentLift (taylorLength - 4) p, Low6969Prices.bentLift (taylorLength - 3) p]


private def integr₂ (a : Cap) : ℚ := integral a

private def signed₂ (p q₁ q₂ : Shape) : ℤ :=
  ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
    integral (Low48BentLattice.Sum J (caps₂ p q₁ q₂))

private theorem base_signed₂ (p q₁ q₂ : Shape) :
    tiltedPair p q₁ q₂ = (signed₂ p q₁ q₂).toNat := by
  change Low48Price.ambientMix (slots.map (caps₂ p q₁ q₂)) = _
  exact ambient_list (caps₂ p q₁ q₂)

private theorem base_normalize₂ (p q₁ q₂ : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr₂ (capSum (caps₂ p q₁ q₂) (positiveDiagonal J))) = (signed₂ p q₁ q₂ : ℚ) := by
  have H := Low48BentPolarization.remove_baseline (caps₂ p q₁ q₂)
  change _ = _ at H
  rw [show (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      integr₂ (capSum (caps₂ p q₁ q₂) (positiveDiagonal J))) =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr₂ (Low48BentLattice.Sum J (caps₂ p q₁ q₂)) from H]
  unfold signed₂
  push_cast
  rfl

private theorem ordinary_coeff₂ (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (latticePoints a)).toRingHom ⊥)).coeff 5 = integr₂ a / 60 := by
  rw [Low48BentVolume.ambient_coeff a ha]
  unfold integr₂ integral
  rw [Low48BentVolume.cast_price_integral a]

theorem ordinary_budget₂ {p q₁ q₂ : Shape} (h : ∀ i, Chamber (caps₂ p q₁ q₂ i)) :
    (60 * 32 : ℚ) * mixedDegree (capFamily (caps₂ p q₁ q₂)) ⊥ Finset.univ ≤
      (tiltedPair p q₁ q₂ : ℚ) := by
  rw [mul_assoc, ambient_cap (caps₂ p q₁ q₂) h (fun a => integr₂ a / 60) ordinary_coeff₂]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize₂, base_signed₂]
  exact_mod_cast (show signed₂ p q₁ q₂ ≤ ((signed₂ p q₁ q₂).toNat : ℤ) by omega)

theorem chart₂ {f Q : Row 4} {l : ℕ} (q₁ q₂ : Shape) (ht : 1 ≤ (shape f).t)
    (b : Branch f Q l) :
    Chart (rawFamily (caps₂ (shape f).chamber q₁ q₂)) b := by
  have h := Low6969ActiveCycle.ordinary_chart ht b
  exact h

private theorem initial_bound₂ {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (G₁ G₂ : Row 4) (weight : Ideal GeoJets → ℕ) (hG₁ : G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (hbox₁ : Section R 0 (oldEmbedding (toGeneric G₁)))
    (hbox₂ : Section R 1 (oldEmbedding (toGeneric G₂))) (S : Finset (Ideal GeoJets))
    (hS : ∀ P ∈ S, ∃ h : (intersectionIdeal G₁ G₂).IsMinimalPrime P,
      (weight P : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) P h.isPrime) :
    (∀ P ∈ S, (cylinder P).IsPrime ∧ OfDim (cylinder P) 3) ∧
      (∑ P ∈ S, (weight P : ℚ) * mixedDegree B (cylinder P) {2, 3, 4}) ≤
        mixedDegree B ⊥ Finset.univ := by
  classical
  let A := sectionIdeal ⊥ (oldEmbedding (toGeneric G₁))
  let J := sectionIdeal A (oldEmbedding (toGeneric G₂))
  have hF : toGeneric G₁ ≠ 0 := K1_13_6_3_6.toGeneric_ne_zero hG₁
  obtain ⟨hregQ, hAlgebra⟩ := cylinder_comparison₂ G₁ G₂ hF hrel
  have hregf : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets5)
      (oldEmbedding (toGeneric G₁))) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne hF
  have hAdim : DimLE A 4 := dim_le_after_section hregf ambient_dim
  have hJdim : DimLE J 3 := dim_le_after_section hregQ hAdim
  have hgeom (P : Ideal GeoJets) (hP : P ∈ S) :
      (cylinder P).IsPrime ∧ OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P), (weight P : ℕ∞) ≤ LengthAt J (cylinder P) hc.isPrime := by
    obtain ⟨h, hw⟩ := hS P hP
    obtain ⟨hd, hc, hl⟩ := hAlgebra P h
    exact ⟨hc.isPrime, hd, hc, hw.trans hl⟩
  refine ⟨fun P hP => ⟨(hgeom P hP).1, (hgeom P hP).2.1⟩, ?_⟩
  have hs := cycleComparison B hB.double_zero hB.double_coordinates J {2, 3, 4} hJdim S cylinder weight
    cylinder_injective.injOn (fun P hP => (hgeom P hP).2.2)
  have hcutQ := properCut B hB.double_zero A {2, 3, 4} 1 (by decide) hAdim
    (oldEmbedding (toGeneric G₂)) (fun m hm => hB.raw_mem (hbox₂ m hm)) (square_support hB hbox₂) hregQ
  have hcutf := properCut B hB.double_zero ⊥ {1, 2, 3, 4} 0 (by decide) ambient_dim
    (oldEmbedding (toGeneric G₁)) (fun m hm => hB.raw_mem (hbox₁ m hm)) (square_support hB hbox₁) hregf
  have hall : (insert (0 : Fin 5) {1, 2, 3, 4} : Finset (Fin 5)) = Finset.univ := by decide
  rw [hall] at hcutf
  exact hs.trans (hcutQ.trans hcutf)

theorem bound_with_cut₂ {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (f Q G₁ G₂ : Row 4) (l : ℕ) (hG₁ : G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (weight : Ideal GeoJets → ℕ)
    (hbox₁ : Section R 0 (oldEmbedding (toGeneric G₁)))
    (hbox₂ : Section R 1 (oldEmbedding (toGeneric G₂)))
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hF : ∀ b ∈ F, Section R 2 b.graph ∧
      (∃ E, Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member)) ∧
      (∀ p ∈ T b, b.Contains p) ∧ Slice R b (T b))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal G₁ G₂).IsMinimalPrime b.surface,
      (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) b.surface h.isPrime) :
    (∑ b ∈ F, (weight b.surface : ℚ) * ((b.weight : ℚ) * (T b).card)) ≤
      mixedDegree B ⊥ Finset.univ := by
  classical
  have hgraph := @Low6969GeometryCut_2_3_1.proof f Q l
  have hmember := @Low6969GeometryCut_2_3_2.proof f Q l
  let S := F.image Branch.surface
  let fibre (P : Ideal GeoJets) := F.filter fun b => b.surface = P
  let charge (b : Branch f Q l) : ℚ := (b.weight : ℚ) * (T b).card
  obtain ⟨hZ, hsumZ⟩ := initial_bound₂ hB G₁ G₂ weight hG₁ hrel hbox₁ hbox₂ S (by
    intro P hP
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    exact hcut b hb)
  have hfibre (P : Ideal GeoJets) (hP : P ∈ S) :
      (∑ c ∈ fibre P, charge c) ≤ mixedDegree B (cylinder P) {2, 3, 4} := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    let G := graphLift b b.surface
    let C (c : Branch f Q l) := graphLift c c.curve
    obtain ⟨hboxG, ⟨E, hboxE, hE⟩, _, _⟩ := hF b hb
    obtain ⟨hZprime, hZdim⟩ := hZ _ hP
    obtain ⟨hproperG, hG, hGdim⟩ := hgraph b hZprime hZdim
    have hC (c : Branch f Q l) (hcs : c.surface = b.surface) :
        Component G E (C c) c.weight ∧ OfDim (C c) 1 := by
      have hr := chart_index_eq hcs
      have hsame : graphLift c c.surface = G :=
        (graphLift_same_chart hr c.surface).trans (congrArg (graphLift b) hcs)
      have hE' := (membership_same_chart hr E).mpr hE
      rw [← hsame]
      exact hmember c E (hsame.symm ▸ hG.minimal.isPrime) (hsame.symm ▸ hGdim) hE'
    have hproperE := member_proper_on_graph b hE
    have inj : Set.InjOn C (fibre b.surface : Set (Branch f Q l)) := by
      intro c hc d hd he
      have hcs := (Finset.mem_filter.mp hc).2
      have hds := (Finset.mem_filter.mp hd).2
      apply Branch.eq_of_surface_curve (hcs.trans hds.symm)
      rw [← graphLift_comap c c.curve c.divisor.isPrime c.regularCurve,
        ← graphLift_comap d d.curve d.divisor.isPrime d.regularCurve]
      exact congrArg (Ideal.comap oldEmbedding) he
    have hmarks : (∑ c ∈ fibre b.surface, charge c) ≤
        ∑ c ∈ fibre b.surface, (c.weight : ℚ) * mixedDegree B (C c) {4} := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨hcF, hcs⟩ := Finset.mem_filter.mp hc
      obtain ⟨_, _, hon, hslice⟩ := hF c hcF
      obtain ⟨hcomp, hdim⟩ := hC c hcs
      exact mul_le_mul_of_nonneg_left
        (bound_marks hB c (T c) hon hslice hcomp.minimal.isPrime hdim)
        (Nat.cast_nonneg _)
    have hEbound := divisorBound B hB.double_zero hB.double_coordinates G {4} 3 hG.minimal.isPrime
      (by decide) hGdim E (fun m hm => hB.raw_mem (hboxE m hm)) (square_support hB hboxE) hproperE
      (fibre b.surface) C Branch.weight inj (fun c hc => (hC c (Finset.mem_filter.mp hc).2).1)
    have hGbound := divisorBound B hB.double_zero hB.double_coordinates (cylinder b.surface) {3, 4} 2
      hZprime (by decide) hZdim
      b.graph (fun m hm => hB.raw_mem (hboxG m hm)) (square_support hB hboxG) hproperG {G} id
      (fun _ => 1) (fun _ _ _ _ h => h) (by
        intro P hP
        obtain rfl := Finset.mem_singleton.mp hP
        exact hG)
    have hGbound' : mixedDegree B G {3, 4} ≤ mixedDegree B (cylinder b.surface) {2, 3, 4} := by
      simpa only [Finset.sum_singleton, Nat.cast_one, one_mul, id_eq] using hGbound
    exact hmarks.trans (hEbound.trans hGbound')
  have hcharge :
      (∑ c ∈ F, (weight c.surface : ℚ) * charge c) ≤
        ∑ P ∈ S, (weight P : ℚ) * mixedDegree B (cylinder P) {2, 3, 4} := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Branch.surface)
      (fun b hb => Finset.mem_image_of_mem Branch.surface hb)
      (fun b => (weight b.surface : ℚ) * charge b)]
    apply Finset.sum_le_sum
    intro P hP
    change (∑ c ∈ fibre P, (weight c.surface : ℚ) * charge c) ≤ _
    calc
      _ = ∑ c ∈ fibre P, (weight P : ℚ) * charge c := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [(Finset.mem_filter.mp hc).2]
      _ = (weight P : ℚ) * ∑ c ∈ fibre P, charge c := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfibre P hP) (Nat.cast_nonneg _)
  exact hcharge.trans hsumZ

end
end Low6969Gate

end Merged_Low6969GateTilted
end Z6969Source2413

-- Source: ProximityPrize.SubmissionLower.Low6969GateShape
section Z6969Source2414
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969GateCoprime
section Merged_Low6969GateCoprime

set_option autoImplicit false

namespace Low6969GateCoprime

variable {K R : Type*} [Field K] [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Algebra K R]

def divisible (V : Submodule K R) (p : R) : Submodule K V where
  carrier := {v | p ∣ (v : R)}
  add_mem' := fun {a b} ha hb => by
    exact (dvd_add ha hb : p ∣ (a : R) + (b : R))
  zero_mem' := dvd_zero p
  smul_mem' := fun c v hv => by
    show p ∣ ((c • v : V) : R)
    rw [Submodule.coe_smul, Algebra.smul_def]
    exact Dvd.dvd.mul_left hv _


theorem exists_relPrime_member [Infinite K] (V : Submodule K R)
    (hV : ∀ p : R, Irreducible p → ∃ v ∈ V, ¬ p ∣ v) {G₁ : R} (hG₁ : G₁ ≠ 0) :
    ∃ G₂ ∈ V, IsRelPrime G₁ G₂ := by
  classical
  let S : Finset R := (UniqueFactorizationMonoid.factors G₁).toFinset
  have hcover : ∃ v : V, ∀ p ∈ S, ¬ p ∣ (v : R) := by
    by_contra hcon
    push_neg at hcon
    have hall : ⋃ i : S, ((divisible V (i : R) : Submodule K V) : Set V) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro v
      obtain ⟨p, hp, hpv⟩ := hcon v
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hpv⟩
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hall
    have hirr : Irreducible (i : R) :=
      UniqueFactorizationMonoid.irreducible_of_factor _ (Multiset.mem_toFinset.mp i.2)
    obtain ⟨v, hvV, hv⟩ := hV _ hirr
    have hmem : (⟨v, hvV⟩ : V) ∈ divisible V (i : R) := by rw [hi]; trivial
    exact hv hmem
  obtain ⟨v, hv⟩ := hcover
  refine ⟨v, v.2, ?_⟩
  intro d hd1 hd2
  by_contra hnu
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hG₁ (zero_dvd_iff.mp hd1)
  obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hd0
  obtain ⟨q, hq, hpq⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hG₁ hp (hpd.trans hd1)
  have hqS : q ∈ S := Multiset.mem_toFinset.mpr hq
  apply hv q hqS
  exact (hpq.symm.dvd).trans (hpd.trans hd2)

end Low6969GateCoprime

end Merged_Low6969GateCoprime

-- merged module Low6969GateGcd
section Merged_Low6969GateGcd

set_option autoImplicit false

namespace Low6969GateGcd

variable {K R : Type*} [Field K] [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Algebra K R]

theorem gcd_split (V : Submodule K R) (hV : V ≠ ⊥) :
    ∃ g : R, g ≠ 0 ∧ ∃ V' : Submodule K R, V' = V.comap (LinearMap.mulLeft K g) ∧
      (∀ v ∈ V, g ∣ v) ∧ (∀ p : R, Irreducible p → ∃ w ∈ V', ¬ p ∣ w) := by
  classical
  obtain ⟨v0, hv0, hv0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  let Q : Set R := {q | ∃ g : R, (∀ v ∈ V, g ∣ v) ∧ v0 = g * q}
  have hne : Q.Nonempty := ⟨v0, 1, fun v _ => one_dvd v, by simp⟩
  obtain ⟨q0, ⟨g0, hg0, hq0⟩, hmin⟩ := (wellFounded_dvdNotUnit (α := R)).has_min Q hne
  have hg0ne : g0 ≠ 0 := by
    rintro rfl
    exact hv0ne (by simpa using hq0)
  refine ⟨g0, hg0ne, V.comap (LinearMap.mulLeft K g0), rfl, hg0, ?_⟩
  intro p hp
  by_contra hcon
  push_neg at hcon
  have hall : ∀ v ∈ V, p * g0 ∣ v := by
    intro v hv
    obtain ⟨w, hw⟩ := hg0 v hv
    have : w ∈ V.comap (LinearMap.mulLeft K g0) := by
      show g0 * w ∈ V
      rw [← hw]; exact hv
    obtain ⟨u, hu⟩ := hcon w this
    exact ⟨u, by rw [hw, hu]; ring⟩
  have hq0mem : q0 ∈ V.comap (LinearMap.mulLeft K g0) := by
    show g0 * q0 ∈ V
    rw [← hq0]; exact hv0
  obtain ⟨q1, hq1⟩ := hcon q0 hq0mem
  have hq1Q : q1 ∈ Q := ⟨p * g0, hall, by rw [hq0, hq1]; ring⟩
  have hq0ne : q0 ≠ 0 := by
    rintro rfl
    exact hv0ne (by simpa using hq0)
  have hq1ne : q1 ≠ 0 := by
    rintro rfl
    exact hq0ne (by simpa using hq1)
  exact hmin q1 hq1Q ⟨hq1ne, p, hp.not_isUnit, by rw [hq1]; ring⟩


theorem two_general [Infinite K] (V' : Submodule K R)
    (hV : ∀ p : R, Irreducible p → ∃ v ∈ V', ¬ p ∣ v) {T : R} (hT : T ≠ 0) (hTn : ¬ IsUnit T) :
    ∃ G₁ ∈ V', ∃ G₂ ∈ V', G₁ ≠ 0 ∧ IsRelPrime T G₁ ∧ IsRelPrime G₁ G₂ := by
  obtain ⟨G₁, h₁, hrel₁⟩ := Low6969GateCoprime.exists_relPrime_member V' hV hT
  have hG : G₁ ≠ 0 := by
    rintro rfl
    exact hTn (hrel₁ (dvd_refl T) (dvd_zero T))
  obtain ⟨G₂, h₂, hrel₂⟩ := Low6969GateCoprime.exists_relPrime_member V' hV hG
  exact ⟨G₁, h₁, G₂, h₂, hG, hrel₁, hrel₂⟩

theorem finrank_split (V : Submodule K R) (g : R) (hg : g ≠ 0) (hdiv : ∀ v ∈ V, g ∣ v) :
    Module.finrank K (V.comap (LinearMap.mulLeft K g)) = Module.finrank K V := by
  have hinj : Function.Injective (LinearMap.mulLeft K g) := mul_right_injective₀ hg
  have hle : V ≤ LinearMap.range (LinearMap.mulLeft K g) := by
    intro v hv
    obtain ⟨w, hw⟩ := hdiv v hv
    exact ⟨w, hw.symm⟩
  have hmap : (V.comap (LinearMap.mulLeft K g)).map (LinearMap.mulLeft K g) = V := by
    rw [Submodule.map_comap_eq]; exact inf_eq_right.mpr hle
  have h := LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (V.comap (LinearMap.mulLeft K g)))
  rw [hmap] at h
  exact h

theorem split_power_nonunit (f g : R) (hf : ¬ IsUnit f) (hg : g ≠ 0) :
    ∃ a : ℕ, ∃ h : R, g = f ^ a * h ∧ ¬ f ∣ h := by
  obtain ⟨n, c, hnd, hc⟩ := WfDvdMonoid.max_power_factor' hg hf
  exact ⟨n, c, hc, hnd⟩

end Low6969GateGcd

end Merged_Low6969GateGcd

-- merged module Low6969GateShape
section Merged_Low6969GateShape

set_option autoImplicit false

namespace Low6969GateShape

open MvPolynomial

variable {F : Type*} [Field F]

def wv : Fin 3 → (Fin 4 → ℕ) := ![fun _ => 1, Fin.val, Pi.single 3 1]

noncomputable def shp (i : Fin 3) (P : MvPolynomial (Fin 4) F) : ℕ := P.weightedTotalDegree (wv i)

theorem shp_mul {P Q : MvPolynomial (Fin 4) F} (hP : P ≠ 0) (hQ : Q ≠ 0) (i : Fin 3) :
    shp i (P * Q) = shp i P + shp i Q :=
  weightedTotalDegree_mul _ _ _ hP hQ

def freeSet («Y» : Fin 3 → ℕ) : Set (Fin 4 →₀ ℕ) := {m | ∀ i, m.weight (wv i) ≤ «Y» i}

theorem freeSet_finite («Y» : Fin 3 → ℕ) : (freeSet «Y»).Finite := by
  apply (Finsupp.finite_of_degree_le («Y» 0)).subset
  intro m hm
  have h := hm 0
  have hd : m.degree = m.weight (wv 0) := by
    rw [Finsupp.degree_eq_weight_one]; rfl
  simpa [hd] using h

noncomputable def free («Y» : Fin 3 → ℕ) : ℕ := (freeSet_finite «Y»).toFinset.card

theorem mem_restrict_iff {P : MvPolynomial (Fin 4) F} {«Y» : Fin 3 → ℕ} :
    P ∈ restrictSupport F (freeSet «Y») ↔ ∀ i, shp i P ≤ «Y» i := by
  rw [mem_restrictSupport_iff]
  constructor
  · intro h i
    unfold shp weightedTotalDegree
    exact Finset.sup_le fun m hm => h hm i
  · intro h m hm i
    exact (Finset.le_sup (f := fun m => m.weight (wv i)) hm).trans (h i)

theorem finrank_restrict («Y» : Fin 3 → ℕ) :
    Module.finrank F (restrictSupport F (freeSet «Y»)) = free «Y» := by
  have h : (↑(freeSet_finite «Y»).toFinset : Set (Fin 4 →₀ ℕ)) = freeSet «Y» := Set.Finite.coe_toFinset _
  rw [← h, finrank_restrictSupport_finset]; rfl

theorem dim_le_free [Infinite F] (V : Submodule F (MvPolynomial (Fin 4) F)) (g : MvPolynomial (Fin 4) F)
    (hg : g ≠ 0) (hdiv : ∀ v ∈ V, g ∣ v) (B : Fin 3 → ℕ) (hB : ∀ v ∈ V, ∀ i, shp i v ≤ B i) :
    Module.finrank F V ≤ free (fun i => B i - shp i g) := by
  classical
  have hsplit : Module.finrank F (V.comap (LinearMap.mulLeft F g)) = Module.finrank F V :=
    Low6969GateGcd.finrank_split V g hg hdiv
  rw [← hsplit, ← finrank_restrict (F := F) (fun i => B i - shp i g)]
  haveI : Module.Finite F (restrictSupport F (freeSet (fun i => B i - shp i g))) :=
    restrictSupport_finite (freeSet_finite _)
  apply Submodule.finrank_mono
  intro w hw
  rw [mem_restrict_iff]
  intro i
  by_cases h0 : w = 0
  · subst h0; simp [shp, MvPolynomial.weightedTotalDegree]
  · have hmem : g * w ∈ V := hw
    have h1 := hB _ hmem i
    rw [shp_mul hg h0] at h1
    omega

theorem wt_apply (m : Fin 4 →₀ ℕ) : m.weight (wv 0) = m 0 + m 1 + m 2 + m 3 ∧
    m.weight (wv 1) = m 1 + 2 * m 2 + 3 * m 3 ∧ m.weight (wv 2) = m 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wv, Fin.sum_univ_four, Pi.single_apply]
  omega

theorem shp_valid {P : MvPolynomial (Fin 4) F} (hP : P ≠ 0) :
    shp 2 P ≤ shp 0 P ∧ 3 * shp 2 P ≤ shp 1 P ∧ shp 1 P ≤ 2 * shp 0 P + shp 2 P := by
  have hne : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  have le : ∀ i, ∀ m ∈ P.support, m.weight (wv i) ≤ shp i P := fun i m hm =>
    Finset.le_sup (f := fun m => m.weight (wv i)) hm
  obtain ⟨m2, hm2, e2⟩ := Finset.exists_mem_eq_sup P.support hne (fun m => m.weight (wv 2))
  obtain ⟨m1, hm1, e1⟩ := Finset.exists_mem_eq_sup P.support hne (fun m => m.weight (wv 1))
  have s2 : shp 2 P = m2.weight (wv 2) := e2
  have s1 : shp 1 P = m1.weight (wv 1) := e1
  have a2 := wt_apply m2
  have a1 := wt_apply m1
  have b0 := le 0 m2 hm2
  have b1 := le 1 m2 hm2
  have c0 := le 0 m1 hm1
  have c2 := le 2 m1 hm1
  rw [a2.1] at b0
  rw [a2.2.1] at b1
  rw [a1.1] at c0
  rw [a1.2.2] at c2
  rw [a2.2.2] at s2
  rw [a1.2.1] at s1
  refine ⟨by omega, by omega, by omega⟩

end Low6969GateShape

end Merged_Low6969GateShape
end Z6969Source2414

-- Source: ProximityPrize.SubmissionLower.Low6969GateTally
section Z6969Source2415
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969GateOrdinary
section Merged_Low6969GateOrdinary

set_option autoImplicit false
set_option Elab.async false

namespace Low6969Gate
noncomputable section

open Low6969Prices (SmallFactor primaryBox taylorLength)
open Low6969GeometryCut (membershipTest)
open Low6969GeometryCut_2 (Branch Slice4 budget4)
open K1_13 (Row Shape shape InBox chart mixed32 volume32 difference)
open K1_13_6 (GeoJets GeoField toGeneric divisorIdeal cycleLength intersectionIdeal separant)
open K1_13_6_2 (JetPoint Box4)
open K1_13_6_2_3 (ChamberBox dimension capCoeff polarize mixedDegree localWeight pointIdeal
  chart_box generic_box regular_cut cut_dimension dimension_bot pair_regular intersection_eq
  surface_dimension weight_cast weight_pos point_injective point_prime point_degree point_proper_section)
open scoped BigOperators
open Low6969GeometryCut_2_2 (surface_slice_sum ambient_degree)

theorem ordinary_bound_with_cut₂ (h1 : K1_13_6_2_3.c1)
    (h2 : K1_13_6_2_3.c2) (h3 : K1_13_6_2_3.c3)
    (f Q G₁ G₂ : Row 4) (l : ℕ) (hf : SmallFactor f) (hG₁ : G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (q₁ q₂ : Shape) (hq₁ : ChamberBox q₁) (hq₂ : ChamberBox q₂)
    (hQ₁ : InBox (shape G₁) q₁) (hQ₂ : InBox (shape G₂) q₂)
    (weight : Ideal GeoJets → ℕ)
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hT : ∀ b ∈ F, Box4 (chart (taylorLength + 1) (shape f).chamber) b.member ∧
      (∀ p ∈ T b, b.Contains p) ∧ Slice4 b (T b))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal G₁ G₂).IsMinimalPrime b.surface,
       (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) b.surface h.isPrime) :
    (∑ b ∈ F, (weight b.surface : ℚ) * ((b.weight * (T b).card : ℕ) : ℚ)) ≤
      (mixed32 q₁ q₂ (chart (taylorLength + 1) (shape f).chamber)
        (chart (taylorLength + 2) (shape f).chamber) : ℚ) / 32 := by
  classical
  let p := (shape f).chamber
  let r := chart (taylorLength + 1) p
  let s := chart (taylorLength + 2) p
  have hr : ChamberBox r := chart_box _ _ (Nat.zero_lt_succ _)
  have hs : ChamberBox s := chart_box _ _ (Nat.zero_lt_succ _)
  have hboxes : ∀ q ∈ [r,s], ChamberBox q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact hq.elim (fun h => h ▸ hr) (fun h => h ▸ hs)
  let J := intersectionIdeal G₁ G₂
  let H : Ideal GeoJets := Ideal.span {toGeneric G₁}
  have hf0 : toGeneric G₁ ≠ 0 := K1_13_6_3_6.toGeneric_ne_zero hG₁
  have hregF : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets) (toGeneric G₁)) :=
    regular_cut (by infer_instance) (by simpa using hf0)
  have hregQ := pair_regular G₁ G₂ hrel
  have hH : dimension H ≤ 3 := by
    simpa [H, dimension_bot] using cut_dimension hregF
  have hJ : dimension J ≤ 2 := by
    rw [show J = H ⊔ Ideal.span {toGeneric G₂} from intersection_eq G₁ G₂]
    have hdrop : dimension (H ⊔ Ideal.span {toGeneric G₂}) ≤ dimension H - 1 := cut_dimension hregQ
    exact hdrop.trans (by omega)
  let surfaces := F.image Branch.surface
  let fiber (P : Ideal GeoJets) := F.filter (fun b => b.surface = P)
  let cost (b : Branch f Q l) : ℚ := ((b.weight * (T b).card : ℕ) : ℚ)
  have hsurface (P : Ideal GeoJets) (hP : P ∈ surfaces) :
      J.IsMinimalPrime P ∧ weight P ≤ localWeight J P ∧
      (∑ b ∈ fiber P, cost b) ≤ mixedDegree P [r,s] := by
    obtain ⟨ref, href, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hmin, hlen⟩ := hcut ref href
    have hl : (weight ref.surface : ℕ∞) ≤ (localWeight J ref.surface : ℕ∞) := by
      rw [weight_cast hmin]
      exact hlen
    refine ⟨hmin, ENat.natCast_le_natCast.mp hl, ?_⟩
    exact surface_slice_sum h2 h3 ref (surface_dimension hf0 hrel hmin) _ T
      (fun _ hb => (Finset.mem_filter.mp hb).2) (hT ref href).1
      (fun b hb => (hT b (Finset.mem_filter.mp hb).1).2)
  change (∑ b ∈ F, (weight b.surface : ℚ) * cost b) ≤ (mixed32 q₁ q₂ r s : ℚ) / 32
  calc
    _ = ∑ P ∈ surfaces, (weight P : ℚ) * ∑ b ∈ fiber P, cost b := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := Branch.surface)
        (fun b hb => Finset.mem_image_of_mem Branch.surface hb)
        (fun b => (weight b.surface : ℚ) * cost b)]
      apply Finset.sum_congr rfl
      intro P _
      change (∑ b ∈ fiber P, (weight b.surface : ℚ) * cost b) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      simp [(Finset.mem_filter.mp hb).2]
    _ ≤ ∑ P ∈ surfaces, (localWeight J P : ℚ) * mixedDegree P [r,s] := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨_, hl, hsum⟩ := hsurface P hP
      have hnonneg : 0 ≤ ∑ b ∈ fiber P, cost b := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hnonneg).trans
        (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
    _ ≤ mixedDegree J [r,s] := h3 J [r,s] hboxes (by simpa using hJ) surfaces
      (fun P hP => (hsurface P hP).1)
    _ ≤ mixedDegree H [q₂,r,s] := by
      rw [show J = H ⊔ Ideal.span {toGeneric G₂} from intersection_eq G₁ G₂]
      exact h2 H q₂ [r,s] hq₂ hboxes (by simpa using hH) _ (generic_box hQ₂) hregQ
    _ ≤ mixedDegree (⊥ : Ideal GeoJets) [q₁,q₂,r,s] := by
      rw [show H = (⊥ : Ideal GeoJets) ⊔ Ideal.span {toGeneric G₁} by simp [H]]
      apply h2 _ q₁ [q₂,r,s] hq₁ _ (by simp) _ _ hregF
      · intro u hu
        exact (List.mem_cons.mp hu).elim (fun h => h ▸ hq₂) (hboxes u)
      · exact generic_box hQ₁
    _ ≤ _ := ambient_degree h1 hq₁ hq₂ hr hs

end
end Low6969Gate

end Merged_Low6969GateOrdinary

-- merged module Low6969GateTally
section Merged_Low6969GateTally

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Low6969Gate
noncomputable section

open P3 (K)
open K1_13 (Row Shape shape InBox chart mixed32)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo)
open Low6969GeometryCut (CutInput)
open Low6969GeometryCut_2 (Branch)
open Low6969Prices (taylorLength)
open Low6969SharedTally (Data)
open scoped Polynomial BigOperators

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

theorem tilted_pair_tally (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (G₁ G₂ : Row 4) (hG₁ : G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (weight : Ideal GeoJets → ℕ) (htilt : Low6969Prices.tiltedFits (shape f))
    (q₁ q₂ : Shape) (hQ₁ : InBox (shape G₁) q₁) (hQ₂ : InBox (shape G₂) q₂)
    (hq₁ : Low48BentLattice.Chamber (q₁, 0)) (hq₂ : Low48BentLattice.Chamber (q₂, 0))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal G₁ G₂).IsMinimalPrime b.surface,
      (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) b.surface h.isPrime) :
    1920 * (∑ b ∈ F, weight b.surface * (b.weight * (D.points b).card)) ≤
      tiltedPair (shape f).chamber q₁ q₂ := by
  let p := (shape f).chamber
  have ht : 1 ≤ p.t := input.small.2.1
  have hfamily := caps₂_chamber (K1_13_7_1.shape_chamber f).1 ht htilt.1 hq₁ hq₂
  let R := Low48BentCycle.rawFamily (caps₂ p q₁ q₂)
  let B := Low48BentCycle.capFamily (caps₂ p q₁ q₂)
  have h := bound_with_cut₂ (R := R) (B := B) ordinary_doubled₂ f Q G₁ G₂ l hG₁ hrel weight
    (Low48BentCycle.old_section hQ₁) (Low48BentCycle.old_section hQ₂)
    F D.points (fun b hb => D.bent input (chart₂ q₁ q₂ ht) b (hF hb)) hcut
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℚ) ≤ 60 * 32)).trans
    (ordinary_budget₂ hfamily)
  norm_num only [show (60 : ℚ) * 32 = 1920 by norm_num] at hh
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, ← Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc] using hh

theorem ordinary_pair_tally (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (G₁ G₂ : Row 4) (hG₁ : G₁ ≠ 0)
    (hrel : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (q₁ q₂ : Shape) (hq₁ : K1_13_6_2_3.ChamberBox q₁) (hq₂ : K1_13_6_2_3.ChamberBox q₂)
    (hQ₁ : InBox (shape G₁) q₁) (hQ₂ : InBox (shape G₂) q₂)
    (weight : Ideal GeoJets → ℕ)
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal G₁ G₂).IsMinimalPrime b.surface,
      (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal G₁ G₂) b.surface h.isPrime) :
    32 * (∑ b ∈ F, weight b.surface * (b.weight * (D.points b).card)) ≤
      mixed32 q₁ q₂ (chart (taylorLength + 1) (shape f).chamber)
        (chart (taylorLength + 2) (shape f).chamber) := by
  have h := ordinary_bound_with_cut₂ K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
    f Q G₁ G₂ l input.small hG₁ hrel q₁ q₂ hq₁ hq₂ hQ₁ hQ₂ weight F D.points
    (fun b hb => D.four input b (hF hb)) hcut
  have h' := (le_div_iff₀ (by norm_num : (0 : ℚ) < 32)).mp h
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, ← Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc] using h'


end
end Low6969Gate

end Merged_Low6969GateTally
end Z6969Source2415

-- Source: ProximityPrize.SubmissionLower.Low6969GateAssembly
section Z6969Source2416
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969GateCombine
section Merged_Low6969GateCombine

set_option autoImplicit false

namespace Low6969GateCombine

open Finset

theorem class_zero (r e m g : ℕ) (he : 1 ≤ e) (hO : r ≤ m + g) :
    ((r : ℚ)) ^ 2 ≤ (g : ℚ) ^ 2 + (m : ℚ) * g + (r : ℚ) * e * m := by
  have he' : (1 : ℚ) ≤ e := by exact_mod_cast he
  have hO' : (r : ℚ) ≤ m + g := by exact_mod_cast hO
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg _
  have hg : (0 : ℚ) ≤ g := Nat.cast_nonneg _
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg _
  by_cases hmr : (r : ℚ) ≤ m
  · nlinarith [mul_nonneg hr (mul_nonneg hm (sub_nonneg.mpr he')), mul_nonneg hg hg, mul_nonneg hm hg]
  · push_neg at hmr
    have h1 : (r : ℚ) - m ≤ g := by linarith
    nlinarith [mul_nonneg hr (mul_nonneg hm (sub_nonneg.mpr he')), mul_nonneg hg hg, mul_nonneg hm hg,
      mul_nonneg (sub_nonneg.mpr h1) (add_nonneg hm hg)]

variable {ι : Type*}

theorem combine (s : Finset ι) (μ e m g : ι → ℕ) (ρ c v : ℚ)
    (Tgg Tmg Tem Teg Tee : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hv : 0 ≤ v)
    (hclass : ∀ i ∈ s, ρ ^ 2 ≤ (1 - c) * ((g i : ℚ) * g i) + (m i : ℚ) * g i + ρ * ((e i : ℚ) * m i) +
      c * ρ * ((e i : ℚ) * g i) + v * ρ ^ 2 * ((e i : ℚ) * ((e i : ℚ) - 1)))
    (hρ : 0 ≤ ρ)
    (hgg : ∑ i ∈ s, (μ i : ℚ) * ((g i : ℚ) * g i) ≤ Tgg)
    (hmg : ∑ i ∈ s, (μ i : ℚ) * ((m i : ℚ) * g i) ≤ Tmg)
    (hem : ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * m i) ≤ Tem)
    (heg : ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * g i) ≤ Teg)
    (hee : ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * ((e i : ℚ) - 1)) ≤ Tee) :
    ρ ^ 2 * (∑ i ∈ s, (μ i : ℚ)) ≤
      (1 - c) * Tgg + Tmg + ρ * Tem + c * ρ * Teg + v * ρ ^ 2 * Tee := by
  have hsum : ∑ i ∈ s, (μ i : ℚ) * ρ ^ 2 ≤
      ∑ i ∈ s, (μ i : ℚ) * ((1 - c) * ((g i : ℚ) * g i) + (m i : ℚ) * g i + ρ * ((e i : ℚ) * m i) +
        c * ρ * ((e i : ℚ) * g i) + v * ρ ^ 2 * ((e i : ℚ) * ((e i : ℚ) - 1))) :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hclass i hi) (Nat.cast_nonneg _)
  have hexp : ∑ i ∈ s, (μ i : ℚ) * ((1 - c) * ((g i : ℚ) * g i) + (m i : ℚ) * g i +
        ρ * ((e i : ℚ) * m i) + c * ρ * ((e i : ℚ) * g i) +
        v * ρ ^ 2 * ((e i : ℚ) * ((e i : ℚ) - 1))) =
      (1 - c) * ∑ i ∈ s, (μ i : ℚ) * ((g i : ℚ) * g i) + ∑ i ∈ s, (μ i : ℚ) * ((m i : ℚ) * g i) +
        ρ * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * m i) + c * ρ * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * g i) +
        v * ρ ^ 2 * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * ((e i : ℚ) - 1)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hl : ∑ i ∈ s, (μ i : ℚ) * ρ ^ 2 = ρ ^ 2 * ∑ i ∈ s, (μ i : ℚ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hl, hexp] at hsum
  have h1 : (1 - c) * ∑ i ∈ s, (μ i : ℚ) * ((g i : ℚ) * g i) ≤ (1 - c) * Tgg :=
    mul_le_mul_of_nonneg_left hgg (by linarith)
  have h3 : ρ * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * m i) ≤ ρ * Tem := mul_le_mul_of_nonneg_left hem hρ
  have h4 : c * ρ * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * g i) ≤ c * ρ * Teg :=
    mul_le_mul_of_nonneg_left heg (mul_nonneg hc0 hρ)
  have h5 : v * ρ ^ 2 * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * ((e i : ℚ) - 1)) ≤ v * ρ ^ 2 * Tee :=
    mul_le_mul_of_nonneg_left hee (mul_nonneg hv (sq_nonneg ρ))
  linarith


end Low6969GateCombine

end Merged_Low6969GateCombine

-- merged module Low6969GateAssembly
section Merged_Low6969GateAssembly

set_option autoImplicit false

namespace Low6969GateAssembly

open Finset

theorem sum_by_surface {β ι : Type*} [DecidableEq ι] (F : Finset β) (surf : β → ι) (c : β → ℕ)
    (w : ι → ℚ) :
    ∑ b ∈ F, w (surf b) * (c b : ℚ) =
      ∑ P ∈ F.image surf, w P * ((∑ b ∈ F.filter (fun b => surf b = P), c b : ℕ) : ℚ) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := surf) (fun b hb => Finset.mem_image_of_mem surf hb)]
  apply Finset.sum_congr rfl
  intro P _
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [(Finset.mem_filter.mp hb).2]

theorem conv {β ι : Type*} [DecidableEq ι] (F : Finset β) (surf : β → ι) (c : β → ℕ) (w : ι → ℚ) {T : ℚ}
    (h : ∑ b ∈ F, w (surf b) * (c b : ℚ) ≤ T) :
    ∑ P ∈ F.image surf, ((∑ b ∈ F.filter (fun b => surf b = P), c b : ℕ) : ℚ) * w P ≤ T := by
  rw [sum_by_surface] at h
  simpa only [mul_comm] using h

theorem combine_branches {β ι : Type*} [DecidableEq ι] (F : Finset β) (surf : β → ι) (c : β → ℕ)
    (e m g : ι → ℕ) (ρ cc v : ℚ) (Tgg Tmg Tem Teg Tee : ℚ) (hc0 : 0 ≤ cc) (hc1 : cc ≤ 1) (hv : 0 ≤ v)
    (hρ : 0 ≤ ρ)
    (hclass : ∀ b ∈ F, ρ ^ 2 ≤ (1 - cc) * ((g (surf b) : ℚ) * g (surf b)) + (m (surf b) : ℚ) * g (surf b) +
      ρ * ((e (surf b) : ℚ) * m (surf b)) + cc * ρ * ((e (surf b) : ℚ) * g (surf b)) +
      v * ρ ^ 2 * ((e (surf b) : ℚ) * ((e (surf b) : ℚ) - 1)))
    (hgg : ∑ b ∈ F, ((g (surf b) : ℚ) * g (surf b)) * (c b : ℚ) ≤ Tgg)
    (hmg : ∑ b ∈ F, ((m (surf b) : ℚ) * g (surf b)) * (c b : ℚ) ≤ Tmg)
    (hem : ∑ b ∈ F, ((e (surf b) : ℚ) * m (surf b)) * (c b : ℚ) ≤ Tem)
    (heg : ∑ b ∈ F, ((e (surf b) : ℚ) * g (surf b)) * (c b : ℚ) ≤ Teg)
    (hee : ∑ b ∈ F, ((e (surf b) : ℚ) * ((e (surf b) : ℚ) - 1)) * (c b : ℚ) ≤ Tee) :
    ρ ^ 2 * (∑ b ∈ F, (c b : ℚ)) ≤
      (1 - cc) * Tgg + Tmg + ρ * Tem + cc * ρ * Teg + v * ρ ^ 2 * Tee := by
  classical
  let S := F.image surf
  let μ : ι → ℕ := fun P => ∑ b ∈ F.filter (fun b => surf b = P), c b
  have hsum1 : ∑ b ∈ F, (c b : ℚ) = ∑ P ∈ S, (μ P : ℚ) := by
    have := sum_by_surface F surf c (fun _ => 1)
    simp only [one_mul] at this
    rw [this]
  have h := Low6969GateCombine.combine S μ e m g ρ cc v Tgg Tmg Tem Teg Tee hc0 hc1 hv
    (fun P hP => by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
      exact hclass b hb)
    hρ
    (conv F surf c (fun P => (g P : ℚ) * g P) hgg)
    (conv F surf c (fun P => (m P : ℚ) * g P) hmg)
    (conv F surf c (fun P => (e P : ℚ) * m P) hem)
    (conv F surf c (fun P => (e P : ℚ) * g P) heg)
    (conv F surf c (fun P => (e P : ℚ) * ((e P : ℚ) - 1)) hee)
  rw [hsum1]
  exact h

end Low6969GateAssembly

end Merged_Low6969GateAssembly
end Z6969Source2416

