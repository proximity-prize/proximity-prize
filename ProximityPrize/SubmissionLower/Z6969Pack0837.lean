import ProximityPrize.SubmissionLower.Z6970H2307PriceDefs
import ProximityPrize.SubmissionLower.Z6969Pack0836
import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.Low48BentCycle
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCycleCaps
import ProximityPrize.SubmissionLower.Low49ActiveLattice
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import Mathlib.Algebra.MvPolynomial.Coeff

set_option Elab.async false
set_option maxRecDepth 50000

namespace Height2307CutEnvelope
noncomputable section
open Polynomial
open K1_13 (Row Geom Shape shape InBox extend atJet OnFactor OrderAt)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength genericCoeffs)
open K1_13_6_1 (anchorBox DerivativeWeight)
open K1_13_6_1_2 (VanishesTo multiOrder hassePartial map_hassePartial
  cycleLength_pos cycleLength_ge_order pair_height hasse_inBox hasse_atJet_eq_zero)
open K1_13_7_1 (GeoFits toGeneric_fits)
open Low6969Prices (primaryBox)
open scoped Polynomial

def SurfaceCut (f Q : Row 4) (surface : Ideal GeoJets) (P : Row 4) : Prop :=
  ∃ (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) (v w : ℕ),
    0 < v ∧ cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) ∧
    (w = 0 ∨ ∃ r, 0 < r ∧ r < (shape f).t ∧ DerivativeWeight f surface r w) ∧
    toGeneric P ∉ surface ∧
    InBox (shape P) (primaryBox.plus ((anchorBox f).scale (4*v + 2*w)))
theorem lowHasse {f Q : Row 4} {l : ℕ} {surface : Ideal GeoJets}
    (hZ : (intersectionIdeal f Q).IsMinimalPrime surface)
    (hf : Irreducible f) (hproper : ¬ f ∣ Q) (hbox : InBox (shape Q) primaryBox) :
    ∃ v : ℕ, 0 < v ∧ v ≤ (shape f).b * primaryBox.b ∧
      cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) ∧
      (v < l → ∃ P : Row 4, toGeneric P ∉ surface ∧ InBox (shape P) primaryBox ∧
        ∀ S, OrderAt Q S l → atJet P S = 0) := by
  let _ : surface.IsPrime := hZ.isPrime
  have hf0 : toGeneric f ≠ 0 := fun h =>
    hf.ne_zero (K1_13_7_1.toGeneric_injective (h.trans (map_zero _).symm))
  have hrel := K1_13_7_1.proper_generic f Q hf hproper
  have hheight : surface.height = 2 := pair_height hf0 hrel hZ
  have hdeg (P : Row 4) : (toGeneric P).totalDegree ≤ (shape P).b :=
    Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  have hup : cycleLength (intersectionIdeal f Q) surface hZ.isPrime ≤
      (↑((shape f).b * primaryBox.b) : ℕ∞) :=
    (K1_13_6_1_2_1.proof _ _ _ hZ hf0 hrel).trans
      (by exact_mod_cast Nat.mul_le_mul (hdeg f) ((hdeg Q).trans hbox.1))
  have hnotop : cycleLength (intersectionIdeal f Q) surface hZ.isPrime ≠ ⊤ :=
    ne_of_lt (hup.trans_lt (ENat.natCast_lt_top _))
  let v := (cycleLength (intersectionIdeal f Q) surface hZ.isPrime).toNat
  have hv : cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) :=
    (ENat.natCast_toNat hnotop).symm
  have hpos := cycleLength_pos hZ.isPrime hZ.le
  rw [hv] at hpos hup
  refine ⟨v, by exact_mod_cast hpos, by exact_mod_cast hup, hv, ?_⟩
  intro hl
  have hcut : ∃ a : Fin 4 →₀ ℕ, multiOrder a < v + 1 ∧
      toGeneric (hassePartial a Q) ∉ surface := by
    by_contra! hn
    have horder : VanishesTo surface (toGeneric Q) (v + 1) := by
      apply K1_13_6_1_2_2.proof _ surface (v + 1) hheight
      intro a ha
      change hassePartial a (MvPolynomial.map genericCoeffs Q) ∈ surface
      rw [← map_hassePartial genericCoeffs a Q]
      exact hn a ha
    have hfp : toGeneric f ∈ surface := hZ.le (Ideal.subset_span (by simp))
    have hge := cycleLength_ge_order hheight hfp horder
    rw [hv] at hge
    exact (by omega : ¬ v + 1 ≤ v) (by exact_mod_cast hge)
  obtain ⟨a, ha, hproper'⟩ := hcut
  exact ⟨hassePartial a Q, hproper', hasse_inBox a hbox,
    fun S hS => hasse_atJet_eq_zero (by omega) hS⟩
theorem box_charge {f P : Row 4} {k j : ℕ}
    (hP : InBox (shape P) ((anchorBox f).scale k)) (hkj : k ≤ j) :
    InBox (shape P) (primaryBox.plus ((anchorBox f).scale j)) := by
  rcases hP with ⟨h1, h2, h3⟩
  exact ⟨h1.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _)),
    h2.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _)),
    h3.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _))⟩
theorem box_cutter_charge {f P : Row 4} {k j : ℕ}
    (hP : InBox (shape P) (primaryBox.plus ((anchorBox f).scale k))) (hkj : k ≤ j) :
    InBox (shape P) (primaryBox.plus ((anchorBox f).scale j)) := by
  rcases hP with ⟨h1, h2, h3⟩
  exact ⟨h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _),
    h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _),
    h3.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _)⟩
private theorem charge_coord (q p v w : ℕ) (hv : 0 < v) :
    q + (4*v + 2*w) * p ≤ v*(q + 4*p) + (2*w)*p := by
  calc
    _ = q + v*(4*p) + (2*w)*p := by ring
    _ ≤ v*q + v*(4*p) + (2*w)*p := by
      have hq : q ≤ v*q := Nat.le_mul_of_pos_left q hv
      exact Nat.add_le_add_right (Nat.add_le_add_right hq _) _
    _ = _ := by ring
theorem supported_charge {f P : Row 4} {v w : ℕ} (hv : 0 < v)
    (h : InBox (shape P) (primaryBox.plus ((anchorBox f).scale (4*v + 2*w)))) :
    GeoFits (toGeneric P)
      (((primaryBox.plus ((anchorBox f).scale 4)).scale v).plus ((anchorBox f).scale (2*w))) :=
  toGeneric_fits ⟨h.1.trans (charge_coord _ _ _ _ hv),
    h.2.1.trans (charge_coord _ _ _ _ hv), h.2.2.trans (charge_coord _ _ _ _ hv)⟩

open K1_13_6_3 (JetIdeal dimension cycleWeight)
open MvPolynomial
open scoped BigOperators

structure CutCycle (f Q : Row 4) : Prop where
  local_bound : ∀ surface (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    dimension surface = 2 ∧ (1 : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime ∧
    cycleLength (intersectionIdeal f Q) surface hz.isPrime ≤ ((shape f).b * primaryBox.b : ℕ)
  weighted_degree :
    ∑ surface ∈ (intersectionIdeal f Q).minimalPrimesFinset,
      (cycleWeight (intersectionIdeal f Q) surface : ℚ) * affineDegree surface
      ≤ ((shape f).b * primaryBox.b : ℕ)
theorem cycleWeight_ge {f Q : Row 4} (hc : CutCycle f Q) {surface : JetIdeal}
    (hz : (intersectionIdeal f Q).IsMinimalPrime surface) {l : ℕ}
    (hl : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime) :
    l ≤ cycleWeight (intersectionIdeal f Q) surface := by
  classical
  have hne : cycleLength (intersectionIdeal f Q) surface hz.isPrime ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hc.local_bound surface hz).2.2
  simpa only [cycleWeight, dite_eq_left hz.isPrime, ENat.toNat_natCast] using ENat.toNat_le_toNat hl hne
theorem surface_sum {f Q : Row 4} (hc : CutCycle f Q) (T : Finset JetIdeal)
    (hT : ∀ P ∈ T, (intersectionIdeal f Q).IsMinimalPrime P) :
    ∑ P ∈ T, affineDegree P ≤ ((shape f).b * primaryBox.b : ℕ) := by
  classical
  let S := (intersectionIdeal f Q).minimalPrimesFinset
  have hsub : T ⊆ S := fun P hP => Ideal.mem_minimalPrimesFinset.mpr (hT P hP)
  calc
    _ ≤ ∑ P ∈ S, affineDegree P :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => affineDegree_nonneg P)
    _ ≤ ∑ P ∈ S, (cycleWeight (intersectionIdeal f Q) P : ℚ) * affineDegree P := by
      apply Finset.sum_le_sum
      intro P hP
      have hz := Ideal.mem_minimalPrimesFinset.mp hP
      have h1 := cycleWeight_ge hc hz (hc.local_bound P hz).2.1
      exact le_mul_of_one_le_left (affineDegree_nonneg P) (by exact_mod_cast h1)
    _ ≤ _ := hc.weighted_degree

end
end Height2307CutEnvelope

-- Source: ProximityPrize.SubmissionLower.Low6969FatPad
section Z6969Source2285
set_option autoImplicit true
set_option Elab.async false
section
namespace Low6969FatPad
noncomputable section
open Polynomial Finset
open P3 (K I node)
open Low6969Prices (Messages taylorLength)
def membershipTest (g : K1_13.Row 4) : K1_13.Row 4 :=
  K1_13_6.jetNumerator g taylorLength
open K1_14_6 (occupancy)
open P0_10 (incidence_arithmetic)
open K1_13_6 (CurveSections SurfaceSections Pieces)
open ProximityPrize.Benchmark
open scoped BigOperators
theorem section_capacity {w Γ s} (h : Messages w Γ s) (d : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) →
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ d) :
    46352 * Γ.card ≤ 82414*d + 46352 := by
  classical
  by_cases hm : Γ.card ≤ 1
  · omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ Γ, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ Γ) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ Γ) : 179730 ≤ (hits γ).card := by
    obtain ⟨T, hT, ht⟩ := h.hits γ hγ
    exact hT.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, ht i hi⟩)
  have pair_count (a : K) (ha : a ∈ Γ) (b : K) (hb : b ∈ Γ) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ 133378 := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < Γ.card)
  have hcommon : common.card ≤ 133378 :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := 179730 - common.card
  let t := 133378 - common.card
  have ht : t = x - 46352 := by dsimp [t, x]; omega
  have hx : 46352 ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + 82414 := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    dsimp [x]
    omega
  have exists_trim (γ : K) :
      ∃ T : Finset I, γ ∈ Γ → T ⊆ hits γ \ common ∧ T.card = x := by
    by_cases hγ : γ ∈ Γ
    · have hc := hit_count γ hγ
      have hd : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨T, hT, hcT⟩ := exists_subset_card_eq hd
      exact ⟨T, fun _ => ⟨hT, hcT⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose T hT using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ Γ) : T γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hT γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ Γ) (b : K) (hb : b ∈ Γ) (hab : a ≠ b) :
      (T a ∩ T b).card ≤ t := by
    have cover : (T a ∩ T b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with ht' | hc
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hT a ha).1 (mem_inter.mp ht').1)).1,
          (mem_sdiff.mp ((hT b hb).1 (mem_inter.mp ht').2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hc, common_le b hb hc⟩
    have disj : Disjoint (T a ∩ T b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) :
      (Γ.filter fun γ => i ∈ T γ).card ≤ d := by
    have proper : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hT γ hγ).1 hi)).1).2⟩
  obtain ⟨sec, first⟩ := occupancy Γ nodes T x t d
    (fun γ hγ => ⟨into_nodes γ hγ, (hT γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at sec
  rw [hnodes] at first
  exact incidence_arithmetic 82414 _ _ 46352 _ (by omega) (by decide) hx (by decide) sec first
theorem curve_capacity {w Γ s d} (h : Messages w Γ s) (hc : CurveSections Γ s d) :
    46352 * Γ.card ≤ 82414*d + 46352 :=
  section_capacity h d (fun i => hc (node i) (w i))
theorem curve_capacity_integral {w Γ s d} (h : Messages w Γ s)
    (hc : CurveSections Γ s d) (hd : 0 < d) : Γ.card ≤ 2*d := by
  have := curve_capacity h hc
  omega
theorem pieces_curve_capacity {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.curves s) : 46352 * C.union.card ≤ 82414 * C.total + 46352 * C.n := by
  classical
  have hc' (i : Fin C.n) := Low6969FatPad.curve_capacity (Low6969Prices.Messages.mono h (C.subset i)) (hc i)
  calc
    _ ≤ 46352 * ∑ i, (C.piece i).card :=
      Nat.mul_le_mul_left _ (by exact card_biUnion_le)
    _ = ∑ i, 46352 * (C.piece i).card := by rw [mul_sum]
    _ ≤ ∑ i : Fin C.n, (82414 * C.degree i + 46352) := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, sum_add_distrib, mul_sum, Nat.mul_comm]
theorem pieces_curve_capacity_integral {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.curves s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 2*C.total := by
  classical
  have hc' (i : Fin C.n) := Low6969FatPad.curve_capacity_integral (Low6969Prices.Messages.mono h (C.subset i)) (hc i) (hd i)
  calc
    _ ≤ ∑ i, (C.piece i).card := card_biUnion_le
    _ ≤ ∑ i : Fin C.n, 2 * C.degree i := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, mul_sum]
theorem surface_capacity {w Γ s d} (h : Messages w Γ s)
    (hs : SurfaceSections Γ s d) (hd : 0 < d) : Γ.card ≤ 4*d := by
  classical
  have hsection (i : I) (hi : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) :
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ 2*d := by
    obtain ⟨C, hC, hc, hpos, hdeg⟩ := hs (node i) (w i) hi
    have hH := Low6969Prices.Messages.mono h (filter_subset (fun γ => (s γ).eval (node i) = w i) Γ)
    exact (card_le_card hC).trans ((pieces_curve_capacity_integral C hH hc hpos).trans
      (Nat.mul_le_mul_left 2 hdeg))
  have := section_capacity h (2*d) hsection
  omega
theorem pieces_surface_capacity {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.surfaces s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 4*C.total := by
  classical
  have hc' (i : Fin C.n) := Low6969FatPad.surface_capacity (Low6969Prices.Messages.mono h (C.subset i)) (hc i) (hd i)
  calc
    _ ≤ ∑ i, (C.piece i).card := card_biUnion_le
    _ ≤ ∑ i : Fin C.n, 4 * C.degree i := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, mul_sum]
end
end Low6969FatPad
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1600
namespace Low6969FatPad
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
open K1_13_6_3_5_3 (tupleHeight_le_of_inclusion finsum_weighted cone_eval_jets jet_zero_nonzero)
def ShortSupport (A : CoeffIdeal) : Prop :=
  ∀ i : Fin K1_13.taylorLength, Low6969Prices.taylorLength ≤ i.val → MvPolynomial.X i ∈ A

private theorem principal_divisors : K1_13_6_3_5_3.c2 :=
  K1_13_6_3_5_3_2.of_children K1_13_6_3_5_3_2_1.proof K1_13_6_3_5_3_2_2.proof
private theorem projective_height : K1_13_6_3_5_3.c3 :=
  K1_13_6_3_5_3_3.of_children K1_13_6_3_5_3_3_1.proof K1_13_6_3_5_3_3_2.proof
    K1_13_6_3_5_3_3_3.proof K1_13_6_3_5_3_3_4.proof
private theorem degree_of_support {R : CoeffIdeal} (D : FreshCurve R) (hs : ShortSupport R) :
    D.polynomial.natDegree ≤ 133378 := by
  by_contra h
  let i : Fin taylorLength := ⟨D.polynomial.natDegree, Nat.lt_succ_iff.mpr D.degree_le⟩
  have hi : Low6969Prices.taylorLength ≤ i.val := Nat.lt_of_not_ge h
  have hx : (MvPolynomial.X i : FreshCoeffRing) ∈ extendIdeal R := by
    change (MvPolynomial.X i : FreshCoeffRing) ∈ R.map (MvPolynomial.map geomConstants)
    simpa only [MvPolynomial.map_X] using
      Ideal.mem_map_of_mem (MvPolynomial.map geomConstants) (hs i hi)
  rw [D.equation, coneIdeal, RingHom.mem_ker, coneEval, MvPolynomial.eval₂Hom_X'] at hx
  change Polynomial.C (D.coefficients i) * Polynomial.X = 0 at hx
  have hleading : D.coefficients i = 1 := by
    change D.includeOld (D.polynomial.coeff D.polynomial.natDegree) = 1
    rw [Polynomial.coeff_natDegree, D.monic.leadingCoeff, map_one]
  rw [hleading, Polynomial.C_1, one_mul] at hx
  exact Polynomial.X_ne_zero hx
private theorem multiplicity_bound {m n : ℕ} (hm : m ≤ n) (hn : 2 ≤ n) :
    2 * m ≤ n * min m 2 := by
  by_cases h : m ≤ 2
  · rw [min_eq_left h]
    exact Nat.mul_le_mul_right _ hn
  · rw [min_eq_right (by omega), Nat.mul_comm n 2]
    exact Nat.mul_le_mul_left _ hm
private theorem height_comparison {R : CoeffIdeal} (D : FreshCurve R)
    (hshort : D.polynomial.natDegree ≤ 133378) (hdiv : PrincipalDivisors GeoField D.Fresh) :
    2 * tupleHeight GeoField D.Fresh D.coefficients ≤
      133378 * tupleHeight GeoField D.Fresh (ratios (D.jets (n := 4)) 0) := by
  let : CharP D.Old K1.p := charP_of_injective_ringHom
    ((algebraMap Geom D.Old).comp K1_13.embed).injective K1.p
  have hdeg : D.polynomial.natDegree < taylorLength := Nat.lt_succ_iff.mpr D.degree_le
  have hchar : D.polynomial.natDegree < K1.p := by
    exact D.degree_le.trans_lt (by decide)
  let B := factorsOfMonic D.monic hchar (by decide : 2 < K1.p)
  let z := fun i => (B.factor i).eval₂ D.includeOld D.center
  let r₃ := ratios (D.jets (n := 3)) 0
  let r₄ := ratios (D.jets (n := 4)) 0
  have hc₀ : genericArgument ≠ 0 := by
    have hinj : Function.Injective genericCoeffs :=
      (algebraMap GenericField GeoField).injective.comp
        (IsFractionRing.injective (Polynomial Geom) GenericField)
    simpa only [genericArgument, map_zero] using
      hinj.ne (show (Polynomial.X : (Polynomial Geom)) ≠ 0 from Polynomial.X_ne_zero)
  have hv (v : CurvePlace GeoField D.Fresh) :=
    K1_13_6_3_5_3_6.proof D.Old D.Fresh D.includeOld D.center D.polynomial B v.value
      taylorLength hdeg (v.on_constants _ hc₀) D.independent (K1_13_6_3_5_3_5.proof R D v)
  have hcoeff : tupleHeight GeoField D.Fresh D.coefficients =
      ∑ i, B.multiplicity i * ∑ᶠ v : CurvePlace GeoField D.Fresh, poleOrder v.value (z i) := by
    have hp (v : CurvePlace GeoField D.Fresh) :
        tuplePole v.value D.coefficients = ∑ i, B.multiplicity i * poleOrder v.value (z i) :=
      (hv v).1
    unfold tupleHeight
    simp_rw [hp]
    exact finsum_weighted _ _ (fun i => (hdiv (z i)).1)
  have hjet : tupleHeight GeoField D.Fresh r₃ =
      ∑ i, min (B.multiplicity i) 2 * ∑ᶠ v : CurvePlace GeoField D.Fresh, zeroOrder v.value (z i) := by
    have hp (v : CurvePlace GeoField D.Fresh) :
        tuplePole v.value r₃ = ∑ i, min (B.multiplicity i) 2 * zeroOrder v.value (z i) :=
      (hv v).2
    unfold tupleHeight
    simp_rw [hp]
    exact finsum_weighted _ _ (fun i => (hdiv (z i)).2.1)
  have hmore : tupleHeight GeoField D.Fresh r₃ ≤ tupleHeight GeoField D.Fresh r₄ := by
    apply tupleHeight_le_of_inclusion hdiv r₃ r₄ (Fin.castLE (by decide : 3 ≤ 4))
    intro i
    rfl
  suffices hh : 2 * tupleHeight GeoField D.Fresh D.coefficients ≤
      133378 * tupleHeight GeoField D.Fresh r₃ from
    hh.trans (Nat.mul_le_mul_left _ hmore)
  rw [hcoeff, hjet, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [(hdiv (z i)).2.2.1, ← mul_assoc, ← mul_assoc]
  apply Nat.mul_le_mul_right
  exact multiplicity_bound ((B.le_degree i).trans hshort) (by decide)
theorem boundary_degree (R : CoeffIdeal) (hR : R.IsPrime) (hprime : (extendIdeal R).IsPrime)
    (hhom : R.IsHomogeneous (homogeneousSubmodule (Fin taylorLength) Geom))
    (hdim : dimension R = 2) (hs : ShortSupport R) :
    dimension (freshImage R) = 2 ∧
      2 * affineDegree (extendIdeal R) ≤
        133378 * (residueDegree freshJetMap (extendIdeal R) : ℚ) * affineDegree (freshImage R) := by
  obtain ⟨D⟩ := K1_13_6_3_5_3_1.proof R hR hprime hhom hdim
  have hdiv := principal_divisors GeoField D.Fresh D.freshCurve
  have hshort := degree_of_support D hs
  let u := D.coefficients
  let v := D.jets (n := 4)
  have hcone : extendIdeal R = coneIdeal GeoField u := D.equation
  let i : Fin taylorLength := ⟨D.polynomial.natDegree, Nat.lt_succ_iff.mpr D.degree_le⟩
  have hi : u i = 1 := by
    simp [u, i, FreshCurve.coefficients, coefficientTuple, Polynomial.coeff_natDegree,
      D.monic.leadingCoeff]
  have hu : ratios u i = u := by funext j; simp [ratios, hi]
  have hv₀ : v 0 ≠ 0 := jet_zero_nonzero D 0 rfl
  have hgen : ratioField GeoField u i = ⊤ := by
    rw [ratioField, hu]
    exact D.generates
  obtain ⟨hpositive, hsource⟩ :=
    projective_height GeoField D.Fresh _ D.freshCurve hdiv u i (by simp [hi])
  have hpos : 0 < tupleHeight GeoField D.Fresh u := by
    rw [← hu]
    exact hpositive.mp (by rw [hu]; exact D.nonconstant)
  have hs : (tupleHeight GeoField D.Fresh u : ℚ) = affineDegree (extendIdeal R) := by
    have h := (hsource (by simpa only [hu] using hpos)).2
    rwa [hu, hgen, IntermediateField.finrank_top, Nat.cast_one, one_mul, ← hcone] at h
  have hcmp := height_comparison D hshort hdiv
  have hjpos : 0 < tupleHeight GeoField D.Fresh (ratios v 0) := by
    change 2 * tupleHeight GeoField D.Fresh u ≤ 133378 * tupleHeight GeoField D.Fresh
      (ratios v 0) at hcmp
    omega
  have himage : coneIdeal GeoField v = freshImage R := by
    rw [freshImage, D.equation]
    change RingHom.ker (coneEval GeoField v) =
      (RingHom.ker (coneEval GeoField u)).comap freshJetMap
    rw [RingHom.comap_ker, cone_eval_jets D]
  have hrank := K1_13_6_3_5_3_4.proof GeoField D.Fresh _ _ u i v 0 freshJetMap (by simp [hi]) hv₀ hgen
    (cone_eval_jets D)
  rw [← hcone] at hrank
  obtain ⟨hdim', ht⟩ := (projective_height GeoField D.Fresh _ D.freshCurve hdiv v 0 hv₀).2 hjpos
  rw [himage, ← hrank] at ht
  refine ⟨himage ▸ hdim', ?_⟩
  have hcmp' : 2 * (tupleHeight GeoField D.Fresh u : ℚ) ≤
      133378 * (tupleHeight GeoField D.Fresh (ratios v 0) : ℚ) := by exact_mod_cast hcmp
  rw [hs, ht] at hcmp'
  simpa only [mul_assoc] using hcmp'
end
end Low6969FatPad
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Low6969FatPad
noncomputable section
open MvPolynomial K1_13_6 K1_13_6_3 K1_13_6_3_5
attribute [local instance] MvPolynomial.gradedAlgebra
private theorem boundary_support {A R : CoeffIdeal} (hs : ShortSupport A)
    (hR : boundaryIdeal A ≤ R) : ShortSupport R := by
  intro i hi
  apply hR
  apply Ideal.subset_span
  refine ⟨MvPolynomial.X i, hs i hi, ?_⟩
  rw [totalDegree_X]
  exact homogeneousComponent_eq_self (isHomogeneous_X _ i)
theorem padding (A : CoeffIdeal) (hA : A.IsPrime) (hAe : (extendIdeal A).IsPrime)
    (hdim : dimension A = 2) (hbir : FreshBirational A) (hs : ShortSupport A) :
    2 * affineDegree A ≤ 133378 * affineDegree (freshImage A) := by
  classical
  have h1 := K1_13_6_3_5_1.of_children K1_13_6_3_5_1_1.proof K1_13_6_3_5_1_2.proof
  have h2 := K1_13_6_3_5_2.proof
  have h4 := K1_13_6_3_5_4.proof
  have h5 := K1_13_6_3_5_5.of_children K1_13_6_3_5_5_1.proof K1_13_6_3_5_5_2.proof
    K1_13_6_3_5_5_3.proof K1_13_6_3_5_5_4.proof
  let B := extendIdeal A
  let C := freshImage A
  let S := (boundaryIdeal B).minimalPrimesFinset
  let T := (boundaryIdeal C).minimalPrimesFinset
  let image (P : Ideal FreshCoeffRing) : JetIdeal := P.comap freshJetMap
  let weight (P : Ideal FreshCoeffRing) : ℕ := boundaryWeight (boundaryIdeal B) P
  let rank (P : Ideal FreshCoeffRing) : ℕ := residueDegree freshJetMap P
  obtain ⟨hpoly, hdescend⟩ := h2 A hA
  have hdimB : dimension B = 2 :=
    (congrArg Polynomial.natDegree hpoly).trans hdim
  have hdegree : affineDegree A = affineDegree B := by
    change affineDegree A = affineDegree (extendIdeal A)
    simp only [affineDegree, hpoly]
  have hbirB : IsBirationalOn freshProjection B := hbir
  obtain ⟨hdimC, hproject⟩ := h4 _ _ _ freshProjection freshProjection_linear B hAe hdimB hbirB
  have hC : C.IsPrime := by
    let _ : B.IsPrime := hAe
    exact Ideal.IsPrime.comap freshJetMap
  have hdimC' : dimension C = 2 := hdimC
  have hheight (P : Ideal FreshCoeffRing) (hP : P ∈ S) :
      dimension (image P) = 2 ∧
      2 * affineDegree P ≤ 133378 * (rank P : ℚ) * affineDegree (image P) := by
    have hp := Ideal.mem_minimalPrimesFinset.mp hP
    obtain ⟨R, hR, rfl⟩ := hdescend P hp
    obtain ⟨hd, hhom⟩ := (h1 _ _ A hA hdim).1 R hR
    exact boundary_degree R hR.isPrime hp.isPrime hhom hd (boundary_support hs hR.le)
  have hmaps (P : Ideal FreshCoeffRing) (hP : P ∈ S) : image P ∈ T := by
    apply Ideal.mem_minimalPrimesFinset.mpr
    exact hproject P (Ideal.mem_minimalPrimesFinset.mp hP) (hheight P hP).1
  have hfibre (Q : JetIdeal) (hQ : Q ∈ T) :
      (∑ P ∈ S.filter (fun P => image P = Q), weight P * rank P) ≤
        boundaryWeight (boundaryIdeal C) Q := by
    exact h5 _ _ _ freshProjection freshProjection_linear B hAe hbirB Q
      (Ideal.mem_minimalPrimesFinset.mp hQ)
  calc
    2 * affineDegree A = 2 * ∑ P ∈ S, (weight P : ℚ) * affineDegree P := by
      rw [hdegree, (h1 _ _ B hAe hdimB).2]
    _ ≤ ∑ P ∈ S, 133378 * ((weight P * rank P : ℕ) : ℚ) * affineDegree (image P) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro P hP
      push_cast
      calc
        2 * ((weight P : ℚ) * affineDegree P) =
            (weight P : ℚ) * (2 * affineDegree P) := by ring
        _ ≤ (weight P : ℚ) * (133378 * (rank P : ℚ) * affineDegree (image P)) :=
          mul_le_mul_of_nonneg_left (hheight P hP).2 (by positivity)
        _ = _ := by ring
    _ = ∑ Q ∈ T, ∑ P ∈ S.filter (fun P => image P = Q),
        133378 * ((weight P * rank P : ℕ) : ℚ) * affineDegree (image P) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ Q ∈ T, 133378 * (boundaryWeight (boundaryIdeal C) Q : ℚ) * affineDegree Q := by
      apply Finset.sum_le_sum
      intro Q hQ
      calc
        _ = ∑ P ∈ S.filter (fun P => image P = Q),
            133378 * ((weight P * rank P : ℕ) : ℚ) * affineDegree Q := by
          apply Finset.sum_congr rfl
          intro P hP
          rw [(Finset.mem_filter.mp hP).2]
        _ = 133378 * ((∑ P ∈ S.filter (fun P => image P = Q), weight P * rank P : ℕ) : ℚ) *
            affineDegree Q := by
          rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hfibre Q hQ) (by positivity))
          (affineDegree_nonneg Q)
    _ = 133378 * affineDegree C := by
      rw [(h1 _ _ C hC hdimC').2, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => mul_assoc ..)
end
end Low6969FatPad
end

end Z6969Source2285

-- Source: ProximityPrize.SubmissionLower.Low6969GeometryCut
section Z6969Source2286
set_option autoImplicit true
set_option Elab.async false
set_option autoImplicit true
section
namespace Low6969GeometryCut
noncomputable section
open Polynomial
open P3 (K)
open Low6969Prices (SmallFactor physicalDegree primaryBox primaryCutoff taylorLength TrueWeightLE)
open K1_13 (Geom Row Shape shape extend InBox OnFactor OrderAt chart mixed32)
open K1_13_6 (HighChart toGeneric markIdeal separant jetNumerator divisorIdeal cycleLength)
structure CutInput (Γ : Finset K) (s : K → (Polynomial K)) (f Q : Row 4) (l : ℕ) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  small : SmallFactor f
  onFactor : ∀ γ ∈ Γ, OnFactor f (extend (s γ))
  positive : 0 < l
  proper : ¬ f ∣ Q
  box : InBox (shape Q) primaryBox
  weight : TrueWeightLE Q primaryCutoff
  order : ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength + 1)
def MixedMark (f Q : Row 4) (l : ℕ) (S : (Polynomial Geom)) : Prop :=
  ∃ surface r, HighChart f Q l S surface r ∧
    let g := (separant^[r]) f
    toGeneric (membershipTest g) ∉ surface ∧ ∃ C,
      ∃ hc : (divisorIdeal surface (membershipTest g)).IsMinimalPrime C,
        C ≤ markIdeal S ∧
        (cycleLength (divisorIdeal surface (membershipTest g)) C hc.isPrime ≠ 1 ∨
          toGeneric (nextTest g) ∉ C)
def ContinuedMark (f Q : Row 4) (l : ℕ) (S : (Polynomial Geom)) : Prop :=
  ∃ surface r, HighChart f Q l S surface r ∧
    let g := (separant^[r]) f
    toGeneric (membershipTest g) ∈ surface ∨ ∃ C,
      ∃ hc : (divisorIdeal surface (membershipTest g)).IsMinimalPrime C,
        toGeneric (membershipTest g) ∉ surface ∧ C ≤ markIdeal S ∧
        cycleLength (divisorIdeal surface (membershipTest g)) C hc.isPrime = 1 ∧
        toGeneric (nextTest g) ∈ C

end
end Low6969GeometryCut
end
section
namespace Low6969GeometryCut_1
noncomputable section
open Polynomial
open scoped Polynomial
open K1_13 (Row Geom Shape shape InBox extend atJet OnFactor)
open K1_13_6 (GeoJets CanonicalChart HighMark Invariant separant toGeneric
  markIdeal intersectionIdeal cycleLength)
open K1_13_6_1 (HasMark anchorBox tangentCut DerivativeWeight
  mem_markIdeal orderAt_vanishes tangentCut_vanishes)
open K1_13_6_1_3 (tangent_box anchor_fits derivative_fits)
open Low6969Prices (SmallFactor primaryBox)
open Low6969GeometryCut (CutInput)
open Height2307CutEnvelope (SurfaceCut)
open P0_9_6_1 (canonicalChart)
open P0_9_6_1 (chart_cut derivative_proper)
open Height2307CutEnvelope (lowHasse box_charge box_cutter_charge)
private theorem tangent_cut {f Q : Row 4} {surface : Ideal GeoJets}
    (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) {v r : ℕ}
    (hf : SmallFactor f) (hproper : ¬ f ∣ Q) (hQbox : InBox (shape Q) primaryBox)
    (hv : 0 < v) (hvmax : v ≤ (shape f).b * primaryBox.b)
    (hlen : cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞))
    (hr : CanonicalChart f surface r) (hi : ¬ Invariant ((separant^[r]) f) surface) :
    let g := (separant^[r]) f
    (r = 0 ∧ toGeneric (tangentCut g Q v) ∉ surface ∧
      InBox (shape (tangentCut g Q v)) (primaryBox.plus ((anchorBox f).scale (2*v)))) ∨
    (0 < r ∧ ∃ w, DerivativeWeight f surface r w ∧ toGeneric (tangentCut g f w) ∉ surface ∧
      InBox (shape (tangentCut g f w)) ((anchorBox f).plus ((anchorBox f).scale (2*w)))) := by
  let g := (separant^[r]) f
  have hsep : toGeneric (separant g) ∉ surface := hr.2.2
  have hgt : toGeneric g ∈ surface := hr.2.1 r le_rfl
  have hAnchor := anchor_fits f
  have hGbox := derivative_fits f r
  have ht : 0 < (anchorBox f).t := hf.2.1
  have hj : 0 < (anchorBox f).j :=
    (by omega : 0 < 3 * (anchorBox f).t).trans_le (K1_13_7_1.shape_chamber f).2
  have hfb : (shape f).b ≤ 143 := hf.2.2.1.1
  by_cases hr0 : r = 0
  · subst r
    have hvChar : v < K1.p :=
      (hvmax.trans (Nat.mul_le_mul_right _ hfb)).trans_lt (by decide)
    exact Or.inl ⟨rfl, chart_cut hZ
        (K1_13_7_1.proper_generic f Q hf.1 hproper) hsep hi hv hvChar hlen,
      tangent_box ht hj hAnchor hQbox v⟩
  · have hrPos : 0 < r := Nat.pos_of_ne_zero hr0
    have hg0 : g ≠ 0 := by
      intro he
      exact hsep (by simp [he, separant, toGeneric])
    have hgProper := derivative_proper hf.1 hf.2.1 r hrPos hg0
    have hgRel := K1_13_7_1.proper_generic f g hf.1 hgProper
    obtain ⟨hfg, w, hw, hwmax, hwlen⟩ := K1_13_6_1_3_1.proof f g Q surface hgRel hZ hgt
    have hgb : (shape g).b ≤ 143 := (K1_13_7_1.derivative_in_box f r).1.trans hfb
    have hwChar : w < K1.p :=
      (hwmax.trans (Nat.mul_le_mul hfb hgb)).trans_lt (by decide)
    have hcomm : intersectionIdeal g f = intersectionIdeal f g := by
      unfold intersectionIdeal
      rw [Set.pair_comm]
    have hgf : (intersectionIdeal g f).IsMinimalPrime surface := hcomm ▸ hfg
    have hwlen' : cycleLength (intersectionIdeal g f) surface hgf.isPrime = (w : ℕ∞) := by
      simpa only [hcomm] using hwlen
    exact Or.inr ⟨hrPos, w, ⟨hgProper, hGbox, hw, hfg, hwlen⟩,
      chart_cut hgf hgRel.symm hsep hi hw hwChar hwlen',
      tangent_box ht hj hGbox hAnchor w⟩
open K1_13_7_1 (topAt topAt_coeff eval_topAt topView_separant)
private theorem canonicalChart13 {f : Row 4} {surface : Ideal GeoJets} {S : (Polynomial Geom)}
    (htop : (shape f).t ≤ 16) (hon : OnFactor f S)
    (hfmem : toGeneric f ∈ surface) (hmark : surface ≤ markIdeal S) :
    ∃ r, CanonicalChart f surface r ∧
      InBox (shape (separant ((separant^[r]) f))) (anchorBox f) := by
  classical
  let t := (shape f).t
  let P := topAt S f
  have hdeg : P.natDegree ≤ t := Polynomial.natDegree_map_le.trans_eq
    (K1_13_1.topView_degree f)
  have hnz : (derivative^[t] P).coeff 0 ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul]
    change (t.factorial : (Polynomial Geom)) * P.coeff t ≠ 0
    rw [← map_natCast (Polynomial.C : Geom →+* (Polynomial Geom))]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      (K1_13_7_1.factorial_cast_ne_zero (htop.trans_lt (by decide : 16 < K1.p))))
      (by simpa only [P, t, topAt_coeff] using hon.2)
  have hc : derivative^[t] P = Polynomial.C ((derivative^[t] P).coeff 0) :=
    eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans
      (by omega : P.natDegree - t ≤ 0))
  have he (k : ℕ) : atJet ((separant^[k]) f) S =
      (derivative^[k] P).eval (K1_13.jet S (3 : Fin 4)) := by
    rw [← eval_topAt]
    congr 1
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      change (K1_13_1.topView (separant ((separant^[k]) f))).map
        (MvPolynomial.eval (K1_13.jet S)) = _
      rw [topView_separant, ← derivative_map]
      exact congrArg derivative ih
  have htSurface : toGeneric ((separant^[t]) f) ∉ surface := by
    intro hm
    have hv := mem_markIdeal.mp (hmark hm)
    rw [he, hc, Polynomial.eval_C] at hv
    exact hnz hv
  have hex : ∃ i, toGeneric ((separant^[i]) f) ∉ surface := ⟨t, htSurface⟩
  let n := Nat.find hex
  have hn : toGeneric ((separant^[n]) f) ∉ surface := Nat.find_spec hex
  have hnt : n ≤ (shape f).t := Nat.find_min' hex htSurface
  have hn0 : n ≠ 0 := by
    intro h
    exact hn (by simpa only [h, Function.iterate_zero_apply] using hfmem)
  have hstep : (n - 1).succ = n := by omega
  have hsep : separant ((separant^[n - 1]) f) = (separant^[n]) f := by
    rw [← Function.iterate_succ_apply' separant (n - 1) f, hstep]
  refine ⟨n - 1, ⟨by omega, ?_, ?_⟩, ?_⟩
  · intro i hi
    by_contra h
    exact Nat.find_min hex (show i < n by omega) h
  · rwa [hsep]
  · rw [hsep]
    exact derivative_fits f n

theorem one_surface {Γ s f Q l surface} (input : CutInput Γ s f Q l)
    (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) (active : HasMark Γ s surface) :
    ∃ P, SurfaceCut f Q surface P ∧
      ∀ γ ∈ Γ, surface ≤ markIdeal (extend (s γ)) →
        ¬ HighMark f Q l (extend (s γ)) → atJet P (extend (s γ)) = 0 := by
  obtain ⟨v, hv, hvmax, hlen, hlow⟩ := lowHasse hZ input.small.1 input.proper input.box
  by_cases low : v < l
  · obtain ⟨P, hP, hPb, hvan⟩ := hlow low
    have hPb' : InBox (shape P) (primaryBox.plus ((anchorBox f).scale 0)) := by
      simpa [InBox, Shape.plus, Shape.scale, Low6969Prices.primaryBox] using hPb
    exact ⟨P, ⟨hZ, v, 0, hv, hlen, Or.inl rfl, hP,
      box_cutter_charge hPb' (Nat.zero_le _)⟩,
      fun γ hγ _ _ => hvan _ (input.order γ hγ)⟩
  obtain ⟨γ₀, hγ₀, hmark₀⟩ := active
  have hfmem : toGeneric f ∈ surface := hZ.le (Ideal.subset_span (Set.mem_insert _ _))
  obtain ⟨r, hr, hrBox⟩ := canonicalChart13 input.small.2.2.1.2.2
    (input.onFactor γ₀ hγ₀) hfmem hmark₀
  let g := (separant^[r]) f
  have on_g : ∀ S, surface ≤ markIdeal S → atJet g S = 0 :=
    fun S hS => mem_markIdeal.mp (hS (hr.2.1 r le_rfl))
  have high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hZ.isPrime := by
    rw [hlen]
    exact_mod_cast Nat.le_of_not_gt low
  by_cases inv : Invariant g surface
  · have hsep : InBox (shape (separant g)) ((anchorBox f).scale 1) := by
      simpa [InBox, Shape.scale] using hrBox
    refine ⟨separant g, ⟨hZ, v, 0, hv, hlen, Or.inl rfl, hr.2.2,
      box_charge hsep (by omega)⟩, ?_⟩
    intro γ _ hpoint hnot
    by_contra hregular
    exact hnot ⟨surface, r, hZ, high, hpoint, hr, hregular, inv⟩
  rcases tangent_cut hZ input.small input.proper input.box hv hvmax hlen hr inv with
    ⟨_, hP, hPb⟩ | ⟨hrPos, w, hw, hP, hPb⟩
  · exact ⟨tangentCut g Q v, ⟨hZ, v, 0, hv, hlen, Or.inl rfl, hP,
      box_cutter_charge hPb (by omega)⟩,
      fun γ hγ hpoint _ => tangentCut_vanishes g Q _ v (on_g _ hpoint)
        (orderAt_vanishes input.positive (input.order γ hγ))⟩
  · have hPb' : InBox (shape (tangentCut g f w)) ((anchorBox f).scale (2*w+1)) := by
      simpa [InBox, Shape.plus, Shape.scale, Nat.add_mul, Nat.add_comm] using hPb
    exact ⟨tangentCut g f w, ⟨hZ, v, w, hv, hlen, Or.inr ⟨r, hrPos, hr.1, hw⟩, hP,
      box_charge hPb' (by omega)⟩,
      fun γ hγ hpoint _ => tangentCut_vanishes g f _ w (on_g _ hpoint)
        (input.onFactor γ hγ).1⟩
end
end Low6969GeometryCut_1
end
section
namespace Low6969GeometryCut_1
noncomputable section
open K1_13 (Row Shape shape InBox chart mixed32)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength divisorIdeal separant)
open K1_13_6_1 (anchorBox DerivativeWeight CurveOnFactor sectionDegree)
open K1_13_6_1_4 (FullChamber pair_dimension curve_of_proper_cut surfaceDegree)
open K1_13_7_1 (toGeneric_fits proper_generic shape_chamber)
open Low6969Prices (SmallFactor primaryBox taylorLength)
open Low6969GeometryCut (auxCurves32 auxPoints32)
open Height2307CutEnvelope (SurfaceCut)
open scoped BigOperators
open P0_9_6_1_1 (proper_divisor additive_sections weighted_pair full_chart full_plus chamber_scale full_scale sum_biUnion_bound toGeneric_ne_zero)
private theorem derivative_sum {f : Row 4} (hf : Irreducible f)
    (hp : FullChamber (anchorBox f)) {h : Shape} (hh : FullChamber h)
    (surfaces : Finset (Ideal GeoJets)) (r w : Ideal GeoJets → ℕ)
    (hr : ∀ surface ∈ surfaces, r surface < (shape f).t)
    (hw : ∀ surface ∈ surfaces, w surface = 0 ∨ DerivativeWeight f surface (r surface) (w surface)) :
    32 * (∑ surface ∈ surfaces, w surface *
      surfaceDegree surface ((anchorBox f).scale 6) (h.scale 6)) ≤
      36 * ((shape f).t * mixed32 (anchorBox f) (anchorBox f) (anchorBox f) h) := by
  classical
  let p := anchorBox f
  let value := fun surface => w surface * surfaceDegree surface (p.scale 6) (h.scale 6)
  let paid := surfaces.filter fun surface => w surface ≠ 0
  let orders := Finset.range (shape f).t
  have hmaps : ∀ surface ∈ paid, r surface ∈ orders := by
    intro surface hs
    exact Finset.mem_range.mpr (hr surface (Finset.mem_filter.mp hs).1)
  have hpaid : (∑ surface ∈ paid, value surface) = ∑ surface ∈ surfaces, value surface := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro surface _
    by_cases hv : w surface = 0 <;> simp [value, hv]
  have group (j : ℕ) :
      32 * (∑ surface ∈ paid.filter (fun surface => r surface = j), value surface) ≤
        36 * mixed32 p p p h := by
    let fibre := paid.filter fun surface => r surface = j
    by_cases he : fibre.Nonempty
    · have data (surface : Ideal GeoJets) (hs : surface ∈ fibre) :
          DerivativeWeight f surface j (w surface) := by
        obtain ⟨hpaid, htag⟩ := Finset.mem_filter.mp hs
        obtain ⟨hs, hpos⟩ := Finset.mem_filter.mp hpaid
        rw [← htag]
        exact (hw surface hs).resolve_left hpos
      obtain ⟨surface, hs⟩ := he
      let g := (separant^[j]) f
      have hgproper : ¬ f ∣ g := (data surface hs).1
      have hgfit : InBox (shape g) p := (data surface hs).2.1
      have hf0 := toGeneric_ne_zero hf.ne_zero
      have hg0 : toGeneric g ≠ 0 := toGeneric_ne_zero fun hg =>
        hgproper (hg.symm ▸ dvd_zero f)
      exact weighted_pair _ _ p p p h hf0 hg0 (proper_generic f g hf hgproper)
        hp hp hp hh (toGeneric_fits ⟨le_max_left _ _, le_rfl, le_rfl⟩) (toGeneric_fits hgfit)
        fibre w (fun t ht => (data t ht).2.2.2)
    · rw [show paid.filter (fun surface => r surface = j) = ∅ from
        Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty, mul_zero]
      exact Nat.zero_le _
  change 32 * (∑ surface ∈ surfaces, value surface) ≤ 36 * ((shape f).t * mixed32 p p p h)
  calc
    _ = ∑ j ∈ orders, 32 * (∑ surface ∈ paid.filter (fun surface => r surface = j), value surface) := by
      rw [← hpaid, ← Finset.sum_fiberwise_of_maps_to hmaps value]
      simp only [Finset.mul_sum]
    _ ≤ ∑ _j ∈ orders, 36 * mixed32 p p p h := Finset.sum_le_sum fun j _ => group j
    _ = _ := by simp [orders, Nat.mul_left_comm]
private theorem degree_bound
    {f Q : Row 4} {surfaces : Finset (Ideal GeoJets)} {P : Ideal GeoJets → Row 4}
    (hf : SmallFactor f) (hq : ¬ f ∣ Q) (hQ : InBox (shape Q) primaryBox)
    (cuts : ∀ surface ∈ surfaces, SurfaceCut f Q surface (P surface))
    {h : Shape} (hh : FullChamber h) :
    32 * (∑ C ∈ surfaces.biUnion (fun surface => (divisorIdeal surface (P surface)).minimalPrimesFinset),
      sectionDegree C (h.scale 6)) ≤
    6 * (mixed32 (anchorBox f) primaryBox (primaryBox.plus ((anchorBox f).scale 4)) h +
      2*(shape f).t * mixed32 (anchorBox f) (anchorBox f) (anchorBox f) h) := by
  classical
  let p := anchorBox f
  let a := primaryBox.plus (p.scale 4)
  let base := fun surface => surfaceDegree surface (a.scale 6) (h.scale 6)
  let extra := fun surface => surfaceDegree surface (p.scale 6) (h.scale 6)
  let components := fun surface => (divisorIdeal surface (P surface)).minimalPrimesFinset
  let d := fun C => sectionDegree C (h.scale 6)
  let total := ∑ C ∈ surfaces.biUnion components, d C
  have hp : FullChamber p := ⟨shape_chamber f, hf.2.1⟩
  have hqBox : FullChamber primaryBox := ⟨⟨by decide, by decide⟩, by decide⟩
  have ha : FullChamber a := full_plus hqBox (chamber_scale hp.1 4)
  have only_on_selected (surface : Ideal GeoJets) :
    ∃ v w r : ℕ, surface ∈ surfaces →
      (∃ hs : (intersectionIdeal f Q).IsMinimalPrime surface,
        cycleLength (intersectionIdeal f Q) surface hs.isPrime = (v : ℕ∞)) ∧
      0 < v ∧ r < (shape f).t ∧ (w = 0 ∨ DerivativeWeight f surface r w) ∧
      toGeneric (P surface) ∉ surface ∧
      InBox (shape (P surface)) (primaryBox.plus ((anchorBox f).scale (4*v + 2*w))) := by
    by_cases hs : surface ∈ surfaces
    · obtain ⟨hz, v, w, hv, hlen, hw, hP, hfit⟩ := cuts surface hs
      rcases hw with hw | ⟨r, _, hr, hw⟩
      · exact ⟨v, w, 0, fun _ => ⟨⟨hz, hlen⟩, hv, hf.2.1, Or.inl hw, hP, hfit⟩⟩
      · exact ⟨v, w, r, fun _ => ⟨⟨hz, hlen⟩, hv, hr, Or.inr hw, hP, hfit⟩⟩
    · exact ⟨0, 0, 0, fun hn => (hs hn).elim⟩
  choose v w r hdata using only_on_selected
  have hf0 := toGeneric_ne_zero hf.1.ne_zero
  have hQ0 : toGeneric Q ≠ 0 := toGeneric_ne_zero fun hzero =>
    hq (hzero.symm ▸ dvd_zero f)
  have hproper := proper_generic f Q hf.1 hq
  have single (surface : Ideal GeoJets) (hs : surface ∈ surfaces) :
      6 * (∑ C ∈ components surface, d C) ≤ v surface * base surface + (2*w surface) * extra surface := by
    obtain ⟨⟨hz, _⟩, hv, _, _, hP, hfit⟩ := hdata surface hs
    have hdim := pair_dimension hf0 hproper hz
    have hab := full_plus (full_scale ha hv) (chamber_scale hp.1 (2*w surface))
    exact (proper_divisor surface _ _ h hz.isPrime hdim hab hh hP (Height2307CutEnvelope.supported_charge hv hfit)).trans
      (additive_sections surface a p h _ _ hz.isPrime hdim ha hp hh hv)
  have hsum : 6 * total ≤
      (∑ surface ∈ surfaces, v surface * base surface) +
        2 * (∑ surface ∈ surfaces, w surface * extra surface) := by
    calc
      _ ≤ 6 * (∑ surface ∈ surfaces, ∑ C ∈ components surface, d C) :=
        Nat.mul_le_mul_left _ (sum_biUnion_bound surfaces components d)
      _ = ∑ surface ∈ surfaces, 6 * (∑ C ∈ components surface, d C) := Finset.mul_sum ..
      _ ≤ ∑ surface ∈ surfaces, (v surface * base surface + (2*w surface) * extra surface) :=
        Finset.sum_le_sum single
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]; simp only [Nat.mul_assoc]
  have hbase := weighted_pair _ _ p primaryBox a h hf0 hQ0 hproper hp hqBox ha hh
    (toGeneric_fits ⟨le_max_left _ _, le_rfl, le_rfl⟩) (toGeneric_fits hQ)
    surfaces v (fun surface hs => (hdata surface hs).1)
  have hextra := derivative_sum hf.1 hp hh surfaces r w
    (fun surface hs => (hdata surface hs).2.2.1)
    (fun surface hs => (hdata surface hs).2.2.2.1)
  change 32 * (∑ surface ∈ surfaces, v surface * base surface) ≤
    36 * mixed32 p primaryBox a h at hbase
  change 32 * (∑ surface ∈ surfaces, w surface * extra surface) ≤
    36 * ((shape f).t * mixed32 p p p h) at hextra
  change 32 * total ≤ 6 * (mixed32 p primaryBox a h + 2*(shape f).t * mixed32 p p p h)
  rw [Nat.mul_assoc 2]
  omega
theorem cut_curves :
  ∀ f Q (surfaces : Finset (Ideal GeoJets)) (P : Ideal GeoJets → Row 4),
    SmallFactor f → (¬ f ∣ Q) → InBox (shape Q) primaryBox →
    (∀ surface ∈ surfaces, SurfaceCut f Q surface (P surface)) →
    ∃ curves : Finset (Ideal GeoJets),
      (∀ surface ∈ surfaces, ∀ C, (divisorIdeal surface (P surface)).IsMinimalPrime C → C ∈ curves) ∧
      (∀ C ∈ curves, CurveOnFactor f C) ∧
      32 * (∑ C ∈ curves, sectionDegree C ((chart taylorLength (anchorBox f)).scale 6)) ≤
        6 * auxCurves32 (shape f) ∧
      32 * (∑ C ∈ curves, sectionDegree C ((anchorBox f).scale 6)) ≤
        6 * auxPoints32 (shape f) := by
  classical
  intro f Q surfaces P hf hq hQ cuts
  let curves := surfaces.biUnion fun surface => (divisorIdeal surface (P surface)).minimalPrimesFinset
  have hf0 := toGeneric_ne_zero hf.1.ne_zero
  have hproper := proper_generic f Q hf.1 hq
  have hp : FullChamber (anchorBox f) := ⟨shape_chamber f, hf.2.1⟩
  have hchart := full_chart taylorLength (show 0 < 133379 by decide) (anchorBox f)
  refine ⟨curves, ?_, ?_, ?_, ?_⟩
  · intro surface hs C hC
    exact Finset.mem_biUnion.mpr ⟨surface, hs, Ideal.mem_minimalPrimesFinset.mpr hC⟩
  · intro C hC
    obtain ⟨surface, hs, hc⟩ := Finset.mem_biUnion.mp hC
    obtain ⟨hz, _, _, _, _, _, hP, _⟩ := cuts surface hs
    exact curve_of_proper_cut hz.isPrime (pair_dimension hf0 hproper hz)
      (hz.le (Ideal.subset_span (by simp))) hP (Ideal.mem_minimalPrimesFinset.mp hc)
  · exact degree_bound hf hq hQ cuts hchart
  · exact degree_bound hf hq hQ cuts hp
end
end Low6969GeometryCut_1
end
section
namespace Low6969GeometryCut_1
noncomputable section
open Polynomial
open P3 (K)
open Low6969Prices (SmallFactor physicalDegree taylorLength)
open K1_13 (InBox chart extend shape atJet)
open K1_13_6 (CanonicalChart CurveSections evalGeneric markIdeal separant)
open K1_13_6_1 (CurveOnFactor anchorBox sectionDegree mem_markIdeal)
open K1_13_6_1_5 (coordinate_cut)
open K1_13_7 (RegularAt)
open K1_13_7_1 (Chamber GeoFits derivative_in_box shape_chamber toGeneric_fits)
open P0_9_6_1_2 (exists_value_cut)
open P0_9_6_1_2 (count_points count_marks chart_has_simplex)
theorem recover_curve :
  ∀ (Γ : Finset K) s f C r, SmallFactor f → CurveOnFactor f C → CanonicalChart f C r →
    InBox (shape (separant ((separant^[r]) f))) (anchorBox f) →
    Set.InjOn s (Γ : Set K) → (∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree) →
    ∃ (A B : Finset K) (d : ℕ),
      A ⊆ Γ ∧ CurveSections A s d ∧
      (∀ γ ∈ Γ, C ≤ markIdeal (extend (s γ)) → γ ∈ A ∪ B) ∧
      6*d ≤ sectionDegree C ((chart taylorLength (anchorBox f)).scale 6) ∧
      6*B.card ≤ sectionDegree C ((anchorBox f).scale 6) ∧
      6 ≤ sectionDegree C ((anchorBox f).scale 6) := by
  classical
  intro Γ s f C r hf hc hr hsep hinj hdeg
  let p := anchorBox f
  let g := (separant^[r]) f
  have hp : Chamber p := shape_chamber f
  have ht : 0 < p.t := hf.2.1
  have hunit : InBox ⟨1, 3, 1⟩ p := by
    change 1 ≤ p.b ∧ 3 ≤ p.j ∧ 1 ≤ p.t
    have hbj := hp.1
    have hjt := hp.2
    omega
  have hgbox : InBox (shape g) p :=
    let hb := derivative_in_box f r
    ⟨hb.1.trans (le_max_left _ _), hb.2.1, hb.2.2⟩
  have hL : taylorLength ≤ K1.p := by
    change 133379 ≤ 0x7f000001
    decide
  let A := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧ RegularAt g (extend (s γ))
  let B := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧ ¬ RegularAt g (extend (s γ))
  let d := sectionDegree C ((chart taylorLength p).scale 6) / 6
  refine ⟨A, B, d, Finset.filter_subset _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro x a hmiss
    obtain ⟨D, hfit, hvalue⟩ := exists_value_cut hL hgbox hp ht x a
    have on {γ} (hγ : γ ∈ A) :
        C ≤ markIdeal (extend (s γ)) ∧
          (evalGeneric (extend (s γ)) D = 0 ↔ (s γ).eval x = a) := by
      obtain ⟨hΓ, hpoint, hreg⟩ := Finset.mem_filter.mp hγ
      have hvan : atJet g (extend (s γ)) = 0 :=
        mem_markIdeal.mp (hpoint (hr.2.1 r le_rfl))
      exact ⟨hpoint, hvalue _ (Nat.lt_succ_of_le (hdeg γ hΓ)) hvan hreg⟩
    have hproper : D ∉ C := by
      obtain ⟨γ, hγ, hmiss⟩ := hmiss
      exact fun hmem => hmiss ((on hγ).2.mp ((on hγ).1 hmem))
    let L := A.filter fun γ => (s γ).eval x = a
    have hLΓ : L ⊆ Γ := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hcount := count_marks hc (chart_has_simplex taylorLength p) hfit hproper hinj hLΓ (by
      intro γ hγ
      change γ ∈ A.filter (fun η => (s η).eval x = a) at hγ
      obtain ⟨hA, hv⟩ := Finset.mem_filter.mp hγ
      exact ⟨(on hA).1, (on hA).2.mpr hv⟩)
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 6)).mpr (by simpa [Nat.mul_comm] using hcount)
  · intro γ hγ hpoint
    by_cases hreg : RegularAt g (extend (s γ))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hpoint, hreg⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hpoint, hreg⟩)
  · simpa only [d, Nat.mul_comm] using
      Nat.div_mul_le_self (sectionDegree C ((chart taylorLength p).scale 6)) 6
  · apply count_marks hc hunit (toGeneric_fits hsep) hr.2.2 hinj (Finset.filter_subset _ _)
    intro γ hγ
    obtain ⟨_, hpoint, hsing⟩ := Finset.mem_filter.mp hγ
    exact ⟨hpoint, mem_markIdeal.mpr (not_ne_iff.mp hsing)⟩
  · obtain ⟨x, P, hx, hP, hproper, hvan⟩ := coordinate_cut hc.prime hc.dim
    have hfitP : GeoFits P p :=
      ⟨hP.1.trans hunit.1, hP.2.1.trans hunit.2.1, hP.2.2.trans hunit.2.2⟩
    simpa using count_points C p hc.prime hc.dim hunit P hfitP hproper {x} (by
      intro y hy
      rw [Finset.mem_singleton.mp hy]
      exact ⟨hx, hvan⟩)
end
end Low6969GeometryCut_1
end
namespace Low6969GeometryCut
export Low6969FatPad (section_capacity curve_capacity curve_capacity_integral pieces_curve_capacity
  pieces_curve_capacity_integral surface_capacity pieces_surface_capacity)
end Low6969GeometryCut

section
namespace Low6969GeometryCut
noncomputable section
open Polynomial
open P3 (K)
open Low6969Prices (Messages SmallFactor ProperCut physicalPrice physicalPriceOld physicalPriceTilted
  tiltedSurface primaryBox surfaceNumerator32 taylorLength)
open K1_13 (Row Shape Geom extend atJet shape ceilDiv)
open K1_13_6 (Pieces toGeneric
  separant jetNumerator HighMark divisorIdeal cycleLength eval_jetNumerator)
open K1_13_6_1 (mem_markIdeal mark_curve)
open scoped BigOperators
def c1 : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l →
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧
      (∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * C.total ≤ auxCurves32 (shape f) ∧
      32 * (B.card + C.n) ≤ 2 * auxPoints32 (shape f)
def MixedBound (Γ : Finset K) (s : K → (Polynomial K)) (f Q : Row 4) (l scale budget : ℕ) : Prop :=
  ∃ (C : Pieces Γ) (B : Finset K),
    C.curves s ∧ (∀ i, 0 < C.degree i) ∧
    (∀ γ ∈ Γ, MixedMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
    scale * l * (2 * C.total + B.card) ≤ budget

def c2 : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l →
    MixedBound Γ s f Q l 32 (surfaceNumerator32 (shape f).chamber primaryBox)

def c2Tilted : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l → Low6969Prices.tiltedFits (shape f) →
    MixedBound Γ s f Q l (60 * 32) (tiltedSurface (shape f).chamber primaryBox)

def c2Active : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l → ∀ K, Low6969Prices.ActiveFits f K →
    Low6969Prices.ActiveFits Q 5192 → Low6969Prices.tiltedFits (shape f) →
    Low6969Prices.activeFitsPrice (shape f) K →
    MixedBound Γ s f Q l (60 * 32) (Low6969Prices.tiltedSurfaceActive (shape f).chamber primaryBox K)

def c6Old : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, K1_13.OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPriceOld (shape f) l

def c3 : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l →
    ∃ C D : Pieces Γ,
      C.curves s ∧ D.surfaces s ∧ (∀ i, 0 < C.degree i) ∧ (∀ i, 0 < D.degree i) ∧
      (∀ γ ∈ Γ, ContinuedMark f Q l (extend (s γ)) → γ ∈ C.union ∪ D.union) ∧
      l * C.total ≤ membershipDegree (shape f) ∧
      2 * D.total ≤ 133378 * (shape f).b * primaryBox.b
private theorem eval_jetNumerator_zero (g : Row 4) (S : (Polynomial Geom))
    (hg : atJet g S = 0) (n : ℕ) (hS : S.natDegree < n) :
    atJet (jetNumerator g n) S = 0 := by
  rw [eval_jetNumerator _ _ hg, iterate_derivative_eq_zero hS, mul_zero]
theorem eval_membership_tests (g : Row 4) (S : (Polynomial Geom))
    (hg : atJet g S = 0) (hS : S.natDegree ≤ 133378) :
    atJet (membershipTest g) S = 0 ∧ atJet (nextTest g) S = 0 :=
  ⟨eval_jetNumerator_zero g S hg taylorLength (Nat.lt_succ_of_le hS),
    eval_jetNumerator_zero g S hg (taylorLength + 1)
      ((Nat.lt_succ_of_le hS).trans (Nat.lt_succ_self _))⟩
theorem highMark_cases {f Q l S} (hS : S.natDegree ≤ 133378)
    (hh : HighMark f Q l S) : MixedMark f Q l S ∨ ContinuedMark f Q l S := by
  obtain ⟨surface, r, hc⟩ := hh
  let g := (separant^[r]) f
  have hg : atJet g S = 0 := mem_markIdeal.mp (hc.point (hc.chart.2.1 r le_rfl))
  have hE := (eval_membership_tests g S hg hS).1
  by_cases onSurface : toGeneric (membershipTest g) ∈ surface
  · exact Or.inr ⟨surface, r, hc, Or.inl onSurface⟩
  obtain ⟨curve, hcurve, hpoint⟩ := mark_curve hc.point hE
  by_cases hsimple : cycleLength (divisorIdeal surface (membershipTest g)) curve hcurve.isPrime = 1
  · by_cases hnext : toGeneric (nextTest g) ∈ curve
    · exact Or.inr ⟨surface, r, hc, Or.inr ⟨curve, hcurve, onSurface, hpoint, hsimple, hnext⟩⟩
    · exact Or.inl ⟨surface, r, hc, onSurface, curve, hcurve, hpoint, Or.inr hnext⟩
  · exact Or.inl ⟨surface, r, hc, onSurface, curve, hcurve, hpoint, Or.inl hsimple⟩
theorem le_ceil {n d count : ℕ} (hd : 0 < d) (h : count*d ≤ n) :
    count ≤ ceilDiv n d := by
  unfold ceilDiv
  exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
theorem price_formula_old (x : Shape) (l : ℕ) :
    physicalPriceOld x l = chargedPrice x l 32 (surfaceNumerator32 x.chamber primaryBox) := by
  simp only [physicalPriceOld, chargedPrice, auxCurves32, auxPoints32, membershipDegree, Nat.mul_assoc]
  rfl

theorem price_formula_tilted (x : Shape) (l : ℕ) :
    physicalPriceTilted x l = chargedPrice x l (60 * 32) (tiltedSurface x.chamber primaryBox) := by
  simp only [physicalPriceTilted, Low6969Prices.physicalPriceWith, chargedPrice, auxCurves32, auxPoints32, membershipDegree, Nat.mul_assoc]
  rfl

theorem assemble_charge (h1 : c1) (h3 : c3) {w Γ s f Q l scale budget}
    (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (hscale : 0 < scale) (h2 : MixedBound Γ s f Q l scale budget) :
    Γ.card ≤ chargedPrice (shape f) l scale budget := by
  classical
  have hl := input.positive
  obtain ⟨A, AB, hA, haCover, haCurves, haPoints⟩ := h1 Γ s f Q l input
  obtain ⟨C, CB, hC, hcPos, hcCover, hcBudget⟩ := h2
  obtain ⟨D, F, hD, hF, hdPos, hfPos, hdCover, hdBudget, hfBudget⟩ := h3 Γ s f Q l input
  let aux := A.union.card + AB.card
  let mixed := C.union.card + CB.card
  have cover : Γ ⊆ (A.union ∪ AB) ∪ (C.union ∪ CB) ∪ D.union ∪ F.union := by
    intro γ hγ
    by_cases hh : HighMark f Q l (extend (s γ))
    · have hdeg : (extend (s γ)).natDegree ≤ 133378 := by
        rw [Polynomial.natDegree_map]
        exact hm.degree γ hγ
      rcases highMark_cases hdeg hh with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (hcCover γ hγ h)))
      · rcases Finset.mem_union.mp (hdCover γ hγ h) with hd | hf
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hd)
        · exact Finset.mem_union_right _ hf
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (haCover γ hγ hh)))
  have card : Γ.card ≤ aux + mixed + D.union.card + F.union.card := by
    refine (Finset.card_le_card cover).trans ?_
    calc
      _ ≤ (((A.union ∪ AB) ∪ (C.union ∪ CB)) ∪ D.union).card + F.union.card :=
        Finset.card_union_le _ _
      _ ≤ ((A.union ∪ AB) ∪ (C.union ∪ CB)).card + D.union.card + F.union.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (A.union ∪ AB).card + (C.union ∪ CB).card + D.union.card + F.union.card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
      _ ≤ _ := by
        exact Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)) _) _
  let x := shape f
  have aux_bound : aux ≤
      ceilDiv (82414 * auxCurves32 x + 2*46352 * auxPoints32 x) (32*46352) := by
    apply le_ceil (by decide)
    have hA' := pieces_curve_capacity A hm hA
    change 32 * A.total ≤ auxCurves32 x at haCurves
    change 32 * (AB.card + A.n) ≤ 2 * auxPoints32 x at haPoints
    dsimp only [aux]
    omega
  have mixed_bound : l * mixed ≤ ceilDiv budget scale := by
    apply le_ceil hscale
    have hC' := Nat.add_le_add_right (pieces_curve_capacity_integral C hm hC hcPos) CB.card
    have h := (Nat.mul_le_mul_left (scale*l) hC').trans hcBudget
    simpa only [mixed, x, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have curve_bound : l * D.union.card ≤
      ceilDiv ((82414 + 2*46352) * membershipDegree x) 46352 := by
    apply le_ceil (by decide)
    have hD' := Nat.mul_le_mul_left l (pieces_curve_capacity_integral D hm hD hdPos)
    change l * D.total ≤ membershipDegree x at hdBudget
    have hD'' : l * D.union.card ≤ 2 * membershipDegree x := by
      rw [Nat.mul_left_comm] at hD'
      omega
    omega
  have main_bound : mixed + D.union.card ≤
      ceilDiv (ceilDiv budget scale +
        ceilDiv ((82414 + 2*46352) * membershipDegree x) 46352) l := by
    apply le_ceil hl
    rw [Nat.add_mul, Nat.mul_comm mixed l, Nat.mul_comm D.union.card l]
    exact Nat.add_le_add mixed_bound curve_bound
  have surface_bound : F.union.card ≤ 2*(133378*x.b*primaryBox.b) := by
    have hF' := pieces_surface_capacity F hm hF hfPos
    change 2 * F.total ≤ 133378*x.b*primaryBox.b at hfBudget
    omega
  change Γ.card ≤ chargedPrice x l scale budget
  unfold chargedPrice
  omega

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : c6Old := by
  intro w Γ s hm f hf hOn l hl hCut
  obtain ⟨Q, hproper, hbox, hweight, hactiveQ, horder⟩ := hCut
  have input : CutInput Γ s f Q l :=
    ⟨hm.distinct, hm.degree, hf, hOn, hl, hproper, hbox, hweight, horder⟩
  rw [price_formula_old]
  exact assemble_charge h1 h3 hm input (by decide) (h2 Γ s f Q l input)

theorem price_formula_active (x : Shape) (l K : ℕ) :
    Low6969Prices.physicalPriceActive x l K =
      chargedPrice x l (60 * 32) (Low6969Prices.tiltedSurfaceActive x.chamber primaryBox K) := by
  simp only [Low6969Prices.physicalPriceActive, Low6969Prices.physicalPriceWith, chargedPrice,
    auxCurves32, auxPoints32, membershipDegree, Nat.mul_assoc]
  rfl

theorem of_children_active (h1 : c1) (h3 : c3) (hold : c6Old)
    (htilt : c2Tilted) (hactive : c2Active) :
    Low6969Prices.c6 := by
  intro w Γ s hm f hf K hK hOn l hl hCut
  have hbase := hold w Γ s hm f hf hOn l hl hCut
  by_cases h : Low6969Prices.tiltedFits (shape f)
  · rw [physicalPrice, ite_eq_left h]
    obtain ⟨Q, hproper, hbox, hweight, hactiveQ, horder⟩ := hCut
    have input : CutInput Γ s f Q l :=
      ⟨hm.distinct, hm.degree, hf, hOn, hl, hproper, hbox, hweight, horder⟩
    have htilt' : Γ.card ≤ physicalPriceTilted (shape f) l := by
      rw [price_formula_tilted]
      exact assemble_charge h1 h3 hm input (by decide) (htilt Γ s f Q l input h)
    split_ifs with ha
    · refine le_min (le_min hbase htilt') ?_
      rw [price_formula_active]
      exact assemble_charge h1 h3 hm input (by decide)
        (hactive Γ s f Q l input K hK hactiveQ h ha)
    · exact le_min hbase htilt'
  · simpa only [physicalPrice, ite_eq_right h] using hbase

end
end Low6969GeometryCut
end
section
namespace Low6969GeometryCut_1
noncomputable section
open P3 (K)
open Low6969Prices (taylorLength)
open Low6969GeometryCut (auxCurves32 auxPoints32)
open K1_13 (Row shape extend chart atJet)
open K1_13_6 (Pieces GeoJets CurveSections HighMark intersectionIdeal markIdeal)
open K1_13_6_1 (HasMark anchorBox sectionDegree mark_surface mark_curve)
open Height2307CutEnvelope (SurfaceCut)
open P0_9_6_1 (canonicalChart)
open scoped BigOperators
private theorem assemble {Γ s f Q l} (curves : Finset (Ideal GeoJets))
    (marks : ∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) →
      ∃ C ∈ curves, C ≤ markIdeal (extend (s γ)))
    (recover : ∀ C : curves, ∃ (A B : Finset K) (d : ℕ),
      A ⊆ Γ ∧ CurveSections A s d ∧
      (∀ γ ∈ Γ, C.val ≤ markIdeal (extend (s γ)) → γ ∈ A ∪ B) ∧
      6*d ≤ sectionDegree C.val ((chart taylorLength (anchorBox f)).scale 6) ∧
      6*B.card ≤ sectionDegree C.val ((anchorBox f).scale 6) ∧
      6 ≤ sectionDegree C.val ((anchorBox f).scale 6))
    (hcurves : 32 * (∑ C ∈ curves,
      sectionDegree C ((chart taylorLength (anchorBox f)).scale 6)) ≤
      6 * auxCurves32 (shape f))
    (hpoints : 32 * (∑ C ∈ curves, sectionDegree C ((anchorBox f).scale 6)) ≤
      6 * auxPoints32 (shape f)) :
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧
      (∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * C.total ≤ auxCurves32 (shape f) ∧
      32 * (B.card + C.n) ≤ 2 * auxPoints32 (shape f) := by
  classical
  choose A B d hd using recover
  let e := curves.equivFin.symm
  let cover : Pieces Γ :=
    ⟨curves.card, fun i => A (e i), fun i => (hd (e i)).1, fun i => d (e i)⟩
  let points := curves.attach.biUnion B
  refine ⟨cover, points, fun i => (hd (e i)).2.1, ?_, ?_, ?_⟩
  · intro γ hγ hn
    obtain ⟨C, hC, hm⟩ := marks γ hγ hn
    let i := curves.equivFin ⟨C, hC⟩
    have hi : e i = ⟨C, hC⟩ := e.apply_symm_apply ⟨C, hC⟩
    rcases Finset.mem_union.mp ((hd ⟨C, hC⟩).2.2.1 γ hγ hm) with ha | hb
    · exact Finset.mem_union_left _ <| Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, by change γ ∈ A (e i); rwa [hi]⟩
    · exact Finset.mem_union_right _ <| Finset.mem_biUnion.mpr
        ⟨⟨C, hC⟩, Finset.mem_attach _ _, hb⟩
  · let degree := fun C => sectionDegree C ((chart taylorLength (anchorBox f)).scale 6)
    have hsum : 6 * cover.total ≤ ∑ C ∈ curves, degree C := by
      change 6 * (∑ i, d (e i)) ≤ _
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ i, degree (e i).val := Finset.sum_le_sum fun i _ => (hd (e i)).2.2.2.1
        _ = _ := by
          rw [← Finset.sum_attach curves degree]
          exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    change 32 * (∑ C ∈ curves, degree C) ≤ _ at hcurves
    omega
  · let degree := fun C => sectionDegree C ((anchorBox f).scale 6)
    have hB : 6 * points.card ≤ ∑ C ∈ curves, degree C := by
      calc
        _ ≤ 6 * (∑ C ∈ curves.attach, (B C).card) :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ C ∈ curves.attach, 6 * (B C).card := by rw [Finset.mul_sum]
        _ ≤ ∑ C ∈ curves.attach, degree C.val :=
          Finset.sum_le_sum fun C _ => (hd C).2.2.2.2.1
        _ = _ := Finset.sum_attach curves degree
    have hN : 6 * cover.n ≤ ∑ C ∈ curves, degree C := by
      calc
        _ = ∑ _ ∈ curves.attach, 6 := by simp [cover, Nat.mul_comm]
        _ ≤ ∑ C ∈ curves.attach, degree C.val :=
          Finset.sum_le_sum fun C _ => (hd C).2.2.2.2.2
        _ = _ := Finset.sum_attach curves degree
    change 32 * (∑ C ∈ curves, degree C) ≤ _ at hpoints
    omega
theorem proof : Low6969GeometryCut.c1 := by
  classical
  intro Γ s f Q l input
  let hs := (intersectionIdeal f Q).finite_minimalPrimes_of_isNoetherianRing
  let zs := hs.toFinset.filter (HasMark Γ s)
  have selected : ∀ surface ∈ zs, ∃ P, SurfaceCut f Q surface P ∧
      ∀ γ ∈ Γ, surface ≤ markIdeal (extend (s γ)) →
        ¬ HighMark f Q l (extend (s γ)) → atJet P (extend (s γ)) = 0 := by
    intro surface hZ
    rcases Finset.mem_filter.mp hZ with ⟨hbase, hmark⟩
    exact one_surface input (hs.mem_toFinset.mp hbase) hmark
  have all : ∀ surface, ∃ P : Row 4, surface ∈ zs →
      SurfaceCut f Q surface P ∧
      ∀ γ ∈ Γ, surface ≤ markIdeal (extend (s γ)) →
        ¬ HighMark f Q l (extend (s γ)) → atJet P (extend (s γ)) = 0 := by
    intro surface
    by_cases hz : surface ∈ zs
    · obtain ⟨P, hP⟩ := selected surface hz
      exact ⟨P, fun _ => hP⟩
    · exact ⟨0, fun h => (hz h).elim⟩
  choose P hP using all
  obtain ⟨cs, hdiv, hcurve, hc, hp⟩ := cut_curves f Q zs P input.small input.proper input.box
    (fun surface hZ => (hP surface hZ).1)
  let curves := cs.filter (HasMark Γ s)
  apply assemble curves
  · intro γ hγ hn
    obtain ⟨surface, hZ, hmark⟩ := mark_surface input.positive
      (input.onFactor γ hγ) (input.order γ hγ)
    have hz : surface ∈ zs := Finset.mem_filter.mpr ⟨hs.mem_toFinset.mpr hZ, γ, hγ, hmark⟩
    obtain ⟨C, hC, hcmark⟩ := mark_curve hmark ((hP surface hz).2 γ hγ hmark hn)
    exact ⟨C, Finset.mem_filter.mpr ⟨hdiv surface hz C hC, γ, hγ, hcmark⟩, hcmark⟩
  · intro C
    obtain ⟨hC, γ, hγ, hmark⟩ := Finset.mem_filter.mp C.property
    have hcf := hcurve C.val hC
    obtain ⟨r, hr, hsep⟩ := canonicalChart13 input.small.2.2.1.2.2
      (input.onFactor γ hγ) hcf.contains hmark
    exact recover_curve Γ s f C.val r input.small hcf hr hsep input.distinct input.degree
  · exact (Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))).trans hc
  · exact (Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))).trans hp
end
end Low6969GeometryCut_1
end
section
namespace Low6969GeometryCut_2
noncomputable section
open Polynomial
open P3 (K)
open Low6969Prices (physicalDegree primaryBox taylorLength)
open Low6969GeometryCut (membershipTest nextTest)
open K1_13 (Row Shape Geom shape extend chart liftedChart mixed32)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength CanonicalChart
  Invariant separant divisorIdeal partialFlow)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint Box4 Box5 graphBox)
open scoped BigOperators
structure Branch (f Q : Row 4) (l : ℕ) where
  surface : Ideal GeoJets
  r : ℕ
  base : (intersectionIdeal f Q).IsMinimalPrime surface
  high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface base.isPrime
  chart : CanonicalChart f surface r
  invariant : Invariant ((separant^[r]) f) surface
  proper : toGeneric (membershipTest ((separant^[r]) f)) ∉ surface
  curve : Ideal GeoJets
  divisor : (divisorIdeal surface (membershipTest ((separant^[r]) f))).IsMinimalPrime curve
  regularCurve : toGeneric (separant ((separant^[r]) f)) ∉ curve
  terminal :
    cycleLength (divisorIdeal surface (membershipTest ((separant^[r]) f))) curve
      divisor.isPrime ≠ 1 ∨ toGeneric (nextTest ((separant^[r]) f)) ∉ curve
namespace Branch
variable {f Q : Row 4} {l : ℕ} (b : Branch f Q l)
def g : Row 4 := (separant^[b.r]) f
def sigma : GeoJets := toGeneric (separant b.g)
def member : GeoJets := toGeneric (membershipTest b.g)
def next : GeoJets := toGeneric (nextTest b.g)
def Simple : Prop := cycleLength (divisorIdeal b.surface (membershipTest b.g))
  b.curve b.divisor.isPrime = 1
def weight : ℕ := by classical exact if b.Simple then 1 else 2
def Contains (p : JetPoint) : Prop :=
  b.curve ≤ RingHom.ker (MvPolynomial.eval p) ∧ MvPolynomial.eval p b.sigma ≠ 0
def graph : GeoJets5 :=
  MvPolynomial.rename Fin.castSucc (toGeneric (partialFlow b.g)) +
    MvPolynomial.C (4 : GeoField) * MvPolynomial.rename Fin.castSucc b.sigma *
      MvPolynomial.X (Fin.last 4)
abbrev Local := Localization.Away b.sigma
def localMap : GeoJets →+* b.Local := algebraMap GeoJets b.Local
def onGraph : GeoJets5 →+* b.Local :=
  MvPolynomial.eval₂Hom (b.localMap.comp MvPolynomial.C)
    (Fin.lastCases
      (b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹) * toGeneric (partialFlow b.g)) *
        IsLocalization.Away.invSelf b.sigma)
      (fun i => b.localMap (MvPolynomial.X i)))
def localCurve : Ideal b.Local := b.curve.map b.localMap
def regularEval (p : JetPoint) (h : b.Contains p) : b.Local →+* GeoField :=
  IsLocalization.Away.lift b.sigma (isUnit_iff_ne_zero.mpr h.2)
def liftedEval (p : JetPoint) (h : b.Contains p) : GeoJets5 →+* GeoField :=
  (b.regularEval p h).comp b.onGraph
end Branch
def budget4 (p : Shape) : ℕ :=
  mixed32 p primaryBox (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
def budget5 (p : Shape) : ℕ :=
  let a := liftedChart (taylorLength + 1) p
  let b := liftedChart (taylorLength + 2) p
  mixed32 p primaryBox a b + (taylorLength + 1) * mixed32 p primaryBox (graphBox p) b +
    (taylorLength + 2) * mixed32 p primaryBox (graphBox p) a
def Slice4 {f Q l} (b : Branch f Q l) (T : Finset JetPoint) : Prop :=
  T.card ≤ 1 ∨ ∃ D, Box4 (chart (taylorLength + 2) (shape f).chamber) D ∧
    D ∉ b.curve ∧ ∀ p ∈ T, MvPolynomial.eval p D = 0
def Slice5 {f Q l} (b : Branch f Q l) (T : Finset JetPoint) : Prop :=
  T.card ≤ 1 ∨ ∃ D, Box5 (liftedChart (taylorLength + 2) (shape f).chamber)
      (taylorLength + 2) D ∧ b.onGraph D ∉ b.localCurve ∧
    ∀ p ∈ T, ∀ h : b.Contains p, b.liftedEval p h D = 0
def Chart4 {f Q l} (b : Branch f Q l) : Prop :=
  let p := (shape f).chamber
  Box4 (chart (taylorLength + 1) p) b.member ∧
    Box4 (chart (taylorLength + 2) p) b.next ∧
    ∀ x a : K, ∃ D, Box4 (chart (taylorLength + 2) p) D ∧
      ∀ S : (Polynomial K), S.natDegree ≤ physicalDegree → b.Contains (actualPoint (extend S)) →
        (MvPolynomial.eval (actualPoint (extend S)) D = 0 ↔ S.eval x = a)
def Chart5 {f Q l} (b : Branch f Q l) : Prop :=
  let p := (shape f).chamber
  Box5 (graphBox p) 1 b.graph ∧
    ∃ E H,
      Box5 (liftedChart (taylorLength + 1) p) (taylorLength + 1) E ∧
      Associated (b.onGraph E) (b.localMap b.member) ∧
      Box5 (liftedChart (taylorLength + 2) p) (taylorLength + 2) H ∧
      Associated (b.onGraph H) (b.localMap b.next) ∧
      ∀ x a : K, ∃ D, Box5 (liftedChart (taylorLength + 2) p) (taylorLength + 2) D ∧
        ∀ S : (Polynomial K), S.natDegree ≤ physicalDegree → ∀ h : b.Contains (actualPoint (extend S)),
          (b.liftedEval (actualPoint (extend S)) h D = 0 ↔ S.eval x = a)
end
end Low6969GeometryCut_2
end
section
namespace Low6969GeometryCut_2
noncomputable section
open Polynomial
open Low6969Prices (physicalDegree)
open Low6969GeometryCut (MixedMark eval_membership_tests)
open K1_13 (Geom Row Shape shape InBox atJet jet indexDegree)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GenericField GeoField genericCoeffs toGeneric separant)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint)
open scoped BigOperators
theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
theorem eval_actualPoint (S : (Polynomial Geom)) (P : Row 4) :
    MvPolynomial.eval (actualPoint S) (toGeneric P) = genericCoeffs (atJet P S) := by
  rw [toGeneric, MvPolynomial.eval_map]
  change MvPolynomial.eval₂ genericCoeffs (⇑genericCoeffs ∘ jet S) P = _
  rw [← MvPolynomial.eval₂_comp]
  rfl
theorem branch_of_mixed {f Q l S} (h : MixedMark f Q l S) :
    ∃ b : Branch f Q l, b.Contains (actualPoint S) := by
  obtain ⟨surf, r, hz, hE, C, hC, hP, hterminal⟩ := h
  have hr : MvPolynomial.eval (actualPoint S) (toGeneric (separant ((separant^[r]) f))) ≠ 0 := by
    rw [eval_actualPoint]
    exact fun hzero => hz.regular (genericCoeffs_injective (by simpa using hzero))
  have hc : toGeneric (separant ((separant^[r]) f)) ∉ C := fun hmem => hr (hP hmem)
  let b : Branch f Q l :=
    ⟨surf, r, hz.base, hz.high, hz.chart, hz.invariant, hE, C, hC, hc, hterminal⟩
  exact ⟨b, hP, hr⟩
namespace Branch
variable {f Q : Row 4} {l : ℕ}
theorem eq_of_surface_curve {b c : Branch f Q l} (hs : b.surface = c.surface)
    (hc : b.curve = c.curve) : b = c := by
  have order (d e : Branch f Q l) (h : d.surface = e.surface) : ¬ d.r < e.r := by
    intro hlt
    have hmem := e.chart.2.1 (d.r + 1) (by omega)
    rw [← h, Function.iterate_succ_apply'] at hmem
    exact d.chart.2.2 hmem
  have hr : b.r = c.r := Nat.le_antisymm (Nat.le_of_not_gt (order c b hs.symm))
    (Nat.le_of_not_gt (order b c hs))
  cases b
  cases c
  cases hs
  cases hr
  cases hc
  rfl
theorem next_proper (b : Branch f Q l) (h : b.Simple) : b.next ∉ b.curve :=
  b.terminal.resolve_left (fun hne => hne h)
theorem g_actual (b : Branch f Q l) {S : (Polynomial Geom)}
    (h : b.Contains (actualPoint S)) : atJet b.g S = 0 :=
  K1_13_6_1.mem_markIdeal.mp
    (h.1 ((le_trans le_sup_left b.divisor.le) (b.chart.2.1 b.r le_rfl)))
theorem regular_actual (b : Branch f Q l) {S : (Polynomial Geom)}
    (h : b.Contains (actualPoint S)) : atJet (separant b.g) S ≠ 0 := by
  intro hz
  exact h.2 (by rw [Branch.sigma, eval_actualPoint, hz, map_zero])
theorem next_actual (b : Branch f Q l) {S : (Polynomial Geom)} (h : b.Contains (actualPoint S))
    (hd : S.natDegree ≤ physicalDegree) : MvPolynomial.eval (actualPoint S) b.next = 0 := by
  rw [next, eval_actualPoint, (eval_membership_tests _ _ (b.g_actual h) hd).2, map_zero]
theorem localMap_mem_localCurve_iff (b : Branch f Q l) (P : GeoJets) :
    b.localMap P ∈ b.localCurve ↔ P ∈ b.curve := by
  change algebraMap GeoJets b.Local P ∈ b.curve.map (algebraMap GeoJets b.Local) ↔ _
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers b.sigma) b.Local]
  constructor
  · rintro ⟨m, ⟨n, rfl⟩, hm⟩
    exact (b.divisor.isPrime.mem_or_mem hm).resolve_left
      (fun hpow => b.regularCurve (b.divisor.isPrime.mem_of_pow_mem n hpow))
  · intro hP
    exact ⟨1, (Submonoid.powers b.sigma).one_mem, by simpa using hP⟩
theorem regularEval_localMap (b : Branch f Q l) (p : JetPoint) (h : b.Contains p) (P : GeoJets) :
    b.regularEval p h (b.localMap P) = MvPolynomial.eval p P := by
  exact IsLocalization.Away.lift_eq b.sigma _ _
theorem lifted_proper_of_nonzero (b : Branch f Q l) (p : JetPoint) (h : b.Contains p)
    {D : GeoJets5} (hn : b.liftedEval p h D ≠ 0) : b.onGraph D ∉ b.localCurve := by
  have hk : b.localCurve ≤ RingHom.ker (b.regularEval p h) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change b.regularEval p h (b.localMap P) = 0
    rw [regularEval_localMap]
    exact h.1 hP
  exact fun hm => hn (hk hm)
theorem lifted_proper_of_associated (b : Branch f Q l) {D : GeoJets5} {P : GeoJets}
    (hD : Associated (b.onGraph D) (b.localMap P)) (hP : P ∉ b.curve) :
    b.onGraph D ∉ b.localCurve := by
  intro hmem
  exact hP ((b.localMap_mem_localCurve_iff _).mp (b.localCurve.mem_of_dvd hD.dvd hmem))
theorem lifted_zero_of_associated (b : Branch f Q l) {D : GeoJets5} {P : GeoJets}
    (hD : Associated (b.onGraph D) (b.localMap P)) {p : JetPoint} (h : b.Contains p)
    (hP : MvPolynomial.eval p P = 0) : b.liftedEval p h D = 0 := by
  obtain ⟨u, hu⟩ := hD
  have hm := congrArg (b.regularEval p h) hu
  rw [map_mul, regularEval_localMap, hP, mul_eq_zero] at hm
  exact hm.resolve_right (IsUnit.ne_zero (IsUnit.map (b.regularEval p h) u.isUnit))
end Branch
private theorem iterate_bound (w : Fin 4 → ℕ) (f : Row 4) (r : ℕ) :
    MvPolynomial.weightedTotalDegree w ((separant^[r]) f) ≤
      MvPolynomial.weightedTotalDegree w f := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (MvPolynomial.weightedTotalDegree_pderiv_le w 3 _).trans ih
open MvPolynomial in
theorem branch_box {f Q l} (b : Branch f Q l) : InBox (shape b.g) (shape f).chamber := by
  refine ⟨?_, ?_, ?_⟩
  · change b.g.totalDegree ≤ max f.totalDegree (indexDegree f)
    exact (by simpa only [Branch.g, weightedTotalDegree_one] using iterate_bound 1 f b.r :
      b.g.totalDegree ≤ f.totalDegree).trans (le_max_left _ _)
  · simpa only [Shape.chamber, shape, indexDegree_eq, Branch.g] using iterate_bound Fin.val f b.r
  · simpa only [Shape.chamber, shape, Branch.g, weightedTotalDegree_piSingle] using
      iterate_bound (Pi.single 3 1) f b.r
end
end Low6969GeometryCut_2
end
section
namespace Low6969GeometryCut_2
noncomputable section
open Polynomial MvPolynomial
open P3 (K)
open Low6969Prices (physicalDegree SmallFactor taylorLength)
open K1_13 (Row Shape Geom InBox embed extend shape chart atJet jet)
open K1_13_6 (GeoJets GeoField GenericField genericCoeffs evalGeneric toGeneric
  separant jetNumerator eval_jetNumerator)
open K1_13_6_2_1 (jet_fits oldBox_of_fits three_weights separant_pow_bound jet_bound)
open K1_13_7_1 (Chamber GeoFits shape_chamber weight_X_le weight_const_mul_le)
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private abbrev TaylorIndex := Fin taylorLength
private structure TaylorChart where
  denom : GeoJets
  numerator : TaylorIndex → GeoJets
private def TaylorChart.Fits (C : TaylorChart) (h : Shape) : Prop :=
  GeoFits C.denom h ∧ ∀ i, GeoFits (C.numerator i) h
private def TaylorChart.Recovers (C : TaylorChart) (S : (Polynomial Geom)) : Prop :=
  evalGeneric S C.denom ≠ 0 ∧
    ∀ i, evalGeneric S (C.numerator i) =
      evalGeneric S C.denom * genericCoeffs (hasseDeriv i.val S)
private abbrev AffineForm := GeoField × (TaylorIndex → GeoField)
private def TaylorChart.pullback (C : TaylorChart) (a : AffineForm) : GeoJets :=
  MvPolynomial.C a.1 * C.denom + ∑ i, MvPolynomial.C (a.2 i) * C.numerator i
private theorem TaylorChart.pullback_fits (C : TaylorChart) {h : Shape} (hC : C.Fits h) (a : AffineForm) :
    GeoFits (C.pullback a) h := by
  classical
  have hw (w : Fin 4 → ℕ) (d : ℕ) (hD : C.denom.weightedTotalDegree w ≤ d)
      (hN : ∀ i, (C.numerator i).weightedTotalDegree w ≤ d) :
      (C.pullback a).weightedTotalDegree w ≤ d := by
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.add_mem
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans hD)
    · apply Submodule.sum_mem
      intro i _
      exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans (hN i))
  refine ⟨?_, hw Fin.val h.j hC.1.2.1 (fun i => (hC.2 i).2.1), ?_⟩
  · simpa only [weightedTotalDegree_one] using hw 1 h.b
      (by simpa only [weightedTotalDegree_one] using hC.1.1)
      (fun i => by simpa only [weightedTotalDegree_one] using (hC.2 i).1)
  · simpa only [weightedTotalDegree_piSingle] using hw (Pi.single (3 : Fin 4) 1) h.t
      (by simpa only [weightedTotalDegree_piSingle] using hC.1.2.2)
      (fun i => by simpa only [weightedTotalDegree_piSingle] using (hC.2 i).2.2)
private def denominator (L : ℕ) (g : Row 4) : Row 4 :=
  separant g ^ (2 * L)
private def numerator (L : ℕ) (g : Row 4) (i : TaylorIndex) : Row 4 :=
  if hi : i.val < 4 then MvPolynomial.X ⟨i.val, hi⟩ * denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑i.val.factorial : Geom)⁻¹) *
      (separant g ^ (2 * (L - i.val)) * jetNumerator g i.val)
private def taylorChart (L : ℕ) (g : Row 4) : TaylorChart where
  denom := toGeneric (denominator L g)
  numerator i := toGeneric (numerator L g i)
private theorem numerator_bound {L : ℕ} (hL : taylorLength ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (i : TaylorIndex) :
    W w (numerator L g i) ≤ d₀ + 2 * L * (B - w 3) + L * Δ := by
  have hi : i.val ≤ L := i.isLt.le.trans hL
  unfold numerator
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (separant_pow_bound w hg _)).trans
        (Nat.le_add_right _ _))
  · apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ 2 * (L - i.val) * (B - w 3) + (w 0 + i.val * (2 * (B - w 3) + Δ)) :=
        Nat.add_le_add (separant_pow_bound w hg _) (jet_bound w Δ hshift hB hg i.val)
      _ = w 0 + 2 * (i.val + (L - i.val)) * (B - w 3) + i.val * Δ := by ring
      _ ≤ _ := by
        rw [Nat.add_sub_of_le hi]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hi)
private theorem chart_fits {L : ℕ} (hL : taylorLength ≤ L) {g : Row 4} {p : Shape}
    (hg : InBox (shape g) p) (hp : Chamber p) (ht : 0 < p.t) :
    (taylorChart L g).Fits (chart L p) := by
  constructor
  · apply three_weights hg hp ht
    intro w Δ d₀ B _ _ _ hB
    exact (separant_pow_bound w hB (2 * L)).trans (by omega)
  · intro i
    exact three_weights hg hp ht (fun w Δ d₀ _ hs hw hwB hB =>
      numerator_bound hL w Δ d₀ hs hw hwB hB i)
private theorem ordinary_eq_hasse (S : (Polynomial Geom)) (n : ℕ) :
    derivative^[n] S = Polynomial.C (n.factorial : Geom) * hasseDeriv n S := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
private theorem eval_generic (S : (Polynomial Geom)) (P : Row 4) :
    evalGeneric S (toGeneric P) = genericCoeffs (atJet P S) :=
  (MvPolynomial.map_eval genericCoeffs (jet S) P).symm
private theorem generic_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
private theorem chart_recovers {L : ℕ} (hL : taylorLength ≤ L) {g : Row 4} {S : (Polynomial Geom)}
    (hg : atJet g S = 0) (hr : atJet (separant g) S ≠ 0) : (taylorChart L g).Recovers S := by
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))) _ _
  constructor
  · change evalGeneric S (toGeneric (denominator L g)) ≠ 0
    rw [eval_generic]
    apply (map_ne_zero_iff _ generic_injective).mpr
    rw [hden]
    exact pow_ne_zero _ hr
  · intro i
    change evalGeneric S (toGeneric (numerator L g i)) =
      evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv i.val S)
    rw [eval_generic, eval_generic, ← map_mul]
    apply congrArg genericCoeffs
    unfold numerator
    split_ifs with hinit
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant g) S ^ (2 * (L - i.val)) *
        atJet (jetNumerator g i.val) S) = _
      rw [eval_jetNumerator _ _ hg, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (K1_13_7_1.factorial_cast_ne_zero
          (i.isLt.trans (by decide : taylorLength < K1.p))), map_one]
      have hpow : 2 * (L - i.val) + 2 * i.val = 2 * L := by
        have hi : i.val ≤ L := i.isLt.le.trans hL
        rw [← Nat.mul_add, Nat.sub_add_cancel hi]
      calc
        _ = (Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom)) *
            ((atJet (separant g) S ^ (2 * (L - i.val)) * atJet (separant g) S ^ (2 * i.val)) *
              hasseDeriv i.val S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]
private def constants : Geom →+* GeoField :=
  genericCoeffs.comp Polynomial.C
private def center : GeoField :=
  genericCoeffs Polynomial.X
private theorem eval_center (S : (Polynomial Geom)) : (S.map constants).eval center = genericCoeffs S := by
  rw [Polynomial.eval_map]
  change eval₂RingHom constants center S = genericCoeffs S
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [constants]
  · simp [center]
private theorem taylor_sum {S : (Polynomial Geom)} (hS : S.natDegree < taylorLength) (x : Geom) :
    (∑ i : TaylorIndex, (constants x - center) ^ i.val * genericCoeffs (hasseDeriv i.val S)) =
      constants (S.eval x) := by
  let T := (S.map constants).taylor center
  have hT : T.natDegree < taylorLength := by
    change ((S.map constants).taylor center).natDegree < taylorLength
    rw [natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt hS
  have hev : T.eval (constants x - center) = constants (S.eval x) := by
    simp [T, taylor_eval]
  rw [← hev, Polynomial.eval_eq_sum_range' hT, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  change _ = ((S.map constants).taylor center).coeff i.val * _
  rw [taylor_coeff, hasseDeriv_map, eval_center, mul_comm]
private def valueForm (x a : Geom) : AffineForm :=
  (-(constants a), fun i => (constants x - center) ^ i.val)
private theorem eval_value {C : TaylorChart} {S : (Polynomial Geom)}
    (h : C.Recovers S) (hd : S.natDegree < taylorLength) (x a : Geom) :
    evalGeneric S (C.pullback (valueForm x a)) = 0 ↔ S.eval x = a := by
  have evC (c : GeoField) : evalGeneric S (MvPolynomial.C c) = c := MvPolynomial.eval_C _
  have hsum :
      (∑ i : TaylorIndex, (constants x - center) ^ i.val *
        (evalGeneric S C.denom * genericCoeffs (hasseDeriv i.val S))) =
      evalGeneric S C.denom * constants (S.eval x) := by
    rw [← taylor_sum hd x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  have heval : evalGeneric S (C.pullback (valueForm x a)) =
      evalGeneric S C.denom * (constants (S.eval x) - constants a) := by
    simp only [TaylorChart.pullback, valueForm, map_add, map_sum, map_mul, evC, h.2, hsum]
    ring
  have hconst : Function.Injective constants := generic_injective.comp Polynomial.C_injective
  rw [heval, mul_eq_zero, or_iff_right h.1, sub_eq_zero, hconst.eq_iff]
theorem chart4 {f Q l} (hf : SmallFactor f) (b : Branch f Q l) : Chart4 b := by
  have hg := branch_box b
  have hp := shape_chamber f
  have ht : 0 < (shape f).chamber.t := hf.2.1
  refine ⟨oldBox_of_fits (jet_fits hg hp ht (Nat.le_succ _)),
    oldBox_of_fits (jet_fits hg hp ht (Nat.le_succ _)), ?_⟩
  intro x a
  let L := taylorLength + 2
  let C := taylorChart L b.g
  have hL : taylorLength ≤ L := Nat.le_add_right _ _
  have hfit : C.Fits (chart L (shape f).chamber) := chart_fits hL hg hp ht
  refine ⟨C.pullback (valueForm (embed x) (embed a)),
    oldBox_of_fits (C.pullback_fits hfit _), ?_⟩
  intro S hd hpoint
  have hdegree : (extend S).natDegree < taylorLength :=
    Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans hd)
  change evalGeneric (extend S) (C.pullback (valueForm (embed x) (embed a))) = 0 ↔ _
  rw [eval_value (chart_recovers hL (b.g_actual hpoint) (b.regular_actual hpoint)) hdegree,
    Polynomial.eval_map_apply, embed.injective.eq_iff]
end
end Low6969GeometryCut_2
end
section
namespace Low6969GeometryCut_2
noncomputable section
open Polynomial
open P3 (K)
open Low6969Prices (SmallFactor primaryBox taylorLength)
open Low6969GeometryCut (MixedMark)
open K1_13 (Row Shape shape extend embed InBox chart liftedChart)
open K1_13_6 (Pieces CurveSections)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand Box4 Box5 graphBox)
open scoped BigOperators
def c1 : Prop :=
  ∀ f Q l, SmallFactor f → ∀ b : Branch f Q l, Chart5 b
def c2 : Prop :=
  ∀ f Q l, SmallFactor f → ¬ f ∣ Q → InBox (shape Q) primaryBox → 0 < l →
    ∀ (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint),
      (∀ b ∈ F, Box4 (chart (taylorLength + 1) (shape f).chamber) b.member ∧
        (∀ p ∈ T b, b.Contains p) ∧ Slice4 b (T b)) →
      32 * l * (∑ b ∈ F, b.weight * (T b).card) ≤ budget4 (shape f).chamber
def c3 : Prop :=
  ∀ f Q l, SmallFactor f → ¬ f ∣ Q → InBox (shape Q) primaryBox → 0 < l →
    ∀ (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint),
      (∀ b ∈ F, Box5 (graphBox (shape f).chamber) 1 b.graph ∧
        (∃ E, Box5 (liftedChart (taylorLength + 1) (shape f).chamber) (taylorLength + 1) E ∧
          Associated (b.onGraph E) (b.localMap b.member)) ∧
        (∀ p ∈ T b, b.Contains p) ∧ Slice5 b (T b)) →
      32 * l * (∑ b ∈ F, b.weight * (T b).card) ≤ budget5 (shape f).chamber
theorem of_children (h5chart : c1) (h4budget : c2) (h5budget : c3) : Low6969GeometryCut.c2 := by
  classical
  intro Γ s f Q l input
  let point (γ : K) := actualPoint (extend (s γ))
  let marked := Γ.filter (fun γ => MixedMark f Q l (extend (s γ)))
  let assign (γ : marked) : Branch f Q l :=
    Classical.choose (branch_of_mixed (Finset.mem_filter.mp γ.property).2)
  let branches := marked.attach.image assign
  let labels (b : Branch f Q l) :=
    marked.filter (fun γ => ∃ h : γ ∈ marked, assign ⟨γ, h⟩ = b)
  have label_sub (b : Branch f Q l) : labels b ⊆ Γ :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have contains_label (b : Branch f Q l) (γ : K) (hγ : γ ∈ labels b) :
      b.Contains (point γ) := by
    obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hγ).2
    exact Classical.choose_spec (branch_of_mixed (Finset.mem_filter.mp h).2)
  have labels_nonempty (b : Branch f Q l) (hb : b ∈ branches) : (labels b).Nonempty := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨γ.val, Finset.mem_filter.mpr ⟨γ.property, γ.property, rfl⟩⟩
  have available (b : Branch f Q l) : ∃ T ⊆ labels b,
      (b.Simple → T = labels b) ∧
      (b ∈ branches → ¬ b.Simple → 0 < T.card ∧ CurveSections (labels b) s T.card ∧
        Demand (labels b) s T) := by
    by_cases hs : b.Simple
    · exact ⟨labels b, Finset.Subset.rfl, fun _ => rfl, fun _ hn => (hn hs).elim⟩
    by_cases hb : b ∈ branches
    · obtain ⟨T, hsub, hd⟩ := maximal_demand (labels b) s (labels_nonempty b hb)
      exact ⟨T, hsub, fun h => (hs h).elim, fun _ _ => hd⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => (hs h).elim, fun h _ => (hb h).elim⟩
  choose demanded demand_sub demand_simple demand_multiple using available
  let points (b : Branch f Q l) := (demanded b).image point
  have points_card (b : Branch f Q l) : (points b).card = (demanded b).card := by
    apply Finset.card_image_of_injOn
    intro γ hγ δ hδ heq
    exact input.distinct (label_sub b (demand_sub b hγ)) (label_sub b (demand_sub b hδ))
      (Polynomial.map_injective embed embed.injective (actualPoint_injective heq))
  have points_on (b : Branch f Q l) (p : JetPoint) (hp : p ∈ points b) : b.Contains p := by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    exact contains_label b γ (demand_sub b hγ)
  have points_next (b : Branch f Q l) (p : JetPoint) (hp : p ∈ points b) :
      MvPolynomial.eval p b.next = 0 := by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    apply b.next_actual (contains_label b γ (demand_sub b hγ))
    simpa only [Polynomial.natDegree_map] using input.degree γ (label_sub b (demand_sub b hγ))
  have bound4 := h4budget f Q l input.small input.proper input.box input.positive branches points
    (by
      intro b hb
      obtain ⟨hmember, hnext, hvalue⟩ := chart4 input.small b
      refine ⟨hmember, points_on b, ?_⟩
      by_cases hs : b.Simple
      · exact Or.inr ⟨b.next, hnext, b.next_proper hs, points_next b⟩
      rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
      · exact Or.inl (by rw [points_card, hone])
      obtain ⟨D, hD, hEval⟩ := hvalue x a
      obtain ⟨δ, hδ, hδvalue⟩ := hwit
      have hδon := contains_label b δ hδ
      have hproper : D ∉ b.curve := fun hmem =>
        hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp (hδon.1 hmem))
      refine Or.inr ⟨D, hD, hproper, ?_⟩
      intro p hp
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
      have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
      exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ)))
        (contains_label b γ (demand_sub b hγ))).mpr hvalueγ)
  have bound5 := h5budget f Q l input.small input.proper input.box input.positive branches points
    (by
      intro b hb
      obtain ⟨hgraph, E, H, hE, hEeq, hH, hHeq, hvalue⟩ := h5chart f Q l input.small b
      refine ⟨hgraph, ⟨E, hE, hEeq⟩, points_on b, ?_⟩
      by_cases hs : b.Simple
      · exact Or.inr ⟨H, hH, b.lifted_proper_of_associated hHeq (b.next_proper hs),
          fun p hp hon => b.lifted_zero_of_associated hHeq hon (points_next b p hp)⟩
      rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
      · exact Or.inl (by rw [points_card, hone])
      obtain ⟨D, hD, hEval⟩ := hvalue x a
      obtain ⟨δ, hδ, hδvalue⟩ := hwit
      have hδon := contains_label b δ hδ
      refine Or.inr ⟨D, hD, b.lifted_proper_of_nonzero (point δ) hδon ?_, ?_⟩
      · exact fun hzero => hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp hzero)
      · intro p hp hon
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
        have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
        exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ))) hon).mpr hvalueγ)
  let simple := branches.filter Branch.Simple
  let multiple := branches.filter (fun b => ¬ b.Simple)
  let e := multiple.equivFin
  let C : Pieces Γ :=
    { n := multiple.card
      piece := fun i => labels (e.symm i).val
      subset := fun i => label_sub (e.symm i).val
      degree := fun i => (demanded (e.symm i).val).card }
  let B := simple.biUnion labels
  have hmultiple (i : Fin C.n) := Finset.mem_filter.mp (e.symm i).property
  refine ⟨C, B,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).2.1,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).1, ?_, ?_⟩
  · intro γ hγ hm
    have hmark : γ ∈ marked := Finset.mem_filter.mpr ⟨hγ, hm⟩
    let b := assign ⟨γ, hmark⟩
    have hb : b ∈ branches := Finset.mem_image.mpr ⟨_, Finset.mem_attach _ _, rfl⟩
    have hlabel : γ ∈ labels b := Finset.mem_filter.mpr ⟨hmark, hmark, rfl⟩
    by_cases hs : b.Simple
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hs⟩, hlabel⟩)
    have hbm : b ∈ multiple := Finset.mem_filter.mpr ⟨hb, hs⟩
    apply Finset.mem_union_left _
    refine Finset.mem_biUnion.mpr ⟨e ⟨b, hbm⟩, Finset.mem_univ _, ?_⟩
    change γ ∈ labels (e.symm (e ⟨b, hbm⟩)).val
    simpa only [Equiv.symm_apply_apply] using hlabel
  · have htotal : C.total = ∑ b ∈ multiple, (demanded b).card := by
      calc
        C.total = ∑ b : multiple, (demanded b.val).card :=
          Equiv.sum_comp e.symm (fun b : multiple => (demanded b.val).card)
        _ = _ := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_attach multiple (fun b => (demanded b).card)
    have hsimple : (∑ b ∈ simple, b.weight * (points b).card) =
        ∑ b ∈ simple, (labels b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, demand_simple b hs, Branch.weight, ite_eq_left hs, one_mul]
    have hmult : (∑ b ∈ multiple, b.weight * (points b).card) = 2 * C.total := by
      rw [htotal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, Branch.weight, ite_eq_right hs]
    have hpart : (∑ b ∈ simple, b.weight * (points b).card) +
        (∑ b ∈ multiple, b.weight * (points b).card) =
        ∑ b ∈ branches, b.weight * (points b).card :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hB : B.card ≤ ∑ b ∈ simple, (labels b).card := Finset.card_biUnion_le
    have hpay : 2 * C.total + B.card ≤ ∑ b ∈ branches, b.weight * (points b).card := by
      rw [← hpart, hsimple, hmult, Nat.add_comm (∑ b ∈ simple, (labels b).card)]
      exact Nat.add_le_add_left hB _
    change _ ≤ min (budget4 (shape f).chamber) (budget5 (shape f).chamber)
    exact (Nat.mul_le_mul_left (32 * l) hpay).trans (le_min bound4 bound5)
end
end Low6969GeometryCut_2
end
section
namespace Low6969GeometryCut_2_1
noncomputable section
open Polynomial MvPolynomial
open Low6969Prices (SmallFactor)
open Low6969GeometryCut_2 (Branch branch_box)
open K1_13 (Geom Row Shape InBox shape indexDegree liftedChart)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GeoField genericCoeffs toGeneric separant partialFlow jetNumerator)
open K1_13_6_2 (GeoJets5 Box5 graphBox)
open K1_13_6_2_2 (lift4 generic5 rawGraph numerator denominator padded)
open K1_13_6_2_2_2 (Chart incl S invS S_mul_invS negQuarter q constants W
  graphMap graphMap_lift graphMap_X_last)
open scoped BigOperators
open K1_13_6_2_2_2 (compare_numerators)
open K1_13_6_2_2_1 (support_bounds topWeight fifthWeight box_of_weights)
variable {f Q : Row 4} {l : ℕ}
@[simp] theorem onGraph_C (b : Branch f Q l) (a : GeoField) :
    b.onGraph (MvPolynomial.C a) = b.localMap (MvPolynomial.C a) := by
  simp [Branch.onGraph]
theorem onGraph_lift4 (b : Branch f Q l) (P : Row 4) :
    b.onGraph (generic5 (lift4 P)) = b.localMap (toGeneric P) := by
  let lift := (MvPolynomial.rename Fin.castSucc : GeoJets →ₐ[GeoField] GeoJets5).toRingHom
  have h : b.onGraph.comp lift = b.localMap := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lift]
    · intro i
      simp [lift, Branch.onGraph]
  rw [MvPolynomial.map_rename]
  exact DFunLike.congr_fun h (toGeneric P)
theorem denominator_onGraph (b : Branch f Q l) (k : ℕ) :
    b.onGraph (generic5 (denominator b.g k)) = b.localMap b.sigma ^ k := by
  simp only [denominator, map_pow, onGraph_lift4, Branch.sigma]
private def toBranch (b : Branch f Q l) : Chart b.g →+* b.Local :=
  IsLocalization.Away.lift (separant b.g)
    (g := b.localMap.comp (MvPolynomial.map genericCoeffs))
    (IsLocalization.Away.algebraMap_isUnit b.sigma)
@[simp] private theorem toBranch_incl (b : Branch f Q l) (P : Row 4) :
    toBranch b (incl b.g P) = b.localMap (toGeneric P) :=
  IsLocalization.Away.lift_eq _ _ _
private theorem toBranch_inv (b : Branch f Q l) :
    toBranch b (invS b.g) = IsLocalization.Away.invSelf b.sigma := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := b.Local) b.sigma).mul_left_cancel
  rw [IsLocalization.Away.mul_invSelf]
  have hm := congrArg (toBranch b) (S_mul_invS b.g)
  simpa only [S, map_mul, toBranch_incl, map_one, Branch.sigma, Branch.localMap] using hm
private theorem toBranch_graph (b : Branch f Q l) (P : Row 5) :
    toBranch b (graphMap b.g P) = b.onGraph (generic5 P) := by
  have hold (U : Row 4) : toBranch b (graphMap b.g (lift4 U)) =
      b.onGraph (generic5 (lift4 U)) := by
    rw [graphMap_lift, toBranch_incl, onGraph_lift4]
  have h : (toBranch b).comp (graphMap b.g) = b.onGraph.comp generic5 := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa only [MvPolynomial.rename_C, RingHom.comp_apply] using hold (C a)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hq : genericCoeffs (Polynomial.C negQuarter) = -(4 : GeoField)⁻¹ := by
          change (genericCoeffs.comp Polynomial.C) negQuarter = _
          rw [negQuarter, map_neg, map_inv₀, map_ofNat]
        change toBranch b (graphMap b.g (MvPolynomial.X (Fin.last 4))) =
          b.onGraph (generic5 (MvPolynomial.X (Fin.last 4)))
        rw [graphMap_X_last, MvPolynomial.map_X, Branch.onGraph, eval₂Hom_X',
          Fin.lastCases_last]
        simp only [W, q, constants, RingHom.comp_apply, map_mul, toBranch_incl, toBranch_inv,
          toGeneric, MvPolynomial.map_C, hq]
      · simpa only [MvPolynomial.rename_X, RingHom.comp_apply] using hold (MvPolynomial.X j)
  exact DFunLike.congr_fun h P
theorem compare_onGraph (b : Branch f Q l) (k : ℕ) :
    b.onGraph (generic5 (numerator b.g k)) * b.localMap b.sigma ^ (k + 8) =
      b.localMap (toGeneric (jetNumerator b.g (k + 4))) := by
  have h := congrArg (toBranch b) (compare_numerators b.g k)
  simpa only [map_mul, map_pow, toBranch_graph, S, toBranch_incl, Branch.sigma] using h
private theorem generic_rawGraph (b : Branch f Q l) :
    generic5 (rawGraph b.g) = b.graph := by
  simp [rawGraph, Branch.graph, Branch.sigma, toGeneric, MvPolynomial.map_rename, map_ofNat]
local notation "wtDegree" => MvPolynomial.weightedTotalDegree
theorem chart_support (hf : SmallFactor f) (branch : Branch f Q l) :
    let p := (shape f).chamber
    Box5 (graphBox p) 1 branch.graph ∧
      ∀ k : ℕ, Box5 (liftedChart (k + 5) p) (k + 5) (generic5 (denominator branch.g k)) ∧
        ∀ i ≤ k + 4, Box5 (liftedChart (k + 5) p) (k + 5) (generic5 (padded branch.g k i)) := by
  let p := (shape f).chamber
  change Box5 (graphBox p) 1 branch.graph ∧ _
  have hp := K1_13_7_1.shape_chamber f
  have ht : 1 ≤ p.t := hf.2.1
  have hj : 3 ≤ p.j := by have := hp.2; change 3 * p.t ≤ p.j at this; omega
  have hb : 1 ≤ p.b := by have := hp.1; change p.j ≤ p.b at this; omega
  have hG : InBox (shape branch.g) p := branch_box branch
  change branch.g.totalDegree ≤ p.b ∧ indexDegree branch.g ≤ p.j ∧
    branch.g.degreeOf 3 ≤ p.t at hG
  have hTotal : wtDegree ((1 : Fin 5 → ℕ) ∘ Fin.castSucc) branch.g ≤ p.b := by
    change wtDegree (1 : Fin 4 → ℕ) branch.g ≤ p.b
    rw [weightedTotalDegree_one]
    exact hG.1
  have hIndex : wtDegree ((Fin.val : Fin 5 → ℕ) ∘ Fin.castSucc) branch.g ≤ p.j := by
    change wtDegree (Fin.val : Fin 4 → ℕ) branch.g ≤ p.j
    rw [← indexDegree_eq]
    exact hG.2.1
  have hTop : wtDegree (topWeight ∘ Fin.castSucc) branch.g ≤ p.t := by
    have hw : topWeight ∘ Fin.castSucc = (Pi.single (3 : Fin 4) 1 : Fin 4 → ℕ) := by
      funext i
      simp [topWeight]
    rw [hw, weightedTotalDegree_piSingle]
    exact hG.2.2
  have hFifth : wtDegree (fifthWeight ∘ Fin.castSucc) branch.g ≤ 0 := by
    have hw : fifthWeight ∘ Fin.castSucc = (0 : Fin 4 → ℕ) := by
      funext i
      change (Pi.single (Fin.last 4) 1 : Fin 5 → ℕ) i.castSucc = 0
      rw [Pi.single_apply, ite_eq_right (Fin.castSucc_ne_last i)]
    rw [hw]
    apply Finset.sup_le
    intro m _
    simp [Finsupp.weight_eq_sum]
  have wt := support_bounds (1 : Fin 5 → ℕ) 0 (fun _ => le_rfl) (by decide)
    (fun _ => le_rfl) hTotal hb
  have wi := support_bounds (Fin.val : Fin 5 → ℕ) 1 (fun i => by rfl) (by decide)
    (fun i => i.isLt.le) hIndex hj
  have ws := support_bounds topWeight 1 (fun i => by fin_cases i <;> decide) (by decide)
    (fun i => by fin_cases i <;> decide) hTop ht
  have wf := support_bounds fifthWeight 1 (fun i => by fin_cases i <;> decide) (by decide)
    (fun i => by fin_cases i <;> decide) hFifth (by decide)
  constructor
  · rw [← generic_rawGraph branch]
    apply box_of_weights
    · exact (wt.1.trans (by simp only [add_zero]; exact le_max_left _ _))
    · exact wi.1
    · exact ws.1
    · exact wf.1
  · intro k
    have hJ : p.j - 3 + 1 = p.j - 2 := by omega
    have hT : p.t - 1 + 1 = p.t := by omega
    have wTotal := wt.2 k
    have wIndex := wi.2 k
    have wTop := ws.2 k
    have wFifth : wtDegree fifthWeight (denominator branch.g k) ≤ 1 + k ∧
        (∀ i ≤ k + 4, wtDegree fifthWeight (padded branch.g k i) ≤ 1 + k) := by
      simpa only [show fifthWeight (Fin.last 4) = 1 by decide,
        show fifthWeight ((3 : Fin 4).castSucc) = 0 by decide, Nat.sub_zero, zero_add, Nat.mul_one]
        using wf.2 k
    simp only [Pi.one_apply, add_zero] at wTotal
    change wtDegree Fin.val (denominator branch.g k) ≤ 4 + k * (p.j - 3 + 1) ∧ _ at wIndex
    change wtDegree topWeight (denominator branch.g k) ≤ 2 + k * (p.t - 1 + 1) ∧ _ at wTop
    simp only [show (Fin.last 4).val = 4 by rfl, show ((3 : Fin 4).castSucc).val = 3 by rfl,
      show topWeight (Fin.last 4) = 2 by decide, show topWeight ((3 : Fin 4).castSucc) = 1 by decide,
      hJ, hT] at wIndex wTop
    have box (P : Row 5) (h1 : wtDegree 1 P ≤ 1 + k * (p.b - 1))
        (h2 : wtDegree Fin.val P ≤ 4 + k * (p.j - 2)) (h3 : wtDegree topWeight P ≤ 2 + k * p.t)
        (h4 : wtDegree fifthWeight P ≤ 1 + k) :
        Box5 (liftedChart (k + 5) p) (k + 5) (generic5 P) := by
      simpa only [liftedChart, Nat.add_sub_cancel] using
        box_of_weights P (h1.trans (le_max_left _ (4 + k * (p.j - 2)))) h2 h3
          (h4.trans (by omega : 1 + k ≤ k + 5))
    exact ⟨box _ wTotal.1 wIndex.1 wTop.1 wFifth.1,
      fun i hi => box _ (wTotal.2 i hi) (wIndex.2 i hi) (wTop.2 i hi) (wFifth.2 i hi)⟩
end
end Low6969GeometryCut_2_1
end
section
namespace Low6969GeometryCut_2_1
noncomputable section
open Polynomial
open P3 (K)
open Low6969Prices (taylorLength)
open Low6969GeometryCut_2 (Branch)
open K1_13 (Geom Row embed extend atJet jet)
open K1_13_6 (GeoField genericCoeffs toGeneric separant jetNumerator eval_jetNumerator)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint)
open K1_13_6_2_2 (lift4 generic5 numerator denominator padded padded_last)
open scoped BigOperators
open K1_13_6_2_2 (ordinary ordinary_eq_hasse const centre taylorScalar factorial_ne_zero box_C_mul box_sum box_sub)
variable {f Q : Row 4} {l : ℕ}
theorem numerator_associated (b : Branch f Q l) (k : ℕ) :
    Associated (b.onGraph (generic5 (numerator b.g k)))
      (b.localMap (toGeneric (jetNumerator b.g (k+4)))) := by
  rw [← compare_onGraph b k]
  exact associated_mul_unit_right _ _ (IsLocalization.Away.algebraMap_pow_isUnit b.sigma (k+8))
private theorem eval_const (b : Branch f Q l) (p : JetPoint) (h : b.Contains p) (a : GeoField) :
    b.liftedEval p h (MvPolynomial.C a) = a := by
  simp [Branch.liftedEval, b.regularEval_localMap]
private theorem eval_denominator (b : Branch f Q l) (p : JetPoint) (h : b.Contains p) (k : ℕ) :
    b.liftedEval p h (generic5 (denominator b.g k)) = MvPolynomial.eval p b.sigma ^ k := by
  simp [Branch.liftedEval, denominator_onGraph, b.regularEval_localMap]
private theorem eval_padded (b : Branch f Q l) {T : (Polynomial Geom)}
    (h : b.Contains (actualPoint T)) (k i : ℕ) (hi : i ≤ k + 4) :
    b.liftedEval (actualPoint T) h (generic5 (padded b.g k i)) =
      ordinary T i * MvPolynomial.eval (actualPoint T) b.sigma ^ k := by
  by_cases hi4 : i < 4
  · rw [padded, dite_eq_left hi4]
    simp only [map_mul, MvPolynomial.map_C, eval_const, eval_denominator]
    have he : b.liftedEval (actualPoint T) h (generic5 (lift4 (MvPolynomial.X ⟨i, hi4⟩))) =
        genericCoeffs (hasseDeriv i T) := by
      change b.regularEval (actualPoint T) h (b.onGraph (generic5 (lift4 (MvPolynomial.X _)))) = _
      rw [onGraph_lift4, b.regularEval_localMap]
      simp [toGeneric, actualPoint, jet]
    rw [he]
    unfold ordinary
    rw [ordinary_eq_hasse, map_mul]
  · rw [padded, dite_eq_right hi4]
    simp only [map_mul, eval_denominator]
    let j := i - 4
    have hj : j + 4 = i := by dsimp only [j]; omega
    have hjk : j ≤ k := by omega
    have hg : atJet b.g T = 0 := b.g_actual h
    let s := MvPolynomial.eval (actualPoint T) b.sigma
    let e := b.regularEval (actualPoint T) h
    have he := congrArg e (compare_onGraph b j)
    simp only [map_mul, map_pow, e, b.regularEval_localMap] at he
    change b.liftedEval (actualPoint T) h (generic5 (numerator b.g j)) * s ^ (j+8) =
      MvPolynomial.eval (actualPoint T) (toGeneric (jetNumerator b.g (j+4))) at he
    have hEval (P : Row 4) :
        MvPolynomial.eval (actualPoint T) (toGeneric P) = genericCoeffs (atJet P T) :=
      (MvPolynomial.map_eval genericCoeffs (jet T) P).symm
    rw [hEval, eval_jetNumerator _ _ hg, map_mul, map_pow, hj] at he
    have hs : genericCoeffs (atJet (separant b.g) T) = s := (hEval _).symm
    rw [hs, show 2*i = j + (j+8) by omega, pow_add s j (j+8)] at he
    have hnum : b.liftedEval (actualPoint T) h (generic5 (numerator b.g j)) =
        ordinary T i * s ^ j := by
      apply mul_right_cancel₀ (pow_ne_zero (j+8) h.2)
      exact he.trans (show s ^ j * s ^ (j+8) * ordinary T i =
        (ordinary T i * s ^ j) * s ^ (j+8) by ac_rfl)
    change b.liftedEval (actualPoint T) h (generic5 (numerator b.g j)) * s ^ (k-j) =
      ordinary T i * s ^ k
    rw [hnum, mul_assoc, ← pow_add, Nat.add_sub_of_le hjk]
private theorem eval_taylor {M : ℕ} (hM : M ≤ K1.p) (T : (Polynomial Geom)) (hT : T.natDegree < M) (x : Geom) :
    (∑ i ∈ Finset.range M, taylorScalar x i * ordinary T i) = const (T.eval x) := by
  have hd : (Polynomial.taylor centre (T.map const)).natDegree < M := by
    rw [Polynomial.natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt hT
  rw [← Polynomial.eval_map_apply const x, ← Polynomial.taylor_eval_sub centre,
    Polynomial.eval_eq_sum_range' hd]
  apply Finset.sum_congr rfl
  intro i hi
  have hcent (P : (Polynomial Geom)) : (P.map const).eval centre = genericCoeffs P := by
    rw [Polynomial.eval_map]
    simpa only [Polynomial.eval₂_C_X] using
      (Polynomial.hom_eval₂ P Polynomial.C genericCoeffs Polynomial.X).symm
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, hcent]
  have hord : ordinary T i = (i.factorial : GeoField) * genericCoeffs (hasseDeriv i T) := by
    unfold ordinary
    rw [ordinary_eq_hasse, map_mul, Polynomial.C_eq_natCast, map_natCast]
  have hn : i < K1.p :=
    (Finset.mem_range.mp hi).trans_le hM
  rw [hord, taylorScalar]
  calc
    _ = ((i.factorial : GeoField)⁻¹ * (i.factorial : GeoField)) *
          (genericCoeffs (hasseDeriv i T) * (const x - centre)^i) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (factorial_ne_zero hn), one_mul]
def valuePolynomial (M : ℕ) (g : Row 4) (k : ℕ) (x a : K) : GeoJets5 :=
  (∑ i ∈ Finset.range M, MvPolynomial.C (taylorScalar (embed x) i) *
      generic5 (padded g k i)) -
    MvPolynomial.C (const (embed a)) * generic5 (denominator g k)
theorem value_section {M : ℕ} (hM : M ≤ K1.p) (b : Branch f Q l) (k : ℕ)
    (hk : M ≤ k + 5) (x a : K) :
    ∀ S : (Polynomial K), S.natDegree < M → ∀ h : b.Contains (actualPoint (extend S)),
      b.liftedEval (actualPoint (extend S)) h (valuePolynomial M b.g k x a) = 0 ↔ S.eval x = a := by
  intro S hS h
  let p := actualPoint (extend S)
  let e := b.liftedEval p h
  let s := MvPolynomial.eval p b.sigma
  have hsum :
      (∑ i ∈ Finset.range M,
        e (MvPolynomial.C (taylorScalar (embed x) i) * generic5 (padded b.g k i))) =
        const ((extend S).eval (embed x)) * s^k := by
    have hdeg : (extend S).natDegree < M := by
      rw [Polynomial.natDegree_map]
      exact hS
    rw [← eval_taylor hM (extend S) hdeg (embed x), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hki : i ≤ k + 4 := by have := Finset.mem_range.mp hi; omega
    simp only [map_mul, e, eval_const, p, eval_padded b h k i hki, s, mul_assoc]
  change e (valuePolynomial M b.g k x a) = 0 ↔ _
  unfold valuePolynomial
  rw [map_sub, map_sum, hsum, map_mul, eval_const, eval_denominator]
  change const ((extend S).eval (embed x)) * s^k - const (embed a) * s^k = 0 ↔ _
  rw [Polynomial.eval_map_apply, ← sub_mul, mul_eq_zero,
    or_iff_left (pow_ne_zero k h.2), sub_eq_zero]
  exact ⟨fun he => embed.injective (const.injective he), fun he => congrArg (const.comp embed) he⟩
theorem proof : Low6969GeometryCut_2.c1 := by
  intro f Q l hf b
  obtain ⟨hg, hbox⟩ := chart_support hf b
  let k := taylorLength - 4
  have hfour : 4 ≤ taylorLength := (by decide : 4 ≤ 133379)
  have hk : k + 4 = taylorLength := Nat.sub_add_cancel hfour
  have hk' : (k + 1) + 4 = taylorLength + 1 := by
    rw [Nat.add_right_comm, hk]
  have hE := (hbox k).2 (k + 4) le_rfl
  have hH := (hbox (k + 1)).2 ((k + 1) + 4) le_rfl
  rw [padded_last] at hE hH
  have hm := numerator_associated b k
  have hn := numerator_associated b (k + 1)
  rw [hk] at hm
  rw [hk'] at hn
  refine ⟨hg, generic5 (numerator b.g k), generic5 (numerator b.g (k + 1)),
    hE, hm, hH, hn, ?_⟩
  intro x a
  have hM : taylorLength ≤ K1.p := (by decide : 133379 ≤ 0x7f000001)
  have hlen : taylorLength ≤ (k + 1) + 5 := calc
    taylorLength ≤ taylorLength + 1 := Nat.le_succ _
    _ = (k + 1) + 4 := hk'.symm
    _ ≤ (k + 1) + 5 := Nat.le_succ _
  refine ⟨valuePolynomial taylorLength b.g (k + 1) x a, ?_, ?_⟩
  · unfold valuePolynomial
    apply box_sub
    · apply box_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hki : i ≤ (k + 1) + 4 := by omega
      exact box_C_mul ((hbox (k + 1)).2 i hki) _
    · exact box_C_mul (hbox (k + 1)).1 _
  · intro T hT h
    exact value_section hM b (k + 1) hlen x a T (Nat.lt_succ_of_le hT) h
end
end Low6969GeometryCut_2_1
end
section
namespace Low6969GeometryCut_2_2
noncomputable section
open Low6969Prices (SmallFactor primaryBox taylorLength)
open Low6969GeometryCut (membershipTest)
open Low6969GeometryCut_2 (Branch Slice4 budget4)
open K1_13 (Row Shape shape chart mixed32 volume32 difference)
open K1_13_6 (GeoJets GeoField toGeneric divisorIdeal cycleLength intersectionIdeal separant)
open K1_13_6_2 (JetPoint Box4)
open K1_13_6_2_3 (ChamberBox dimension capCoeff polarize mixedDegree localWeight pointIdeal
  chart_box generic_box regular_cut cut_dimension dimension_bot pair_regular intersection_eq
  surface_dimension weight_cast weight_pos point_injective point_prime point_degree point_proper_section)
open scoped BigOperators
private lemma branch_weight_le {f Q l} (b : Branch f Q l) :
    b.weight ≤ localWeight (divisorIdeal b.surface (membershipTest b.g)) b.curve := by
  have hcast : (localWeight (divisorIdeal b.surface (membershipTest b.g)) b.curve : ℕ∞) =
      cycleLength (divisorIdeal b.surface (membershipTest b.g)) b.curve b.divisor.isPrime :=
    weight_cast b.divisor
  have hpos : 0 < localWeight (divisorIdeal b.surface (membershipTest b.g)) b.curve := weight_pos b.divisor
  by_cases hs : b.Simple
  · simpa [Branch.weight, hs] using (Nat.succ_le_of_lt hpos)
  · rw [Branch.weight, ite_eq_right hs]
    have hne : localWeight (divisorIdeal b.surface (membershipTest b.g)) b.curve ≠ 1 := by
      intro h
      apply hs
      exact hcast.symm.trans (by rw [h]; rfl)
    omega
private lemma same_member {f Q l} {b c : Branch f Q l} (h : b.surface = c.surface) : b.member = c.member := by
  have order (d e : Branch f Q l) (heq : d.surface = e.surface) : ¬ d.r < e.r := by
    intro hlt
    have hmem := e.chart.2.1 (d.r + 1) (by omega)
    rw [← heq, Function.iterate_succ_apply'] at hmem
    exact d.chart.2.2 hmem
  have hr : b.r = c.r := Nat.le_antisymm (Nat.le_of_not_gt (order c b h.symm))
    (Nat.le_of_not_gt (order b c h))
  simp only [Branch.member, Branch.g, hr]
private lemma curve_dimension {f Q l} (b : Branch f Q l) (h : dimension b.surface = 2) :
    dimension b.curve = 1 := by
  have := b.base.isPrime
  have hdim := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one b.proper b.divisor
  change dimension b.curve + 1 = dimension b.surface at hdim
  omega
private lemma chamber_plus {x y : Shape} (hx : ChamberBox x) (hy : ChamberBox y) :
    ChamberBox (x.plus y) := by
  obtain ⟨hx₁, hx₂, hx₃⟩ := hx
  obtain ⟨hy₁, hy₂, hy₃⟩ := hy
  refine ⟨Nat.add_le_add hx₁ hy₁, ?_, Nat.add_pos_left hx₃ _⟩
  change 3 * (x.t + y.t) ≤ x.j + y.j
  omega
private lemma polarize_congr {A B : Shape → ℚ} (h : ∀ p, ChamberBox p → A p = B p)
    {boxes : List Shape} (hboxes : ∀ q ∈ boxes, ChamberBox q) {p : Shape}
    (hp : ChamberBox p) : polarize A boxes p = polarize B boxes p := by
  induction boxes generalizing p with
  | nil => exact h p hp
  | cons q boxes ih =>
    have hq := hboxes q List.mem_cons_self
    have hr := fun r hr => hboxes r (List.mem_cons_of_mem _ hr)
    simp only [polarize, ih hr (chamber_plus hp hq), ih hr hp]
lemma ambient_degree (h : K1_13_6_2_3.c1) {p q r s : Shape}
    (hp : ChamberBox p) (hq : ChamberBox q) (hr : ChamberBox r) (hs : ChamberBox s) :
    mixedDegree (⊥ : Ideal GeoJets) [p,q,r,s] ≤ (mixed32 p q r s : ℚ) / 32 := by
  have hb : ChamberBox ⟨3, 3, 1⟩ := ⟨by decide, by decide, by decide⟩
  have hboxes : ∀ u ∈ [p,q,r,s], ChamberBox u := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
    · exact hs
  unfold mixedDegree
  change polarize (capCoeff ⊥ 4) [p,q,r,s] ⟨3,3,1⟩ / (2 : ℚ)^4 ≤ _
  rw [polarize_congr h hboxes hb]
  let n := difference (difference (difference (difference volume32 p) q) r) s ⟨0,0,0⟩
  have hpoly : polarize (fun x => 16 * (volume32 x : ℚ) / 32) [p,q,r,s] ⟨3,3,1⟩ /
      (2 : ℚ)^4 = (n : ℚ) / 32 := by
    simp only [n, polarize, difference, volume32, Shape.plus]
    push_cast
    ring
  rw [hpoly]
  have hn : n ≤ (n.toNat : ℤ) := by omega
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast hn
private lemma point_minimal {J : Ideal GeoJets} (hJ : dimension J = 0)
    (x : JetPoint) (hx : J ≤ pointIdeal x) : J.IsMinimalPrime (pointIdeal x) := by
  have : Module.Finite GeoField (GeoJets ⧸ J) :=
    MvPolynomial.natDegree_affineHilbertPolynomial_eq_zero_iff.mp hJ
  have : IsArtinianRing (GeoJets ⧸ J) := IsArtinianRing.of_finite GeoField _
  have : Ring.KrullDimLE 0 (GeoJets ⧸ J) := isArtinianRing_iff_krullDimLE_zero.mp ‹_›
  have hp := point_prime x
  change pointIdeal x ∈ J.minimalPrimes
  rw [Ideal.minimalPrimes_eq_comap]
  refine ⟨(pointIdeal x).map (Ideal.Quotient.mk J), ?_, Ideal.comap_map_mk hx⟩
  have := Ideal.isPrime_map_quotientMk_of_isPrime hx
  exact Ideal.mem_minimalPrimes_of_krullDimLE_zero _
private lemma proper_slice_card (h2 : K1_13_6_2_3.c2) (h3 : K1_13_6_2_3.c3) {C : Ideal GeoJets} (hC : C.IsPrime)
    (hdim : dimension C = 1) {s : Shape} (hs : ChamberBox s)
    {D : GeoJets} (hD : Box4 s D) (hproper : D ∉ C) (T : Finset JetPoint)
    (hT : ∀ x ∈ T, C ≤ pointIdeal x ∧ MvPolynomial.eval x D = 0) :
    (T.card : ℚ) ≤ mixedDegree C [s] := by
  classical
  let J := C ⊔ Ideal.span {D}
  have hreg := regular_cut hC hproper
  have hJ : dimension J = 0 := by
    have hdrop := cut_dimension hreg
    change dimension J ≤ dimension C - 1 at hdrop
    omega
  have hmin (x : JetPoint) (hx : x ∈ T) : J.IsMinimalPrime (pointIdeal x) :=
    point_minimal hJ x (sup_le (hT x hx).1 ((pointIdeal x).span_singleton_le_iff_mem.mpr (hT x hx).2))
  calc
    (T.card : ℚ) = ∑ _x ∈ T, (1 : ℚ) := by simp
    _ ≤ ∑ x ∈ T, (localWeight J (pointIdeal x) : ℚ) * mixedDegree (pointIdeal x) [] := by
      apply Finset.sum_le_sum
      intro x hx
      rw [point_degree, mul_one]
      exact_mod_cast Nat.succ_le_of_lt (weight_pos (hmin x hx))
    _ = ∑ P ∈ T.image pointIdeal, (localWeight J P : ℚ) * mixedDegree P [] :=
      (Finset.sum_image (f := fun P => (localWeight J P : ℚ) * mixedDegree P [])
        point_injective.injOn).symm
    _ ≤ mixedDegree J [] := h3 J [] (by simp) (by simp [hJ]) _ (by
      intro P hP
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
      exact hmin x hx)
    _ ≤ mixedDegree C [s] := h2 C s [] hs (by simp) (by simp [hdim]) D hD hreg
private lemma slice_card (h2 : K1_13_6_2_3.c2) (h3 : K1_13_6_2_3.c3) {f Q l} (b : Branch f Q l)
    (hdim : dimension b.curve = 1) (T : Finset JetPoint)
    (hT : ∀ x ∈ T, b.Contains x) (hS : Slice4 b T) :
    (T.card : ℚ) ≤ mixedDegree b.curve [chart (taylorLength + 2) (shape f).chamber] := by
  classical
  let s := chart (taylorLength + 2) (shape f).chamber
  have hs : ChamberBox s := chart_box _ _ (Nat.zero_lt_succ _)
  rcases hS with hone | ⟨D, hD, hproper, hzero⟩
  · by_cases hemp : T = ∅
    · rw [hemp]
      simpa using h3 b.curve [s] (by simpa using hs) (by simp [hdim]) ∅ (by simp)
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hsingle : T = {x} := by
        symm
        apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hx)
        simpa using hone
      obtain ⟨D, hD, hproper, hzero⟩ := point_proper_section hdim hs x (hT x hx).1
      exact proper_slice_card h2 h3 b.divisor.isPrime hdim hs hD hproper T (by
        intro y hy
        have hxy : y = x := by simpa [hsingle] using hy
        exact ⟨(hT y hy).1, by rw [hxy]; exact hzero⟩)
  · exact proper_slice_card h2 h3 b.divisor.isPrime hdim hs hD hproper T
      (fun x hx => ⟨(hT x hx).1, hzero x hx⟩)
lemma surface_slice_sum (h2 : K1_13_6_2_3.c2) (h3 : K1_13_6_2_3.c3) {f Q l} (ref : Branch f Q l)
    (hdim : dimension ref.surface = 2) (F : Finset (Branch f Q l))
    (T : Branch f Q l → Finset JetPoint) (hF : ∀ b ∈ F, b.surface = ref.surface)
    (hmember : Box4 (chart (taylorLength + 1) (shape f).chamber) ref.member)
    (hT : ∀ b ∈ F, (∀ x ∈ T b, b.Contains x) ∧ Slice4 b (T b)) :
    (∑ b ∈ F, ((b.weight * (T b).card : ℕ) : ℚ)) ≤
      mixedDegree ref.surface [chart (taylorLength + 1) (shape f).chamber,
        chart (taylorLength + 2) (shape f).chamber] := by
  classical
  let p := chart (taylorLength + 1) (shape f).chamber
  let s := chart (taylorLength + 2) (shape f).chamber
  have hp : ChamberBox p := chart_box _ _ (Nat.zero_lt_succ _)
  have hs : ChamberBox s := chart_box _ _ (Nat.zero_lt_succ _)
  let J := ref.surface ⊔ Ideal.span {ref.member}
  have hcut (b) (hb : b ∈ F) : divisorIdeal b.surface (membershipTest b.g) = J := by
    change b.surface ⊔ Ideal.span {b.member} = J
    rw [hF b hb, same_member (hF b hb)]
  have hreg := regular_cut ref.base.isPrime ref.proper
  have hJdim : dimension J ≤ 1 := (cut_dimension hreg).trans (by simp [hdim])
  calc
    _ ≤ ∑ b ∈ F, (localWeight J b.curve : ℚ) * mixedDegree b.curve [s] := by
      apply Finset.sum_le_sum
      intro b hb
      have hdimB := curve_dimension b ((hF b hb).symm ▸ hdim)
      have hS := slice_card h2 h3 b hdimB (T b) (hT b hb).1 (hT b hb).2
      have hW := (hcut b hb) ▸ branch_weight_le b
      push_cast
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hW) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _))
    _ = ∑ P ∈ F.image Branch.curve, (localWeight J P : ℚ) * mixedDegree P [s] :=
      (Finset.sum_image (f := fun P => (localWeight J P : ℚ) * mixedDegree P [s]) (fun b hb c hc heq =>
        Branch.eq_of_surface_curve ((hF b hb).trans (hF c hc).symm) heq)).symm
    _ ≤ mixedDegree J [s] := h3 J [s] (by simpa using hs) (by simpa using hJdim) _ (by
      intro P hP
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
      exact hcut b hb ▸ b.divisor)
    _ ≤ mixedDegree ref.surface [p,s] :=
      h2 ref.surface p [s] hp (by simpa using hs) (by simp [hdim]) ref.member hmember hreg
private theorem ordinary_bound (h1 : K1_13_6_2_3.c1)
    (h2 : K1_13_6_2_3.c2) (h3 : K1_13_6_2_3.c3) : Low6969GeometryCut_2.c2 := by
  classical
  intro f Q l hf hproper hQ _ F T hT
  let p := (shape f).chamber
  let r := chart (taylorLength + 1) p
  let s := chart (taylorLength + 2) p
  have hp : ChamberBox p :=
    ⟨(K1_13_7_1.shape_chamber f).1, (K1_13_7_1.shape_chamber f).2, hf.2.1⟩
  have hprimary : ChamberBox primaryBox := ⟨by decide, by decide, by decide⟩
  have hr : ChamberBox r := chart_box _ _ (Nat.zero_lt_succ _)
  have hs : ChamberBox s := chart_box _ _ (Nat.zero_lt_succ _)
  have hboxes : ∀ q ∈ [r,s], ChamberBox q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact hq.elim (fun h => h ▸ hr) (fun h => h ▸ hs)
  let J := intersectionIdeal f Q
  let H : Ideal GeoJets := Ideal.span {toGeneric f}
  have hpair := K1_13_7_1.proper_generic f Q hf.1 hproper
  have hf0 : toGeneric f ≠ 0 := by
    intro hz
    exact hf.1.ne_zero (K1_13_7_1.toGeneric_injective (hz.trans (map_zero _).symm))
  have hregF : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets) (toGeneric f)) :=
    regular_cut (by infer_instance) (by simpa using hf0)
  have hregQ := pair_regular f Q hpair
  have hH : dimension H ≤ 3 := by
    simpa [H, dimension_bot] using cut_dimension hregF
  have hJ : dimension J ≤ 2 := by
    rw [show J = H ⊔ Ideal.span {toGeneric Q} from intersection_eq f Q]
    have hdrop : dimension (H ⊔ Ideal.span {toGeneric Q}) ≤ dimension H - 1 := cut_dimension hregQ
    exact hdrop.trans (by omega)
  let surfaces := F.image Branch.surface
  let fiber (P : Ideal GeoJets) := F.filter (fun b => b.surface = P)
  let cost (b : Branch f Q l) : ℚ := ((b.weight * (T b).card : ℕ) : ℚ)
  have hsurface (P : Ideal GeoJets) (hP : P ∈ surfaces) :
      J.IsMinimalPrime P ∧ l ≤ localWeight J P ∧
      (∑ b ∈ fiber P, cost b) ≤ mixedDegree P [r,s] := by
    obtain ⟨ref, href, rfl⟩ := Finset.mem_image.mp hP
    have hl : (l : ℕ∞) ≤ (localWeight J ref.surface : ℕ∞) := by
      rw [weight_cast ref.base]
      exact ref.high
    refine ⟨ref.base, ENat.natCast_le_natCast.mp hl, ?_⟩
    exact surface_slice_sum h2 h3 ref (surface_dimension hf0 hpair ref.base) _ T
      (fun _ hb => (Finset.mem_filter.mp hb).2) (hT ref href).1
      (fun b hb => (hT b (Finset.mem_filter.mp hb).1).2)
  have hcalc : (l : ℚ) * (∑ b ∈ F, cost b) ≤ (budget4 p : ℚ) / 32 := by
    calc
      _ = ∑ P ∈ surfaces, (l : ℚ) * ∑ b ∈ fiber P, cost b := by
        rw [← Finset.mul_sum]
        congr 1
        exact (Finset.sum_fiberwise_of_maps_to (fun _ hb => Finset.mem_image_of_mem _ hb) cost).symm
      _ ≤ ∑ P ∈ surfaces, (localWeight J P : ℚ) * mixedDegree P [r,s] := by
        apply Finset.sum_le_sum
        intro P hP
        obtain ⟨_, hl, hsum⟩ := hsurface P hP
        have hnonneg : 0 ≤ ∑ b ∈ fiber P, cost b := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hnonneg).trans
          (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
      _ ≤ mixedDegree J [r,s] := h3 J [r,s] hboxes (by simpa using hJ) surfaces
        (fun P hP => (hsurface P hP).1)
      _ ≤ mixedDegree H [primaryBox,r,s] := by
        rw [show J = H ⊔ Ideal.span {toGeneric Q} from intersection_eq f Q]
        exact h2 H primaryBox [r,s] hprimary hboxes (by simpa using hH) _ (generic_box hQ) hregQ
      _ ≤ mixedDegree (⊥ : Ideal GeoJets) [p,primaryBox,r,s] := by
        rw [show H = (⊥ : Ideal GeoJets) ⊔ Ideal.span {toGeneric f} by simp [H]]
        apply h2 _ p [primaryBox,r,s] hp _ (by simp) _ _ hregF
        · intro q hq
          exact (List.mem_cons.mp hq).elim (fun h => h ▸ hprimary) (hboxes q)
        · exact generic_box ⟨le_max_left _ _, le_rfl, le_rfl⟩
      _ ≤ _ := ambient_degree h1 hp hprimary hr hs
  have hfinal := (le_div_iff₀ (by norm_num : (0 : ℚ) < 32)).mp hcalc
  rw [mul_comm _ (32 : ℚ), ← mul_assoc] at hfinal
  dsimp only [cost, p] at hfinal
  exact_mod_cast hfinal
theorem proof : Low6969GeometryCut_2.c2 :=
  ordinary_bound K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
end
end Low6969GeometryCut_2_2
end
section
namespace Low6969GeometryCut_2_3
noncomputable section
open Low6969Prices (primaryBox taylorLength)
open Low6969GeometryCut_2 (Branch)
open K1_13 (Shape liftedChart)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5 graphBox)
open K1_13_6_2_4 (Boxes)
def boxes (p : Shape) : Boxes := fun i =>
  if i = 0 then (p, 0) else
  if i = 1 then (primaryBox, 0) else
  if i = 2 then (graphBox p, 1) else
  if i = 3 then (liftedChart (taylorLength + 1) p, taylorLength + 1)
  else (liftedChart (taylorLength + 2) p, taylorLength + 2)
def graphLift {f Q l} (b : Branch f Q l) (P : Ideal GeoJets) : Ideal GeoJets5 :=
  (P.map b.localMap).comap b.onGraph
end
end Low6969GeometryCut_2_3
end
section
namespace Low6969GeometryCut_2_3
noncomputable section
open Low6969Prices (primaryBox taylorLength)
open Low6969GeometryCut_2 (budget5)
open K1_13 (Shape liftedChart mixed32)
open K1_13_6 (GeoField)
open K1_13_6_2 (graphBox)
open K1_13_6_2_4 (Boxes Chamber Allowed Admissible allowed_coordinate
  mixedDegree diagonalExponents)
open K1_13_6_2_4_3 (volumeProduct sumCap diagonal)
open MvPolynomial
open scoped BigOperators
open K1_13_6_2_4 (chart_chamber)
open K1_13_6_2_4_3 (diagonal_coeff)
open K1_13_6_2_4_3 (alt alt_insert alt_empty capDiff five_differences signed4_le)
theorem last_caps (p : Shape) :
    1 ≤ (boxes p 4).1.b ∧ 3 ≤ (boxes p 4).1.j ∧ 1 ≤ (boxes p 4).1.t ∧ 1 ≤ (boxes p 4).2 := by
  let H := 4 + (taylorLength + 2 - 5) * (p.j - 2)
  change 1 ≤ max _ H ∧ 3 ≤ H ∧ 1 ≤ min _ (H / 3) ∧ 1 ≤ taylorLength + 2
  have hH : 4 ≤ H := Nat.le_add_right _ _
  refine ⟨(by omega : 1 ≤ H).trans (le_max_right _ _), by omega, le_min ?_ (by omega), by decide⟩
  omega
theorem boxes_admissible (p : Shape) (h : Chamber p) : Admissible (boxes p) := by
  constructor
  · intro i
    fin_cases i
    · exact h
    · change 1679 ≤ 4024 ∧ 3 * 500 ≤ (1679 : ℕ)
      decide
    · change p.j + 1 ≤ max p.b (p.j + 1) ∧
        3 * min (p.t + 1) ((p.j + 1) / 3) ≤ p.j + 1
      have ht := min_le_right (p.t + 1) ((p.j + 1) / 3)
      exact ⟨le_max_right _ _, by omega⟩
    · exact chart_chamber _ _
    · exact chart_chamber _ _
  · intro v
    refine ⟨4, ?_⟩
    obtain ⟨hb, hj, ht, hd⟩ := last_caps p
    change Allowed ((boxes p 4).1.scale 2, 2 * (boxes p 4).2) (Finsupp.single v 1)
    apply allowed_coordinate
    change 1 ≤ 2 * (boxes p 4).1.b ∧ 3 ≤ 2 * (boxes p 4).1.j ∧
      1 ≤ 2 * (boxes p 4).1.t ∧ 1 ≤ 2 * (boxes p 4).2
    omega
private theorem polarized_budget (p : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      volumeProduct (sumCap (boxes p) (diagonal J))) ≤ (budget5 p : ℚ) := by
  change alt (boxes p) Finset.univ volumeProduct ≤ _
  have hu : (Finset.univ : Finset (Fin 5)) = insert 0 (insert 1 (insert 2 (insert 3 (insert 4 ∅)))) := by
    decide
  rw [hu, alt_insert _ (by decide), alt_insert _ (by decide), alt_insert _ (by decide),
    alt_insert _ (by decide), alt_insert _ (by decide), alt_empty]
  let a := liftedChart (taylorLength + 1) p
  let b := liftedChart (taylorLength + 2) p
  change capDiff (b, taylorLength + 2) (capDiff (a, taylorLength + 1)
    (capDiff (graphBox p, 1) (capDiff (primaryBox, 0) (capDiff (p, 0) volumeProduct)))) _ ≤ _
  rw [five_differences]
  change _ ≤ ((mixed32 p primaryBox a b + (taylorLength + 1) * mixed32 p primaryBox (graphBox p) b +
    (taylorLength + 2) * mixed32 p primaryBox (graphBox p) a : ℕ) : ℚ)
  push_cast
  gcongr <;> apply signed4_le
theorem ambient_budget (p : Shape) (hp : Chamber p) :
    32 * mixedDegree (boxes p) ⊥ Finset.univ ≤ (budget5 p : ℚ) := by
  have hB := (boxes_admissible p hp).1
  unfold mixedDegree
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show (2 : ℚ) ^ 5 = 32 by norm_num, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num)]
  change (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (diagonalExponents (boxes p) (diagonal J))) ⊥)).coeff 5) ≤ _
  simp only [diagonal_coeff K1_13_6_2_4_3_1.proof K1_13_6_2_4_3_2.proof (boxes p) hB]
  exact polarized_budget p
end
end Low6969GeometryCut_2_3
end
section
namespace Low6969GeometryCut_2_3
noncomputable section
open Low6969GeometryCut_2 (Branch)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (oldEmbedding)
theorem chart_index_eq {f Q l} {b c : Branch f Q l} (h : b.surface = c.surface) :
    b.r = c.r := by
  have order (d e : Branch f Q l) (he : d.surface = e.surface) : ¬ d.r < e.r := by
    intro hlt
    have hmem := e.chart.2.1 (d.r + 1) (by omega)
    rw [← he, Function.iterate_succ_apply'] at hmem
    exact d.chart.2.2 hmem
  exact Nat.le_antisymm (Nat.le_of_not_gt (order c b h.symm)) (Nat.le_of_not_gt (order b c h))
theorem graphLift_same_chart {f Q l} {b c : Branch f Q l} (h : b.r = c.r)
    (P : Ideal GeoJets) : graphLift b P = graphLift c P := by
  cases b
  cases c
  cases h
  rfl
theorem membership_same_chart {f Q l} {b c : Branch f Q l} (h : b.r = c.r) (D : GeoJets5) :
    Associated (b.onGraph D) (b.localMap b.member) ↔
      Associated (c.onGraph D) (c.localMap c.member) := by
  cases b
  cases c
  cases h
  rfl
theorem graph_on_old {f Q l} (b : Branch f Q l) :
    b.onGraph.comp oldEmbedding = b.localMap := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [oldEmbedding, Branch.onGraph]
  · intro i
    simp [oldEmbedding, Branch.onGraph]
theorem graphLift_comap {f Q l} (b : Branch f Q l) (P : Ideal GeoJets)
    (hP : P.IsPrime) (hregular : b.sigma ∉ P) :
    (graphLift b P).comap oldEmbedding = P := by
  rw [graphLift, Ideal.comap_comap, graph_on_old]
  ext D
  change algebraMap GeoJets b.Local D ∈ P.map (algebraMap GeoJets b.Local) ↔ D ∈ P
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers b.sigma) b.Local]
  constructor
  · rintro ⟨m, ⟨n, rfl⟩, hm⟩
    exact (hP.mem_or_mem hm).resolve_left (fun hpow => hregular (hP.mem_of_pow_mem n hpow))
  · intro hD
    exact ⟨1, (Submonoid.powers b.sigma).one_mem, by simpa using hD⟩
theorem member_proper_on_graph {f Q l} (b : Branch f Q l) {E : GeoJets5}
    (hE : Associated (b.onGraph E) (b.localMap b.member)) :
    E ∉ graphLift b b.surface := by
  intro hmem
  have hlocal : b.localMap b.member ∈ b.surface.map b.localMap :=
    (b.surface.map b.localMap).mem_of_dvd hE.dvd hmem
  have hold : oldEmbedding b.member ∈ graphLift b b.surface := by
    change b.onGraph (oldEmbedding b.member) ∈ b.surface.map b.localMap
    rw [show b.onGraph (oldEmbedding b.member) = b.localMap b.member from
      RingHom.congr_fun (graph_on_old b) _]
    exact hlocal
  have hcont := graphLift_comap b b.surface b.base.isPrime b.chart.2.2
  exact b.proper (hcont ▸ hold)
end
end Low6969GeometryCut_2_3
end
section
namespace Low6969GeometryCut_2_3
noncomputable section
open Low6969Prices (SmallFactor primaryBox)
open Low6969GeometryCut_2 (Branch Slice5 budget5)
open P0_9_6_2_3 (cylinder_comparison cycle_comparison divisor_comparison proper_cut_comparison)
open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5 Box5)
open K1_13_6_2_4 (Admissible Chamber Component DimLE DivisorBound OfDim LengthAt
  ambient_dim cylinder cylinder_injective dim_le_after_section mixedDegree oldEmbedding
  old_section_box point_bound pointIdeal sectionIdeal)
open scoped BigOperators
def c1 : Prop :=
  ∀ {f Q l} (b : Branch f Q l),
    (cylinder b.surface).IsPrime → OfDim (cylinder b.surface) 3 →
    b.graph ∉ cylinder b.surface ∧
    Component (cylinder b.surface) b.graph (graphLift b b.surface) 1 ∧
    OfDim (graphLift b b.surface) 2
def c2 : Prop :=
  ∀ {f Q l} (b : Branch f Q l) (E : GeoJets5),
    (graphLift b b.surface).IsPrime → OfDim (graphLift b b.surface) 2 →
    Associated (b.onGraph E) (b.localMap b.member) →
    Component (graphLift b b.surface) E (graphLift b b.curve) b.weight ∧
    OfDim (graphLift b b.curve) 1
def liftedPoint {f Q l} (b : Branch f Q l) (p : JetPoint) : Fin 5 → GeoField := by
  classical
  exact if h : b.Contains p then fun i => b.liftedEval p h (MvPolynomial.X i)
    else Fin.lastCases 0 p
theorem eval_liftedPoint {f Q l} (b : Branch f Q l) (p : JetPoint) (h : b.Contains p) :
    MvPolynomial.eval (liftedPoint b p) = b.liftedEval p h := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [Branch.liftedEval, Branch.onGraph, Branch.regularEval_localMap]
  · intro i
    simp [liftedPoint, h]
theorem liftedPoint_old {f Q l} (b : Branch f Q l) (p : JetPoint) (h : b.Contains p)
    (i : Fin 4) : liftedPoint b p i.castSucc = p i := by
  simp [liftedPoint, h, Branch.liftedEval, Branch.onGraph, Branch.regularEval_localMap]
theorem liftedPoint_mem {f Q l} (b : Branch f Q l) (p : JetPoint) (h : b.Contains p) :
    graphLift b b.curve ≤ pointIdeal (liftedPoint b p) := by
  have hk : b.localCurve ≤ RingHom.ker (b.regularEval p h) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change b.regularEval p h (b.localMap P) = 0
    rw [Branch.regularEval_localMap]
    exact h.1 hP
  intro D hD
  change MvPolynomial.eval (liftedPoint b p) D = 0
  rw [eval_liftedPoint b p h]
  exact hk hD
theorem bound_marks {f Q l} (hdiv : DivisorBound) {p : Shape}
    (hB : Admissible (boxes p)) (b : Branch f Q l) (T : Finset JetPoint)
    (hp : p = (shape f).chamber) (hT : ∀ y ∈ T, b.Contains y) (hSlice : Slice5 b T)
    (hprime : (graphLift b b.curve).IsPrime) (hdim : OfDim (graphLift b b.curve) 1) :
    (T.card : ℚ) ≤ mixedDegree (boxes p) (graphLift b b.curve) {4} := by
  classical
  subst p
  let U := T.image (liftedPoint b)
  have hcard : U.card = T.card := Finset.card_image_of_injOn (by
    intro x hx y hy he
    funext i
    have hz := congrFun he i.castSucc
    rwa [liftedPoint_old b x (hT x hx), liftedPoint_old b y (hT y hy)] at hz)
  rw [← hcard]
  apply point_bound hdiv _ hB (last_caps _) _ hprime hdim U
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact liftedPoint_mem b y (hT y hy)
  · rcases hSlice with hsingle | ⟨D, hD, hproper, hvanish⟩
    · exact Or.inl (hcard ▸ hsingle)
    · refine Or.inr ⟨D, hD, hproper, ?_⟩
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      rw [eval_liftedPoint b y (hT y hy)]
      exact hvanish y hy (hT y hy)
private theorem initial_bound
    (f Q : Row 4) (l : ℕ) (hf : SmallFactor f) (hQ : ¬ f ∣ Q)
    (hQbox : InBox (shape Q) primaryBox) (S : Finset (Ideal GeoJets))
    (hS : ∀ P ∈ S, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime) :
    (∀ P ∈ S, (cylinder P).IsPrime ∧ OfDim (cylinder P) 3) ∧
      (l : ℚ) * (∑ P ∈ S, mixedDegree (boxes (shape f).chamber) (cylinder P) {2, 3, 4}) ≤
        mixedDegree (boxes (shape f).chamber) ⊥ Finset.univ := by
  classical
  let p := (shape f).chamber
  let B := boxes p
  have hB := boxes_admissible p (K1_13_7_1.shape_chamber f)
  let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
  let J := sectionIdeal A (oldEmbedding (toGeneric Q))
  obtain ⟨hregQ, hAlgebra⟩ := cylinder_comparison f Q hf.1 hQ
  have hregf : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets5)
      (oldEmbedding (toGeneric f))) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne
      (K1_13_6_3_6.toGeneric_ne_zero hf.1.ne_zero)
  have hboxf : Box5 p 0 (oldEmbedding (toGeneric f)) :=
    old_section_box ⟨le_max_left _ _, le_rfl, le_rfl⟩
  have hAdim : DimLE A 4 := dim_le_after_section hregf ambient_dim
  have hJdim : DimLE J 3 := dim_le_after_section hregQ hAdim
  have hgeom (P : Ideal GeoJets) (hP : P ∈ S) :
      (cylinder P).IsPrime ∧ OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P), (l : ℕ∞) ≤ LengthAt J (cylinder P) hc.isPrime := by
    obtain ⟨h, hw⟩ := hS P hP
    obtain ⟨hd, hc, hl⟩ := hAlgebra P h
    exact ⟨hc.isPrime, hd, hc, hw.trans hl⟩
  refine ⟨fun P hP => ⟨(hgeom P hP).1, (hgeom P hP).2.1⟩, ?_⟩
  have hs := cycle_comparison B hB J {2, 3, 4} hJdim S cylinder (fun _ => l) cylinder_injective.injOn
    (fun P hP => (hgeom P hP).2.2)
  have hcutQ := proper_cut_comparison B hB A {2, 3, 4} 1 (by decide) hAdim
    (oldEmbedding (toGeneric Q)) (old_section_box hQbox) hregQ
  have hcutf := proper_cut_comparison B hB ⊥ {1, 2, 3, 4} 0 (by decide) ambient_dim
    (oldEmbedding (toGeneric f)) hboxf hregf
  have hall : (insert (0 : Fin 5) {1, 2, 3, 4} : Finset (Fin 5)) = Finset.univ := by decide
  rw [hall] at hcutf
  rw [Finset.mul_sum]
  exact hs.trans (hcutQ.trans hcutf)
theorem of_children (hgraph : c1) (hmember : c2) : Low6969GeometryCut_2.c3 := by
  classical
  have hdiv := divisor_comparison
  intro f Q l hf hproper hQ hl F T hF
  let p := (shape f).chamber
  have hp : Chamber p := K1_13_7_1.shape_chamber f
  let B := boxes p
  have hB : Admissible B := boxes_admissible p hp
  let S := F.image Branch.surface
  let fibre (P : Ideal GeoJets) := F.filter fun b => b.surface = P
  let charge (b : Branch f Q l) : ℚ := (b.weight : ℚ) * (T b).card
  obtain ⟨hZ, hsumZ⟩ := initial_bound f Q l hf hproper hQ S (by
    intro P hP
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨b.base, b.high⟩)
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
        (bound_marks hdiv hB c (T c) rfl hon hslice hcomp.minimal.isPrime hdim)
        (Nat.cast_nonneg _)
    have hEbound := hdiv B hB G {4} 3 hG.minimal.isPrime (by decide) hGdim E hboxE hproperE
      (fibre b.surface) C Branch.weight inj (fun c hc => (hC c (Finset.mem_filter.mp hc).2).1)
    have hGbound := hdiv B hB (cylinder b.surface) {3, 4} 2 hZprime (by decide) hZdim
      b.graph hboxG hproperG {G} id (fun _ => 1) (fun _ _ _ _ h => h) (by
        intro P hP
        obtain rfl := Finset.mem_singleton.mp hP
        exact hG)
    have hGbound' : mixedDegree B G {3, 4} ≤ mixedDegree B (cylinder b.surface) {2, 3, 4} := by
      simpa only [Finset.sum_singleton, Nat.cast_one, one_mul, id_eq] using hGbound
    exact hmarks.trans (hEbound.trans hGbound')
  have hcharge : (∑ c ∈ F, charge c) ≤ ∑ P ∈ S, mixedDegree B (cylinder P) {2, 3, 4} := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Branch.surface)
      (fun b hb => Finset.mem_image_of_mem Branch.surface hb) charge]
    exact Finset.sum_le_sum hfibre
  have htotal := (mul_le_mul_of_nonneg_left hcharge (Nat.cast_nonneg l)).trans hsumZ
  have hr : 32 * ((l : ℚ) * (∑ b ∈ F, charge b)) ≤ (budget5 p : ℚ) :=
    (mul_le_mul_of_nonneg_left htotal (by norm_num)).trans (ambient_budget p hp)
  apply (Nat.cast_le (α := ℚ)).mp
  push_cast
  simpa only [charge, mul_assoc] using hr
end
end Low6969GeometryCut_2_3
end
section
namespace Low6969GeometryCut_2_3_1
noncomputable section
open Low6969GeometryCut_2 (Branch)
open Low6969GeometryCut_2_3 (graphLift graph_on_old graphLift_comap)
open K1_13_6 (GeoField GeoJets partialFlow toGeneric)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (OfDim cylinder oldEmbedding one_le_length sectionIdeal)
open K1_13_6_2_4_5 (four_ne_zero substituteLast substituteLast_old)
open K1_13_6_2_4_5 (dim_after_proper_cut)
private theorem graph_eq {f Q l} (b : Branch f Q l) :
    b.graph = oldEmbedding (toGeneric (partialFlow b.g)) +
      oldEmbedding (MvPolynomial.C (4 : GeoField) * b.sigma) * MvPolynomial.X (Fin.last 4) := by
  simp [Branch.graph, oldEmbedding]
private theorem graph_old {f Q l} (b : Branch f Q l) (D : GeoJets) :
    b.onGraph (oldEmbedding D) = b.localMap D :=
  RingHom.congr_fun (graph_on_old b) D
private theorem onGraph_graph {f Q l} (b : Branch f Q l) : b.onGraph b.graph = 0 := by
  rw [graph_eq, map_add, map_mul, graph_old, graph_old, map_mul]
  have hx : b.onGraph (MvPolynomial.X (Fin.last 4)) =
      b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹) * toGeneric (partialFlow b.g)) *
        IsLocalization.Away.invSelf b.sigma := by
    rw [Branch.onGraph, MvPolynomial.eval₂Hom_X', Fin.lastCases_last]
  have hσ : b.localMap b.sigma * IsLocalization.Away.invSelf b.sigma = 1 :=
    IsLocalization.Away.mul_invSelf b.sigma
  have h4 : b.localMap (MvPolynomial.C (4 : GeoField)) *
      b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹)) = -1 := by
    rw [← map_mul, ← map_mul, mul_neg, mul_inv_cancel₀ K1_13_6_2_4_5.four_ne_zero,
      map_neg, map_one, map_neg, map_one]
  rw [hx, map_mul]
  calc
    _ = b.localMap (toGeneric (partialFlow b.g)) +
        (b.localMap (MvPolynomial.C (4 : GeoField)) *
          b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹))) *
        (b.localMap b.sigma * IsLocalization.Away.invSelf b.sigma) *
        b.localMap (toGeneric (partialFlow b.g)) := by ac_rfl
    _ = 0 := by rw [h4, hσ, mul_one, neg_one_mul, add_neg_cancel]
private theorem factor_onGraph {f Q l} (b : Branch f Q l) {A : Type*} [CommRing A]
    (k : GeoJets5 →+* A) (hs : IsUnit (k (oldEmbedding b.sigma))) (hg : k b.graph = 0) :
    k = (IsLocalization.Away.lift b.sigma (g := k.comp oldEmbedding) hs).comp b.onGraph := by
  let φ : b.Local →+* A := IsLocalization.Away.lift b.sigma (g := k.comp oldEmbedding) hs
  let ψ := φ.comp b.onGraph
  have hold (D : GeoJets) : ψ (oldEmbedding D) = k (oldEmbedding D) := by
    change φ (b.onGraph (oldEmbedding D)) = _
    rw [graph_old]
    exact IsLocalization.Away.lift_eq b.sigma hs D
  have hψ : ψ b.graph = 0 := by simp [ψ, onGraph_graph]
  change k = ψ
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa [oldEmbedding] using (hold (MvPolynomial.C a)).symm
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [graph_eq, map_add, map_mul] at hg hψ
      rw [hold, hold] at hψ
      have hμ : IsUnit (k (oldEmbedding (MvPolynomial.C (4 : GeoField) * b.sigma))) := by
        rw [map_mul, map_mul]
        exact ((isUnit_iff_ne_zero.mpr K1_13_6_2_4_5.four_ne_zero).map
          (k.comp (oldEmbedding.comp MvPolynomial.C))).mul hs
      exact hμ.mul_right_inj.mp (add_left_cancel (hg.trans hψ.symm))
    · simpa [oldEmbedding] using (hold (MvPolynomial.X j)).symm
private theorem graphLift_prime {f Q l} (b : Branch f Q l) (P : Ideal GeoJets)
    (hP : P.IsPrime) (hs : b.sigma ∉ P) : (graphLift b P).IsPrime := by
  have hdis : Disjoint (↑(Submonoid.powers b.sigma) : Set GeoJets) P := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨n, rfl⟩ hn
    exact hs (hP.mem_of_pow_mem n hn)
  let : (P.map b.localMap).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers b.sigma) b.Local P hP hdis
  exact Ideal.comap_isPrime b.onGraph _
private theorem graphLift_contains_graph {f Q l} (b : Branch f Q l) (P : Ideal GeoJets) :
    b.graph ∈ graphLift b P := by
  change b.onGraph b.graph ∈ P.map b.localMap
  rw [onGraph_graph]
  exact Ideal.zero_mem _
private theorem cylinder_le_graphLift {f Q l} (b : Branch f Q l) (P : Ideal GeoJets) :
    cylinder P ≤ graphLift b P := by
  rw [cylinder, Ideal.map_le_iff_le_comap, graphLift, Ideal.comap_comap, graph_on_old]
  exact Ideal.le_comap_map
private theorem prime_eq_graphLift {f Q l} (b : Branch f Q l) (T : Ideal GeoJets5)
    (hT : T.IsPrime) (hs : oldEmbedding b.sigma ∉ T) (hg : b.graph ∈ T) :
    T = graphLift b (T.comap oldEmbedding) := by
  let := hT
  let A := FractionRing (GeoJets5 ⧸ T)
  let k := (algebraMap (GeoJets5 ⧸ T) A).comp (Ideal.Quotient.mk T)
  have hk (x : GeoJets5) : k x = 0 ↔ x ∈ T := by
    change algebraMap (GeoJets5 ⧸ T) A (Ideal.Quotient.mk T x) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  have hs' : IsUnit (k (oldEmbedding b.sigma)) := isUnit_iff_ne_zero.mpr (mt (hk _).mp hs)
  let φ : b.Local →+* A := IsLocalization.Away.lift b.sigma (g := k.comp oldEmbedding) hs'
  have hφ : φ.comp b.localMap = k.comp oldEmbedding :=
    IsLocalization.Away.lift_comp b.sigma hs'
  have hker : (RingHom.ker φ).comap b.localMap = T.comap oldEmbedding := by
    ext x
    change φ (b.localMap x) = 0 ↔ oldEmbedding x ∈ T
    rw [show φ (b.localMap x) = k (oldEmbedding x) from RingHom.congr_fun hφ x, hk]
  rw [graphLift, ← hker]
  have he : ((RingHom.ker φ).comap b.localMap).map b.localMap =
      RingHom.ker φ := IsLocalization.map_under (Submonoid.powers b.sigma) b.Local _
  rw [he]
  ext D
  change D ∈ T ↔ φ (b.onGraph D) = 0
  exact (hk D).symm.trans (Iff.of_eq (congrArg (fun j : GeoJets5 →+* A => j D = 0)
    (factor_onGraph b k hs' ((hk _).mpr hg))))
private theorem graph_proper {f Q l} (b : Branch f Q l) :
    b.graph ∉ cylinder b.surface := by
  intro h
  have hm (x : GeoJets) : substituteLast x b.graph ∈ b.surface := by
    have hle : cylinder b.surface ≤ b.surface.comap (substituteLast x) := by
      rw [cylinder, Ideal.map_le_iff_le_comap, Ideal.comap_comap, substituteLast_old, Ideal.comap_id]
    exact hle h
  have evalGraph (x : GeoJets) : substituteLast x b.graph =
      toGeneric (partialFlow b.g) + (MvPolynomial.C (4 : GeoField) * b.sigma) * x := by
    have ho (D : GeoJets) : substituteLast x (oldEmbedding D) = D :=
      RingHom.congr_fun (substituteLast_old x) D
    rw [graph_eq, map_add, map_mul, ho, ho]
    rw [substituteLast, MvPolynomial.eval₂Hom_X', Fin.lastCases_last]
  have h0 := hm 0
  have h1 := hm 1
  rw [evalGraph, mul_zero, add_zero] at h0
  rw [evalGraph, mul_one] at h1
  have hσ : MvPolynomial.C (4 : GeoField) * b.sigma ∈ b.surface :=
    (b.surface.add_mem_iff_right h0).mp h1
  have hu : IsUnit (MvPolynomial.C (4 : GeoField) : GeoJets) :=
    (isUnit_iff_ne_zero.mpr K1_13_6_2_4_5.four_ne_zero).map MvPolynomial.C
  exact b.chart.2.2 ((b.base.isPrime.mem_or_mem hσ).resolve_left
    (fun hc => b.base.isPrime.ne_top (b.surface.eq_top_of_isUnit_mem hc hu)))
private theorem graph_minimal {f Q l} (b : Branch f Q l) :
    (sectionIdeal (cylinder b.surface) b.graph).IsMinimalPrime (graphLift b b.surface) := by
  refine ⟨⟨graphLift_prime b b.surface b.base.isPrime b.chart.2.2,
    sup_le (cylinder_le_graphLift b _) ((Ideal.span_singleton_le_iff_mem _).mpr
      (graphLift_contains_graph b _))⟩, ?_⟩
  intro T hT hTG
  have hs : oldEmbedding b.sigma ∉ T := by
    intro h
    have hm : b.sigma ∈ (graphLift b b.surface).comap oldEmbedding := hTG h
    rw [graphLift_comap b b.surface b.base.isPrime b.chart.2.2] at hm
    exact b.chart.2.2 hm
  have hg : b.graph ∈ T := hT.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hb : b.surface ≤ T.comap oldEmbedding :=
    Ideal.map_le_iff_le_comap.mp (le_sup_left.trans hT.2)
  rw [prime_eq_graphLift b T hT.1 hs hg]
  exact Ideal.comap_mono (Ideal.map_mono hb)
theorem proof : Low6969GeometryCut_2_3.c1 := by
  intro f Q l b hZ hZd
  have hproper := graph_proper b
  have hG := graph_minimal b
  exact ⟨hproper, ⟨hG, one_le_length hG⟩, dim_after_proper_cut (d := 2) hZ hZd hproper hG⟩
end
end Low6969GeometryCut_2_3_1
end
section
namespace Low6969GeometryCut_2_3_2
noncomputable section
open Low6969GeometryCut (membershipTest)
open Low6969GeometryCut_2 (Branch)
open Low6969GeometryCut_2_3 (graphLift graph_on_old graphLift_comap member_proper_on_graph)
open K1_13_6 (GeoField GeoJets toGeneric partialFlow divisorIdeal cycleLength)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_3 (localWeight weight_cast weight_pos)
open K1_13_6_2_4 (OfDim LengthAt sectionIdeal oldEmbedding)
open K1_13_6_2_4_5 (four_ne_zero)
open K1_13_6_2_4_5 (length_le_of_surjection dim_after_proper_cut)
local notation "memberDiv" b => divisorIdeal (Branch.surface b) (membershipTest (Branch.g b))
private theorem graph_eq {f Q l} (b : Branch f Q l) :
    b.graph = oldEmbedding (toGeneric (partialFlow b.g)) +
      oldEmbedding (MvPolynomial.C (4 : GeoField) * b.sigma) * MvPolynomial.X (Fin.last 4) := by
  simp [Branch.graph, oldEmbedding]
private theorem graph_old {f Q l} (b : Branch f Q l) (D : GeoJets) :
    b.onGraph (oldEmbedding D) = b.localMap D :=
  RingHom.congr_fun (graph_on_old b) D
private theorem onGraph_graph {f Q l} (b : Branch f Q l) : b.onGraph b.graph = 0 := by
  rw [graph_eq, map_add, map_mul, graph_old, graph_old, map_mul]
  have hx : b.onGraph (MvPolynomial.X (Fin.last 4)) =
      b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹) * toGeneric (partialFlow b.g)) *
        IsLocalization.Away.invSelf b.sigma := by
    rw [Branch.onGraph, MvPolynomial.eval₂Hom_X', Fin.lastCases_last]
  have hσ : b.localMap b.sigma * IsLocalization.Away.invSelf b.sigma = 1 :=
    IsLocalization.Away.mul_invSelf b.sigma
  have h4 : b.localMap (MvPolynomial.C (4 : GeoField)) *
      b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹)) = -1 := by
    rw [← map_mul, ← map_mul, mul_neg, mul_inv_cancel₀ four_ne_zero, map_neg, map_one, map_neg, map_one]
  rw [hx, map_mul]
  calc
    _ = b.localMap (toGeneric (partialFlow b.g)) +
        (b.localMap (MvPolynomial.C (4 : GeoField)) *
          b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹))) *
        (b.localMap b.sigma * IsLocalization.Away.invSelf b.sigma) *
        b.localMap (toGeneric (partialFlow b.g)) := by ac_rfl
    _ = 0 := by rw [h4, hσ, mul_one, neg_one_mul, add_neg_cancel]
private theorem factor_onGraph {f Q l} (b : Branch f Q l) {A : Type*} [CommRing A]
    (k : GeoJets5 →+* A) (hs : IsUnit (k (oldEmbedding b.sigma))) (hg : k b.graph = 0) :
    k = (IsLocalization.Away.lift b.sigma (g := k.comp oldEmbedding) hs).comp b.onGraph := by
  let φ : b.Local →+* A := IsLocalization.Away.lift b.sigma (g := k.comp oldEmbedding) hs
  let ψ := φ.comp b.onGraph
  have hold (D : GeoJets) : ψ (oldEmbedding D) = k (oldEmbedding D) := by
    change φ (b.onGraph (oldEmbedding D)) = _
    rw [graph_old]
    exact IsLocalization.Away.lift_eq b.sigma hs D
  have hψ : ψ b.graph = 0 := by simp [ψ, onGraph_graph]
  change k = ψ
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa [oldEmbedding] using (hold (MvPolynomial.C a)).symm
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [graph_eq, map_add, map_mul] at hg hψ
      rw [hold, hold] at hψ
      have hμ : IsUnit (k (oldEmbedding (MvPolynomial.C (4 : GeoField) * b.sigma))) := by
        rw [map_mul, map_mul]
        exact ((isUnit_iff_ne_zero.mpr (four_ne_zero : (4 : GeoField) ≠ 0)).map
          (k.comp (oldEmbedding.comp MvPolynomial.C))).mul hs
      exact hμ.mul_right_inj.mp (add_left_cancel (hg.trans hψ.symm))
    · simpa [oldEmbedding] using (hold (MvPolynomial.X j)).symm
private theorem graphLift_prime {f Q l} (b : Branch f Q l) (P : Ideal GeoJets)
    (hP : P.IsPrime) (hs : b.sigma ∉ P) : (graphLift b P).IsPrime := by
  have hdis : Disjoint (↑(Submonoid.powers b.sigma) : Set GeoJets) P := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨n, rfl⟩ hn
    exact hs (hP.mem_of_pow_mem n hn)
  let : (P.map b.localMap).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers b.sigma) b.Local P hP hdis
  exact Ideal.comap_isPrime b.onGraph _
private theorem graphLift_contains_graph {f Q l} (b : Branch f Q l) (P : Ideal GeoJets) :
    b.graph ∈ graphLift b P := by
  change b.onGraph b.graph ∈ P.map b.localMap
  rw [onGraph_graph]
  exact Ideal.zero_mem _
private theorem prime_eq_graphLift {f Q l} (b : Branch f Q l) (T : Ideal GeoJets5)
    (hT : T.IsPrime) (hs : oldEmbedding b.sigma ∉ T) (hg : b.graph ∈ T) :
    T = graphLift b (T.comap oldEmbedding) := by
  let := hT
  let A := FractionRing (GeoJets5 ⧸ T)
  let k := (algebraMap (GeoJets5 ⧸ T) A).comp (Ideal.Quotient.mk T)
  have hk (x : GeoJets5) : k x = 0 ↔ x ∈ T := by
    change algebraMap (GeoJets5 ⧸ T) A (Ideal.Quotient.mk T x) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  have hs' : IsUnit (k (oldEmbedding b.sigma)) := isUnit_iff_ne_zero.mpr (mt (hk _).mp hs)
  let φ : b.Local →+* A := IsLocalization.Away.lift b.sigma (g := k.comp oldEmbedding) hs'
  have hφ : φ.comp b.localMap = k.comp oldEmbedding :=
    IsLocalization.Away.lift_comp b.sigma hs'
  have hker : (RingHom.ker φ).comap b.localMap = T.comap oldEmbedding := by
    ext x
    change φ (b.localMap x) = 0 ↔ oldEmbedding x ∈ T
    rw [show φ (b.localMap x) = k (oldEmbedding x) from RingHom.congr_fun hφ x, hk]
  rw [graphLift, ← hker]
  have he : ((RingHom.ker φ).comap b.localMap).map b.localMap =
      RingHom.ker φ := IsLocalization.map_under (Submonoid.powers b.sigma) b.Local _
  rw [he]
  ext D
  change D ∈ T ↔ φ (b.onGraph D) = 0
  exact (hk D).symm.trans (Iff.of_eq (congrArg (fun j : GeoJets5 →+* A => j D = 0)
    (factor_onGraph b k hs' ((hk _).mpr hg))))
private theorem member_minimal {f Q l} (b : Branch f Q l) {E : GeoJets5}
    (hE : Associated (b.onGraph E) (b.localMap b.member)) :
    (sectionIdeal (graphLift b b.surface) E).IsMinimalPrime (graphLift b b.curve) := by
  have hSC : b.surface ≤ b.curve := le_sup_left.trans b.divisor.le
  have hm : b.member ∈ b.curve := b.divisor.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine ⟨⟨graphLift_prime b b.curve b.divisor.isPrime b.regularCurve,
    sup_le (Ideal.comap_mono (Ideal.map_mono hSC)) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩, ?_⟩
  · change b.onGraph E ∈ b.curve.map b.localMap
    exact (b.curve.map b.localMap).mem_of_dvd hE.dvd' (Ideal.mem_map_of_mem _ hm)
  · intro T hT hTC
    let P := T.comap oldEmbedding
    have hP : P.IsPrime := by
      let := hT.1
      exact Ideal.comap_isPrime oldEmbedding _
    have hPC : P ≤ b.curve := by
      have hle := Ideal.comap_mono (f := oldEmbedding) hTC
      rwa [graphLift_comap b b.curve b.divisor.isPrime b.regularCurve] at hle
    have hS : b.surface ≤ P := by
      have hle := Ideal.comap_mono (f := oldEmbedding) (le_sup_left.trans hT.2 :
        graphLift b b.surface ≤ T)
      rwa [graphLift_comap b b.surface b.base.isPrime b.chart.2.2] at hle
    have hreg : b.sigma ∉ P := fun h => b.regularCurve (hPC h)
    have hEq : T = graphLift b P := prime_eq_graphLift b T hT.1 hreg
      (hT.2 (Ideal.mem_sup_left (graphLift_contains_graph b _)))
    have hEmem : E ∈ T := hT.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [hEq] at hEmem
    have hold : oldEmbedding b.member ∈ graphLift b P := by
      change b.onGraph (oldEmbedding b.member) ∈ P.map b.localMap
      rw [graph_old]
      exact (P.map b.localMap).mem_of_dvd hE.dvd hEmem
    have hmP : b.member ∈ P := by
      have hh : b.member ∈ (graphLift b P).comap oldEmbedding := hold
      rwa [graphLift_comap b P hP hreg] at hh
    have hCP : b.curve ≤ P :=
      b.divisor.2 ⟨hP, sup_le hS ((Ideal.span_singleton_le_iff_mem _).mpr hmP)⟩ hPC
    rw [hEq]
    exact Ideal.comap_mono (Ideal.map_mono hCP)
private theorem membership_length {f Q l} (b : Branch f Q l) {E : GeoJets5}
    (hE : Associated (b.onGraph E) (b.localMap b.member)) :
    cycleLength (memberDiv b) b.curve b.divisor.isPrime ≤
      LengthAt (sectionIdeal (graphLift b b.surface) E) (graphLift b b.curve)
        (member_minimal b hE).isPrime := by
  let C := graphLift b b.curve
  let : C.IsPrime := (member_minimal b hE).isPrime
  let : b.curve.IsPrime := b.divisor.isPrime
  let A := Localization.AtPrime C
  let B := Localization.AtPrime b.curve
  let M := IsLocalRing.maximalIdeal B
  let I := sectionIdeal (graphLift b b.surface) E
  let J := memberDiv b
  let L := J.map (algebraMap GeoJets B)
  have hσ : IsUnit (algebraMap GeoJets B b.sigma) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff B b.curve b.sigma).mpr b.regularCurve
  let φ : b.Local →+* B := IsLocalization.Away.lift b.sigma hσ
  let θ := φ.comp b.onGraph
  have hφ : φ.comp b.localMap = algebraMap GeoJets B :=
    IsLocalization.Away.lift_comp b.sigma hσ
  have hφM : M.comap φ = b.curve.map b.localMap := by
    have hco : (M.comap φ).comap b.localMap = b.curve := by
      rw [Ideal.comap_comap, hφ]
      exact IsLocalization.AtPrime.under_maximalIdeal B b.curve
    calc
      M.comap φ = ((M.comap φ).comap b.localMap).map b.localMap :=
        (IsLocalization.map_under (Submonoid.powers b.sigma) b.Local (M.comap φ)).symm
      _ = _ := congrArg (Ideal.map b.localMap) hco
  have hθM : M.comap θ = C := by
    change M.comap (φ.comp b.onGraph) = (b.curve.map b.localMap).comap b.onGraph
    rw [← Ideal.comap_comap, hφM]
  have hθold : θ.comp oldEmbedding = algebraMap GeoJets B := by
    change (φ.comp b.onGraph).comp oldEmbedding = _
    rw [RingHom.comp_assoc, graph_on_old, hφ]
  have hθunit (x : C.primeCompl) : IsUnit (θ x) := by
    have hn : θ x ∉ M := by
      intro hm
      have hh : (x : GeoJets5) ∈ M.comap θ := hm
      rw [hθM] at hh
      exact x.2 hh
    simpa only [M, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hn
  let ψ : A →+* B := IsLocalization.lift hθunit
  have hψ : ψ.comp (algebraMap GeoJets5 A) = θ := IsLocalization.lift_comp hθunit
  have hsurj : Function.Surjective ψ := by
    apply (IsLocalization.lift_surjective_iff hθunit).mpr
    intro v
    obtain ⟨⟨num, den⟩, hv⟩ := IsLocalization.surj b.curve.primeCompl v
    have hden : oldEmbedding den ∈ C.primeCompl := by
      change oldEmbedding den ∉ C
      intro hd
      have hm : (den : GeoJets) ∈ C.comap oldEmbedding := hd
      change (den : GeoJets) ∈ (graphLift b b.curve).comap oldEmbedding at hm
      rw [graphLift_comap b b.curve b.divisor.isPrime b.regularCurve] at hm
      exact den.2 hm
    refine ⟨⟨oldEmbedding num, ⟨oldEmbedding den, hden⟩⟩, ?_⟩
    change v * θ (oldEmbedding den) = θ (oldEmbedding num)
    have hold (x : GeoJets) : θ (oldEmbedding x) = algebraMap GeoJets B x :=
      RingHom.congr_fun hθold x
    simpa only [hold] using hv
  have hI : I ≤ L.comap θ := by
    apply sup_le
    · change (b.surface.map b.localMap).comap b.onGraph ≤ L.comap (φ.comp b.onGraph)
      rw [← Ideal.comap_comap]
      apply Ideal.comap_mono
      apply Ideal.map_le_iff_le_comap.mp
      rw [Ideal.map_map, hφ]
      exact Ideal.map_mono le_sup_left
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      change φ (b.onGraph E) ∈ L
      have hm : b.member ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      have hm' : φ (b.localMap b.member) ∈ L := by
        rw [show φ (b.localMap b.member) = algebraMap GeoJets B b.member from
          RingHom.congr_fun hφ _]
        exact Ideal.mem_map_of_mem _ hm
      exact L.mem_of_dvd (map_dvd φ hE.dvd') hm'
  have hIL : I.map (algebraMap GeoJets5 A) ≤ L.comap ψ := by
    rwa [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hψ]
  exact length_le_of_surjection ψ hsurj hIL
private theorem branch_weight_le {f Q l} (b : Branch f Q l) :
    b.weight ≤ localWeight (memberDiv b) b.curve := by
  have hcast : (localWeight (memberDiv b) b.curve : ℕ∞) =
      cycleLength (memberDiv b) b.curve b.divisor.isPrime :=
    weight_cast b.divisor
  have hpos : 0 < localWeight (memberDiv b) b.curve := weight_pos b.divisor
  by_cases hs : b.Simple
  · simpa [Branch.weight, hs] using (Nat.succ_le_of_lt hpos)
  · rw [Branch.weight, ite_eq_right hs]
    have hne : localWeight (memberDiv b) b.curve ≠ 1 := by
      intro h
      apply hs
      exact hcast.symm.trans (congrArg (fun n : ℕ => (n : ℕ∞)) h)
    omega
theorem proof : Low6969GeometryCut_2_3.c2 := by
  intro f Q l b E hprime hdim hE
  have hC := member_minimal b hE
  have hw : (b.weight : ℕ∞) ≤
      cycleLength (memberDiv b) b.curve b.divisor.isPrime := by
    calc
      _ ≤ (localWeight (memberDiv b) b.curve : ℕ∞) :=
        ENat.natCast_le_natCast.mpr (branch_weight_le b)
      _ = _ := weight_cast b.divisor
  exact ⟨⟨hC, hw.trans (membership_length b hE)⟩,
    dim_after_proper_cut hprime hdim (member_proper_on_graph b hE) hC⟩
end
end Low6969GeometryCut_2_3_2
end
section
set_option autoImplicit false
namespace Low6969GeometryCut_3
noncomputable section
open K1_13 (Row)
open K1_13_6 (toGeneric divisorIdeal cycleLength)
open K1_13_6_3 (CoeffIdeal JetIdeal)
open Low6969GeometryCut (membershipTest nextTest)
structure SimpleCut (g : Row 4) (surface P : JetIdeal) : Prop where
  proper : toGeneric (membershipTest g) ∉ surface
  minimal : (divisorIdeal surface (membershipTest g)).IsMinimalPrime P
  one : cycleLength (divisorIdeal surface (membershipTest g)) P minimal.isPrime = 1
  next : toGeneric (nextTest g) ∈ P
abbrev ShortSupport := Low6969FatPad.ShortSupport
end
end Low6969GeometryCut_3
end
section
set_option autoImplicit false
namespace Low6969GeometryCut_3
noncomputable section
open K1_13 K1_13_6 MvPolynomial
open P0_9_6_3 (iterate_separant_degree jetNumerator_degree)
theorem membershipTest_degree (f : Row 4) (r : ℕ) :
    (toGeneric (Low6969GeometryCut.membershipTest ((separant^[r]) f))).totalDegree ≤
      (chart (Low6969Prices.taylorLength + 1) (shape f).chamber).b := by
  let d := (shape f).chamber.b
  have hd : ((separant^[r]) f).totalDegree ≤ d :=
    (iterate_separant_degree f r).trans (le_max_left _ _)
  have hmap (P : Row 4) : (toGeneric P).totalDegree ≤ P.totalDegree :=
    Finset.sup_mono (support_map_subset _ _)
  unfold Low6969GeometryCut.membershipTest
  apply (hmap _).trans ((jetNumerator_degree hd Low6969Prices.taylorLength).trans ?_)
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _))) _ |>.trans (le_max_left _ _)
end
end Low6969GeometryCut_3
end
section
set_option autoImplicit false
namespace Low6969GeometryCut_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal)
open K1_13_6_3_1
attribute [local instance] MvPolynomial.algebraMvPolynomial
open P0_9_6_3 (flat_sepToGeo map_eq_maximal_of_length_one step_in_sep sep_sq_dvd_jet nonvanishing_of_simple_cut stable_of_simple_cut)
private theorem simple_saturation (g : K1_13.Row 4) (surface P : JetIdeal)
    (hdesc : (surface.comap sepToGeo).map sepToGeo = surface)
    (hsimple : SimpleCut g surface P) :
    ∀ x ∈ P.comap sepToGeo, ∃ t ∉ P.comap sepToGeo,
      t * x ∈ surface.comap sepToGeo ⊔ Ideal.span {rowToSep (Low6969GeometryCut.membershipTest g)} := by
  have : P.IsPrime := hsimple.minimal.isPrime
  let q := P.comap sepToGeo
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : P.LiesOver q := ⟨rfl⟩
  let A := Localization.AtPrime q
  let B := Localization.AtPrime P
  let _ : Algebra A B := Localization.AtPrime.algebraOfLiesOver q P
  have : Module.Flat SepJets GeoJets := flat_sepToGeo
  have : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q P sepToGeo rfl)
    infer_instance
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let J : Ideal SepJets := surface.comap sepToGeo ⊔ Ideal.span {rowToSep (Low6969GeometryCut.membershipTest g)}
  have hJ : J.map (algebraMap SepJets GeoJets) = divisorIdeal surface (Low6969GeometryCut.membershipTest g) := by
    change (surface.comap sepToGeo ⊔ Ideal.span {rowToSep (Low6969GeometryCut.membershipTest g)}).map sepToGeo = _
    rw [Ideal.map_sup, hdesc, Ideal.map_span, Set.image_singleton, sepToGeo_rowToSep,
      divisorIdeal]
  have hJB : (J.map (algebraMap SepJets A)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq SepJets A B,
      IsScalarTower.algebraMap_eq SepJets GeoJets B, ← Ideal.map_map, hJ]
    exact map_eq_maximal_of_length_one _ P hsimple.one
  intro x hx
  have hxB : algebraMap A B (algebraMap SepJets A x) ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsScalarTower.algebraMap_apply SepJets A B,
      IsScalarTower.algebraMap_apply SepJets GeoJets B, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hx
  rw [← hJB] at hxB
  have hxA : algebraMap SepJets A x ∈ J.map (algebraMap SepJets A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J.map (algebraMap SepJets A))]
    exact hxB
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A J x).mp hxA
theorem invariant_of_simpleCut {f Q : Row 4} {surface P : JetIdeal} {r : ℕ}
    (hz : (intersectionIdeal f Q).IsMinimalPrime surface)
    (hchart : CanonicalChart f surface r)
    (hlen : cycleLength (intersectionIdeal f Q) surface hz.isPrime < (K1.p : ℕ∞))
    (hI : Invariant ((separant^[r]) f) surface)
    (hcut : SimpleCut ((separant^[r]) f) surface P) : Invariant ((separant^[r]) f) P := by
  let g := (separant^[r]) f
  let T := surface.comap sepToGeo
  let q := P.comap sepToGeo
  let s := rowToSep (separant g)
  let e := rowToSep (Low6969GeometryCut.membershipTest g)
  have : T.IsPrime := hz.isPrime.comap sepToGeo
  have : q.IsPrime := hcut.minimal.isPrime.comap sepToGeo
  obtain ⟨D, hD, hstable⟩ := K1_13_6_3_1_2.proof g surface hz.isPrime hI
  have hle : T ≤ q := Ideal.comap_mono (le_sup_left.trans hcut.minimal.le)
  have he : e ∈ q := by
    change sepToGeo (rowToSep (Low6969GeometryCut.membershipTest g)) ∈ P
    rw [sepToGeo_rowToSep]
    apply hcut.minimal.le
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hsat := simple_saturation g surface P (K1_13_6_3_1_1.proof f Q surface hz hlen) hcut
  have hs : s ∉ T := by
    change sepToGeo (rowToSep (separant g)) ∉ surface
    rw [sepToGeo_rowToSep]
    exact hchart.2.2
  have hsq : s^2 ∣ e := sep_sq_dvd_jet g D hD Low6969Prices.taylorLength (by decide)
  have hs' : s ∉ q := nonvanishing_of_simple_cut T q hle hs hsq hsat
  have hnext : rowToSep (Low6969GeometryCut.nextTest g) ∈ q := by
    change sepToGeo (rowToSep (Low6969GeometryCut.nextTest g)) ∈ P
    rw [sepToGeo_rowToSep]
    exact hcut.next
  change rowToSep (jetNumerator g (Low6969Prices.taylorLength+1)) ∈ q at hnext
  rw [step_in_sep g D hD Low6969Prices.taylorLength] at hnext
  change s * D e - (↑(2*Low6969Prices.taylorLength) : SepJets) * D s * e ∈ q at hnext
  have hDe : D e ∈ q :=
    (‹q.IsPrime›.mem_or_mem
      ((q.sub_mem_iff_left (q.mul_mem_left _ he)).mp hnext)).resolve_left hs'
  intro U hU
  have hU' : rowToSep U ∈ q := by
    change sepToGeo (rowToSep U) ∈ P
    rwa [sepToGeo_rowToSep]
  have hflow : D (rowToSep U) ∈ q :=
    stable_of_simple_cut T q hle D hstable he hDe hsat _ hU'
  rw [← sepToGeo_rowToSep]
  change rowToSep (flowNumerator g U) ∈ q
  exact (hD U) ▸ hflow
end
end Low6969GeometryCut_3
end
section
set_option autoImplicit false
namespace Low6969GeometryCut_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal dimension cycleWeight)
open K1_13_6_3_6 MvPolynomial
open Height2307CutEnvelope (CutCycle)
open scoped BigOperators
open P0_9_6_2_3 (geometric_regular)
open P0_9_6_3 (coefficient_budget)
private theorem surface_dimension {f Q : Row 4} (hf : Irreducible f) (hQ : ¬ f ∣ Q)
    {P : JetIdeal} (hP : (intersectionIdeal f Q).IsMinimalPrime P) : dimension P = 2 := by
  let F : Ideal GeoJets := Ideal.span {toGeneric f}
  have heq : intersectionIdeal f Q = F ⊔ Ideal.span {toGeneric Q} := by
    simp only [intersectionIdeal, F, ← Ideal.span_union, Set.singleton_union]
  have hFP : F ≤ P := le_sup_left.trans (heq ▸ hP.le)
  have := hP.isPrime
  obtain ⟨A, hA, hAP⟩ := Ideal.exists_minimalPrimes_le hFP
  have hn : toGeneric Q ∉ A := by
    intro h
    obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hA h
    exact hy (Ideal.Quotient.eq_zero_iff_mem.mp (P0_9_6_2_3.geometric_regular hf hQ (by
      change Ideal.Quotient.mk F (toGeneric Q) * Ideal.Quotient.mk F y =
        Ideal.Quotient.mk F (toGeneric Q) * 0
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hxy, mul_zero])))
  have hsub : A ⊔ Ideal.span {toGeneric Q} ≤ P :=
    sup_le hAP (le_sup_right.trans (heq ▸ hP.le))
  have hmin : P ∈ (A ⊔ Ideal.span {toGeneric Q}).minimalPrimes := by
    refine ⟨⟨hP.isPrime, hsub⟩, fun B hB hBP => hP.2 ⟨hB.1, ?_⟩ hBP⟩
    rw [heq]
    exact sup_le ((hA.le.trans le_sup_left).trans hB.2) (le_sup_right.trans hB.2)
  have h₁ := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton
    (toGeneric_ne_zero hf.ne_zero) hA
  have := hA.isPrime
  have h₂ := principalCut_natDegree_affineHilbertPolynomial_add_one hn hmin
  rw [Nat.card_fin] at h₁
  change (affineHilbertPolynomial P).natDegree = 2
  omega
private theorem intersection_hilbert {f Q : Row 4} (hf : Irreducible f)
    (htop : 0 < (shape f).t) (hQ : ¬ f ∣ Q) :
    dimension (intersectionIdeal f Q) ≤ 2 ∧
      2 * (affineHilbertPolynomial (intersectionIdeal f Q)).coeff 2 ≤
        (shape f).b * (shape Q).b := by
  let F : Ideal GeoJets := Ideal.span {toGeneric f}
  have heq : intersectionIdeal f Q = F ⊔ Ideal.span {toGeneric Q} := by
    simp only [intersectionIdeal, F, ← Ideal.span_union, Set.singleton_union]
  have hF : F ≠ ⊤ := by
    intro ht
    have hg : IsUnit (toGeneric f) := Ideal.span_singleton_eq_top.mp ht
    have hdeg := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hg).2
    have ht : (shape f).t ≤ f.totalDegree := degreeOf_le_totalDegree _ _
    rw [totalDegree_toGeneric] at hdeg
    omega
  have hdeg := natDegree_affineHilbertPolynomial_span_singleton_add_one
    (toGeneric_ne_zero hf.ne_zero) hF
  rw [Nat.card_fin] at hdeg
  have hthree : (affineHilbertPolynomial (Ideal.span {toGeneric f})).natDegree = 3 := by omega
  have hcoeff : 6 * (affineHilbertPolynomial F).leadingCoeff = (shape f).b := by
    have hd := affineDegree_span_singleton (toGeneric_ne_zero hf.ne_zero)
    rw [affineDegree, hthree, totalDegree_toGeneric] at hd
    norm_num at hd
    exact hd
  have hc := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (P0_9_6_2_3.geometric_regular hf hQ) (totalDegree_toGeneric Q).le
  rw [← heq, hthree] at hc
  norm_num at hc
  refine ⟨hc.1, ?_⟩
  change 2 * (affineHilbertPolynomial (intersectionIdeal f Q)).coeff 2 ≤
    (f.totalDegree : ℚ) * (Q.totalDegree : ℚ)
  change 6 * (affineHilbertPolynomial F).leadingCoeff = (f.totalDegree : ℚ) at hcoeff
  nlinarith only [hc.2, congrArg (fun x : ℚ => x * Q.totalDegree) hcoeff]
set_option maxHeartbeats 0 in
theorem cutCycle {f Q : Row 4} (hf : Low6969Prices.SmallFactor f) (hQ : ¬ f ∣ Q)
    (hbox : InBox (shape Q) Low6969Prices.primaryBox) : CutCycle f Q := by
  classical
  let J := intersectionIdeal f Q
  obtain ⟨hj, hd⟩ := intersection_hilbert hf.1 hf.2.1 hQ
  obtain ⟨hfin, hcoeff⟩ := coefficient_budget J hj
  have hdim (P : JetIdeal) (hp : J.IsMinimalPrime P) : dimension P = 2 :=
    surface_dimension hf.1 hQ hp
  have hb : (shape Q).b ≤ Low6969Prices.primaryBox.b := hbox.1
  have hw : ∑ P ∈ J.minimalPrimesFinset, (cycleWeight J P : ℚ) * affineDegree P ≤
      ((shape f).b * Low6969Prices.primaryBox.b : ℕ) := by
    calc
      _ = 2 * ∑ P ∈ J.minimalPrimesFinset,
          (cycleWeight J P : ℚ) * (affineHilbertPolynomial P).coeff 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun P hP => ?_
        have hp := hdim P (Ideal.mem_minimalPrimesFinset.mp hP)
        simp only [affineDegree, Polynomial.leadingCoeff, hp]
        norm_num
        ring
      _ ≤ (shape f).b * (shape Q).b := (mul_le_mul_of_nonneg_left hcoeff (by norm_num)).trans hd
      _ ≤ ((shape f).b * Low6969Prices.primaryBox.b : ℕ) := by
        push_cast
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hb) (by positivity)
  refine ⟨?_, hw⟩
  intro P hp
  refine ⟨hdim P hp, length_pos hp.isPrime hp.le, ?_⟩
  have hsingle := Finset.single_le_sum
    (f := fun P => (cycleWeight J P : ℚ) * affineDegree P)
    (fun P _ => mul_nonneg (by positivity) (affineDegree_nonneg P))
    (Ideal.mem_minimalPrimesFinset.mpr hp)
  have hnat : cycleWeight J P ≤ (shape f).b * Low6969Prices.primaryBox.b := by
    exact_mod_cast (le_mul_of_one_le_right (by positivity : 0 ≤ (cycleWeight J P : ℚ))
      (degree_at_least_one P hp.isPrime.ne_top (hdim P hp))).trans (hsingle.trans hw)
  have hen : (cycleWeight J P : ℕ∞) = cycleLength J P hp.isPrime := by
    simp only [cycleWeight, dite_eq_left hp.isPrime]
    exact ENat.natCast_toNat (hfin P hp)
  rw [← hen]
  exact_mod_cast hnat
end
end Low6969GeometryCut_3
end
section
set_option autoImplicit false
namespace Low6969GeometryCut_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped Polynomial
open P0_9_6_3 (fresh_prime fresh_birational dim_fresh_of_recovery dim_lt_of_prime_lt)
private theorem classify {f Q g : Row 4} {surface P J : JetIdeal} (hp : P.IsPrime)
    (hJ : J.IsPrime) (hS : (intersectionIdeal f Q).IsMinimalPrime surface)
    (hCycle : ∀ T, (intersectionIdeal f Q).IsMinimalPrime T → dimension T = 2)
    (hsource : P = surface ∨ SimpleCut g surface P) (hcontain : intersectionIdeal f Q ≤ J)
    (hold : J ≤ P) {A : CoeffIdeal} (hdim : dimension J = dimension A) :
    ((dimension A = 1 ∧ J = P ∧ SimpleCut g surface P) ∨
      (dimension A = 2 ∧ (intersectionIdeal f Q).IsMinimalPrime J)) := by
  let _ := hJ
  obtain ⟨T, hT, hTJ⟩ := Ideal.exists_minimalPrimes_le hcontain
  have hdT := hCycle T hT
  have hdJ := natDegree_affineHilbertPolynomial_le_of_le hTJ
  change dimension J ≤ dimension T at hdJ
  have hdP : 1 ≤ dimension P := by
    rcases hsource with hEq | hcut
    · rw [hEq, hCycle surface hS]
      decide
    · let _ := hS.isPrime
      have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hcut.proper hcut.minimal
      change dimension P + 1 = dimension surface at hd
      rw [hCycle surface hS] at hd
      omega
  have hPJ := natDegree_affineHilbertPolynomial_le_of_le hold
  change dimension P ≤ dimension J at hPJ
  by_cases hd1 : dimension J = 1
  · have hEq : J = P := by
      by_contra hne
      have := dim_lt_of_prime_lt hJ hp (lt_of_le_of_ne hold hne)
      omega
    have hcut : SimpleCut g surface P := by
      rcases hsource with hEq' | hcut
      · rw [hEq, hEq', hCycle surface hS] at hd1
        contradiction
      · exact hcut
    exact Or.inl ⟨hdim.symm.trans hd1, hEq, hcut⟩
  · have hd2 : dimension J = 2 := by omega
    have hEq : T = J := by
      by_contra hne
      have := dim_lt_of_prime_lt hT.isPrime hJ (lt_of_le_of_ne hTJ hne)
      omega
    exact Or.inr ⟨hdim.symm.trans hd2, hEq ▸ hT⟩
theorem fresh_of_integrated {f Q : Row 4} {surface : JetIdeal} {r : ℕ} {P : JetIdeal}
    [hp : P.IsPrime] {U : (Polynomial (JetField P))}
    (hS : (intersectionIdeal f Q).IsMinimalPrime surface)
    (hCycle : ∀ T, (intersectionIdeal f Q).IsMinimalPrime T → dimension T = 2)
    (hsep : toGeneric (separant ((separant^[r]) f)) ∉ P)
    (hsource : P = surface ∨ SimpleCut ((separant^[r]) f) surface P)
    (hIntegrated : Integrated f Q ((separant^[r]) f) P U) :
    let A := coefficientKernel (componentConstants P) U
    FreshModel f A ∧
      ((dimension A = 1 ∧ freshImage A = P ∧ SimpleCut ((separant^[r]) f) surface P) ∨
        (dimension A = 2 ∧ (intersectionIdeal f Q).IsMinimalPrime (freshImage A))) := by
  let A := coefficientKernel (componentConstants P) U
  have hA : A.IsPrime := RingHom.ker_isPrime _
  obtain ⟨hext, hdim, _⟩ := K1_13_6_3_3_1.proof A hA
  obtain ⟨hcontain, hold, hg, hs⟩ :=
    K1_13_6_3_3.trajectory_to_fresh hIntegrated hsep
  have recovery := K1_13_6_3_3_2.proof
  refine ⟨⟨hA, hext, ⟨r, hg, hs⟩, fresh_birational recovery hA hext hg hs⟩, ?_⟩
  exact classify hp (fresh_prime hext) hS hCycle hsource hcontain hold
    ((dim_fresh_of_recovery recovery hA hext hg hs).trans hdim)
theorem shortSupport_of_degree {F : Type} [Field F] (k : Geom →+* F) (U : (Polynomial F))
    (hU : U.natDegree < Low6969Prices.taylorLength) : ShortSupport (coefficientKernel k U) := by
  intro i hi
  rw [coefficientKernel, RingHom.mem_ker, MvPolynomial.eval₂Hom_X']
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (hU.trans_le hi)
end
end Low6969GeometryCut_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Low6969GeometryCut_3
noncomputable section
open K1 K1_13 K1_13_6 Polynomial MvPolynomial
open K1_13_6_3
open Low6969Prices (primaryBox)
open P0_9_6_3 (freshImage_injective)
open P0_9_6_3 (curve_degree markPoint_inj canonical_unique)
open Height2307CutEnvelope (cycleWeight_ge surface_sum)
open scoped BigOperators
def c1 : Prop :=
  ∀ (f Q : Row 4) (r : ℕ) (P : JetIdeal) (hp : P.IsPrime),
    Low6969Prices.TrueWeightLE f Low6969Prices.anchorCutoff → Low6969Prices.TrueWeightLE Q Low6969Prices.primaryCutoff →
    intersectionIdeal f Q ≤ P →
    let g := (separant^[r]) f
    toGeneric g ∈ P → toGeneric (separant g) ∉ P →
    toGeneric (Low6969GeometryCut.membershipTest g) ∈ P → Invariant g P →
    ∃ U : (Polynomial (JetField P)), @Integrated f Q g P hp U ∧ U.natDegree < Low6969Prices.taylorLength
def c2 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime → (extendIdeal A).IsPrime → dimension A = 2 →
    FreshBirational A → ShortSupport A →
    2 * affineDegree A ≤ 133378 * affineDegree (freshImage A)
private def CurveSource (f Q : Row 4) (l : ℕ) (P : JetIdeal) : Prop :=
  ∃ (surface : JetIdeal) (r : ℕ) (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime ∧
    CanonicalChart f surface r ∧ SimpleCut ((separant^[r]) f) surface P
private def FamilyCase (f Q : Row 4) (l : ℕ) (A : CoeffIdeal) : Prop :=
  (dimension A = 1 ∧ CurveSource f Q l (freshImage A)) ∨
  (dimension A = 2 ∧ (intersectionIdeal f Q).IsMinimalPrime (freshImage A))
private theorem curve_sum {f Q : Row 4} {l : ℕ} (hc : Height2307CutEnvelope.CutCycle f Q)
    (T : Finset JetIdeal) (hT : ∀ P ∈ T, CurveSource f Q l P) :
    (l : ℚ) * (∑ P ∈ T, affineDegree P) ≤ (Low6969GeometryCut.membershipDegree (shape f) : ℕ) := by
  classical
  let J := intersectionIdeal f Q
  let S := J.minimalPrimesFinset
  let b := (chart (Low6969Prices.taylorLength + 1) (shape f).chamber).b
  let parent : JetIdeal → JetIdeal := fun P =>
    if h : P ∈ T then Classical.choose (hT P h) else ⊥
  have hd (P : JetIdeal) (hP : P ∈ T) :
      ∃ (r : ℕ) (hz : J.IsMinimalPrime (parent P)),
        (l : ℕ∞) ≤ cycleLength J (parent P) hz.isPrime ∧
        CanonicalChart f (parent P) r ∧ SimpleCut ((separant^[r]) f) (parent P) P := by
    simpa only [parent, dite_eq_left hP] using Classical.choose_spec (hT P hP)
  have hm (P : JetIdeal) (hP : P ∈ T) : parent P ∈ S := by
    obtain ⟨_, hz, _⟩ := hd P hP
    exact Ideal.mem_minimalPrimesFinset.mpr hz
  have hfibre (surface : JetIdeal) :
      (∑ P ∈ T.filter (fun P => parent P = surface), (l : ℚ) * affineDegree P) ≤
        b * ((cycleWeight J surface : ℚ) * affineDegree surface) := by
    let V := T.filter (fun P => parent P = surface)
    by_cases hV : V.Nonempty
    · obtain ⟨P₀, hP₀⟩ := hV
      obtain ⟨hP₀T, hP₀parent⟩ := Finset.mem_filter.mp hP₀
      have hdata := hd P₀ hP₀T
      rw [hP₀parent] at hdata
      obtain ⟨r, hz, hhigh, hchart, hcut⟩ := hdata
      let _ := hz.isPrime
      let g := (separant^[r]) f
      let B := (divisorIdeal surface (Low6969GeometryCut.membershipTest g)).minimalPrimesFinset
      have hsub : V ⊆ B := by
        intro P hP
        obtain ⟨hPT, hPparent⟩ := Finset.mem_filter.mp hP
        obtain ⟨r', hz', _, hchart', hcut'⟩ := hd P hPT
        rw [hPparent] at hchart' hcut'
        have hEq := canonical_unique hchart' hchart
        subst r'
        exact Ideal.mem_minimalPrimesFinset.mpr hcut'.minimal
      have hB : (∑ P ∈ B, affineDegree P) ≤ (b : ℚ) * affineDegree surface :=
        principalCut_sum_affineDegree_minimalPrimes_le hcut.proper (membershipTest_degree f r)
      have hl := cycleWeight_ge hc hz hhigh
      calc
        _ = (l : ℚ) * (∑ P ∈ V, affineDegree P) := (Finset.mul_sum ..).symm
        _ ≤ (l : ℚ) * ((b : ℚ) * affineDegree surface) :=
          mul_le_mul_of_nonneg_left
            ((Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun P _ _ => affineDegree_nonneg P)).trans hB) (by positivity)
        _ ≤ _ := by
          rw [mul_left_comm]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) (affineDegree_nonneg _))
            (by positivity)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hV
      change (∑ P ∈ V, (l : ℚ) * affineDegree P) ≤ _
      rw [he, Finset.sum_empty]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (affineDegree_nonneg _))
  calc
    _ = ∑ P ∈ T, (l : ℚ) * affineDegree P := Finset.mul_sum ..
    _ = ∑ surface ∈ S, ∑ P ∈ T.filter (fun P => parent P = surface),
          (l : ℚ) * affineDegree P :=
      (Finset.sum_fiberwise_of_maps_to hm _).symm
    _ ≤ ∑ surface ∈ S, (b : ℚ) * ((cycleWeight J surface : ℚ) * affineDegree surface) :=
      Finset.sum_le_sum (fun surface _ => hfibre surface)
    _ = (b : ℚ) * ∑ surface ∈ S, (cycleWeight J surface : ℚ) * affineDegree surface :=
      (Finset.mul_sum ..).symm
    _ ≤ (b : ℚ) * (((shape f).b * primaryBox.b : ℕ) : ℚ) :=
      mul_le_mul_of_nonneg_left hc.weighted_degree (by positivity)
    _ = _ := by simp only [Low6969GeometryCut.membershipDegree, Nat.cast_mul, b]; ring
private theorem family_of_mark (h1 : c1)
    {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}
    (input : Low6969GeometryCut.CutInput Γ s f Q l) (hc : Height2307CutEnvelope.CutCycle f Q)
    {γ : K} (hγ : γ ∈ Γ) (hmark : Low6969GeometryCut.ContinuedMark f Q l (extend (s γ))) :
    ∃ A : CoeffIdeal, FreshModel f A ∧ ShortSupport A ∧ FamilyCase f Q l A ∧ γ ∈ marksOn Γ s A := by
  obtain ⟨surface, r, hz, hcont⟩ := hmark
  let g := (separant^[r]) f
  have hdim (T : JetIdeal) (hT : (intersectionIdeal f Q).IsMinimalPrime T) :
      dimension T = 2 := (hc.local_bound T hT).1
  have hnum : (shape f).b * primaryBox.b < K1.p :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ input.small.2.2.1.1) (by decide)
  have hsmall : cycleLength (intersectionIdeal f Q) surface hz.base.isPrime < (K1.p : ℕ∞) :=
    (hc.local_bound surface hz.base).2.2.trans_lt (by exact_mod_cast hnum)
  have integrate (P : JetIdeal) (hp : P.IsPrime) (hle : surface ≤ P)
      (hpoint : P ≤ markIdeal (extend (s γ))) (hI : Invariant g P)
      (hE : toGeneric (Low6969GeometryCut.membershipTest g) ∈ P)
      (hbranch : P = surface ∨ SimpleCut g surface P) :
      ∃ A : CoeffIdeal, FreshModel f A ∧ ShortSupport A ∧ FamilyCase f Q l A ∧ γ ∈ marksOn Γ s A := by
    have hg : toGeneric g ∈ P := hle (hz.chart.2.1 r le_rfl)
    have hsep : toGeneric (separant g) ∉ P :=
      fun hm => hz.regular (K1_13_6_1.mem_markIdeal.mp (hpoint hm))
    obtain ⟨U, hU, hshort⟩ := h1 f Q r P hp input.small.2.2.2 input.weight
      (hz.base.1.2.trans hle) hg hsep hE hI
    let _ := hp
    obtain ⟨hA, hcase⟩ := fresh_of_integrated hz.base hdim hsep hbranch hU
    refine ⟨_, hA, shortSupport_of_degree _ U hshort, ?_, mem_marksOn.mpr ⟨hγ, ?_⟩⟩
    · rcases hcase with ⟨hd, heq, hsimple⟩ | hsurface
      · exact Or.inl ⟨hd, surface, r, hz.base, hz.high, hz.chart, heq.symm ▸ hsimple⟩
      · exact Or.inr hsurface
    · have hs : (extend (s γ)).natDegree < taylorLength := by
        rw [Polynomial.natDegree_map]
        exact (Nat.lt_succ_of_le (input.degree γ hγ)).trans (by decide)
      exact hU.specializes _ hs hpoint hz.regular
  rcases hcont with hE | ⟨P, hm, hproper, hpoint, hone, hnext⟩
  · exact integrate surface hz.base.isPrime le_rfl hz.point hz.invariant hE (Or.inl rfl)
  · have hs : SimpleCut g surface P := ⟨hproper, hm, hone, hnext⟩
    have hI := invariant_of_simpleCut hz.base hz.chart hsmall hz.invariant hs
    have hl : divisorIdeal surface (Low6969GeometryCut.membershipTest g) ≤ P := hm.1.2
    have hE : toGeneric (Low6969GeometryCut.membershipTest g) ∈ P :=
      hl (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
    exact integrate P hm.isPrime (le_sup_left.trans hl) hpoint hI hE (Or.inr hs)
theorem of_children (h1 : c1) (h2 : c2) : Low6969GeometryCut.c3 := by
  classical
  intro Γ s f Q l input
  have hc := cutCycle input.small input.proper input.box
  let B := Γ.filter (fun γ => Low6969GeometryCut.ContinuedMark f Q l (extend (s γ)))
  have hw (γ : B) :
      ∃ A : CoeffIdeal, FreshModel f A ∧ ShortSupport A ∧ FamilyCase f Q l A ∧ γ.val ∈ marksOn Γ s A := by
    obtain ⟨hγ, hmark⟩ := Finset.mem_filter.mp γ.property
    exact family_of_mark h1 input hc hγ hmark
  let A : B → CoeffIdeal := fun γ => Classical.choose (hw γ)
  have hA (γ : B) : FreshModel f (A γ) ∧ ShortSupport (A γ) ∧ FamilyCase f Q l (A γ) ∧ γ.val ∈ marksOn Γ s (A γ) :=
    Classical.choose_spec (hw γ)
  let T := B.attach.image A
  let Tc := T.filter (fun P => dimension P = 1)
  let Td := T.filter (fun P => dimension P = 2)
  have hT (P : CoeffIdeal) (hp : P ∈ T) :
      FreshModel f P ∧ ShortSupport P ∧ FamilyCase f Q l P ∧ (marksOn Γ s P).Nonempty := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(hA γ).1, (hA γ).2.1, (hA γ).2.2.1, ⟨γ.val, (hA γ).2.2.2⟩⟩
  have hd (P : CoeffIdeal) (hp : P ∈ T) : dimension P = 1 ∨ dimension P = 2 :=
    (hT P hp).2.2.1.imp And.left And.left
  have hC (P : CoeffIdeal) (hp : P ∈ Tc) : CurveSource f Q l (freshImage P) := by
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp hp
    rcases (hT P ht).2.2.1 with h | h
    · exact h.2
    · exact False.elim (by omega)
  have hD (P : CoeffIdeal) (hp : P ∈ Td) :
      (intersectionIdeal f Q).IsMinimalPrime (freshImage P) := by
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp hp
    rcases (hT P ht).2.2.1 with h | h
    · exact False.elim (by omega)
    · exact h.2
  have hinj : Set.InjOn freshImage (T : Set CoeffIdeal) := by
    apply (freshImage_injective f).mono
    intro P hp
    have hm := (hT P hp).1
    exact ⟨hm.prime, hm.regular⟩
  have hpart (P : CoeffIdeal) : marksOn Γ s P ⊆ Γ := fun _ h => (mem_marksOn.mp h).1
  let C := piecesOf Tc (marksOn Γ s) (fun P _ => hpart P)
  let D := piecesOf Td (marksOn Γ s) (fun P _ => hpart P)
  have hdegree (γ : K) (hγ : γ ∈ Γ) : (s γ).natDegree < taylorLength :=
    (Nat.lt_succ_of_le (input.degree γ hγ)).trans (by decide)
  refine ⟨C, D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    let P := Tc.equivFin.symm i
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp P.property
    exact curveSections_of_prime (hT P ht).1.prime he
      (fun γ hγ => hdegree γ (hpart P hγ))
      ((markPoint_inj input.distinct hdegree).mono (hpart P))
      (fun _ hγ => (mem_marksOn.mp hγ).2)
  · intro i
    let P := Td.equivFin.symm i
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp P.property
    exact surfaceSections_of_prime (hT P ht).1.prime he
      (fun γ hγ => hdegree γ (hpart P hγ))
      ((markPoint_inj input.distinct hdegree).mono (hpart P))
      (fun _ hγ => (mem_marksOn.mp hγ).2)
  · intro i
    let P := Tc.equivFin.symm i
    have ht := hT P (Finset.mem_filter.mp P.property).1
    exact degreeAllowance_pos ht.1.prime ht.2.2.2
  · intro i
    let P := Td.equivFin.symm i
    have ht := hT P (Finset.mem_filter.mp P.property).1
    exact degreeAllowance_pos ht.1.prime ht.2.2.2
  · intro γ hγ hm
    let γ' : B := ⟨γ, Finset.mem_filter.mpr ⟨hγ, hm⟩⟩
    have hmem : A γ' ∈ T := Finset.mem_image_of_mem A (Finset.mem_attach _ _)
    rcases hd _ hmem with h | h
    · exact Finset.mem_union_left _ (mem_piecesOf.mpr
        ⟨_, Finset.mem_filter.mpr ⟨hmem, h⟩, (hA γ').2.2.2⟩)
    · exact Finset.mem_union_right _ (mem_piecesOf.mpr
        ⟨_, Finset.mem_filter.mpr ⟨hmem, h⟩, (hA γ').2.2.2⟩)
  · have hsum := curve_sum hc (Tc.image freshImage) (by
      intro P hp
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hp
      exact hC A hA)
    have heq : (∑ P ∈ Tc, affineDegree P) = ∑ P ∈ Tc.image freshImage, affineDegree P := by
      rw [Finset.sum_image (fun P hP R hR h => hinj (Finset.mem_filter.mp hP).1
        (Finset.mem_filter.mp hR).1 h)]
      apply Finset.sum_congr rfl
      intro P hP
      obtain ⟨ht, he⟩ := Finset.mem_filter.mp hP
      have hf := (hT P ht).1
      exact curve_degree P hf.prime hf.extended_prime he hf.birational
    rw [← heq] at hsum
    exact_mod_cast
      (mul_le_mul_of_nonneg_left (piecesOf_le_degree (T := Tc) (part := marksOn Γ s))
        (show (0 : ℚ) ≤ l by positivity)).trans hsum
  · have hsum := surface_sum hc (Td.image freshImage) (by
      intro P hp
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hp
      exact hD A hA)
    have hbound : (2 : ℚ) * (D.total : ℚ) ≤ 133378 * (((shape f).b * primaryBox.b : ℕ) : ℚ) := by
      calc
        _ ≤ 2 * (∑ P ∈ Td, affineDegree P) :=
          mul_le_mul_of_nonneg_left (piecesOf_le_degree (T := Td) (part := marksOn Γ s))
            (by positivity)
        _ ≤ ∑ P ∈ Td, 133378 * affineDegree (freshImage P) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro P hP
          obtain ⟨ht, he⟩ := Finset.mem_filter.mp hP
          have hf := (hT P ht).1
          exact h2 P hf.prime hf.extended_prime he hf.birational (hT P ht).2.1
        _ = 133378 * (∑ P ∈ Td.image freshImage, affineDegree P) := by
          rw [Finset.mul_sum, Finset.sum_image (fun P hP R hR h =>
            hinj (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hR).1 h)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
    rw [Nat.mul_assoc]
    exact_mod_cast hbound
end
end Low6969GeometryCut_3
end
section
set_option autoImplicit false
set_option maxRecDepth 200000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Low6969GeometryCut_3_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_2 Polynomial
private theorem old_weight {H : Row 4} {B : ℕ} (h : Low6969Prices.TrueWeightLE H B) :
    TrueWeightLE H (2 * B) := by
  intro m hm
  have hpoint (i : Fin 4) :
      133671 - i.val ≤ 2 * (Low6969Prices.physicalDegree - i.val) := by
    have hi := i.isLt
    change 133671 - i.val ≤ 2 * (133378 - i.val)
    omega
  have hsum : m.sum (fun i a => (133671 - i.val) * a) ≤
      2 * m.sum (fun i a => (133378 - i.val) * a) := by
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (hpoint i)
  have hnew := h m hm
  change (H.coeff m).natDegree + m.sum (fun i a => (133378 - i.val) * a) ≤ B at hnew
  change (H.coeff m).natDegree + m.sum (fun i a => (133671 - i.val) * a) ≤ 2 * B
  omega
open P0_9_6_3_1 (iterate_zero_of_le differentialTaylor_degree rowAt_eval initial_dividedIterate chartTaylor_toComponent)
theorem proof : Low6969GeometryCut_3.c1 := by
  intro f Q r P hp hf hQ hcut
  dsimp only
  intro hg hsep hmember hinv
  let g := (separant^[r]) f
  let e := rowAt P
  let x := abscissa e
  let y := jetCoordinate e 0
  let k := toComponent P
  obtain ⟨D, hx, hshift, haction⟩ := K1_13_6_3_2_1.proof g P hp hg hsep hinv
  have hs : e (separant g) ≠ 0 := fun hz => hsep ((rowAt_eq_zero P _).mp hz)
  have hM : ((D : ContractedField P → ContractedField P)^[Low6969Prices.taylorLength]) y = 0 := by
    have hz := (rowAt_eq_zero P (Low6969GeometryCut.membershipTest g)).mpr hmember
    change e (jetNumerator g Low6969Prices.taylorLength) = 0 at hz
    rw [jetNumerator_eq_iterate e g D haction] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hs)
  have hlength : Low6969Prices.taylorLength ≤ taylorLength := by decide
  have hOldM := iterate_zero_of_le D y hM hlength
  have hcanon : chartTaylor e g = differentialTaylor D x y := by
    unfold chartTaylor differentialTaylor
    apply congrArg (fromTaylor (M := taylorLength) x)
    funext i
    unfold dividedIterate
    rw [jetNumerator_eq_iterate e g D haction, mul_div_cancel_left₀ _ (pow_ne_zero _ hs)]
  have hmap : (differentialTaylor D x y).map k = chartTaylor (componentRow P) g := by
    rw [← hcanon]
    exact chartTaylor_toComponent P g
  have hdegree : (chartTaylor (componentRow P) g).natDegree < Low6969Prices.taylorLength := by
    rw [← hmap]
    exact natDegree_map_le.trans_lt
      (differentialTaylor_degree D x y (by decide) hlength hM)
  have hinitial (i : Fin 4) : dividedIterate D y i.val = jetCoordinate e i :=
    initial_dividedIterate e D hshift i
  have hconstants : k.comp (algebraMap Geom (ContractedField P)) = componentConstants P := by
    ext a
    exact toComponent_constantsAt P a
  have hcontinue (H : Row 4) (B : ℕ) (hW : TrueWeightLE H B) (hguard : B + 3 < K1.p)
      (hH : toGeneric H ∈ P) :
      trajectory (componentConstants P) H (chartTaylor (componentRow P) g) = 0 := by
    have hzero : MvPolynomial.eval₂ (Polynomial.aeval x).toRingHom
        (fun i => dividedIterate D y i.val) H = 0 := by
      simp only [hinitial]
      exact (rowAt_eval P H).trans ((rowAt_eq_zero P H).mpr hH)
    have hh := congrArg (fun U : (Polynomial (ContractedField P)) => U.map k)
      (K1_13_6_3_2_2.proof (ContractedField P) D x y hx hOldM H B hW hguard hzero)
    rw [map_trajectory, hconstants, hmap, Polynomial.map_zero] at hh
    exact hh
  have hfP : toGeneric f ∈ P :=
    hcut (Ideal.subset_span (by simp : toGeneric f ∈ ({toGeneric f, toGeneric Q} : Set GeoJets)))
  have hQP : toGeneric Q ∈ P :=
    hcut (Ideal.subset_span (by simp : toGeneric Q ∈ ({toGeneric f, toGeneric Q} : Set GeoJets)))
  have hfW := old_weight hf
  have hQW := old_weight hQ
  have hfguard : 2 * Low6969Prices.anchorCutoff + 3 < K1.p := by decide
  have hQguard : 2 * Low6969Prices.primaryCutoff + 3 < K1.p := by decide
  refine ⟨chartTaylor (componentRow P) g, ⟨hdegree.trans_le hlength, ?_, ?_, ?_, ?_, ?_⟩, hdegree⟩
  · intro i
    rw [← hmap]
    change (hasseDeriv i.val ((differentialTaylor D x y).map k)).eval
      (onComponent P (MvPolynomial.C genericArgument)) = _
    rw [Polynomial.hasseDeriv_map, ← toComponent_abscissa P]
    change ((hasseDeriv i.val (differentialTaylor D x y)).map k).eval (k x) = _
    rw [Polynomial.eval_map_apply]
    have hT := fromTaylor_hasse x (fun j => dividedIterate D y j.val)
      (i.castLE (by decide : 4 ≤ taylorLength))
    change (hasseDeriv i.val (differentialTaylor D x y)).eval x = dividedIterate D y i.val at hT
    rw [hT, hinitial]
    exact toComponent_jetCoordinate P i
  · exact hcontinue f _ hfW hfguard hfP
  · exact hcontinue Q _ hQW hQguard hQP
  · exact hcontinue g _ (iterate_separant_weight hfW r) hfguard hg
  · intro S hS hPS hsepS
    exact K1_13_6_3_2_3.proof g P hg hsep S hS hPS hsepS
end
end Low6969GeometryCut_3_1
end
namespace Low6969GeometryCut_3_2
theorem proof : Low6969GeometryCut_3.c2 := Low6969FatPad.padding
end Low6969GeometryCut_3_2

namespace Low6969GeometryCut

private theorem mixed_bound : c2 :=
  Low6969GeometryCut_2.of_children Low6969GeometryCut_2_1.proof Low6969GeometryCut_2_2.proof
    (Low6969GeometryCut_2_3.of_children Low6969GeometryCut_2_3_1.proof Low6969GeometryCut_2_3_2.proof)

theorem continued_bound : c3 :=
  Low6969GeometryCut_3.of_children Low6969GeometryCut_3_1.proof Low6969GeometryCut_3_2.proof

/-- The original box price covers all proper cuts. -/
theorem proof_old : c6Old := of_children Low6969GeometryCut_1.proof mixed_bound continued_bound

/-- On eligible shapes, use both the original box bound and the refined mixed-charge bound. -/
theorem proof (htilt : c2Tilted) (hactive : c2Active) : Low6969Prices.c6 :=
  of_children_active Low6969GeometryCut_1.proof continued_bound proof_old htilt hactive

end Low6969GeometryCut

end Z6969Source2286

-- Source: ProximityPrize.SubmissionLower.Low6969ActiveCycleBound
section Z6969Source2287
set_option autoImplicit true
set_option Elab.async false

set_option autoImplicit false
set_option Elab.async false

namespace Low6969ActiveCycle

noncomputable section

open Low48BentCycle (Family mixedDegree properCut cycleComparison divisorBound diagonalExponents)

open Low6969Prices (SmallFactor)
open Low6969GeometryCut_2 (Branch)
open Low6969GeometryCut_2_3 (graphLift chart_index_eq graphLift_same_chart
  membership_same_chart graphLift_comap member_proper_on_graph)
open P0_9_6_2_3 (cylinder_comparison)
open K1_13 (Row)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5)
open K1_13_6_2_4 (Exponent Component DimLE OfDim LengthAt ambient_dim cylinder cylinder_injective
  dim_le_after_section oldEmbedding pointIdeal sectionIdeal)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators Pointwise

open K1_13_6_2_4 (eval_surjective pointIdeal_injective point_component exists_coordinate_cut)
open Low6969GeometryCut_2_3 (liftedPoint eval_liftedPoint liftedPoint_old liftedPoint_mem)

def Section (R : Family) (i : Fin 5) (D : GeoJets5) : Prop :=
  ∀ m ∈ D.support, m ∈ R i

structure Doubled (R B : Family) : Prop where
  zero_mem : ∀ i, 0 ∈ R i
  pair_mem : ∀ i, ∀ a ∈ R i, ∀ b ∈ R i, a + b ∈ B i
  last_coordinate : ∀ v : Fin 5, Finsupp.single v 1 ∈ R 4

theorem Doubled.raw_mem {R B : Family} (hB : Doubled R B)
    {i : Fin 5} {a : Exponent} (ha : a ∈ R i) : a ∈ B i := by
  simpa using hB.pair_mem i a ha 0 (hB.zero_mem i)

theorem Doubled.double_zero {R B : Family} (hB : Doubled R B) (i : Fin 5) : 0 ∈ B i :=
  hB.raw_mem (hB.zero_mem i)

theorem Doubled.double_coordinates {R B : Family} (hB : Doubled R B) (v : Fin 5) :
    ∃ i, Finsupp.single v 1 ∈ B i :=
  ⟨4, hB.raw_mem (hB.last_coordinate v)⟩

theorem square_support {R B : Family} (hB : Doubled R B) {i : Fin 5} {D : GeoJets5}
    (hD : Section R i D) : ∀ m ∈ (D ^ 2).support, m ∈ B i := by
  classical
  intro m hm
  rw [pow_two] at hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul D D hm)
  exact hB.pair_mem i a (hD a ha) b (hD b hb)

private theorem constant_section {R B : Family} (hB : Doubled R B) (i : Fin 5) (a : GeoField) :
    Section R i (MvPolynomial.C a) := by
  classical
  intro m hm
  by_cases ha : a = 0
  · simp [ha] at hm
  · rw [MvPolynomial.support_C, ite_eq_right ha, Finset.mem_singleton] at hm
    exact hm ▸ hB.zero_mem i

private theorem coordinate_section {R B : Family} (hB : Doubled R B)
    (z : Fin 5 → GeoField) (i : Fin 5) : Section R 4 (MvPolynomial.X i - MvPolynomial.C (z i)) := by
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ _ _ hm) with hX | hC
  · rw [MvPolynomial.support_X, Finset.mem_singleton] at hX
    exact hX ▸ hB.last_coordinate i
  · exact constant_section hB 4 (z i) m hC

private theorem point_degree (B : Family) [∀ i, Finite (B i)] (z : Fin 5 → GeoField) :
    mixedDegree B (pointIdeal z) ∅ = 1 := by
  let A := diagonalExponents B (positiveDiagonal ∅)
  let φ := (MvPolynomial.aeval z).comp (MvPolynomial.monomialMap GeoField A)
  have hφ : Function.Surjective φ := fun a => ⟨MvPolynomial.C a, φ.commutes a⟩
  have heq : (pointIdeal z).comap (MvPolynomial.monomialMap GeoField A) = RingHom.ker φ := rfl
  let e := Ideal.quotientKerAlgEquivOfSurjective hφ
  let := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  unfold mixedDegree
  simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, tsub_self,
    pow_zero, one_mul, div_one]
  change (MvPolynomial.affineHilbertPolynomial
    ((pointIdeal z).comap (MvPolynomial.monomialMap GeoField A))).coeff 0 = 1
  rw [heq, MvPolynomial.affineHilbertPolynomial_eq_C_finrank, Polynomial.coeff_C_zero,
    e.toLinearEquiv.finrank_eq, Module.finrank_self, Nat.cast_one]
theorem point_bound {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (C : Ideal GeoJets5) (hprime : C.IsPrime) (hdim : OfDim C 1)
    (U : Finset (Fin 5 → GeoField)) (hU : ∀ z ∈ U, C ≤ pointIdeal z)
    (hslice : U.card ≤ 1 ∨ ∃ D, Section R 4 D ∧ D ∉ C ∧
      ∀ z ∈ U, MvPolynomial.eval z D = 0) :
    (U.card : ℚ) ≤ mixedDegree B C {4} := by
  classical
  have cut_bound (D : GeoJets5) (hB' : Section R 4 D) (hproper : D ∉ C)
      (hD : ∀ z ∈ U, MvPolynomial.eval z D = 0) : (U.card : ℚ) ≤ mixedDegree B C {4} := by
    have hb := divisorBound B hB.double_zero hB.double_coordinates C ∅ 4 hprime (by simp) hdim D
      (fun m hm => hB.raw_mem (hB' m hm)) (square_support hB hB') hproper U pointIdeal (fun _ => 1)
      pointIdeal_injective.injOn (fun z hz => point_component hprime hdim (hU z hz) hproper (hD z hz))
    simpa [point_degree] using hb
  rcases hslice with hone | ⟨D, hD, hp, hz⟩
  · by_cases hempty : U = ∅
    · apply cut_bound (MvPolynomial.C 1) (constant_section hB 4 1)
      · rw [map_one]
        exact (Ideal.ne_top_iff_one C).mp hprime.ne_top
      · simp [hempty]
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hlt : C < pointIdeal z := by
      refine lt_of_le_of_ne (hU z hz) ?_
      intro h
      rw [h, OfDim, pointIdeal] at hdim
      have e := (MvPolynomial.eval z).quotientKerEquivOfSurjective (eval_surjective z)
      rw [e.ringKrullDim, ringKrullDim_eq_zero_of_field] at hdim
      exact (by decide : (0 : WithBot ℕ∞) ≠ 1) hdim
    obtain ⟨i, hi⟩ := exists_coordinate_cut hlt
    apply cut_bound _ (coordinate_section hB z i) hi
    intro y hy
    have hyz := Finset.card_le_one.mp hone y hy z hz
    subst y
    simp
  · exact cut_bound D hD hp hz
def Slice {f Q : Row 4} {l : ℕ} (R : Family) (b : Branch f Q l) (T : Finset JetPoint) : Prop :=
  T.card ≤ 1 ∨ ∃ D, Section R 4 D ∧ b.onGraph D ∉ b.localCurve ∧
    ∀ p ∈ T, ∀ h : b.Contains p, b.liftedEval p h D = 0

theorem bound_marks {f Q : Row 4} {l : ℕ} {R B : Family} [∀ i, Finite (B i)]
    (hB : Doubled R B) (b : Branch f Q l) (T : Finset JetPoint)
    (hT : ∀ y ∈ T, b.Contains y) (hSlice : Slice R b T)
    (hprime : (graphLift b b.curve).IsPrime) (hdim : OfDim (graphLift b b.curve) 1) :
    (T.card : ℚ) ≤ mixedDegree B (graphLift b b.curve) {4} := by
  classical
  let U := T.image (liftedPoint b)
  have hcard : U.card = T.card := Finset.card_image_of_injOn (by
    intro x hx y hy he
    funext i
    have hz := congrFun he i.castSucc
    rwa [liftedPoint_old b x (hT x hx), liftedPoint_old b y (hT y hy)] at hz)
  rw [← hcard]
  apply point_bound hB _ hprime hdim U
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact liftedPoint_mem b y (hT y hy)
  · rcases hSlice with hsingle | ⟨D, hD, hproper, hvanish⟩
    · exact Or.inl (hcard ▸ hsingle)
    · refine Or.inr ⟨D, hD, hproper, ?_⟩
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      rw [eval_liftedPoint b y (hT y hy)]
      exact hvanish y hy (hT y hy)
private theorem initial_bound {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (f Q : Row 4) (l : ℕ) (hf : SmallFactor f) (hQ : ¬ f ∣ Q)
    (hfbox : Section R 0 (oldEmbedding (toGeneric f)))
    (hQbox : Section R 1 (oldEmbedding (toGeneric Q))) (S : Finset (Ideal GeoJets))
    (hS : ∀ P ∈ S, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime) :
    (∀ P ∈ S, (cylinder P).IsPrime ∧ OfDim (cylinder P) 3) ∧
      (l : ℚ) * (∑ P ∈ S, mixedDegree B (cylinder P) {2, 3, 4}) ≤
        mixedDegree B ⊥ Finset.univ := by
  classical
  let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
  let J := sectionIdeal A (oldEmbedding (toGeneric Q))
  obtain ⟨hregQ, hAlgebra⟩ := cylinder_comparison f Q hf.1 hQ
  have hregf : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets5)
      (oldEmbedding (toGeneric f))) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne
      (K1_13_6_3_6.toGeneric_ne_zero hf.1.ne_zero)
  have hAdim : DimLE A 4 := dim_le_after_section hregf ambient_dim
  have hJdim : DimLE J 3 := dim_le_after_section hregQ hAdim
  have hgeom (P : Ideal GeoJets) (hP : P ∈ S) :
      (cylinder P).IsPrime ∧ OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P), (l : ℕ∞) ≤ LengthAt J (cylinder P) hc.isPrime := by
    obtain ⟨h, hw⟩ := hS P hP
    obtain ⟨hd, hc, hl⟩ := hAlgebra P h
    exact ⟨hc.isPrime, hd, hc, hw.trans hl⟩
  refine ⟨fun P hP => ⟨(hgeom P hP).1, (hgeom P hP).2.1⟩, ?_⟩
  have hs := cycleComparison B hB.double_zero hB.double_coordinates J {2, 3, 4} hJdim S cylinder (fun _ => l) cylinder_injective.injOn
    (fun P hP => (hgeom P hP).2.2)
  have hcutQ := properCut B hB.double_zero A {2, 3, 4} 1 (by decide) hAdim
    (oldEmbedding (toGeneric Q)) (fun m hm => hB.raw_mem (hQbox m hm)) (square_support hB hQbox) hregQ
  have hcutf := properCut B hB.double_zero ⊥ {1, 2, 3, 4} 0 (by decide) ambient_dim
    (oldEmbedding (toGeneric f)) (fun m hm => hB.raw_mem (hfbox m hm)) (square_support hB hfbox) hregf
  have hall : (insert (0 : Fin 5) {1, 2, 3, 4} : Finset (Fin 5)) = Finset.univ := by decide
  rw [hall] at hcutf
  rw [Finset.mul_sum]
  exact hs.trans (hcutQ.trans hcutf)
theorem bound {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (f Q : Row 4) (l : ℕ) (hf : SmallFactor f) (hproper : ¬ f ∣ Q)
    (hfbox : Section R 0 (oldEmbedding (toGeneric f)))
    (hQ : Section R 1 (oldEmbedding (toGeneric Q)))
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hF : ∀ b ∈ F, Section R 2 b.graph ∧
      (∃ E, Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member)) ∧
      (∀ p ∈ T b, b.Contains p) ∧ Slice R b (T b)) :
    (l : ℚ) * (∑ b ∈ F, (b.weight : ℚ) * (T b).card) ≤ mixedDegree B ⊥ Finset.univ := by
  classical
  have hgraph := @Low6969GeometryCut_2_3_1.proof f Q l
  have hmember := @Low6969GeometryCut_2_3_2.proof f Q l
  let S := F.image Branch.surface
  let fibre (P : Ideal GeoJets) := F.filter fun b => b.surface = P
  let charge (b : Branch f Q l) : ℚ := (b.weight : ℚ) * (T b).card
  obtain ⟨hZ, hsumZ⟩ := initial_bound hB f Q l hf hproper hfbox hQ S (by
    intro P hP
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨b.base, b.high⟩)
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
    have hEbound := divisorBound B hB.double_zero hB.double_coordinates G {4} 3 hG.minimal.isPrime (by decide) hGdim E (fun m hm => hB.raw_mem (hboxE m hm)) (square_support hB hboxE) hproperE
      (fibre b.surface) C Branch.weight inj (fun c hc => (hC c (Finset.mem_filter.mp hc).2).1)
    have hGbound := divisorBound B hB.double_zero hB.double_coordinates (cylinder b.surface) {3, 4} 2 hZprime (by decide) hZdim
      b.graph (fun m hm => hB.raw_mem (hboxG m hm)) (square_support hB hboxG) hproperG {G} id (fun _ => 1) (fun _ _ _ _ h => h) (by
        intro P hP
        obtain rfl := Finset.mem_singleton.mp hP
        exact hG)
    have hGbound' : mixedDegree B G {3, 4} ≤ mixedDegree B (cylinder b.surface) {2, 3, 4} := by
      simpa only [Finset.sum_singleton, Nat.cast_one, one_mul, id_eq] using hGbound
    exact hmarks.trans (hEbound.trans hGbound')
  have hcharge : (∑ c ∈ F, charge c) ≤ ∑ P ∈ S, mixedDegree B (cylinder P) {2, 3, 4} := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Branch.surface)
      (fun b hb => Finset.mem_image_of_mem Branch.surface hb) charge]
    exact Finset.sum_le_sum hfibre
  exact (mul_le_mul_of_nonneg_left hcharge (Nat.cast_nonneg l)).trans hsumZ

end

end Low6969ActiveCycle
end Z6969Source2287

-- Source: ProximityPrize.SubmissionLower.Low6969ActiveCycleCaps
section Z6969Source2288
set_option autoImplicit true
set_option Elab.async false



-- merged module R6960Low6969ActiveCycleCaps
section Merged_R6960Low6969ActiveCycleCaps

set_option autoImplicit false
set_option Elab.async false

namespace Low6969ActiveCycle
noncomputable section
open K1_13 (Shape InBox Row shape)
open K1_13_6 (GeoField genericCoeffs toGeneric)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (Exponent oldEmbedding)
open Low6969Prices (primaryBox taylorLength evenClip)
open Low48BentLattice (Cap Allowed Chamber)
open Low48BentSupport (graph lifted)
open Low48BentCycle (Family rawFamily capFamily)
open Low49ActiveLattice (points Active)
open Low49ActiveSupport (Raw)
open MvPolynomial

def caps (p : Shape) : Fin 5 → Cap :=
  ![(p, 0), (primaryBox, 0), graph p, lifted p (taylorLength - 4), lifted p (taylorLength - 3)]

theorem caps_chamber {p : Shape} (hb : p.j ≤ p.b) (ht : 1 ≤ p.t) (hj : 3 * p.t + 3 ≤ p.j) :
    ∀ i, Chamber (caps p i) := by
  intro i
  fin_cases i
  · change Chamber (p, 0)
    exact ⟨hb, show 3 * p.t ≤ p.j by omega, Nat.zero_le _⟩
  · change 1679 ≤ 4024 ∧ 3 * 500 ≤ 1679 ∧ 2 * 0 ≤ (500 : ℕ)
    decide
  · exact Low48BentSupport.graph_chamber ht hj
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 4)
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 3)

private theorem last_allowed {p : Shape}
    (v : Fin 5) : Allowed (caps p 4) (Finsupp.single v 1) := by
  let k := taylorLength - 3
  have hb' : 1 ≤ 1 + k * (p.b - 1) := by omega
  have hj' : 4 ≤ 4 + k * (p.j - 2) := by omega
  have ht' : 2 ≤ 2 + k * p.t := by omega
  have hd' : 1 ≤ min (1 + k) ((2 + k * p.t) / 2) := by omega
  fin_cases v <;> simp [caps, lifted, Allowed, ← show k = taylorLength - 3 from rfl] <;> omega

theorem ordinary_doubled {p : Shape} :
    Doubled (rawFamily (caps p)) (capFamily (caps p)) where
  zero_mem i := by simp [rawFamily, Allowed]
  pair_mem _ _ ha _ hb := Low48BentSupport.raw_add ha hb
  last_coordinate := last_allowed

def baseClip (p : Shape) (K : ℕ) : ℕ := evenClip p 0 (p.b + p.j - K)

def graphClip (p : Shape) (K : ℕ) : ℕ :=
  evenClip ⟨p.b, p.j + 1, p.t + 1⟩ 1 (baseClip p K)

def liftClip (p : Shape) (K k : ℕ) : ℕ :=
  evenClip (lifted p k).1 (k + 1) (2 + k * (baseClip p K - 2))

def clips (p : Shape) (K : ℕ) : Fin 5 → ℕ :=
  ![baseClip p K, 498, graphClip p K, liftClip p K (taylorLength - 4),
    liftClip p K (taylorLength - 3)]

theorem clip_bounds (p : Shape) (h m : ℕ) :
    evenClip p h m ≤ m ∧ evenClip p h m ≤ p.b - p.j ∧
      2 * evenClip p h m ≤ p.j ∧ evenClip p h m ≤ 2 * (p.t - h) ∧
      evenClip p h m % 2 = 0 := by
  let c := min (min m (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  have hm : c ≤ m := (min_le_left _ _).trans (min_le_left _ _)
  have hb : c ≤ p.b - p.j := (min_le_left _ _).trans (min_le_right _ _)
  have hj : c ≤ p.j / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have ht : c ≤ 2 * (p.t - h) := (min_le_right _ _).trans (min_le_right _ _)
  change c - c % 2 ≤ m ∧ c - c % 2 ≤ p.b - p.j ∧
    2 * (c - c % 2) ≤ p.j ∧ c - c % 2 ≤ 2 * (p.t - h) ∧ (c - c % 2) % 2 = 0
  omega

theorem lift_height (p : Shape) (ht : 3 ≤ p.t) (k : ℕ) :
    (lifted p k).2 = k + 1 := by
  have hm := Nat.mul_le_mul_left k ht
  rw [Nat.mul_comm k 3] at hm
  change min (1 + k) ((2 + k*p.t)/2) = k + 1
  omega

private theorem fit_clip (a : Cap) (ha : Chamber a) (m : ℕ)
    (hv : 2 * a.2 ≤ evenClip a.1 a.2 m) :
    Low49ActiveLattice.Fits a (evenClip a.1 a.2 m) := by
  obtain ⟨_, hb, hj, ht, he⟩ := clip_bounds a.1 a.2 m
  exact ⟨by have := ha.1; omega, ha.2.1, hj, by have := ha.2.2; omega, hv, he⟩

private theorem fit_lift (p : Shape) (K k : ℕ) (ht : 3 ≤ p.t)
    (h : Chamber (lifted p k)) (hv : 2 * (lifted p k).2 ≤ liftClip p K k) :
    Low49ActiveLattice.Fits (lifted p k) (liftClip p K k) := by
  have hh : evenClip (lifted p k).1 (lifted p k).2 (2 + k * (baseClip p K - 2)) =
      liftClip p K k := by rw [lift_height p ht]; rfl
  rw [← hh] at hv ⊢
  exact fit_clip _ h _ hv

def slots : List (Fin 5) := [0, 1, 2, 3, 4]

theorem clip_list (p : Shape) (K : ℕ) (ht : 3 ≤ p.t) :
    slots.map (fun i => ((caps p i).2, clips p K i)) = Low6969Prices.activeClips p K := by
  change [(0, baseClip p K), (0, 498), (1, graphClip p K),
    ((lifted p (taylorLength - 4)).2, liftClip p K (taylorLength - 4)),
    ((lifted p (taylorLength - 3)).2, liftClip p K (taylorLength - 3))] = _
  rw [lift_height p ht, lift_height p ht]
  rfl

private theorem mem_slots (i : Fin 5) : i ∈ slots := by fin_cases i <;> decide

theorem caps_active {f : Row 4} {K : ℕ}
    (hg : Low6969Prices.tiltedFits (shape f))
    (ha : Low6969Prices.activeFitsPrice (shape f) K) :
    ∀ i, Low49ActiveLattice.Fits (caps (shape f).chamber i) (clips (shape f).chamber K i) := by
  let p := (shape f).chamber
  have ht : 3 ≤ p.t := ha.1
  have hgj : p.j + 1 ≤ p.b := hg.2.trans (le_max_left _ _)
  have hCh := caps_chamber (le_max_right _ _) (by omega : 1 ≤ p.t) hg.1
  have hl (i : Fin 5) : 2 * (caps p i).2 ≤ clips p K i := by
    have H := ha.2.2
    change (Low6969Prices.activeClips p K).all _ = true at H
    rw [← clip_list p K ht, List.all_eq_true] at H
    simpa using H _ (List.mem_map_of_mem (mem_slots i))
  intro i
  fin_cases i
  · exact fit_clip (p, 0) (hCh 0) _ (hl 0)
  · change Low49ActiveLattice.Fits (primaryBox, 0) 498
    show 1679 + 498 ≤ 4024 ∧ 3 * 500 ≤ 1679 ∧ 2*498 ≤ 1679 ∧
      498 + 2*0 ≤ 2*500 ∧ 2*0 ≤ 498 ∧ 498 % 2 = 0
    decide
  · have hmax : max p.b (p.j + 1) = p.b := max_eq_left hgj
    have Eqg : graph p = (⟨p.b,p.j+1,p.t+1⟩,1) := by simp [graph, hmax]
    change Low49ActiveLattice.Fits (graph p) (graphClip p K)
    rw [Eqg]
    have hCh' : Chamber (graph p) := hCh 2
    rw [Eqg] at hCh'
    exact fit_clip _ hCh' _ (hl 2)
  · exact fit_lift p K (taylorLength - 4) ht (hCh 3) (hl 3)
  · exact fit_lift p K (taylorLength - 3) ht (hCh 4) (hl 4)

def activeRaw (p : Shape) (K : ℕ) : Family := fun i => {m | Raw (caps p i) (clips p K i) m}

def activeFamily (p : Shape) (K : ℕ) : Family := fun i => points (caps p i) (clips p K i)

instance (p : Shape) (K : ℕ) (i : Fin 5) : Finite (activeFamily p K i) :=
  (Low49ActiveLattice.finite _ _).to_subtype

theorem active_doubled {p : Shape} {K : ℕ}
    (hf : ∀ i, Low49ActiveLattice.Fits (caps p i) (clips p K i)) :
    Doubled (activeRaw p K) (activeFamily p K) where
  zero_mem i := Low49ActiveSupport.raw_zero _ _ (by
    have h := (hf i).1
    omega)
  pair_mem _ _ hx _ hy := Low49ActiveSupport.raw_pair hx hy
  last_coordinate v := by
    refine ⟨last_allowed v, ?_⟩
    have hfit := (hf 4).1
    let k := taylorLength - 3
    have HJ : 4 ≤ (caps p 4).1.j := by
      change 4 ≤ 4 + k * (p.j - 2)
      omega
    fin_cases v <;> simp [Active] <;> omega

theorem old_section_active {q : Shape} {P : Row 4} {c K : ℕ}
    (h : InBox (shape P) q) (hK : Low6969Prices.ActiveFits P K) (hc : K + c ≤ q.b + q.j) :
    Low49ActiveSupport.Box (q, 0) c (oldEmbedding (toGeneric P)) := by
  intro m hm
  refine ⟨Low48BentCycle.old_section h m hm, ?_⟩
  change m ∈ (MvPolynomial.rename Fin.castSucc (toGeneric P)).support at hm
  rw [MvPolynomial.support_rename_of_injective (Fin.castSucc_injective 4)] at hm
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
  have haP := MvPolynomial.support_map_subset genericCoeffs P ha
  have hlast : Fin.last 4 ∉ Set.range (Fin.castSucc : Fin 4 → Fin 5) := by
    rintro ⟨i, hi⟩
    exact Fin.castSucc_ne_last i hi
  have h0 : Fin.castSucc (0 : Fin 4) = 0 := rfl
  have h1 : Fin.castSucc (1 : Fin 4) = 1 := rfl
  have h2 : Fin.castSucc (2 : Fin 4) = 2 := rfl
  have h3 : Fin.castSucc (3 : Fin 4) = 3 := rfl
  have h4 : Fin.last 4 = 4 := rfl
  unfold Active
  rw [← h0, ← h1, ← h2, ← h3, ← h4,
    Finsupp.mapDomain_of_notMem_range _ _ hlast]
  simp only [Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 4)]
  have H := hK a haP
  omega

end
end Low6969ActiveCycle

end Merged_R6960Low6969ActiveCycleCaps
end Z6969Source2288

-- Source: ProximityPrize.SubmissionLower.Low6969ActiveCyclePrice
section Z6969Source2289
set_option autoImplicit true
set_option Elab.async false





-- merged module R6960Low6969ActiveCyclePrice
section Merged_R6960Low6969ActiveCyclePrice

set_option autoImplicit false
set_option Elab.async false

namespace Low6969ActiveCycle
noncomputable section

open Low48BentLattice (Cap Chamber Scale latticePoints)
open Low49ActiveLattice (Fits points)
open K1_13 (Shape)
open K1_13_6 (GeoField)
open K1_13_6_2_4_1 (Grade Form unitGrade positiveDiagonal positiveDiagonal_apply
  cube_extract line_coeff squarefree squarefree_apply)
open Low48BentCycle (Family capFamily capSum ambient_cap integral mixedDegree diagonalExponents
  diagonal_nsmul diagonal_add)
open MvPolynomial
open scoped BigOperators Pointwise

open Low48BentCycle (diagonal_unit grade_sum diagonal_sum coeff_congr)
open Low48BentCycle (ambient_list)
open Low49ActiveVolume (fits_scale point_scale point_zero)

private def integr (a : Cap) : ℚ := integral a

private def signed (p : Shape) : ℤ :=
  ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
    integral (Low48BentLattice.Sum J (caps p))

private theorem base_signed (p : Shape) :
    Low6969Prices.tiltedSurface p Low6969Prices.primaryBox = (signed p).toNat := by
  change Low48Price.ambientMix (slots.map (caps p)) = _
  exact ambient_list (caps p)

private theorem base_normalize (p : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (capSum (caps p) (positiveDiagonal J))) = (signed p : ℚ) := by
  have H := Low48BentPolarization.remove_baseline (caps p)
  change _ = _ at H
  rw [show (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      integr (capSum (caps p) (positiveDiagonal J))) =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (Low48BentLattice.Sum J (caps p)) from H]
  unfold signed
  push_cast
  rfl

private theorem ordinary_coeff (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (latticePoints a)).toRingHom ⊥)).coeff 5 = integr a / 60 := by
  rw [Low48BentVolume.ambient_coeff a ha]
  unfold integr integral
  rw [Low48BentVolume.cast_price_integral a]

theorem ordinary_budget {p : Shape} (h : ∀ i, Chamber (caps p i)) :
    (60 * 32 : ℚ) * mixedDegree (capFamily (caps p)) ⊥ Finset.univ ≤
      (Low6969Prices.tiltedSurface p Low6969Prices.primaryBox : ℚ) := by
  rw [mul_assoc, ambient_cap (caps p) h (fun a => integr a / 60) ordinary_coeff]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize, base_signed]
  exact_mod_cast (show signed p ≤ ((signed p).toNat : ℤ) by omega)

private theorem fits_sum (s : Finset (Fin 5)) (a : Fin 5 → Cap) (c : Fin 5 → ℕ)
    (h : ∀ i ∈ s, Fits (a i) (c i)) :
    Fits (Low48BentLattice.Sum s a) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [Fits, Low48BentLattice.Sum]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have hs := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hm := Low49ActiveLattice.fits_add (h i (Finset.mem_insert_self _ _)) hs
    simpa only [Low48BentLattice.Sum, Finset.sum_insert hi, Low48BentLattice.Add, Shape.plus] using hm

private theorem points_sum (s : Finset (Fin 5)) (a : Fin 5 → Cap) (c : Fin 5 → ℕ)
    (h : ∀ i ∈ s, Fits (a i) (c i)) :
    (∑ i ∈ s, points (a i) (c i)) = points (Low48BentLattice.Sum s a) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Low48BentLattice.Sum] using point_zero.symm
  | insert i s hi ih =>
    have hs (j : Fin 5) (hj : j ∈ s) := h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih hs,
      Low49ActiveLattice.add (h i (Finset.mem_insert_self _ _)) (fits_sum s a c hs)]
    simp only [Low48BentLattice.Sum, Low48BentLattice.Add, Finset.sum_insert hi, Shape.plus]

private def clipSum (p : Shape) (K : ℕ) (t : Grade) : ℕ := ∑ i, t i * clips p K i

private theorem active_diagonal {p : Shape} {K : ℕ} (t : Grade)
    (h : ∀ i, Fits (caps p i) (clips p K i)) :
    diagonalExponents (activeFamily p K) t = points (capSum (caps p) t) (clipSum p K t) := by
  have h0 := (active_doubled h).double_zero
  calc
    _ = ∑ i : Fin 5, diagonalExponents (activeFamily p K) (t i • unitGrade i) := by
      conv_lhs => rw [← grade_sum t]
      exact diagonal_sum _ _ _
    _ = ∑ i : Fin 5, points (Scale (t i) (caps p i)) (t i * clips p K i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diagonal_nsmul, diagonal_unit _ h0]
      exact point_scale _ _ (h i) _
    _ = _ := points_sum _ _ _ (fun i _ => fits_scale (h i) _)

private theorem fifth_difference (v : Fin 5 → ℚ) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      (∑ i, (positiveDiagonal J i : ℚ) * v i)^5) = 120 * ∏ i, v i := by
  let f : Form := (∑ i : Fin 5, C (v i) * MvPolynomial.X i)^5
  have hlin : (∑ i : Fin 5, (C (v i) * MvPolynomial.X i : Form)).IsHomogeneous 1 := by
    change _ ∈ homogeneousSubmodule (Fin 5) ℚ 1
    apply Submodule.sum_mem
    intro i _
    exact (isHomogeneous_X ℚ i).C_mul _
  have hf : f.IsHomogeneous 5 := by
    simpa only [Nat.mul_one] using hlin.pow 5
  have hsum := cube_extract (Finset.univ : Finset (Fin 5)) f
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  simp_rw [line_coeff, homogeneousComponent_eq_self hf] at hsum
  have he (J : Finset (Fin 5)) :
      eval (fun i => (positiveDiagonal J i : ℚ)) f = (∑ i, (positiveDiagonal J i : ℚ) * v i)^5 := by
    simp [f, mul_comm]
  simp_rw [he] at hsum
  rw [hsum]
  unfold f
  simp only [← smul_eq_C_mul]
  rw [coeff_linearCombination_X_pow_of_fintype]
  have hu (i : Fin 5) : squarefree Finset.univ i = 1 := by simp [squarefree_apply]
  have hd : (squarefree (Finset.univ : Finset (Fin 5))).degree = 5 := by
    simp [K1_13_6_2_4_1.squarefree_degree]
  have hh : (squarefree (Finset.univ : Finset (Fin 5))).support = Finset.univ := by
    ext i
    simp [Finsupp.mem_support_iff, hu]
  have hsum' : (squarefree (Finset.univ : Finset (Fin 5))).sum (fun _ m => m) = 5 := hd
  simp [hsum', Finsupp.multinomial_eq, Finsupp.prod, hh, hu, Nat.multinomial,
    Finset.sum_const, Nat.factorial]

private theorem clips_prod (p : Shape) (K : ℕ) (ht : 3 ≤ p.t)
    (h : ∀ i, Fits (caps p i) (clips p K i)) :
    (Low6969Prices.activeLoss (Low6969Prices.activeClips p K) : ℚ) =
      480 * ((∏ i, (clips p K i : ℚ)) -
        (∏ i, ((clips p K i : ℚ) - 2 * ((caps p i).2 : ℚ)))) := by
  rw [← clip_list p K ht]
  unfold Low6969Prices.activeLoss
  have hi (i : Fin 5) : 2 * (caps p i).2 ≤ clips p K i := (h i).2.2.2.2.1
  have hle : (∏ i, (clips p K i - 2 * (caps p i).2)) ≤ ∏ i, clips p K i :=
    Finset.prod_le_prod fun _ _ => Nat.sub_le _ _
  have hp (a : Fin 5 → ℕ) : (slots.map a).prod = ∏ i, a i := by
    rw [← List.prod_toFinset a (show slots.Nodup by decide)]
    rw [show slots.toFinset = Finset.univ by decide]
  simp only [List.map_map, Function.comp_apply, hp]
  rw [Nat.cast_mul, Nat.cast_sub hle]
  push_cast [Nat.cast_sub, hi]
  norm_num

theorem active_budget {p : Shape} {K : ℕ} (ht : 3 ≤ p.t)
    (h : ∀ i, Fits (caps p i) (clips p K i)) :
    (60 * 32 : ℚ) * mixedDegree (activeFamily p K) ⊥ Finset.univ ≤
      (Low6969Prices.tiltedSurfaceActive p Low6969Prices.primaryBox K : ℚ) := by
  classical
  have hcoeff (J : Finset (Fin 5)) :
      (affineHilbertPolynomial (Ideal.comap
        (monomialMap GeoField (diagonalExponents (activeFamily p K) (positiveDiagonal J))) ⊥)).coeff 5 =
      (integr (capSum (caps p) (positiveDiagonal J)) -
        4 * ((clipSum p K (positiveDiagonal J) : ℚ)^5 -
          ((clipSum p K (positiveDiagonal J) : ℚ) -
            2 * ((capSum (caps p) (positiveDiagonal J)).2 : ℚ))^5)) / 60 := by
    rw [coeff_congr _ _ (active_diagonal _ h)]
    have hs := fits_sum Finset.univ (fun i => Scale (positiveDiagonal J i) (caps p i))
      (fun i => positiveDiagonal J i * clips p K i) (fun i _ => fits_scale (h i) _)
    let a := capSum (caps p) (positiveDiagonal J)
    let c := clipSum p K (positiveDiagonal J)
    change (affineHilbertPolynomial ((⊥ : Ideal K1_13_6_2.GeoJets5).comap
      (monomialMap GeoField (points a c)).toRingHom)).coeff 5 = _
    rw [Low49ActiveVolume.ambient_coeff a c hs]
    unfold integr integral
    rw [Low48BentVolume.cast_price_integral a]
  have hc (J : Finset (Fin 5)) :
      (clipSum p K (positiveDiagonal J) : ℚ) = ∑ i, (positiveDiagonal J i : ℚ) * clips p K i := by
    unfold clipSum
    push_cast
    rfl
  have hcd (J : Finset (Fin 5)) :
      (clipSum p K (positiveDiagonal J) : ℚ) -
          2 * ((capSum (caps p) (positiveDiagonal J)).2 : ℚ) =
        ∑ i, (positiveDiagonal J i : ℚ) * ((clips p K i : ℚ) - 2 * ((caps p i).2 : ℚ)) := by
    rw [hc]
    simp only [capSum, Low48BentLattice.Sum, Scale, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum,
      Finset.sum_sub_distrib, mul_sub]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold mixedDegree
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show (2 : ℚ)^5 = 32 by norm_num, mul_assoc, ← mul_div_assoc (32 : ℚ),
    mul_div_cancel_left₀ _ (by norm_num : (32 : ℚ) ≠ 0)]
  simp_rw [hcoeff, ← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0)]
  have hsum_rearr (A C D : Finset (Fin 5) → ℚ) :
      (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        (A J - 4 * (C J - D J))) =
      (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * A J) -
        4 * ((∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * C J) -
          (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * D J)) := by
    simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro J _
    ring
  rw [hsum_rearr, base_normalize]
  simp_rw [hcd, hc]
  simp_rw [fifth_difference]
  rw [show 4 * (120 * (∏ i, (clips p K i : ℚ)) -
      120 * ∏ i, ((clips p K i : ℚ) - 2 * ((caps p i).2 : ℚ))) =
      (Low6969Prices.activeLoss (Low6969Prices.activeClips p K) : ℚ) by rw [clips_prod p K ht h]; ring]
  unfold Low6969Prices.tiltedSurfaceActive
  rw [base_signed]
  exact_mod_cast (show signed p - (Low6969Prices.activeLoss (Low6969Prices.activeClips p K) : ℤ) ≤
    (((signed p).toNat - Low6969Prices.activeLoss (Low6969Prices.activeClips p K) : ℕ) : ℤ) by omega)

end
end Low6969ActiveCycle

end Merged_R6960Low6969ActiveCyclePrice
end Z6969Source2289

-- Source: ProximityPrize.SubmissionLower.Low6969ActiveCycleMixed
section Z6969Source2290
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969SharedBentCaps
section Merged_Low6969SharedBentCaps

-- merged module R6960Low6969ActiveCycleChart
section Merged_R6960Low6969ActiveCycleChart

set_option autoImplicit false
set_option Elab.async false

namespace Low6969ActiveCycle

noncomputable section

open Polynomial
open P3 (K)
open Low6969Prices (physicalDegree taylorLength)
open K1_13 (Row shape extend InBox Shape)
open Low48BentCycle (Family rawFamily)
open K1_13_6 (GeoField toGeneric)
open K1_13_6_2 (GeoJets5 actualPoint)
open K1_13_6_2_2 (generic5 rawGraph numerator denominator padded padded_last)
open Low6969GeometryCut_2 (Branch branch_box)
open MvPolynomial
open Low6969GeometryCut_2_1 (valuePolynomial value_section numerator_associated)

private theorem scalar_section {R : Family} {i : Fin 5} {D : GeoJets5}
    (h : Section R i D) (c : GeoField) : Section R i (MvPolynomial.C c * D) := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
  exact h m (MvPolynomial.mem_support_iff.mpr fun hz => hm (mul_eq_zero_of_right _ hz))

private theorem sum_section {R : Family} {i : Fin 5} {ι : Type*} (S : Finset ι)
    (D : ι → GeoJets5) (h : ∀ j ∈ S, Section R i (D j)) :
    Section R i (∑ j ∈ S, D j) := by
  classical
  intro m hm
  obtain ⟨j, hj, hjm⟩ := Finset.mem_biUnion.mp (support_sum hm)
  exact h j hj m hjm

private theorem sub_section {R : Family} {i : Fin 5} {D E : GeoJets5}
    (hD : Section R i D) (hE : Section R i E) : Section R i (D - E) := by
  intro m hm
  exact (Finset.mem_union.mp (MvPolynomial.support_sub (Fin 5) D E hm)).elim (hD m) (hE m)

def Chart {f Q : Row 4} {l : ℕ} (R : Family) (b : Branch f Q l) : Prop :=
    Section R 2 b.graph ∧ ∃ E H : GeoJets5,
      Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member) ∧
      Section R 4 H ∧ Associated (b.onGraph H) (b.localMap b.next) ∧
      ∀ x a : K, ∃ D, Section R 4 D ∧
        ∀ S : (Polynomial K), S.natDegree ≤ physicalDegree → ∀ h : b.Contains (actualPoint (extend S)),
          (b.liftedEval (actualPoint (extend S)) h D = 0 ↔ S.eval x = a)

private theorem recover {f Q : Row 4} {l : ℕ} {R : Family} (b : Branch f Q l)
    (hG : Section R 2 (generic5 (rawGraph b.g)))
    (hmem : Section R 3 (generic5 (padded b.g (taylorLength - 4) taylorLength)))
    (hden : Section R 4 (generic5 (denominator b.g (taylorLength - 3))))
    (hpad : ∀ i ≤ taylorLength + 1,
      Section R 4 (generic5 (padded b.g (taylorLength - 3) i))) : Chart R b := by
  have hGraph : generic5 (rawGraph b.g) = b.graph := by
    simp [rawGraph, Branch.graph, Branch.sigma, toGeneric, MvPolynomial.map_rename, map_ofNat]
  let k := taylorLength - 4
  have hk : k + 4 = taylorLength := by decide
  have hk' : (k + 1) + 4 = taylorLength + 1 := by decide
  have hE : Section R 3 (generic5 (padded b.g k (k + 4))) := by
    rw [hk]
    exact hmem
  have hH : Section R 4 (generic5 (padded b.g (k + 1) ((k + 1) + 4))) :=
    hpad _ (by omega)
  rw [padded_last] at hE hH
  have hm := numerator_associated b k
  have hn := numerator_associated b (k + 1)
  rw [hk] at hm
  rw [hk'] at hn
  refine ⟨hGraph ▸ hG, generic5 (numerator b.g k), generic5 (numerator b.g (k + 1)),
    hE, hm, hH, hn, ?_⟩
  intro x a
  have hM : taylorLength ≤ K1.p := by decide
  have hlen : taylorLength ≤ (k + 1) + 5 := by decide
  refine ⟨valuePolynomial taylorLength b.g (k + 1) x a, ?_, ?_⟩
  · unfold valuePolynomial
    apply sub_section
    · apply sum_section
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact scalar_section (R := R) (i := 4) (hpad i (by omega)) _
    · exact scalar_section (R := R) (i := 4) hden _
  · intro T hT h
    exact value_section hM b (k + 1) hlen x a T (Nat.lt_succ_of_le hT) h

theorem ordinary_chart {f Q : Row 4} {l : ℕ} (ht : 1 ≤ (shape f).t) (b : Branch f Q l) :
    Chart (rawFamily (caps (shape f).chamber)) b := by
  obtain ⟨hg, hbox⟩ := Low48BentSupport.chart_support (K1_13_7_1.shape_chamber f) ht (branch_box b)
  exact recover b hg ((hbox _).2 _ (by decide)) (hbox _).1
    (fun i hi => (hbox _).2 i hi)

theorem active_chart {f Q : Row 4} {l K : ℕ}
    (hK : Low6969Prices.ActiveFits f K) (ha : Low6969Prices.activeFitsPrice (shape f) K)
    (b : Branch f Q l) : Chart (activeRaw (shape f).chamber K) b := by
  let p := (shape f).chamber
  have ht : 1 ≤ p.t := by have H : 3 ≤ p.t := ha.1; omega
  have hc : 4 ≤ baseClip p K := ha.2.1
  obtain ⟨hK', hb, _, _, _⟩ := clip_bounds p 0 (p.b + p.j - K)
  have hKb : K ≤ p.b + p.j - baseClip p K := by
    change baseClip p K ≤ p.b + p.j - K at hK'
    omega
  have hFits : Low49ActiveSupport.Fits b.g (p.b + p.j - baseClip p K) := by
    have hsep := Low49ActiveSupport.separant_fits hK b.r
    exact fun m hm => (hsep m hm).trans hKb
  have hg : graphClip p K ≤ baseClip p K := (clip_bounds _ _ _).1
  obtain ⟨hG, hbox⟩ := Low49ActiveSupport.chart_support (K1_13_7_1.shape_chamber f) ht
    (branch_box b) (show 2 ≤ baseClip p K by omega) hFits hb hg
  have hchart (k : ℕ) := hbox k (liftClip p K k) (clip_bounds _ _ _).1
  exact recover b hG ((hchart (taylorLength - 4)).2 taylorLength (by decide))
    (hchart (taylorLength - 3)).1
    (fun i hi => (hchart (taylorLength - 3)).2 i hi)

end

end Low6969ActiveCycle

end Merged_R6960Low6969ActiveCycleChart

-- merged module R6960Low6969SharedBentCaps
section Merged_R6960Low6969SharedBentCaps
set_option Elab.async false
namespace Low6969SharedBentCaps
noncomputable section

open K1_13 (Shape Row shape)
open K1_13_6 (GeoField)
open Low6969Prices (taylorLength)
open Low6969ActiveCycle (Doubled Chart)
open Low48BentLattice (Cap Allowed Chamber latticePoints)
open Low48BentSupport (graph lifted)
open Low48BentCycle (Family rawFamily capFamily capSum ambient_cap integral mixedDegree)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators
open Low48BentCycle (slots ambient_list)

def caps (p q : Shape) : Fin 5 → Cap :=
  ![(p, 0), (q, 0), graph p, lifted p (taylorLength - 4), lifted p (taylorLength - 3)]

theorem caps_chamber {p q : Shape} (hb : p.j ≤ p.b) (ht : 1 ≤ p.t) (hj : 3 * p.t + 3 ≤ p.j) (hq : Chamber (q,0)) :
    ∀ i, Chamber (caps p q i) := by
  intro i
  fin_cases i
  · change Chamber (p, 0)
    exact ⟨hb, show 3 * p.t ≤ p.j by omega, Nat.zero_le _⟩
  · exact hq
  · exact Low48BentSupport.graph_chamber ht hj
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 4)
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 3)

private theorem last_allowed {p q : Shape}
    (v : Fin 5) : Allowed (caps p q 4) (Finsupp.single v 1) := by
  let k := taylorLength - 3
  have hb' : 1 ≤ 1 + k * (p.b - 1) := by omega
  have hj' : 4 ≤ 4 + k * (p.j - 2) := by omega
  have ht' : 2 ≤ 2 + k * p.t := by omega
  have hd' : 1 ≤ min (1 + k) ((2 + k * p.t) / 2) := by omega
  fin_cases v <;> simp [caps, lifted, Allowed, ← show k = taylorLength - 3 from rfl] <;> omega

theorem ordinary_doubled {p q : Shape} :
    Doubled (rawFamily (caps p q)) (capFamily (caps p q)) where
  zero_mem i := by simp [rawFamily, Allowed]
  pair_mem _ _ ha _ hb := Low48BentSupport.raw_add ha hb
  last_coordinate := last_allowed

private def integr (a : Cap) : ℚ := integral a

private def signed (p q : Shape) : ℤ :=
  ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
    integral (Low48BentLattice.Sum J (caps p q))

private theorem base_signed (p q : Shape) :
    Low6969Prices.tiltedSurface p q = (signed p q).toNat := by
  change Low48Price.ambientMix (slots.map (caps p q)) = _
  exact ambient_list (caps p q)

private theorem base_normalize (p q : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (capSum (caps p q) (positiveDiagonal J))) = (signed p q : ℚ) := by
  have H := Low48BentPolarization.remove_baseline (caps p q)
  change _ = _ at H
  rw [show (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      integr (capSum (caps p q) (positiveDiagonal J))) =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (Low48BentLattice.Sum J (caps p q)) from H]
  unfold signed
  push_cast
  rfl

private theorem ordinary_coeff (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (latticePoints a)).toRingHom ⊥)).coeff 5 = integr a / 60 := by
  rw [Low48BentVolume.ambient_coeff a ha]
  unfold integr integral
  rw [Low48BentVolume.cast_price_integral a]

theorem ordinary_budget {p q : Shape} (h : ∀ i, Chamber (caps p q i)) :
    (60 * 32 : ℚ) * mixedDegree (capFamily (caps p q)) ⊥ Finset.univ ≤
      (Low6969Prices.tiltedSurface p q : ℚ) := by
  rw [mul_assoc, ambient_cap (caps p q) h (fun a => integr a / 60) ordinary_coeff]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize, base_signed]
  exact_mod_cast (show signed p q ≤ ((signed p q).toNat : ℤ) by omega)


theorem chart {f Q : Row 4} {l : ℕ} (q : Shape) (ht : 1 ≤ (shape f).t)
    (b : Low6969GeometryCut_2.Branch f Q l) :
    Chart (rawFamily (caps (shape f).chamber q)) b := by
  have h := Low6969ActiveCycle.ordinary_chart ht b
  exact h


end
end Low6969SharedBentCaps

end Merged_R6960Low6969SharedBentCaps

end Merged_Low6969SharedBentCaps

-- merged module Low6969ActiveCycleMixed
section Merged_Low6969ActiveCycleMixed

set_option autoImplicit false
set_option Elab.async false

namespace Low6969ActiveCycle

noncomputable section

open Polynomial MvPolynomial
open P3 (K)
open Low6969GeometryCut (MixedMark CutInput MixedBound)
open Low6969GeometryCut_2 (Branch branch_of_mixed)
open Low6969Prices (primaryBox tiltedSurface)
open K1_13 (Row extend embed shape)
open Low48BentCycle (Family mixedDegree rawFamily capFamily)
open K1_13_6 (Pieces CurveSections toGeneric)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand)
open K1_13_6_2_4 (oldEmbedding)
open scoped BigOperators

theorem mixed {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l budget : ℕ}
    {R B : Family} [∀ i, Finite (B i)]
    (input : CutInput Γ s f Q l) (hDB : Doubled R B)
    (hfbox : Section R 0 (oldEmbedding (toGeneric f)))
    (hQbox : Section R 1 (oldEmbedding (toGeneric Q)))
    (hchart : ∀ b : Branch f Q l, Chart R b)
    (hbudget : (60 * 32 : ℚ) * mixedDegree B ⊥ Finset.univ ≤ (budget : ℚ)) :
    MixedBound Γ s f Q l (60 * 32) budget := by
  classical
  let point (γ : K) := actualPoint (extend (s γ))
  let marked := Γ.filter (fun γ => MixedMark f Q l (extend (s γ)))
  let assign (γ : marked) : Branch f Q l :=
    Classical.choose (branch_of_mixed (Finset.mem_filter.mp γ.property).2)
  let branches := marked.attach.image assign
  let labels (b : Branch f Q l) :=
    marked.filter (fun γ => ∃ h : γ ∈ marked, assign ⟨γ, h⟩ = b)
  have label_sub (b : Branch f Q l) : labels b ⊆ Γ :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have contains_label (b : Branch f Q l) (γ : K) (hγ : γ ∈ labels b) :
      b.Contains (point γ) := by
    obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hγ).2
    exact Classical.choose_spec (branch_of_mixed (Finset.mem_filter.mp h).2)
  have labels_nonempty (b : Branch f Q l) (hb : b ∈ branches) : (labels b).Nonempty := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨γ.val, Finset.mem_filter.mpr ⟨γ.property, γ.property, rfl⟩⟩
  have available (b : Branch f Q l) : ∃ T ⊆ labels b,
      (b.Simple → T = labels b) ∧
      (b ∈ branches → ¬ b.Simple → 0 < T.card ∧ CurveSections (labels b) s T.card ∧
        Demand (labels b) s T) := by
    by_cases hs : b.Simple
    · exact ⟨labels b, Finset.Subset.rfl, fun _ => rfl, fun _ hn => (hn hs).elim⟩
    by_cases hb : b ∈ branches
    · obtain ⟨T, hsub, hd⟩ := maximal_demand (labels b) s (labels_nonempty b hb)
      exact ⟨T, hsub, fun h => (hs h).elim, fun _ _ => hd⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => (hs h).elim, fun h _ => (hb h).elim⟩
  choose demanded demand_sub demand_simple demand_multiple using available
  let points (b : Branch f Q l) := (demanded b).image point
  have points_card (b : Branch f Q l) : (points b).card = (demanded b).card := by
    apply Finset.card_image_of_injOn
    intro γ hγ δ hδ heq
    exact input.distinct (label_sub b (demand_sub b hγ)) (label_sub b (demand_sub b hδ))
      (Polynomial.map_injective embed embed.injective (actualPoint_injective heq))
  have points_on (b : Branch f Q l) (p : JetPoint) (hp : p ∈ points b) : b.Contains p := by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    exact contains_label b γ (demand_sub b hγ)
  have points_next (b : Branch f Q l) (p : JetPoint) (hp : p ∈ points b) :
      MvPolynomial.eval p b.next = 0 := by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    apply b.next_actual (contains_label b γ (demand_sub b hγ))
    simpa only [Polynomial.natDegree_map] using input.degree γ (label_sub b (demand_sub b hγ))
  have bound5 := bound hDB f Q l input.small input.proper hfbox hQbox branches points
    (by
      intro b hb
      obtain ⟨hgraph, E, H, hE, hEeq, hH, hHeq, hvalue⟩ := hchart b
      refine ⟨hgraph, ⟨E, hE, hEeq⟩, points_on b, ?_⟩
      by_cases hs : b.Simple
      · exact Or.inr ⟨H, hH, b.lifted_proper_of_associated hHeq (b.next_proper hs),
          fun p hp hon => b.lifted_zero_of_associated hHeq hon (points_next b p hp)⟩
      rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
      · exact Or.inl (by rw [points_card, hone])
      obtain ⟨D, hD, hEval⟩ := hvalue x a
      obtain ⟨δ, hδ, hδvalue⟩ := hwit
      have hδon := contains_label b δ hδ
      refine Or.inr ⟨D, hD, b.lifted_proper_of_nonzero (point δ) hδon ?_, ?_⟩
      · exact fun hzero => hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp hzero)
      · intro p hp hon
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
        have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
        exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ))) hon).mpr hvalueγ)
  let simple := branches.filter Branch.Simple
  let multiple := branches.filter (fun b => ¬ b.Simple)
  let e := multiple.equivFin
  let C : Pieces Γ :=
    { n := multiple.card
      piece := fun i => labels (e.symm i).val
      subset := fun i => label_sub (e.symm i).val
      degree := fun i => (demanded (e.symm i).val).card }
  let B := simple.biUnion labels
  have hmultiple (i : Fin C.n) := Finset.mem_filter.mp (e.symm i).property
  refine ⟨C, B,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).2.1,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).1, ?_, ?_⟩
  · intro γ hγ hm
    have hmark : γ ∈ marked := Finset.mem_filter.mpr ⟨hγ, hm⟩
    let b := assign ⟨γ, hmark⟩
    have hb : b ∈ branches := Finset.mem_image.mpr ⟨_, Finset.mem_attach _ _, rfl⟩
    have hlabel : γ ∈ labels b := Finset.mem_filter.mpr ⟨hmark, hmark, rfl⟩
    by_cases hs : b.Simple
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hs⟩, hlabel⟩)
    have hbm : b ∈ multiple := Finset.mem_filter.mpr ⟨hb, hs⟩
    apply Finset.mem_union_left _
    refine Finset.mem_biUnion.mpr ⟨e ⟨b, hbm⟩, Finset.mem_univ _, ?_⟩
    change γ ∈ labels (e.symm (e ⟨b, hbm⟩)).val
    simpa only [Equiv.symm_apply_apply] using hlabel
  · have htotal : C.total = ∑ b ∈ multiple, (demanded b).card := by
      calc
        C.total = ∑ b : multiple, (demanded b.val).card :=
          Equiv.sum_comp e.symm (fun b : multiple => (demanded b.val).card)
        _ = _ := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_attach multiple (fun b => (demanded b).card)
    have hsimple : (∑ b ∈ simple, b.weight * (points b).card) =
        ∑ b ∈ simple, (labels b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, demand_simple b hs, Branch.weight, ite_eq_left hs, one_mul]
    have hmult : (∑ b ∈ multiple, b.weight * (points b).card) = 2 * C.total := by
      rw [htotal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, Branch.weight, ite_eq_right hs]
    have hpart : (∑ b ∈ simple, b.weight * (points b).card) +
        (∑ b ∈ multiple, b.weight * (points b).card) =
        ∑ b ∈ branches, b.weight * (points b).card :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hB : B.card ≤ ∑ b ∈ simple, (labels b).card := Finset.card_biUnion_le
    have hpay : 2 * C.total + B.card ≤ ∑ b ∈ branches, b.weight * (points b).card := by
      rw [← hpart, hsimple, hmult, Nat.add_comm (∑ b ∈ simple, (labels b).card)]
      exact Nat.add_le_add_left hB _
    have hcount := (mul_le_mul_of_nonneg_left bound5 (by norm_num : (0 : ℚ) ≤ 60 * 32)).trans
      hbudget
    have hcount' : (60 * 32) * l * (∑ b ∈ branches, b.weight * (points b).card) ≤
        budget := by
      apply (Nat.cast_le (α := ℚ)).mp
      push_cast
      simpa only [← mul_assoc, show (60 : ℚ) * 32 = 1920 by norm_num] using hcount
    exact (Nat.mul_le_mul_left ((60 * 32) * l) hpay).trans hcount'

theorem mixed_tilted : Low6969GeometryCut.c2Tilted := by
  intro Γ s f Q l input hguard
  let p := (shape f).chamber
  have hp := K1_13_7_1.shape_chamber f
  have ht : 1 ≤ p.t := input.small.2.1
  have hj : 3 * p.t + 3 ≤ p.j := hguard.1
  have hCh : ∀ i, Low48BentLattice.Chamber (caps p i) := caps_chamber hp.1 ht hj
  refine mixed (R := rawFamily (caps p)) (B := capFamily (caps p)) input
    ordinary_doubled ?_ ?_ ?_ ?_
  · exact Low48BentCycle.old_section ⟨le_max_left _ _, le_rfl, le_rfl⟩
  · exact Low48BentCycle.old_section input.box
  · exact ordinary_chart ht
  · exact ordinary_budget hCh

theorem mixed_active : Low6969GeometryCut.c2Active := by
  intro Γ s f Q l input K hK hQ hguard hactive
  let p := (shape f).chamber
  have ht3 : 3 ≤ p.t := hactive.1
  have hfits := caps_active hguard hactive
  have hc : 4 ≤ baseClip p K := hactive.2.1
  have hK' : baseClip p K ≤ p.b + p.j - K := (clip_bounds _ _ _).1
  have hsum : K + baseClip p K ≤ p.b + p.j := by omega
  refine mixed (R := activeRaw p K) (B := activeFamily p K) input
    (active_doubled hfits) ?_ ?_ ?_ ?_
  · exact old_section_active ⟨le_max_left _ _, le_rfl, le_rfl⟩ hK hsum
  · exact old_section_active input.box hQ (by decide : 5192 + 498 ≤ 4024 + 1679)
  · exact active_chart hK hactive
  · exact active_budget ht3 hfits

theorem proof : Low6969Prices.c6 := Low6969GeometryCut.proof mixed_tilted mixed_active

end

end Low6969ActiveCycle


end Merged_Low6969ActiveCycleMixed
end Z6969Source2290

-- Source: ProximityPrize.SubmissionLower.Low6969SharedCycleBound
section Z6969Source2291
set_option autoImplicit true
set_option Elab.async false

set_option autoImplicit false
set_option Elab.async false

namespace Low6969SharedCycleBound

noncomputable section

open Low48BentCycle (Family mixedDegree properCut cycleComparison divisorBound diagonalExponents)

open Low6969Prices (SmallFactor)
open Low6969GeometryCut_2 (Branch)
open Low6969GeometryCut_2_3 (graphLift chart_index_eq graphLift_same_chart
  membership_same_chart graphLift_comap member_proper_on_graph)
open P0_9_6_2_3 (cylinder_comparison)
open K1_13 (Row)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5)
open K1_13_6_2_4 (Exponent Component DimLE OfDim LengthAt ambient_dim cylinder cylinder_injective
  dim_le_after_section oldEmbedding pointIdeal sectionIdeal)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators Pointwise

open Low6969ActiveCycle (Section Doubled Slice)
open Low6969ActiveCycle (square_support bound_marks)

private theorem initial_bound {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (f Q : Row 4) (weight : Ideal GeoJets → ℕ) (hf : SmallFactor f) (hQ : ¬ f ∣ Q)
    (hfbox : Section R 0 (oldEmbedding (toGeneric f)))
    (hQbox : Section R 1 (oldEmbedding (toGeneric Q))) (S : Finset (Ideal GeoJets))
    (hS : ∀ P ∈ S, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (weight P : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime) :
    (∀ P ∈ S, (cylinder P).IsPrime ∧ OfDim (cylinder P) 3) ∧
      (∑ P ∈ S, (weight P : ℚ) * mixedDegree B (cylinder P) {2, 3, 4}) ≤
        mixedDegree B ⊥ Finset.univ := by
  classical
  let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
  let J := sectionIdeal A (oldEmbedding (toGeneric Q))
  obtain ⟨hregQ, hAlgebra⟩ := cylinder_comparison f Q hf.1 hQ
  have hregf : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets5)
      (oldEmbedding (toGeneric f))) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne
      (K1_13_6_3_6.toGeneric_ne_zero hf.1.ne_zero)
  have hAdim : DimLE A 4 := dim_le_after_section hregf ambient_dim
  have hJdim : DimLE J 3 := dim_le_after_section hregQ hAdim
  have hgeom (P : Ideal GeoJets) (hP : P ∈ S) :
      (cylinder P).IsPrime ∧ OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P), (weight P : ℕ∞) ≤ LengthAt J (cylinder P) hc.isPrime := by
    obtain ⟨h, hw⟩ := hS P hP
    obtain ⟨hd, hc, hl⟩ := hAlgebra P h
    exact ⟨hc.isPrime, hd, hc, hw.trans hl⟩
  refine ⟨fun P hP => ⟨(hgeom P hP).1, (hgeom P hP).2.1⟩, ?_⟩
  have hs := cycleComparison B hB.double_zero hB.double_coordinates J {2, 3, 4} hJdim S cylinder weight cylinder_injective.injOn
    (fun P hP => (hgeom P hP).2.2)
  have hcutQ := properCut B hB.double_zero A {2, 3, 4} 1 (by decide) hAdim
    (oldEmbedding (toGeneric Q)) (fun m hm => hB.raw_mem (hQbox m hm)) (square_support hB hQbox) hregQ
  have hcutf := properCut B hB.double_zero ⊥ {1, 2, 3, 4} 0 (by decide) ambient_dim
    (oldEmbedding (toGeneric f)) (fun m hm => hB.raw_mem (hfbox m hm)) (square_support hB hfbox) hregf
  have hall : (insert (0 : Fin 5) {1, 2, 3, 4} : Finset (Fin 5)) = Finset.univ := by decide
  rw [hall] at hcutf
  exact hs.trans (hcutQ.trans hcutf)
/-- Bound fixed chart incidences with a separate cut and surface-dependent orders. -/
theorem bound_with_cut {R B : Family} [∀ i, Finite (B i)] (hB : Doubled R B)
    (f Q cut : Row 4) (l : ℕ) (hf : SmallFactor f) (hproper : ¬ f ∣ cut)
    (weight : Ideal GeoJets → ℕ)
    (hfbox : Section R 0 (oldEmbedding (toGeneric f)))
    (hQ : Section R 1 (oldEmbedding (toGeneric cut)))
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hF : ∀ b ∈ F, Section R 2 b.graph ∧
      (∃ E, Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member)) ∧
      (∀ p ∈ T b, b.Contains p) ∧ Slice R b (T b))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal f cut).IsMinimalPrime b.surface,
      (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal f cut) b.surface h.isPrime) :
    (∑ b ∈ F, (weight b.surface : ℚ) * ((b.weight : ℚ) * (T b).card)) ≤
      mixedDegree B ⊥ Finset.univ := by
  classical
  have hgraph := @Low6969GeometryCut_2_3_1.proof f Q l
  have hmember := @Low6969GeometryCut_2_3_2.proof f Q l
  let S := F.image Branch.surface
  let fibre (P : Ideal GeoJets) := F.filter fun b => b.surface = P
  let charge (b : Branch f Q l) : ℚ := (b.weight : ℚ) * (T b).card
  obtain ⟨hZ, hsumZ⟩ := initial_bound hB f cut weight hf hproper hfbox hQ S (by
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
    have hEbound := divisorBound B hB.double_zero hB.double_coordinates G {4} 3 hG.minimal.isPrime (by decide) hGdim E (fun m hm => hB.raw_mem (hboxE m hm)) (square_support hB hboxE) hproperE
      (fibre b.surface) C Branch.weight inj (fun c hc => (hC c (Finset.mem_filter.mp hc).2).1)
    have hGbound := divisorBound B hB.double_zero hB.double_coordinates (cylinder b.surface) {3, 4} 2 hZprime (by decide) hZdim
      b.graph (fun m hm => hB.raw_mem (hboxG m hm)) (square_support hB hboxG) hproperG {G} id (fun _ => 1) (fun _ _ _ _ h => h) (by
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

end Low6969SharedCycleBound
end Z6969Source2291
