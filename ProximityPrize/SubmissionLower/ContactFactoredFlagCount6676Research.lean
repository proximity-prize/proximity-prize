import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedUnitFamily6600Research
import ProximityPrize.SubmissionLower.ContactCumulativeWeightedDegreeResearch
import ProximityPrize.SubmissionLower.ContactGCDCumulativeLedgerResearch
import ProximityPrize.SubmissionLower.ContactGeometricFactorCover

/-! .
 -/
namespace ProximityPrize.SubmissionLower.ContactFactoredFlagCount6676Research

open scoped Classical BigOperators
open ContactFlagBezout6543Research ContactFlagSymbolicTrapezoidResearch
open ContactCumulativeWeightedDegreeResearch ContactGeometricFactorCover
open ContactRegularComponentCover ContactWeakSeparableSeparatorResearch
open ContactAdaptiveNestedProjection6600Research ContactAdaptiveNestedUnitFamily6600Research
open ContactAdaptiveUnitPoleFamilyResearch ContactPrimeFlagBudgetFamilyResearch
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveJointProjectionBounds
open ActualCoordinateDegreeSum

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 300000

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K

def exactFlag (A : Poly) : FlagDegree :=
  let s := MvPolynomial.weightedTotalDegree flagSWeights A
  let m := MvPolynomial.weightedTotalDegree flagYSWeights A
  let t := MvPolynomial.weightedTotalDegree flagTotalWeights A
  ⟨t-m,m-s,s⟩

theorem flag_weights_nested (A : Poly) :
    MvPolynomial.weightedTotalDegree flagSWeights A ≤
      MvPolynomial.weightedTotalDegree flagYSWeights A ∧
    MvPolynomial.weightedTotalDegree flagYSWeights A ≤
      MvPolynomial.weightedTotalDegree flagTotalWeights A := by
  constructor
  all_goals
    apply Finset.sup_le
    intro d hd
  · have h := MvPolynomial.le_weightedTotalDegree flagYSWeights hd
    rw [flag_weight_fin3] at h ⊢
    change d 0*0+d 1*1+d 2*0 ≤ _
    change d 0*1+d 1*1+d 2*0 ≤ _ at h
    simpa using (show d 1 ≤ MvPolynomial.weightedTotalDegree flagYSWeights A by omega)
  · have h := MvPolynomial.le_weightedTotalDegree flagTotalWeights hd
    rw [flag_weight_fin3] at h ⊢
    change d 0*1+d 1*1+d 2*0 ≤ _
    change d 0*1+d 1*1+d 2*1 ≤ _ at h
    omega

theorem exactFlag_cumulative (A : Poly) :
    (exactFlag A).all = MvPolynomial.weightedTotalDegree flagSWeights A ∧
    (exactFlag A).yz+(exactFlag A).all = MvPolynomial.weightedTotalDegree flagYSWeights A ∧
    (exactFlag A).zOnly+(exactFlag A).yz+(exactFlag A).all =
      MvPolynomial.weightedTotalDegree flagTotalWeights A := by
  have h := flag_weights_nested A
  dsimp [exactFlag]
  omega

theorem polynomialIn_exactFlag (A : Poly) : PolynomialInFlag (exactFlag A) A := by
  intro d hd
  have hs := MvPolynomial.le_weightedTotalDegree flagSWeights hd
  have hm := MvPolynomial.le_weightedTotalDegree flagYSWeights hd
  have ht := MvPolynomial.le_weightedTotalDegree flagTotalWeights hd
  rw [flag_weight_fin3] at hs hm ht
  have hc := exactFlag_cumulative A
  change d 0*0+d 1*1+d 2*0 ≤ _ at hs
  change d 0*1+d 1*1+d 2*0 ≤ _ at hm
  change d 0*1+d 1*1+d 2*1 ≤ _ at ht
  unfold InFlag
  omega

theorem inFlag_weight_caps (A : Poly) (p : FlagDegree) (hA : PolynomialInFlag p A) :
    MvPolynomial.weightedTotalDegree flagSWeights A ≤ p.all ∧
    MvPolynomial.weightedTotalDegree flagYSWeights A ≤ p.yz+p.all ∧
    MvPolynomial.weightedTotalDegree flagTotalWeights A ≤ p.zOnly+p.yz+p.all := by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply Finset.sup_le
    intro d hd
    have h := hA d hd
    rw [flag_weight_fin3]
  · change d 0*0+d 1*1+d 2*0 ≤ _; exact by simpa using h.1
  · change d 0*1+d 1*1+d 2*0 ≤ _; exact by simpa using h.2.1
  · change d 0*1+d 1*1+d 2*1 ≤ _; exact by simpa using h.2.2

theorem sum_flagMixed_le_of_cumulative {I : Type*} [Fintype I]
    (f : I → FlagDegree) (p q r : FlagDegree)
    (hs : (∑ i, (f i).all) ≤ p.all)
    (hm : (∑ i, ((f i).yz+(f i).all)) ≤ p.yz+p.all)
    (ht : (∑ i, ((f i).zOnly+(f i).yz+(f i).all)) ≤ p.zOnly+p.yz+p.all) :
    (∑ i, flagMixed (f i) q r) ≤ flagMixed p q r := by
  let z := flagMixed unitZFlag q r
  let y := flagMixed unitYZFlag q r
  let a := flagMixed unitAllFlag q r
  have hzy : z ≤ y := by simp [z,y,flagMixed,unitZFlag,unitYZFlag]; nlinarith
  have hya : y ≤ a := by simp [y,a,flagMixed,unitYZFlag,unitAllFlag]; nlinarith
  have heq (v : FlagDegree) : flagMixed v q r =
      z * (v.zOnly+v.yz+v.all) + (y-z) * (v.yz+v.all) + (a-y) * v.all := by
    calc
      flagMixed v q r = v.zOnly*z + v.yz*y + v.all*a := by
        simp only [z,y,a,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
        ring
      _ = _ := ContactGCDCumulativeLedgerResearch.linear_cost_cumulative z y a v hzy hya
  rw [Finset.sum_congr rfl (fun i _ ↦ heq (f i)), heq p]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  simpa only [Finset.sum_add_distrib] using Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left z ht) (Nat.mul_le_mul_left (y-z) hm))
    (Nat.mul_le_mul_left (a-y) hs)

def activeFactors (F N : Poly) : Finset Poly :=
  (normalizedFactorSet F).filter fun g ↦ ¬ g ∣ N ∧ MvPolynomial.pderiv (1 : Fin 3) g ≠ 0

theorem activeFactors_spec (F N : Poly) (g : ↥(activeFactors F N)) :
    Irreducible g.1 ∧ g.1 ∣ F ∧ ¬ g.1 ∣ N ∧ MvPolynomial.pderiv (1 : Fin 3) g.1 ≠ 0 := by
  have h := Finset.mem_filter.mp g.2
  exact ⟨(normalizedFactorSet_spec F g.1 h.1).1,
    (normalizedFactorSet_spec F g.1 h.1).2,h.2⟩

theorem activeFactors_mixed_sum_le (F N : Poly) (hF : F ≠ 0)
    (p q r : FlagDegree) (hsupport : PolynomialInFlag p F) :
    (∑ g : ↥(activeFactors F N), flagMixed (exactFlag g.1) q r) ≤ flagMixed p q r := by
  have hc := inFlag_weight_caps F p hsupport
  have hw (w : Fin 3 → ℕ) :
      (∑ g : ↥(activeFactors F N), MvPolynomial.weightedTotalDegree w g.1) ≤
        MvPolynomial.weightedTotalDegree w F := by
    rw [Finset.sum_coe_sort]
    exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
      (sum_weightedTotalDegree_le_of_prod_dvd_fin3 w (normalizedFactorSet F) id F hF
        (normalizedFactorSet_product_dvd F hF))
  apply sum_flagMixed_le_of_cumulative
  · simpa only [(exactFlag_cumulative _).1] using (hw flagSWeights).trans hc.1
  · calc
      _ = ∑ g : ↥(activeFactors F N), MvPolynomial.weightedTotalDegree flagYSWeights g.1 :=
        Finset.sum_congr rfl (fun g _ ↦ (exactFlag_cumulative g.1).2.1)
      _ ≤ _ := (hw flagYSWeights).trans hc.2.1
  · calc
      _ = ∑ g : ↥(activeFactors F N), MvPolynomial.weightedTotalDegree flagTotalWeights g.1 :=
        Finset.sum_congr rfl (fun g _ ↦ (exactFlag_cumulative g.1).2.2)
      _ ≤ _ := (hw flagTotalWeights).trans hc.2.2

variable [IsAlgClosed K]

def IsolatedPoint (F N A : Poly) (v : Fin 3 → K) : Prop :=
  ∀ D : Ideal Poly, D.IsPrime →
    (∀ w : Fin 3 → K, D ≠ RingHom.ker (MvPolynomial.aeval w).toRingHom) →
    D ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom → F ∈ D → N ∈ D → A ∉ D

/-- .

 -/
theorem exists_active_factor_of_isolated (F N A R : Poly) (hF : F ≠ 0)
    (v : Fin 3 → K) (hvF : MvPolynomial.eval v F = 0)
    (hvA : MvPolynomial.eval v A = 0) (hvR : MvPolynomial.eval v R ≠ 0)
    (hvD : MvPolynomial.eval v (MvPolynomial.pderiv (1 : Fin 3) F) ≠ 0)
    (hi : IsolatedPoint F N A v) :
    ∃ g : ↥(activeFactors F N), MvPolynomial.eval v g.1 = 0 := by
  obtain ⟨g,hg,hgv⟩ := exists_normalizedFactorSet_zero (MvPolynomial.eval v) F hF hvF
  have hs := normalizedFactorSet_spec F g hg
  have hproper : ¬ g ∣ N := by
    intro hgN
    obtain ⟨D,hD⟩ := exists_regular_component K g A R v hgv hvA hvR
    have hmem := regularComponent_G_mem K g A R D
    exact hi D.1 inferInstance (regularComponent_ne_point K g A R D) hD
      (D.1.mem_of_dvd hs.2 hmem) (D.1.mem_of_dvd hgN hmem)
      (regularComponent_T_mem K g A R D)
  have hderiv : MvPolynomial.pderiv (1 : Fin 3) g ≠ 0 := by
    intro hz
    obtain ⟨b,hb⟩ := hs.2
    apply hvD
    rw [hb, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hz, map_zero, hgv]
    ring
  exact ⟨⟨g,Finset.mem_filter.mpr ⟨hg,hproper,hderiv⟩⟩,hgv⟩

/-- .
 -/
theorem isolated_points_card_le (F N A R : Poly) (p q r : FlagDegree)
    (hF : F ≠ 0) (hFp : PolynomialInFlag p F)
    (hNq : PolynomialInFlag q N) (hAr : PolynomialInFlag r A)
    (base : ∀ g : ↥(activeFactors F N), ∀ C : RegularComponent K g.1 N R,
      SeparableLiteralCoordinate C.1)
    (hY : ∀ g : ↥(activeFactors F N), ∀ C : RegularComponent K g.1 N R,
      LiteralProjectionGate C 0)
    (hZ : ∀ g : ↥(activeFactors F N), ∀ C : RegularComponent K g.1 N R,
      LiteralProjectionGate C 2)
    (points : Finset (Fin 3 → K))
    (hcover : ∀ v ∈ points, ∃ g : ↥(activeFactors F N), MvPolynomial.eval v g.1 = 0)
    (hN : ∀ v ∈ points, MvPolynomial.eval v N = 0)
    (hA : ∀ v ∈ points, MvPolynomial.aeval v A = 0)
    (hR : ∀ v ∈ points, MvPolynomial.eval v R ≠ 0)
    (hisolated : ∀ g : ↥(activeFactors F N), ∀ C : RegularComponent K g.1 N R,
      ∀ v ∈ points, C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom → A ∉ C.1) :
    points.card ≤ flagMixed p q r := by
  classical
  letI : DecidableEq K := Classical.decEq K
  let S (g : ↥(activeFactors F N)) : Finset (Fin 3 → K) :=
    points.filter fun (v : Fin 3 → K) ↦ MvPolynomial.eval v g.1 = (0 : K)
  have hcoverage : points ⊆ Finset.univ.biUnion S := by
    intro v hv
    obtain ⟨g,hg⟩ := hcover v hv
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hv,hg⟩⟩
  have hcount (g : ↥(activeFactors F N)) : (S g).card ≤ flagMixed (exactFlag g.1) q r := by
    have hg := activeFactors_spec F N g
    obtain ⟨P⟩ := exists_adaptiveUnitProjectionFamily_of_nested (exactFlag g.1) q
      (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
      ((support_subset_flagSupport_iff _ _).mpr (polynomialIn_exactFlag g.1))
      ((support_subset_flagSupport_iff _ _).mpr hNq)
    let B := P.toPrimeFlagBudgetFamily
    calc
      (S g).card ≤ ∑ C : RegularComponent K g.1 N R,
          (componentSeeds K g.1 N R (S g) id C).card :=
        card_le_sum_componentSeeds K g.1 N R (S g) id
          (fun v hv ↦ (Finset.mem_filter.mp hv).2)
          (fun v hv ↦ hN v (Finset.mem_filter.mp hv).1)
          (fun v hv ↦ hR v (Finset.mem_filter.mp hv).1)
      _ ≤ ∑ C : RegularComponent K g.1 N R, B.weightedCost r C := by
        apply Finset.sum_le_sum
        intro C _
        by_cases hempty : (componentSeeds K g.1 N R (S g) id C).Nonempty
        · obtain ⟨v,hv⟩ := hempty
          have hvP := componentSeeds_on_prime K g.1 N R (S g) id C v hv
          have hvS := componentSeeds_subset K g.1 N R (S g) id C hv
          apply (B.primeBudget C).zero_le r A hAr
            (hisolated g C v (Finset.mem_filter.mp hvS).1 hvP)
          · intro w hw
            exact componentSeeds_on_prime K g.1 N R (S g) id C w hw
          · intro w hw
            exact hA w (Finset.mem_filter.mp
              (componentSeeds_subset K g.1 N R (S g) id C hw)).1
        · simp only [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.card_empty,Nat.zero_le]
      _ ≤ flagMixed (exactFlag g.1) q r := B.sum_weightedCost_le r
  exact ((Finset.card_le_card hcoverage).trans Finset.card_biUnion_le).trans
    ((Finset.sum_le_sum (fun g _ ↦ hcount g)).trans (activeFactors_mixed_sum_le F N hF p q r hFp))

theorem degreeOf_le_flag_total (F : Poly) (p : FlagDegree) (hF : PolynomialInFlag p F)
    (i : Fin 3) : F.degreeOf i ≤ p.zOnly+p.yz+p.all := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := (hF d hd).2.2
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hi with rfl | rfl | rfl <;> omega

/-- .

 -/
theorem exists_small_projection_data (F N R : Poly) (hF : F ≠ 0)
    (p q : FlagDegree) (hFp : PolynomialInFlag p F) (hNq : PolynomialInFlag q N)
    (c : ℕ) [CharP K c] (hdeg : p.zOnly+p.yz+p.all < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c) :
    ∃ base : ∀ g : ↥(activeFactors F N), ∀ C : RegularComponent K g.1 N R,
        SeparableLiteralCoordinate C.1,
      (∀ g : ↥(activeFactors F N), ∀ C : RegularComponent K g.1 N R, LiteralProjectionGate C 0) ∧
      (∀ g : ↥(activeFactors F N), ∀ C : RegularComponent K g.1 N R, LiteralProjectionGate C 2) := by
  have hgate (g : ↥(activeFactors F N)) (C : RegularComponent K g.1 N R)
      (i : Fin 3) (hi : Transcendental K (coordinate K C.1 i)) :
      letI : Algebra (RatFunc K) (CoordinateField K C.1) := rationalBaseAlgebra K C.1 i hi
      FiniteDimensional (RatFunc K) (CoordinateField K C.1) ∧
        Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1) := by
    have hg := activeFactors_spec F N g
    have hgdeg (j : Fin 3) : g.1.degreeOf j ≤ p.zOnly+p.yz+p.all :=
      (coordinate_degree_le_of_dvd j g.1 F hg.2.1 hF).trans (degreeOf_le_flag_total F p hFp j)
    have hNdeg (j : Fin 3) := degreeOf_le_flag_total N q hNq j
    apply finite_separable_at_of_original_coordinate_gate K C.1 i hi c g.1 N
      hg.1 (regularComponent_G_mem K _ _ _ C) (regularComponent_T_mem K _ _ _ C)
      hg.2.2.1 (fun j ↦ (hgdeg j).trans_lt hdeg)
    have hprod (u v : Fin 3) : N.degreeOf u*g.1.degreeOf v+g.1.degreeOf u*N.degreeOf v ≤
        2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) := by
      calc
        _ ≤ (q.zOnly+q.yz+q.all)*(p.zOnly+p.yz+p.all)+
            (p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) :=
          Nat.add_le_add (Nat.mul_le_mul (hNdeg u) (hgdeg v))
            (Nat.mul_le_mul (hgdeg u) (hNdeg v))
        _ = _ := by ring
    have hi3 : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi3 with rfl | rfl | rfl
    · rw [coordinateMixedDegree_zero]; exact (hprod 1 2).trans_lt hmix
    · rw [coordinateMixedDegree_one]; exact (hprod 0 2).trans_lt hmix
    · rw [coordinateMixedDegree_two]; exact (hprod 0 1).trans_lt hmix
  refine ⟨fun g C ↦ Classical.choice (exists_separableLiteralCoordinate_of_YZ_gates C.1
    (regularComponent_ne_point K _ _ _ C) (hgate g C 0) (hgate g C 2)),?_,?_⟩
  · exact fun g C ↦ hgate g C 0
  · exact fun g C ↦ hgate g C 2

end
end ProximityPrize.SubmissionLower.ContactFactoredFlagCount6676Research
