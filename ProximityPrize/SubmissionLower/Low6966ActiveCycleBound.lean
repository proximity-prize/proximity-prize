import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup58
import ProximityPrize.SubmissionLower.Low6966GeometryCut

section Merged6967_Low6966ActiveCycleBound
set_option Elab.async false



set_option Elab.async false

set_option autoImplicit false
set_option Elab.async false

namespace Low6966ActiveCycle

noncomputable section

open Low48BentCycle (Family mixedDegree properCut cycleComparison divisorBound diagonalExponents)

open Low6966Prices (SmallFactor)
open Low6966GeometryCut_2 (Branch)
open Low6966GeometryCut_2_3 (graphLift chart_index_eq graphLift_same_chart
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
open Low6966GeometryCut_2_3 (liftedPoint eval_liftedPoint liftedPoint_old liftedPoint_mem)

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
  have hgraph := @Low6966GeometryCut_2_3_1.proof f Q l
  have hmember := @Low6966GeometryCut_2_3_2.proof f Q l
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

end Low6966ActiveCycle

end Merged6967_Low6966ActiveCycleBound

section Merged6967_Low6966SharedCycleFour
set_option Elab.async false

set_option Elab.async false

namespace Low6966SharedCycleFour
noncomputable section
open Low6966Prices (SmallFactor primaryBox taylorLength)
open Low6966GeometryCut (membershipTest)
open Low6966GeometryCut_2 (Branch Slice4 budget4)
open K1_13 (Row Shape shape InBox chart mixed32 volume32 difference)
open K1_13_6 (GeoJets GeoField toGeneric divisorIdeal cycleLength intersectionIdeal separant)
open K1_13_6_2 (JetPoint Box4)
open K1_13_6_2_3 (ChamberBox dimension capCoeff polarize mixedDegree localWeight pointIdeal
  chart_box generic_box regular_cut cut_dimension dimension_bot pair_regular intersection_eq
  surface_dimension weight_cast weight_pos point_injective point_prime point_degree point_proper_section)
open scoped BigOperators
open Low6966GeometryCut_2_2 (surface_slice_sum ambient_degree)

theorem bound_with_cut (h1 : K1_13_6_2_3.c1)
    (h2 : K1_13_6_2_3.c2) (h3 : K1_13_6_2_3.c3)
    (f Q cut : Row 4) (l : ℕ) (hf : SmallFactor f) (hproper : ¬ f ∣ cut)
    (q : Shape) (hq : ChamberBox q) (hQ : InBox (shape cut) q)
    (weight : Ideal GeoJets → ℕ)
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hT : ∀ b ∈ F, Box4 (chart (taylorLength + 1) (shape f).chamber) b.member ∧
      (∀ p ∈ T b, b.Contains p) ∧ Slice4 b (T b))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal f cut).IsMinimalPrime b.surface,
       (weight b.surface : ℕ∞) ≤ cycleLength (intersectionIdeal f cut) b.surface h.isPrime) :
    let p := (shape f).chamber
    (∑ b ∈ F, (weight b.surface : ℚ) * ((b.weight * (T b).card : ℕ) : ℚ)) ≤
      (mixed32 p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p) : ℚ) / 32 := by
  classical
  dsimp only
  let p := (shape f).chamber
  let r := chart (taylorLength + 1) p
  let s := chart (taylorLength + 2) p
  have hp : ChamberBox p :=
    ⟨(K1_13_7_1.shape_chamber f).1, (K1_13_7_1.shape_chamber f).2, hf.2.1⟩
  have hr : ChamberBox r := chart_box _ _ (Nat.zero_lt_succ _)
  have hs : ChamberBox s := chart_box _ _ (Nat.zero_lt_succ _)
  have hboxes : ∀ q ∈ [r,s], ChamberBox q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact hq.elim (fun h => h ▸ hr) (fun h => h ▸ hs)
  let J := intersectionIdeal f cut
  let H : Ideal GeoJets := Ideal.span {toGeneric f}
  have hpair := K1_13_7_1.proper_generic f cut hf.1 hproper
  have hf0 : toGeneric f ≠ 0 := by
    intro hz
    exact hf.1.ne_zero (K1_13_7_1.toGeneric_injective (hz.trans (map_zero _).symm))
  have hregF : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets) (toGeneric f)) :=
    regular_cut (by infer_instance) (by simpa using hf0)
  have hregQ := pair_regular f cut hpair
  have hH : dimension H ≤ 3 := by
    simpa [H, dimension_bot] using cut_dimension hregF
  have hJ : dimension J ≤ 2 := by
    rw [show J = H ⊔ Ideal.span {toGeneric cut} from intersection_eq f cut]
    have hdrop : dimension (H ⊔ Ideal.span {toGeneric cut}) ≤ dimension H - 1 := cut_dimension hregQ
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
    exact surface_slice_sum h2 h3 ref (surface_dimension hf0 hpair hmin) _ T
      (fun _ hb => (Finset.mem_filter.mp hb).2) (hT ref href).1
      (fun b hb => (hT b (Finset.mem_filter.mp hb).1).2)
  change (∑ b ∈ F, (weight b.surface : ℚ) * cost b) ≤ (mixed32 p q r s : ℚ) / 32
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
    _ ≤ mixedDegree H [q,r,s] := by
      rw [show J = H ⊔ Ideal.span {toGeneric cut} from intersection_eq f cut]
      exact h2 H q [r,s] hq hboxes (by simpa using hH) _ (generic_box hQ) hregQ
    _ ≤ mixedDegree (⊥ : Ideal GeoJets) [p,q,r,s] := by
      rw [show H = (⊥ : Ideal GeoJets) ⊔ Ideal.span {toGeneric f} by simp [H]]
      apply h2 _ p [q,r,s] hp _ (by simp) _ _ hregF
      · intro u hu
        exact (List.mem_cons.mp hu).elim (fun h => h ▸ hq) (hboxes u)
      · exact generic_box ⟨le_max_left _ _, le_rfl, le_rfl⟩
    _ ≤ _ := ambient_degree h1 hp hq hr hs

#print axioms bound_with_cut
end
end Low6966SharedCycleFour

end Merged6967_Low6966SharedCycleFour
