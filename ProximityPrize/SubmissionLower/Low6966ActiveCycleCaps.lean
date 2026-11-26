import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Low6966ActiveCycleBound
import ProximityPrize.SubmissionLower.R6960HelperPrefix

section Merged6967_Low6966ActiveCycleCaps
set_option Elab.async false






set_option Elab.async false



-- merged module R6960Low6966ActiveCycleCaps
section Merged_R6960Low6966ActiveCycleCaps

set_option autoImplicit false
set_option Elab.async false

namespace Low6966ActiveCycle
noncomputable section
open K1_13 (Shape InBox Row shape)
open K1_13_6 (GeoField genericCoeffs toGeneric)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (Exponent oldEmbedding)
open Low6966Prices (primaryBox taylorLength evenClip)
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
  · change 1650 ≤ 4012 ∧ 3 * 550 ≤ 1650 ∧ 2 * 0 ≤ (550 : ℕ)
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
    slots.map (fun i => ((caps p i).2, clips p K i)) = Low6966Prices.activeClips p K := by
  change [(0, baseClip p K), (0, 498), (1, graphClip p K),
    ((lifted p (taylorLength - 4)).2, liftClip p K (taylorLength - 4)),
    ((lifted p (taylorLength - 3)).2, liftClip p K (taylorLength - 3))] = _
  rw [lift_height p ht, lift_height p ht]
  rfl

private theorem mem_slots (i : Fin 5) : i ∈ slots := by fin_cases i <;> decide

theorem caps_active {f : Row 4} {K : ℕ}
    (hg : Low6966Prices.tiltedFits (shape f))
    (ha : Low6966Prices.activeFitsPrice (shape f) K) :
    ∀ i, Low49ActiveLattice.Fits (caps (shape f).chamber i) (clips (shape f).chamber K i) := by
  let p := (shape f).chamber
  have ht : 3 ≤ p.t := ha.1
  have hgj : p.j + 1 ≤ p.b := hg.2.trans (le_max_left _ _)
  have hCh := caps_chamber (le_max_right _ _) (by omega : 1 ≤ p.t) hg.1
  have hl (i : Fin 5) : 2 * (caps p i).2 ≤ clips p K i := by
    have H := ha.2.2
    change (Low6966Prices.activeClips p K).all _ = true at H
    rw [← clip_list p K ht, List.all_eq_true] at H
    simpa using H _ (List.mem_map_of_mem (mem_slots i))
  intro i
  fin_cases i
  · exact fit_clip (p, 0) (hCh 0) _ (hl 0)
  · change Low49ActiveLattice.Fits (primaryBox, 0) 498
    show 1650 + 498 ≤ 4012 ∧ 3 * 550 ≤ 1650 ∧ 2*498 ≤ 1650 ∧
      498 + 2*0 ≤ 2*550 ∧ 2*0 ≤ 498 ∧ 498 % 2 = 0
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
    (h : InBox (shape P) q) (hK : Low6966Prices.ActiveFits P K) (hc : K + c ≤ q.b + q.j) :
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
end Low6966ActiveCycle

end Merged_R6960Low6966ActiveCycleCaps

end Merged6967_Low6966ActiveCycleCaps

section Merged6967_Low6966SharedCycleBound
set_option Elab.async false


set_option Elab.async false

set_option autoImplicit false
set_option Elab.async false

namespace Low6966SharedCycleBound

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

open Low6966ActiveCycle (Section Doubled Slice)
open Low6966ActiveCycle (square_support bound_marks)

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
  have hgraph := @Low6966GeometryCut_2_3_1.proof f Q l
  have hmember := @Low6966GeometryCut_2_3_2.proof f Q l
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

#print axioms bound_with_cut

end

end Low6966SharedCycleBound

end Merged6967_Low6966SharedCycleBound
