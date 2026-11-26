import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low48BentCyclePrice

section Merged6967_Low6966Leading
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true

section
namespace Low6966Leading_1
noncomputable section
variable {top : Fin 16}
open P3 (I K)
open Low6966Prices (Messages taylorLength physicalDegree)
open Low6966Leading (ProperCover SecondFactors Whole mixedBudget invariantBudget)
open K1_13 (Row Geom atJet extend)
open K1_13_5 (RegularAt NodeFamily separant)
open K1_13_5_4 (GeometricX GeoRow genericRow genericCoeff genericCoeff_injective
  jetPoint regularLocus eval_genericRow_at_point jetPoint_injOn)
open Polynomial
open scoped BigOperators
def c1 (top : Fin 16) : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors top f → ∀ T : ∀ i, LiftedChart top (f i),
    Nonempty (MixedSections top f T)
def c2 (top : Fin 16) : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors top f → ∀ a ∈ properComponents f,
    SimpleInvariant (f a.1) a.2 →
    ∃ Q : CoefficientIdeal, ActualSolutionCurve (f a.1) Q ∧
      ∀ S : (Polynomial Geom), S.natDegree ≤ physicalDegree → jetPoint S ∈ regularLocus (f a.1) a.2 →
        coefficientPoint S ∈ MvPolynomial.zeroLocus GeometricX Q
def c3 (top : Fin 16) : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors top f →
    (∀ i, (oldCut (f i)).totalDegree ≤
      1 + (2 * (taylorLength + 1) - 7) * ((f i).totalDegree - 1)) →
    ∀ C : Finset CoefficientIdeal,
      (∀ Q ∈ C, ∃ i, ¬ Whole (f i) ∧ ActualSolutionCurve (f i) Q) →
      ∃ d : CoefficientIdeal → ℕ,
        (∀ Q ∈ C, 0 < d Q ∧ MvPolynomial.affineDegree Q ≤ (d Q : ℚ)) ∧
          (∑ Q ∈ C, d Q) ≤ (invariantBudget top)
private theorem exists_properComponent {n : ℕ} {f : Fin n → Row 3}
    (T : ∀ i, LiftedChart top (f i)) {i : Fin n} {S : (Polynomial Geom)}
    (hS : S.natDegree ≤ physicalDegree) (hr : RegularAt 2 (f i) S) (hw : ¬ Whole (f i)) :
    ∃ P, (i, P) ∈ properComponents f ∧ jetPoint S ∈ regularLocus (f i) P := by
  have hzero : jetPoint S ∈ MvPolynomial.zeroLocus GeometricX (oldCutIdeal (f i)) := by
    apply MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mpr
    apply Ideal.span_le.mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    change g ∈ RingHom.ker (MvPolynomial.aeval (jetPoint S))
    rw [RingHom.mem_ker]
    change MvPolynomial.eval (jetPoint S) g = 0
    rcases hg with rfl | rfl
    · rw [eval_genericRow_at_point, hr.1, map_zero]
    · rw [eval_genericRow_at_point, (T i).actual S hS hr |>.1, map_zero]
  have hsep : MvPolynomial.eval (jetPoint S) (genericRow (separant (f i))) ≠ 0 := by
    rw [eval_genericRow_at_point]
    exact fun h => hr.2 ((map_eq_zero_iff genericCoeff genericCoeff_injective).mp h)
  obtain ⟨P, hP, hy⟩ := MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus
    (oldCutIdeal (f i)) (genericRow (separant (f i))) (jetPoint S) hzero hsep
  exact ⟨P, mem_properComponents.mpr ⟨hw, hP⟩, ⟨hy, hsep⟩⟩
private def componentMarks {n : ℕ} (f : Fin n → Row 3)
    (Γ : Finset K) (s : K → (Polynomial K)) (a : CurveIndex n) : Finset K := by
  classical
  exact Γ.filter fun γ => jetPoint (extend (s γ)) ∈ regularLocus (f a.1) a.2
private theorem mem_componentMarks {n : ℕ} {f : Fin n → Row 3} {Γ : Finset K}
    {s : K → (Polynomial K)} {a : CurveIndex n} {γ : K} : γ ∈ componentMarks f Γ s a ↔
    γ ∈ Γ ∧ jetPoint (extend (s γ)) ∈ regularLocus (f a.1) a.2 := by
  classical
  exact Finset.mem_filter
private theorem regular_of_componentMark {n : ℕ} {f : Fin n → Row 3} {a : CurveIndex n}
    {S : (Polynomial Geom)} (ha : a ∈ properComponents f) (hS : jetPoint S ∈ regularLocus (f a.1) a.2) :
    RegularAt 2 (f a.1) S := by
  have hp := (Ideal.mem_retainedMinimalPrimes.mp (mem_properComponents.mp ha).2).1.le
  have hz : genericRow (f a.1) ∈ oldCutIdeal (f a.1) := Ideal.subset_span (by simp)
  have he : MvPolynomial.eval (jetPoint S) (genericRow (f a.1)) = 0 :=
    hS.1 _ (hp hz)
  have hsep := hS.2
  rw [eval_genericRow_at_point] at he hsep
  refine ⟨?_, fun h => hsep (by rw [show atJet (separant (f a.1)) S = 0 from h, map_zero])⟩
  exact (map_eq_zero_iff genericCoeff genericCoeff_injective).mp he
private theorem mixedComponent_card {w Γ s n f} (hm : Messages w Γ s)
    {T : ∀ i, LiftedChart top (f i)} (M : MixedSections top (n := n) f T)
    {a : CurveIndex n} (ha : a ∈ properComponents f) (hi : ¬ SimpleInvariant (f a.1) a.2) :
    (componentMarks f Γ s a).card ≤ M.length a * M.degree a := by
  classical
  have hsub : componentMarks f Γ s a ⊆ Γ := fun _ hg => (mem_componentMarks.mp hg).1
  have hdeg (γ : K) (hγ : γ ∈ Γ) : (extend (s γ)).natDegree ≤ physicalDegree := by
    simpa only [Polynomial.natDegree_map] using hm.degree γ hγ
  by_cases hlen : M.length a = 1
  · have hsimp : componentLength (f a.1) a.2 = 1 := by rw [← M.length_eq a ha, hlen, Nat.cast_one]
    have hn : genericRow (oldNext (f a.1)) ∉ a.2 := fun hn => hi ⟨hsimp, hn⟩
    obtain ⟨hfinite, hcard⟩ := M.points a ha hn
    let pt := fun γ => jetPoint (n := 3) (extend (s γ))
    have hpts : ↑((componentMarks f Γ s a).image pt) ⊆ nextCutLocus (f a.1) a.2 := by
      intro y hy
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hmem, hy⟩ := mem_componentMarks.mp hγ
      have hreg := regular_of_componentMark ha hy
      exact ⟨hy, by rw [eval_genericRow_at_point, ((T a.1).actual _ (hdeg γ hmem) hreg).2.1, map_zero]⟩
    have hle := (Set.ncard_le_ncard hpts hfinite).trans hcard
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn ((jetPoint_injOn s Γ hm.distinct).mono hsub)] at hle
    simpa [hlen] using hle
  · have htwo : 2 ≤ M.length a := by have := M.length_pos a ha; omega
    obtain ⟨Q, hprime, hdim, hd, hdegree, hrec⟩ := M.curves a ha htwo
    have hm' := hm.mono hsub
    have hcap := nodeCapacity_of_coefficient_curve hm' Q hprime hdim hdegree (by
      intro γ hγ
      obtain ⟨hmem, hy⟩ := mem_componentMarks.mp hγ
      have hreg := regular_of_componentMark ha hy
      rw [← ((T a.1).actual _ (hdeg γ hmem) hreg).2.2]
      exact hrec _ hy)
    exact (curveCount_le_twice_degree hm' hd hcap).trans (Nat.mul_le_mul_right _ htwo)
private def coefficientFamily {w Γ s} (hm : Messages w Γ s)
    (C : Finset CoefficientIdeal) (d : CoefficientIdeal → ℕ)
    (hcut : ∀ Q ∈ C, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      MvPolynomial.affineDegree Q ≤ (d Q : ℚ)) : NodeFamily w Γ s := by
  classical
  let e : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
  let part : Fin C.card → Finset K := fun i => Γ.filter fun γ =>
    coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX (e i).val
  have hs : ∀ i, part i ⊆ Γ := fun _ => Finset.filter_subset _ _
  refine ⟨C.card, part, fun i => d (e i).val, hs, ?_⟩
  intro i
  obtain ⟨hp, hdim, hd⟩ := hcut (e i).val (e i).property
  exact nodeCapacity_of_coefficient_curve (hm.mono (hs i)) (e i).val hp hdim hd
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
private theorem coefficientFamily_total {w Γ s} (hm : Messages w Γ s)
    (C : Finset CoefficientIdeal) (d : CoefficientIdeal → ℕ) (hcut) :
    (coefficientFamily hm C d hcut).totalCap = ∑ Q ∈ C, d Q := by
  classical
  let e : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
  change (∑ i : Fin C.card, d (e i).val) = ∑ Q ∈ C, d Q
  rw [Equiv.sum_comp e (fun P : C => d P.val), Finset.sum_coe_sort]
private theorem mem_coefficientFamily {w Γ s} (hm : Messages w Γ s)
    (C : Finset CoefficientIdeal) (d : CoefficientIdeal → ℕ) (hcut) {γ : K} (hγ : γ ∈ Γ)
    {Q : CoefficientIdeal} (hQ : Q ∈ C)
    (hy : coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX Q) :
    γ ∈ (coefficientFamily hm C d hcut).labels := by
  classical
  let e : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
  rw [NodeFamily.labels]
  let i := e.symm ⟨Q, hQ⟩
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, ?_⟩⟩
  change coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX (e i).val
  simpa [i] using hy
private def emptyFamily (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) : NodeFamily w Γ s where
  n := 0
  part := Fin.elim0
  cap := Fin.elim0
  sub i := Fin.elim0 i
  localCapacity i := Fin.elim0 i
theorem of_children (h1 : c1 top) (h2 : c2 top) (h3 : c3 top) : Low6966Leading.c1 top := by
  classical
  intro w Γ s hm n f hf marks
  let T (i : Fin n) := Classical.choice (lifted_chart n f hf i)
  obtain ⟨M⟩ := h1 n f hf T
  let direct := (properComponents f).filter fun a => ¬ SimpleInvariant (f a.1) a.2
  let isolated := direct.biUnion (componentMarks f Γ s)
  have hmixed : isolated.card ≤ mixedBudget top := by
    calc
      _ ≤ ∑ a ∈ direct, (componentMarks f Γ s a).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ direct, M.length a * M.degree a := Finset.sum_le_sum fun a ha =>
        mixedComponent_card hm M (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      _ ≤ ∑ a ∈ properComponents f, M.length a * M.degree a :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ _ := M.total
  let stable := (properComponents f).filter fun a => SimpleInvariant (f a.1) a.2
  have heach (a : stable) := h2 n f hf a.val (Finset.mem_filter.mp a.property).1
    (Finset.mem_filter.mp a.property).2
  choose Q hQ hrec using heach
  let C := stable.attach.image Q
  have hfresh : ∀ P ∈ C, ∃ i, ¬ Whole (f i) ∧ ActualSolutionCurve (f i) P := by
    intro P hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    have ha := (Finset.mem_filter.mp a.property).1
    exact ⟨a.val.1, (mem_properComponents.mp ha).1, hQ a⟩
  obtain ⟨d, hd, hsum⟩ := h3 n f hf (fun i => ordinary_bound (f i)) C hfresh
  have hcut (P : CoefficientIdeal) (hp : P ∈ C) : P.IsPrime ∧
      (MvPolynomial.affineHilbertPolynomial P).natDegree ≤ 1 ∧
      MvPolynomial.affineDegree P ≤ (d P : ℚ) := by
    obtain ⟨i, _, h⟩ := hfresh P hp
    exact ⟨h.prime, h.dimension.le, (hd P hp).2⟩
  let F := coefficientFamily hm C d hcut
  have hFnum : F.n ≤ (invariantBudget top) := by
    calc
      F.n = ∑ P ∈ C, 1 := Finset.card_eq_sum_ones C
      _ ≤ ∑ P ∈ C, d P := Finset.sum_le_sum fun P hp => (hd P hp).1
      _ ≤ _ := hsum
  refine ⟨⟨isolated, emptyFamily w Γ s, F, ?_, ?_, ?_, ?_⟩⟩
  · intro γ hγ
    obtain ⟨i, hi, hw⟩ := marks γ hγ
    have hdeg : (extend (s γ)).natDegree ≤ physicalDegree := by
      simpa only [Polynomial.natDegree_map] using hm.degree γ hγ
    obtain ⟨P, hp, hy⟩ := exists_properComponent T hdeg hi hw
    by_cases hs : SimpleInvariant (f i) P
    · let a : stable := ⟨(i, P), Finset.mem_filter.mpr ⟨hp, hs⟩⟩
      have hQC : Q a ∈ C := Finset.mem_image.mpr ⟨a, Finset.mem_attach _ _, rfl⟩
      exact Finset.mem_union_right _ (mem_coefficientFamily hm C d hcut hγ hQC
        (hrec a _ hdeg hy))
    · have hγiso : γ ∈ isolated := Finset.mem_biUnion.mpr
        ⟨(i,P), Finset.mem_filter.mpr ⟨hp, hs⟩, mem_componentMarks.mpr ⟨hγ, hy⟩⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hγiso)
  · have hz : (emptyFamily w Γ s).totalCap = 0 := by
      change (∑ i : Fin 0, (Fin.elim0 i : ℕ)) = 0
      exact Finset.sum_eq_zero fun i _ => Fin.elim0 i
    simpa [hz] using hmixed
  · exact (coefficientFamily_total hm C d hcut).trans_le hsum
  · change 0 + F.n ≤ 2 * (invariantBudget top)
    omega
end
end Low6966Leading_1
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1
noncomputable section
variable {top : Fin 16}
open K1_13 (Row)
open K1_13_5 (separant)
open Low6966Leading (graphBox liftedBox)
open K1_13_5_4 (InLiftedBox GeoRow GeometricX genericRow)
open K1_13_5_4_2 (JetPoint ExponentSpace boxExponents graphLocus graphCurve capBody mixedVolume4)
open Low6966Prices (taylorLength)
open Low6966Leading (Whole)
open Low6966Leading_1 (oldCutIdeal)
open MvPolynomial
def factorCurves (f : Row 3) : Finset (Ideal (GeoRow 3)) := by
  classical
  exact if Whole f then ∅ else
    (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))
abbrev lastBox (top : Fin 16) := liftedBox top (taylorLength + 2)
abbrev lastExponents (top : Fin 16) := boxExponents (lastBox top) taylorLength
abbrev lastMap (top : Fin 16) := monomialMap GeometricX (lastExponents top)
def sectionIdeal (top : Fin 16) (f : Row 3) (P : Ideal (GeoRow 3)) :
    Ideal (MvPolynomial (lastExponents top) GeometricX) :=
  (graphCurve f P).comap (lastMap top)
def IsSectionCurve (top : Fin 16) (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  (sectionIdeal top f P).IsPrime ∧ (affineHilbertPolynomial (sectionIdeal top f P)).natDegree = 1
def sectionDegree (top : Fin 16) (f : Row 3) (P : Ideal (GeoRow 3)) : ℚ :=
  affineDegree (sectionIdeal top f P)
structure GenericSection (top : Fin 16) (f : Row 3) where
  polynomial : GeoRow 4
  support : InLiftedBox polynomial (lastBox top) taylorLength
  points : Ideal (GeoRow 3) → Finset JetPoint
  card_eq : ∀ P ∈ factorCurves f, ((points P).card : ℚ) = sectionDegree top f P
  proper : ∀ P ∈ factorCurves f, polynomial ∉ graphCurve f P
  roots : ∀ P ∈ factorCurves f, ∀ y ∈ points P,
    y ∈ graphLocus f P ∧ eval y polynomial = 0
  off_other_curves : ∀ P ∈ factorCurves f, ∀ P' ∈ factorCurves f, P ≠ P' →
    ∀ y ∈ points P, y ∉ graphLocus f P'
def lastMixedVolume (top : Fin 16) (first : Set ExponentSpace) : ℝ :=
  mixedVolume4 ![first, capBody (graphBox top) 1,
    capBody (liftedBox top (taylorLength + 1)) (taylorLength - 1),
    capBody (lastBox top) taylorLength]
end
end Low6966Leading_1_1
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1
noncomputable section
variable {top : Fin 16}
open K1_13 (Row Geom Shape)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericCoeff_injective genericRow
  liftRow regularLocus graphPoint)
open K1_13_5_4_2 (boxExponents graphCurve eval_represents_iff)
open Low6966Prices (taylorLength)
open Low6966Leading (Whole)
open Low6966Leading_1 (oldCut oldCutIdeal properComponents CurveIndex componentLength nextCutLocus
  oldNext LiftedChart)
open MvPolynomial RingTheory.Sequence
open scoped BigOperators Polynomial
open K1_13_5_4_2_1 (quotient_regular_iff graph_dimension)
open K1_13_5_4_2 (graphPoint_injective)
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem mem_factorCurves {f : Row 3} {P : Ideal (GeoRow 3)} :
    P ∈ factorCurves f ↔ ¬ Whole f ∧
      P ∈ (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f)) := by
  classical
  by_cases hf : Whole f <;> simp [factorCurves, hf]
theorem properComponents_eq {n : ℕ} (f : Fin n → Row 3) :
    properComponents f = Finset.univ.biUnion fun i =>
      (factorCurves (f i)).image (fun P => (i, P)) := by
  classical
  unfold properComponents
  congr 1
  funext i
  by_cases hf : Whole (f i) <;> simp [factorCurves, hf]
theorem mem_properComponents {n : ℕ} {f : Fin n → Row 3} {a : CurveIndex n} :
    a ∈ properComponents f ↔ a.2 ∈ factorCurves (f a.1) := by
  classical
  rcases a with ⟨i, P⟩
  rw [properComponents_eq]
  simp
theorem sum_properComponents {n : ℕ} (f : Fin n → Row 3) (v : CurveIndex n → ℕ) :
    (∑ a ∈ properComponents f, v a) =
      ∑ i, ∑ P ∈ factorCurves (f i), v (i, P) := by
  classical
  rw [properComponents_eq, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨Q, _, he⟩ := Finset.mem_image.mp hb
    exact hij (Prod.mk.inj he).1.symm
theorem componentLength_of_retained {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    0 < componentLength f P ∧ componentLength f P < ⊤ := by
  classical
  have hm := (Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2).1
  have hp : P.IsPrime := hm.isPrime
  rw [componentLength, dite_eq_left hp]
  let A := Localization.AtPrime P
  let L := (oldCutIdeal f).map (algebraMap (GeoRow 3) A)
  have hle : L ≤ IsLocalRing.maximalIdeal A := by
    apply Ideal.map_le_iff_le_comap.mpr
    change oldCutIdeal f ≤ (IsLocalRing.maximalIdeal A).under (GeoRow 3)
    rw [IsLocalization.AtPrime.under_maximalIdeal A P]
    exact hm.le
  have hL : L ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hle
  let : Nontrivial (A ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr hL
  exact ⟨Module.length_pos, K1_13_5_4_2.localLength_lt_top hm⟩
theorem componentLength_toNat {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    ((componentLength f P).toNat : ℕ∞) = componentLength f P :=
  ENat.natCast_toNat (componentLength_of_retained hP).2.ne
theorem componentLength_toNat_pos {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) : 0 < (componentLength f P).toNat := by
  have h := (componentLength_of_retained hP).1
  rw [← componentLength_toNat hP] at h
  exact_mod_cast h
private theorem single_mem_box (s : Shape) (h : ℕ)
    (hb : 1 ≤ s.b) (hj : 2 ≤ s.j) (ht : 1 ≤ s.t) (hh : 1 ≤ h)
    (i : Fin 4) : Finsupp.single i 1 ∈ boxExponents s h := by
  change (Finsupp.single i 1) 0 + (Finsupp.single i 1) 1 + (Finsupp.single i 1) 2 ≤
    s.b ∧ (Finsupp.single i 1) 1 + 2 * (Finsupp.single i 1) 2 ≤ s.j ∧
    (Finsupp.single i 1) 2 ≤ s.t ∧ (Finsupp.single i 1) 3 ≤ h
  fin_cases i <;> norm_num [Finsupp.single_apply] <;> omega
theorem lastExponents_single (i : Fin 4) : Finsupp.single i 1 ∈ (lastExponents top) :=
  single_mem_box (lastBox top) taylorLength
    (show 1 ≤ (lastBox top).b by fin_cases top <;> decide) (show 2 ≤ (lastBox top).j by fin_cases top <;> decide)
    (show 1 ≤ (lastBox top).t by fin_cases top <;> decide) (show 1 ≤ 133388 by decide) i
private theorem cut_regular {f : Row 3} (hf : Irreducible f) (hw : ¬ Whole f) :
    IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span {genericRow f}) (genericRow (oldCut f))) := by
  let : Algebra (Polynomial Geom) GeometricX := genericCoeff.toAlgebra
  have : Module.IsTorsionFree ((Polynomial Geom)) GeometricX :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr genericCoeff_injective
  have : Module.Flat ((Polynomial Geom)) GeometricX := inferInstance
  have hbase : IsBaseChange (Row 3)
      (IsScalarTower.toAlgHom ((Polynomial Geom)) GeometricX (GeoRow 3)).toLinearMap :=
    Algebra.IsPushout.out
  have : Module.Flat (Row 3) (GeoRow 3) :=
    Module.Flat.isBaseChange (R := (Polynomial Geom)) (S := Row 3) (M := GeometricX)
      (N := GeoRow 3) hbase
  have : (Ideal.span {f} : Ideal (Row 3)).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hc : oldCut f ∉ (Ideal.span {f} : Ideal (Row 3)) :=
    fun h => hw (Ideal.mem_span_singleton.mp h)
  have hseq : IsWeaklyRegular (Row 3) [f, oldCut f] := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff, quotient_regular_iff]
    exact ⟨fun _ _ h => mul_left_cancel₀ hf.ne_zero h,
      fun _ _ h => mul_left_cancel₀ (mt Ideal.Quotient.eq_zero_iff_mem.mp hc) h⟩
  have h := hseq.of_flat (S := GeoRow 3)
  change IsWeaklyRegular (GeoRow 3) [genericRow f, genericRow (oldCut f)] at h
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff, quotient_regular_iff] at h
  exact h.2
private theorem retained_dimension {f : Row 3} (hf : Irreducible f)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) :
    (affineHilbertPolynomial P).natDegree = 1 := by
  obtain ⟨hw, hret⟩ := mem_factorCurves.mp hP
  have hmin := (Ideal.mem_retainedMinimalPrimes.mp hret).1
  let := hmin.isPrime
  let H : Ideal (GeoRow 3) := Ideal.span {genericRow f}
  let g := genericRow (oldCut f)
  have heq : oldCutIdeal f = H ⊔ Ideal.span {g} := by
    rw [← Ideal.span_union]
    rfl
  have hHP : H ≤ P := le_sup_left.trans (heq ▸ hmin.le)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hHP
  let := hQ.isPrime
  have hgQ : g ∉ Q := by
    intro hg
    obtain ⟨a, ha, hga⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hQ hg
    have hga' : Ideal.Quotient.mk H g * Ideal.Quotient.mk H a = Ideal.Quotient.mk H g * 0 := by
      rw [← map_mul, mul_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hga
    exact ha (Ideal.Quotient.eq_zero_iff_mem.mp (cut_regular hf hw hga'))
  have hP' : P ∈ (Q ⊔ Ideal.span {g}).minimalPrimes := by
    have hle : H ⊔ Ideal.span {g} ≤ Q ⊔ Ideal.span {g} := sup_le_sup_right hQ.le _
    refine ⟨⟨hmin.isPrime, sup_le hQP (le_sup_right.trans (heq ▸ hmin.le))⟩, ?_⟩
    intro J hJ hJP
    exact hmin.2 ⟨hJ.1, heq.trans_le (hle.trans hJ.2)⟩ hJP
  have hF : genericRow f ≠ 0 :=
    fun h => hf.ne_zero (map_injective _ genericCoeff_injective (h.trans (map_zero _).symm))
  have hdQ := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hQ
  have hdP := principalCut_natDegree_affineHilbertPolynomial_add_one hgQ hP'
  rw [Nat.card_fin] at hdQ
  omega
theorem section_curve {f : Row 3} (hf : Irreducible f)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) : IsSectionCurve top f P := by
  have hm := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let := hm.1.isPrime
  obtain ⟨hprime, hdim⟩ := graph_dimension f P hm.2
  refine ⟨hprime.comap (lastMap top), ?_⟩
  unfold sectionIdeal
  rw [natDegree_affineHilbertPolynomial_comap_of_surjective (lastMap top)
      (monomialMap_surjective lastExponents_single), hdim, retained_dimension hf hP]
private theorem eval_factor_of_regular {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) {x : Fin 3 → GeometricX} (hx : x ∈ regularLocus f P) :
    eval x (genericRow f) = 0 :=
  hx.1 _ ((Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2).1.le
    (Ideal.subset_span (by simp)))
private theorem next_notMem_graphCurve {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (T : LiftedChart top f) (hnext : genericRow (oldNext f) ∉ P) :
    T.next ∉ graphCurve f P := by
  intro hn
  have hm := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let := hm.1.isPrime
  have hvanish : genericRow (separant f) * genericRow (oldNext f) ∈
      vanishingIdeal GeometricX (zeroLocus GeometricX P) := by
    intro x hx
    change eval x (_ * _) = 0
    rw [map_mul]
    by_cases hs : eval x (genericRow (separant f)) = 0
    · rw [hs, zero_mul]
    · have hr : x ∈ regularLocus f P := ⟨hx, hs⟩
      have he : eval (graphPoint f x) T.next = 0 := hn _ ⟨x, hr, rfl⟩
      rw [(eval_represents_iff T.next_represents (eval_factor_of_regular hP hr) hs).mp he,
        mul_zero]
  rw [IsPrime.vanishingIdeal_zeroLocus P] at hvanish
  exact (hm.1.isPrime.mem_or_mem hvanish).elim hm.2 hnext
theorem points_le_sectionDegree {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hcurve : IsSectionCurve top f P) (T : LiftedChart top f)
    (hnext : genericRow (oldNext f) ∉ P) :
    (nextCutLocus f P).Finite ∧ ((nextCutLocus f P).ncard : ℚ) ≤ sectionDegree top f P := by
  let h : T.next ∈ restrictSupport GeometricX (lastExponents top) := T.next_box
  let l := monomialLift T.next h
  have hmap : (lastMap top) l = T.next := monomialMap_monomialLift _ _
  have hl : l ∉ sectionIdeal top f P := by
    intro hm
    change (lastMap top) l ∈ graphCurve f P at hm
    rw [hmap] at hm
    exact next_notMem_graphCurve hP T hnext hm
  let J := sectionIdeal top f P ⊔ Ideal.span {l}
  obtain ⟨hdim, hbound⟩ := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hcurve.1 hl (totalDegree_monomialLift_le_one _ _)
  change (affineHilbertPolynomial J).natDegree ≤ _ at hdim
  rw [hcurve.2] at hdim hbound
  have hzero : (affineHilbertPolynomial J).natDegree = 0 := Nat.eq_zero_of_le_zero hdim
  have hdeg : affineDegree J ≤ sectionDegree top f P := by
    rw [sectionDegree, affineDegree_of_natDegree_eq_zero hzero, affineDegree, hcurve.2]
    simpa [J] using hbound
  obtain ⟨hfinite, hcard⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) J hzero
  let m := fun x => monomialPoint (lastExponents top) (graphPoint f x)
  have hinj : Function.Injective m :=
    (monomialPoint_injective lastExponents_single).comp (graphPoint_injective f)
  have hsubset : m '' nextCutLocus f P ⊆ zeroLocus GeometricX J := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_zeroLocus_iff_le_ker_aeval.mpr
    apply sup_le
    · apply mem_zeroLocus_iff_le_ker_aeval.mp
      apply (monomialPoint_mem_zeroLocus_comap_iff lastExponents_single _ _).mpr
      exact zeroLocus_vanishingIdeal_le _ ⟨x, hx.1, rfl⟩
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker, aeval_monomialPoint, hmap]
      exact (eval_represents_iff T.next_represents
        (eval_factor_of_regular hP hx.1) hx.1.2).mpr hx.2
  refine ⟨(hfinite.subset hsubset).of_finite_image hinj.injOn, ?_⟩
  rw [← Set.ncard_image_of_injective _ hinj]
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard hsubset hfinite)).trans (hcard.trans hdeg)
end
end Low6966Leading_1_1
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1
noncomputable section
variable {top : Fin 16}
open Low6966Leading (graphBox liftedBox)
open K1_13_5_4 (InLiftedBox GeoRow)
open K1_13_5_4_2 (JetPoint fourCutIdeal pointIdeal pointLength downBody capBody)
open K1_13_5_4_2_4 (Exponent Downward cutIdeal downSupport capSupport mem_downSupport mem_capSupport
  latticeBody latticeBody_downSupport latticeBody_capSupport)
open Low6966Prices (taylorLength)
open MvPolynomial
open scoped BigOperators Pointwise
open K1_13_5_4_2_4 (mixed_eq_generic downSupport_downward capSupport_downward zero_mem_capSupport)
private theorem deformation_bound : K1_13_5_4_2_4.c1 :=
  K1_13_5_4_2_4_1.of_children K1_13_5_4_2_4_1_1.proof K1_13_5_4_2_4_1_2.proof
private theorem generic_degree : K1_13_5_4_2_4.c2 :=
  K1_13_5_4_2_4_2.of_children K1_13_5_4_2_4_2_1.proof K1_13_5_4_2_4_2_2.proof
    (K1_13_5_4_2_4_2_3.of_children K1_13_5_4_2_4_2_3_1.proof K1_13_5_4_2_4_2_3_2.proof)
theorem sparse_bound
    (F G E L : GeoRow 4) (hF : F ≠ 0) (hG : InLiftedBox G (graphBox top) 1)
    (hE : InLiftedBox E (liftedBox top (taylorLength + 1)) (taylorLength - 1))
    (hL : InLiftedBox L (lastBox top) taylorLength) (points : Finset JetPoint)
    (hpoints : ∀ y ∈ points, pointIdeal y ∈ (fourCutIdeal F G E L).minimalPrimes) :
    (↑(∑ y ∈ points, (pointLength (fourCutIdeal F G E L) y).toNat) : ℝ) ≤
      lastMixedVolume top (downBody F) := by
  classical
  let A : Fin 4 → Finset Exponent :=
    ![downSupport F, capSupport (graphBox top) 1,
      capSupport (liftedBox top (taylorLength + 1)) (taylorLength - 1),
      capSupport (lastBox top) taylorLength]
  let f : Fin 4 → GeoRow 4 := ![F, G, E, L]
  have hz : ∀ i, 0 ∈ A i := by
    intro i
    fin_cases i
    · obtain ⟨e, he⟩ := support_nonempty.mpr hF
      exact mem_downSupport.mpr ⟨e, he, fun _ => Nat.zero_le _⟩
    · exact zero_mem_capSupport _ _
    · exact zero_mem_capSupport _ _
    · exact zero_mem_capSupport _ _
  have hd : ∀ i, Downward (A i) := by
    intro i
    fin_cases i
    · exact downSupport_downward F
    · exact capSupport_downward _ _
    · exact capSupport_downward _ _
    · exact capSupport_downward _ _
  have hv (j : Fin 4) : ∃ i, Finsupp.single j 1 ∈ A i := by
    exact ⟨3, mem_capSupport.mpr (lastExponents_single j)⟩
  have hsup : ∀ i, (f i).support ⊆ A i := by
    intro i
    fin_cases i
    · exact fun a ha => mem_downSupport.mpr ⟨a, ha, le_rfl⟩
    · exact fun a ha => mem_capSupport.mpr (hG a ha)
    · exact fun a ha => mem_capSupport.mpr (hE a ha)
    · exact fun a ha => mem_capSupport.mpr (hL a ha)
  have hJ : cutIdeal f = fourCutIdeal F G E L := by
    unfold cutIdeal fourCutIdeal
    apply congrArg Ideal.span
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [f]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  obtain ⟨hfinite, hmv⟩ := mixed_eq_generic generic_degree K1_13_5_4_2_4_3.proof A hz hd hv
  have hbound := deformation_bound A hz hfinite f hsup points (by simpa only [hJ] using hpoints)
  have hbodies : (fun i => latticeBody (A i)) =
      ![downBody F, capBody (graphBox top) 1,
        capBody (liftedBox top (taylorLength + 1)) (taylorLength - 1), capBody (lastBox top) taylorLength] := by
    funext i
    fin_cases i
    · exact latticeBody_downSupport F
    · exact latticeBody_capSupport _ _ (show (graphBox top).j ≤ (graphBox top).b by fin_cases top <;> decide) (show 2 * (graphBox top).t ≤ (graphBox top).j by fin_cases top <;> decide)
    · exact latticeBody_capSupport _ _ (show (liftedBox top (taylorLength + 1)).j ≤ (liftedBox top (taylorLength + 1)).b by fin_cases top <;> decide)
        (show 2 * (liftedBox top (taylorLength + 1)).t ≤ (liftedBox top (taylorLength + 1)).j by fin_cases top <;> decide)
    · exact latticeBody_capSupport _ _ (show (lastBox top).j ≤ (lastBox top).b by fin_cases top <;> decide)
        (show 2 * (lastBox top).t ≤ (lastBox top).j by fin_cases top <;> decide)
  simpa only [hJ, hmv, hbodies, lastMixedVolume] using (Nat.cast_le (α := ℝ)).mpr hbound
end
end Low6966Leading_1_1
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1
noncomputable section
variable {top : Fin 16}
open K1_13 (Row Shape indexDegree)
open K1_13_5 (separant)
open Low6966Leading (lowBox liftedBox mixedCoefficients)
open K1_13_5_4 (InLiftedBox GeometricX GeoRow genericRow liftRow graphPoint regularLocus)
open K1_13_5_4_2 (graphLocus JetPoint eval_liftRow_graphPoint)
open Low6966Prices (taylorLength)
open Low6966Leading (SecondFactors)
open Low6966Leading_1 (LiftedChart reconstruct CoefficientIdeal)
open MvPolynomial
open scoped BigOperators Pointwise
open K1_13_5_4_2 (ratio_image_degree box_mono)
private theorem separator_box {n : ℕ} {f : Fin n → Row 3} (hf : SecondFactors top f)
    (i : Fin n) : InLiftedBox (liftRow (genericRow (separant (f i)))) (⟨Low6966Prices.lowerWidth top, Low6966Prices.lowerIndex top, Low6966Prices.lowerTop top⟩ : K1_13.Shape) 0 := by
  classical
  intro a ha
  rw [liftRow, support_rename_of_injective (Fin.castSucc_injective 3)] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  have hs : b ∈ (separant (f i)).support := support_map_subset _ _ hb
  let m : Fin 3 →₀ ℕ := b + Finsupp.single 2 1
  have hm : m ∈ (f i).support := by
    rw [MvPolynomial.mem_support_iff, separant, coeff_pderiv] at hs
    exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs)
  have hb₀ : m.degree ≤ (⟨Low6966Prices.lowerWidth top, Low6966Prices.lowerIndex top, Low6966Prices.lowerTop top⟩ : K1_13.Shape).b :=
    (le_totalDegree hm).trans ((Finset.single_le_sum (fun j _ => Nat.zero_le ((f j).totalDegree))
      (Finset.mem_univ i)).trans hf.total)
  have hj₀ : (m.sum fun j a => j.val * a) ≤ (⟨Low6966Prices.lowerWidth top, Low6966Prices.lowerIndex top, Low6966Prices.lowerTop top⟩ : K1_13.Shape).j :=
    (Finset.le_sup hm).trans ((Finset.single_le_sum (fun j _ => Nat.zero_le (indexDegree (f j)))
      (Finset.mem_univ i)).trans hf.index)
  have ht₀ : m 2 ≤ (⟨Low6966Prices.lowerWidth top, Low6966Prices.lowerIndex top, Low6966Prices.lowerTop top⟩ : K1_13.Shape).t :=
    (monomial_le_degreeOf 2 hm).trans ((Finset.single_le_sum
      (fun j _ => Nat.zero_le ((f j).degreeOf 2)) (Finset.mem_univ i)).trans hf.coordinate)
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hb₀
  rw [Finsupp.sum_fintype _ _ (fun j => mul_zero j.val), Fin.sum_univ_three] at hj₀
  have h0 : Finsupp.mapDomain Fin.castSucc b 0 = b 0 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 0
  have h1 : Finsupp.mapDomain Fin.castSucc b 1 = b 1 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 1
  have h2 : Finsupp.mapDomain Fin.castSucc b 2 = b 2 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 2
  have h3 : Finsupp.mapDomain Fin.castSucc b 3 = 0 :=
    Finsupp.mapDomain_of_notMem_range b _ (fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj)
  simp only [h0, h1, h2, h3, le_refl, and_true]
  simp [m, Finsupp.add_apply] at hb₀ hj₀ ht₀
  omega
private theorem pow_separator_box {n : ℕ} {f : Fin n → Row 3} (hf : SecondFactors top f)
    (i : Fin n) (r : ℕ) :
    InLiftedBox (liftRow (genericRow (separant (f i))) ^ r)
      ⟨Low6966Prices.lowerWidth top * r, Low6966Prices.lowerIndex top * r, Low6966Prices.lowerTop top * r⟩ 0 := by
  classical
  induction r with
  | zero =>
      simp only [pow_zero, InLiftedBox, support_one, Finset.mem_singleton]
      rintro a rfl
      simp
  | succ r ih =>
      intro a ha
      rw [pow_succ] at ha
      obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ ha)
      have ⟨hb₀, hb₁, hb₂, hb₃⟩ := ih b hb
      have ⟨hc₀, hc₁, hc₂, hc₃⟩ := separator_box hf i c hc
      simp only [Finsupp.add_apply, Nat.mul_succ] at *
      exact ⟨by omega, by omega, by omega, by omega⟩
theorem coefficient_image_degree {n : ℕ} {f : Fin n → Row 3} (hf : SecondFactors top f)
    (i : Fin n) (P : Ideal (GeoRow 3)) (T : LiftedChart top (f i))
    (hcurve : IsSectionCurve top (f i) P) (hone : 1 ≤ sectionDegree top (f i) P) :
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      affineDegree Q ≤ sectionDegree top (f i) P ∧
      ∀ y ∈ regularLocus (f i) P, reconstruct (f i) T.numerator y ∈ zeroLocus GeometricX Q := by
  let A := monomialPoint (lastExponents top) '' graphLocus (f i) P
  have hA : sectionIdeal top (f i) P = vanishingIdeal GeometricX A := by
    ext p
    constructor
    · intro hp
      rintro _ ⟨z, hz, rfl⟩
      rw [aeval_monomialPoint]
      exact hp z hz
    · intro hp z hz
      have he := hp _ ⟨z, hz, rfl⟩
      rwa [aeval_monomialPoint] at he
  obtain ⟨D, hD_eq⟩ : ∃ D : GeoRow 4,
      D = liftRow (genericRow (separant (f i))) ^ (taylorLength - 4) := ⟨_, rfl⟩
  have hD : D ∈ restrictSupport GeometricX (lastExponents top) := by
    have hbox : InLiftedBox D
        ⟨Low6966Prices.lowerWidth top * (taylorLength - 4), Low6966Prices.lowerIndex top * (taylorLength - 4), Low6966Prices.lowerTop top * (taylorLength - 4)⟩ 0 := by
      rw [hD_eq]
      exact pow_separator_box hf i (taylorLength - 4)
    change InLiftedBox D (lastBox top) taylorLength
    exact box_mono (show Low6966Prices.lowerWidth top * (taylorLength - 4) ≤ (lastBox top).b by fin_cases top <;> decide)
      (show Low6966Prices.lowerIndex top * (taylorLength - 4) ≤ (lastBox top).j by fin_cases top <;> decide) (show Low6966Prices.lowerTop top * (taylorLength - 4) ≤ (lastBox top).t by fin_cases top <;> decide)
      (Nat.zero_le _) hbox
  have hN (j : Fin taylorLength) : T.numerator j ∈ restrictSupport GeometricX (lastExponents top) := by
    change InLiftedBox (T.numerator j) (lastBox top) taylorLength
    exact box_mono (show (liftedBox top taylorLength).b ≤ (lastBox top).b by fin_cases top <;> decide)
      (show (liftedBox top taylorLength).j ≤ (lastBox top).j by fin_cases top <;> decide) (show (liftedBox top taylorLength).t ≤ (lastBox top).t by fin_cases top <;> decide)
      (Nat.sub_le _ _) (T.coefficient_box j)
  let d := monomialLift D hD
  let ν (j : Fin taylorLength) := monomialLift (T.numerator j) (hN j)
  have hdeval (z : JetPoint) : eval (monomialPoint (lastExponents top) z) d = eval z D := by
    have hmap : (lastMap top) d = D := monomialMap_monomialLift D hD
    simpa only [aeval_eq_eval, hmap] using aeval_monomialPoint z d
  have hνeval (z : JetPoint) (j : Fin taylorLength) :
      eval (monomialPoint (lastExponents top) z) (ν j) = eval z (T.numerator j) := by
    have hmap : (lastMap top) (ν j) = T.numerator j := monomialMap_monomialLift _ _
    simpa only [aeval_eq_eval, hmap] using aeval_monomialPoint z (ν j)
  have hden (z) (hz : z ∈ A) : eval z d ≠ 0 := by
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    rw [hdeval, hD_eq, map_pow, eval_liftRow_graphPoint]
    exact pow_ne_zero _ hx.2
  obtain ⟨Q, hp, hd, hb, hz⟩ := ratio_image_degree A _ hA hcurve.1 hcurve.2 hone d ν
    (totalDegree_monomialLift_le_one _ _) (fun j => totalDegree_monomialLift_le_one _ _) hden
  refine ⟨Q, hp, hd, hb, fun x hx => ?_⟩
  have hz' := hz (monomialPoint (lastExponents top) (graphPoint (f i) x)) ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  unfold reconstruct
  simpa only [hνeval, hdeval, hD_eq, map_pow, eval_liftRow_graphPoint] using hz'
end
end Low6966Leading_1_1
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1
noncomputable section
variable {top : Fin 16}
open K1_13 (Row)
open K1_13_5_4 (GeoRow genericRow liftRow graph)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve fourCutIdeal pointIdeal pointLength downBody
  localLength_lt_top)
open Low6966Leading (SecondFactors mixedBudget)
open Low6966Leading_1 (LiftedChart CurveIndex properComponents componentLength)
open MvPolynomial
open scoped BigOperators
open K1_13_5_4_2 (lift_generic_ne_zero)
def c1 (top : Fin 16) : Prop :=
  ∀ (f : Row 3), (∀ P ∈ factorCurves f, IsSectionCurve top f P) →
    Nonempty (GenericSection top f)
def c2 (top : Fin 16) : Prop :=
  ∀ (f : Row 3), Irreducible f → 0 < f.degreeOf 2 → ∀ (T : LiftedChart top f) (L : GeoRow 4),
    (∀ P ∈ factorCurves f, L ∉ graphCurve f P) →
    ∀ P ∈ factorCurves f, ∀ y ∈ graphLocus f P, eval y L = 0 →
      let J := fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut L
      pointIdeal y ∈ J.minimalPrimes ∧ componentLength f P ≤ pointLength J y
def c3 (top : Fin 16) : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors top f →
    (∑ i, lastMixedVolume top (downBody (liftRow (genericRow (f i))))) ≤ (mixedBudget top : ℝ)
private theorem section_cost (hlocal : c2 top) {f : Row 3}
    (hf : Irreducible f) (hpos : 0 < f.degreeOf 2) (T : LiftedChart top f) (S : GenericSection top f) :
    (↑(∑ P ∈ factorCurves f, (componentLength f P).toNat * (S.points P).card) : ℝ) ≤
      lastMixedVolume top (downBody (liftRow (genericRow f))) := by
  classical
  let J := fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut S.polynomial
  let points := (factorCurves f).biUnion S.points
  have hlocal' (P) (hP : P ∈ factorCurves f) (y) (hy : y ∈ S.points P) :
      pointIdeal y ∈ J.minimalPrimes ∧ componentLength f P ≤ pointLength J y :=
    hlocal f hf hpos T S.polynomial S.proper P hP y (S.roots P hP y hy).1
      (S.roots P hP y hy).2
  have hmin : ∀ y ∈ points, pointIdeal y ∈ J.minimalPrimes := by
    intro y hy
    obtain ⟨P, hP, hyP⟩ := Finset.mem_biUnion.mp hy
    exact (hlocal' P hP y hyP).1
  have hd : Set.PairwiseDisjoint (↑(factorCurves f)) S.points := by
    intro P hP P' hP' hne
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    exact S.off_other_curves P hP P' hP' hne y hy (S.roots P' hP' y hy').1
  have hcost : (∑ P ∈ factorCurves f, (componentLength f P).toNat * (S.points P).card) ≤
      ∑ y ∈ points, (pointLength J y).toNat := by
    change _ ≤ ∑ y ∈ (factorCurves f).biUnion S.points, (pointLength J y).toNat
    rw [Finset.sum_biUnion hd]
    apply Finset.sum_le_sum
    intro P hP
    calc
      _ = ∑ _ ∈ S.points P, (componentLength f P).toNat := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro y hy
        exact ENat.toNat_le_toNat (hlocal' P hP y hy).2 (localLength_lt_top (hmin y
          (Finset.mem_biUnion.mpr ⟨P, hP, hy⟩))).ne
  exact (Nat.cast_le.mpr hcost).trans
    (sparse_bound _ _ _ _ (lift_generic_ne_zero hf.ne_zero) T.graph_box T.cut_box S.support points hmin)
theorem of_children (h1 : c1 top) (h2 : c2 top) (h3 : c3 top) : Low6966Leading_1.c1 top := by
  classical
  intro n f hf T
  have hcurve (i : Fin n) (P) (hP : P ∈ factorCurves (f i)) : IsSectionCurve top (f i) P :=
    section_curve (hf.irreducible i) hP
  let S (i : Fin n) := Classical.choice (h1 (f i) (hcurve i))
  let e : CurveIndex n → ℕ := fun a => (componentLength (f a.1) a.2).toNat
  let d : CurveIndex n → ℕ := fun a => ((S a.1).points a.2).card
  have hdeg (a : CurveIndex n) (ha : a ∈ properComponents f) :
      (d a : ℚ) = sectionDegree top (f a.1) a.2 :=
    (S a.1).card_eq a.2 (mem_properComponents.mp ha)
  refine ⟨⟨e, d, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun _ ha => componentLength_toNat (mem_properComponents.mp ha)
  · exact fun _ ha => componentLength_toNat_pos (mem_properComponents.mp ha)
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [sum_properComponents, Nat.cast_sum]
    exact (Finset.sum_le_sum fun i _ =>
      section_cost h2 (hf.irreducible i) (hf.positive i) (T i) (S i)).trans (h3 n f hf)
  · intro a ha hn
    have hp := mem_properComponents.mp ha
    obtain ⟨hfin, hcard⟩ := points_le_sectionDegree hp (hcurve _ _ hp) (T a.1) hn
    exact ⟨hfin, Nat.cast_le.mp (hcard.trans_eq (hdeg a ha).symm)⟩
  · intro a ha _
    have hp := mem_properComponents.mp ha
    have hC := hcurve _ _ hp
    have hpos : 0 < d a := by
      have h : (0 : ℚ) < (d a : ℚ) := by
        rw [hdeg a ha]
        exact affineDegree_pos hC.1.ne_top
      exact_mod_cast h
    have hone : 1 ≤ sectionDegree top (f a.1) a.2 := by
      rw [← hdeg a ha]
      exact_mod_cast (Nat.succ_le_of_lt hpos)
    obtain ⟨Q, hprime, hdim, hb, hrec⟩ := coefficient_image_degree hf a.1 a.2 (T a.1) hC hone
    exact ⟨Q, hprime, hdim, hpos, hb.trans_eq (hdeg a ha).symm, hrec⟩
end
end Low6966Leading_1_1
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1_1
noncomputable section
variable {top : Fin 16}
open K1_13 (Row)
open K1_13_5 (separant lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow regularLocus graph graphPoint)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve eval_liftRow_graphPoint eval_graph_graphPoint)
open Low6966Leading_1 (oldCutIdeal)
open Low6966Leading_1_1 (factorCurves mem_factorCurves lastExponents lastExponents_single lastMap
  sectionIdeal IsSectionCurve)
open MvPolynomial
open K1_13_5_4_2 (three_ne_zero)
open K1_13_5_4_2_3 (graphCurve_comap)
abbrev EmbeddedPoint (top : Fin 16) := (lastExponents top) → GeometricX
def jetOfEmbedded (top : Fin 16) (z : (EmbeddedPoint top)) : JetPoint :=
  fun i => z ⟨Finsupp.single i 1, lastExponents_single i⟩
private theorem jetOf_monomialPoint (y : JetPoint) :
    jetOfEmbedded top (monomialPoint (lastExponents top) y) = y :=
  funext fun i => monomialPoint_single y (lastExponents_single i)
theorem monomialPoint_jetOf {f : Row 3} {P : Ideal (GeoRow 3)} {z : (EmbeddedPoint top)}
    (hz : z ∈ zeroLocus GeometricX (sectionIdeal top f P)) :
    monomialPoint (lastExponents top) (jetOfEmbedded top z) = z := by
  obtain ⟨y, hy⟩ := exists_monomialPoint_eq_of_mem_zeroLocus_ker lastExponents_single
    (zeroLocus_anti_mono (show RingHom.ker (lastMap top) ≤ sectionIdeal top f P from
      fun q hq => show (lastMap top) q ∈ graphCurve f P from
        (RingHom.mem_ker.mp hq).symm ▸ (graphCurve f P).zero_mem) hz)
  rw [← hy, jetOf_monomialPoint]
private theorem jetOf_mem_closure {f : Row 3} {P : Ideal (GeoRow 3)} {z : (EmbeddedPoint top)}
    (hz : z ∈ zeroLocus GeometricX (sectionIdeal top f P)) :
    jetOfEmbedded top z ∈ zeroLocus GeometricX (graphCurve f P) := by
  apply (monomialPoint_mem_zeroLocus_comap_iff lastExponents_single _ _).mp
  rw [monomialPoint_jetOf hz]
  exact hz
private theorem retained {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    P ∈ (oldCutIdeal f).minimalPrimes ∧ genericRow (separant f) ∉ P :=
  Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
private theorem lift_mem_graphCurve_iff {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (g : GeoRow 3) :
    liftRow g ∈ graphCurve f P ↔ g ∈ P := by
  let : P.IsPrime := (retained hP).1.isPrime
  change g ∈ (graphCurve f P).comap (rename Fin.castSucc).toRingHom ↔ g ∈ P
  rw [graphCurve_comap (retained hP).2]
private theorem mem_graphLocus_of_mem_closure {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) {y : JetPoint}
    (hy : y ∈ zeroLocus GeometricX (graphCurve f P))
    (hs : eval y (liftRow (genericRow (separant f))) ≠ 0) :
    y ∈ graphLocus f P := by
  let x : Fin 3 → GeometricX := y ∘ Fin.castSucc
  have hs' : eval x (genericRow (separant f)) ≠ 0 := by
    simpa only [liftRow, eval_rename, x] using hs
  have hx : x ∈ regularLocus f P := by
    refine ⟨fun g hg => ?_, hs'⟩
    have h := hy (liftRow g) ((lift_mem_graphCurve_iff hP g).mpr hg)
    simpa only [aeval_eq_eval, liftRow, eval_rename, x] using h
  have hvan : graph f ∈ graphCurve f P := by
    rintro _ ⟨w, hw, rfl⟩
    exact eval_graph_graphPoint hw.2
  have h := hy (graph f) hvan
  simp only [aeval_eq_eval, graph, map_add, map_mul, map_ofNat, eval_X, liftRow,
    eval_rename] at h
  change eval x (genericRow (lowerTangent f)) +
    3 * y 3 * eval x (genericRow (separant f)) = 0 at h
  refine ⟨x, hx, ?_⟩
  funext i
  refine Fin.lastCases ?_ (fun j => Fin.snoc_castSucc _ _ j) i
  rw [graphPoint, Fin.snoc_last, div_eq_iff (mul_ne_zero K1_13_5_4_2.three_ne_zero hs')]
  change -eval x (genericRow (lowerTangent f)) =
    y 3 * (3 * eval x (genericRow (separant f)))
  linear_combination -h
private theorem finite_cut {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : IsSectionCurve top f P) {g : GeoRow 4} (hg : g ∉ graphCurve f P) :
    {z | z ∈ zeroLocus GeometricX (sectionIdeal top f P) ∧
      eval (jetOfEmbedded top z) g = 0}.Finite := by
  obtain ⟨G, hG⟩ := monomialMap_surjective lastExponents_single g
  have hnot : G ∉ sectionIdeal top f P := by
    change (lastMap top) G ∉ graphCurve f P
    rwa [hG]
  obtain ⟨hdim, _⟩ :=
    principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hP.1 hnot (b := G.totalDegree) le_rfl
  rw [hP.2] at hdim
  have hn := Nat.eq_zero_of_le_zero hdim
  refine ((finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) _ hn).1).subset ?_
  intro z hz
  apply mem_zeroLocus_sup_span_singleton_iff.mpr
  refine ⟨hz.1, ?_⟩
  rw [← monomialPoint_jetOf hz.1, aeval_monomialPoint, hG, aeval_eq_eval]
  exact hz.2
private theorem finite_boundary {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hC : IsSectionCurve top f P) :
    {z | z ∈ zeroLocus GeometricX (sectionIdeal top f P) ∧
      jetOfEmbedded top z ∉ graphLocus f P}.Finite := by
  have hsep : liftRow (genericRow (separant f)) ∉ graphCurve f P :=
    fun h => (retained hP).2 ((lift_mem_graphCurve_iff hP _).mp h)
  refine (finite_cut hC hsep).subset ?_
  intro z hz
  exact ⟨hz.1, not_ne_iff.mp fun hs =>
    hz.2 (mem_graphLocus_of_mem_closure hP (jetOf_mem_closure hz.1) hs)⟩
private theorem finite_overlap {f : Row 3} {P Q : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hQ : Q ∈ factorCurves f) (hne : P ≠ Q)
    (hC : IsSectionCurve top f P) :
    {z | z ∈ zeroLocus GeometricX (sectionIdeal top f P) ∧
      jetOfEmbedded top z ∈ graphLocus f Q}.Finite := by
  have h : ¬ Q ≤ P := Ideal.not_le_of_mem_minimalPrimes (retained hQ).1 (retained hP).1 hne.symm
  obtain ⟨g, hgQ, hgP⟩ : ∃ g, g ∈ Q ∧ g ∉ P := by
    by_contra! hbad
    exact h hbad
  refine (finite_cut hC (fun hg => hgP ((lift_mem_graphCurve_iff hP _).mp hg))).subset ?_
  intro z hz
  refine ⟨hz.1, ?_⟩
  obtain ⟨x, hx, he⟩ := hz.2
  rw [← he, eval_liftRow_graphPoint]
  exact hx.1 g hgQ
theorem exists_excluded_points {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hC : IsSectionCurve top f P) :
    ∃ B : Finset (EmbeddedPoint top),
      ∀ z ∈ zeroLocus GeometricX (sectionIdeal top f P), z ∉ B →
        jetOfEmbedded top z ∈ graphLocus f P ∧
        ∀ Q ∈ factorCurves f, P ≠ Q → jetOfEmbedded top z ∉ graphLocus f Q := by
  classical
  let boundary := (finite_boundary hP hC).toFinset
  let overlap (Q : (factorCurves f).erase P) :=
    (finite_overlap hP (Finset.mem_of_mem_erase Q.property)
      (Finset.ne_of_mem_erase Q.property).symm hC).toFinset
  refine ⟨boundary ∪ Finset.univ.biUnion overlap, ?_⟩
  intro z hz hB
  constructor
  · by_contra hn
    apply hB
    exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr ⟨hz, hn⟩)
  · intro Q hQ hne hmeet
    let q : (factorCurves f).erase P := ⟨Q, Finset.mem_erase.mpr ⟨hne.symm, hQ⟩⟩
    apply hB
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q, Finset.mem_univ _, (Set.Finite.mem_toFinset _).mpr ⟨hz, hmeet⟩⟩)
end
end Low6966Leading_1_1_1
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1_1
noncomputable section
variable {top : Fin 16}
open K1_13_5_4 (GeoRow GeometricX InLiftedBox)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve)
open K1_13_5_4_2_2 (linearForm fiberIdeal totalDegree_hyperplane_le_one zeroLocus_fiber_iff
  ncard_eq_affineDegree_of_radical)
open Low6966Prices (taylorLength)
open Low6966Leading_1_1 (factorCurves lastBox lastExponents lastMap sectionIdeal sectionDegree)
open MvPolynomial
open scoped Pointwise
private theorem hyperplane_support (a : (EmbeddedPoint top)) (t : GeometricX) :
    InLiftedBox ((lastMap top) (linearForm a - MvPolynomial.C t)) (lastBox top) taylorLength := by
  have hz : (0 : Fin 4 →₀ ℕ) ∈ (lastExponents top) := by
    change 0 + 0 + 0 ≤ (lastBox top).b ∧ 0 + 2 * 0 ≤ (lastBox top).j ∧ 0 ≤ (lastBox top).t ∧ 0 ≤ taylorLength
    simp
  have h := monomialMap_mem_restrictSupport_nsmul hz (totalDegree_hyperplane_le_one a t)
  rw [one_nsmul] at h
  exact h
theorem proof : Low6966Leading_1_1.c1 top := by
  classical
  intro f hC
  have h1 := K1_13_5_4_2_2_1.proof
  have h2 := K1_13_5_4_2_2_2.proof
  have h3 := K1_13_5_4_2_2_3.proof
  let I (P : factorCurves f) := sectionIdeal top f P.val
  obtain ⟨degreeBad, hdegreeBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    h1 GeometricX (lastExponents top) (I P) (hC P.val P.property).1 (hC P.val P.property).2
  obtain ⟨separationBad, hseparationBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    h2 GeometricX (lastExponents top) (I P) (hC P.val P.property).1 (hC P.val P.property).2
  let bad := Finset.univ.biUnion fun P => insert (separationBad P) (degreeBad P)
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun V : bad => V.val) (by
      intro V
      obtain ⟨P, _, hV⟩ := Finset.mem_biUnion.mp V.property
      rcases Finset.mem_insert.mp hV with h | h
      · rw [h]
        exact (hseparationBad P).1
      · exact (hdegreeBad P).1 _ h)
  have havoid (P : factorCurves f) (V : Submodule GeometricX (EmbeddedPoint top))
      (hV : V ∈ insert (separationBad P) (degreeBad P)) : a ∉ V :=
    ha ⟨V, Finset.mem_biUnion.mpr ⟨P, Finset.mem_univ _, hV⟩⟩
  have hdegree (P : factorCurves f) :=
    (hdegreeBad P).2 a (fun V hV => havoid P V (Finset.mem_insert_of_mem hV))
  obtain ⟨valueBad, hvalueBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    h3 GeometricX (lastExponents top) (I P) (hC P.val P.property).1 a (hdegree P).1
      ((hseparationBad P).2 a (havoid P _ (Finset.mem_insert_self _ _)))
  obtain ⟨pointsBad, hpointsBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    exists_excluded_points P.property (hC P.val P.property)
  let value (z : (EmbeddedPoint top)) := aeval z (linearForm a)
  let excludedValues := Finset.univ.biUnion fun P => valueBad P ∪ (pointsBad P).image value
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset excludedValues
  have hmiss (P : factorCurves f) : t ∉ valueBad P ∪ (pointsBad P).image value :=
    fun h => ht (Finset.mem_biUnion.mpr ⟨P, Finset.mem_univ _, h⟩)
  let L := linearForm a - MvPolynomial.C t
  let J (P : Ideal (GeoRow 3)) := fiberIdeal (sectionIdeal top f P) a t
  have hcut (P) (hP : P ∈ factorCurves f) :
      (affineHilbertPolynomial (J P)).natDegree = 0 ∧
        affineDegree (J P) = sectionDegree top f P :=
    (hdegree ⟨P, hP⟩).2 t
  have hproper (P) (hP : P ∈ factorCurves f) : (lastMap top) L ∉ graphCurve f P := by
    intro hmem
    have hL : L ∈ sectionIdeal top f P := hmem
    have heq : J P = sectionIdeal top f P :=
      sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hL)
    have hz := (hcut P hP).1
    rw [heq, (hC P hP).2] at hz
    omega
  have hfinite (P) (hP : P ∈ factorCurves f) : (zeroLocus GeometricX (J P)).Finite :=
    (finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) _ (hcut P hP).1).1
  let points (P : Ideal (GeoRow 3)) : Finset JetPoint :=
    if hP : P ∈ factorCurves f then (hfinite P hP).toFinset.image (jetOfEmbedded top) else ∅
  have hg (P) (hP : P ∈ factorCurves f) {z : (EmbeddedPoint top)}
      (hz : z ∈ zeroLocus GeometricX (J P)) :
      jetOfEmbedded top z ∈ graphLocus f P ∧
      (∀ Q ∈ factorCurves f, P ≠ Q → jetOfEmbedded top z ∉ graphLocus f Q) := by
    obtain ⟨hzC, hzt⟩ := zeroLocus_fiber_iff.mp hz
    apply hpointsBad ⟨P, hP⟩ z hzC
    intro hbad
    exact hmiss ⟨P, hP⟩ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨z, hbad, hzt⟩))
  have hpoint (P) (hP : P ∈ factorCurves f) (y) (hy : y ∈ points P) :
      ∃ z ∈ zeroLocus GeometricX (J P), jetOfEmbedded top z = y := by
    simp only [points, dite_eq_left hP] at hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨z, (Set.Finite.mem_toFinset _).mp hz, rfl⟩
  refine ⟨⟨(lastMap top) L, hyperplane_support a t, points, ?_, hproper, ?_, ?_⟩⟩
  · intro P hP
    have hrad := hvalueBad ⟨P, hP⟩ t (fun ht' => hmiss ⟨P, hP⟩ (Finset.mem_union_left _ ht'))
    have hinj : Set.InjOn (jetOfEmbedded top) (zeroLocus GeometricX (J P)) := by
      intro x hx y hy hxy
      rw [← monomialPoint_jetOf (zeroLocus_fiber_iff.mp hx).1,
        ← monomialPoint_jetOf (zeroLocus_fiber_iff.mp hy).1, hxy]
    simp only [points, dite_eq_left hP]
    rw [Finset.card_image_of_injOn (by simpa using hinj),
      ← Set.ncard_eq_toFinset_card _ (hfinite P hP)]
    exact (ncard_eq_affineDegree_of_radical (J P) (hcut P hP).1 hrad).trans (hcut P hP).2
  · intro P hP y hy
    obtain ⟨z, hz, rfl⟩ := hpoint P hP y hy
    have hzC := (zeroLocus_fiber_iff.mp hz).1
    refine ⟨(hg P hP hz).1, ?_⟩
    have hev := (mem_zeroLocus_sup_span_singleton_iff.mp hz).2
    rw [← monomialPoint_jetOf hzC, aeval_monomialPoint, aeval_eq_eval] at hev
    exact hev
  · intro P hP Q hQ hne y hy
    obtain ⟨z, hz, rfl⟩ := hpoint P hP y hy
    exact (hg P hP hz).2 Q hQ hne
end
end Low6966Leading_1_1_1
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1_2
noncomputable section
variable {top : Fin 16}
open K1_13 (Row)
open K1_13_5 (lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow graph graphIdeal)
open Low6966Leading_1 (LiftedChart oldCutIdeal)
open K1_13_5_4_2_3 (OpenRing onOpen onOpen_kills onOpen_isUnit onOpen_hom_ext
  openLift openLift_onOpen sep liftedSep)
open MvPolynomial
open K1_13_5_4_2_3 (three_isUnit graph_coord_unique represents_vanish)
def threeCut (f : Row 3) (T : LiftedChart top f) : Ideal (GeoRow 4) :=
  graphIdeal f ⊔ Ideal.span {T.cut}
abbrev OldOpen (f : Row 3) := OpenRing (oldCutIdeal f) (sep f)
abbrev GraphOpen (f : Row 3) (T : LiftedChart top f) := OpenRing (threeCut f T) (liftedSep f)
abbrev oldMap (f : Row 3) := onOpen (oldCutIdeal f) (sep f)
abbrev graphMap (f : Row 3) (T : LiftedChart top f) := onOpen (threeCut f T) (liftedSep f)
private def newJet (f : Row 3) : OldOpen f :=
  -oldMap f (genericRow (lowerTangent f)) *
    ↑(((three_isUnit ((oldMap f).comp C)).mul (onOpen_isUnit (oldCutIdeal f) (sep f))).unit⁻¹)
private theorem newJet_eq (f : Row 3) :
    oldMap f (genericRow (lowerTangent f)) + 3 * newJet f * oldMap f (sep f) = 0 := by
  let a := oldMap f (genericRow (lowerTangent f))
  let s := oldMap f (sep f)
  let u := ((three_isUnit ((oldMap f).comp C)).mul (onOpen_isUnit (oldCutIdeal f) (sep f))).unit
  have hu : (u : OldOpen f) = 3 * s := IsUnit.unit_spec _
  change a + 3 * (-a * (↑u⁻¹ : OldOpen f)) * s = 0
  calc
    _ = a + -a * ((↑u⁻¹ : OldOpen f) * (u : OldOpen f)) := by rw [hu]; ring
    _ = 0 := by simp
private def substitute (f : Row 3) : GeoRow 4 →+* OldOpen f :=
  eval₂Hom ((oldMap f).comp C) (Fin.snoc (fun i => oldMap f (MvPolynomial.X i)) (newJet f))
@[simp] private theorem substitute_lift (f : Row 3) (p : GeoRow 3) :
    substitute f (liftRow p) = oldMap f p := by
  rw [substitute, liftRow, eval₂Hom_rename, Fin.snoc_comp_castSucc]
  have h : eval₂Hom ((oldMap f).comp C) (fun i : Fin 3 => oldMap f (MvPolynomial.X i)) = oldMap f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp
  rw [h]
private theorem substitute_last (f : Row 3) :
    substitute f (MvPolynomial.X (Fin.last 3)) = newJet f := by
  rw [substitute, eval₂Hom_X']
  exact Fin.snoc_last _ _
private theorem substitute_graph (f : Row 3) : substitute f (graph f) = 0 := by
  rw [graph, map_add, map_mul, map_mul, map_ofNat, substitute_lift, substitute_lift,
    show (3 : Fin 4) = Fin.last 3 from rfl, substitute_last]
  exact newJet_eq f
private theorem substitute_kills (f : Row 3) (T : LiftedChart top f) :
    threeCut f T ≤ RingHom.ker (substitute f) := by
  have hG : graphIdeal f ≤ RingHom.ker (substitute f) := by
    rw [graphIdeal, Ideal.span_insert, sup_le_iff, Ideal.span_singleton_le_iff_mem,
      Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, RingHom.mem_ker]
    refine ⟨?_, substitute_graph f⟩
    rw [substitute_lift]
    exact onOpen_kills (Ideal.subset_span (by simp))
  have hs : IsUnit (substitute f (liftedSep f)) := by
    rw [substitute_lift]
    exact onOpen_isUnit _ _
  refine sup_le hG ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr ?_))
  apply (represents_vanish T.cut_represents _ hG hs).mpr
  rw [substitute_lift]
  exact onOpen_kills (Ideal.subset_span (by simp))
private def graphToOld (f : Row 3) (T : LiftedChart top f) : GraphOpen f T →+* OldOpen f :=
  openLift _ _ (substitute f) (substitute_kills f T)
    (by rw [substitute_lift]; exact onOpen_isUnit _ _)
private theorem graphToOld_on (f : Row 3) (T : LiftedChart top f) (b : GeoRow 4) :
    graphToOld f T (graphMap f T b) = substitute f b := by
  rw [graphToOld, openLift_onOpen]
private theorem oldToGraph_kills (f : Row 3) (T : LiftedChart top f) :
    oldCutIdeal f ≤ RingHom.ker ((graphMap f T).comp (rename Fin.castSucc).toRingHom) := by
  let b := (graphMap f T).comp (rename Fin.castSucc).toRingHom
  have hG : graphIdeal f ≤ RingHom.ker (graphMap f T) := fun u hu =>
    RingHom.mem_ker.mpr (onOpen_kills (show u ∈ threeCut f T from Ideal.mem_sup_left hu))
  change oldCutIdeal f ≤ RingHom.ker b
  rw [oldCutIdeal, Ideal.span_insert, sup_le_iff]
  rw [Ideal.span_singleton_le_iff_mem, Ideal.span_singleton_le_iff_mem]
  refine ⟨hG (show liftRow (genericRow f) ∈ graphIdeal f from
    Ideal.subset_span (by simp)), RingHom.mem_ker.mpr ?_⟩
  exact (represents_vanish T.cut_represents _ hG (onOpen_isUnit _ _)).mp
    (onOpen_kills (show T.cut ∈ threeCut f T from
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
private def oldToGraph (f : Row 3) (T : LiftedChart top f) : OldOpen f →+* GraphOpen f T :=
  openLift _ _ ((graphMap f T).comp (rename Fin.castSucc).toRingHom)
    (oldToGraph_kills f T) (onOpen_isUnit (threeCut f T) (liftedSep f))
@[simp] private theorem oldToGraph_on (f : Row 3) (T : LiftedChart top f) (a : GeoRow 3) :
    oldToGraph f T (oldMap f a) = graphMap f T (liftRow a) :=
  openLift_onOpen _ _ ((graphMap f T).comp (rename Fin.castSucc).toRingHom)
    (oldToGraph_kills f T) (onOpen_isUnit (threeCut f T) (liftedSep f)) a
def graphEquiv (f : Row 3) (T : LiftedChart top f) : OldOpen f ≃+* GraphOpen f T := by
  refine RingEquiv.ofRingHom (oldToGraph f T) (graphToOld f T) ?_ ?_
  · apply onOpen_hom_ext
    have hcomp : (graphToOld f T).comp (graphMap f T) = substitute f :=
      RingHom.ext (graphToOld_on f T)
    rw [RingHom.comp_assoc, RingHom.id_comp, hcomp]
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [substitute, liftRow]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hG : graphMap f T (graph f) = 0 :=
          onOpen_kills (Ideal.mem_sup_left (Ideal.subset_span (by simp)))
        have he := DFunLike.congr_arg (oldToGraph f T) (newJet_eq f)
        rw [map_add, map_mul, map_mul, map_ofNat, map_zero, oldToGraph_on, oldToGraph_on] at he
        have h := graph_coord_unique f (graphMap f T) (onOpen_isUnit _ _) hG he
        rw [RingHom.comp_apply, substitute_last]
        exact h.symm
      · simp [substitute, liftRow]
  · apply onOpen_hom_ext
    apply RingHom.ext
    intro a
    simp [graphToOld_on]
@[simp] theorem graphEquiv_on (f : Row 3) (T : LiftedChart top f) (a : GeoRow 3) :
    graphEquiv f T (oldMap f a) = graphMap f T (liftRow a) :=
  oldToGraph_on f T a
end
end Low6966Leading_1_1_2
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1_2
noncomputable section
variable {top : Fin 16}
open K1_13 (Row)
open K1_13_5_4 (GeoRow GeometricX genericRow regularLocus liftRow graph graphIdeal graphPoint)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve fourCutIdeal pointIdeal
  eval_liftRow_graphPoint eval_graph_graphPoint eval_represents_iff)
open K1_13_5_4_2_3 (sep liftedSep openLift openLift_onOpen onOpen_kills
  length_atPrime_le_length_principalCut)
open Low6966Leading_1 (LiftedChart componentLength oldCutIdeal)
open Low6966Leading_1_1 (factorCurves mem_factorCurves)
open MvPolynomial
open K1_13_5_4_2_1 (graph_dimension)
open K1_13_5_4_2_3 (graphCurve_comap graphCurve_le_point sep_notMem_point)
open Low6966Leading_1_1 (retained_dimension)
open K1_13_5_4_2_3_1 (mem_iff_vanishes_regular)
open K1_13_5_4_2_3_2 (exists_open_prime openAtPrimeEquivQuotient colength_eq_of_quotient_equiv)
private theorem threeCut_le_graphCurve {f : Row 3} (T : LiftedChart top f)
    {P : Ideal (GeoRow 3)} (hP : oldCutIdeal f ≤ P) :
    threeCut f T ≤ graphCurve f P := by
  have hf (x : Fin 3 → GeometricX) (hx : x ∈ regularLocus f P) :
      eval x (genericRow f) = 0 :=
    hx.1 _ (hP (Ideal.subset_span (by simp)))
  apply sup_le
  · apply Ideal.span_le.mpr
    intro u hu y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · simpa only [aeval_eq_eval, eval_liftRow_graphPoint] using hf x hx
    · exact eval_graph_graphPoint hx.2
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (eval_represents_iff T.cut_represents (hf x hx) hx.2).mpr
      (hx.1 _ (hP (Ideal.subset_span (by simp))))
private theorem prime_of_chart {f : Row 3} (T : LiftedChart top f)
    (Q : Ideal (GeoRow 4)) [Q.IsPrime] (hcut : threeCut f T ≤ Q) (hsep : liftedSep f ∉ Q) :
    let P := Q.comap (rename Fin.castSucc).toRingHom
    oldCutIdeal f ≤ P ∧ graphCurve f P = Q := by
  let P := Q.comap (rename Fin.castSucc).toRingHom
  let : P.IsPrime := Ideal.comap_isPrime _ Q
  let F := FractionRing (GeoRow 4 ⧸ Q)
  let q : GeoRow 4 →+* F := (algebraMap (GeoRow 4 ⧸ Q) F).comp (Ideal.Quotient.mk Q)
  have hq (b : GeoRow 4) : q b = 0 ↔ b ∈ Q := by
    change algebraMap (GeoRow 4 ⧸ Q) F (Ideal.Quotient.mk Q b) = 0 ↔ b ∈ Q
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hsq : q (liftedSep f) ≠ 0 := fun h => hsep ((hq _).mp h)
  let qOpen := openLift (threeCut f T) (liftedSep f) q
    (fun b hb => RingHom.mem_ker.mpr ((hq b).mpr (hcut hb))) (isUnit_iff_ne_zero.mpr hsq)
  have hqOpen (b : GeoRow 4) : qOpen (graphMap f T b) = q b := openLift_onOpen _ _ _ _ _ b
  have hP : oldCutIdeal f ≤ P := by
    intro a ha
    change liftRow a ∈ Q
    apply (hq _).mp
    rw [← hqOpen, ← graphEquiv_on, onOpen_kills ha, map_zero, map_zero]
  refine ⟨hP, ?_⟩
  apply SetLike.ext
  intro b
  let e := graphEquiv f T
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (oldCutIdeal f) (sep f)) (e.symm (graphMap f T b))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  change e.symm (graphMap f T b) * oldMap f (sep f) ^ n = oldMap f a at hc
  have hab : graphMap f T b * graphMap f T (liftedSep f) ^ n = graphMap f T (liftRow a) := by
    simpa only [e, map_mul, map_pow, RingEquiv.apply_symm_apply, graphEquiv_on] using congrArg e hc
  have hfrac := congrArg qOpen hab
  simp only [map_mul, map_pow, hqOpen] at hfrac
  have hQmem : b ∈ Q ↔ a ∈ P := by
    change b ∈ Q ↔ liftRow a ∈ Q
    rw [← hq b, ← hq (liftRow a), ← hfrac, mul_eq_zero]
    simp only [pow_ne_zero n hsq, or_false]
  have hpoint (x : Fin 3 → GeometricX) (hx : x ∈ regularLocus f P) :
      eval (graphPoint f x) b * eval x (sep f) ^ n = eval x a := by
    have hs : eval (graphPoint f x) (liftedSep f) ≠ 0 := by
      rw [eval_liftRow_graphPoint]
      exact hx.2
    have hkill : threeCut f T ≤ RingHom.ker (eval (graphPoint f x)) := by
      intro g hg
      exact RingHom.mem_ker.mpr (threeCut_le_graphCurve T hP hg _ ⟨x, hx, rfl⟩)
    let w := openLift (threeCut f T) (liftedSep f) (eval (graphPoint f x)) hkill
      (isUnit_iff_ne_zero.mpr hs)
    have hw (g : GeoRow 4) : w (graphMap f T g) = eval (graphPoint f x) g :=
      openLift_onOpen _ _ _ _ _ g
    simpa only [map_mul, map_pow, hw, eval_liftRow_graphPoint] using congrArg w hab
  rw [hQmem, mem_iff_vanishes_regular (show sep f ∉ P from hsep)]
  constructor
  · intro hb x hx
    have hz : eval (graphPoint f x) b = 0 := hb _ ⟨x, hx, rfl⟩
    rw [← hpoint x hx, hz, zero_mul]
  · intro ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (mul_eq_zero.mp ((hpoint x hx).trans (ha x hx))).resolve_right (pow_ne_zero n hx.2)
private theorem chart_colength {f : Row 3} (T : LiftedChart top f)
    (P : Ideal (GeoRow 3)) (Q : Ideal (GeoRow 4)) [P.IsPrime] [Q.IsPrime]
    (hQ : threeCut f T ≤ Q) (hsQ : liftedSep f ∉ Q)
    (hQP : Q.comap (rename Fin.castSucc).toRingHom = P) :
    let A := Localization.AtPrime P
    let B := Localization.AtPrime Q
    Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A)) =
      Module.length B (B ⧸ (threeCut f T).map (algebraMap (GeoRow 4) B)) := by
  obtain ⟨q, hprime, hq⟩ := exists_open_prime hQ hsQ
  let : q.IsPrime := hprime
  let e := graphEquiv f T
  let p := q.comap e.toRingHom
  let : p.IsPrime := Ideal.comap_isPrime _ q
  have hp : p.comap (oldMap f) = P := by
    ext b
    change graphEquiv f T (oldMap f b) ∈ q ↔ b ∈ P
    rw [graphEquiv_on]
    change liftRow b ∈ q.comap (graphMap f T) ↔ b ∈ P
    rw [hq]
    change b ∈ Q.comap (rename Fin.castSucc).toRingHom ↔ b ∈ P
    rw [hQP]
  exact colength_eq_of_quotient_equiv
    ((openAtPrimeEquivQuotient p hp).symm.trans
      ((Localization.localRingEquiv p q e rfl).trans (openAtPrimeEquivQuotient q hq)))
private theorem graph_is_curve {f : Row 3} (hf : Irreducible f)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) :
    (graphCurve f P).IsPrime ∧ (affineHilbertPolynomial (graphCurve f P)).natDegree = 1 := by
  obtain ⟨hm, hs⟩ := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let : P.IsPrime := hm.isPrime
  obtain ⟨hp, hdim⟩ := graph_dimension f P hs
  exact ⟨hp, hdim.trans (retained_dimension hf hP)⟩
private theorem point_isolated {f : Row 3} (hf : Irreducible f)
    (T : LiftedChart top f) {L : GeoRow 4} (hL : ∀ P ∈ factorCurves f, L ∉ graphCurve f P)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) {y : JetPoint}
    (hy : y ∈ graphLocus f P) (hLy : eval y L = 0) :
    pointIdeal y ∈ (threeCut f T ⊔ Ideal.span {L}).minimalPrimes := by
  let m := pointIdeal y
  have hmsep : liftedSep f ∉ m := sep_notMem_point hy
  obtain ⟨hProper, hRet⟩ := mem_factorCurves.mp hP
  have hBm : threeCut f T ≤ m :=
    (threeCut_le_graphCurve T (Ideal.mem_retainedMinimalPrimes.mp hRet).1.le).trans
      (graphCurve_le_point hy)
  have hmL : L ∈ m := (mem_vanishingIdeal_singleton_iff _ _).mpr hLy
  refine ⟨⟨inferInstance, sup_le hBm ((Ideal.span_singleton_le_iff_mem _).mpr hmL)⟩, ?_⟩
  intro Q hQ hQm
  let q := Q.comap (rename Fin.castSucc).toRingHom
  have hQsep : liftedSep f ∉ Q := fun h => hmsep (hQm h)
  let : Q.IsPrime := hQ.1
  let : q.IsPrime := hQ.1.comap _
  obtain ⟨hIq, hGQ⟩ := prime_of_chart T Q (le_sup_left.trans hQ.2) hQsep
  have hsq : sep f ∉ q := hQsep
  obtain ⟨P', hP', hP'q⟩ := Ideal.exists_mem_retainedMinimalPrimes_le (Q := q) hIq hsq
  have hP'f : P' ∈ factorCurves f := mem_factorCurves.mpr ⟨hProper, hP'⟩
  have hle : graphCurve f P' ≤ Q := by
    rw [← hGQ]
    exact vanishingIdeal_anti_mono
      (Set.image_mono fun _ hx => ⟨zeroLocus_anti_mono hP'q hx.1, hx.2⟩)
  obtain ⟨hp', hd⟩ := graph_is_curve hf hP'f
  have hLQ : Ideal.span {L} ≤ Q := le_sup_right.trans hQ.2
  have hcut := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hp' (hL P' hP'f) le_rfl).1
  rw [hd, Nat.sub_self] at hcut
  have hdeg := (natDegree_affineHilbertPolynomial_le_of_le (sup_le hle hLQ)).trans hcut
  let : Module.Finite GeometricX (GeoRow 4 ⧸ Q) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero (Nat.eq_zero_of_le_zero hdeg)
  have hfield : IsField (GeoRow 4 ⧸ Q) :=
    isField_of_isIntegral_of_isField' (R := GeometricX) (Field.toIsField _)
  exact (Ideal.Quotient.maximal_of_isField Q hfield).eq_of_le
    (inferInstance : m.IsPrime).ne_top hQm |>.ge
theorem proof : Low6966Leading_1_1.c2 top := by
  intro f hf _ T L hL P hP y hy hLy
  have hJ : fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut L =
      threeCut f T ⊔ Ideal.span {L} := by
    simp [fourCutIdeal, threeCut, graphIdeal, Ideal.span_insert, sup_assoc]
  dsimp only
  rw [hJ]
  refine ⟨point_isolated hf T hL hP hy hLy, ?_⟩
  obtain ⟨hmin, hsep⟩ := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let : P.IsPrime := hmin.isPrime
  let Q := graphCurve f P
  let : Q.IsPrime := (graph_is_curve hf hP).1
  have hQy : Q ≤ pointIdeal y := graphCurve_le_point hy
  have hLiftSep : liftedSep f ∉ Q := fun h => sep_notMem_point hy (hQy h)
  rw [componentLength, dite_eq_left hmin.isPrime]
  rw [chart_colength T P Q (threeCut_le_graphCurve T hmin.le) hLiftSep (graphCurve_comap hsep)]
  exact length_atPrime_le_length_principalCut hQy
    ((mem_vanishingIdeal_singleton_iff _ _).mpr hLy) (hL P hP)
end
end Low6966Leading_1_1_2
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1_3
noncomputable section
variable {top : Fin 16}
open K1_13 (Shape)
open Low6966Leading (lowBox liftedBox mixedCoefficients)
open K1_13_5_4_2 K1_13_5_4_2_5 K1_13_5_4_2_5_2
open MeasureTheory Set Filter
open scoped Topology Pointwise ENNReal BigOperators
open K1_13_5_4_2_5_2_2 (realCap shiftedCap shiftedCap_tendsto form form_apply form_fun bounds mem_realCap support support_attains Pair nonparallel remaining slabMatrix slabRegion volume_slabRegion slabMatrix_invertible slabMap_apply)

private theorem mem_shifted {P : Set ExponentSpace} (h0 : 0 ∈ P)
    (hsub : P ⊆ capBody lowBox 0) {s : Shape} {h : ℕ} {t : ℝ} {x : ExponentSpace} :
    x ∈ shiftedCap P s h t ↔ x 3 ∈ Icc 0 (h : ℝ) ∧
      ∀ i, form i x ≤ bounds s i + t * K1_13_5_4_2_5_2_2.support P i := by
  rw [shiftedCap, mem_realCap]
  have hlow (i : Fin 6) (hi : 3 ≤ i.val) : K1_13_5_4_2_5_2_2.support P i = 0 := by
    have hzero : (0 : ℝ) ∈ form i '' P := ⟨0, h0, map_zero _⟩
    have hub : 0 ∈ upperBounds (form i '' P) := by
      rintro _ ⟨p, hp, rfl⟩
      have hn := (hsub hp).1
      fin_cases i <;> norm_num at hi
      all_goals simpa [form_apply] using hn _
    exact le_antisymm (csSup_le ⟨0, hzero⟩ hub) (le_csSup ⟨0, hub⟩ hzero)
  refine and_congr_right (fun _ => forall_congr' (fun i => ?_))
  fin_cases i
  · simp [bounds, K1_13_5_4_2_5_2_2.support, totalSupport, form_fun]
  · simp [bounds, K1_13_5_4_2_5_2_2.support, indexSupport, form_fun]
  · simp [bounds, K1_13_5_4_2_5_2_2.support, topSupport, form_fun]
  all_goals rw [hlow _ (by decide)]; simp [bounds]
private theorem form_bounded {P : Set ExponentSpace} (hsub : P ⊆ capBody lowBox 0)
    {x : ExponentSpace} (hx : x ∈ P) (i : Fin 6) : |form i x| ≤ 284 := by
  have hp := hsub hx
  have h0 := hp.1 0
  have h1 := hp.1 1
  have h2 := hp.1 2
  have hb := hp.2.1
  change x 0 + x 1 + x 2 ≤ (lowBox.b : ℝ) at hb
  norm_num [lowBox] at hb
  rw [abs_le, form_apply]
  fin_cases i <;> simp <;> constructor <;> linarith
private theorem shiftedCap_error {P : Set ExponentSpace} (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0)
    (s : Shape) (h : ℕ) (htop : 0 < s.t) :
    ∃ K : ℝ, ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ),
      0 ≤ (volume (shiftedCap P s h t)).toReal - (volume (t • P + capBody s h)).toReal ∧
      (volume (shiftedCap P s h t)).toReal - (volume (t • P + capBody s h)).toReal ≤ K * t^2 := by
  have hc : IsCompact P := by
    obtain ⟨v, hv, rfl⟩ := hP.polytope
    exact hv.isCompact_convexHull ℝ
  choose pt hpt heq hmax using support_attains hc hP.zero_mem
  have hsup (i : Fin 6) : K1_13_5_4_2_5_2_2.support P i ≤ 284 :=
    (heq i).symm.trans_le ((le_abs_self _).trans (form_bounded hsub (hpt i) i))
  let R : ℝ := (s.b : ℝ) + (h : ℝ) + 284
  let coeff (p : Pair) : ℝ := |(slabMatrix p).det⁻¹| * 4 * R^2 * 284^2
  have hR : 0 ≤ R := by positivity
  refine ⟨∑ p, coeff p, ?_⟩
  have htop' : (0 : ℝ) < (s.t : ℝ) := by exact_mod_cast htop
  have hsmall : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), t < (s.t : ℝ) / 284 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (div_pos htop' (by norm_num : (0 : ℝ) < 284)))
  have hone : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0), hone, hsmall]
      with t ht ht1 hts
  have ht' : 0 < t := ht
  let e : ℝ := t * 284
  have he : 0 ≤ e := by positivity
  let S := shiftedCap P s h t
  let C := t • P + capBody s h
  let E := fun p : Pair => slabRegion (bounds s) R e p
  have hCS : C ⊆ S := by
    rintro x hx
    obtain ⟨w, hw, z, hz, rfl⟩ := mem_add.mp hx
    obtain ⟨y, hy, hwy⟩ := mem_smul_set.mp hw
    subst w
    have hz' := mem_realCap.mp (show z ∈ K1_13_5_4_2_5_2_2.realCap s.b s.j s.t h from hz)
    refine (mem_shifted hP.zero_mem hsub).mpr ⟨?_, fun i => ?_⟩
    · simpa [Pi.add_apply, Pi.smul_apply, hP.zero_height y hy] using hz'.1
    · rw [map_add, map_smul, smul_eq_mul]
      exact (add_le_add (mul_le_mul_of_nonneg_left (hmax i y hy) ht'.le) (hz'.2 i)).trans_eq
        (add_comm _ _)
  have hcube : S ⊆ Icc (0 : ExponentSpace) (fun _ => R) := by
    intro x hx
    obtain ⟨hn, hb, _, _, hh⟩ := (show x ∈ K1_13_5_4_2_5_2_2.realCap _ _ _ _ from hx)
    have htotal : totalSupport P = K1_13_5_4_2_5_2_2.support P 0 := by simp [totalSupport, K1_13_5_4_2_5_2_2.support, form_fun]
    have hbx : x 0 + x 1 + x 2 ≤ (s.b : ℝ) + t * 284 := by
      rw [htotal] at hb
      exact hb.trans (add_le_add_right (mul_le_mul_of_nonneg_left (hsup 0) ht'.le) _)
    refine ⟨hn, fun i => ?_⟩
    have h0 := hn 0
    have h1 := hn 1
    have h2 := hn 2
    have hH : 0 ≤ (h : ℝ) := by positivity
    have hB : 0 ≤ (s.b : ℝ) := by positivity
    fin_cases i <;> dsimp [R] <;> linarith
  have hcover : S ⊆ C ∪ ⋃ p, E p := by
    intro x hx
    by_cases hxc : x ∈ C
    · exact Or.inl hxc
    have hb := (mem_shifted hP.zero_mem hsub).mp hx
    have hbase : x ∉ capBody s h := fun h =>
      hxc (mem_add.mpr ⟨0, ⟨0, hP.zero_mem, smul_zero _⟩, x, h, zero_add _⟩)
    have hviol : ¬ ∀ i, form i x ≤ bounds s i :=
      fun h => hbase (mem_realCap.mpr ⟨hb.1, h⟩)
    push Not at hviol
    obtain ⟨i, hi⟩ := hviol
    let y := x - t • pt i
    have hyh : y 3 ∈ Icc 0 (h : ℝ) := by
      simpa [y, Pi.sub_apply, Pi.smul_apply, hP.zero_height _ (hpt i)] using hb.1
    have hy : y ∉ capBody s h := fun h =>
      hxc (mem_add.mpr ⟨t • pt i, ⟨pt i, hpt i, rfl⟩, y, h, by dsimp [y]; abel⟩)
    have hother : ¬ ∀ j, form j y ≤ bounds s j :=
      fun h => hy (mem_realCap.mpr ⟨hyh, h⟩)
    push Not at hother
    obtain ⟨j, hj⟩ := hother
    have hshift (k : Fin 6) : form k y = form k x - t * form k (pt i) := by
      simp [y, smul_eq_mul]
    have hji : i ≠ j := by
      rintro rfl
      rw [hshift, heq] at hj
      linarith [hb.2 i]
    have hlo : bounds s j - e ≤ form j x := by
      have h := (abs_le.mp (form_bounded hsub (hpt i) j)).1
      rw [hshift] at hj
      dsimp [e]
      linarith [mul_le_mul_of_nonneg_left h ht'.le]
    have hhi (k : Fin 6) : form k x ≤ bounds s k + e :=
      (hb.2 k).trans (add_le_add_right (mul_le_mul_of_nonneg_left (hsup k) ht'.le) _)
    have hpar : nonparallel (i, j) := by
      refine ⟨?_, hji, ?_⟩
      · have hn : ∀ k : Fin 4, 0 ≤ x k := (hcube hx).1
        fin_cases i <;> norm_num [bounds, form_apply] at hi ⊢
        · exact (not_lt_of_ge (hn 0)) hi
        · exact (not_lt_of_ge (hn 1)) hi
        · exact (not_lt_of_ge (hn 2)) hi
      · by_contra hn
        push Not at hn
        obtain ⟨rfl, rfl⟩ := hn
        simp [bounds, form_apply] at hi hlo
        linarith [show e < (s.t : ℝ) from (lt_div_iff₀ (by norm_num : (0 : ℝ) < 284)).mp hts]
    refine Or.inr (mem_iUnion.mpr ⟨(i,j), ?_⟩)
    change x ∈ slabRegion _ _ _ _
    simp only [slabRegion, hpar, ↓reduceIte, mem_preimage, slabMap_apply]
    have hxl := (hcube hx).1
    have hxu := (hcube hx).2
    constructor <;> intro k <;> fin_cases k
    · exact (sub_le_self _ he).trans hi.le
    · exact hlo
    · exact hxl (remaining (i, j))
    · exact hxl 3
    · exact hhi i
    · exact hhi j
    · exact hxu (remaining (i, j))
    · exact hxu 3
  have hevol : volume (⋃ p, E p) ≤ ENNReal.ofReal ((∑ p, coeff p) * t^2) := by
    calc
      _ ≤ ∑ p, volume (E p) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ p, ENNReal.ofReal (coeff p * t^2) := by
        apply Finset.sum_le_sum
        intro p _
        have h := volume_slabRegion (bounds s) hR he p
        convert h using 2
        dsimp [coeff, e]
        ring
      _ = _ := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  have hS : volume S ≠ ∞ := measure_ne_top_of_subset hcube isCompact_Icc.measure_ne_top
  have hC : volume C ≠ ∞ := measure_ne_top_of_subset hCS hS
  have hevol' : volume S ≤ volume C + ENNReal.ofReal ((∑ p, coeff p) * t^2) :=
    (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add_right hevol _))
  constructor
  · exact sub_nonneg.mpr (ENNReal.toReal_mono hS (measure_mono hCS))
  · have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hC, ENNReal.ofReal_ne_top⟩) hevol'
    rw [ENNReal.toReal_add hC ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at h
    exact sub_le_iff_le_add'.mpr h
theorem volume_variation (P : Set ExponentSpace) (hP : FirstBody P)
    (hsub : P ⊆ capBody lowBox 0) (s : Shape) (h : ℕ)
    (hs : Chamber s) (hjb : s.j < s.b) (htop : 0 < s.t) :
    Tendsto (volumeQuotient P (capBody s h)) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (capFirstVariation s h (totalSupport P) (indexSupport P) (topSupport P))) := by
  obtain ⟨K, hK⟩ := shiftedCap_error hP hsub s h htop
  let f := fun t : ℝ =>
    ((volume (shiftedCap P s h t)).toReal - (volume (capBody s h)).toReal) / t
  have hupper := shiftedCap_tendsto P s h hs hjb htop
  have hzero : Tendsto (fun t : ℝ => K * t) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.const_mul K
  have hlower : Tendsto (fun t => f t - K * t) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (capFirstVariation s h (totalSupport P) (indexSupport P) (topSupport P))) := by
    simpa using hupper.sub hzero
  apply hlower.squeeze' hupper
  · filter_upwards [hK, eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht htpos
    have hpos : 0 < t := htpos
    have he := (div_le_iff₀ hpos).mpr (show _ ≤ K * t * t by
      simpa only [pow_two, mul_assoc] using ht.2)
    have hd : f t - volumeQuotient P (capBody s h) t =
        ((volume (shiftedCap P s h t)).toReal -
          (volume (t • P + capBody s h)).toReal) / t := by
      unfold f volumeQuotient
      rw [← sub_div]
      congr 1
      ring
    linarith
  · filter_upwards [hK, eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht htpos
    have hpos : 0 < t := htpos
    exact div_le_div_of_nonneg_right (by linarith [ht.1]) hpos.le
end
end Low6966Leading_1_1_3
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1_3
noncomputable section
variable {top : Fin 16}
open K1_13 (Shape)
open Low6966Leading (lowBox graphBox liftedBox mixedCoefficients)
open K1_13_5_4_2 (ExponentSpace capBody mixedVolume4)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation
  volumeQuotient rest univ_eq_insert zero_notMem_rest)
open K1_13_5_4_2_5_2_1 (cap_polytope closedOrthant)
open Low6966Prices (taylorLength)
open Low6966Leading_1_1 (lastBox lastMixedVolume)
open MeasureTheory Filter MvPolynomial
open scoped BigOperators Pointwise Topology
open K1_13_5_4_2_5 (sumShape sumChamber sum_capBody capBody_zero)
open K1_13_5_4_2_5_2_1 (labelHull_eq positivePolynomial)
open K1_13_5_4_2_5_2 (weights polar_linear)
open K1_13_5_4_2_5_2 (volume_zero_height)
def boxShape (top : Fin 16) : Fin 4 → Shape := ![lowBox, (graphBox top), liftedBox top (taylorLength + 1), (lastBox top)]
def boxHeight : Fin 4 → ℕ := ![0, 1, taylorLength - 1, taylorLength]
abbrev baseShape (top : Fin 16) (S : Finset (Fin 4)) : Shape := K1_13_5_4_2_5.sumShape S (boxShape top)
def baseHeight (S : Finset (Fin 4)) : ℕ := ∑ i ∈ S, boxHeight i
private def base (top : Fin 16) (S : Finset (Fin 4)) : Set ExponentSpace :=
  capBody (baseShape top S) (baseHeight S)
private def slots (top : Fin 16) (P : Set ExponentSpace) : Fin 4 → Set ExponentSpace :=
  Function.update (fun i => capBody ((boxShape top) i) (boxHeight i)) 0 P
private theorem mixed_eq (P : Set ExponentSpace) : lastMixedVolume top P = mixedVolume4 (slots top P) := by
  unfold lastMixedVolume
  congr 1
  funext i
  fin_cases i <;> rfl
theorem box_chamber (i : Fin 4) : Chamber ((boxShape top) i) := by
  fin_cases top <;> fin_cases i <;> exact ⟨by decide, by decide⟩
theorem base_chamber (S : Finset (Fin 4)) : Chamber (baseShape top S) :=
  sumChamber S (boxShape top) box_chamber
private theorem slots_nonempty (P : Set ExponentSpace) (hP : FirstBody P)
    (i : Fin 4) : 0 ∈ slots top P i := by
  by_cases hi : i = 0
  · simpa [slots, hi] using hP.zero_mem
  · simp [slots, Function.update_of_ne hi, capBody]
private theorem volume_polynomial (P : Set ExponentSpace) (hP : FirstBody P) :
    ∃ p : MvPolynomial (Fin 4) ℝ, p.IsHomogeneous 4 ∧
      ∀ w : Fin 4 → ℝ, (∀ i, 0 ≤ w i) →
        p.eval w = (volume (∑ i, w i • slots top P i)).toReal := by
  classical
  have hslot (i : Fin 4) :
      ∃ v : Finset ExponentSpace, slots top P i = convexHull ℝ (v : Set ExponentSpace) := by
    by_cases hi : i = 0
    · subst i
      obtain ⟨s, hs, hr⟩ := hP.polytope
      exact ⟨hs.toFinset, by simpa [slots] using hr⟩
    · rw [slots, Function.update_of_ne hi]
      exact cap_polytope _ _ (box_chamber i)
  choose v hv using hslot
  obtain ⟨p, hp, he⟩ := positivePolynomial K1_13_5_4_2_5_2_1_1.proof
    K1_13_5_4_2_5_2_1_2.proof (slots top P) v hv
  refine ⟨p, hp, closedOrthant (slots top P) ?_ (slots_nonempty P hP) ?_ p he⟩
  · intro i
    rw [hv i]
    exact convex_convexHull _ _
  · intro w
    rw [← labelHull_eq (slots top P) v hv w]
    exact (Set.finite_range _).isCompact_convexHull ℝ
private theorem polar_slots (P : Set ExponentSpace) (hP : FirstBody P)
    (t : ℝ) (S : Finset (Fin 4)) :
    (∑ i, weights t S i • slots top P i) = ∑ i ∈ S, slots top (t • P) i := by
  calc
    _ = ∑ i ∈ S, (![t, 1, 1, 1] : Fin 4 → ℝ) i • slots top P i := by
      rw [← Finset.sum_subset (s₁ := S) (s₂ := Finset.univ) (Finset.subset_univ S)
        (f := fun i => weights t S i • slots top P i)]
      · exact Finset.sum_congr rfl (fun i hi => by simp [weights, hi])
      · intro i _ hi
        simp [weights, hi, Set.zero_smul_set (Set.nonempty_of_mem (slots_nonempty P hP i))]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      fin_cases i <;> simp [slots]
private theorem mixed_scale (P : Set ExponentSpace) (hP : FirstBody P) (t : ℝ) (ht : 0 ≤ t) :
    lastMixedVolume top (t • P) = t * lastMixedVolume top P := by
  obtain ⟨p, hp, heval⟩ := volume_polynomial P hP
  have hw (s : ℝ) (hs : 0 ≤ s) (S : Finset (Fin 4)) (i : Fin 4) :
      0 ≤ weights s S i := by
    unfold weights
    apply ite_nonneg _ (le_refl (0 : ℝ))
    fin_cases i
    · exact hs
    all_goals exact zero_le_one
  have hpol (s : ℝ) (hs : 0 ≤ s) (S : Finset (Fin 4)) :
      p.eval (weights s S) = (volume (∑ i ∈ S, slots top (s • P) i)).toReal := by
    rw [heval _ (hw s hs S), polar_slots P hP]
  simpa only [mixed_eq, mixedVolume4, hpol _ ht, hpol 1 zero_le_one, one_smul]
    using polar_linear p hp t
private theorem sum_slots (P : Set ExponentSpace) {S : Finset (Fin 4)} (h0 : 0 ∉ S) :
    (∑ i ∈ S, slots top P i) = base top S := by
  change _ = capBody (K1_13_5_4_2_5.sumShape S (boxShape top)) (∑ i ∈ S, boxHeight i)
  rw [← sum_capBody _ _ _ box_chamber]
  apply Finset.sum_congr rfl
  intro i hi
  have hne : i ≠ 0 := fun h => h0 (h ▸ hi)
  simp [slots, Function.update_of_ne hne]
private theorem mixed_increment (P : Set ExponentSpace) (t : ℝ) :
    lastMixedVolume top (t • P) =
      ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        ((volume (t • P + base top S)).toReal - (volume (base top S)).toReal) := by
  rw [mixed_eq, mixedVolume4, univ_eq_insert,
    Finset.sum_powerset_insert zero_notMem_rest, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  have h0 : (0 : Fin 4) ∉ S := fun h => zero_notMem_rest (hsub h)
  have hs : S.card ≤ 3 :=
    (Finset.card_le_card hsub).trans (show rest.card ≤ 3 by decide)
  rw [Finset.sum_insert h0, Finset.card_insert_of_notMem h0,
    sum_slots _ h0, show slots top (t • P) 0 = t • P by simp [slots]]
  have e₁ : 4 - S.card = (3 - S.card) + 1 := by omega
  have e₂ : 4 - (S.card + 1) = 3 - S.card := by omega
  rw [e₁, e₂, pow_succ]
  ring
private theorem empty_quotient (P : Set ExponentSpace) (hP : FirstBody P) (t : ℝ) :
    volumeQuotient P (base top ∅) t = 0 := by
  have hbase : base top ∅ = 0 := by simp [base, K1_13_5_4_2_5.sumShape, baseHeight, capBody_zero]
  have hPz : volume (t • P) = 0 := by
    apply volume_zero_height
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    simp [Pi.smul_apply, hP.zero_height y hy]
  rw [volumeQuotient, hbase, add_zero, hPz,
    show (0 : Set ExponentSpace) = {0} by rfl]
  simp
private theorem tendsto_quotient (P : Set ExponentSpace)
    (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) {S : Finset (Fin 4)} (hS : S ⊆ rest) :
    Tendsto (volumeQuotient P (base top S)) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (capFirstVariation (baseShape top S) (baseHeight S)
        (totalSupport P) (indexSupport P) (topSupport P))) := by
  by_cases he : S = ∅
  · subst S
    rw [show volumeQuotient P (base top ∅) = (fun _ : ℝ => 0) from funext (empty_quotient P hP)]
    simp [capFirstVariation, K1_13_5_4_2_5.sumShape, baseHeight]
  · have hn := Finset.nonempty_iff_ne_empty.mpr he
    apply volume_variation P hP hsub _ _ (base_chamber S)
    · exact Finset.sum_lt_sum_of_nonempty hn (fun i _ => by fin_cases top <;> fin_cases i <;> decide)
    · exact Finset.sum_pos (fun i _ => by fin_cases top <;> fin_cases i <;> decide) hn
theorem variation_eq (P : Set ExponentSpace) (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) :
    lastMixedVolume top P =
      ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        capFirstVariation (baseShape top S) (baseHeight S)
          (totalSupport P) (indexSupport P) (topSupport P) := by
  have hlim := tendsto_finsetSum rest.powerset (fun S hS =>
    (tendsto_quotient (top := top) P hP hsub (Finset.mem_powerset.mp hS)).const_mul
      ((-1 : ℝ) ^ (3 - S.card)))
  have heq : (fun _ : ℝ => lastMixedVolume top P) =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      (fun t : ℝ => ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        volumeQuotient P (base top S) t) := by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht
    have ht' : 0 < t := ht
    have hquot : lastMixedVolume top (t • P) / t = lastMixedVolume top P := by
      rw [mixed_scale P hP t ht'.le]
      exact mul_div_cancel_left₀ _ ht'.ne'
    calc
      lastMixedVolume top P = lastMixedVolume top (t • P) / t := hquot.symm
      _ = _ := by simp only [mixed_increment, Finset.sum_div, volumeQuotient, mul_div_assoc]
  exact tendsto_const_nhds_iff.mp (hlim.congr' heq.symm)
end
end Low6966Leading_1_1_3
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1_3
noncomputable section
variable {top : Fin 16}
open K1_13 (Shape)
open Low6966Leading (lowBox liftedBox mixedCoefficients)
open K1_13_5_4_2 (ExponentSpace capBody)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation rest)
open Low6966Leading (mixedBudget)
open Low6966Leading_1_1 (lastMixedVolume)
open scoped BigOperators

private def coefficients (s : Shape) (h : ℕ) : ℕ × ℕ × ℕ :=
  (2 * h * s.t * (s.j - s.t),
    h * s.t * (2 * (s.b - s.j) + s.t),
    h * (s.j - 2 * s.t) * (2 * s.b - s.j))
private theorem twice_variation (s : Shape) (h : ℕ) (hs : Chamber s) (B J T : ℝ) :
    2 * capFirstVariation s h B J T =
      (coefficients s h).1 * B + (coefficients s h).2.1 * J + (coefficients s h).2.2 * T := by
  have hB : s.j ≤ s.b := hs.1
  have hJ : 2 * s.t ≤ s.j := hs.2
  have ht : s.t ≤ s.j := by omega
  have hb : s.j ≤ 2 * s.b := by omega
  simp only [capFirstVariation, coefficients, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_sub hB, Nat.cast_sub hJ, Nat.cast_sub ht, Nat.cast_sub hb]
  ring
private def row (top : Fin 16) (S : Finset (Fin 4)) : ℕ × ℕ × ℕ :=
  coefficients (baseShape top S) (baseHeight S)
private theorem alternating_three (F : Finset (Fin 4) → ℝ) :
    (∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) * F S) =
      F (insert 1 (insert 2 (insert 3 ∅))) -
        F (insert 1 (insert 2 ∅)) - F (insert 1 (insert 3 ∅)) - F (insert 2 (insert 3 ∅)) +
        F (insert 1 ∅) + F (insert 2 ∅) + F (insert 3 ∅) - F ∅ := by
  unfold rest
  simp only [
    Finset.sum_powerset_insert (a := (1 : Fin 4)) (s := insert 2 (insert 3 ∅)) (by decide),
    Finset.sum_powerset_insert (a := (2 : Fin 4)) (s := insert 3 ∅) (by decide),
    Finset.sum_powerset_insert (a := (3 : Fin 4)) (s := ∅) (by decide),
    Finset.powerset_empty, Finset.sum_singleton]
  norm_num [Finset.card_insert_of_notMem, Finset.mem_insert]
  ring
private theorem twice_row (S : Finset (Fin 4)) (B J T : ℝ) :
    2 * capFirstVariation (baseShape top S) (baseHeight S) B J T =
      (row top S).1 * B + (row top S).2.1 * J + (row top S).2.2 * T :=
  twice_variation _ _ (base_chamber S) _ _ _
private def alternate {A : Type*} [AddGroup A] (F : Finset (Fin 4) → A) : A :=
  F (insert 1 (insert 2 (insert 3 ∅))) -
    F (insert 1 (insert 2 ∅)) - F (insert 1 (insert 3 ∅)) - F (insert 2 (insert 3 ∅)) +
    F (insert 1 ∅) + F (insert 2 ∅) + F (insert 3 ∅) - F ∅

private def coordinate (x : ℕ × ℕ × ℕ) : Fin 3 → ℕ := ![x.1, x.2.1, x.2.2]

private theorem mixed_receipt (top : Fin 16) (i : Fin 3) :
    alternate (fun S => (coordinate (row top S) i : ℤ)) =
      2 * (coordinate (mixedCoefficients top) i : ℤ) := by
  fin_cases top <;> fin_cases i <;> decide

theorem mixed_formula (P : Set ExponentSpace) (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) :
    lastMixedVolume top P = (mixedCoefficients top).1 * totalSupport P +
      (mixedCoefficients top).2.1 * indexSupport P + (mixedCoefficients top).2.2 * topSupport P := by
  rw [variation_eq P hP hsub]
  apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
  generalize totalSupport P = B
  generalize indexSupport P = J
  generalize topSupport P = T
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm (2 : ℝ), twice_row]
  rw [alternating_three]
  have hc (i : Fin 3) :
      alternate (fun S => (coordinate (row top S) i : ℝ)) =
        2 * (coordinate (mixedCoefficients top) i : ℝ) := by
    unfold alternate
    have h := mixed_receipt top i
    unfold alternate at h
    have hr := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at hr
    exact hr
  have hB := hc 0
  have hJ := hc 1
  have hT := hc 2
  change alternate (fun S => ((row top S).1 : ℝ)) = 2 * ((mixedCoefficients top).1 : ℝ) at hB
  change alternate (fun S => ((row top S).2.1 : ℝ)) = 2 * ((mixedCoefficients top).2.1 : ℝ) at hJ
  change alternate (fun S => ((row top S).2.2 : ℝ)) = 2 * ((mixedCoefficients top).2.2 : ℝ) at hT
  unfold alternate at hB hJ hT
  linear_combination B * hB + J * hJ + T * hT
theorem price_eq (top : Fin 16) :
    (mixedCoefficients top).1 * (Low6966Prices.lowerWidth top : ℝ) +
    (mixedCoefficients top).2.1 * (Low6966Prices.lowerIndex top : ℝ) +
    (mixedCoefficients top).2.2 * (Low6966Prices.lowerTop top : ℝ) =
      (mixedBudget top : ℝ) := by
  unfold mixedBudget
  rcases h : mixedCoefficients top with ⟨b, j, r⟩
  simp only [Nat.cast_add, Nat.cast_mul]

end
end Low6966Leading_1_1_3
end
section
set_option autoImplicit false
namespace Low6966Leading_1_1_3
noncomputable section
variable {top : Fin 16}
open K1_13 (Row indexDegree)
open Low6966Leading (lowBox liftedBox mixedCoefficients)
open K1_13_5_4 (genericRow liftRow)
open K1_13_5_4_2 (ExponentSpace downBody capBody)
open K1_13_5_4_2_5 (FirstBody firstBody_zero firstBody_row)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport)
open Low6966Leading (SecondFactors mixedBudget)
open Low6966Leading_1_1 (lastMixedVolume)
open MvPolynomial
open scoped BigOperators Pointwise
open K1_13_5_4_2_5 (rowShape row_support downBody_subset)
private theorem sum_downBody_subset {n : ℕ} (f : Fin n → Row 3)
    (S : Finset (Fin n)) (a : K1_13.Shape)
    (ht : (∑ i, (f i).totalDegree) ≤ a.b)
    (hj : (∑ i, indexDegree (f i)) ≤ a.j)
    (htop : (∑ i, (f i).degreeOf 2) ≤ a.t) :
    (∑ i ∈ S, downBody (liftRow (genericRow (f i)))) ⊆ capBody a 0 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Set.mem_finsetSum S _ x).mp hx
  have hb (i : Fin n) (hi : i ∈ S) : y i ∈ capBody (rowShape (f i)) 0 :=
    downBody_subset (row_support (f i)) (hy hi)
  have cap (degree : Fin n → ℕ) (b : ℕ) (h : (∑ i, degree i) ≤ b) :
      (∑ i ∈ S, (degree i : ℝ)) ≤ b := by
    rw [← Nat.cast_sum, Nat.cast_le]
    exact (Finset.sum_le_sum_of_subset (Finset.subset_univ S)).trans h
  simp only [capBody, Set.mem_ofPred_eq, Finset.sum_apply]
  refine ⟨fun j => Finset.sum_nonneg (fun i hi => (hb i hi).1 j), ?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact (Finset.sum_le_sum (fun i hi => (hb i hi).2.1)).trans (cap _ _ ht)
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact (Finset.sum_le_sum (fun i hi => (hb i hi).2.2.1)).trans (cap _ _ hj)
  · exact (Finset.sum_le_sum (fun i hi => (hb i hi).2.2.2.1)).trans (cap _ _ htop)
  · rw [Nat.cast_zero]
    exact Finset.sum_nonpos (fun i hi => by simpa using (hb i hi).2.2.2.2)
private theorem support_add {P Q : Set ExponentSpace} (hP : FirstBody P) (hQ : FirstBody Q)
    (L : ExponentSpace → ℝ) (hL : Continuous L) (ha : ∀ x y, L (x + y) = L x + L y) :
    sSup (L '' (P + Q)) = sSup (L '' P) + sSup (L '' Q) := by
  let ℓ := AddMonoidHom.mk' L ha
  change sSup (ℓ '' (P + Q)) = _
  have bounded {U : Set ExponentSpace} (hU : FirstBody U) : BddAbove (L '' U) := by
    obtain ⟨v, hv, rfl⟩ := hU.polytope
    exact (hv.isCompact_convexHull ℝ).bddAbove_image hL.continuousOn
  rw [Set.image_add ℓ]
  exact csSup_add ((Set.nonempty_of_mem hP.zero_mem).image L) (bounded hP)
    ((Set.nonempty_of_mem hQ.zero_mem).image L) (bounded hQ)
private theorem sum_mixed {ι : Type} (P : ι → Set ExponentSpace) (hP : ∀ i, FirstBody (P i))
    (hsub : ∀ S : Finset ι, (∑ i ∈ S, P i) ⊆ capBody lowBox 0) (S : Finset ι) :
    FirstBody (∑ i ∈ S, P i) ∧
      (∑ i ∈ S, lastMixedVolume top (P i)) = lastMixedVolume top (∑ i ∈ S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨firstBody_zero, ?_⟩
    have hz : (0 : Set ExponentSpace) ⊆ capBody lowBox 0 := by simpa using hsub ∅
    rw [mixed_formula _ firstBody_zero hz]
    simp [totalSupport, indexSupport, topSupport, show (0 : Set ExponentSpace) = {0} from rfl]
  | @insert i S hi ih =>
    let Q := ∑ j ∈ S, P j
    have hPi : P i ⊆ capBody lowBox 0 := by simpa using hsub {i}
    have hPQ : P i + Q ⊆ capBody lowBox 0 := by simpa only [Q, Finset.sum_insert hi] using hsub (insert i S)
    have hbody := (hP i).add ih.1
    simp only [Finset.sum_insert hi, ih.2]
    refine ⟨hbody, ?_⟩
    rw [mixed_formula (P i) (hP i) hPi, mixed_formula Q ih.1 (hsub S), mixed_formula _ hbody hPQ]
    have hB : totalSupport (P i + Q) = totalSupport (P i) + totalSupport Q :=
      support_add (hP i) ih.1 _ (by fun_prop) (fun x y => by simp only [Pi.add_apply]; ring)
    have hJ : indexSupport (P i + Q) = indexSupport (P i) + indexSupport Q :=
      support_add (hP i) ih.1 _ (by fun_prop) (fun x y => by simp only [Pi.add_apply]; ring)
    have hT : topSupport (P i + Q) = topSupport (P i) + topSupport Q :=
      support_add (hP i) ih.1 _ (by fun_prop) (fun _ _ => rfl)
    rw [hB, hJ, hT]
    ring
private theorem support_bound (P : Set ExponentSpace) (hP : FirstBody P)
    (L : ExponentSpace → ℝ) {x : ℝ} (hx : ∀ p ∈ P, L p ≤ x) :
    sSup (L '' P) ≤ x :=
  csSup_le ((Set.nonempty_of_mem hP.zero_mem).image L) (by rintro _ ⟨p, hp, rfl⟩; exact hx p hp)
theorem proof : Low6966Leading_1_1.c3 top := by
  intro n f hf
  let P (i : Fin n) := downBody (liftRow (genericRow (f i)))
  have hP (i : Fin n) : FirstBody (P i) := firstBody_row (hf.irreducible i).ne_zero
  have hB₀ : (∑ i, (f i).totalDegree) ≤ lowBox.b := hf.total.trans (by fin_cases top <;> decide)
  have hJ₀ : (∑ i, indexDegree (f i)) ≤ lowBox.j := hf.index.trans (by fin_cases top <;> decide)
  have hT₀ : (∑ i, (f i).degreeOf 2) ≤ lowBox.t := hf.coordinate.trans (by fin_cases top <;> decide)
  have hs (S : Finset (Fin n)) : (∑ i ∈ S, P i) ⊆ capBody lowBox 0 := sum_downBody_subset f S lowBox hB₀ hJ₀ hT₀
  obtain ⟨hbody, hsum⟩ := sum_mixed (top := top) P hP hs Finset.univ
  change (∑ i, lastMixedVolume top (P i)) ≤ (mixedBudget top : ℝ)
  rw [hsum, mixed_formula _ hbody (hs _), ← price_eq]
  let bounds : K1_13.Shape :=
    ⟨Low6966Prices.lowerWidth top, Low6966Prices.lowerIndex top, Low6966Prices.lowerTop top⟩
  have hsT : (∑ i, P i) ⊆ capBody bounds 0 :=
    sum_downBody_subset f _ bounds hf.total hf.index hf.coordinate
  have hB : totalSupport (∑ i, P i) ≤ (bounds.b : ℝ) :=
    support_bound _ hbody _ (fun _ hx => (hsT hx).2.1)
  have hJ : indexSupport (∑ i, P i) ≤ (bounds.j : ℝ) :=
    support_bound _ hbody _ (fun _ hx => (hsT hx).2.2.1)
  have hT : topSupport (∑ i, P i) ≤ (bounds.t : ℝ) :=
    support_bound _ hbody _ (fun _ hx => (hsT hx).2.2.2.1)
  dsimp only [bounds] at hB hJ hT
  gcongr
end
end Low6966Leading_1_1_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Low6966Leading_1_2
noncomputable section
variable {top : Fin 16}
open K1_13 (Row)
open K1_13_5 (compatibilityNumerator separant tangentNumerator)
open K1_13_5_4 (GeoRow genericRow genericCoeff genericCoeff_injective)
open K1_13_5_4_3 (TangentStable)
open K1_13_5_4_3_1 (tangentNumerator_add tangentNumerator_mul)
open Low6966Prices (taylorLength)
open Low6966Leading (Whole)
open Low6966Leading_1 (oldCut oldNext oldCutIdeal componentLength SimpleInvariant)
open Polynomial
open K1_13_5_4_3_1 (flat_rowToGeo rowToGeo_eq tangent_self)
open K1_13_5_4_3_3 (generic_cut_regular)
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem map_eq_maximal_of_length_one (f : Row 3) (P : Ideal (GeoRow 3))
    [P.IsPrime] (h : componentLength f P = 1) :
    (oldCutIdeal f).map (algebraMap (GeoRow 3) (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  classical
  unfold componentLength at h
  rw [dite_eq_left ‹P.IsPrime›, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
    ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at h
  exact h
private theorem simple_saturation (f : Row 3) (P : Ideal (GeoRow 3))
    [P.IsPrime] (h : componentLength f P = 1) (x : Row 3) (hx : genericRow x ∈ P) :
    ∃ s : Row 3, genericRow s ∉ P ∧ s * x ∈ Ideal.span {f, oldCut f} := by
  let q := P.comap (algebraMap (Row 3) (GeoRow 3))
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : P.LiesOver q := ⟨rfl⟩
  let A := Localization.AtPrime q
  let B := Localization.AtPrime P
  let _ : Algebra A B := Localization.AtPrime.algebraOfLiesOver q P
  have : Module.Flat (Row 3) (GeoRow 3) := flat_rowToGeo
  have : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q P (algebraMap (Row 3) (GeoRow 3)) rfl)
    infer_instance
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let J : Ideal (Row 3) := Ideal.span {f, oldCut f}
  have hJ : J.map (algebraMap (Row 3) (GeoRow 3)) = oldCutIdeal f := by
    simp only [J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, rowToGeo_eq,
      oldCutIdeal]
  have hJB : (J.map (algebraMap (Row 3) A)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq (Row 3) A B,
      IsScalarTower.algebraMap_eq (Row 3) (GeoRow 3) B, ← Ideal.map_map, hJ]
    exact map_eq_maximal_of_length_one f P h
  have hxB : algebraMap A B (algebraMap (Row 3) A x) ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsScalarTower.algebraMap_apply (Row 3) A B,
      IsScalarTower.algebraMap_apply (Row 3) (GeoRow 3) B, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (by rwa [rowToGeo_eq])
  rw [← hJB] at hxB
  have hxA : algebraMap (Row 3) A x ∈ J.map (algebraMap (Row 3) A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J.map (algebraMap (Row 3) A))]
    exact hxB
  obtain ⟨s, hs, hsx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A J x).mp hxA
  refine ⟨s, ?_, hsx⟩
  change algebraMap (Row 3) (GeoRow 3) s ∉ P at hs
  rwa [rowToGeo_eq] at hs
private theorem numerator_succ (f : Row 3) (P : Ideal (GeoRow 3)) (j : ℕ)
    (hj : genericRow (compatibilityNumerator f j) ∈ P) :
    genericRow (compatibilityNumerator f (j + 1)) ∈ P ↔
      genericRow (separant f) * genericRow (tangentNumerator f (compatibilityNumerator f j)) ∈ P := by
  have hterm :
      genericRow (((2 * j + 1 : ℕ) : Row 3) * compatibilityNumerator f j *
        tangentNumerator f (separant f)) ∈ P := by
    simp only [genericRow, map_mul]
    exact P.mul_mem_right _ (P.mul_mem_left _ hj)
  change (MvPolynomial.map genericCoeff) (_ - _) ∈ P ↔ _
  unfold genericRow at hterm ⊢
  rw [map_sub, P.sub_mem_iff_left hterm, map_mul]
theorem tangent_stable {f : Row 3} {P : Ideal (GeoRow 3)} (hp : P.IsPrime)
    (hle : oldCutIdeal f ≤ P) (hsep : genericRow (separant f) ∉ P)
    (hInv : SimpleInvariant f P) : TangentStable f P := by
  let := hp
  have hf : genericRow f ∈ P := hle (Ideal.subset_span (by simp))
  have hc : genericRow (oldCut f) ∈ P := hle (Ideal.subset_span (by simp))
  have hprod := (numerator_succ f P (taylorLength - 3) hc).mp hInv.2
  have hcut := (hp.mem_or_mem hprod).resolve_left hsep
  have hgen : ∀ z ∈ (Ideal.span {f, oldCut f} : Ideal (Row 3)),
      genericRow (tangentNumerator f z) ∈ P := by
    intro z hz
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hz
    rw [tangentNumerator_add, tangentNumerator_mul, tangentNumerator_mul, tangent_self,
      mul_zero, add_zero]
    simp only [genericRow, map_add, map_mul]
    exact P.add_mem (P.mul_mem_left _ hf)
      (P.add_mem (P.mul_mem_left _ hc) (P.mul_mem_left _ hcut))
  intro x hx
  obtain ⟨s, hs, hsx⟩ := simple_saturation f P hInv.1 x hx
  have hd := hgen (s * x) hsx
  rw [tangentNumerator_mul] at hd
  simp only [genericRow, map_add, map_mul] at hd
  change genericRow (tangentNumerator f s) * genericRow x +
    genericRow s * genericRow (tangentNumerator f x) ∈ P at hd
  have hz := P.sub_mem hd (P.mul_mem_left (genericRow (tangentNumerator f s)) hx)
  rw [add_sub_cancel_left] at hz
  exact (hp.mem_or_mem hz).resolve_left hs
theorem numerator_mem {f : Row 3} {P : Ideal (GeoRow 3)} (h : TangentStable f P)
    (hc : genericRow (oldCut f) ∈ P) {j : ℕ} (hj : taylorLength - 3 ≤ j) :
    genericRow (compatibilityNumerator f j) ∈ P := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  clear hj
  induction i with
  | zero => exact hc
  | succ i hi =>
    exact (numerator_succ f P _ hi).mpr (P.mul_mem_left _ (h _ hi))
theorem component_dimension {f : Row 3} {P : Ideal (GeoRow 3)}
    (hf : Irreducible f) (hwhole : ¬ Whole f)
    (hP : P ∈ (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))) :
    (MvPolynomial.affineHilbertPolynomial P).natDegree = 1 := by
  let F := genericRow f
  let G := genericRow (oldCut f)
  have hF : F ≠ 0 := by
    simpa only [F, genericRow, map_zero] using
      (MvPolynomial.map_injective _ genericCoeff_injective).ne hf.ne_zero
  have hregular := generic_cut_regular hf (show ¬ f ∣ oldCut f from hwhole)
  have hmin := (Ideal.mem_retainedMinimalPrimes.mp hP).1
  change P ∈ (Ideal.span {F, G}).minimalPrimes at hmin
  rw [Ideal.span_insert] at hmin
  have hp := hmin.isPrime
  obtain ⟨D, hD, hDP⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hmin.le)
  have hd := hD.isPrime
  have hFD : F ∈ D := hD.le (Ideal.mem_span_singleton_self F)
  have hDne : D ≠ ⊥ := fun h => hF (Ideal.mem_bot.mp (h ▸ hFD))
  have hDheight : D.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hD)
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hDne))
  obtain ⟨a, ha⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hDheight).principal
  change D = Ideal.span {a} at ha
  have hGD : G ∉ D := by
    intro hG
    obtain ⟨b, hFb⟩ := Ideal.mem_span_singleton.mp (ha ▸ hFD)
    obtain ⟨c, hGc⟩ := Ideal.mem_span_singleton.mp (ha ▸ hG)
    have hb0 : b ≠ 0 := by
      intro hb
      exact hF (by simp [hFb, hb])
    have hdiv : F ∣ G * b := ⟨c, by rw [hGc, hFb, mul_right_comm]⟩
    obtain ⟨q, hq⟩ := hregular b hdiv
    have hb : b * (a * q) = b * 1 := by
      calc
        b * (a * q) = (a * b) * q := by rw [← mul_assoc, mul_comm b a]
        _ = b := by rw [← hFb, ← hq]
        _ = b * 1 := (mul_one _).symm
    have haUnit := IsUnit.of_mul_eq_one q (mul_left_cancel₀ hb0 hb)
    exact hd.ne_top (ha.trans (Ideal.span_singleton_eq_top.mpr haUnit))
  have hcut : P ∈ (D ⊔ Ideal.span {G}).minimalPrimes :=
    ⟨⟨hp, sup_le hDP (le_sup_right.trans hmin.le)⟩, fun J hJ hJP =>
      hmin.2 ⟨hJ.1, sup_le (hD.le.trans (le_sup_left.trans hJ.2))
        (le_sup_right.trans hJ.2)⟩ hJP⟩
  have hsurface :=
    MvPolynomial.natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hD
  rw [Nat.card_fin] at hsurface
  have hcurve := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hGD hcut
  omega
end
end Low6966Leading_1_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Low6966Leading_1_2
noncomputable section
variable {top : Fin 16}
open K1_13 (Row Geom)
open K1_13_5 (separant)
open K1_13_5_4 (GeoRow GeometricX genericRow regularLocus extendedAtJet)
open K1_13_5_4_3 (TangentStable trajectory pointEval taylorAt)
open K1_13_5_4_3_2
open Low6966Prices (physicalDegree taylorLength TrueWeightLE anchorCutoff)
open Low6966Leading_1 (oldCut oldCutIdeal)
open Polynomial
open K1_13_5_4_3_2 (fresh_identity initial_residual)
open K1_13_5_4_3_2 (specialize specialize_trajectory specialize_taylor)
private theorem trajectory_degree {A : Type*} [CommRing A] (k : Geom →+* A) (f : Row 3)
    (U : (Polynomial A)) (hU : U.natDegree ≤ physicalDegree) {D : ℕ} (hf : TrueWeightLE f D) :
    (trajectory k f U).natDegree ≤ D := by
  classical
  rw [trajectory, MvPolynomial.eval₂_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun m hm => (natDegree_mul_le).trans ?_
  apply le_trans _ (hf m hm)
  apply Nat.add_le_add natDegree_map_le
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact natDegree_pow_le_of_le _ ((natDegree_hasseDeriv_le _ _).trans
    (Nat.sub_le_sub_right hU _)) |>.trans_eq (Nat.mul_comm _ _)
theorem stable_taylor {f : Row 3} {P : Ideal (GeoRow 3)}
    (hf : TrueWeightLE f anchorCutoff) (hc : oldCutIdeal f ≤ P)
    (h : TangentStable f P) {y : Fin 3 → GeometricX} (hy : y ∈ regularLocus f P) :
    (taylorAt f (pointEval y)).natDegree ≤ physicalDegree ∧
      extendedAtJet f (taylorAt f (pointEval y)) = 0 := by
  have hrow : genericRow f ∈ P := hc (Ideal.subset_span (by simp))
  have hcut : genericRow (oldCut f) ∈ P := hc (Ideal.subset_span (by simp))
  have hold : K1_13_5_4.oldCutIdeal f ≤ P := by
    apply Ideal.span_le.mpr
    intro b hb
    rcases (show b = genericRow f ∨ b = genericRow (K1_13_5_4.oldCut f) by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hb) with rfl | rfl
    · exact hrow
    · exact numerator_mem h hcut (by decide)
  have hU : (localTaylor f P).natDegree ≤ physicalDegree := by
    rw [localTaylor, natDegree_taylor, natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have hsmall : 3 ≤ j := by
      change 133387 < j at hj
      omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hsmall
    rw [Nat.add_comm 3 n, centred, coeff_jetPolynomial]
    have hn : taylorLength - 3 ≤ n := by
      change 133387 < 3 + n at hj
      change 133385 ≤ n
      omega
    have hz : localJet f P (n + 3) = 0 := by
      rw [localJet, chart_zero f P (numerator_mem h hcut hn), mul_zero, zero_mul, zero_mul]
    split_ifs with hj'
    · exact hz
    · rfl
  refine ⟨by rw [← specialize_taylor hy]; exact natDegree_map_le.trans hU, ?_⟩
  have hOne : delta h (1 : Chart f P) = 0 := by
    simpa only [map_one] using delta_constants h (1 : Geom)
  have hShift : taylor (chartEval f P (MvPolynomial.C Polynomial.X)) (localTaylor f P) =
      centred f P := by
    rw [localTaylor, taylor_taylor, add_neg_cancel, taylor_zero]
  have hidentity := fresh_identity (delta h) hOne (delta_mul h) (constants (chartEval f P))
    (delta_constants h) _ (delta_centre h) f (localTaylor f P) (centred f P) hShift
    (centred_step h hold) (initial_residual hold)
    ((trajectory_degree _ _ _ hU hf).trans_lt (by decide : anchorCutoff < K1.p))
    (fun n hn hp => by
      rw [← map_natCast (constants (chartEval f P))]
      exact (natCast_geom_ne_zero hn hp).isUnit.map _)
  rw [← specialize_trajectory hy, hidentity, Polynomial.map_zero]
end
end Low6966Leading_1_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Low6966Leading_1_2
noncomputable section
variable {top : Fin 16}
open K1_13 (Geom)
open K1_13_5 (RegularAt separant)
open K1_13_5_4 (GeoRow GeometricX extendedAtJet genericCoeff genericCoeff_injective
  genericRow jetPoint regularLocus eval_genericRow_at_point)
open K1_13_5_4_3 (coefficientImage coefficientPolynomial_reconstructAt curveIdeal
  eval_trajectory_at_centre pointEval reconstructAt reconstructAt_mark regularLocus_nonempty
  solves_on_closure taylorAt)
open K1_13_5_4_3_2 (jetPolynomial coeff_jetPolynomial)
open Low6966Prices (physicalDegree taylorLength)
open Low6966Leading_1 (Coefficients coefficientPoint coefficientPolynomial oldCutIdeal mem_properComponents)
open Polynomial MvPolynomial
private theorem length_le : taylorLength ≤ K1_13.taylorLength := by
  change 133388 ≤ 133672
  decide
private def pad {m n : ℕ} (a : Fin m → GeometricX) (i : Fin n) : GeometricX :=
  if h : i.val < m then a ⟨i.val, h⟩ else 0
private def truncate {m n : ℕ} : GeoRow n →ₐ[GeometricX] GeoRow m :=
  aeval fun i => if h : i.val < m then MvPolynomial.X ⟨i.val, h⟩ else 0
private theorem truncate_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (truncate : GeoRow n →ₐ[GeometricX] GeoRow m) := by
  let r := rename (R := GeometricX) (Fin.castLE h)
  have he : truncate.comp r = AlgHom.id GeometricX (GeoRow m) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, rename_X, truncate, MvPolynomial.aeval_X, AlgHom.id_apply]
    exact dite_eq_left i.isLt
  exact fun p => ⟨r p, DFunLike.congr_fun he p⟩
private theorem eval_truncate {m n : ℕ} (a : Fin m → GeometricX) (p : GeoRow n) :
    MvPolynomial.eval a (truncate p) = MvPolynomial.eval (pad a) p := by
  change aeval a (truncate p) = aeval (pad a) p
  rw [truncate, comp_aeval_apply]
  apply congrArg (fun z : Fin n → GeometricX => aeval z p)
  funext i
  unfold pad
  split_ifs <;> simp only [MvPolynomial.aeval_X, map_zero]
private theorem pad_restrict {m n : ℕ} (h : m ≤ n) (a : Fin n → GeometricX)
    (hz : ∀ i : Fin n, m ≤ i.val → a i = 0) : pad (a ∘ Fin.castLE h) = a := by
  funext i
  unfold pad
  split_ifs with hi
  · exact congrArg a (Fin.ext rfl)
  · exact (hz i (Nat.le_of_not_lt hi)).symm
private theorem vanishingIdeal_restrict {m n : ℕ} (h : m ≤ n)
    (C : Set (Fin n → GeometricX)) (hz : ∀ a ∈ C, ∀ i : Fin n, m ≤ i.val → a i = 0) :
    vanishingIdeal GeometricX C =
      (vanishingIdeal GeometricX ((fun a => a ∘ Fin.castLE h) '' C)).comap
        (truncate : GeoRow n →ₐ[GeometricX] GeoRow m).toRingHom := by
  ext p
  constructor
  · intro hp a ha
    obtain ⟨b, hb, rfl⟩ := ha
    change MvPolynomial.eval (b ∘ Fin.castLE h) (truncate p) = 0
    rw [eval_truncate, pad_restrict h b (hz b hb)]
    exact hp b hb
  · intro hp b hb
    have ha := hp (b ∘ Fin.castLE h) ⟨b, hb, rfl⟩
    change MvPolynomial.eval (b ∘ Fin.castLE h) (truncate p) = 0 at ha
    rwa [eval_truncate, pad_restrict h b (hz b hb)] at ha
private theorem polynomial_pad {m n : ℕ} (h : m ≤ n) (a : Fin m → GeometricX) :
    (∑ i : Fin n, Polynomial.monomial i.val (pad a i)) =
      ∑ i : Fin m, Polynomial.monomial i.val (a i) := by
  let c : ℕ → GeometricX := fun j => if hj : j < m then a ⟨j, hj⟩ else 0
  change jetPolynomial n c = _
  have he : (∑ i : Fin m, Polynomial.monomial i.val (a i)) = jetPolynomial m c := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [c, dite_eq_left i.isLt, Fin.eta]
  rw [he]
  ext j
  simp only [coeff_jetPolynomial]
  by_cases hj : j < m
  · rw [ite_eq_left hj, ite_eq_left (hj.trans_le h)]
  · simp [c, hj]
theorem proof : Low6966Leading_1.c2 top := by
  intro n f hf a ha hs
  rcases a with ⟨i, P⟩
  obtain ⟨hw, hm⟩ := mem_properComponents.mp ha
  obtain ⟨hmin, hsep⟩ := Ideal.mem_retainedMinimalPrimes.mp hm
  have hp := hmin.isPrime
  have hle := hmin.le
  have hstable := tangent_stable hp hle hsep hs
  have hdim := component_dimension (hf.irreducible i) hw hm
  obtain ⟨hprime, hcurve⟩ :=
    K1_13_5_4_3_4.proof (f i) P hp hsep hdim
  have hTaylor := fun y hy => stable_taylor (hf.weight i) hle hstable (y := y) hy
  let C := coefficientImage (f i) P
  let Q := vanishingIdeal GeometricX ((fun b => b ∘ Fin.castLE length_le) '' C)
  have hz : ∀ b ∈ C, ∀ j : Fin K1_13.taylorLength, taylorLength ≤ j.val → b j = 0 := by
    rintro b ⟨y, hy, rfl⟩ j hj
    exact coeff_eq_zero_of_natDegree_lt ((hTaylor y hy).1.trans_lt (Nat.lt_of_succ_le hj))
  let T : GeoRow K1_13.taylorLength →ₐ[GeometricX] GeoRow taylorLength := truncate
  have hT : Function.Surjective T := truncate_surjective length_le
  have hQ : curveIdeal (f i) P = Q.comap T.toRingHom :=
    vanishingIdeal_restrict length_le C hz
  have hQprime : Q.IsPrime := by
    have hker : RingHom.ker T.toRingHom ≤ curveIdeal (f i) P := by
      rw [hQ]
      intro p hp'
      change T p = 0 at hp'
      change T p ∈ Q
      rw [hp']
      exact Q.zero_mem
    let := hprime
    have hmap := Ideal.map_isPrime_of_surjective (f := T.toRingHom) hT hker
    rwa [hQ, Ideal.map_comap_of_surjective T.toRingHom hT] at hmap
  have hQdim : (affineHilbertPolynomial Q).natDegree = 1 := by
    rw [hQ] at hcurve
    change (affineHilbertPolynomial (Q.comap T)).natDegree = 1 at hcurve
    rwa [natDegree_affineHilbertPolynomial_comap_of_surjective T hT Q] at hcurve
  have hmem (b : K1_13_5_4.Coefficients) (hb : b ∈ C) :
      b ∘ Fin.castLE length_le ∈ zeroLocus GeometricX Q :=
    zeroLocus_vanishingIdeal_le _ ⟨b, hb, rfl⟩
  have hpoly (b : Coefficients) :
      K1_13_5_4.coefficientPolynomial (pad b) = coefficientPolynomial b :=
    polynomial_pad length_le b
  refine ⟨Q, ⟨hQprime, hQdim, ?_, ?_⟩, ?_⟩
  · intro b hb
    have hpad : pad b ∈ zeroLocus GeometricX (curveIdeal (f i) P) := by
      intro p hp'
      change MvPolynomial.eval (pad b) p = 0
      rw [← eval_truncate]
      exact hb (T p) (by rw [hQ] at hp'; exact hp')
    rw [← hpoly b]
    exact solves_on_closure _ _ (fun y hy => (hTaylor y hy).2) _ hpad
  · obtain ⟨y, hy⟩ := regularLocus_nonempty (f i) P hp hsep
    let b := reconstructAt (f i) y
    have hb : b ∈ C := ⟨y, hy, rfl⟩
    refine ⟨b ∘ Fin.castLE length_le, hmem b hb, ?_⟩
    rw [← hpoly, pad_restrict length_le b (hz b hb), coefficientPolynomial_reconstructAt]
    intro hzero
    apply hy.2
    rw [← eval_trajectory_at_centre (f i), hzero, Polynomial.eval_zero]
  · intro S hS hy
    have hfP : genericRow (f i) ∈ P := hle (Ideal.subset_span (by simp))
    have he : MvPolynomial.eval (jetPoint S) (genericRow (f i)) = 0 := hy.1 _ hfP
    have hn : MvPolynomial.eval (jetPoint S) (genericRow (separant (f i))) ≠ 0 := hy.2
    rw [eval_genericRow_at_point] at he hn
    have hr : RegularAt 2 (f i) S :=
      ⟨genericCoeff_injective (he.trans genericCoeff.map_zero.symm),
        fun h => hn (by rw [show K1_13.atJet (separant (f i)) S = 0 from h, map_zero])⟩
    have hS' : S.natDegree ≤ 133671 := hS.trans (by change 133387 ≤ 133671; decide)
    have hres := hmem (reconstructAt (f i) (jetPoint S)) ⟨jetPoint S, hy, rfl⟩
    rw [reconstructAt_mark (f i) S hS' hr] at hres
    exact hres
end
end Low6966Leading_1_2
end
section
set_option autoImplicit false
namespace Low6966Leading_1_3
noncomputable section
variable {top : Fin 16}
open K1_13_5_4 (GeometricX)
open MvPolynomial
open scoped BigOperators
open P0_9_5_1_4 (restrictVariables restrict_rename padded_hilbert sum_monomial_eq_of_tail_zero)
theorem length_le : Low6966Prices.taylorLength ≤ K1_13.taylorLength := by decide
private def dropCoefficients : K1_13_5_4.GeoRow K1_13.taylorLength →ₐ[GeometricX]
    K1_13_5_4.GeoRow Low6966Prices.taylorLength :=
  MvPolynomial.aeval restrictVariables
def pad (Q : Low6966Leading_1.CoefficientIdeal) : K1_13_5_4.CoefficientIdeal :=
  Q.comap dropCoefficients
theorem pad_injective : Function.Injective pad :=
  Ideal.comap_injective_of_surjective dropCoefficients
    (fun p => ⟨rename (Fin.castLE length_le) p, restrict_rename length_le p⟩)
theorem pad_hilbert (Q : Low6966Leading_1.CoefficientIdeal) :
    affineHilbertPolynomial (pad Q) = affineHilbertPolynomial Q :=
  padded_hilbert length_le Q
theorem pad_degree (Q : Low6966Leading_1.CoefficientIdeal) :
    affineDegree (pad Q) = affineDegree Q := by
  unfold affineDegree
  rw [pad_hilbert]
theorem pad_points {Q : Low6966Leading_1.CoefficientIdeal} {b : K1_13_5_4.Coefficients}
    (hb : b ∈ zeroLocus GeometricX (pad Q)) :
    let a := b ∘ Fin.castLE length_le
    a ∈ zeroLocus GeometricX Q ∧
      K1_13_5_4.coefficientPolynomial b = Low6966Leading_1.coefficientPolynomial a := by
  dsimp only
  constructor
  · intro p hp
    have hv := hb (rename (Fin.castLE length_le) p)
      (show dropCoefficients (rename (Fin.castLE length_le) p) ∈ Q from
        (restrict_rename length_le p).symm ▸ hp)
    change eval b (rename (Fin.castLE length_le) p) = 0 at hv
    rwa [eval_rename] at hv
  · apply sum_monomial_eq_of_tail_zero length_le
    intro i hi
    have hx : MvPolynomial.X i ∈ pad Q := by
      change dropCoefficients (MvPolynomial.X i) ∈ Q
      simp [dropCoefficients, restrictVariables, Nat.not_lt.mpr hi]
    exact (eval_X (f := b) i).symm.trans (hb _ hx)
private def paddedPoint (a : Low6966Leading_1.Coefficients) : K1_13_5_4.Coefficients :=
  fun i => if hi : i.val < Low6966Prices.taylorLength then a ⟨i.val, hi⟩ else 0
private theorem eval_paddedPoint (a : Low6966Leading_1.Coefficients) :
    MvPolynomial.aeval (paddedPoint a) =
      (MvPolynomial.aeval a).comp dropCoefficients := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i.val < Low6966Prices.taylorLength <;>
    simp [dropCoefficients, restrictVariables, paddedPoint, hi]
theorem pad_actual {f : K1_13.Row 3} {Q : Low6966Leading_1.CoefficientIdeal}
    (h : Low6966Leading_1.ActualSolutionCurve f Q) : K1_13_5_4.ActualSolutionCurve f (pad Q) := by
  refine ⟨h.prime.comap dropCoefficients, ?_, ?_, ?_⟩
  · rw [pad_hilbert]
    exact h.dimension
  · intro b hb
    obtain ⟨ha, he⟩ := pad_points hb
    rw [he]
    exact h.solves _ ha
  · obtain ⟨a, ha, hs⟩ := h.regular
    have hb : paddedPoint a ∈ zeroLocus GeometricX (pad Q) := by
      intro p hp
      exact (DFunLike.congr_fun (eval_paddedPoint a) p).trans (ha _ hp)
    obtain ⟨_, he⟩ := pad_points hb
    exact ⟨paddedPoint a, hb, by
      have hrestrict : paddedPoint a ∘ Fin.castLE length_le = a := by
        funext i
        simp [paddedPoint, i.isLt]
      rw [he, hrestrict]
      exact hs⟩
end
end Low6966Leading_1_3
end
section
set_option autoImplicit false
namespace Low6966Leading_1_3
noncomputable section
variable {top : Fin 16}
open K1_13 (Geom Row embed)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX extendedAtJet)
open K1_13_5_4_4
open Low6966Prices (taylorLength)
open Low6966Leading (Whole invariantBudget)
open Low6966Leading_1 (CoefficientIdeal ActualSolutionCurve coefficientPolynomial oldCut)
open MvPolynomial Finset
open scoped BigOperators Polynomial
open K1_13_5_4_4 (flat_of_injective regular_cut_of_flat_map)
open K1_13_5_4_4 (curve_minimal)
private theorem donorCharts : K1_13_5_4_4.c1 :=
  K1_13_5_4_4_1.of_children K1_13_5_4_4_1_1.proof K1_13_5_4_4_1_2.proof
private def projectedIdeal (Q : CoefficientIdeal) : FreshJetIdeal := freshImage (pad Q)
private def retunedDivisor (f : Row 3) : FreshJetIdeal :=
  freshHypersurface f ⊔ Ideal.span {freshRow (oldCut f)}
private theorem compatibility_zero (f : Row 3) (S : (Polynomial GeometricX)) (k : ℕ)
    (hk : k + 3 ≤ K1_13.taylorLength) (hS : S.natDegree < k + 3)
    (hf : extendedAtJet f S = 0) : extendedAtJet (K1_13_5.compatibilityNumerator f k) S = 0 := by
  have h := K1_13_5_4_4_1_2.proof f S (hS.trans_le hk) hf k hk
  rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree S (k + 3) hS, mul_zero, mul_zero] at h
  have htwo : (2 : (Polynomial GeometricX)) ≠ 0 := by
    let g : K1.K →+* (Polynomial GeometricX) :=
      Polynomial.C.comp ((algebraMap Geom GeometricX).comp embed)
    have hne : (2 : K1.K) ≠ 0 := by decide
    exact fun hz => hne (g.injective (by simpa only [map_ofNat, map_zero] using hz))
  exact (mul_eq_zero.mp h).resolve_left htwo
private theorem cut_zero (f : Row 3) (S : (Polynomial GeometricX))
    (hS : S.natDegree < taylorLength) (hf : extendedAtJet f S = 0) :
    extendedAtJet (oldCut f) S = 0 := by
  have hk : taylorLength - 3 + 3 = taylorLength := rfl
  change extendedAtJet (K1_13_5.compatibilityNumerator f (taylorLength - 3)) S = 0
  exact compatibility_zero f S _ (hk.le.trans length_le) (hk.symm ▸ hS) hf
private theorem projected_on_divisor {f : Row 3} {Q : CoefficientIdeal}
    (h : ActualSolutionCurve f Q) : retunedDivisor f ≤ projectedIdeal Q := by
  have hold := pad_actual h
  have hrow : freshHypersurface f ≤ projectedIdeal Q :=
    le_sup_left.trans (((donorCharts f).1 (pad Q) hold).on_divisor)
  refine sup_le hrow ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  change freshProjection (freshRow (oldCut f)) ∈ extendIdeal (pad Q)
  rw [(K1_13_5_4_4_1_1.proof (pad Q) hold.prime).2]
  intro b hb
  obtain ⟨ha, he⟩ := pad_points hb
  have hdeg (a : Low6966Leading_1.Coefficients) : (coefficientPolynomial a).natDegree < taylorLength := by
    apply Nat.lt_succ_of_le
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt j.isLt)
  rw [K1_13_5_4_4_1.point_projected, K1_13_5_4_4_1.eval_row, he,
    cut_zero f _ (hdeg _) (h.solves _ ha), map_zero]
private theorem projected_comparison {f : Row 3} {Q : CoefficientIdeal}
    (h : ActualSolutionCurve f Q) :
    (projectedIdeal Q).IsPrime ∧ (affineHilbertPolynomial (projectedIdeal Q)).natDegree = 1 ∧
      affineDegree Q ≤ affineDegree (projectedIdeal Q) := by
  have hold := pad_actual h
  have hc := (donorCharts f).1 (pad Q) hold
  obtain ⟨hdim, hdeg⟩ := K1_13_5_4_4_2.proof (pad Q) hold.prime hold.dimension
    hc.extended_prime hc.birational
  exact ⟨hc.extended_prime.comap freshProjection, hdim, (pad_degree Q).symm.trans_le hdeg⟩
private theorem retunedCut_regular {f : Row 3} (hf : Irreducible f) (hw : ¬ Whole f) :
    IsLeftRegular (Ideal.Quotient.mk (freshHypersurface f) (freshRow (oldCut f))) := by
  letI : (Ideal.span {f} : Ideal (Row 3)).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hc : oldCut f ∉ (Ideal.span {f} : Ideal (Row 3)) :=
    fun h => hw (Ideal.mem_span_singleton.mp h)
  apply regular_cut_of_flat_map freshCoeff (flat_of_injective freshCoeff freshCoeff_injective)
  · exact fun _ _ h => mul_left_cancel₀ hf.ne_zero h
  · exact fun _ _ h => mul_left_cancel₀ (mt Ideal.Quotient.eq_zero_iff_mem.mp hc) h
private theorem factor_degree_sum (f : Row 3) (hf : Irreducible f) (hw : ¬ Whole f)
    (T : Finset FreshJetIdeal)
    (hT : ∀ Q ∈ T, Q.IsPrime ∧ retunedDivisor f ≤ Q ∧
      (affineHilbertPolynomial Q).natDegree = 1) :
    (∑ Q ∈ T, affineDegree Q) ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
  classical
  by_cases hEmpty : T = ∅
  · rw [hEmpty, sum_empty]
    positivity
  have hPproper : freshHypersurface f ≠ ⊤ := by
    obtain ⟨Q, hQ⟩ := nonempty_iff_ne_empty.mpr hEmpty
    exact ne_top_of_le_ne_top (hT Q hQ).1.ne_top
      (le_sup_left.trans (hT Q hQ).2.1)
  have hPdim : (affineHilbertPolynomial (freshHypersurface f)).natDegree = 2 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      (freshRow_ne_zero hf.ne_zero) hPproper
    rw [Nat.card_fin] at h
    change (affineHilbertPolynomial (freshHypersurface f)).natDegree + 1 = 3 at h
    omega
  have hcut := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (retunedCut_regular hf hw) (freshRow_degree_le (oldCut f))
  rw [hPdim] at hcut
  have hJdim : (affineHilbertPolynomial (retunedDivisor f)).natDegree ≤ 1 := hcut.1
  have hsub : T ⊆ (retunedDivisor f).minimalPrimesFinset := by
    intro Q hQ
    obtain ⟨hp, hle, hdim⟩ := hT Q hQ
    exact Ideal.mem_minimalPrimesFinset.mpr (curve_minimal hp hle hJdim hdim)
  have hdeg : affineDegree (freshHypersurface f) ≤ (f.totalDegree : ℚ) := by
    rw [freshHypersurface, affineDegree_span_singleton (freshRow_ne_zero hf.ne_zero)]
    exact_mod_cast freshRow_degree_le f
  calc
    (∑ Q ∈ T, affineDegree Q) = ∑ Q ∈ T, (affineHilbertPolynomial Q).coeff 1 := by
      apply sum_congr rfl
      intro Q hQ
      rw [affineDegree, (hT Q hQ).2.2, Polynomial.leadingCoeff, (hT Q hQ).2.2]
      simp
    _ ≤ ∑ Q ∈ (retunedDivisor f).minimalPrimesFinset, (affineHilbertPolynomial Q).coeff 1 := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro Q hQ _
      have hle := (Ideal.mem_minimalPrimesFinset.mp hQ).le
      exact Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
        ((natDegree_affineHilbertPolynomial_le_of_le hle).trans hJdim)
        (eventually_eval_affineHilbertPolynomial_nonneg Q)
    _ ≤ (affineHilbertPolynomial (retunedDivisor f)).coeff 1 :=
      sum_coeff_affineHilbertPolynomial_minimalPrimes_le _ hJdim
    _ ≤ ((oldCut f).totalDegree : ℚ) * affineDegree (freshHypersurface f) := by
      simpa [retunedDivisor, affineDegree, hPdim, mul_assoc] using hcut.2
    _ ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
      rw [Nat.cast_mul, mul_comm (f.totalDegree : ℚ)]
      exact mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _)
private theorem curve_family_bound (f : Row 3) (hf : Irreducible f) (hw : ¬ Whole f)
    (C : Finset CoefficientIdeal) (hC : ∀ Q ∈ C, ActualSolutionCurve f Q) :
    (∑ Q ∈ C, affineDegree Q) ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
  classical
  have hinj : Set.InjOn projectedIdeal (C : Set CoefficientIdeal) := by
    intro Q hQ R hR he
    exact pad_injective ((donorCharts f).2 (pad_actual (hC Q hQ)) (pad_actual (hC R hR)) he)
  calc
    (∑ Q ∈ C, affineDegree Q) ≤ ∑ Q ∈ C, affineDegree (projectedIdeal Q) :=
      sum_le_sum fun Q hQ => (projected_comparison (hC Q hQ)).2.2
    _ = ∑ P ∈ C.image projectedIdeal, affineDegree P := (sum_image hinj).symm
    _ ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
      apply factor_degree_sum f hf hw
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hP
      have hc := projected_comparison (hC Q hQ)
      exact ⟨hc.1, projected_on_divisor (hC Q hQ), hc.2.1⟩
private def cutterBound (b : ℕ) : ℕ :=
  1 + (2 * (taylorLength + 1) - 7) * (b - 1)
private theorem cutterBound_mono : Monotone cutterBound := by
  intro a b hab
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hab _)) _
theorem proof : Low6966Leading_1.c3 top := by
  classical
  intro n f hf hcut C hsource
  by_cases hEmpty : C = ∅
  · subst C
    exact ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨Q₀, hQ₀⟩ := nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨i₀, _⟩ := hsource Q₀ hQ₀
  let pick (Q : CoefficientIdeal) : Fin n :=
    if hQ : Q ∈ C then Classical.choose (hsource Q hQ) else i₀
  have hpick (Q : CoefficientIdeal) (hQ : Q ∈ C) :
      ¬ Whole (f (pick Q)) ∧ ActualSolutionCurve (f (pick Q)) Q := by
    simpa only [pick, dite_eq_left hQ] using Classical.choose_spec (hsource Q hQ)
  let part (i : Fin n) := C.filter fun Q => pick Q = i
  have hlocal (i : Fin n) : (∑ Q ∈ part i, affineDegree Q) ≤
      ((f i).totalDegree * (oldCut (f i)).totalDegree : ℕ) := by
    have hpart (Q : CoefficientIdeal) (hQ : Q ∈ part i) :
        ¬ Whole (f i) ∧ ActualSolutionCurve (f i) Q := by
      obtain ⟨hm, hi⟩ := mem_filter.mp hQ
      simpa only [hi] using hpick Q hm
    by_cases hw : Whole (f i)
    · have he : part i = ∅ := eq_empty_iff_forall_notMem.mpr fun Q hQ => (hpart Q hQ).1 hw
      rw [he, sum_empty]
      positivity
    exact curve_family_bound _ (hf.irreducible i) hw _ fun Q hQ => (hpart Q hQ).2
  have hnat : (∑ i : Fin n, (f i).totalDegree * (oldCut (f i)).totalDegree) ≤ (invariantBudget top) := by
    calc
      _ ≤ ∑ i : Fin n, (f i).totalDegree * cutterBound (Low6966Prices.lowerWidth top) := by
        apply sum_le_sum
        intro i _
        have hi := (single_le_sum (f := fun j => (f j).totalDegree)
          (fun _ _ => Nat.zero_le _) (mem_univ i)).trans hf.total
        exact Nat.mul_le_mul_left _ ((hcut i).trans (cutterBound_mono hi))
      _ = (∑ i : Fin n, (f i).totalDegree) * cutterBound (Low6966Prices.lowerWidth top) := by rw [sum_mul]
      _ ≤ (invariantBudget top) := Nat.mul_le_mul_right _ hf.total
  have hsum : (∑ Q ∈ C, affineDegree Q) ≤ ((invariantBudget top) : ℚ) := by
    calc
      _ = ∑ i : Fin n, ∑ Q ∈ part i, affineDegree Q :=
        (sum_fiberwise_of_maps_to (t := (univ : Finset (Fin n)))
          (g := pick) (fun _ _ => mem_univ _) affineDegree).symm
      _ ≤ ∑ i : Fin n, (((f i).totalDegree * (oldCut (f i)).totalDegree : ℕ) : ℚ) :=
        sum_le_sum fun i _ => hlocal i
      _ ≤ ((invariantBudget top) : ℚ) := by exact_mod_cast hnat
  have hex (Q : CoefficientIdeal) : ∃ d : ℕ, Q ∈ C → 0 < d ∧ affineDegree Q = (d : ℚ) := by
    by_cases hQ : Q ∈ C
    · have h := (hpick Q hQ).2
      have hp := pad_actual h
      obtain ⟨d, hd, he⟩ := curve_degree_nat (pad Q) hp.prime hp.dimension
      exact ⟨d, fun _ => ⟨hd, (pad_degree Q).symm.trans he⟩⟩
    · exact ⟨0, fun h => False.elim (hQ h)⟩
  let d (Q : CoefficientIdeal) := Classical.choose (hex Q)
  have hd (Q : CoefficientIdeal) (hQ : Q ∈ C) : 0 < d Q ∧ affineDegree Q = (d Q : ℚ) :=
    Classical.choose_spec (hex Q) hQ
  refine ⟨d, fun Q hQ => ⟨(hd Q hQ).1, (hd Q hQ).2.le⟩, ?_⟩
  have hcast : (∑ Q ∈ C, (d Q : ℚ)) ≤ ((invariantBudget top) : ℚ) :=
    (sum_congr rfl fun Q hQ => (hd Q hQ).2.symm).trans_le hsum
  exact_mod_cast hcast
end
end Low6966Leading_1_3
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace Low6966Leading_2
noncomputable section
variable {top : Fin 16}
open P3 (K I node)
open Low6966Prices (Messages)
open K1_13 (Geom embed extend taylorLength)
open K1_13_5 (NodeCapacity)
open K1_13_5_5 (CoeffRing CoeffIndex coeffPoint)
open Finset MvPolynomial
open scoped BigOperators Polynomial
open K1_13_5_5 (valueCut valueCut_degree valueCut_eval nodeCapacity_of_sections curve_degree_nat)
private theorem coeffPoint_injOn {w Γ s} (h : Messages w Γ s) :
    Set.InjOn (fun γ => coeffPoint (extend (s γ))) (Γ : Set K) := by
  intro γ hγ η hη heq
  apply h.distinct hγ hη
  apply Polynomial.ext
  intro j
  by_cases hj : j < taylorLength
  · exact embed.injective (by simpa [coeffPoint] using congrFun heq ⟨j, hj⟩)
  · change ¬ j < 133672 at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := s γ) (by
          have hdeg : (s γ).natDegree ≤ 133387 := h.degree γ hγ
          omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (p := s η) (by
          have hdeg : (s η).natDegree ≤ 133387 := h.degree η hη
          omega)]
private theorem zeroDim_count {w Γ s} (h : Messages w Γ s) (P : Ideal CoeffRing)
    (hdim : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P) :
    (Γ.card : ℚ) ≤ affineDegree P := by
  classical
  let A := Γ.image (fun γ => coeffPoint (extend (s γ)))
  have hA : A.card = Γ.card := card_image_of_injOn (coeffPoint_injOn h)
  have hsub : (A : Set _) ⊆ zeroLocus Geom P := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := Geom) P hdim
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hA] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree
private theorem section_count {w Γ s} (h : Messages w Γ s) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P)
    (x a : K) (hmiss : ∃ γ ∈ Γ, (s γ).eval x ≠ a)
    {c : ℚ} (hc : 0 ≤ c)
    (bound : ∀ (V : Finset K), V ⊆ Γ → ∀ (Q : Ideal CoeffRing), Q.IsPrime →
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V, coeffPoint (extend (s γ)) ∈ zeroLocus Geom Q) →
      (V.card : ℚ) ≤ c * affineDegree Q) :
    ((Γ.filter fun γ => (s γ).eval x = a).card : ℚ) ≤ c * affineDegree P := by
  classical
  let prime := hP
  let cut := valueCut x a
  let Ps := (P ⊔ Ideal.span {cut}).minimalPrimesFinset
  let U := Γ.filter fun γ => (s γ).eval x = a
  let part (Q : Ideal CoeffRing) := U.filter fun γ => coeffPoint (extend (s γ)) ∈ zeroLocus Geom Q
  have hdegree (γ : K) (hγ : γ ∈ Γ) : (s γ).natDegree ≤ 133671 :=
    (h.degree γ hγ).trans (by decide : 133387 ≤ 133671)
  have hproper : cut ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hm
    exact hv ((valueCut_eval (hdegree γ hγ) x a).mp (hpoints γ hγ _ hm))
  have hcover : U ⊆ Ps.biUnion part := by
    intro γ hγ
    obtain ⟨hγΓ, hv⟩ := mem_filter.mp hγ
    have hp : coeffPoint (extend (s γ)) ∈ zeroLocus Geom (P ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγΓ, (valueCut_eval (hdegree γ hγΓ) x a).mpr hv⟩
    obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact mem_biUnion.mpr ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  have hsum : U.card ≤ ∑ Q ∈ Ps, (part Q).card :=
    (card_le_card hcover).trans card_biUnion_le
  have hdeg : (∑ Q ∈ Ps, affineDegree Q) ≤ affineDegree P := by
    simpa only [Ps, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCut_degree x a)
  change (U.card : ℚ) ≤ c * affineDegree P
  calc
    _ ≤ ∑ Q ∈ Ps, ((part Q).card : ℚ) := by exact_mod_cast hsum
    _ ≤ ∑ Q ∈ Ps, c * affineDegree Q := by
      apply sum_le_sum
      intro Q hQ
      have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
      exact bound _ ((filter_subset _ _).trans (filter_subset _ _)) Q hmin.isPrime
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ => (mem_filter.mp hγ).2)
    _ ≤ c * affineDegree P := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hdeg hc
private theorem curve_count {w Γ s} (h : Messages w Γ s) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hdim : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P) :
    (Γ.card : ℚ) ≤ 2 * affineDegree P := by
  classical
  obtain ⟨δ, hδ, hdeg⟩ := curve_degree_nat P hP hdim
  have hcap : NodeCapacity w Γ s δ := by
    apply nodeCapacity_of_sections
    intro i hi
    have hcount := section_count h hP hpoints (node i) (w i) hi (c := 1) zero_le_one
      (fun V hV Q _ hQ hp => by
        rw [one_mul]
        exact zeroDim_count (h.mono hV) Q (by omega) hp)
    rw [one_mul, hdeg] at hcount
    exact_mod_cast hcount
  have hcount := Low6966Leading.nodeCapacity_count h hcap
  have hi : Γ.card ≤ 2 * δ := by omega
  rw [hdeg]
  exact_mod_cast hi
theorem surface_nodeCapacity {w Γ s} {d : ℕ} (h : Messages w Γ s) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hdim : (affineHilbertPolynomial P).natDegree = 2)
    (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P)
    (hd : 2 * affineDegree P ≤ (d : ℚ)) :
    NodeCapacity w Γ s d := by
  classical
  apply nodeCapacity_of_sections
  intro i hi
  have hcount := section_count h hP hpoints (node i) (w i) hi (c := 2) (by norm_num)
    (fun _ hV _ hQ hdimQ hp => curve_count (h.mono hV) hQ (by omega) hp)
  exact_mod_cast hcount.trans hd
end
end Low6966Leading_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Low6966Leading_2
noncomputable section
variable {top : Fin 16}
open K1_13 (Geom embed Row atJet)
open K1_13_5 (RegularAt separant compatibilityNumerator)
open K1_13_5_5 K1_13_5_5_1
open Low6966Prices (taylorLength physicalDegree TrueWeightLE anchorCutoff)
open Low6966Leading (Whole)
open scoped Polynomial
open P0_9_5_2 (chart_trajectory)
def LowSupport (P : Ideal CoeffRing) : Prop :=
  ∀ i : CoeffIndex, taylorLength ≤ i.val → MvPolynomial.X i ∈ P
private theorem degree_trajectory {F : Type} [Field F] (k : Geom →+* F) {U : (Polynomial F)}
    (hU : U.natDegree < taylorLength) (f : Row 3) (hf : TrueWeightLE f anchorCutoff) :
    (trajectory k U f).natDegree ≤ anchorCutoff := by
  classical
  unfold trajectory
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hprod : (∏ i ∈ m.support, Polynomial.hasseDeriv i.val U ^ m i).natDegree ≤
      m.sum (fun i e => (physicalDegree - i.val) * e) := by
    unfold Finsupp.sum
    apply (Polynomial.natDegree_prod_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    change ((Polynomial.hasseDeriv i.val U) ^ m i).natDegree ≤ (physicalDegree - i.val) * m i
    rw [Nat.mul_comm]
    exact Polynomial.natDegree_pow_le_of_le _ ((Polynomial.natDegree_hasseDeriv_le U i.val).trans
      (Nat.sub_le_sub_right (Nat.le_of_lt_succ hU) _))
  exact (Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_map_le hprod).trans (hf m hm)
private theorem separant_regular_contracted (f : Row 3) (hf : Irreducible f) (hd : 0 < f.degreeOf 2)
    (hmax : f.degreeOf 2 ≤ 29) : freshRow (separant f) ∉ chartIdeal f := by
  change separant f ∉ (chartIdeal f).comap rowMap
  rw [chart_contract f hf hd]
  have : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  have : CharP (Polynomial Geom) K1.p :=
    charP_of_injective_ringHom Polynomial.C_injective K1.p
  have hcast : (f.degreeOf 2 : (Polynomial Geom)) ≠ 0 := by
    intro h
    have hp := (CharP.cast_eq_zero_iff (Polynomial Geom) K1.p (f.degreeOf 2)).mp h
    exact (not_le_of_gt (hmax.trans_lt (by decide : 29 < K1.p))) (Nat.le_of_dvd hd hp)
  have hsep : separant f ≠ 0 := MvPolynomial.pderiv_ne_zero_of_natCast_ne_zero 2 f hcast
  intro hmem
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hmem
  have hgn : g ≠ 0 := by
    intro he
    exact hsep (by simpa [he] using hg)
  have hdeg := MvPolynomial.degreeOf_pderiv_le_sub_one 2 f
  have h := congrArg (MvPolynomial.degreeOf (2 : Fin 3)) hg
  rw [MvPolynomial.degreeOf_mul_eq hf.ne_zero hgn] at h
  change (separant f).degreeOf 2 ≤ f.degreeOf 2 - 1 at hdeg
  omega
theorem chart_of_whole (f : Row 3) (hf : Irreducible f)
    (hd : 0 < f.degreeOf 2) (hmax : f.degreeOf 2 ≤ 29)
    (hw : TrueWeightLE f anchorCutoff) (hwhole : Whole f) :
    ∃ P : Ideal CoeffRing, FreshChart P (freshRow f) (freshRow (separant f)) ∧
      LowSupport P ∧ ∀ S : (Polynomial Geom), S.natDegree ≤ physicalDegree → RegularAt 2 f S →
        coeffPoint S ∈ MvPolynomial.zeroLocus Geom P := by
  let hp : (chartIdeal f).IsPrime := chart_prime f hf hd
  have hs := separant_regular_contracted f hf hd hmax
  have hweight (U : (Polynomial (ChartField f))) (hU : U.natDegree < taylorLength) :
      (trajectory (chartConstants f) U f).natDegree < K1.p :=
    (degree_trajectory _ hU f hw).trans_lt (by decide : anchorCutoff < K1.p)
  obtain ⟨U, hsmall, hsol, hinit⟩ :=
    chart_trajectory f taylorLength (by decide) (by decide) hs hweight hwhole
  have length_le : taylorLength ≤ K1_13.taylorLength := by decide
  have hU := hsmall.trans_le length_le
  obtain ⟨m, v, hv⟩ := K1_13_5_5_1_1.proof f
  let k := chartConstants f
  let point : CoeffIndex → ChartField f := fun a => U.coeff a.val
  let P := RingHom.ker (coeffEval k point)
  have hbase := freshIdeal_eq_ker k point
  have himage := freshJetEval_ker f hf hd U hU hsol hinit
  have hD : onChart f (freshRow (separant f)) ≠ 0 :=
    fun h => hs ((onChart_eq_zero f _).mp h)
  have hUreg : trajectory k U (separant f) ≠ 0 := by
    intro hz
    have h := eval_trajectory k U (chartCenter f) (separant f)
    rw [hz, Polynomial.eval_zero, hinit, rowAt_chart] at h
    exact hD h.symm
  refine ⟨P, ⟨RingHom.ker_isPrime _, ?_, ?_, hs, ?_⟩, ?_, ?_⟩
  · exact fun h => hf.ne_zero (rowMap_injective (h.trans (map_zero _).symm))
  · change (freshIdeal P).comap freshProjection.toRingHom = chartIdeal f
    rw [hbase, RingHom.comap_ker]
    exact himage
  · intro a
    refine ⟨freshRow (v a), m, ?_⟩
    have hU' : (U.map (newConstants : ChartField f →+* NewField (ChartField f))).natDegree <
        K1_13.taylorLength := Polynomial.natDegree_map_le.trans_lt hU
    have hsol' : trajectory (newConstants.comp k) (U.map newConstants) f = 0 := by
      rw [← map_trajectory, hsol, Polynomial.map_zero]
    have hs' : rowAt (newConstants.comp k) newCenter
        (jetAt newCenter (U.map newConstants)) (separant f) ≠ 0 := by
      rw [newTrajectory_eval]
      exact fun h => hUreg ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
    have h := hv (NewField (ChartField f)) (newConstants.comp k) (U.map newConstants) newCenter
      hU' hsol' hs' a
    rw [newTrajectory_eval, newTrajectory_eval, Polynomial.coeff_map,
      ← freshJetEval_row k U hU, ← freshJetEval_row k U hU] at h
    exact fresh_recovered_mem k U a m _ _ h
  · intro a ha
    change coeffEval k point (MvPolynomial.X a) = 0
    rw [coeffEval, MvPolynomial.eval₂Hom_X']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hsmall.trans_le ha)
  · intro S hS hreg
    let e : FreshJetRing →+* ChartField f := onChart f
    let g : FreshJetRing →+* FreshField :=
      MvPolynomial.eval (jetAt freshCenter (S.map freshConstants))
    let b : Geom →+* FreshJetRing := MvPolynomial.C.comp freshConstants
    have hg (q : Row 3) : g (freshRow q) = algebraMap (Polynomial Geom) FreshField (atJet q S) := by
      rw [← actual_eval, actual_eval_fresh]
      rfl
    have hreg' : g (freshRow (separant f)) ≠ 0 := by
      rw [hg]
      exact fun h => hreg.2 ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
    have hker : RingHom.ker e ≤ RingHom.ker g := by
      rw [show RingHom.ker e = chartIdeal f by
        ext q
        exact onChart_eq_zero f q]
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker, hg, hreg.1, map_zero]
    have hS' : (S.map freshConstants).natDegree < K1_13.taylorLength :=
      Polynomial.natDegree_map_le.trans_lt ((Nat.lt_succ_of_le hS).trans_le length_le)
    have hsolS : trajectory freshConstants (S.map freshConstants) f = 0 := by
      simpa only [trajectory_actual, hreg.1, Polynomial.map_zero, RingHom.comp_id] using
        (map_trajectory (RingHom.id Geom) freshConstants S f).symm
    have hrecU (a : CoeffIndex) :
        e (freshRow (separant f)) ^ m * point a = e (freshRow (v a)) := by
      have hc := hv (ChartField f) k U (chartCenter f) hU hsol
        (by rwa [hinit, rowAt_chart]) a
      rwa [hinit, rowAt_chart] at hc
    have hrecS (a : CoeffIndex) :
        g (freshRow (separant f)) ^ m * freshConstants (S.coeff a.val) = g (freshRow (v a)) := by
      have hc := hv FreshField freshConstants (S.map freshConstants) freshCenter hS' hsolS
        (by rwa [actual_eval_fresh]) a
      rwa [actual_eval_fresh, Polynomial.coeff_map] at hc
    have hle := eval_kernel_le_of_cleared b e g hker (freshRow (separant f)) m
      (fun a => freshRow (v a)) hD hreg' point (freshConstants ∘ coeffPoint S) hrecU hrecS
    intro q hq
    have hz := hle hq
    change MvPolynomial.eval₂Hom (g.comp b) (freshConstants ∘ coeffPoint S) q = 0 at hz
    have hqmap : MvPolynomial.eval₂Hom (g.comp b) (freshConstants ∘ coeffPoint S) =
        freshConstants.comp (MvPolynomial.aeval (coeffPoint S)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [b, g]
      · intro a
        simp
    rw [hqmap] at hz
    exact freshConstants.injective (hz.trans (map_zero _).symm)
end
end Low6966Leading_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Low6966Leading_2
noncomputable section
variable {top : Fin 16}
open K1_13 (Geom)
open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1
open Low6966Prices (physicalDegree)
open MvPolynomial
open scoped BigOperators Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
open K1_13_5_5_2_1 (monic_chart_aux)
open K1_13_5_5_2_1 (commonFactor_monic trimmedValue_monic trimmedValue_dvd)
open P0_9_5_2 (eval_divisions)
private theorem supported_height (Q : Ideal CoeffRing) (L : Fin 2 → FreshJetRing)
    (hQ : Q.IsPrime) (hhom : Q.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom))
    (hdim : (affineHilbertPolynomial Q).natDegree = 2)
    (hL : FiniteJetPair L (jetImage (freshIdeal Q))) (hlow : LowSupport Q) :
    2 * affineDegree Q ≤
      (physicalDegree : ℚ) * (genericFiberDimension L (freshIdeal Q) : ℚ) := by
  have h1 := K1_13_5_5_2_1_1.of_children K1_13_5_5_2_1_1_1.proof
    K1_13_5_5_2_1_1_2.proof K1_13_5_5_2_1_1_3.proof
  have h2 := K1_13_5_5_2_1_2.proof
  have h3 := K1_13_5_5_2_1_3.proof
  have h4 := K1_13_5_5_2_1_4.of_children K1_13_5_5_2_1_4_1.proof K1_13_5_5_2_1_4_2.proof
  have h5 := K1_13_5_5_2_1_5.proof
  have h6 := K1_13_5_5_2_1_6.proof
  obtain ⟨i, hi, hchart, hmonic, hdegree⟩ := monic_chart_aux Q hQ hhom (by omega)
  have hid : i.val ≤ physicalDegree :=
    Nat.le_of_lt_succ (lt_of_not_ge (fun h => hi (hlow i h)))
  let : IsDomain (ChartRing Q i) := hchart
  obtain ⟨a, ha, ⟨s⟩⟩ := h2 (ChartRing Q i) (direction Q i) hmonic ((hdegree.trans hid).trans (by decide))
  obtain ⟨hdom, heval, hfinite, hcoeff⟩ := h1 Q i a hQ hhom hdim hi hchart ha
  let : IsDomain (FreshOpen Q i a) := hdom
  let : IsDomain (OpenRing Q i a) := IsLocalization.Away.isDomain _ ha
  change Factorization (openDirection Q i a) at s
  obtain ⟨q, hq0, hq, hqspan⟩ := h3 (OpenRing Q i a) (openDirection Q i a) s
  let e : (Polynomial (OpenRing Q i a)) →+* FreshOpen Q i a := freshEval (OpenRing Q i a)
  let x := e (openDirection Q i a)
  let b := e (commonFactor s)
  let d : Fin 3 → FreshOpen Q i a := fun j => e (q j)
  have hx : x ≠ 0 := by
    simpa only [e, x, openDirection, map_zero] using
      heval.ne (hmonic.map (algebraMap _ (OpenRing Q i a))).ne_zero
  have hb : b ≠ 0 := by
    simpa only [e, b, map_zero] using heval.ne (commonFactor_monic s).ne_zero
  have hd : d 0 ≠ 0 := by
    simpa only [d, hq0, e, map_zero] using heval.ne (trimmedValue_monic s).ne_zero
  have htrim : ∀ j, b * d j = e (Polynomial.hasseDeriv j.val (openDirection Q i a)) := by
    intro j
    exact (e.map_mul _ _).symm.trans (congrArg e (hq j))
  have hspan : Ideal.span (Set.range d) = ⊤ := by
    have hm := congrArg (Ideal.map e) hqspan
    rwa [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at hm
  let : Module.Finite FreshField (PrincipalQuot x) := hfinite
  have hdegree' : (openDirection Q i a).natDegree ≤ physicalDegree :=
    Polynomial.natDegree_map_le.trans (hdegree.trans hid)
  have hdiv := eval_divisions e s hdegree' (by decide)
  have hdeq : d 0 = e (trimmedValue s) := congrArg e hq0
  rw [← hdeq] at hdiv
  obtain ⟨hdfin, hlen⟩ := length_bound x (d 0) physicalDegree hx hd hdiv.1 hdiv.2
  rw [← hcoeff]
  have hlenQ : 2 * (Module.finrank FreshField (PrincipalQuot x) : ℚ) ≤
      (physicalDegree : ℚ) * (Module.finrank FreshField (PrincipalQuot (d 0)) : ℚ) := by
    exact_mod_cast hlen
  by_cases hu : IsUnit (d 0)
  · have hzero : Module.finrank FreshField (PrincipalQuot (d 0)) = 0 := by
      have : Subsingleton (PrincipalQuot (d 0)) :=
        Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hu)
      exact Module.finrank_zero_of_subsingleton
    exact hlenQ.trans (by rw [hzero, Nat.cast_zero, mul_zero]; positivity)
  · obtain ⟨hk, hcomparison⟩ := h4 Q i a hQ hhom hdim hi hchart ha hdom b d hb htrim
    obtain ⟨hpairfin, hrank⟩ := hcomparison L hL
    have hL' : FiniteJetPair L (coneJetIdeal d) := hk ▸ hL
    obtain ⟨M, w, hM, hMw, hinj, hw⟩ := h5 _ d L hd hu hspan hL'
    obtain ⟨hwfin, hwRank⟩ := h6 _ d L M hL' hpairfin hM hinj
    rw [hMw] at hwfin hwRank hinj
    let : Module.Finite PairField (pairFiber (valuePairMap (d 0) w)) := hwfin
    let : Module.Finite FreshField (PrincipalQuot (d 0)) := hdfin
    have hbound := pin_bound (d 0) w hw hinj
    rw [hwRank, hrank] at hbound
    exact hlenQ.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hbound)
      (Nat.cast_nonneg physicalDegree))
theorem chart_degree (P : Ideal CoeffRing) (g d : FreshJetRing)
    (hchart : FreshChart P g d) (hlow : LowSupport P) :
    (affineHilbertPolynomial P).natDegree = 2 ∧
      2 * affineDegree P ≤ (physicalDegree : ℚ) * (g.totalDegree : ℚ) := by
  have hdim := K1_13_5_5_2.chart_dimension P g d hchart
  refine ⟨hdim, ?_⟩
  have h2 := K1_13_5_5_2_2.of_children K1_13_5_5_2_2_1.proof K1_13_5_5_2_2_2.proof
  have h3 := K1_13_5_5_2_3.of_children K1_13_5_5_2_3_1.proof
    K1_13_5_5_2_3_2.proof K1_13_5_5_2_3_3.proof
  obtain ⟨n, Q, hQ, hdeg, hfiber⟩ := h2 P hchart.prime hdim
  obtain ⟨L, hL, hfinite, hbudget⟩ := h3 P g d hchart
  have htail : LowSupport (infinityIdeal P) := by
    intro i hi
    change MvPolynomial.X i ∈ Ideal.span _
    apply Ideal.subset_span
    refine ⟨MvPolynomial.X i, hlow i hi, ?_⟩
    change homogeneousComponent (MvPolynomial.X (R := Geom) i).totalDegree
      (MvPolynomial.X i) = MvPolynomial.X i
    rw [totalDegree_X]
    exact homogeneousComponent_eq_self (isHomogeneous_X Geom i)
  have hcurve (i : Fin n) : 2 * affineDegree (Q i) ≤
      (physicalDegree : ℚ) * (genericFiberDimension L (freshIdeal (Q i)) : ℚ) := by
    obtain ⟨hi, hhom, hd⟩ := hQ i
    have hle : jetImage (freshIdeal (infinityIdeal P)) ≤ jetImage (freshIdeal (Q i)) :=
      Ideal.comap_mono (Ideal.map_mono hi.le)
    exact supported_height (Q i) L hi.isPrime hhom hd (hL.of_le hle)
      (fun j hj => hi.le (htail j hj))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcurve i)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [hdeg]
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg physicalDegree))
  exact_mod_cast (hfiber L hfinite).trans hbudget
end
end Low6966Leading_2
end
section
set_option maxHeartbeats 1000000
namespace Low6966Leading_2
noncomputable section
variable {top : Fin 16}
open P3 (K)
open Low6966Leading (Whole)
open K1_13 (Row Geom extend)
open K1_13_5 (RegularAt NodeCapacity NodeFamily)
open K1_13_5_5 (freshRow FreshField)
open Finset MvPolynomial
open scoped BigOperators Polynomial
private theorem freshRow_degree_le (f : Row 3) : (freshRow f).totalDegree ≤ f.totalDegree := by
  unfold freshRow MvPolynomial.totalDegree
  exact Finset.sup_mono (support_map_subset (algebraMap (Polynomial Geom) FreshField) f)
theorem proof : Low6966Leading.c2 top := by
  classical
  intro w Γ s hm n f hf hcover
  let part (i : Fin n) := Γ.filter fun γ => RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)
  let cap (i : Fin n) := 133387 * (f i).totalDegree
  have hsub (i : Fin n) : part i ⊆ Γ := filter_subset _ _
  have hlocal (i : Fin n) : NodeCapacity w (part i) s (cap i) := by
    by_cases hi : Whole (f i)
    · have htop : (f i).degreeOf 2 ≤ 29 :=
        (single_le_sum (f := fun j => (f j).degreeOf 2) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
          (hf.coordinate.trans (by fin_cases top <;> decide))
      obtain ⟨P, hp, hsupport, hall⟩ := chart_of_whole _ (hf.irreducible i) (hf.positive i) htop (hf.weight i) hi
      obtain ⟨hdim, hdeg⟩ := chart_degree _ _ _ hp hsupport
      change 2 * affineDegree P ≤ (133387 : ℚ) * ((freshRow (f i)).totalDegree : ℚ) at hdeg
      apply surface_nodeCapacity (hm.mono (hsub i)) hp.prime hdim
      · intro γ hγ
        have hγΓ := hsub i hγ
        exact hall _ (Polynomial.natDegree_map_le.trans (hm.degree γ hγΓ))
          (mem_filter.mp hγ).2.1
      · have hle : ((freshRow (f i)).totalDegree : ℚ) ≤ ((f i).totalDegree : ℚ) :=
          Nat.cast_le.mpr (freshRow_degree_le (f i))
        simpa only [cap, Nat.cast_mul, Nat.cast_ofNat] using
          hdeg.trans (mul_le_mul_of_nonneg_left hle (by norm_num))
    · have hempty : part i = ∅ := by simp [part, hi]
      rw [hempty]
      exact ⟨∅, by simp, by simp⟩
  let C : NodeFamily w Γ s := ⟨n, part, cap, hsub, hlocal⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨i, hi, hwhole⟩ := hcover γ hγ
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hγ, hi, hwhole⟩⟩
  · change n ≤ Low6966Prices.lowerWidth top
    calc
      n = ∑ _i : Fin n, 1 := by simp
      _ ≤ ∑ i, (f i).totalDegree := sum_le_sum fun i _ =>
        (hf.positive i).trans_le (degreeOf_le_totalDegree _ _)
      _ ≤ Low6966Prices.lowerWidth top := hf.total
  · change (∑ i, 133387 * (f i).totalDegree) ≤ 133387 * Low6966Prices.lowerWidth top
    rw [← mul_sum]
    exact Nat.mul_le_mul_left _ hf.total
end
end Low6966Leading_2
end

namespace Low6966Leading
variable {top : Fin 16}
private theorem gateLow6966Leading_1_1_1 : Low6966Leading_1_1.c1 top := Low6966Leading_1_1_1.proof
private theorem gateLow6966Leading_1_1_2 : Low6966Leading_1_1.c2 top := Low6966Leading_1_1_2.proof
private theorem gateLow6966Leading_1_1_3 {top : Fin 16} : Low6966Leading_1_1.c3 top := Low6966Leading_1_1_3.proof
private theorem gateLow6966Leading_1_1 {top : Fin 16} : Low6966Leading_1.c1 top := Low6966Leading_1_1.of_children gateLow6966Leading_1_1_1 gateLow6966Leading_1_1_2 gateLow6966Leading_1_1_3
private theorem gateLow6966Leading_1_2 {top : Fin 16} : Low6966Leading_1.c2 top := Low6966Leading_1_2.proof
private theorem gateLow6966Leading_1_3 {top : Fin 16} : Low6966Leading_1.c3 top := Low6966Leading_1_3.proof
private theorem gateLow6966Leading_1 {top : Fin 16} : Low6966Leading.c1 top := Low6966Leading_1.of_children gateLow6966Leading_1_1 gateLow6966Leading_1_2 gateLow6966Leading_1_3
private theorem gateLow6966Leading_2 {top : Fin 16} : Low6966Leading.c2 top := Low6966Leading_2.proof
theorem lower_count {t : ℕ} (ht : t ≤ 15) : Low6966Prices.c5 t :=
  of_children (top := ⟨t, by omega⟩) gateLow6966Leading_1 gateLow6966Leading_2

#print axioms lower_count
end Low6966Leading

end Merged6967_Low6966Leading

section Merged6967_Low6966Mass10
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6966Allocation.Group10

private def m0 : MassCell 10 :=
  ⟨⟨2,5,7⟩,mass_cell 10 2 5 7 189 (by decide)
    (by decide +kernel) [4606755133925, 3795097543302, 3042885585162, 2397139492422, 1849789550010, 1392750926310, 1017923673162, 717192725862, 482427903162, 305483907270, 178200323850, 92401622022, 39897154362, 12481156902, 1932749130, 30226326] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 10 :=
  ⟨⟨2,6,15⟩,mass_cell 10 2 6 15 179 (by decide)
    (by decide +kernel) [4679106249028, 4064152064581, 3203614905323, 2470172570607, 1857465547091, 1354934890775, 951924889659, 637683063743, 401360165027, 232010177511, 118590317195, 49961032079, 14886002163, 2032139447, 17280705] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 10 :=
  ⟨⟨1,8,25⟩,mass_cell 10 1 8 25 161 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3536291597878, 2626179279382, 1883279811574, 1292518703062, 838104826294, 503530417558, 271571076982, 124285768534, 43016820022, 8389923094, 316271865, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 10 :=
  ⟨⟨2,9,29⟩,mass_cell 10 2 9 29 154 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3705229214234, 2716670200562, 1896319540646, 1257859554786, 779954969126, 440556783602, 216902271942, 85514981666, 22204734086, 2067624306, 863338] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 10 :=
  ⟨⟨2,10,32⟩,mass_cell 10 2 10 32 148 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3806760990764, 2811219401009, 1916636752685, 1232061575433, 731466260933, 387723142241, 172604493789, 56782531385, 9829412213, 238488956, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 10 :=
  ⟨⟨4,12,37⟩,mass_cell 10 4 12 37 139 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3029924856228, 1962716544452, 1179386414564, 637411400196, 293362465316, 102904604228, 20796841572, 894073640, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 10 :=
  ⟨⟨2,14,40⟩,mass_cell 10 2 14 40 130 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3204042438294, 2013975775185, 1142889040437, 564116176185, 222050135517, 56972171553, 5051837445, 989635] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 10 :=
  ⟨⟨1,15,41⟩,mass_cell 10 1 15 41 126 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3254585780626, 2022888190177, 1113287883977, 522348162457, 187347626449, 39069787889, 1805015739, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 10 :=
  ⟨⟨4,16,43⟩,mass_cell 10 4 16 43 124 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3355694148216, 2085976575004, 1109205408572, 495405932380, 163559368828, 28444444316, 697470818, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 10 :=
  ⟨⟨4,18,45⟩,mass_cell 10 4 18 45 119 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3439831024823, 2147394286147, 1074168198391, 432652698251, 116419484671, 11827556947, 12060931] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 10 :=
  ⟨⟨5,19,46⟩,mass_cell 10 5 19 46 116 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3474956070478, 2187417654444, 1059639765872, 404461340228, 97499462376, 7222861340, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 10 :=
  ⟨⟨1,21,47⟩,mass_cell 10 1 21 47 112 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3503831622992, 2225646197728, 1021937317252, 349257483176, 64289615500, 1868101406, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 10 :=
  ⟨⟨1,24,49⟩,mass_cell 10 1 24 49 106 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2347139737968, 987735795584, 284106576272, 33498540960, 102317924] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 10 :=
  ⟨⟨9,27,51⟩,mass_cell 10 9 27 51 103 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2498979750770, 954384177627, 227571137587, 16345849059, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 10 :=
  ⟨⟨4,30,52⟩,mass_cell 10 4 30 52 99 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2579001622818, 928685520131, 183250428111, 6768432046, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 10 :=
  ⟨⟨4,33,53⟩,mass_cell 10 4 33 53 96 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2654667473142, 899434666694, 144336582778, 2340667789] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 10 :=
  ⟨⟨12,36,54⟩,mass_cell 10 12 36 54 94 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2725068411708, 862582937832, 110425955752, 622844266] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 10 :=
  ⟨⟨6,41,55⟩,mass_cell 10 6 41 55 90 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2803600803136, 827085233619, 72471044331, 7743848] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 10 :=
  ⟨⟨1,48,56⟩,mass_cell 10 1 48 56 86 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2874181940465, 762535283350, 36473424276, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 10 :=
  ⟨⟨10,54,57⟩,mass_cell 10 10 54 57 84 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2949765109491, 730925688097, 20801521858] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 10 :=
  ⟨⟨64,14,48⟩,mass_cell 10 64 14 48 138 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3524501299114, 2247004860567, 1004047459251, 360666850479, 85806659211, 5726614076, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 10 :=
  ⟨⟨60,24,52⟩,mass_cell 10 60 24 52 109 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2543911518276, 908414082612, 217990538132, 23862703604, 220005294, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 10 :=
  ⟨⟨65,4,42⟩,mass_cell 10 65 4 42 247 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3323108584601, 2118807006452, 1169192278356, 500119961421, 83897239562, 51332555, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 10 :=
  ⟨⟨62,21,51⟩,mass_cell 10 62 21 51 116 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2462381626789, 930978470644, 255784329728, 38822872612, 1352579296, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 10 :=
  ⟨⟨68,30,54⟩,mass_cell 10 68 30 54 101 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2702967205604, 849988920001, 139750283645, 5417914522, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 10 :=
  ⟨⟨38,38,55⟩,mass_cell 10 38 38 55 93 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2791884833350, 822922088127, 87626649363, 248350809] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 10 :=
  ⟨⟨59,19,50⟩,mass_cell 10 59 19 50 120 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2384596616330, 957046474614, 294413197346, 56184275150, 3690244794, 3726330] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 10 :=
  ⟨⟨53,28,53⟩,mass_cell 10 53 28 53 103 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2628019221687, 886174176290, 176434640882, 10727425986, 5732] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 10 :=
  ⟨⟨57,36,55⟩,mass_cell 10 57 36 55 95 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2785854841287, 818593492830, 95773982254, 748968661] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 10 :=
  ⟨⟨36,44,56⟩,mass_cell 10 36 44 56 89 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2869473766852, 780857630004, 52378746708, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 10 :=
  ⟨⟨62,49,57⟩,mass_cell 10 62 49 57 87 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2940582213161, 730040010224, 31035547926, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 10 :=
  ⟨⟨66,35,55⟩,mass_cell 10 66 35 55 96 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2783175610894, 815488358829, 98690136765, 1099519293] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 10 :=
  ⟨⟨46,43,56⟩,mass_cell 10 46 43 56 90 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2867014733859, 779873771724, 55743206248, 878438] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 10 :=
  ⟨⟨61,27,53⟩,mass_cell 10 61 27 53 105 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2625192844620, 883689276282, 179445744654, 12524460346, 3963753] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 10 :=
  ⟨⟨74,34,55⟩,mass_cell 10 74 34 55 97 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2781539494769, 814123367395, 101370049439, 1495135518, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 10 :=
  ⟨⟨65,41,56⟩,mass_cell 10 65 41 56 91 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2862614256841, 776561472498, 61680726102, 32863661] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 10 :=
  ⟨⟨71,48,57⟩,mass_cell 10 71 48 57 87 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2939357955375, 729924698308, 33010073464, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 10 :=
  ⟨⟨87,16,51⟩,mass_cell 10 87 16 51 132 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2479004838913, 947248837400, 242688855688, 16518759908, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 10 :=
  ⟨⟨69,26,53⟩,mass_cell 10 69 26 53 107 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2622042277778, 878836531758, 179676335382, 13639683966, 21729914] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 10 :=
  ⟨⟨88,27,54⟩,mass_cell 10 88 27 54 106 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2701619168891, 849445307287, 142805142047, 6602768630, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 10 :=
  ⟨⟨90,15,51⟩,mass_cell 10 90 15 51 136 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2488316137586, 959215883240, 240281259475, 11450184754, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 10 :=
  ⟨⟨79,21,52⟩,mass_cell 10 79 21 52 117 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2543357712826, 907108157021, 216702011229, 22714736883, 45300737, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 10 :=
  ⟨⟨75,25,53⟩,mass_cell 10 75 25 53 108 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2622792486792, 881440754359, 182123000879, 14575334407, 46386435] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 10 :=
  ⟨⟨80,47,57⟩,mass_cell 10 80 47 57 88 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2938078357902, 728864923290, 34757438838, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 10 :=
  ⟨⟨96,45,57⟩,mass_cell 10 96 45 57 89 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2936528089832, 728595882057, 37983849961, 16906] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 10 :=
  ⟨⟨73,40,56⟩,mass_cell 10 73 40 56 92 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2861547220417, 777117205790, 64669808318, 80170244] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 10 :=
  ⟨⟨97,37,56⟩,mass_cell 10 97 37 56 95 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2857818447617, 771526061077, 69107070957, 331104581] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 10 :=
  ⟨⟨106,10,51⟩,mass_cell 10 106 10 51 167 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2528544523600, 987318437183, 169912335684, 13654305, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 10 :=
  ⟨⟨104,44,57⟩,mass_cell 10 104 44 57 90 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2935679854796, 727064559628, 38992415596, 1185336] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 10 :=
  ⟨⟨110,54,58⟩,mass_cell 10 110 54 58 85 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3011774368349, 674914737967, 16145126626, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 10 :=
  ⟨⟨111,43,57⟩,mass_cell 10 111 43 57 91 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2935378854058, 727159093336, 39949065932, 4959317] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 10 :=
  ⟨⟨103,36,56⟩,mass_cell 10 103 36 56 96 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2858179879014, 773585311056, 70429852176, 408711008] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 10 :=
  ⟨⟨118,42,57⟩,mass_cell 10 118 42 57 91 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2935036123671, 726373660685, 40323402297, 10100725] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 10 :=
  ⟨⟨112,12,52⟩,mass_cell 10 112 12 52 154 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2595286172742, 957300917096, 143528439354, 73815, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 10 :=
  ⟨⟨110,35,56⟩,mass_cell 10 110 35 56 97 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2857580111366, 771253662356, 69566797160, 374639340, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 10 :=
  ⟨⟨118,53,58⟩,mass_cell 10 118 53 58 85 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3011268136363, 674268154633, 16842930658, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 10 :=
  ⟨⟨115,34,56⟩,mass_cell 10 115 34 56 98 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2858716356891, 774711467838, 69826087822, 274632759, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 10 :=
  ⟨⟨121,33,56⟩,mass_cell 10 121 33 56 99 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2858889780037, 773660911100, 67457420850, 68140953, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 10 :=
  ⟨⟨126,32,56⟩,mass_cell 10 126 32 56 100 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2859920793310, 775247155128, 65069987919, 720720, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 10 :=
  ⟨⟨111,28,55⟩,mass_cell 10 111 28 55 105 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2782711784653, 817580052026, 100973943882, 733535772, 0] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 10 :=
  ⟨⟨120,9,52⟩,mass_cell 10 120 9 52 177 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2618910008621, 970823848080, 105693457790, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 10 :=
  ⟨⟨128,24,55⟩,mass_cell 10 128 24 55 112 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2791513805756, 828988267972, 81532430962, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 10 :=
  ⟨⟨130,40,57⟩,mass_cell 10 130 40 57 93 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2935441507914, 727774838684, 40230423324, 1227535] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 10 :=
  ⟨⟨132,4,52⟩,mass_cell 10 132 4 52 257 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2660459787516, 976353644760, 51416464879, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 10 :=
  ⟨⟨124,13,53⟩,mass_cell 10 124 13 53 149 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2669269028501, 922160130681, 97243648865, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 10 :=
  ⟨⟨135,30,56⟩,mass_cell 10 135 30 56 103 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2862769617911, 779578950328, 58602891415, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 10 :=
  ⟨⟨135,22,55⟩,mass_cell 10 135 22 55 117 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2797550575293, 836184955716, 69744136047, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m67 : MassCell 10 :=
  ⟨⟨136,39,57⟩,mass_cell 10 136 39 57 94 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2935592287423, 727244398928, 38970107872, 0] (by decide +kernel) (by decide +kernel)⟩
private def m68 : MassCell 10 :=
  ⟨⟨126,52,58⟩,mass_cell 10 126 52 58 86 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3010738571788, 672925137456, 17335318720, 0] (by decide +kernel) (by decide +kernel)⟩
private def m69 : MassCell 10 :=
  ⟨⟨134,9,53⟩,mass_cell 10 134 9 53 178 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2696206211498, 937249446054, 61144795598, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m70 : MassCell 10 :=
  ⟨⟨139,21,55⟩,mass_cell 10 139 21 55 120 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2799806850592, 835498436372, 61640112138, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 10) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67, m68, m69, m70]

end Low6966Allocation.Group10

end Merged6967_Low6966Mass10
