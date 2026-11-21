import ProximityPrize.SubmissionLower.GoldBranch6N5
import ProximityPrize.SubmissionLower.UpperBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_7
noncomputable section
open Polynomial MvPolynomial
open P1 (I K node p)
open K1_14 (FX L seedEmbedding)
open K1_14_6 (Biform ClosedField rootPoint)
abbrev box (a b : ℕ) := restrictBidegree (Fin 2) FX a b
def poleProduct (H : L[X]) : FX[X] :=
  (H * H.map (frobenius L p)).map (algebraMap L FX)
structure CRTChart (w : ℕ) where
  denominator : Biform
  numerator : Biform[X]
  degree_numerator : numerator.natDegree < 2 * w
  bound_denominator : denominator ∈ box 0 (2 * w)
  bound_numerator : ∀ j, numerator.coeff j ∈ box 0 (2 * w)
def CRTChart.Recovers {w : ℕ} (C : CRTChart w) (G : FX[X]) (z : K) (S : K[X]) : Prop :=
  let ev := MvPolynomial.eval (rootPoint z S)
  ev C.denominator ≠ 0 ∧
    G ∣ S.map seedEmbedding - (ev C.denominator)⁻¹ • C.numerator.map ev
def localOrd (d w e s : ℕ) := 1 + 2 * (d - 2 * w - s) * (e - 1)
def localSeed (d w v s : ℕ) := 2 * w + 2 * (d - 2 * w - s) * v
def ShortCharts (d w e v : ℕ) (word : I → K) (T : Finset K)
    (z : K → K) (S : K → K[X]) : Prop :=
  ∀ U ⊆ T, ∀ sites : Finset I, sites.card ≤ d →
    (∀ γ ∈ U, ∀ j ∈ sites, (S γ).eval (node j) = word j) →
    ∃ cut : I → Biform,
      (∀ j, cut j ∈ box (localOrd d w e sites.card) (localSeed d w v sites.card)) ∧
      ∀ γ ∈ U, ∀ j, MvPolynomial.eval (rootPoint (z γ) (S γ)) (cut j) = 0 ↔
        (S γ).eval (node j) = word j
abbrev BoxVars (a b : ℕ) := bidegreeExponents (Fin 2) a b
abbrev BoxRing (a b : ℕ) := MvPolynomial (BoxVars a b) ClosedField
abbrev boxMap (a b : ℕ) := bidegreeMap (Fin 2) ClosedField a b
def WeightedCut : Prop :=
  ∀ (a b m n r t : ℕ), 0 < a → 0 < b → 0 < r → 0 < t →
    r * m ≤ t * a → r * n ≤ t * b →
    ∀ (P : Ideal (BoxRing a b)), P.IsPrime → RingHom.ker (boxMap a b) ≤ P →
    0 < (affineHilbertPolynomial P).natDegree →
    ∀ (q : BoxRing a b), q ∉ P →
      boxMap a b q ∈ restrictBidegree (Fin 2) ClosedField m n →
      (r : ℚ) * (∑ Q ∈ (P ⊔ Ideal.span {q}).minimalPrimesFinset, affineDegree Q) ≤
        (t : ℚ) * affineDegree P
def CurveScale : Prop :=
  ∀ (a b D : ℕ), 0 < D → D ≤ a → D ≤ b →
    ∀ (P : Ideal (BoxRing a b)), P.IsPrime → RingHom.ker (boxMap a b) ≤ P →
    (affineHilbertPolynomial P).natDegree = 1 → (D : ℚ) ≤ affineDegree P
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open Polynomial Finset MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
open P1 (K I node agreement blockLength)
open K1_14 (FX)
open K1_14_6 (Biform ClosedField rootPoint)
open private card_le_sum_cover from ProximityPrize.SubmissionLower.Fast055
open private closedPoint eval_extend extend_mem from ProximityPrize.SubmissionLower.Fast055
structure FixedWord (word : I → K) (T : Finset K) (S : K → K[X]) (d : ℕ) : Prop where
  distinct : Set.InjOn S (T : Set K)
  degree : ∀ γ ∈ T, (S γ).natDegree ≤ d
  hits : ∀ γ ∈ T, ∃ V : Finset I, agreement ≤ V.card ∧
    ∀ j ∈ V, (S γ).eval (node j) = word j
abbrev point (a b : ℕ) (z : K → K) (S : K → K[X]) (γ : K) :=
  monomialPoint (BoxVars a b) (closedPoint (z γ) (S γ))
def slice {a b : ℕ} (z : K → K) (S : K → K[X]) (U : Finset K)
    (P : Ideal (BoxRing a b)) : Finset K := by
  classical
  exact U.filter fun γ => point a b z S γ ∈ zeroLocus ClosedField P
theorem slice_subset {a b z S U} (P : Ideal (BoxRing a b)) : slice z S U P ⊆ U := by
  classical
  exact filter_subset _ _
theorem slice_on {a b z S U} (P : Ideal (BoxRing a b)) {γ : K}
    (hγ : γ ∈ slice z S U P) : point a b z S γ ∈ zeroLocus ClosedField P := by
  classical
  exact (mem_filter.mp hγ).2
theorem point_injective {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {z : K → K} {S : K → K[X]} {T : Finset K} (hz : Set.InjOn z (T : Set K)) :
    Set.InjOn (point a b z S) (T : Set K) := by
  intro γ hγ η hη hpt
  have hcoords : closedPoint (z γ) (S γ) = closedPoint (z η) (S η) :=
    monomialPoint_injective (fun i => single_mem_bidegreeExponents ha hb i) hpt
  have hfirst := congrFun hcoords (some (0 : Fin 2))
  let ι := algebraMap FX ClosedField
  change ι (K1_14.seedEmbedding (z γ)) = ι (K1_14.seedEmbedding (z η)) at hfirst
  exact hz hγ hη (K1_14.seedEmbedding.injective (ι.injective hfirst))
private theorem zero_dim_count {a b z S T} {U : Finset K} (hU : U ⊆ T)
    (hinj : Set.InjOn (point a b z S) (T : Set K)) (P : Ideal (BoxRing a b))
    (hdim : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ U, point a b z S γ ∈ zeroLocus ClosedField P) :
    (U.card : ℚ) ≤ affineDegree P := by
  classical
  let image := U.image (point a b z S)
  have hc : image.card = U.card := card_image_of_injOn (hinj.mono hU)
  have hsub : (image : Set _) ⊆ zeroLocus ClosedField P := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hx
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := ClosedField) P hdim
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hc] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree
private def common (word : I → K) (U : Finset K) (S : K → K[X]) : Finset I := by
  classical
  exact univ.filter fun j => ∀ γ ∈ U, (S γ).eval (node j) = word j
private theorem common_agrees {word U S} {γ : K} (hγ : γ ∈ U) {j : I}
    (hj : j ∈ common word U S) : (S γ).eval (node j) = word j := by
  classical
  exact (mem_filter.mp hj).2 γ hγ
structure Invoice (d w e v a b D : ℕ) : Prop where
  scale_pos : 0 < D
  ordinate : D ≤ a
  seed : D ≤ b
  degree : d < agreement
  fits : ∀ s ≤ d, D * (blockLength-s) * localOrd d w e s ≤ (agreement-s) * a ∧
    D * (blockLength-s) * localSeed d w v s ≤ (agreement-s) * b
end
end P1_7_7
end
section
namespace P1_7_7
open P1 (HighBand agreement blockLength)
open P1_7 (degreeAt gap scale quotientOrder muNum lambdaNum ceilRatio persistentFee)
private theorem cross_ratio {A n d s : ℕ} (hn : A ≤ n) (hd : d ≤ A) (hs : s ≤ d) :
    (A-d) * (n-s) ≤ (A-s) * (n-d) := by
  have h : 0 ≤ ((n : ℤ)-A) * ((d : ℤ)-s) :=
    mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hn)) (sub_nonneg.mpr (Int.ofNat_le.mpr hs))
  apply Int.ofNat_le.mp
  push_cast [Int.ofNat_sub hd, Int.ofNat_sub (hs.trans hd), Int.ofNat_sub (hd.trans hn),
    Int.ofNat_sub (hs.trans (hd.trans hn))]
  nlinarith only [h]
private theorem order_ratio {A ell s : ℕ} (hell : ell ≤ A) :
    A * (ell-s) ≤ (A-s) * ell := by
  by_cases hs : s ≤ ell
  · have h : 0 ≤ ((A : ℤ)-ell) * (s : ℤ) :=
      mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hell)) (Int.natCast_nonneg s)
    apply Int.ofNat_le.mp
    push_cast [Int.ofNat_sub hs, Int.ofNat_sub (hs.trans hell)]
    nlinarith only [h]
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.mul_zero]
    exact Nat.zero_le _
private theorem coordinate_bounds {A n d hi ell w e v s : ℕ}
    (hAn : A ≤ n) (hd : d ≤ hi) (hg : hi < A)
    {height : ℕ} (hheight : w ≤ height)
    (hord : d - 2 * w ≤ ell) (hs : s ≤ d) :
    let D := A * (A-hi)
    let m := A * (n-hi)
    let t := n * (A-hi) * ell
    D * (n-s) * localOrd d w e s ≤ (A-s) * (m + 2 * t * (e-1)) ∧
    D * (n-s) * localSeed d w v s ≤ (A-s) * (2 * height * m + 2 * t * v) := by
  dsimp only
  let D := A * (A-hi)
  let m := A * (n-hi)
  let t := n * (A-hi) * ell
  let l := d - 2*w
  have hmu : D * (n-s) ≤ (A-s) * m := by
    calc
      _ = A * ((A-hi) * (n-s)) := by simp only [D]; ring
      _ ≤ A * ((A-s) * (n-hi)) := Nat.mul_le_mul_left _ (cross_ratio hAn hg.le (hs.trans hd))
      _ = _ := by simp only [m]; ring
  have horder : A * (l-s) ≤ (A-s) * ell := by
    exact (order_ratio ((Nat.sub_le d _).trans (hd.trans hg.le))).trans (Nat.mul_le_mul_left _ hord)
  have htime : D * (n-s) * (l-s) ≤ (A-s) * t := by
    calc
      _ = (A-hi) * (n-s) * (A * (l-s)) := by simp only [D]; ring
      _ ≤ ((A-hi) * n) * ((A-s) * ell) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) horder
      _ = _ := by simp only [t]; ring
  change D * (n-s) * (1 + 2 * (l-s) * (e-1)) ≤ (A-s) * (m + 2*t*(e-1)) ∧
    D * (n-s) * (2*w + 2*(l-s)*v) ≤ (A-s) * (2*height*m + 2*t*v)
  constructor
  · calc
      _ = D * (n-s) + (D * (n-s) * (l-s)) * (2*(e-1)) := by ring
      _ ≤ (A-s) * m + ((A-s) * t) * (2*(e-1)) :=
        Nat.add_le_add hmu (Nat.mul_le_mul_right _ htime)
      _ = _ := by ring
  · calc
      _ = (D * (n-s)) * (2*w) + (D * (n-s) * (l-s)) * (2*v) := by ring
      _ ≤ ((A-s) * m) * (2*height) + ((A-s) * t) * (2*v) :=
        Nat.add_le_add (Nat.mul_le_mul hmu (Nat.mul_le_mul_left _ hheight)) (Nat.mul_le_mul_right _ htime)
      _ = _ := by ring
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
open P1 (K)
open P1_7 (regularRoot)
open K1_14 (Equation FX SeedBound atMark)
open K1_14_6 (ClosedField)
open K1_14_6_2 (SourcePolynomial flatten eval_flatten)
open private K1_14_6_2.flatten_bound factor_span_minimal comap_span_flatten positiveFactors_card_le
  positive_factor_at_root from ProximityPrize.SubmissionLower.Fast055
open private closedPoint extendEquation extendEquation_eval from ProximityPrize.SubmissionLower.Fast055
private theorem regular_components {a b e v : ℕ} (ha : 0 < a) (hb : 0 < b)
    (f : SourcePolynomial ClosedField) (hf : f ≠ 0) (he : f.natDegree ≤ e)
    (hv : ∀ j, (f.coeff j).totalDegree ≤ v) :
    ∃ Ps : Finset (Ideal (BoxRing a b)),
      (∀ P ∈ Ps, P.IsPrime ∧ RingHom.ker (boxMap a b) ≤ P ∧
        (affineHilbertPolynomial P).natDegree = 2) ∧
      Ps.card ≤ e ∧
      (∑ P ∈ Ps, affineDegree P) ≤ (e * b ^ 2 + 2 * v * a * b : ℕ) ∧
      ∀ x : Option (Fin 2) → ClosedField,
        f.eval₂ (MvPolynomial.eval (x ∘ some)) (x none) = 0 →
        f.derivative.eval₂ (MvPolynomial.eval (x ∘ some)) (x none) ≠ 0 →
        ∃ P ∈ Ps, monomialPoint (BoxVars a b) x ∈ zeroLocus ClosedField P := by
  classical
  let φ := boxMap a b
  let fs := ((factors f).filter (fun g => 0 < g.natDegree)).toFinset
  let component := fun g : SourcePolynomial ClosedField => (Ideal.span {flatten g}).comap φ
  let Ps := fs.image component
  have hminimal {g : SourcePolynomial ClosedField} (hg : g ∈ fs) :
      component g ∈ ((Ideal.span {flatten f}).comap φ).minimalPrimes := by
    have hfac := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hg)).1
    have h := Ideal.minimalPrimes_comap_of_surjective
      (f := (optionEquivLeft ClosedField (Fin 2)).toRingHom)
      (optionEquivLeft ClosedField (Fin 2)).surjective (factor_span_minimal hf hfac)
    rw [comap_span_flatten, comap_span_flatten] at h
    exact Ideal.minimalPrimes_comap_of_surjective (bidegreeMap_surjective ha hb) h
  refine ⟨Ps, ?_, Finset.card_image_le.trans ((positiveFactors_card_le f hf).trans he), ?_, ?_⟩
  · intro P hP
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hP
    have hp := (hminimal hg).isPrime
    have hg0 := (prime_of_factor g
      (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hg)).1).ne_zero
    have hflat : flatten g ≠ 0 := by
      simpa only [map_zero] using (flatten : SourcePolynomial ClosedField ≃ₐ[ClosedField] _).injective.ne hg0
    have hproper : Ideal.span {flatten g} ≠ ⊤ := by
      intro ht
      exact hp.ne_top (by simp [component, ht])
    refine ⟨hp, ?_, ?_⟩
    · intro r hr
      change φ r ∈ Ideal.span {flatten g}
      rw [RingHom.mem_ker.mp hr]
      exact zero_mem _
    · simpa [component, φ, Nat.card_eq_fintype_card] using
        natDegree_affineHilbertPolynomial_comap_bidegreeMap_span_singleton ha hb hflat hproper
  · have hsub : Ps ⊆ ((Ideal.span {flatten f}).comap φ).minimalPrimesFinset := by
      intro P hP
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hP
      exact Ideal.mem_minimalPrimesFinset.mpr (hminimal hg)
    have hflat : flatten f ≠ 0 := by
      simpa only [map_zero] using (flatten : SourcePolynomial ClosedField ≃ₐ[ClosedField] _).injective.ne hf
    have hbound := affineDegree_comap_bidegreeMap_span_singleton_le ha hb hflat
      (K1_14_6_2.flatten_bound f he hv)
    have hsum := sum_affineDegree_minimalPrimes_comap_bidegreeMap_span_singleton_le ha hb
      (flatten f)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => affineDegree_nonneg P)).trans
      (hsum.trans (by simpa [φ, Nat.card_eq_fintype_card] using hbound))
  · intro x hroot hreg
    obtain ⟨g, hg, hd, hz⟩ := positive_factor_at_root f hf _ _ hroot hreg
    refine ⟨component g, Finset.mem_image.mpr
      ⟨g, Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨hg, hd⟩), rfl⟩, ?_⟩
    change monomialPoint _ x ∈ zeroLocus ClosedField ((Ideal.span {flatten g}).comap φ)
    rw [show φ = monomialMap ClosedField (BoxVars a b) from bidegreeMap_eq_monomialMap a b,
      monomialPoint_mem_zeroLocus_comap_iff (fun i => single_mem_bidegreeExponents ha hb i),
      mem_zeroLocus_iff_le_ker_aeval, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    change MvPolynomial.eval x (flatten g) = 0
    rwa [eval_flatten]
theorem sheet_cover {a b e v : ℕ} (ha : 0 < a) (hb : 0 < b)
    (f : Equation) (hf : 0 < f.natDegree) (he : f.natDegree ≤ e) (hseed : SeedBound f v)
    (T : Finset K) (z : K → K) (S : K → K[X])
    (hr : ∀ γ ∈ T, regularRoot f (z γ) (S γ)) :
    ∃ Ps : Finset (Ideal (BoxRing a b)),
      (∀ P ∈ Ps, P.IsPrime ∧ RingHom.ker (boxMap a b) ≤ P ∧
        (affineHilbertPolynomial P).natDegree = 2) ∧
      Ps.card ≤ e ∧
      (∑ P ∈ Ps, affineDegree P) ≤ (e * b ^ 2 + 2 * v * a * b : ℕ) ∧
      ∀ γ ∈ T, ∃ P ∈ Ps, point a b z S γ ∈ zeroLocus ClosedField P := by
  let ι := algebraMap FX ClosedField
  let F := extendEquation f
  have hnat : F.natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (MvPolynomial.map_injective _ ι.injective) f
  have hF : F ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by rw [hnat]; exact hf)
  have hcoeff : ∀ j, (F.coeff j).totalDegree ≤ v := by
    intro j
    change ((f.map (MvPolynomial.map ι)).coeff j).totalDegree ≤ v
    rw [Polynomial.coeff_map]
    exact (Finset.sup_mono (support_map_subset _ _)).trans (hseed j)
  obtain ⟨Ps, hdim, hcount, hsum, hcover⟩ :=
    regular_components ha hb F hF (hnat.trans_le he) hcoeff
  refine ⟨Ps, hdim, hcount, hsum, fun γ hγ => ?_⟩
  apply hcover (closedPoint (z γ) (S γ))
  · rw [show F = extendEquation f from rfl, extendEquation_eval, (hr γ hγ).1, map_zero]
  · rw [show F.derivative = extendEquation f.derivative from Polynomial.derivative_map _ _,
      extendEquation_eval]
    simpa only [map_zero] using ι.injective.ne (hr γ hγ).2.2
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open MvPolynomial
open K1_14_6 (ClosedField)
open scoped BigOperators
theorem curve_scale_of_cut (hcut : WeightedCut) : CurveScale := by
  classical
  intro a b D hD ha hb P hP hbase hdim
  let : P.IsPrime := hP
  have ha' := hD.trans_le ha
  have hb' := hD.trans_le hb
  have hnfinite : ¬(zeroLocus ClosedField P).Finite := fun h =>
    (show (affineHilbertPolynomial P).natDegree ≠ 0 by omega)
      ((finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero P).mp h)
  obtain ⟨x', hx', y', hy', hxy'⟩ :
      ∃ x' ∈ zeroLocus ClosedField P, ∃ y' ∈ zeroLocus ClosedField P, x' ≠ y' := by
    by_contra! h
    exact hnfinite ((show (zeroLocus ClosedField P).Subsingleton from
      fun _ hx _ hy => h _ hx _ hy).finite)
  have hcoord {z : BoxVars a b → ClosedField} (hz : z ∈ zeroLocus ClosedField P) :
      ∃ x : Option (Fin 2) → ClosedField, monomialPoint (BoxVars a b) x = z := by
    apply exists_monomialPoint_eq_of_mem_zeroLocus_ker (k := ClosedField)
      (fun i => single_mem_bidegreeExponents ha' hb' i)
    rw [← bidegreeMap_eq_monomialMap]
    exact zeroLocus_anti_mono hbase hz
  obtain ⟨x, rfl⟩ := hcoord hx'
  obtain ⟨y, rfl⟩ := hcoord hy'
  have hxy : x ≠ y := fun h => hxy' (congrArg (monomialPoint (BoxVars a b)) h)
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  let raw : MvPolynomial (Option (Fin 2)) ClosedField := MvPolynomial.X i - MvPolynomial.C (x i)
  have hraw : raw ∈ restrictBidegree (Fin 2) ClosedField 1 1 := by
    apply Submodule.sub_mem
    · rw [mem_restrictBidegree, support_X]
      intro m hm
      rw [Finset.mem_singleton] at hm
      subst m
      exact mem_bidegreeExponents.mp (single_mem_bidegreeExponents (by decide) (by decide) i)
    · rw [mem_restrictBidegree]
      intro m hm
      have hm0 := Finset.mem_singleton.mp (support_C_subset hm)
      subst m
      simp
  obtain ⟨q, hq⟩ := bidegreeMap_surjective (R := ClosedField) ha' hb' raw
  have heval (z : Option (Fin 2) → ClosedField) :
      aeval (monomialPoint (BoxVars a b) z) q = z i - x i := by
    rw [aeval_monomialPoint, ← bidegreeMap_eq_monomialMap, hq]
    simp [raw]
  have hproper : q ∉ P := by
    intro h
    exact hi ((sub_eq_zero.mp ((heval y).symm.trans (hy' _ h))).symm)
  have hpoint : monomialPoint (BoxVars a b) x ∈ zeroLocus ClosedField (P ⊔ Ideal.span {q}) :=
    mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hx', (heval x).trans (sub_self _)⟩
  obtain ⟨Q, hQ, hQpoint⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hpoint (by simp)
  have hmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
  have hdQ : (affineHilbertPolynomial Q).natDegree = 0 := by
    have := principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin
    omega
  obtain ⟨hfinite, hdegree⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := ClosedField) Q hdQ
  have hone : (1 : ℚ) ≤ affineDegree Q := by
    refine le_trans ?_ hdegree
    exact_mod_cast (show 1 ≤ (zeroLocus ClosedField Q).ncard by
      simpa using Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hQpoint) hfinite)
  have hsum : (1 : ℚ) ≤ ∑ Q ∈ (P ⊔ Ideal.span {q}).minimalPrimesFinset, affineDegree Q :=
    hone.trans (Finset.single_le_sum (fun J _ => affineDegree_nonneg J)
      (Ideal.mem_minimalPrimesFinset.mpr hmin))
  have hbound := hcut a b 1 1 D 1 ha' hb' hD (by decide)
    (by simpa using ha) (by simpa using hb) P hP hbase (by omega) q hproper (by rwa [hq])
  rw [Nat.cast_one, one_mul] at hbound
  simpa only [mul_one] using (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg D)).trans hbound
end
end P1_7_7
end
section
namespace P1_7_7
noncomputable section
open Polynomial MvPolynomial
open P1 (AnchorModel AnchoredFamily HighBand I K agreement node p)
open P1_7 (AdjacentChart GradeIndex InBand Reduced regularRoot grades scale)
open K1_14 (Equation FX L SeedBound seedEmbedding)
open scoped BigOperators
def c1 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ) (H : L[X]),
    0 < M.overhead.toNat → AdjacentChart M F H →
    ∃ C : CRTChart M.overhead.toNat, ∀ γ ∈ Γ,
      C.Recovers (poleProduct H) (M.label γ) (F.scalar γ)
def c2 : Prop :=
  ∀ (d w e v : ℕ), 0 < w → 2 * w ≤ d → d < p →
    ∀ (G : FX[X]), G.Monic → G.natDegree = 2 * w →
    G.eval (algebraMap L[X] FX Polynomial.X) ≠ 0 →
    (∀ j : I, G.eval (seedEmbedding (node j)) ≠ 0) →
    ∀ (f : Equation), 0 < f.natDegree → f.natDegree ≤ e → SeedBound f v →
    ∀ (T : Finset K) (z : K → K) (S : K → K[X]) (word : I → K),
      (∀ γ ∈ T, (S γ).natDegree ≤ d) →
      (∀ γ ∈ T, regularRoot f (z γ) (S γ)) →
      ∀ (C : CRTChart w), (∀ γ ∈ T, C.Recovers G (z γ) (S γ)) →
        ShortCharts d w e v word T z S
def c3 : Prop := WeightedCut
private theorem pole_data {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {H : L[X]} (h : AdjacentChart M F H) :
    (poleProduct H).Monic ∧ (poleProduct H).natDegree = 2 * M.overhead.toNat ∧
    (poleProduct H).eval (algebraMap L[X] FX Polynomial.X) ≠ 0 ∧
    ∀ j : I, (poleProduct H).eval (seedEmbedding (node j)) ≠ 0 := by
  obtain ⟨hm, hd, _, hm', hd', _, _, hn, _, _, _⟩ := h
  let B := H * H.map (frobenius L p)
  let incl := algebraMap L[X] FX
  have hb : B.Monic := hm.mul hm'
  have hdeg : B.natDegree = 2 * M.overhead.toNat := by
    rw [show B = H * H.map (frobenius L p) from rfl,
      Polynomial.natDegree_mul hm.ne_zero hm'.ne_zero, hd, hd']
    omega
  refine ⟨hb.map _, (hb.natDegree_map _).trans hdeg, ?_, ?_⟩
  · have heval : (poleProduct H).eval (incl Polynomial.X) = incl B := by
      rw [poleProduct, Polynomial.eval_map]
      change B.eval₂ (incl.comp Polynomial.C) (incl Polynomial.X) = incl B
      rw [← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]
    rw [heval]
    exact (map_ne_zero_iff incl (IsFractionRing.injective L[X] FX)).mpr hb.ne_zero
  · intro j
    let x := algebraMap K L (node j)
    have heval : (poleProduct H).eval (seedEmbedding (node j)) = incl (Polynomial.C (B.eval x)) := by
      rw [poleProduct, Polynomial.eval_map]
      change B.eval₂ (incl.comp Polynomial.C) ((incl.comp Polynomial.C) x) = _
      rw [Polynomial.eval₂_hom]
      rfl
    have hval : B.eval x ≠ 0 := by
      rw [show B = H * H.map (frobenius L p) from rfl, Polynomial.eval_mul]
      exact mul_ne_zero (hn j).1 (hn j).2
    rw [heval]
    exact (map_ne_zero_iff incl (IsFractionRing.injective L[X] FX)).mpr
      ((map_ne_zero_iff _ Polynomial.C_injective).mpr hval)
end
end P1_7_7
end
section
namespace P1_7_7_1
noncomputable section
open Polynomial Module K1_14_1
open K1_14 (L)
open scoped Polynomial BigOperators
open private K1_14_1_1.quotientBasis K1_14_1_1.mulMatrix K1_14_1_1.mulMatrix_entry mulMatrix_specialize
  mulMatrix_det_ne_zero eval_map_constants from ProximityPrize.SubmissionLower.Fast065
private theorem det_degree {w : ℕ} (A : Matrix (Fin w) (Fin w) L[X])
    (hA : ∀ i j, (A i j).natDegree ≤ 1) : A.det.natDegree ≤ w := by
  rw [Matrix.det_apply']
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine natDegree_mul_le.trans ?_
  rw [natDegree_intCast, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  calc
    (∑ i : Fin w, (A (σ i) i).natDegree) ≤ ∑ _ : Fin w, 1 :=
      Finset.sum_le_sum fun i _ => hA _ _
    _ = w := by simp
private theorem affine_remainder {b : L[X]} (hb : b.Monic) (a₀ a₁ : L[X]) (j : ℕ) :
    (((a₀.map C + Polynomial.X (R := L) • a₁.map C) %ₘ b.map C).coeff j).natDegree ≤ 1 := by
  rw [add_modByMonic, smul_modByMonic, ← map_modByMonic C hb, ← map_modByMonic C hb,
    coeff_add, coeff_smul, coeff_map, coeff_map, smul_eq_mul]
  exact (natDegree_add_le _ _).trans (max_le (by simp) (by
    exact natDegree_mul_le.trans (by simp)))
private theorem bounded_solution {b : Polynomial L[X]} {w : ℕ}
    (hb : b.Monic) (hd : b.natDegree = w) (a q : Polynomial L[X])
    (ha : ∀ i j, (K1_14_1_1.mulMatrix hb hd a i j).natDegree ≤ 1)
    (hq : ∀ j, (((-q) %ₘ b).coeff j).natDegree ≤ 1) :
    ∃ t : Polynomial L[X], t.degree < b.degree ∧
      b ∣ a * t + C (K1_14_1_1.mulMatrix hb hd a).det * q ∧
      ∀ j, (t.coeff j).natDegree ≤ w := by
  let basis := K1_14_1_1.quotientBasis hb hd
  let matrix := K1_14_1_1.mulMatrix hb hd a
  let target := AdjoinRoot.mk b (-q)
  let solution := basis.equivFun.symm (matrix.cramer (basis.equivFun target))
  have hcoord : basis.equivFun solution = matrix.cramer (basis.equivFun target) :=
    basis.equivFun.apply_symm_apply _
  have hsol : AdjoinRoot.mk b a * solution = matrix.det • target := by
    apply basis.equivFun.injective
    have hvec := Algebra.leftMulMatrix_mulVec_repr basis (AdjoinRoot.mk b a) solution
    change matrix.mulVec (basis.repr solution) = ⇑(basis.repr (AdjoinRoot.mk b a * solution)) at hvec
    rw [← Basis.equivFun_apply, ← Basis.equivFun_apply, hcoord, Matrix.mulVec_cramer] at hvec
    rw [map_smul]
    exact hvec.symm
  obtain ⟨t, ht⟩ := AdjoinRoot.mk_surjective solution
  have hrep : AdjoinRoot.mk b (t %ₘ b) = solution := by
    rw [← AdjoinRoot.modByMonicHom_mk hb, AdjoinRoot.mk_leftInverse hb, ht]
  have hdeg := degree_modByMonic_lt t hb
  refine ⟨t %ₘ b, hdeg, AdjoinRoot.mk_eq_zero.mp ?_, ?_⟩
  · change AdjoinRoot.mk b (a * (t %ₘ b) + C matrix.det * q) = 0
    rw [map_add, map_mul, map_mul, hrep, hsol, AdjoinRoot.mk_C]
    simp [target, Algebra.smul_def]
  · have hrepr (f : Polynomial L[X]) (i : Fin w) :
        basis.equivFun (AdjoinRoot.mk b f) i = (f %ₘ b).coeff i := by
      rw [Basis.equivFun_apply]
      change ((AdjoinRoot.powerBasisAux' hb).reindex (finCongr hd)).repr _ _ = _
      rw [Basis.repr_reindex_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
        AdjoinRoot.modByMonicHom_mk]
      rfl
    intro j
    by_cases hj : j < w
    · let i : Fin w := ⟨j, hj⟩
      have he := congrFun hcoord i
      rw [← ht, hrepr, Matrix.cramer_apply] at he
      change ((t %ₘ b).coeff j) = _ at he
      rw [he]
      apply det_degree
      intro k l
      rw [Matrix.updateCol_apply]
      split
      · exact (hrepr (-q) k).symm ▸ hq k
      · exact ha k l
    · have hz : (t %ₘ b).coeff j = 0 := by
        apply coeff_eq_zero_of_degree_lt
        exact hdeg.trans_le (degree_le_natDegree.trans (by exact_mod_cast (hd ▸ le_of_not_gt hj)))
      simp [hz]
theorem bounded_crt {w : ℕ} (D : PoleData w) :
    ∃ C : CRTLift D, (∀ i, (C.denominator i).natDegree ≤ w) ∧
      ∀ i j, ((C.numerator i).coeff j).natDegree ≤ w := by
  have block (i : Fin 2) :
      ∃ (d : L[X]) (N : Polynomial L[X]),
        d ≠ 0 ∧ N.degree < (2 * w : ℕ) ∧
        (D.block (otherBlock i)).map C ∣ N ∧
        (D.block i).map C ∣
          ((D.constant i).map C + C (Polynomial.X (R := L)) * (D.slope i).map C) * N +
            C (d * Polynomial.X (R := L)) * (D.offset i).map C ∧
        (∀ z, IsCoprime (residueAt D i z) (D.block i) → d.eval z ≠ 0) ∧
        d.natDegree ≤ w ∧ ∀ j, (N.coeff j).natDegree ≤ w := by
    let b := (D.block i).map (C : L →+* L[X])
    let e := (D.block (otherBlock i)).map (C : L →+* L[X])
    let amplitude := (D.constant i).map (C : L →+* L[X]) +
      C (Polynomial.X (R := L)) * (D.slope i).map (C : L →+* L[X])
    let a := amplitude * e
    let q := C (Polynomial.X (R := L)) * (D.offset i).map (C : L →+* L[X])
    have hb : b.Monic := (D.monic i).map _
    have he : e.Monic := (D.monic (otherBlock i)).map _
    have hbd : b.natDegree = w := ((D.monic i).natDegree_map _).trans (D.degree i)
    have hed : e.natDegree = w :=
      ((D.monic (otherBlock i)).natDegree_map _).trans (D.degree (otherBlock i))
    have hcop : IsCoprime (D.block (otherBlock i)) (D.block i) := by
      fin_cases i
      · exact D.coprime.symm
      · exact D.coprime
    let d := (K1_14_1_1.mulMatrix hb hbd a).det
    have hregular (z : L) (hz : IsCoprime (residueAt D i z) (D.block i)) :
        d.eval z ≠ 0 := by
      have hmapa : a.map (evalRingHom z) =
          residueAt D i z * D.block (otherBlock i) := by
        simp only [a, amplitude, e, residueAt, Polynomial.map_add, Polynomial.map_mul,
          Polynomial.map_C, eval_map_constants, coe_evalRingHom, eval_X]
      change (evalRingHom z) (K1_14_1_1.mulMatrix hb hbd a).det ≠ 0
      rw [mulMatrix_specialize (evalRingHom z) hb hbd (D.monic i) (D.degree i)
        (eval_map_constants z (D.block i)) hmapa]
      exact mulMatrix_det_ne_zero _ _ (hz.mul_left hcop)
    have hd : d ≠ 0 := by
      have hc : IsCoprime (D.constant i) (D.block i) := (D.determinant i).of_mul_left_right
      intro hd
      exact hregular 0 (by simpa [residueAt] using hc) (by simp [hd])
    have ha (k l : Fin w) : (K1_14_1_1.mulMatrix hb hbd a k l).natDegree ≤ 1 := by
      rw [K1_14_1_1.mulMatrix_entry]
      let f := D.block (otherBlock i) * Polynomial.X ^ (l : ℕ)
      have hform : a * Polynomial.X ^ (l : ℕ) =
          (D.constant i * f).map C + Polynomial.X (R := L) • (D.slope i * f).map C := by
        simp only [a, amplitude, e, f, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
          smul_eq_C_mul, add_mul, mul_assoc]
      rw [hform]
      exact affine_remainder (D.monic i) _ _ _
    have hq (j : ℕ) : (((-q) %ₘ b).coeff j).natDegree ≤ 1 := by
      have hform : -q = (0 : L[X]).map C + Polynomial.X (R := L) • (-D.offset i).map C := by
        simp [q, smul_eq_C_mul]
      rw [hform]
      exact affine_remainder (D.monic i) _ _ _
    obtain ⟨t, ht, hdiv, htseed⟩ := bounded_solution hb hbd a q ha hq
    refine ⟨d, e * t, hd, ?_, dvd_mul_right _ _, ?_, hregular, det_degree _ ha, ?_⟩
    · by_cases ht0 : t = 0
      · rw [ht0, mul_zero, degree_zero]
        exact WithBot.bot_lt_coe _
      have htn : t.natDegree < w := by
        rw [degree_eq_natDegree ht0, degree_eq_natDegree hb.ne_zero, hbd, Nat.cast_lt] at ht
        exact ht
      apply (degree_mul_le e t).trans_lt
      rw [degree_eq_natDegree he.ne_zero, degree_eq_natDegree ht0, hed, ← Nat.cast_add, Nat.cast_lt]
      omega
    · change b ∣ amplitude * (e * t) + C (d * Polynomial.X (R := L)) * (D.offset i).map C
      simpa only [a, q, ← mul_assoc, ← map_mul] using hdiv
    · intro j
      rw [coeff_mul]
      apply natDegree_sum_le_of_forall_le
      intro k _
      rw [show e.coeff k.1 = C ((D.block (otherBlock i)).coeff k.1) from coeff_map _ _]
      exact (natDegree_C_mul_le _ _).trans (htseed k.2)
  choose d N hN using block
  exact ⟨⟨d, N, fun i => (hN i).1, fun i => (hN i).2.1, fun i => (hN i).2.2.1,
    fun i => (hN i).2.2.2.1, fun i => (hN i).2.2.2.2.1⟩,
    fun i => (hN i).2.2.2.2.2.1, fun i => (hN i).2.2.2.2.2.2⟩
end
end P1_7_7_1
end
section
namespace P1_7_7_1
noncomputable section
open P1 (AnchorModel AnchoredFamily K p)
open P1_7 (AdjacentChart)
open K1_14 (L FX liftPoly seedEmbedding)
open K1_14_1 (PoleData CRTLift MarkResidues seedPair)
open K1_14_6 (Biform rootPoint)
open P1_7_7 (CRTChart box)
open MvPolynomial (mem_restrictBidegree mem_restrictBidegree_mono mul_mem_restrictBidegree)
open Polynomial
open scoped Polynomial BigOperators
set_option backward.isDefEq.respectTransparency false in
private theorem chart_poles {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : L[X]) (hH : AdjacentChart M F H) :
    ∃ D : PoleData M.overhead.toNat,
      K1_14_1.poleProduct D = H * H.map (frobenius L p) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  let σ := frobenius L p
  rcases hH with ⟨hm, hd, _, hm', hd', _, hcop, _, hdet, hdet', hmarks⟩
  let A := liftPoly (M.factor * M.A₀)
  let B := liftPoly (M.factor * M.A₁)
  let Q := liftPoly M.Q
  have hdet0 : IsCoprime (Q * A) H := by
    simpa [Q, A, liftPoly, mul_assoc] using hdet
  have hdet1 : IsCoprime (Q.map σ * A.map σ) (H.map σ) := by
    simpa [Q, A, liftPoly, mul_assoc, σ, Polynomial.map_mul] using hdet'
  let D : PoleData M.overhead.toNat :=
    ⟨![H, H.map σ], ![Q, Q.map σ], ![A, A.map σ], ![B, B.map σ],
      fun i => by fin_cases i <;> first | exact hm | exact hm',
      fun i => by fin_cases i <;> first | exact hd | exact hd',
      hcop, fun i => by fin_cases i <;> first | exact hdet0 | exact hdet1⟩
  refine ⟨D, rfl, ?_⟩
  · intro γ hγ i
    let z := algebraMap K L (M.label γ)
    have hz : liftPoly (M.factor * M.amplitude γ) = A + (@Polynomial.C L _) z * B := by
      simp [A, B, z, P1.ModelAt.amplitude, liftPoly, mul_add, mul_left_comm]
    obtain ⟨h₀, h₁, hr₀, hr₁⟩ := hmarks γ hγ
    fin_cases i
    · change IsCoprime (A + (@Polynomial.C L _) z * B) H ∧
        H ∣ (A + (@Polynomial.C L _) z * B) * liftPoly (F.scalar γ) + (@Polynomial.C L _) z * Q
      rw [← hz]
      exact ⟨h₀, hr₀⟩
    · have hσ : (liftPoly (M.factor * M.amplitude γ)).map σ =
          A.map σ + (@Polynomial.C L _) (z^p) * B.map σ := by
        rw [hz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) (H.map σ) ∧
        H.map σ ∣ (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) * liftPoly (F.scalar γ) +
          (@Polynomial.C L _) (z^p) * Q.map σ
      rw [← hσ]
      exact ⟨h₁, hr₁⟩
private def constantEmbedding : L →+* FX :=
  (algebraMap L[X] FX).comp Polynomial.C
private def embed (i : Fin 2) : L[X] →+* Biform :=
  eval₂RingHom (MvPolynomial.C.comp constantEmbedding) (MvPolynomial.X (some i))
private theorem embed_mem (i : Fin 2) {P : L[X]} {w : ℕ} (hP : P.natDegree ≤ w) :
    embed i P ∈ box 0 w := by
  have hvar : (MvPolynomial.X (some i) : Biform) ∈ box 0 1 := by
    classical
    rw [mem_restrictBidegree, MvPolynomial.support_X]
    intro m hm
    rw [Finset.mem_singleton] at hm
    subst m
    simp [Finsupp.some_single_some]
  rw [congrArg (embed i) P.as_sum_range_C_mul_X_pow, map_sum]
  apply (box 0 w).sum_mem
  intro j hj
  have hjw : j ≤ w := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hP
  have hC : MvPolynomial.C (constantEmbedding (P.coeff j)) ∈ box 0 0 := by
    classical
    rw [mem_restrictBidegree, MvPolynomial.support_C]
    split_ifs <;> simp
  have hpow : (MvPolynomial.X (some i) : Biform) ^ j ∈ box 0 j := by
    simpa only [Nat.mul_zero, Nat.mul_one] using K1_14_6_1.box_pow hvar j
  have hprod := mul_mem_restrictBidegree hC hpow
  simpa [embed] using mem_restrictBidegree_mono hprod (by simp : 0 + 0 ≤ 0)
    (by simpa using hjw)
private theorem eval_embed (z : K) (S : K[X]) (i : Fin 2) :
    (MvPolynomial.eval (rootPoint z S)).comp (embed i) =
      constantEmbedding.comp (evalRingHom (seedPair z i)) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [embed, RingHom.comp_apply]
  · fin_cases i <;>
      simp [embed, RingHom.comp_apply, rootPoint, seedPair, seedEmbedding, constantEmbedding]
private def commonDen {w : ℕ} {D : PoleData w} (B : CRTLift D) : Biform :=
  embed 0 (B.denominator 0) * embed 1 (B.denominator 1)
private def commonNum {w : ℕ} {D : PoleData w} (B : CRTLift D) : Biform[X] :=
  C (embed 1 (B.denominator 1)) * (B.numerator 0).map (embed 0) +
  C (embed 0 (B.denominator 0)) * (B.numerator 1).map (embed 1)
private theorem commonNum_degree {w : ℕ} (hw : 0 < w) {D : PoleData w} (B : CRTLift D) :
    (commonNum B).natDegree < 2 * w := by
  have hN (i : Fin 2) : (B.numerator i).natDegree < 2 * w := by
    by_cases hz : B.numerator i = 0
    · rw [hz, natDegree_zero]
      omega
    · exact (natDegree_lt_iff_degree_lt hz).mpr (B.numerator_degree i)
  unfold commonNum
  apply (natDegree_add_le _ _).trans_lt
  exact max_lt
    ((natDegree_C_mul_le _ _).trans_lt (natDegree_map_le.trans_lt (hN 0)))
    ((natDegree_C_mul_le _ _).trans_lt (natDegree_map_le.trans_lt (hN 1)))
private theorem commonDen_mem {w : ℕ} {D : PoleData w} (B : CRTLift D)
    (hd : ∀ i, (B.denominator i).natDegree ≤ w) :
    commonDen B ∈ box 0 (2 * w) := by
  simpa only [commonDen, Nat.zero_add, two_mul] using
    mul_mem_restrictBidegree (embed_mem 0 (hd 0)) (embed_mem 1 (hd 1))
private theorem commonNum_mem {w : ℕ} {D : PoleData w} (B : CRTLift D)
    (hd : ∀ i, (B.denominator i).natDegree ≤ w)
    (hn : ∀ i j, ((B.numerator i).coeff j).natDegree ≤ w) (j : ℕ) :
    (commonNum B).coeff j ∈ box 0 (2 * w) := by
  rw [commonNum, coeff_add, coeff_C_mul, coeff_C_mul, coeff_map, coeff_map, two_mul]
  apply (box 0 (w+w)).add_mem
  · simpa only [Nat.zero_add] using
      mul_mem_restrictBidegree (embed_mem 1 (hd 1)) (embed_mem 0 (hn 0 j))
  · simpa only [Nat.zero_add] using
      mul_mem_restrictBidegree (embed_mem 0 (hd 0)) (embed_mem 1 (hn 1 j))
private def commonChart {w : ℕ} (hw : 0 < w) {D : PoleData w} (B : CRTLift D)
    (hd : ∀ i, (B.denominator i).natDegree ≤ w)
    (hn : ∀ i j, ((B.numerator i).coeff j).natDegree ≤ w) : CRTChart w :=
  ⟨commonDen B, commonNum B, commonNum_degree hw B, commonDen_mem B hd, commonNum_mem B hd hn⟩
private theorem common_recovers {w : ℕ} (hw : 0 < w) {D : PoleData w} (B : CRTLift D)
    (hd : ∀ i, (B.denominator i).natDegree ≤ w)
    (hn : ∀ i j, ((B.numerator i).coeff j).natDegree ≤ w)
    {z : K} {S : K[X]} (hm : MarkResidues D z S) :
    (commonChart hw B hd hn).Recovers ((K1_14_1.poleProduct D).map (algebraMap L FX)) z S := by
  let ev := MvPolynomial.eval (rootPoint z S)
  let a (i : Fin 2) := constantEmbedding ((B.denominator i).eval (seedPair z i))
  let N (i : Fin 2) := ((B.numerator i).map (evalRingHom (seedPair z i))).map constantEmbedding
  have he (i : Fin 2) (P : L[X]) : ev (embed i P) =
      constantEmbedding (P.eval (seedPair z i)) :=
    DFunLike.congr_fun (eval_embed z S i) P
  have hN (i : Fin 2) : ((B.numerator i).map (embed i)).map ev = N i := by
    change ((B.numerator i).map (embed i)).map ev =
      ((B.numerator i).map (evalRingHom (seedPair z i))).map constantEmbedding
    have hcomp : ev.comp (embed i) = constantEmbedding.comp (evalRingHom (seedPair z i)) :=
      eval_embed z S i
    rw [Polynomial.map_map, Polynomial.map_map, hcomp]
  have ha (i : Fin 2) : a i ≠ 0 := by
    have hinj : Function.Injective constantEmbedding :=
      (IsFractionRing.injective L[X] FX).comp Polynomial.C_injective
    exact (map_ne_zero_iff _ hinj).mpr (B.regular i _ (hm i).1)
  have hden : ev (commonDen B) = a 0 * a 1 := by
    rw [commonDen, map_mul, he, he]
  have hnum : (commonNum B).map ev = C (a 1) * N 0 + C (a 0) * N 1 := by
    rw [commonNum, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_C, hN, hN, he, he]
  change ev (commonDen B) ≠ 0 ∧
    (K1_14_1.poleProduct D).map (algebraMap L FX) ∣
      S.map seedEmbedding - (ev (commonDen B))⁻¹ • (commonNum B).map ev
  rw [hden, hnum]
  refine ⟨mul_ne_zero (ha 0) (ha 1), ?_⟩
  have hS : (liftPoly S).map constantEmbedding = S.map seedEmbedding := by
    rw [liftPoly, Polynomial.map_map]
    rfl
  have hL : (K1_14_1_2.markedLift B (seedPair z)).map constantEmbedding =
      C (a 0)⁻¹ * N 0 + C (a 1)⁻¹ * N 1 := by
    simp only [a, N, K1_14_1_2.markedLift, Fin.sum_univ_two, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C, map_inv₀]
  have hc₀ : (a 0 * a 1)⁻¹ * a 1 = (a 0)⁻¹ := by
    field_simp [ha 0, ha 1]
  have hc₁ : (a 0 * a 1)⁻¹ * a 0 = (a 1)⁻¹ := by
    field_simp [ha 0, ha 1]
  have hL' : (a 0 * a 1)⁻¹ • (C (a 1) * N 0 + C (a 0) * N 1) =
      (K1_14_1_2.markedLift B (seedPair z)).map constantEmbedding := by
    rw [hL, smul_eq_C_mul, mul_add, ← mul_assoc, ← mul_assoc,
      ← Polynomial.C_mul, ← Polynomial.C_mul, hc₀, hc₁]
  rw [hL', ← hS, ← Polynomial.map_sub]
  exact Polynomial.map_dvd constantEmbedding (K1_14_1_2.markedLift_residue B hm)
theorem proof : P1_7_7.c1 := by
  intro u del M Γ F H hw hH
  obtain ⟨D, hD, hmarks⟩ := chart_poles M F H hH
  obtain ⟨B, hd, hn⟩ := bounded_crt D
  refine ⟨commonChart hw B hd hn, ?_⟩
  intro γ hγ
  rw [P1_7_7.poleProduct, ← hD]
  exact common_recovers hw B hd hn (hmarks γ hγ)
end
end P1_7_7_1
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open Polynomial
open scoped BigOperators
private theorem zero_of_zero_data {E ι : Type} [Field E] [Fintype ι]
    (nodes : ι → E) (hinj : Function.Injective nodes)
    (ξ : E) (hne : ∀ i, nodes i ≠ ξ) (sites : Finset ι)
    (d m r : ℕ) (hlen : d < m + sites.card + r)
    (G : E[X]) (hm : G.Monic) (hG : G.natDegree = m)
    (hc : G.eval ξ ≠ 0) (hn : ∀ i ∈ sites, G.eval (nodes i) ≠ 0)
    (P : E[X]) (hP : P.natDegree ≤ d)
    (hres : P %ₘ G = 0) (hsites : ∀ i ∈ sites, P.eval (nodes i) = 0)
    (hjets : ∀ j : Fin r, (taylor ξ P).coeff j = 0) : P = 0 := by
  classical
  obtain ⟨Q, hQ⟩ := (modByMonic_eq_zero_iff_dvd hm).mp hres
  have ht : (Polynomial.X : E[X]) ^ r ∣ taylor ξ P :=
    X_pow_dvd_iff.mpr fun j hj => hjets ⟨j, hj⟩
  rw [hQ, taylor_mul] at ht
  have hunit : ¬ (Polynomial.X : E[X]) ∣ taylor ξ G := by
    rwa [X_dvd_iff, taylor_coeff_zero]
  obtain ⟨R, hR⟩ := prime_X.pow_dvd_of_dvd_mul_left r hunit ht
  by_cases hRzero : R = 0
  · have hz : taylor ξ Q = 0 := by rw [hR, hRzero, mul_zero]
    have hQzero : Q = 0 := by
      rw [← taylor_zero Q, ← neg_add_cancel ξ, ← taylor_taylor, hz, map_zero]
    rw [hQ, hQzero, mul_zero]
  · have hQzero : Q ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hR
      exact (mul_ne_zero (pow_ne_zero _ X_ne_zero) hRzero) hR.symm
    have hdeg : m + (r + R.natDegree) ≤ d := by
      rwa [hQ, natDegree_mul hm.ne_zero hQzero, hG, ← natDegree_taylor Q ξ,
        hR, natDegree_mul (pow_ne_zero _ X_ne_zero) hRzero, natDegree_X_pow] at hP
    have hroots (i : ι) (hi : i ∈ sites) : R.eval (nodes i - ξ) = 0 := by
      have hi' := hsites i hi
      rw [hQ, eval_mul] at hi'
      have h := (mul_eq_zero.mp hi').resolve_left (hn i hi)
      rw [← sub_add_cancel (nodes i) ξ, ← taylor_eval, hR, eval_mul, eval_pow, eval_X] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr (hne i)))
    have hshift : Function.Injective (fun i => nodes i - ξ) := fun _ _ h =>
      hinj (sub_left_inj.mp h)
    have hcard := FrobeniusLocator.Strata.root_nodes_card_le _ hshift R hRzero sites hroots
    omega
private theorem linear_pi_apply {E ι : Type} [Field E] [Fintype ι] [DecidableEq ι]
    (L : (ι → E) →ₗ[E] E) (v : ι → E) :
    L v = ∑ i, L (Pi.single i 1) * v i := by
  calc
    L v = L (∑ i, v i • Pi.single i 1) := congrArg L (pi_eq_sum_univ' v)
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem interpolation_weights {E ι : Type} [Field E] [Fintype ι]
    (nodes : ι → E) (hinj : Function.Injective nodes)
    (ξ : E) (hne : ∀ i, nodes i ≠ ξ) (sites : Finset ι)
    (d m r : ℕ) (hlen : d < m + sites.card + r) (hmpos : 0 < m)
    (G : E[X]) (hm : G.Monic) (hG : G.natDegree = m)
    (hc : G.eval ξ ≠ 0) (hn : ∀ i ∈ sites, G.eval (nodes i) ≠ 0)
    (word : ι → E) (x : E) :
    ∃ c : E, ∃ b : Fin m → E, ∃ a : Fin r → E,
      ∀ P : E[X], P.natDegree ≤ d →
        (∀ i ∈ sites, P.eval (nodes i) = word i) →
        P.eval x = c + (∑ j, b j * (P %ₘ G).coeff j) +
          ∑ j, a j * (taylor ξ P).coeff j := by
  classical
  let V := degreeLE E (d : WithBot ℕ)
  let A := sites → E
  let B := Fin m → E
  let J := Fin r → E
  let evalAtNodes : V →ₗ[E] A := LinearMap.pi fun i =>
    (leval (nodes i)).comp V.subtype
  let residue : V →ₗ[E] B := LinearMap.pi fun j =>
    ((lcoeff E (j : ℕ)).comp (modByMonicHom G)).comp V.subtype
  let jets : V →ₗ[E] J := LinearMap.pi fun j =>
    ((lcoeff E (j : ℕ)).comp (taylor ξ)).comp V.subtype
  let data : V →ₗ[E] A × B × J := evalAtNodes.prod (residue.prod jets)
  have hG1 : G ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hG
    omega
  have hker : LinearMap.ker data = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro P hP
    apply Subtype.ext
    have hsite (i : sites) : P.1.eval (nodes i) = 0 :=
      congrFun (congrArg Prod.fst hP) i
    have hres (j : Fin m) : (P.1 %ₘ G).coeff j = 0 :=
      congrFun (congrArg (fun v => v.2.1) hP) j
    have hj (j : Fin r) : (taylor ξ P.1).coeff j = 0 :=
      congrFun (congrArg (fun v => v.2.2) hP) j
    have hres0 : P.1 %ₘ G = 0 := by
      ext j
      rw [coeff_zero]
      by_cases hjm : j < m
      · exact hres ⟨j, hjm⟩
      · apply coeff_eq_zero_of_natDegree_lt
        exact (natDegree_modByMonic_lt P.1 hm hG1).trans_le (hG.trans_le (Nat.le_of_not_gt hjm))
    exact zero_of_zero_data nodes hinj ξ hne sites d m r hlen G hm hG hc hn P.1
      (natDegree_le_iff_degree_le.mpr (mem_degreeLE.mp P.2))
      hres0 (fun i hi => hsite ⟨i, hi⟩) hj
  have hleft : ∃ lift : (A × B × J) →ₗ[E] V, lift.comp data = LinearMap.id := by
    apply LinearMap.exists_leftInverse_of_injective
    exact hker
  obtain ⟨lift, hlift⟩ := hleft
  let value := ((leval x).comp V.subtype).comp lift
  let fixed : A := fun i => word i
  let insertResidue := (LinearMap.inr E A (B × J)).comp (LinearMap.inl E B J)
  let insertJets := (LinearMap.inr E A (B × J)).comp (LinearMap.inr E B J)
  let readResidue := value.comp insertResidue
  let readJets := value.comp insertJets
  refine ⟨value (fixed, 0, 0), (fun j => readResidue (Pi.single j 1)),
    (fun j => readJets (Pi.single j 1)), ?_⟩
  intro P hP hs
  let P' : V := ⟨P, mem_degreeLE.mpr (natDegree_le_iff_degree_le.mp hP)⟩
  have hx : value (data P') = P.eval x := by
    change (lift (data P')).1.eval x = _
    rw [show lift (data P') = P' from DFunLike.congr_fun hlift P']
  rw [← hx]
  have hd : data P' = (fixed, 0, 0) + insertResidue (residue P') + insertJets (jets P') := by
    change (evalAtNodes P', residue P', jets P') = _
    rw [show evalAtNodes P' = fixed from funext fun i => hs i i.property]
    simp [insertResidue, insertJets]
  rw [hd, map_add, map_add]
  change value (fixed, 0, 0) + readResidue (residue P') + readJets (jets P') = _
  rw [linear_pi_apply readResidue (residue P'), linear_pi_apply readJets (jets P')]
  rfl
end
end P1_7_7_2
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open P1 (K p)
open K1_14 (Equation FX SeedBound seedEmbedding atX liftPoly)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant box_pow separant_bound ordinate_mem cleared_bound cleared
  markEval eval_cleared derivativeAt)
open P1_7_7 (box)
open MvPolynomial
open scoped Polynomial
open private eval_center factorial_ne_zero from ProximityPrize.SubmissionLower.Fast074
local notation "Y" => MvPolynomial.X (R := FX) (none : Option (Fin 2))
def jetNumerator (f : Biform) (t : ℕ) : Fin (t+1) → Biform :=
  Fin.cases (separant f ^ (2*t) * Y) fun i =>
    (((i.val+1).factorial : FX)⁻¹) •
      (separant f ^ (2*t - (2*i.val+1)) * cleared f i.val)
private theorem jet_pad {t : ℕ} (i : Fin t) :
    2*t - (2*i.val+1) + (2*i.val+1) = 2*t := by
  have hi := i.isLt
  omega
theorem jet_bound {e v t : ℕ} {f : Equation} (he : 0 < e)
    (hf : f.natDegree ≤ e) (hv : SeedBound f v) (j : Fin (t+1)) :
    jetNumerator (flatten f) t j ∈ box (1 + 2*t*(e-1)) (2*t*v) := by
  have hsep := separant_bound hf hv
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [jetNumerator, Fin.cases_zero, Nat.add_comm, Nat.add_zero, Nat.zero_add] using
      mul_mem_restrictBidegree (box_pow hsep (2*t)) ordinate_mem
  · simp only [jetNumerator, Fin.cases_succ]
    apply (box _ _).smul_mem
    have h := mul_mem_restrictBidegree (box_pow hsep (2*t - (2*i.val+1)))
      (cleared_bound he hf hv i.val)
    have hy : (2*t - (2*i.val+1))*(e-1) + (1+(2*i.val+1)*(e-1)) =
        1+2*t*(e-1) := by
      calc
        _ = 1+((2*t - (2*i.val+1))+(2*i.val+1))*(e-1) := by ring
        _ = _ := by rw [jet_pad i]
    rwa [hy, ← Nat.add_mul, jet_pad i] at h
theorem jet_eval {t : ℕ} (htp : t < p) (f : Biform) (z : K)
    (S : K[X]) (hroot : markEval z S f = 0) (j : Fin (t+1)) :
    markEval z S (jetNumerator f t j) = markEval z S (separant f ^ (2*t)) *
      (Polynomial.taylor (algebraMap K1_14.L[X] FX Polynomial.X) (S.map seedEmbedding)).coeff j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [jetNumerator, Fin.cases_zero, map_mul, Fin.val_zero,
      Polynomial.taylor_coeff_zero, eval_center]
    rw [show markEval z S Y = atX S from eval_X _]
  · let a := markEval z S (separant f)
    let j' := i.val+1
    have hjp : j' < p := (Nat.succ_le_of_lt i.isLt).trans_lt htp
    have hfactor : derivativeAt S j' = (j'.factorial : FX) *
        (Polynomial.taylor (algebraMap K1_14.L[X] FX Polynomial.X) (S.map seedEmbedding)).coeff j' := by
      rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_center]
      have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) j') S
      dsimp only [derivativeAt]
      rw [← h, LinearMap.smul_apply]
      simp only [nsmul_eq_mul, atX, liftPoly, Polynomial.map_mul,
        Polynomial.map_natCast, map_mul, map_natCast]
    simp only [jetNumerator, Fin.cases_succ, MvPolynomial.smul_eq_C_mul, map_mul, map_pow,
      MvPolynomial.eval_C, eval_cleared _ _ _ hroot, Fin.val_succ]
    change (j'.factorial : FX)⁻¹ *
      (a ^ (2*t - (2*i.val+1)) * (a ^ (2*i.val+1) * derivativeAt S j')) =
        a ^ (2*t) * _
    rw [hfactor]
    calc
      _ = ((j'.factorial : FX) * (j'.factorial : FX)⁻¹) *
          (a ^ (2*t - (2*i.val+1)) * a ^ (2*i.val+1)) *
          (Polynomial.taylor (algebraMap K1_14.L[X] FX Polynomial.X) (S.map seedEmbedding)).coeff j' := by ring
      _ = _ := by rw [mul_inv_cancel₀ (factorial_ne_zero hjp), one_mul, ← pow_add, jet_pad i]
end
end P1_7_7_2
end
section
set_option autoImplicit false
namespace P1_7_7_2
noncomputable section
open P1 (I K node p)
open P1_7 (regularRoot)
open P1_7_7 (CRTChart box localOrd localSeed)
open K1_14 (L FX seedEmbedding)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten separant box_pow separant_bound markEval eval_flatten eval_separant)
open Polynomial MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
private abbrev center : FX := algebraMap L[X] FX Polynomial.X
private theorem mapped_node_ne_center (x : K) : seedEmbedding x ≠ center := by
  intro h
  exact (Polynomial.X_ne_C (algebraMap K L x))
    ((IsFractionRing.injective L[X] FX) h.symm)
private theorem residue_coeff {w : ℕ} (C : CRTChart w)
    (G : FX[X]) (hm : G.Monic) (hd : G.natDegree = 2*w)
    {z : K} {S : K[X]} (h : C.Recovers G z S) (i : ℕ) :
    markEval z S (C.numerator.coeff i) =
      markEval z S C.denominator * ((S.map seedEmbedding) %ₘ G).coeff i := by
  let ev := markEval z S
  let P := S.map seedEmbedding
  let R := (ev C.denominator)⁻¹ • C.numerator.map ev
  change ev C.denominator ≠ 0 ∧ G ∣ P - R at h
  obtain ⟨hnz, Q, hQ⟩ := h
  have hdeg : R.natDegree < 2*w :=
    (Polynomial.natDegree_smul_le _ _).trans_lt
      (Polynomial.natDegree_map_le.trans_lt C.degree_numerator)
  have hRg : R.degree < G.degree := by
    rw [degree_eq_natDegree hm.ne_zero, hd]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hdeg)
  have hmod : P %ₘ G = R :=
    (div_modByMonic_unique Q R hm ⟨by rw [← hQ]; ring, hRg⟩).2
  change ev (C.numerator.coeff i) = ev C.denominator * (P %ₘ G).coeff i
  rw [hmod, Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_map, ← mul_assoc,
    mul_inv_cancel₀ hnz, one_mul]
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem proof : P1_7_7.c2 := by
  classical
  intro d w e v hw hwd hdp G hG hd hcenter hnodes f hf hfe hfv
    T z S word hS hroot C hCRT U hUT sites _hcard hfixed
  let t := d - 2*w - sites.card
  let r := d - 2*w + 1 - sites.card
  have hlength : d < 2*w + sites.card + r := by dsimp only [r]; omega
  have hrt : r ≤ t+1 := by dsimp only [r, t]; omega
  have htp : t < p := by dsimp only [t]; omega
  have he := hf.trans_le hfe
  choose c b a hweights using fun j : I =>
    interpolation_weights (seedEmbedding ∘ node)
      (seedEmbedding.injective.comp IRSProfile.domain.injective)
      center (fun i => mapped_node_ne_center (node i)) sites d (2*w) r hlength
      (by omega) G hG hd hcenter (fun i _ => hnodes i) (seedEmbedding ∘ word)
      (seedEmbedding (node j))
  let D := separant (flatten f) ^ (2*t)
  let R (j : I) : Biform := ∑ i, b j i • C.numerator.coeff i
  let J (j : I) : Biform := ∑ i, a j i • jetNumerator (flatten f) t (Fin.castLE hrt i)
  let cut (j : I) : Biform :=
    (c j - seedEmbedding (word j)) • (C.denominator * D) +
      (R j * D + C.denominator * J j)
  have hD : D ∈ box (2*t*(e-1)) (2*t*v) :=
    box_pow (separant_bound hfe hfv) (2*t)
  have hR (j : I) : R j ∈ box 0 (2*w) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (C.bound_numerator i)
  have hJ (j : I) : J j ∈ box (1 + 2*t*(e-1)) (2*t*v) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (jet_bound he hfe hfv _)
  refine ⟨cut, ?_, ?_⟩
  · intro j
    change cut j ∈ box (1 + 2*t*(e-1)) (2*w + 2*t*v)
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      exact mem_restrictBidegree_mono (mul_mem_restrictBidegree C.bound_denominator hD)
        (by rw [Nat.zero_add]; exact Nat.le_add_left _ _) le_rfl
    · apply Submodule.add_mem
      · exact mem_restrictBidegree_mono (mul_mem_restrictBidegree (hR j) hD)
          (by rw [Nat.zero_add]; exact Nat.le_add_left _ _) le_rfl
      · simpa only [Nat.zero_add] using mul_mem_restrictBidegree C.bound_denominator (hJ j)
  · intro γ hγ j
    let ev := markEval (z γ) (S γ)
    let P := (S γ).map seedEmbedding
    have hγT := hUT hγ
    have hchart := hCRT γ hγT
    have hreg := hroot γ hγT
    have hDne : ev D ≠ 0 := by
      change markEval (z γ) (S γ) (separant (flatten f) ^ (2*t)) ≠ 0
      rw [map_pow, eval_separant]
      exact pow_ne_zero _ hreg.2.2
    have hroot' : ev (flatten f) = 0 :=
      (eval_flatten (z γ) (S γ) f).trans hreg.1
    have hevC (x : FX) : ev (MvPolynomial.C x) = x := MvPolynomial.eval_C x
    have hval := hweights j P (Polynomial.natDegree_map_le.trans (hS γ hγT))
      (fun i hi => by
        change ((S γ).map seedEmbedding).eval (seedEmbedding (node i)) =
          seedEmbedding (word i)
        rw [Polynomial.eval_map_apply, hfixed γ hγ i hi])
    rw [show P.eval (seedEmbedding (node j)) = seedEmbedding ((S γ).eval (node j)) from
      Polynomial.eval_map_apply seedEmbedding (node j)] at hval
    have hRcoeff (i : Fin (2*w)) :
        ev (C.numerator.coeff i) = ev C.denominator * (P %ₘ G).coeff i :=
      residue_coeff C G hG hd hchart i
    have hRval : ev (R j) =
        ev C.denominator * ∑ i, b j i * (P %ₘ G).coeff i := by
      simp only [R, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, hevC, hRcoeff, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hJcoeff (i : Fin r) :
        ev (jetNumerator (flatten f) t (Fin.castLE hrt i)) =
          ev D * (taylor center P).coeff i :=
      jet_eval htp (flatten f) (z γ) (S γ) hroot' (Fin.castLE hrt i)
    have hJval : ev (J j) =
        ev D * ∑ i, a j i * (taylor center P).coeff i := by
      simp only [J, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, hevC, hJcoeff, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hcut : ev (cut j) = (ev C.denominator * ev D) *
        (seedEmbedding ((S γ).eval (node j)) - seedEmbedding (word j)) := by
      simp only [cut, map_add, map_mul, MvPolynomial.smul_eq_C_mul, hevC, hRval, hJval]
      rw [hval]
      ring
    change ev (cut j) = 0 ↔ _
    rw [hcut, mul_eq_zero, or_iff_right (mul_ne_zero hchart.1 hDne), sub_eq_zero]
    exact seedEmbedding.injective.eq_iff
end
end P1_7_7_2
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial
open scoped BigOperators
private theorem split_exponent {σ : Type*} {a b t : ℕ} {e : Option σ →₀ ℕ}
    (he : e ∈ bidegreeExponents σ ((t + 1) * a) ((t + 1) * b)) :
    ∃ u ∈ bidegreeExponents σ a b, ∃ v ∈ bidegreeExponents σ (t * a) (t * b),
      u + v = e := by
  obtain ⟨hord, hseed⟩ := mem_bidegreeExponents.mp he
  rw [Nat.add_mul, Nat.one_mul] at hord hseed
  obtain ⟨u, hu, hdu⟩ := Finsupp.exists_le_degree_eq e.some
    (e.some.degree - t * b) (Nat.sub_le _ _)
  obtain ⟨v, hv⟩ := le_iff_exists_add.mp hu
  have hseed_v : v.degree ≤ t * b := by
    have h := congrArg Finsupp.degree hv
    rw [map_add, hdu] at h
    omega
  have hord_sum : e none - t * a + min (e none) (t * a) = e none := by omega
  refine ⟨u.optionElim (e none - t * a), mem_bidegreeExponents.mpr ?_,
    v.optionElim (min (e none) (t * a)), mem_bidegreeExponents.mpr ?_, ?_⟩
  · rw [Finsupp.optionElim_apply_none, Finsupp.some_optionElim, hdu]
    omega
  · rw [Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
    exact ⟨min_le_right _ _, hseed_v⟩
  · rw [← Finsupp.optionElim_add, hord_sum, ← hv, Finsupp.optionElim_some]
private theorem lift_monomial {σ R : Type*} [CommSemiring R] (a b : ℕ) :
    ∀ t (e : Option σ →₀ ℕ), e ∈ bidegreeExponents σ (t * a) (t * b) →
      ∃ f : MvPolynomial (bidegreeExponents σ a b) R,
        bidegreeMap σ R a b f = monomial e 1 ∧ f.totalDegree ≤ t := by
  intro t
  induction t with
  | zero =>
    intro e he
    obtain ⟨hord, hseed⟩ := mem_bidegreeExponents.mp he
    have hv : e.some = 0 := (Finsupp.degree_eq_zero_iff _).mp (by omega)
    have he0 : e = 0 := by
      rw [← Finsupp.optionElim_some e, hv, show e none = 0 by omega]
      simp
    subst e
    exact ⟨1, by simp, by simp⟩
  | succ t ih =>
    intro e he
    obtain ⟨u, hu, v, hv, rfl⟩ := split_exponent he
    obtain ⟨f, hf, hd⟩ := ih v hv
    let x : bidegreeExponents σ a b := ⟨u, hu⟩
    refine ⟨MvPolynomial.X x * f, ?_, ?_⟩
    · rw [map_mul, bidegreeMap_X, hf, monomial_mul_monomial, one_mul]
    · have hx : (MvPolynomial.X x : MvPolynomial (bidegreeExponents σ a b) R).totalDegree ≤ 1 :=
        (totalDegree_monomial_le _ _).trans_eq (Finsupp.degree_single _ _)
      exact (totalDegree_mul _ _).trans ((Nat.add_le_add hx hd).trans_eq (Nat.add_comm 1 t))
theorem lift_box {σ R : Type*} [CommSemiring R] {a b t : ℕ}
    {g : MvPolynomial (Option σ) R} (hg : g ∈ restrictBidegree σ R (t * a) (t * b)) :
    ∃ f : MvPolynomial (bidegreeExponents σ a b) R,
      bidegreeMap σ R a b f = g ∧ f.totalDegree ≤ t := by
  classical
  choose f hf hd using fun e : g.support ↦ lift_monomial (σ := σ) (R := R) a b t e.val
    (mem_bidegreeExponents.mpr (mem_restrictBidegree.mp hg e e.2))
  refine ⟨∑ e : g.support, C (g.coeff e) * f e, ?_, ?_⟩
  · simp only [map_sum, map_mul, bidegreeMap, aeval_C, algebraMap_eq]
    change (∑ e : g.support, C (g.coeff e) * bidegreeMap σ R a b (f e)) = g
    simp only [hf, C_mul_monomial, mul_one]
    rw [Finset.sum_coe_sort g.support fun e ↦ monomial e (g.coeff e)]
    exact g.support_sum_monomial_coeff
  · exact totalDegree_finsetSum_le fun e _ ↦
      (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hd e)
theorem pow_mem_box {σ R : Type*} [CommSemiring R] {m n : ℕ}
    {g : MvPolynomial (Option σ) R} (hg : g ∈ restrictBidegree σ R m n) (r : ℕ) :
    g ^ r ∈ restrictBidegree σ R (r * m) (r * n) := by
  induction r with
  | zero =>
    rw [pow_zero, Nat.zero_mul, Nat.zero_mul, mem_restrictBidegree]
    intro e he
    have he' : e ∈ (monomial (0 : Option σ →₀ ℕ) (1 : R)).support := by
      rw [monomial_zero', C_1]
      exact he
    have he0 := Finset.mem_singleton.mp (support_monomial_subset he')
    subst e
    simp
  | succ r ih =>
    simpa only [pow_succ, Nat.succ_mul] using mul_mem_restrictBidegree ih hg
end
end P1_7_7_3
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial Filter
open private quotientDegreeLEFactor quotientDegreeLEFactor_surjective from
  ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbert
open private mulQuotient mulQuotient_mk from
  ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComponents
variable {k σ : Type*} [Field k]
def cutPower (P : Ideal (MvPolynomial σ k)) (q : MvPolynomial σ k) (i : ℕ) :
    Ideal (MvPolynomial σ k) :=
  P ⊔ Ideal.span {q ^ i}
private theorem mul_mem_cutPower_iff {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime)
    {q : MvPolynomial σ k} (hq : q ∉ P) (i : ℕ) (x : MvPolynomial σ k) :
    q * x ∈ cutPower P q (i + 1) ↔ x ∈ cutPower P q i := by
  unfold cutPower
  constructor
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hv
    have hcancel : q * (x - c * q ^ i) ∈ P := by
      have heq : q * (x - c * q ^ i) = u := by
        calc q * (x - c * q ^ i) = q * x - c * q ^ (i + 1) := by rw [pow_succ]; ring
          _ = u := by rw [← huv]; ring
      exact heq ▸ hu
    have hp : x - c * q ^ i ∈ P := (hP.mem_or_mem hcancel).resolve_left hq
    exact Submodule.mem_sup.mpr ⟨_, hp, _, Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩,
      sub_add_cancel _ _⟩
  · intro hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hv
    exact Submodule.mem_sup.mpr ⟨q * u, P.mul_mem_left _ hu, c * q ^ (i + 1),
      Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩, by rw [pow_succ]; ring⟩
private theorem cutPower_succ_le_one (P : Ideal (MvPolynomial σ k))
    (q : MvPolynomial σ k) (i : ℕ) : cutPower P q (i + 1) ≤ cutPower P q 1 := by
  apply sup_le_sup_left
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  rw [pow_one, pow_succ]
  exact Ideal.mem_span_singleton'.mpr ⟨q ^ i, rfl⟩
private theorem hilbert_step [Finite σ] {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime)
    {q : MvPolynomial σ k} (hq : q ∉ P) (i N : ℕ) :
    affineHilbertFunction (cutPower P q i) N +
        affineHilbertFunction (cutPower P q 1) (N + q.totalDegree) ≤
      affineHilbertFunction (cutPower P q (i + 1)) (N + q.totalDegree) := by
  let J := cutPower P q i
  let J' := cutPower P q (i + 1)
  let J₁ := cutPower P q 1
  let B := N + q.totalDegree
  let project := quotientDegreeLEFactor (cutPower_succ_le_one P q i) B
  have hmem : ∀ x ∈ J, q * x ∈ J' := fun x hx ↦ (mul_mem_cutPower_iff hP hq i x).mpr hx
  let mul := mulQuotient J J' q hmem
  have hinj : Function.Injective mul := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change mulQuotient _ _ _ _ _ = mulQuotient _ _ _ _ _ at hxy
    rw [mulQuotient_mk, mulQuotient_mk, Ideal.Quotient.eq, ← mul_sub] at hxy
    exact Ideal.Quotient.eq.mpr ((mul_mem_cutPower_iff hP hq i _).mp hxy)
  have hfiltered : ∀ x : quotientDegreeLE J N, mul x ∈ quotientDegreeLE J' B := by
    intro x
    obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
    rw [← hpx]
    change mulQuotient _ _ _ _ _ ∈ _
    rw [mulQuotient_mk]
    exact mk_mem_quotientDegreeLE ((totalDegree_mul _ _).trans
      ((Nat.add_le_add_left hp _).trans_eq (Nat.add_comm _ _)))
  let lift := (mul.domRestrict (quotientDegreeLE J N)).codRestrict
      (quotientDegreeLE J' B) hfiltered
  have hker : ∀ x, lift x ∈ LinearMap.ker project := by
    intro x
    obtain ⟨p, _hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change Ideal.Quotient.factor (cutPower_succ_le_one P q i) (mul x) = 0
    rw [← hpx]
    change Ideal.Quotient.factor _ (mulQuotient _ _ _ _ _) = 0
    rw [mulQuotient_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.mem_sup_right
    rw [pow_one]
    exact Ideal.mem_span_singleton'.mpr ⟨p, mul_comm p q⟩
  have hf : Function.Injective (lift.codRestrict (LinearMap.ker project) hker) := by
    intro x y hxy
    exact Subtype.ext (hinj (congrArg
      (fun z : LinearMap.ker project ↦ (z.val.val : MvPolynomial σ k ⧸ J')) hxy))
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  have hproject := project.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    (quotientDegreeLEFactor_surjective (cutPower_succ_le_one P q i) B), finrank_top] at hproject
  unfold affineHilbertFunction
  change Module.finrank k (quotientDegreeLE J N) + Module.finrank k (quotientDegreeLE J₁ B) ≤
    Module.finrank k (quotientDegreeLE J' B)
  change Module.finrank k (quotientDegreeLE J N) ≤ Module.finrank k (LinearMap.ker project) at hdim
  change Module.finrank k (quotientDegreeLE J₁ B) + Module.finrank k (LinearMap.ker project) =
    Module.finrank k (quotientDegreeLE J' B) at hproject
  omega
private theorem hilbert_power [Finite σ] {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime)
    {q : MvPolynomial σ k} (hq : q ∉ P) (r N : ℕ) :
    r * affineHilbertFunction (cutPower P q 1) N ≤
      affineHilbertFunction (cutPower P q r) (N + r * q.totalDegree) := by
  induction r with
  | zero => simp
  | succ i ih =>
    simp only [Nat.succ_mul, ← Nat.add_assoc]
    have hN : N ≤ N + i * q.totalDegree + q.totalDegree := by omega
    exact (Nat.add_le_add ih (affineHilbertFunction_mono _ hN)).trans
      (hilbert_step hP hq i (N + i * q.totalDegree))
theorem power_coeff_bound [Finite σ] {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime)
    {q : MvPolynomial σ k} (hq : q ∉ P) {r t : ℕ} {f : MvPolynomial σ k}
    (hf : f ∉ P) (hcut : P ⊔ Ideal.span {f} = cutPower P q r)
    (hdeg : f.totalDegree ≤ t) :
    (r : ℚ) * (affineHilbertPolynomial (P ⊔ Ideal.span {q})).coeff
      ((affineHilbertPolynomial P).natDegree - 1) ≤
      (t : ℚ) * (affineHilbertPolynomial P).natDegree *
        (affineHilbertPolynomial P).leadingCoeff := by
  let d := (affineHilbertPolynomial P).natDegree - 1
  let H := affineHilbertPolynomial (cutPower P q 1)
  let H' := affineHilbertPolynomial (cutPower P q r)
  let b := r * q.totalDegree
  have hH : H.natDegree ≤ d := by
    simpa only [H, d, cutPower, pow_one] using
      (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime hP hq le_rfl).1
  obtain ⟨hH', hbound⟩ :=
    principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime hP hf hdeg
  rw [hcut] at hH' hbound
  let S := Polynomial.C (r : ℚ) * Polynomial.taylor (-(b : ℚ)) H
  have hS : S.natDegree ≤ d :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by rwa [Polynomial.natDegree_taylor])
  have hcoeff : S.coeff d ≤ H'.coeff d := by
    apply Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hS hH'
    obtain ⟨N₀, hN₀⟩ := exists_eval_affineHilbertPolynomial (cutPower P q 1)
    filter_upwards [eventually_eval_affineHilbertPolynomial (cutPower P q r),
      eventually_ge_atTop (N₀ + b)] with N hN hlarge
    have hbN : b ≤ N := by omega
    have hsmall : N₀ ≤ N - b := by omega
    dsimp only [S]
    rw [show H'.eval (N : ℚ) = _ from hN, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.taylor_eval, ← sub_eq_add_neg, ← Nat.cast_sub hbN,
      show H.eval ((N - b : ℕ) : ℚ) = _ from hN₀ _ hsmall]
    have hlayers := hilbert_power hP hq r (N - b)
    change r * affineHilbertFunction (cutPower P q 1) (N - b) ≤
      affineHilbertFunction (cutPower P q r) (N - b + b) at hlayers
    rw [Nat.sub_add_cancel hbN] at hlayers
    exact_mod_cast hlayers
  dsimp only [S] at hcoeff
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_taylor_of_natDegree_le _ hH] at hcoeff
  simpa only [H, cutPower, pow_one] using hcoeff.trans hbound
end
end P1_7_7_3
end
section
namespace P1_7_7_3
noncomputable section
open MvPolynomial
open P1_7_7 (BoxRing boxMap)
open scoped BigOperators
private theorem cut_eq_of_sub_mem {R : Type*} [CommRing R] {P : Ideal R} {f g : R}
    (h : f - g ∈ P) : P ⊔ Ideal.span {f} = P ⊔ Ideal.span {g} := by
  apply le_antisymm <;> refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · exact Submodule.mem_sup.mpr ⟨_, h, _, Ideal.mem_span_singleton_self g, sub_add_cancel _ _⟩
  · exact Submodule.mem_sup.mpr ⟨g - f, by simpa only [neg_sub] using P.neg_mem h,
      _, Ideal.mem_span_singleton_self f, sub_add_cancel _ _⟩
theorem proof : P1_7_7.c3 := by
  intro a b m n r t _ha _hb hr _ht hm hn P hP hker hdim q hq hbox
  have := hP
  have hpower := mem_restrictBidegree_mono (pow_mem_box hbox r) hm hn
  obtain ⟨f, hf, hdeg⟩ := lift_box hpower
  have hsub : f - q ^ r ∈ P := hker <| by
    change boxMap a b (f - q ^ r) = 0
    rw [map_sub, map_pow, hf, sub_self]
  have hfP : f ∉ P := by
    intro hfP
    have hqr : q ^ r ∈ P := by simpa only [sub_sub_cancel] using P.sub_mem hfP hsub
    exact hq ((hP.pow_mem_iff_mem r hr).mp hqr)
  have hcut : P ⊔ Ideal.span {f} = cutPower P q r := cut_eq_of_sub_mem hsub
  have hcoeff := power_coeff_bound hP hq hfP hcut hdeg
  let d := (affineHilbertPolynomial P).natDegree - 1
  let J := P ⊔ Ideal.span {q}
  have hQdim : ∀ Q ∈ J.minimalPrimesFinset, (affineHilbertPolynomial Q).natDegree = d := by
    intro Q hQ
    have h := principalCut_natDegree_affineHilbertPolynomial_add_one hq
      (Ideal.mem_minimalPrimesFinset.mp hQ)
    exact Nat.eq_sub_of_add_eq h
  have hJdim : (affineHilbertPolynomial J).natDegree ≤ d :=
    (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime hP hq le_rfl).1
  have hsum := sum_coeff_affineHilbertPolynomial_minimalPrimes_le J hJdim
  have hfactor : (d.factorial : ℚ) * ((affineHilbertPolynomial P).natDegree : ℚ) =
      ((affineHilbertPolynomial P).natDegree.factorial : ℚ) := by
    have hd : d + 1 = (affineHilbertPolynomial P).natDegree := Nat.sub_add_cancel hdim
    calc
      _ = ((d + 1).factorial : ℚ) := by rw [Nat.factorial_succ, Nat.cast_mul, hd, mul_comm]
      _ = _ := by rw [hd]
  change (r : ℚ) * (∑ Q ∈ J.minimalPrimesFinset, affineDegree Q) ≤ (t : ℚ) * affineDegree P
  calc
    _ = (d.factorial : ℚ) *
        ((r : ℚ) * ∑ Q ∈ J.minimalPrimesFinset, (affineHilbertPolynomial Q).coeff d) := by
      have hsum_eq : (∑ Q ∈ J.minimalPrimesFinset, affineDegree Q) =
          (d.factorial : ℚ) * ∑ Q ∈ J.minimalPrimesFinset, (affineHilbertPolynomial Q).coeff d := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun Q hQ ↦ ?_
        rw [affineDegree, Polynomial.leadingCoeff, hQdim Q hQ]
      rw [hsum_eq, mul_left_comm]
    _ ≤ (d.factorial : ℚ) * ((t : ℚ) * (affineHilbertPolynomial P).natDegree *
        (affineHilbertPolynomial P).leadingCoeff) :=
      mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg r)).trans hcoeff) (Nat.cast_nonneg _)
    _ = (t : ℚ) * (((d.factorial : ℚ) * (affineHilbertPolynomial P).natDegree) *
        (affineHilbertPolynomial P).leadingCoeff) := by ring
    _ = _ := by rw [hfactor, affineDegree]
end
end P1_7_7_3
end
