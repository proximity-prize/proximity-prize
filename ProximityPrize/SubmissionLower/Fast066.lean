import ProximityPrize.SubmissionLower.Fast058
import ProximityPrize.SubmissionLower.Fast061
import ProximityPrize.SubmissionLower.Fast062
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace K1_13_7_6
noncomputable section
open K1_13 K1_13_7 MvPolynomial
def c1 : Prop :=
  ∀ {σ : Type} [Finite σ] (φ : MvPolynomial σ GeometricX →ₐ[GeometricX] Lower),
    Function.Surjective φ →
    ∀ (p : PrimeSpectrum Lower) (L : MvPolynomial σ GeometricX),
      L.totalDegree ≤ 1 → φ L ∉ p.asIdeal →
      ∀ qs : Finset (PrimeSpectrum Lower),
        (∀ q ∈ qs, q.asIdeal ∈ (cutIdeal p (φ L)).minimalPrimes) →
        (∀ q ∈ qs, localColength q (cutIdeal p (φ L)) < ⊤) →
        cutCost (chartDegree φ) p (φ L) qs ≤ chartDegree φ p
def c2 : Prop :=
  ∀ (f g h : Lower) (D : PrimeSpectrum Lower → ℚ),
    (∀ q, 0 ≤ D q) →
    (∀ (y : LowerPoint) (q : PrimeSpectrum Lower), q.asIdeal = pointIdeal y → 1 ≤ D q) →
    (∀ (t : Lower), t ∈ ({f, g, h} : Set Lower) →
      ∀ (p : PrimeSpectrum Lower), t ∉ p.asIdeal →
        ∀ qs : Finset (PrimeSpectrum Lower),
          (∀ q ∈ qs, q.asIdeal ∈ (cutIdeal p t).minimalPrimes) →
          (∀ q ∈ qs, localColength q (cutIdeal p t) < ⊤) →
          cutCost D p t qs ≤ D p) →
    ∀ (points : Finset LowerPoint) (w : ℕ),
      (∀ y ∈ points, ∃ q : PrimeSpectrum Lower,
        q.asIdeal = pointIdeal y ∧ q.asIdeal ∈ (Ideal.span {f, g, h}).minimalPrimes ∧
        (w : ℕ∞) ≤ localColength q (Ideal.span {f, g, h}) ∧
        localColength q (Ideal.span {f, g, h}) < ⊤) →
      (points.card : ℚ) * w ≤ D zeroPrime
theorem of_children (h1 : c1) (h2 : c2) : K1_13_7.c6 := by
  classical
  intro P Q R hP hQ hR points hpoints
  let f := genericRow P
  let g := genericRow Q
  let h := genericRow R
  let D := chartDegree chartMap
  have hcuts : ∀ t : Lower, t ∈ ({f, g, h} : Set Lower) →
      ∃ L : MvPolynomial chartExponents GeometricX, chartMap L = t ∧ L.totalDegree ≤ 1 := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact chart_lift P hP
    · exact chart_lift Q hQ
    · exact chart_lift R hR
  have hpay : ∀ t : Lower, t ∈ ({f, g, h} : Set Lower) →
      ∀ p : PrimeSpectrum Lower, t ∉ p.asIdeal →
        ∀ qs : Finset (PrimeSpectrum Lower),
          (∀ q ∈ qs, q.asIdeal ∈ (cutIdeal p t).minimalPrimes) →
          (∀ q ∈ qs, localColength q (cutIdeal p t) < ⊤) →
          cutCost D p t qs ≤ D p := by
    intro t ht p hp qs hmin hfin
    obtain ⟨L, rfl, hL⟩ := hcuts t ht
    exact h1 chartMap chartMap_surjective p L hL hp qs hmin hfin
  have hpoints_cost := h2 f g h D
    (fun q => affineDegree_nonneg (q.asIdeal.comap chartMap))
    (fun y q hy => (chartDegree_eq_one chartMap chartMap_surjective y q hy).ge)
    hpay points (41481 * (41481 - 33184 + 1) * 1037) hpoints
  have hbound := hpoints_cost.trans chartDegree_bound
  norm_num [totalCap, halfIndexCap] at hbound
  have hprice : isolatedPrice = 344924340099310 := by
    norm_num [isolatedPrice, ceilDiv]
  rw [hprice]
  by_contra! hlarge
  have hlarge' : (344924340099311 : ℚ) ≤ points.card := by exact_mod_cast hlarge
  linarith
end
end K1_13_7_6
end
section
set_option autoImplicit false
namespace K1_13_7_6_1
noncomputable section
variable {R : Type*} [CommRing R]
theorem exists_prime_factor [IsNoetherianRing R] {J : Ideal R} (hJ : J ≠ ⊤) :
    ∃ (a : R) (Q : Ideal R), a ∉ J ∧ Q.IsPrime ∧ ∀ x : R, x * a ∈ J ↔ x ∈ Q := by
  let _ := Ideal.Quotient.nontrivial_iff.mpr hJ
  obtain ⟨Q, hQ, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (1 : R ⧸ J) one_ne_zero
  obtain ⟨hp, z, hz⟩ := isAssociatedPrime_iff.mp hQ
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hann (x : R) : x * a ∈ J ↔ x ∈ Q := by
    rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot]
    change x * a ∈ J ↔ Ideal.Quotient.mk J (x * a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  refine ⟨a, Q, fun ha => hp.ne_top (Q.eq_top_of_isUnit_mem (hann 1 |>.mp ?_) isUnit_one),
    hp, hann⟩
  simpa only [one_mul] using ha
variable {k : Type*} [CommRing k] [Algebra k R]
def factorMul {J Q : Ideal R} {a : R} (ha : ∀ x : R, x * a ∈ J ↔ x ∈ Q) :
    (R ⧸ Q) →ₗ[k] R ⧸ J :=
  (Q.restrictScalars k).liftQ
    ((Ideal.Quotient.mkₐ k J).toLinearMap ∘ₗ LinearMap.mulLeft k a) fun x hx => by
      change Ideal.Quotient.mk J (a * x) = 0
      rw [mul_comm]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((ha x).mpr hx)
@[simp]
theorem factorMul_mk {J Q : Ideal R} {a : R} (ha : ∀ x : R, x * a ∈ J ↔ x ∈ Q) (x : R) :
    factorMul (k := k) ha (Ideal.Quotient.mk Q x) = Ideal.Quotient.mk J (a * x) := rfl
theorem factorMul_injective {J Q : Ideal R} {a : R} (ha : ∀ x : R, x * a ∈ J ↔ x ∈ Q) :
    Function.Injective (factorMul (k := k) ha) := by
  refine (LinearMap.ker_eq_bot.mp ?_)
  ext z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [LinearMap.mem_ker, factorMul_mk, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.Quotient.eq_zero_iff_mem, mul_comm, ha]
theorem factorMul_exact {J Q : Ideal R} {a : R} (ha : ∀ x : R, x * a ∈ J ↔ x ∈ Q) :
    Function.Exact (factorMul (k := k) ha)
      (Ideal.Quotient.factorₐ k (le_sup_left : J ≤ J ⊔ Ideal.span {a})).toLinearMap := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mk (J ⊔ Ideal.span {a}) x = 0 ↔
    Ideal.Quotient.mk J x ∈ LinearMap.range (factorMul (k := k) ha)
  rw [Ideal.Quotient.eq_zero_iff_mem, sup_comm J, Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨y, b, hb, rfl⟩
    exact ⟨Ideal.Quotient.mk Q y, by simp [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, mul_comm]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [factorMul_mk, mul_comm] at hz
    have hb : x - y * a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp
      (by rw [map_sub, hz, sub_self])
    exact ⟨y, x - y * a, hb, add_sub_cancel _ _⟩
theorem length_factor {J Q : Ideal R} {a : R} (ha : ∀ x : R, x * a ∈ J ↔ x ∈ Q) :
    Module.length R (R ⧸ J) =
      Module.length R (R ⧸ Q) + Module.length R (R ⧸ (J ⊔ Ideal.span {a})) :=
  Module.length_eq_add_of_exact _ _ (factorMul_injective (k := R) ha)
    (Ideal.Quotient.factor_surjective le_sup_left) (factorMul_exact (k := R) ha)
end
end K1_13_7_6_1
end
section
set_option autoImplicit false
namespace K1_13_7_6_1
noncomputable section
open Filter MvPolynomial Polynomial
variable {k σ : Type*} [Field k] [Finite σ]
theorem hilbertFunction_step {J K Q : Ideal (MvPolynomial σ k)} {a : MvPolynomial σ k}
    (hJK : J ≤ K) (haK : a ∈ K) (ha : ∀ x, x * a ∈ J ↔ x ∈ Q)
    {N : ℕ} (hN : a.totalDegree ≤ N) :
    affineHilbertFunction K N + affineHilbertFunction Q (N - a.totalDegree) ≤
      affineHilbertFunction J N := by
  let π := ((Ideal.Quotient.factorₐ k hJK).toLinearMap.domRestrict (quotientDegreeLE J N)).codRestrict
    (quotientDegreeLE K N) fun x => by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.2
      change Ideal.Quotient.factor hJK x ∈ quotientDegreeLE K N
      rw [← hpx, Ideal.Quotient.factor_mk]
      exact mk_mem_quotientDegreeLE hp
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.2
    exact ⟨⟨Ideal.Quotient.mk J p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hpy⟩
  let μ := ((factorMul (k := k) ha).domRestrict (quotientDegreeLE Q (N - a.totalDegree))).codRestrict
    (quotientDegreeLE J N) fun x => by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.2
      change factorMul ha x ∈ quotientDegreeLE J N
      rw [← hpx, factorMul_mk]
      exact mk_mem_quotientDegreeLE ((totalDegree_mul a p).trans (by omega))
  have hμ : ∀ x, μ x ∈ LinearMap.ker π := by
    intro x
    obtain ⟨p, -, hpx⟩ := mem_quotientDegreeLE.mp x.2
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change Ideal.Quotient.factor hJK (factorMul ha x) = 0
    rw [← hpx, factorMul_mk, Ideal.Quotient.factor_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (K.mul_mem_right _ haK)
  have hinj : Function.Injective (μ.codRestrict (LinearMap.ker π) hμ) := fun x y hxy =>
    Subtype.ext (factorMul_injective ha (congrArg (fun z => (z.val.val : MvPolynomial σ k ⧸ J)) hxy))
  have hker := LinearMap.finrank_le_finrank_of_injective hinj
  have hrank := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrank
  unfold affineHilbertFunction
  omega
theorem hilbertCoeff_step {J K Q : Ideal (MvPolynomial σ k)} {a : MvPolynomial σ k}
    (hJK : J ≤ K) (haK : a ∈ K) (ha : ∀ x, x * a ∈ J ↔ x ∈ Q)
    {d : ℕ} (hd : (affineHilbertPolynomial J).natDegree ≤ d) :
    (affineHilbertPolynomial K).coeff d + (affineHilbertPolynomial Q).coeff d ≤
      (affineHilbertPolynomial J).coeff d := by
  have hJQ : J ≤ Q := fun x hx => (ha x).mp (J.mul_mem_right _ hx)
  have hKd := (natDegree_affineHilbertPolynomial_le_of_le hJK).trans hd
  have hQd := (natDegree_affineHilbertPolynomial_le_of_le hJQ).trans hd
  let b := a.totalDegree
  let P : (Polynomial ℚ) := affineHilbertPolynomial K + taylor (-(b : ℚ)) (affineHilbertPolynomial Q)
  have hPd : P.natDegree ≤ d :=
    (natDegree_add_le_of_le hKd ((natDegree_taylor _ _).trans_le hQd)).trans (max_self d).le
  have hcoeff : P.coeff d =
      (affineHilbertPolynomial K).coeff d + (affineHilbertPolynomial Q).coeff d := by
    simp only [P, coeff_add, coeff_taylor_of_natDegree_le _ hQd]
  rw [← hcoeff]
  refine coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hPd hd ?_
  obtain ⟨T, hT⟩ := exists_eval_affineHilbertPolynomial Q
  filter_upwards [eventually_eval_affineHilbertPolynomial J,
    eventually_eval_affineHilbertPolynomial K, eventually_ge_atTop (T + b)] with N hJ hK hTN
  have hbN : b ≤ N := by omega
  simp only [P, Polynomial.eval_add, taylor_eval]
  rw [hJ, hK, ← sub_eq_add_neg, ← Nat.cast_sub hbN, hT _ (by omega)]
  exact_mod_cast hilbertFunction_step hJK haK ha hbN
end
end K1_13_7_6_1
end
section
set_option autoImplicit false
namespace K1_13_7_6_1
noncomputable section
open K1_13_7
theorem factor_localizes {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] {J Q : Ideal R} {a : R}
    (ha : ∀ x : R, x * a ∈ J ↔ x ∈ Q) (z : S) :
    z * algebraMap R S a ∈ J.map (algebraMap R S) ↔ z ∈ Q.map (algebraMap R S) := by
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
  rw [← IsLocalization.mk'_one (M := M) S a, ← IsLocalization.mk'_mul,
    IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
  simp only [← mul_assoc, ha]
theorem localColength_step {B J Q : Ideal Lower} (hBJ : B ≤ J) (hQ : Q.IsPrime)
    {a : Lower} (ha : ∀ x : Lower, x * a ∈ J ↔ x ∈ Q)
    {q : PrimeSpectrum Lower} (hq : q.asIdeal ∈ B.minimalPrimes) :
    localColength q J = (if Q = q.asIdeal then 1 else 0) +
      localColength q (J ⊔ Ideal.span {a}) := by
  classical
  let S := Localization.AtPrime q.asIdeal
  let f : Lower →+* S := algebraMap Lower S
  have hmul := length_factor (factor_localizes (S := S) q.asIdeal.primeCompl ha)
  change Module.length S (S ⧸ J.map f) = _ +
    Module.length S (S ⧸ (J ⊔ Ideal.span {a}).map f)
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hmul]
  congr 1
  by_cases h : Q = q.asIdeal
  · subst Q
    rw [ite_eq_left rfl]
    have he : q.asIdeal.map f = IsLocalRing.maximalIdeal S :=
      Localization.AtPrime.map_eq_maximalIdeal
    rw [he]
    have : IsSimpleModule S (S ⧸ IsLocalRing.maximalIdeal S) :=
      (isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal _).1)
    exact Module.length_eq_one S _
  · rw [ite_eq_right h]
    have hBQ : B ≤ Q := fun x hx => (ha x).mp (J.mul_mem_right _ (hBJ hx))
    have hnot : ¬ Q ≤ q.asIdeal := fun hle => h (hle.antisymm (hq.2 ⟨hQ, hBQ⟩ hle))
    obtain ⟨s, hs, hsq⟩ := Set.not_subset.mp hnot
    have hmap : Q.map f = ⊤ :=
      (Q.map f).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem f hs)
        (IsLocalization.map_units S (⟨s, hsq⟩ : q.asIdeal.primeCompl))
    rw [hmap]
    exact Module.length_eq_zero
end
end K1_13_7_6_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_2
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ {σ : Type} [Finite σ] (J Q : Ideal (MvPolynomial σ GeoField))
    (a : MvPolynomial σ GeoField),
    (∀ x, x * a ∈ J ↔ x ∈ Q) →
    ∀ d : ℕ, (affineHilbertPolynomial J).natDegree ≤ d →
      (affineHilbertPolynomial J).coeff d ≤
        (affineHilbertPolynomial (J ⊔ Ideal.span {a})).coeff d +
          (affineHilbertPolynomial Q).coeff d
def c2 : Prop :=
  ∀ (B : Boxes), Admissible B →
    ∀ (P : Ideal GeoJets5) (I : Finset (Fin 5)), P.IsPrime →
      DimLE P I.card → 0 ≤ mixedDegree B P I
theorem dim_mono {J Q : Ideal GeoJets5} {d : ℕ} (hJQ : J ≤ Q) (hJ : DimLE J d) :
    DimLE Q d :=
  (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hJQ)).trans hJ
private theorem mixed_step (hadd : c1) {B : Boxes} (hB : Admissible B) {I : Finset (Fin 5)}
    {J Q : Ideal GeoJets5} (hJ : DimLE J I.card) {a : GeoJets5}
    (ha : ∀ x, x * a ∈ J ↔ x ∈ Q) :
    mixedDegree B J I = mixedDegree B (sectionIdeal J a) I + mixedDegree B Q I := by
  classical
  have hdiag (U : Finset (Fin 5)) :
      let f := monomialMap GeoField (diagonalExponents B (fun i => if i ∈ U then 2 else 1))
      (affineHilbertPolynomial (J.comap f)).coeff I.card =
        (affineHilbertPolynomial ((sectionIdeal J a).comap f)).coeff I.card +
          (affineHilbertPolynomial (Q.comap f)).coeff I.card := by
    let t (i : Fin 5) : ℕ := if i ∈ U then 2 else 1
    have ht : ∀ i, 0 < t i := fun i => by by_cases hi : i ∈ U <;> simp [t, hi]
    let f := monomialMap GeoField (diagonalExponents B t)
    have hf : Function.Surjective f := diagonal_surjective hB ht
    obtain ⟨A, hA⟩ := hf a
    change (affineHilbertPolynomial (J.comap f)).coeff I.card =
      (affineHilbertPolynomial ((sectionIdeal J a).comap f)).coeff I.card +
        (affineHilbertPolynomial (Q.comap f)).coeff I.card
    have hsection : (sectionIdeal J a).comap f = J.comap f ⊔ Ideal.span {A} := by
      have hk : J.comap f ⊔ Ideal.span {A} =
          (J.comap f ⊔ Ideal.span {A}) ⊔ Ideal.comap f ⊥ :=
        (sup_eq_left.mpr ((Ideal.comap_mono bot_le).trans le_sup_left)).symm
      calc
        (sectionIdeal J a).comap f = ((J.comap f ⊔ Ideal.span {A}).map f).comap f := by
          rw [Ideal.map_sup, Ideal.map_comap_of_surjective f hf, Ideal.map_span,
            Set.image_singleton, hA, sectionIdeal]
        _ = J.comap f ⊔ Ideal.span {A} :=
          (Ideal.comap_map_of_surjective f hf _).trans hk.symm
    have hAann (x : MvPolynomial (diagonalExponents B t) GeoField) :
        x * A ∈ J.comap f ↔ x ∈ Q.comap f := by
      simp only [Ideal.mem_comap, map_mul, hA, ha]
    have hd := diagonal_degree_le hB hJ ht
    have hlow := K1_13_7_6_1.hilbertCoeff_step
      (J := J.comap f) (K := J.comap f ⊔ Ideal.span {A})
      le_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self A)) hAann hd
    rw [hsection]
    exact le_antisymm (hadd _ _ A hAann _ hd) hlow
  unfold mixedDegree
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  rw [hdiag U, mul_add]
theorem local_step {H J Q P : Ideal GeoJets5} (hHJ : H ≤ J) (hQ : Q.IsPrime)
    {a : GeoJets5} (ha : ∀ x, x * a ∈ J ↔ x ∈ Q) (hP : H.IsMinimalPrime P) :
    LengthAt J P hP.isPrime =
      (if Q = P then 1 else 0) + LengthAt (sectionIdeal J a) P hP.isPrime := by
  classical
  have := hP.isPrime
  let A := Localization.AtPrime P
  let f : GeoJets5 →+* A := algebraMap GeoJets5 A
  have hf := K1_13_7_6_1.length_factor
    (K1_13_7_6_1.factor_localizes (S := A) P.primeCompl ha)
  change Module.length A (A ⧸ J.map f) = _ +
    Module.length A (A ⧸ (J ⊔ Ideal.span {a}).map f)
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hf]
  congr 1
  by_cases h : Q = P
  · subst Q
    rw [ite_eq_left rfl]
    have he : P.map f = IsLocalRing.maximalIdeal A := Localization.AtPrime.map_eq_maximalIdeal
    rw [he]
    have : IsSimpleModule A (A ⧸ IsLocalRing.maximalIdeal A) :=
      isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal A).1
    exact Module.length_eq_one A _
  · rw [ite_eq_right h]
    have hHQ : H ≤ Q := fun x hx => (ha x).mp (J.mul_mem_right _ (hHJ hx))
    have hnot : ¬ Q ≤ P := fun hle => h (hle.antisymm (hP.2 ⟨hQ, hHQ⟩ hle))
    obtain ⟨s, hs, hsp⟩ := Set.not_subset.mp hnot
    have he : Q.map f = ⊤ :=
      (Q.map f).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem f hs)
        (IsLocalization.map_units A (⟨s, hsp⟩ : P.primeCompl))
    rw [he]
    exact Module.length_eq_zero
def weight (J P : Ideal GeoJets5) : ℕ := by
  classical
  exact if h : P.IsPrime then (LengthAt J P h).toNat else 0
theorem weight_eq {J P : Ideal GeoJets5} (h : P.IsPrime) :
    weight J P = (LengthAt J P h).toNat := by
  rw [weight, dite_eq_left h]
theorem length_top (P : Ideal GeoJets5) (hP : P.IsPrime) :
    LengthAt ⊤ P hP = 0 := by
  have := hP
  let A := Localization.AtPrime P
  change Module.length A (A ⧸ (⊤ : Ideal GeoJets5).map (algebraMap GeoJets5 A)) = 0
  rw [Ideal.map_top]
  exact Module.length_eq_zero
private theorem cycleBudget (hadd : c1) (hpos : c2) {B : Boxes} (hB : Admissible B)
    {H : Ideal GeoJets5} {I : Finset (Fin 5)} (hH : DimLE H I.card)
    {ι : Type} (S : Finset ι) {C : ι → Ideal GeoJets5}
    (hinj : Set.InjOn C (S : Set ι)) (hp : ∀ a ∈ S, H.IsMinimalPrime (C a))
    (J : Ideal GeoJets5) (hHJ : H ≤ J) :
    (∀ a (ha : a ∈ S), LengthAt J (C a) (hp a ha).isPrime ≠ ⊤) ∧
      (∑ a ∈ S, (weight J (C a) : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B J I := by
  classical
  let D (P : Ideal GeoJets5) := mixedDegree B P I
  change _ ∧ (∑ a ∈ S, (weight J (C a) : ℚ) * D (C a)) ≤ D J
  revert hHJ
  induction J using WellFounded.induction (wellFounded_gt (α := Ideal GeoJets5)) with
  | h J ih =>
    intro hHJ
    by_cases hJ : J = ⊤
    · subst J
      have hz (a : ι) (ha : a ∈ S) : LengthAt ⊤ (C a) (hp a ha).isPrime = 0 :=
        length_top _ (hp a ha).isPrime
      constructor
      · intro a ha
        simp [hz a ha]
      · have hs : (∑ a ∈ S, (weight ⊤ (C a) : ℚ) * D (C a)) = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          simp [weight_eq (hp a ha).isPrime, hz a ha]
        rw [hs]
        simp [D, mixedDegree, affineHilbertPolynomial_top]
    obtain ⟨a, Q, haJ, hQ, hann⟩ := K1_13_7_6_1.exists_prime_factor hJ
    let K := sectionIdeal J a
    have hJK : J ≤ K := le_sup_left
    have haK : a ∈ K := Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < K := lt_of_le_of_ne hJK fun he => haJ (he ▸ haK)
    have hHQ : H ≤ Q := fun x hx => (hann x).mp (J.mul_mem_right _ (hHJ hx))
    obtain ⟨hfinK, hboundK⟩ := ih K hlt (hHJ.trans hJK)
    have hstep (i : ι) (hi : i ∈ S) :
        LengthAt J (C i) (hp i hi).isPrime =
          (if Q = C i then 1 else 0) + LengthAt K (C i) (hp i hi).isPrime :=
      local_step hHJ hQ hann (hp i hi)
    have hDQ : 0 ≤ D Q := hpos B hB Q I hQ (dim_mono hHQ hH)
    have hweight (i : ι) (hi : i ∈ S) :
        (weight J (C i) : ℚ) = (weight K (C i) : ℚ) + (if Q = C i then 1 else 0) := by
      rw [weight_eq (hp i hi).isPrime, weight_eq (J := K) (hp i hi).isPrime, hstep i hi]
      split_ifs with hEq
      · rw [ENat.toNat_add (by simp) (hfinK i hi)]
        simp [add_comm]
      · simp
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [hstep i hi]
      have hfinite : (if Q = C i then 1 else 0 : ℕ∞) ≠ ⊤ := by
        split_ifs <;> simp
      exact WithTop.add_ne_top.mpr ⟨hfinite, hfinK i hi⟩
    · have hindicator : (∑ i ∈ S, if Q = C i then D Q else 0) ≤ D Q := by
        by_cases hex : ∃ i ∈ S, Q = C i
        · obtain ⟨i, hi, he⟩ := hex
          rw [Finset.sum_eq_single_of_mem i hi, ite_eq_left he]
          intro j hj hji
          exact ite_eq_right fun hjQ => hji (hinj hj hi (hjQ.symm.trans he))
        · rw [Finset.sum_eq_zero (fun i hi => ite_eq_right (fun h => hex ⟨i, hi, h⟩))]
          exact hDQ
      calc
        _ = (∑ i ∈ S, (weight K (C i) : ℚ) * D (C i)) +
            (∑ i ∈ S, if Q = C i then D Q else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hweight i hi, add_mul]
          split_ifs with he
          · rw [← he, one_mul]
          · rw [zero_mul]
        _ ≤ D K + D Q := add_le_add hboundK hindicator
        _ = D J := (mixed_step hadd hB (dim_mono hHJ hH) hann).symm
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_2_4.c2 := by
  intro B hB J I hJ ι S C w hinj h
  have hp (a : ι) (ha : a ∈ S) : J.IsMinimalPrime (C a) := Exists.choose (h a ha)
  obtain ⟨hfin, hbudget⟩ := cycleBudget h1 h2 hB hJ S hinj hp J le_rfl
  refine le_trans (Finset.sum_le_sum fun a ha => ?_) hbudget
  have hlen : (w a : ℕ∞) ≤ LengthAt J (C a) (hp a ha).isPrime := Exists.choose_spec (h a ha)
  have hw : w a ≤ weight J (C a) := by
    rw [weight_eq (hp a ha).isPrime]
    exact ENat.toNat_le_toNat hlen (hfin a ha)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hw)
    (h2 B hB (C a) I (hp a ha).isPrime (dim_mono (hp a ha).le hJ))
end
end K1_13_6_2_4_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
abbrev SlotVars (B : Boxes) := (i : Fin 5) × latticePoints (B i)
def slotDegree {σ : Type} (slot : σ → Fin 5) (e : σ →₀ ℕ) (i : Fin 5) : ℕ :=
  e.sum fun v n => if slot v = i then n else 0
def sliceCount {σ : Type} (slot : σ → Fin 5) (bad : Finset (σ →₀ ℕ))
    (u : Fin 5 → ℕ) : ℕ :=
  {e : σ →₀ ℕ | slotDegree slot e = u ∧ ∀ b ∈ bad, ¬ b ≤ e}.ncard
def slotMap (B : Boxes) (P : Ideal GeoJets5) :
    MvPolynomial (SlotVars B) GeoField →ₐ[GeoField] MvPolynomial (Fin 5) (GeoJets5 ⧸ P) :=
  MvPolynomial.aeval fun v =>
    monomial (Finsupp.single v.1 1) (Ideal.Quotient.mk P (monomial v.2.val 1))
def slotPiece (B : Boxes) (P : Ideal GeoJets5) (u : Fin 5 → ℕ) :
    Submodule GeoField (GeoJets5 ⧸ P) :=
  (restrictSupport GeoField (diagonalExponents B u)).map
    (Ideal.Quotient.mkₐ GeoField P).toLinearMap
def diagonalIdeal (B : Boxes) (P : Ideal GeoJets5) (t : Fin 5 → ℕ) :
    Ideal (MvPolynomial (diagonalExponents B t) GeoField) :=
  P.comap (monomialMap GeoField (diagonalExponents B t))
end
end K1_13_6_2_4_2_2
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_2
noncomputable section
open K1_13_7_6_1
variable {R : Type*} [CommRing R]
private abbrev At (p : PrimeSpectrum R) := Localization.AtPrime p.asIdeal
abbrev colength (p : PrimeSpectrum R) (J : Ideal R) : ℕ∞ :=
  Module.length (At p) (At p ⧸ J.map (algebraMap R (At p)))
private theorem regular_step {J Q : Ideal R} {a d : R}
    (hfactor : ∀ x, x * a ∈ J ↔ x ∈ Q)
    (hdQ : ∀ x, d * x ∈ Q → x ∈ Q)
    (hdK : ∀ x, d * x ∈ J ⊔ Ideal.span {a} → x ∈ J ⊔ Ideal.span {a})
    (x : R) (hx : d * x ∈ J) : x ∈ J := by
  have hxK := hdK x (Ideal.mem_sup_left hx)
  rw [sup_comm J, Ideal.mem_span_singleton_sup] at hxK
  obtain ⟨t, b, hb, rfl⟩ := hxK
  have hdt : (d * t) * a ∈ J := by
    rw [show (d * t) * a = d * (t * a + b) - d * b by ring]
    exact J.sub_mem hx (J.mul_mem_left d hb)
  exact J.add_mem ((hfactor t).mpr (hdQ t ((hfactor (d * t)).mp hdt))) hb
private theorem cut_annihilator {J Q : Ideal R} {a d : R}
    (hfactor : ∀ x, x * a ∈ J ↔ x ∈ Q)
    (hdK : ∀ x, d * x ∈ J ⊔ Ideal.span {a} → x ∈ J ⊔ Ideal.span {a})
    (x : R) : x * a ∈ J ⊔ Ideal.span {d} ↔ x ∈ Q ⊔ Ideal.span {d} := by
  rw [sup_comm J, sup_comm Q, Ideal.mem_span_singleton_sup, Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨t, b, hb, he⟩
    have ht : d * t ∈ J ⊔ Ideal.span {a} := by
      rw [show d * t = x * a - b by rw [← he]; ring]
      exact sub_mem (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self a)))
        (Ideal.mem_sup_left hb)
    have htK := hdK t ht
    rw [sup_comm J, Ideal.mem_span_singleton_sup] at htK
    obtain ⟨u, c, hc, rfl⟩ := htK
    refine ⟨u, x - u * d, (hfactor _).mp ?_, by ring⟩
    rw [show (x - u * d) * a = x * a - u * d * a by ring, ← he,
      show (u * a + c) * d + b - u * d * a = c * d + b by ring]
    exact J.add_mem (J.mul_mem_right d hc) hb
  · rintro ⟨t, b, hb, rfl⟩
    exact ⟨t * a, b * a, (hfactor b).mpr hb, by ring⟩
private theorem map_adjoin_eq {J Q : Ideal R} {a s : R}
    (hfactor : ∀ x, x * a ∈ J ↔ x ∈ Q)
    (p : PrimeSpectrum R) (hsQ : s ∈ Q) (hsp : s ∉ p.asIdeal) :
    (J ⊔ Ideal.span {a}).map (algebraMap R (At p)) = J.map (algebraMap R (At p)) := by
  let f : R →+* At p := algebraMap R (At p)
  change (J ⊔ Ideal.span {a}).map f = J.map f
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, sup_eq_left,
    Ideal.span_singleton_le_iff_mem]
  have hunit : IsUnit (f s) :=
    IsLocalization.map_units (At p) (⟨s, hsp⟩ : p.asIdeal.primeCompl)
  apply ((J.map f).unit_mul_mem_iff_mem hunit).mp
  exact (factor_localizes p.asIdeal.primeCompl hfactor (f s)).mpr
    (Ideal.mem_map_of_mem f hsQ)
private theorem colength_step (r : PrimeSpectrum R) {J : Ideal R} {a : R}
    (hfactor : ∀ x, x * a ∈ J ↔ x ∈ r.asIdeal) :
    colength r J = 1 + colength r (J ⊔ Ideal.span {a}) := by
  let S := At r
  let f : R →+* S := algebraMap R S
  change Module.length S (S ⧸ J.map f) =
    1 + Module.length S (S ⧸ (J ⊔ Ideal.span {a}).map f)
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    length_factor (factor_localizes r.asIdeal.primeCompl hfactor)]
  congr 1
  have he : r.asIdeal.map f = IsLocalRing.maximalIdeal S :=
    Localization.AtPrime.map_eq_maximalIdeal
  rw [he]
  let : IsSimpleModule S (S ⧸ IsLocalRing.maximalIdeal S) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal S).1
  exact Module.length_eq_one S _
private theorem section_step (r p : PrimeSpectrum R) (hrp : r.asIdeal ≤ p.asIdeal)
    {J : Ideal R} {a D : R} (hfactor : ∀ x, x * a ∈ J ↔ x ∈ r.asIdeal)
    (hD : D ∉ r.asIdeal)
    (hreg : ∀ x : At p, algebraMap R (At p) D * x ∈
      (J ⊔ Ideal.span {a}).map (algebraMap R (At p)) →
        x ∈ (J ⊔ Ideal.span {a}).map (algebraMap R (At p))) :
    (∀ x : At p, algebraMap R (At p) D * x ∈ J.map (algebraMap R (At p)) →
      x ∈ J.map (algebraMap R (At p))) ∧
    (D ∈ p.asIdeal → 1 + colength p ((J ⊔ Ideal.span {a}) ⊔ Ideal.span {D}) ≤
      colength p (J ⊔ Ideal.span {D})) := by
  let S := At p
  let f : R →+* S := algebraMap R S
  let L := J.map f
  let Q := r.asIdeal.map f
  let K := L ⊔ Ideal.span {f a}
  have hmap (I : Ideal R) (z : R) :
      (I ⊔ Ideal.span {z}).map f = I.map f ⊔ Ideal.span {f z} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hann : ∀ x : S, x * f a ∈ L ↔ x ∈ Q :=
    factor_localizes p.asIdeal.primeCompl hfactor
  have hQprime : Q.IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime p.asIdeal hrp
  have hdQ : f D ∉ Q := by
    change D ∉ (r.asIdeal.map f).under R
    rwa [Ideal.under_map_of_isLocalizationAtPrime p.asIdeal hrp]
  have hKreg : ∀ x : S, f D * x ∈ K → x ∈ K := by
    change ∀ x : S, f D * x ∈ (J ⊔ Ideal.span {a}).map f →
      x ∈ (J ⊔ Ideal.span {a}).map f at hreg
    rw [hmap J a] at hreg
    exact hreg
  refine ⟨regular_step hann (fun x hx => (hQprime.mem_or_mem hx).resolve_left hdQ) hKreg, ?_⟩
  intro hDp
  have hcut := length_factor (cut_annihilator hann hKreg)
  have heq : (L ⊔ Ideal.span {f D}) ⊔ Ideal.span {f a} =
      K ⊔ Ideal.span {f D} := sup_right_comm _ _ _
  change 1 + Module.length S (S ⧸ ((J ⊔ Ideal.span {a}) ⊔ Ideal.span {D}).map f) ≤
    Module.length S (S ⧸ (J ⊔ Ideal.span {D}).map f)
  rw [hmap, hmap J a, hmap J D, hcut, heq]
  apply add_le_add_left
  have hle : Q ⊔ Ideal.span {f D} ≤ IsLocalRing.maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
    exact sup_le (Ideal.map_mono hrp)
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem f hDp))
  let : Nontrivial (S ⧸ (Q ⊔ Ideal.span {f D})) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
      (IsLocalRing.maximalIdeal.isMaximal S).ne_top hle)
  exact Order.one_le_iff_pos.mpr Module.length_pos
set_option maxHeartbeats 800000 in
theorem exists_weight_guard [IsNoetherianRing R] (B : Ideal R) (r : PrimeSpectrum R)
    (hr : r.asIdeal ∈ B.minimalPrimes) :
    ∃ g : R, g ∉ r.asIdeal ∧ ∀ (p : PrimeSpectrum R), r.asIdeal ≤ p.asIdeal →
      g ∉ p.asIdeal → ∀ D : R, D ∉ r.asIdeal → D ∈ p.asIdeal →
      colength r B ≤ colength p (B ⊔ Ideal.span {D}) := by
  suffices ∀ J : Ideal R, B ≤ J →
    ∃ g : R, g ∉ r.asIdeal ∧ ∀ (p : PrimeSpectrum R), r.asIdeal ≤ p.asIdeal →
      g ∉ p.asIdeal → ∀ D : R, D ∉ r.asIdeal →
      (∀ x : At p, algebraMap R (At p) D * x ∈ J.map (algebraMap R (At p)) →
        x ∈ J.map (algebraMap R (At p))) ∧
      (D ∈ p.asIdeal → colength r J ≤ colength p (J ⊔ Ideal.span {D})) by
    obtain ⟨g, hgr, hg⟩ := this B le_rfl
    exact ⟨g, hgr, fun p hrp hgp D hD hDp => (hg p hrp hgp D hD).2 hDp⟩
  intro J
  induction J using WellFounded.induction (wellFounded_gt (α := Ideal R)) with
  | h J ih =>
    intro hBJ
    by_cases hJ : J = ⊤
    · subst J
      refine ⟨1, r.asIdeal.ne_top_iff_one.mp r.isPrime.ne_top, ?_⟩
      intro p _ _ D _
      refine ⟨?_, ?_⟩
      · intro x _
        rw [Ideal.map_top]
        exact Submodule.mem_top
      · intro _
        unfold colength
        rw [Ideal.map_top]
        exact Module.length_eq_zero.trans_le zero_le
    obtain ⟨a, Q, ha, hQ, hann⟩ := exists_prime_factor hJ
    let K := J ⊔ Ideal.span {a}
    have hJK : J ≤ K := le_sup_left
    have haK : a ∈ K := Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < K := lt_of_le_of_ne hJK fun he => ha (he ▸ haK)
    obtain ⟨g, hgr, hg⟩ := ih K hlt (hBJ.trans hJK)
    by_cases hQr : Q = r.asIdeal
    · subst Q
      refine ⟨g, hgr, fun p hrp hgp D hD => ?_⟩
      obtain ⟨hreg, hlength⟩ := hg p hrp hgp D hD
      obtain ⟨hregular, hcut⟩ := section_step r p hrp hann hD hreg
      refine ⟨hregular, fun hDp => ?_⟩
      rw [colength_step r hann]
      exact (add_le_add_right (hlength hDp) 1).trans (hcut hDp)
    · have hBQ : B ≤ Q := fun x hx => (hann x).mp (J.mul_mem_right _ (hBJ hx))
      have hnle : ¬ Q ≤ r.asIdeal :=
        fun hle => hQr (hle.antisymm (hr.2 ⟨hQ, hBQ⟩ hle))
      obtain ⟨s, hsQ, hsr⟩ := Set.not_subset.mp hnle
      refine ⟨g * s, fun h => (r.isPrime.mem_or_mem h).elim hgr hsr, ?_⟩
      intro p hrp hgp D hD
      have hg' : g ∉ p.asIdeal := fun h => hgp (p.asIdeal.mul_mem_right s h)
      have hs' : s ∉ p.asIdeal := fun h => hgp (p.asIdeal.mul_mem_left g h)
      have hlocal : K.map (algebraMap R (At p)) = J.map (algebraMap R (At p)) :=
        map_adjoin_eq hann p hsQ hs'
      have hgen : K.map (algebraMap R (At r)) = J.map (algebraMap R (At r)) :=
        map_adjoin_eq hann r hsQ hsr
      obtain ⟨hreg, hlength⟩ := hg p hrp hg' D hD
      rw [hlocal] at hreg
      refine ⟨hreg, fun hDp => ?_⟩
      have hsgen : colength r K = colength r J := by
        unfold colength
        rw [hgen]
      have hscut : colength p (K ⊔ Ideal.span {D}) = colength p (J ⊔ Ideal.span {D}) := by
        unfold colength
        let f : R →+* At p := algebraMap R (At p)
        have hmap (I : Ideal R) :
            (I ⊔ Ideal.span {D}).map f = I.map f ⊔ (Ideal.span {D}).map f := by
          rw [Ideal.map_sup]
        change Module.length (At p) (At p ⧸ (K ⊔ Ideal.span {D}).map f) =
          Module.length (At p) (At p ⧸ (J ⊔ Ideal.span {D}).map f)
        rw [hmap K, hmap J, hlocal]
      simpa only [hsgen, hscut] using hlength hDp
end
end K1_13_7_5_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_3_1
noncomputable section
open Filter MvPolynomial Polynomial
variable {k σ : Type*} [Field k] [Finite σ]
private theorem hilbertFunction_step_upper
    {I Q : Ideal (MvPolynomial σ k)} {g : MvPolynomial σ k}
    (ha : ∀ x, x * g ∈ I ↔ x ∈ Q)
    (C : ℕ) (hC : ∀ f ∈ I ⊔ Ideal.span {g}, ∃ q : MvPolynomial σ k,
      f - q * g ∈ I ∧ q.totalDegree ≤ f.totalDegree + C) (N : ℕ) :
    affineHilbertFunction I N ≤ affineHilbertFunction (I ⊔ Ideal.span {g}) N +
      affineHilbertFunction Q (N + C) := by
  let J := I ⊔ Ideal.span {g}
  have hIJ : I ≤ J := le_sup_left
  let π := ((Ideal.Quotient.factorₐ k hIJ).toLinearMap.domRestrict
    (quotientDegreeLE I N)).codRestrict (quotientDegreeLE J N) fun x => by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
      change Ideal.Quotient.factor hIJ x.val ∈ quotientDegreeLE J N
      rw [← hpx, Ideal.Quotient.factor_mk]
      exact mk_mem_quotientDegreeLE hp
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hpy⟩
  let μ := K1_13_7_6_1.factorMul (k := k) ha
  have hμ : Function.Injective μ := K1_13_7_6_1.factorMul_injective ha
  have hrep (x : LinearMap.ker π) :
      ∃ q : MvPolynomial σ k, q.totalDegree ≤ N + C ∧
        μ (Ideal.Quotient.mk Q q) = x.val.val := by
    obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.val.property
    have hpJ : p ∈ J := by
      have hzero := congrArg Subtype.val (LinearMap.mem_ker.mp x.property)
      change Ideal.Quotient.factor hIJ x.val.val = 0 at hzero
      rw [← hpx, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hzero
      exact hzero
    obtain ⟨q, hq, hqd⟩ := hC p hpJ
    refine ⟨q, hqd.trans (Nat.add_le_add_right hp C), ?_⟩
    rw [← hpx]
    change K1_13_7_6_1.factorMul ha (Ideal.Quotient.mk Q q) = _
    rw [K1_13_7_6_1.factorMul_mk, mul_comm g q, Ideal.Quotient.eq]
    simpa only [neg_sub] using I.neg_mem hq
  let inc := (quotientDegreeLE I N).subtype.comp (LinearMap.ker π).subtype
  let intoRange := inc.codRestrict (LinearMap.range μ) fun x => by
    obtain ⟨q, _, hq⟩ := hrep x
    exact ⟨Ideal.Quotient.mk Q q, hq⟩
  let e := LinearEquiv.ofInjective μ hμ
  let back := e.symm.toLinearMap.comp intoRange
  let bounded := back.codRestrict (quotientDegreeLE Q (N + C)) fun x => by
    obtain ⟨q, hq, hqx⟩ := hrep x
    have he : e (Ideal.Quotient.mk Q q) = intoRange x := Subtype.ext hqx
    change e.symm (intoRange x) ∈ _
    rw [← he, LinearEquiv.symm_apply_apply]
    exact mk_mem_quotientDegreeLE hq
  have hback (x : LinearMap.ker π) : μ (bounded x).val = x.val.val :=
    congrArg Subtype.val (e.apply_symm_apply (intoRange x))
  have hinj : Function.Injective bounded := by
    intro x y hxy
    apply Subtype.ext (Subtype.ext _)
    rw [← hback x, ← hback y, hxy]
  have hker := LinearMap.finrank_le_finrank_of_injective hinj
  have hrank := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrank
  change affineHilbertFunction I N ≤ affineHilbertFunction J N + affineHilbertFunction Q (N + C)
  unfold affineHilbertFunction
  omega
theorem hilbertCoeff_step {I Q : Ideal (MvPolynomial σ k)} {g : MvPolynomial σ k}
    (ha : ∀ x, x * g ∈ I ↔ x ∈ Q) {d : ℕ}
    (hd : (affineHilbertPolynomial I).natDegree ≤ d) :
    (affineHilbertPolynomial I).coeff d =
      (affineHilbertPolynomial (I ⊔ Ideal.span {g})).coeff d +
        (affineHilbertPolynomial Q).coeff d := by
  let J := I ⊔ Ideal.span {g}
  have hIJ : I ≤ J := le_sup_left
  have hIQ : I ≤ Q := fun x hx => (ha x).mp (I.mul_mem_right _ hx)
  have hJd := (natDegree_affineHilbertPolynomial_le_of_le hIJ).trans hd
  have hQd := (natDegree_affineHilbertPolynomial_le_of_le hIQ).trans hd
  refine le_antisymm ?_ (K1_13_7_6_1.hilbertCoeff_step hIJ
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)) ha hd)
  obtain ⟨C, hC⟩ := exists_degree_shift I g
  let P := affineHilbertPolynomial J + taylor (C : ℚ) (affineHilbertPolynomial Q)
  have hPd : P.natDegree ≤ d :=
    natDegree_add_le_of_degree_le hJd (by rwa [natDegree_taylor])
  have hcoeff : P.coeff d =
      (affineHilbertPolynomial J).coeff d + (affineHilbertPolynomial Q).coeff d := by
    simp only [P, coeff_add, coeff_taylor_of_natDegree_le _ hQd]
  rw [← hcoeff]
  refine coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hd hPd ?_
  obtain ⟨T, hT⟩ := exists_eval_affineHilbertPolynomial Q
  filter_upwards [eventually_eval_affineHilbertPolynomial I,
    eventually_eval_affineHilbertPolynomial J, eventually_ge_atTop T] with N hI hJ hN
  simp only [P, Polynomial.eval_add, taylor_eval]
  rw [hI, hJ, ← Nat.cast_add, hT _ (hN.trans (Nat.le_add_right _ _))]
  exact_mod_cast hilbertFunction_step_upper ha C hC N
end
end K1_13_6_2_3_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped BigOperators Pointwise
private theorem sum_blocks {t : Fin 5 → ℕ} {n : ℕ}
    (u : (i : Fin 5) → Fin (n * t i) → Exponent) :
    (∑ i, ∑ j, u i j) =
      ∑ k : Fin n, ∑ i, ∑ j : Fin (t i), u i (finProdFinEquiv (k, j)) := by
  calc
    (∑ i, ∑ j, u i j) =
        ∑ i, ∑ k : Fin n, ∑ j : Fin (t i), u i (finProdFinEquiv (k, j)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Fintype.sum_prod_type']
      exact (Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl).symm
    _ = _ := Finset.sum_comm
private theorem diagonal_nsmul (B : Boxes) (t : Fin 5 → ℕ) (n : ℕ) :
    n • diagonalExponents B t = diagonalExponents B (fun i => n * t i) := by
  ext x
  rw [Set.mem_nsmul_iff_sum]
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose u hu he using hg
    let v (i : Fin 5) (j : Fin (n * t i)) : Exponent :=
      u (finProdFinEquiv.symm j).1 i (finProdFinEquiv.symm j).2
    refine ⟨v, fun i j => hu _ _ _, ?_⟩
    rw [sum_blocks v]
    simp only [v, Equiv.symm_apply_apply]
    exact Finset.sum_congr rfl fun k _ => he k
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun k => ∑ i, ∑ j : Fin (t i), u i (finProdFinEquiv (k, j)),
      fun k => ⟨fun i j => u i (finProdFinEquiv (k, j)), fun i j => hu _ _, rfl⟩,
      (sum_blocks u).symm⟩
private theorem zero_mem_diagonal (B : Boxes) (t : Fin 5 → ℕ) :
    0 ∈ diagonalExponents B t :=
  ⟨fun _ _ => 0, fun _ _ => by simp [latticePoints, Allowed], by simp⟩
private theorem monomial_preimage {S : Set Exponent} {n : ℕ} {e : Exponent}
    (he : e ∈ n • S) :
    ∃ q : MvPolynomial S GeoField,
      q.totalDegree ≤ n ∧ monomialMap GeoField S q = monomial e 1 := by
  induction n generalizing e with
  | zero =>
    rw [zero_smul, Set.mem_zero] at he
    subst e
    exact ⟨1, by simp, by simp⟩
  | succ n ih =>
    rw [succ_nsmul'] at he
    obtain ⟨a, ha, b, hb, rfl⟩ := he
    obtain ⟨q, hq, heq⟩ := ih hb
    refine ⟨MvPolynomial.X ⟨a, ha⟩ * q, ?_, ?_⟩
    · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_X]; omega)
    · rw [map_mul, monomialMap_X, heq, monomial_mul_monomial, one_mul]
theorem diagonal_hilbert (B : Boxes) (P : Ideal GeoJets5) (t : Fin 5 → ℕ) (n : ℕ) :
    affineHilbertFunction (diagonalIdeal B P t) n =
      Module.finrank GeoField (slotPiece B P (fun i => n * t i)) := by
  let S := diagonalExponents B t
  let f := monomialMap GeoField S
  let g : (MvPolynomial S GeoField ⧸ diagonalIdeal B P t) →ₐ[GeoField] (GeoJets5 ⧸ P) :=
    Ideal.quotientMapₐ P f le_rfl
  let V := quotientDegreeLE (diagonalIdeal B P t) n
  change Module.finrank GeoField V = _
  have hmap : V.map g.toLinearMap = slotPiece B P (fun i => n * t i) := by
    rw [slotPiece, ← diagonal_nsmul]
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨q, hq, rfl⟩ := mem_quotientDegreeLE.mp hv
      exact ⟨f q, monomialMap_mem_restrictSupport_nsmul (zero_mem_diagonal B t) hq, rfl⟩
    · rw [restrictSupport_eq_span, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
      obtain ⟨q, hq, heq⟩ := monomial_preimage he
      exact ⟨Ideal.Quotient.mk (diagonalIdeal B P t) q, mk_mem_quotientDegreeLE hq,
        congrArg (Ideal.Quotient.mk P) heq⟩
  rw [← hmap]
  have hg : Function.Injective g := Ideal.quotientMap_injective (I := P) (f := f.toRingHom)
  exact (Submodule.equivMapOfInjective g.toLinearMap hg V).finrank_eq
end
end K1_13_6_2_4_2_2
end
section
set_option autoImplicit false
namespace K1_14_3_4_4
noncomputable section
open K1_13_7_6_1
open scoped BigOperators
section Cyclic
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
private theorem factor_flat [Module.Flat R S] {J D : Ideal R} {a : R}
    (ha : ∀ x : R, x * a ∈ J ↔ x ∈ D) (x : S) :
    x * algebraMap R S a ∈ J.map (algebraMap R S) ↔
      x ∈ D.map (algebraMap R S) := by
  let f := factorMul (k := R) ha
  have hf : Function.Injective (f.lTensor S) :=
    Module.Flat.lTensor_preserves_injective_linearMap f (factorMul_injective ha)
  let eJ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S J
  let eD := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S D
  have he : f.lTensor S (eD (Ideal.Quotient.mk (D.map (algebraMap R S)) x)) =
      eJ (Ideal.Quotient.mk (J.map (algebraMap R S)) (x * algebraMap R S a)) := by
    simp only [eD, eJ, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
      LinearMap.lTensor_tmul, f]
    have hS : x * algebraMap R S a = a • x := by rw [Algebra.smul_def, mul_comm]
    rw [hS, TensorProduct.smul_tmul]
    congr 1
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hx
    apply eD.injective
    apply hf
    simp only [he, hx, map_zero]
  · intro hx
    apply eJ.injective
    simp only [← he, hx, map_zero]
end Cyclic
variable {R : Type*} [CommRing R]
def localColength (q : PrimeSpectrum R) (J : Ideal R) : ℕ∞ :=
  let A := Localization.AtPrime q.asIdeal
  Module.length A (A ⧸ J.map (algebraMap R A))
theorem localColength_eq_zero_of_not_le {q : PrimeSpectrum R} {J : Ideal R}
    (h : ¬ J ≤ q.asIdeal) : localColength q J = 0 := by
  let A := Localization.AtPrime q.asIdeal
  obtain ⟨s, hs, hsq⟩ := Set.not_subset.mp h
  have htop : J.map (algebraMap R A) = ⊤ :=
    (J.map (algebraMap R A)).eq_top_of_isUnit_mem
      (Ideal.mem_map_of_mem (algebraMap R A) hs)
      (IsLocalization.map_units A (⟨s, hsq⟩ : q.asIdeal.primeCompl))
  change Module.length A (A ⧸ J.map (algebraMap R A)) = 0
  rw [htop]
  exact Module.length_eq_zero
private theorem localColength_step {B J D : Ideal R} (hBJ : B ≤ J)
    {a : R} (hD : D.IsPrime) (ha : ∀ x : R, x * a ∈ J ↔ x ∈ D)
    {q : PrimeSpectrum R} (hq : q.asIdeal ∈ B.minimalPrimes) :
    localColength q J = (if D = q.asIdeal then 1 else 0) +
      localColength q (J ⊔ Ideal.span {a}) := by
  classical
  let A := Localization.AtPrime q.asIdeal
  let f : R →+* A := algebraMap R A
  have hmul := length_factor (factor_localizes (S := A) q.asIdeal.primeCompl ha)
  change Module.length A (A ⧸ J.map f) = _ +
    Module.length A (A ⧸ (J ⊔ Ideal.span {a}).map f)
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hmul]
  congr 1
  by_cases h : D = q.asIdeal
  · subst D
    rw [ite_eq_left rfl, show q.asIdeal.map f = IsLocalRing.maximalIdeal A from
      Localization.AtPrime.map_eq_maximalIdeal]
    have : IsSimpleModule A (A ⧸ IsLocalRing.maximalIdeal A) :=
      isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal A).1
    exact Module.length_eq_one A _
  · rw [ite_eq_right h]
    have hBD : B ≤ D := fun x hx => (ha x).mp (J.mul_mem_right _ (hBJ hx))
    have hn : ¬ D ≤ q.asIdeal := fun hle => h (hle.antisymm (hq.2 ⟨hD, hBD⟩ hle))
    exact localColength_eq_zero_of_not_le hn
section Weighted
variable {S k : Type*} [CommRing S] [Field k] [Algebra R S] [Algebra k S]
  [Module.Flat R S]
private def lengthAfter (I : Ideal R) : ℕ∞ :=
  Module.length k (S ⧸ I.map (algebraMap R S))
private theorem lengthAfter_step {J D : Ideal R} {a : R}
    (ha : ∀ x : R, x * a ∈ J ↔ x ∈ D) :
    lengthAfter (S := S) (k := k) J =
      lengthAfter (S := S) (k := k) D + lengthAfter (S := S) (k := k) (J ⊔ Ideal.span {a}) := by
  let f : R →+* S := algebraMap R S
  let b := f a
  let H := J.map f
  let E := D.map f
  have hb : ∀ x : S, x * b ∈ H ↔ x ∈ E := factor_flat ha
  have h := Module.length_eq_add_of_exact
    (factorMul (k := k) hb)
    (Ideal.Quotient.factorₐ k (le_sup_left : H ≤ H ⊔ Ideal.span {b})).toLinearMap
    (factorMul_injective hb) (Ideal.Quotient.factor_surjective le_sup_left) (factorMul_exact hb)
  unfold lengthAfter
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact h
private theorem sum_indicator_le (D : Ideal R) (qs : Finset (PrimeSpectrum R)) (d : ℕ∞) :
    (∑ q ∈ qs, if D = q.asIdeal then d else 0) ≤ d := by
  classical
  by_cases he : ∃ q ∈ qs, D = (q : PrimeSpectrum R).asIdeal
  · obtain ⟨q, hq, heq⟩ := he
    rw [Finset.sum_eq_single_of_mem q hq, ite_eq_left heq]
    intro r _ hr
    exact ite_eq_right (fun her => hr (PrimeSpectrum.ext (her.symm.trans heq)))
  · rw [Finset.sum_eq_zero fun q hq => ite_eq_right (fun h => he ⟨q, hq, h⟩)]
    exact zero_le
theorem weighted_lengths [IsNoetherianRing R] (B : Ideal R)
    (qs : Finset (PrimeSpectrum R)) (hmin : ∀ q ∈ qs, q.asIdeal ∈ B.minimalPrimes)
    (J : Ideal R) (hBJ : B ≤ J) :
    ∑ q ∈ qs, localColength q J * Module.length k (S ⧸ q.asIdeal.map (algebraMap R S)) ≤
      Module.length k (S ⧸ J.map (algebraMap R S)) := by
  classical
  change ∑ q ∈ qs, localColength q J * lengthAfter (S := S) (k := k) q.asIdeal ≤
    lengthAfter (S := S) (k := k) J
  revert hBJ
  induction J using WellFounded.induction (wellFounded_gt (α := Ideal R)) with
  | h J ih =>
    intro hBJ
    by_cases hJ : J = ⊤
    · subst J
      have hz (q : PrimeSpectrum R) : localColength q ⊤ = 0 :=
        localColength_eq_zero_of_not_le fun h => q.isPrime.ne_top (top_le_iff.mp h)
      simp [hz]
    obtain ⟨a, D, haJ, hD, hann⟩ := exists_prime_factor hJ
    let T := J ⊔ Ideal.span {a}
    have hJT : J ≤ T := le_sup_left
    have haT : a ∈ T := Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < T := lt_of_le_of_ne hJT fun he => haJ (he ▸ haT)
    let d := lengthAfter (S := S) (k := k) D
    have hterm (q : PrimeSpectrum R) (hq : q ∈ qs) :
        localColength q J * lengthAfter (S := S) (k := k) q.asIdeal =
          localColength q T * lengthAfter (S := S) (k := k) q.asIdeal +
            (if D = q.asIdeal then d else 0) := by
      rw [localColength_step hBJ hD hann (hmin q hq), add_mul, add_comm]
      by_cases he : D = q.asIdeal
      · simp [he, d, T]
      · simp [he, T]
    calc
      _ = (∑ q ∈ qs, localColength q T * lengthAfter (S := S) (k := k) q.asIdeal) +
          (∑ q ∈ qs, if D = q.asIdeal then d else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl hterm
      _ ≤ lengthAfter (S := S) (k := k) T + d :=
        add_le_add (ih T hlt (hBJ.trans hJT)) (sum_indicator_le D qs d)
      _ = lengthAfter (S := S) (k := k) J := by
        rw [lengthAfter_step hann, add_comm]
end Weighted
end
end K1_14_3_4_4
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_2_1
noncomputable section
open Filter MvPolynomial Polynomial
variable {σ k : Type*} [Field k] [Finite σ]
private theorem bounded_multiplier (J : Ideal (MvPolynomial σ k)) (a : MvPolynomial σ k) :
    ∃ C : ℕ, ∀ p ∈ J ⊔ Ideal.span {a}, ∃ b : MvPolynomial σ k,
      b.totalDegree ≤ p.totalDegree + C ∧ Ideal.Quotient.mk J p = Ideal.Quotient.mk J (a * b) := by
  classical
  let K := J ⊔ Ideal.span {a}
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  obtain ⟨B, hB⟩ := m.exists_finset_standardExponents_iff K
  have hchoose (e : ↥B) : ∃ f ∈ K, f ≠ 0 ∧ m.degree f ≤ e.val := by
    have he : e.val ∉ m.standardExponents K := fun h => (hB _).mp h _ e.property le_rfl
    simp only [MonomialOrder.standardExponents, Set.mem_ofPred_eq, not_forall, not_imp,
      not_not] at he
    obtain ⟨p, hp, hp0, hle⟩ := he
    exact ⟨p, hp, hp0, hle⟩
  choose f hf hf0 hfe using hchoose
  have hlift (e : ↥B) : ∃ u : MvPolynomial σ k,
      Ideal.Quotient.mk J (f e) = Ideal.Quotient.mk J (a * u) := by
    have he := hf e
    change f e ∈ J ⊔ Ideal.span {a} at he
    rw [sup_comm] at he
    obtain ⟨u, v, hv, heq⟩ := Ideal.mem_span_singleton_sup.mp he
    exact ⟨u, by rw [← heq, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hv, add_zero, mul_comm]⟩
  choose u hu using hlift
  obtain ⟨C, hC⟩ := Finite.exists_le (fun e => (u e).totalDegree)
  refine ⟨C, fun p hp => ?_⟩
  obtain ⟨g, r, hpr, hd, hr⟩ := m.div (b := f) (fun e => m.isUnit_leadingCoeff.mpr (hf0 e)) p
  have heq : p = (∑ e ∈ g.support, g e * f e) + r := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul] using hpr
  have hsum : (∑ e ∈ g.support, g e * f e) ∈ K :=
    K.sum_mem (fun e _ => K.mul_mem_left _ (hf e))
  have hrK : r ∈ K := by
    rw [← add_sub_cancel_left (∑ e ∈ g.support, g e * f e) r, ← heq]
    exact K.sub_mem hp hsum
  have hrstd : r ∈ m.standardSpace K := by
    intro c hc
    exact (hB c).mpr (fun e he hle => hr c hc ⟨e, he⟩ ((hfe ⟨e, he⟩).trans hle))
  rw [m.eq_zero_of_mem_standardSpace_of_mem hrstd hrK, add_zero] at heq
  refine ⟨∑ e ∈ g.support, g e * u e, ?_, ?_⟩
  · rw [← mem_restrictTotalDegree]
    apply Submodule.sum_mem
    intro e he
    rw [mem_restrictTotalDegree]
    have hgd : (g e).totalDegree ≤ p.totalDegree := by
      have hprod := degLex_totalDegree_monotone (hd e)
      rw [totalDegree_mul_of_isDomain (hf0 e) (Finsupp.mem_support_iff.mp he)] at hprod
      omega
    exact (totalDegree_mul _ _).trans (Nat.add_le_add hgd (hC e))
  · rw [heq, Finset.mul_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun e _ => by simp only [map_mul, hu, mul_left_comm])
private theorem hilbertFunction_upper {J Q : Ideal (MvPolynomial σ k)} {a : MvPolynomial σ k}
    (ha : ∀ x, x * a ∈ J ↔ x ∈ Q) :
    ∃ C : ℕ, ∀ N : ℕ, affineHilbertFunction J N ≤
      affineHilbertFunction (J ⊔ Ideal.span {a}) N + affineHilbertFunction Q (N + C) := by
  let K := J ⊔ Ideal.span {a}
  have hJK : J ≤ K := le_sup_left
  obtain ⟨C, hC⟩ := bounded_multiplier J a
  refine ⟨C, fun N => ?_⟩
  let π := ((Ideal.Quotient.factorₐ k hJK).toLinearMap.domRestrict (quotientDegreeLE J N)).codRestrict
    (quotientDegreeLE K N) fun x => by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
      change Ideal.Quotient.factor hJK x ∈ quotientDegreeLE K N
      rw [← hpx, Ideal.Quotient.factor_mk]
      exact mk_mem_quotientDegreeLE hp
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk J p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hpy⟩
  let μ := (K1_13_7_6_1.factorMul (k := k) ha).domRestrict (quotientDegreeLE Q (N + C))
  let ι := (quotientDegreeLE J N).subtype.comp (LinearMap.ker π).subtype
  have him (z : LinearMap.ker π) : ι z ∈ LinearMap.range μ := by
    obtain ⟨p, hp, hpz⟩ := mem_quotientDegreeLE.mp z.val.property
    have hz : π z.val = 0 := LinearMap.mem_ker.mp z.property
    have hpK : p ∈ K := Ideal.Quotient.eq_zero_iff_mem.mp (by
      have hz' := congrArg (fun w : quotientDegreeLE K N => (w : MvPolynomial σ k ⧸ K)) hz
      change Ideal.Quotient.factor hJK (z.val : MvPolynomial σ k ⧸ J) = 0 at hz'
      rwa [← hpz, Ideal.Quotient.factor_mk] at hz')
    obtain ⟨b, hb, he⟩ := hC p hpK
    refine ⟨⟨Ideal.Quotient.mk Q b, mk_mem_quotientDegreeLE (hb.trans (Nat.add_le_add_right hp C))⟩, ?_⟩
    change K1_13_7_6_1.factorMul ha (Ideal.Quotient.mk Q b) = (z.val : MvPolynomial σ k ⧸ J)
    rw [K1_13_7_6_1.factorMul_mk, ← he, hpz]
  have hinj : Function.Injective (ι.codRestrict (LinearMap.range μ) him) := by
    intro x y hxy
    have hxy' : (x.val : MvPolynomial σ k ⧸ J) = (y.val : MvPolynomial σ k ⧸ J) :=
      congrArg (fun w : LinearMap.range μ => (w : MvPolynomial σ k ⧸ J)) hxy
    exact Subtype.ext (Subtype.ext hxy')
  have hdim := (LinearMap.finrank_le_finrank_of_injective hinj).trans μ.finrank_range_le
  have hrank := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrank
  exact hrank.ge.trans (Nat.add_le_add_left hdim _)
theorem proof : K1_13_6_2_4_2.c1 := by
  intro σ _ J Q a ha d hd
  let K := J ⊔ Ideal.span {a}
  have hJQ : J ≤ Q := fun x hx => (ha x).mp (J.mul_mem_right _ hx)
  have hKd := (natDegree_affineHilbertPolynomial_le_of_le (show J ≤ K from le_sup_left)).trans hd
  have hQd := (natDegree_affineHilbertPolynomial_le_of_le hJQ).trans hd
  obtain ⟨C, hC⟩ := hilbertFunction_upper ha
  let P : (Polynomial ℚ) := affineHilbertPolynomial K + taylor (C : ℚ) (affineHilbertPolynomial Q)
  have hPd : P.natDegree ≤ d :=
    (natDegree_add_le_of_le hKd ((natDegree_taylor _ _).trans_le hQd)).trans (max_self d).le
  have hcoeff : P.coeff d =
      (affineHilbertPolynomial K).coeff d + (affineHilbertPolynomial Q).coeff d := by
    simp only [P, coeff_add, coeff_taylor_of_natDegree_le _ hQd]
  change (affineHilbertPolynomial J).coeff d ≤
    (affineHilbertPolynomial K).coeff d + (affineHilbertPolynomial Q).coeff d
  rw [← hcoeff]
  refine coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hd hPd ?_
  have hshift : Tendsto (fun n : ℕ => n + C) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n C) tendsto_id
  filter_upwards [eventually_eval_affineHilbertPolynomial J, eventually_eval_affineHilbertPolynomial K,
    hshift.eventually (eventually_eval_affineHilbertPolynomial Q)] with N hJ hK hQ
  simp only [P, Polynomial.eval_add, taylor_eval]
  rw [← Nat.cast_add, hJ, hK, hQ]
  exact_mod_cast hC N
end
end K1_13_6_2_4_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ (B : Boxes) (P : Ideal GeoJets5),
    ∃ o : MonomialOrder.{0, 0} (SlotVars B), ∀ u : Fin 5 → ℕ,
      Module.finrank GeoField (slotPiece B P u) =
        {e : SlotVars B →₀ ℕ | slotDegree (fun v => v.1) e = u ∧
          e ∈ o.standardExponents (RingHom.ker (slotMap B P).toRingHom)}.ncard
def c2 : Prop :=
  ∀ {σ : Type} [Finite σ] (slot : σ → Fin 5) (bad : Finset (σ →₀ ℕ)),
    ∃ (m : ℕ) (p : Fin m → Fin 5 → Polynomial ℚ),
      (∀ a i, 0 < (p a i).leadingCoeff) ∧
      ∃ N : ℕ, ∀ (u : Fin 5 → ℕ), (∀ i, N ≤ u i) →
        (sliceCount slot bad u : ℚ) = ∑ a, ∏ i, (p a i).eval (u i : ℚ)
private def rayFactor (p : Polynomial ℚ) (t : ℕ) : Polynomial ℚ :=
  p.comp (Polynomial.C (t : ℚ) * Polynomial.X)
private def rayTerm (p : Fin 5 → Polynomial ℚ) (t : Fin 5 → ℕ) : Polynomial ℚ :=
  ∏ i, rayFactor (p i) (t i)
private theorem rayFactor_natDegree (p : Polynomial ℚ) {t : ℕ} (ht : 0 < t) :
    (rayFactor p t).natDegree = p.natDegree := by
  rw [rayFactor, Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul_X _ (Nat.cast_ne_zero.mpr ht.ne'), mul_one]
private theorem rayFactor_leadingCoeff (p : Polynomial ℚ) {t : ℕ} (ht : 0 < t) :
    (rayFactor p t).leadingCoeff = p.leadingCoeff * (t : ℚ) ^ p.natDegree := by
  rw [rayFactor, Polynomial.leadingCoeff_comp, Polynomial.leadingCoeff_C_mul_X]
  rw [Polynomial.natDegree_C_mul_X _ (Nat.cast_ne_zero.mpr ht.ne')]
  exact one_ne_zero
private theorem rayTerm_natDegree (p : Fin 5 → Polynomial ℚ)
    (hp : ∀ i, 0 < (p i).leadingCoeff) {t : Fin 5 → ℕ} (ht : ∀ i, 0 < t i) :
    (rayTerm p t).natDegree = ∑ i, (p i).natDegree := by
  rw [rayTerm, Polynomial.natDegree_prod]
  · exact Finset.sum_congr rfl fun i _ => rayFactor_natDegree _ (ht i)
  · intro i _
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [rayFactor_leadingCoeff _ (ht i)]
    exact (mul_pos (hp i) (pow_pos (Nat.cast_pos.mpr (ht i)) _)).ne'
private theorem rayTerm_leadingCoeff (p : Fin 5 → Polynomial ℚ)
    {t : Fin 5 → ℕ} (ht : ∀ i, 0 < t i) :
    (rayTerm p t).leadingCoeff =
      (∏ i, (p i).leadingCoeff) * ∏ i, (t i : ℚ) ^ (p i).natDegree := by
  rw [rayTerm, Polynomial.leadingCoeff_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => rayFactor_leadingCoeff _ (ht i)
private theorem summand_degree_le {m d : ℕ} (q : Fin m → Polynomial ℚ)
    (hq : ∀ a, 0 < (q a).leadingCoeff) (hd : (∑ a, q a).natDegree ≤ d) (a : Fin m) :
    (q a).natDegree ≤ d := by
  by_contra! h
  let M := (Finset.univ : Finset (Fin m)).sup (fun a => (q a).natDegree)
  have hle (b : Fin m) : (q b).natDegree ≤ M := Finset.le_sup (f := fun a => (q a).natDegree) (Finset.mem_univ b)
  have hdM := h.trans_le (hle a)
  obtain ⟨b, hb, he⟩ := Finset.exists_mem_eq_sup _ ⟨a, Finset.mem_univ a⟩
    (fun a => (q a).natDegree)
  have hn (b : Fin m) : 0 ≤ (q b).coeff M := by
    rcases (hle b).lt_or_eq with hlt | heq
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    · rw [← heq, Polynomial.coeff_natDegree]
      exact (hq b).le
  have hs : 0 < ∑ b, (q b).coeff M := Finset.sum_pos' (fun b _ => hn b)
    ⟨b, hb, by rw [show M = (q b).natDegree from he, Polynomial.coeff_natDegree]; exact hq b⟩
  rw [← Polynomial.finsetSum_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hdM)]
    at hs
  exact (lt_irrefl 0) hs
private def direction (J : Finset (Fin 5)) (i : Fin 5) : ℕ := if i ∈ J then 2 else 1
private theorem direction_pos (J : Finset (Fin 5)) (i : Fin 5) : 0 < direction J i := by
  by_cases h : i ∈ J <;> simp [direction, h]
private theorem direction_prod (J : Finset (Fin 5)) (r : Fin 5 → ℕ) :
    (∏ i, (direction J i : ℚ) ^ r i) = ∏ i ∈ J, (2 : ℚ) ^ r i := by
  calc
    (∏ i, (direction J i : ℚ) ^ r i) = ∏ i ∈ J, (direction J i : ℚ) ^ r i :=
      (Finset.prod_subset (Finset.subset_univ J) fun i _ hi => by simp [direction, hi]).symm
    _ = _ := Finset.prod_congr rfl fun i hi => by simp [direction, hi]
private theorem signed_prod (I : Finset (Fin 5)) (r : Fin 5 → ℕ) :
    (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
      ∏ i, (direction J i : ℚ) ^ r i) = ∏ i ∈ I, ((2 : ℚ) ^ r i - 1) := by
  simp_rw [direction_prod, sub_eq_add_neg]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hJ), mul_comm]
private theorem coefficient_sum {m d : ℕ} (p : Fin m → Fin 5 → Polynomial ℚ)
    (hp : ∀ a i, 0 < (p a i).leadingCoeff) {t : Fin 5 → ℕ} (ht : ∀ i, 0 < t i)
    (hd : ∀ a, (∑ i, (p a i).natDegree) ≤ d) :
    (∑ a, rayTerm (p a) t).coeff d =
      ∑ a, (if (∑ i, (p a i).natDegree) = d then ∏ i, (p a i).leadingCoeff else 0) *
        ∏ i, (t i : ℚ) ^ (p a i).natDegree := by
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases (hd a).lt_or_eq with hlt | heq
  · have htlt : (rayTerm (p a) t).natDegree < d := (rayTerm_natDegree (p a) (hp a) ht).trans_lt hlt
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt htlt, ite_eq_right hlt.ne, zero_mul]
  · rw [ite_eq_left heq, ← rayTerm_leadingCoeff _ ht,
      ← (rayTerm_natDegree (p a) (hp a) ht).trans heq, Polynomial.coeff_natDegree]
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_2_4_2.c2 := by
  intro B hB P I _ hP
  obtain ⟨o, ho⟩ := h1 B P
  obtain ⟨bad, hb⟩ := o.exists_finset_standardExponents_iff (RingHom.ker (slotMap B P).toRingHom)
  have hbad (u : Fin 5 → ℕ) :
      Module.finrank GeoField (slotPiece B P u) = sliceCount (fun v => v.1) bad u := by
    rw [ho]
    simp only [sliceCount, hb]
  obtain ⟨m, p, hp, N, hN⟩ := h2 (fun v : SlotVars B => v.1) bad
  have hray (t : Fin 5 → ℕ) (ht : ∀ i, 0 < t i) :
      affineHilbertPolynomial (diagonalIdeal B P t) = ∑ a, rayTerm (p a) t := by
    symm
    refine eq_affineHilbertPolynomial_of_eval_eq (N₀ := N) fun n hn => ?_
    rw [diagonal_hilbert B P t n, hbad, hN (fun i => n * t i)
      (fun i => hn.trans (Nat.le_mul_of_pos_right n (ht i)))]
    simp only [rayTerm, rayFactor, Polynomial.eval_finsetSum, Polynomial.eval_prod,
      Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Nat.cast_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (t i : ℚ) (n : ℚ)]
  have hd : ∀ a, (∑ i, (p a i).natDegree) ≤ I.card := by
    let t : Fin 5 → ℕ := fun _ => 1
    have ht (i : Fin 5) : 0 < t i := Nat.zero_lt_one
    have hle := K1_13_6_2_4_2.diagonal_degree_le hB hP ht
    change (affineHilbertPolynomial (diagonalIdeal B P t)).natDegree ≤ I.card at hle
    rw [hray t ht] at hle
    intro a
    rw [← rayTerm_natDegree (p a) (hp a) ht]
    apply summand_degree_le _ _ hle
    intro b
    rw [rayTerm_leadingCoeff _ ht]
    exact mul_pos (Finset.prod_pos fun i _ => hp b i)
      (Finset.prod_pos fun i _ => pow_pos (Nat.cast_pos.mpr (ht i)) _)
  let w (a : Fin m) : ℚ :=
    if (∑ i, (p a i).natDegree) = I.card then ∏ i, (p a i).leadingCoeff else 0
  have hcoeff (J : Finset (Fin 5)) :
      (affineHilbertPolynomial (diagonalIdeal B P (direction J))).coeff I.card =
        ∑ a, w a * ∏ i, (direction J i : ℚ) ^ (p a i).natDegree := by
    rw [hray _ (direction_pos J)]
    exact coefficient_sum p hp (direction_pos J) hd
  change 0 ≤ (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
    (affineHilbertPolynomial (diagonalIdeal B P (direction J))).coeff I.card) / (2 : ℚ) ^ I.card
  apply div_nonneg _ (by positivity)
  simp_rw [hcoeff, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun a _ => ?_
  simp_rw [mul_left_comm ((-1 : ℚ) ^ _) (w a), ← Finset.mul_sum]
  rw [signed_prod]
  apply mul_nonneg
  · unfold w
    split_ifs
    · exact Finset.prod_nonneg fun i _ => (hp a i).le
    · exact le_rfl
  · exact Finset.prod_nonneg fun i _ =>
      sub_nonneg.mpr (one_le_pow₀ (by norm_num))
end
end K1_13_6_2_4_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_2_2_1
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 K1_13_6_2_4_2_2 MvPolynomial
open scoped BigOperators
def tagExponent (B : Boxes) : (SlotVars B →₀ ℕ) →+ Exponent :=
  Finsupp.mapDomain.addMonoidHom fun v => v.1
def affineExponent (B : Boxes) : (SlotVars B →₀ ℕ) →+ Exponent :=
  Finsupp.liftAddHom fun v => multiplesHom Exponent v.2.val
private theorem tagExponent_apply (B : Boxes) (e : SlotVars B →₀ ℕ) (i : Fin 5) :
    tagExponent B e i = slotDegree (fun v => v.1) e i := by
  classical
  change (Finsupp.mapDomain (fun v => v.1) e) i = _
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [slotDegree, Finsupp.single_apply]
theorem tagExponent_eq_iff (B : Boxes) (e : SlotVars B →₀ ℕ) (u : Fin 5 → ℕ) :
    tagExponent B e = Finsupp.equivFunOnFinite.symm u ↔
      slotDegree (fun v => v.1) e = u := by
  rw [Finsupp.equivFunOnFinite.eq_symm_apply]
  change (fun i => tagExponent B e i) = u ↔ _
  rw [funext (tagExponent_apply B e)]
@[simp] private theorem tag_single (B : Boxes) (v : SlotVars B) (n : ℕ) :
    tagExponent B (Finsupp.single v n) = Finsupp.single v.1 n :=
  Finsupp.mapDomain_single
@[simp] private theorem affine_single (B : Boxes) (v : SlotVars B) (n : ℕ) :
    affineExponent B (Finsupp.single v n) = n • v.2.val :=
  Finsupp.liftAddHom_apply_single _ _ _
private theorem affine_mem_diagonal (B : Boxes) (e : SlotVars B →₀ ℕ) :
    affineExponent B e ∈ diagonalExponents B (tagExponent B e) := by
  classical
  induction e using Finsupp.induction_linear with
  | zero =>
      rw [map_zero, map_zero]
      exact ⟨fun _ j => j.elim0, fun _ j => j.elim0, by simp⟩
  | add x y hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      simp only [map_add]
      change ∃ w : (i : Fin 5) → Fin (tagExponent B x i + tagExponent B y i) → Exponent,
        (∀ i j, w i j ∈ latticePoints (B i)) ∧ affineExponent B x + affineExponent B y =
          ∑ i, ∑ j, w i j
      refine ⟨fun i => Fin.append (a i) (b i),
        fun i => Fin.addCases (fun j => by simpa using ha i j)
          (fun j => by simpa using hb i j), ?_⟩
      rw [hax, hby, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
  | single v n =>
      simp only [affine_single, tag_single]
      let w : (i : Fin 5) → Fin (Finsupp.single v.1 n i) → Exponent :=
        fun i _ => if v.1 = i then v.2.val else 0
      refine ⟨w, fun i j => ?_, ?_⟩
      · by_cases hi : v.1 = i
        · subst i
          simp [w, v.2.property]
        · simp [w, hi, latticePoints, Allowed]
      · simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [Finset.sum_eq_single v.1]
        · simp
        · intro i _ hi
          simp [hi.symm]
        · simp
theorem diagonal_eq_image (B : Boxes) (u : Fin 5 → ℕ) :
    diagonalExponents B u =
      affineExponent B '' {e | tagExponent B e = Finsupp.equivFunOnFinite.symm u} := by
  classical
  ext m
  constructor
  · rintro ⟨a, ha, rfl⟩
    let e : SlotVars B →₀ ℕ :=
      ∑ i, ∑ j, Finsupp.single (⟨i, ⟨a i j, ha i j⟩⟩ : SlotVars B) 1
    refine ⟨e, ?_, ?_⟩
    · change tagExponent B e = Finsupp.equivFunOnFinite.symm u
      ext i
      simp only [e, map_sum, tag_single, Finsupp.finsetSum_apply,
        Finsupp.coe_equivFunOnFinite_symm, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    · simp only [e, map_sum, affine_single, one_nsmul]
  · rintro ⟨e, he, rfl⟩
    have h := affine_mem_diagonal B e
    change tagExponent B e = Finsupp.equivFunOnFinite.symm u at he
    rw [he] at h
    exact h
theorem slotMap_monomial (B : Boxes) (P : Ideal GeoJets5) (e : SlotVars B →₀ ℕ) :
    slotMap B P (monomial e 1) =
      monomial (tagExponent B e) (Ideal.Quotient.mk P (monomial (affineExponent B e) 1)) := by
  classical
  induction e using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [show monomial (x + y) (1 : GeoField) = monomial x 1 * monomial y 1 by
        rw [monomial_mul_monomial, one_mul]]
      rw [map_mul, hx, hy, monomial_mul_monomial, map_add, map_add, ← map_mul,
        monomial_mul_monomial, one_mul]
  | single v n =>
      have hv : slotMap B P (MvPolynomial.X v) =
          monomial (Finsupp.single v.1 1) (Ideal.Quotient.mk P (monomial v.2.val 1)) :=
        aeval_X _ _
      rw [← X_pow_eq_monomial, map_pow, hv, monomial_pow, tag_single, affine_single,
        ← map_pow, monomial_pow, one_pow]
      simp
end
end K1_13_6_2_4_2_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_3_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 MvPolynomial
open scoped BigOperators
private abbrev capMap (p : Shape) := monomialMap GeoField (capExponents p)
private abbrev capIdeal (I : Ideal GeoJets) (p : Shape) := I.comap (capMap p).toRingHom
private theorem capMap_surjective {p : Shape} (hp : ChamberBox p) :
    Function.Surjective (capMap p) := by
  obtain ⟨hb, hj, ht⟩ := hp
  apply monomialMap_surjective
  intro i
  fin_cases i <;> simp [capExponents, Fin.sum_univ_four] <;> omega
private theorem cap_dimension (I : Ideal GeoJets) {p : Shape} (hp : ChamberBox p) :
    (affineHilbertPolynomial (capIdeal I p)).natDegree = dimension I :=
  natDegree_affineHilbertPolynomial_comap_of_surjective (capMap p) (capMap_surjective hp) I
private theorem capCoeff_eq_zero_of_lt {P Q : Ideal GeoJets} (hP : P.IsPrime) (hPQ : P < Q)
    {p : Shape} (hp : ChamberBox p) {d : ℕ} (hd : dimension P ≤ d) :
    capCoeff Q d p = 0 := by
  obtain ⟨f, hfQ, hfP⟩ := Set.not_subset.mp
    (show ¬ (Q : Set GeoJets) ⊆ P from hPQ.not_ge)
  let J := P ⊔ Ideal.span {f}
  have hJQ : J ≤ Q := sup_le hPQ.le (Q.span_singleton_le_iff_mem.mpr hfQ)
  have hdrop := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hP hfP (b := f.totalDegree) le_rfl
  have hQdim : dimension Q ≤ dimension J := natDegree_affineHilbertPolynomial_le_of_le hJQ
  by_cases hz : d = 0
  · subst d
    have hP0 := Nat.eq_zero_of_le_zero hd
    have hJ0 : dimension J ≤ 0 := by simpa [J, hP0] using hdrop.1
    have hJtop : J = ⊤ := by
      apply affineHilbertPolynomial_eq_zero_iff.mp
      have hupper : (affineHilbertPolynomial J).coeff 0 ≤ 0 := by
        simpa [J, hP0] using hdrop.2
      have hzero := le_antisymm hupper
        (Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg hJ0
          (eventually_eval_affineHilbertPolynomial_nonneg J))
      rw [Polynomial.eq_C_of_natDegree_le_zero hJ0, hzero, map_zero]
    have hQtop : Q = ⊤ := top_le_iff.mp (hJtop ▸ hJQ)
    simp [hQtop, capCoeff, Ideal.comap_top, affineHilbertPolynomial_top]
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [cap_dimension Q hp]
    have hj : dimension J ≤ dimension P - 1 := hdrop.1
    omega
private theorem capCoeff_step (I : Ideal GeoJets) (g : GeoJets) {p : Shape} (hp : ChamberBox p)
    {d : ℕ} (hd : dimension I ≤ d) :
    capCoeff I d p = capCoeff (I ⊔ Ideal.span {g}) d p + capCoeff (I.colon {g}) d p := by
  let φ := (capMap p).toRingHom
  have hφ : Function.Surjective φ := capMap_surjective hp
  obtain ⟨G, hG⟩ := hφ g
  have hcut : capIdeal (I ⊔ Ideal.span {g}) p = capIdeal I p ⊔ Ideal.span {G} := by
    have hm : (capIdeal I p ⊔ Ideal.span {G}).map φ = I ⊔ Ideal.span {g} := by
      change (I.comap φ ⊔ Ideal.span {G}).map φ = _
      rw [Ideal.map_sup, Ideal.map_comap_of_surjective _ hφ, Ideal.map_span, Set.image_singleton, hG]
    change (I ⊔ Ideal.span {g}).comap φ = _
    rw [← hm, Ideal.comap_map_of_surjective _ hφ]
    exact sup_eq_left.mpr ((Ideal.comap_mono (f := φ) bot_le :
      (⊥ : Ideal GeoJets).comap φ ≤ I.comap φ).trans le_sup_left)
  have hann (x : MvPolynomial (capExponents p) GeoField) :
      x * G ∈ capIdeal I p ↔ x ∈ capIdeal (I.colon {g}) p := by
    change φ (x * G) ∈ I ↔ φ x ∈ I.colon {g}
    rw [map_mul, hG, Submodule.mem_colon_singleton, smul_eq_mul]
  change (affineHilbertPolynomial (capIdeal I p)).coeff d =
    (affineHilbertPolynomial (capIdeal (I ⊔ Ideal.span {g}) p)).coeff d +
      (affineHilbertPolynomial (capIdeal (I.colon {g}) p)).coeff d
  rw [hcut]
  exact hilbertCoeff_step hann ((cap_dimension I hp).trans_le hd)
private theorem length_finite {J I P : Ideal GeoJets} (hJI : J ≤ I)
    (hP : J.IsMinimalPrime P) : cycleLength I P hP.isPrime ≠ ⊤ := by
  by_cases hIP : I ≤ P
  · have hm : I.IsMinimalPrime P :=
      ⟨⟨hP.isPrime, hIP⟩, fun _ hR hRP => hP.2 ⟨hR.1, hJI.trans hR.2⟩ hRP⟩
    exact (positive_length hm).2
  · rw [K1_13_6_3_6.length_eq_zero_of_not_le hP.isPrime hIP]
    simp
private theorem weight_step {J I P : Ideal GeoJets} (hJI : J ≤ I)
    (hP : J.IsMinimalPrime P) (g : GeoJets) (hA : (I.colon {g}).IsPrime) :
    (localWeight I P : ℚ) =
      (localWeight (I ⊔ Ideal.span {g}) P : ℚ) + (if P = I.colon {g} then 1 else 0) := by
  classical
  let A := I.colon {g}
  have hterm : cycleLength A P hP.isPrime = if P = A then 1 else 0 := by
    split_ifs with h
    · subst P
      exact K1_13_6_3_6.length_self A hP.isPrime
    · exact K1_13_6_3_6.length_eq_zero_of_not_le hP.isPrime
        (fun hAP => h (le_antisymm (hP.2 ⟨hA, hJI.trans Ideal.le_colon⟩ hAP) hAP))
  change (localWeight I P : ℚ) =
    (localWeight (I ⊔ Ideal.span {g}) P : ℚ) + (if P = A then 1 else 0)
  simp only [localWeight, dite_eq_left hP.isPrime]
  rw [K1_13_6_3_6.length_step I P hP.isPrime g,
    ENat.toNat_add (length_finite (hJI.trans Ideal.le_colon) hP)
      (length_finite (hJI.trans le_sup_left) hP), hterm, Nat.cast_add]
  split_ifs <;> simp [add_comm]
theorem proof : K1_13_6_2_3_3.c1 := by
  classical
  intro J d hd p hp
  let T := J.minimalPrimesFinset
  suffices h : ∀ I : Ideal GeoJets, J ≤ I →
      capCoeff I d p = ∑ P ∈ T, (localWeight I P : ℚ) * capCoeff P d p from h J le_rfl
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α := Ideal GeoJets)) with
  | h I ih =>
    intro hJI
    by_cases hI : I = ⊤
    · subst I
      simp only [capCoeff, Ideal.comap_top, affineHilbertPolynomial_top, Polynomial.coeff_zero]
      symm
      apply Finset.sum_eq_zero
      intro P hP
      have hprime := (Ideal.mem_minimalPrimesFinset.mp hP).isPrime
      have hz := K1_13_6_3_6.length_eq_zero_of_not_le (I := ⊤) hprime (by simpa using hprime.ne_top)
      simp [localWeight, hprime, hz]
    obtain ⟨g, hg, hprime⟩ := K1_13_6_3_6.exists_prime_colon I hI
    let A := I.colon {g}
    let B := I ⊔ Ideal.span {g}
    have hJA : J ≤ A := hJI.trans Ideal.le_colon
    have hIB : I < B := lt_of_le_not_ge le_sup_left
      (fun h => hg (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))
    have hrec := ih B hIB (hJI.trans hIB.le)
    have hindicator : capCoeff A d p = if A ∈ T then capCoeff A d p else 0 := by
      by_cases hA : A ∈ T
      · rw [ite_eq_left hA]
      · have : A.IsPrime := hprime
        obtain ⟨P, hP, hPA⟩ := Ideal.exists_minimalPrimes_le hJA
        have hlt : P < A := hPA.lt_of_ne (fun h => hA (h ▸ Ideal.mem_minimalPrimesFinset.mpr hP))
        rw [ite_eq_right hA]
        exact capCoeff_eq_zero_of_lt hP.isPrime hlt hp
          ((natDegree_affineHilbertPolynomial_le_of_le hP.le).trans hd)
    have hdim := (natDegree_affineHilbertPolynomial_le_of_le hJI).trans hd
    calc
      capCoeff I d p = capCoeff B d p + capCoeff A d p := capCoeff_step I g hp hdim
      _ = (∑ P ∈ T, (localWeight B P : ℚ) * capCoeff P d p) +
          (if A ∈ T then capCoeff A d p else 0) := by rw [hrec, ← hindicator]
      _ = _ := by
        rw [← Finset.sum_ite_eq' T A (fun P => capCoeff P d p), ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [weight_step hJI (Ideal.mem_minimalPrimesFinset.mp hP) g hprime, add_mul, ite_mul,
          one_mul, zero_mul]
end
end K1_13_6_2_3_3_1
end
section
set_option autoImplicit false
namespace K1_13_7_6_1
noncomputable section
open K1_13_7 K1_13_7_6 MvPolynomial
variable {σ : Type} [Finite σ]
set_option maxHeartbeats 800000 in
theorem weightedCoeff_le (φ : MvPolynomial σ GeometricX →ₐ[GeometricX] Lower)
    (hφ : Function.Surjective φ) (B : Ideal Lower) {d : ℕ}
    (hd : (affineHilbertPolynomial (B.comap φ)).natDegree ≤ d)
    (qs : Finset (PrimeSpectrum Lower))
    (hmin : ∀ q ∈ qs, q.asIdeal ∈ B.minimalPrimes)
    (J : Ideal Lower) (hBJ : B ≤ J) (hfin : ∀ q ∈ qs, localColength q J < ⊤) :
    ∑ q ∈ qs, (localColength q J).toNat *
        (affineHilbertPolynomial (q.asIdeal.comap φ)).coeff d ≤
      (affineHilbertPolynomial (J.comap φ)).coeff d := by
  classical
  let C := fun I : Ideal Lower => (affineHilbertPolynomial (I.comap φ)).coeff d
  change ∑ q ∈ qs, (localColength q J).toNat * C q.asIdeal ≤ C J
  revert hBJ hfin
  induction J using WellFounded.induction (wellFounded_gt (α := Ideal Lower)) with
  | h J ih =>
    intro hBJ hfin
    by_cases hJ : J = ⊤
    · subst J
      have htop (q : PrimeSpectrum Lower) : localColength q ⊤ = 0 := by
        dsimp only [localColength]
        rw [Ideal.map_top]
        exact Module.length_eq_zero
      simp [htop, C, Ideal.comap_top, affineHilbertPolynomial_top]
    obtain ⟨a, Q, haJ, hQ, hann⟩ := exists_prime_factor hJ
    obtain ⟨A, hA⟩ := hφ a
    let K := J ⊔ Ideal.span {a}
    have hJK : J ≤ K := le_sup_left
    have haK : a ∈ K := Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < K := lt_of_le_of_ne hJK fun he => haJ (he ▸ haK)
    have hBQ : B ≤ Q := fun x hx => (hann x).mp (J.mul_mem_right _ (hBJ hx))
    have hQd := (natDegree_affineHilbertPolynomial_le_of_le (Ideal.comap_mono hBQ)).trans hd
    have hCQ : 0 ≤ C Q :=
      Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg hQd
        (eventually_eval_affineHilbertPolynomial_nonneg (Q.comap φ))
    have hstep (q : PrimeSpectrum Lower) (hq : q ∈ qs) :
        localColength q J = (if Q = q.asIdeal then 1 else 0) + localColength q K :=
      localColength_step hBJ hQ hann (hmin q hq)
    have hfinK (q : PrimeSpectrum Lower) (hq : q ∈ qs) : localColength q K < ⊤ := by
      have hle : localColength q K ≤ localColength q J := by
        rw [hstep q hq]
        exact le_add_self
      exact hle.trans_lt (hfin q hq)
    have hrec := ih K hlt (hBJ.trans hJK) hfinK
    have hCKQ : C K + C Q ≤ C J := by
      have hAK : A ∈ K.comap φ := by
        change φ A ∈ K
        rwa [hA]
      refine hilbertCoeff_step (Ideal.comap_mono hJK) hAK (fun x => ?_) ?_
      · change φ (x * A) ∈ J ↔ φ x ∈ Q
        rw [map_mul, hA, hann]
      · exact (natDegree_affineHilbertPolynomial_le_of_le (Ideal.comap_mono hBJ)).trans hd
    have hindicator : ∑ q ∈ qs, (if Q = q.asIdeal then C Q else 0) ≤ C Q := by
      by_cases he : ∃ q ∈ qs, Q = (q : PrimeSpectrum Lower).asIdeal
      · obtain ⟨q, hq, hEq⟩ := he
        rw [Finset.sum_eq_single_of_mem q hq, ite_eq_left hEq]
        intro r _ hr
        exact ite_eq_right (fun hrQ => hr (PrimeSpectrum.ext (hrQ.symm.trans hEq)))
      · rw [Finset.sum_eq_zero fun q hq => ite_eq_right (fun h => he ⟨q, hq, h⟩)]
        exact hCQ
    calc
      ∑ q ∈ qs, (localColength q J).toNat * C q.asIdeal
          = (∑ q ∈ qs, (localColength q K).toNat * C q.asIdeal) +
              ∑ q ∈ qs, (if Q = q.asIdeal then C Q else 0) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun q hq => ?_
            by_cases he : Q = q.asIdeal
            · rw [hstep q hq, ite_eq_left he, ite_eq_left he, ENat.toNat_add (by simp) (hfinK q hq).ne,
                ENat.toNat_one, Nat.cast_add, Nat.cast_one, add_mul, one_mul, he, add_comm]
            · rw [hstep q hq, ite_eq_right he, ite_eq_right he, zero_add, add_zero]
      _ ≤ C K + C Q := add_le_add hrec hindicator
      _ ≤ C J := hCKQ
theorem proof : K1_13_7_6.c1 := by
  classical
  intro σ _ φ hφ p L hL hp qs hmin hfin
  by_cases hempty : qs = ∅
  · rw [hempty]
    simpa only [cutCost, Finset.sum_empty, chartDegree] using
      affineDegree_nonneg (p.asIdeal.comap φ)
  let P := p.asIdeal.comap φ
  let B := cutIdeal p (φ L)
  have hBc : B.comap φ = P ⊔ Ideal.span {L} := by
    have hm : (P ⊔ Ideal.span {L}).map φ = B := by
      dsimp [P, B, cutIdeal]
      rw [Ideal.map_sup, Ideal.map_comap_of_surjective _ hφ, Ideal.map_span, Set.image_singleton]
    rw [← hm, Ideal.comap_map_of_surjective _ hφ]
    exact sup_eq_left.mpr ((Ideal.comap_mono (f := φ) bot_le : (⊥ : Ideal Lower).comap φ ≤ P).trans
      le_sup_left)
  have hP : P.IsPrime := Ideal.comap_isPrime _ _
  have := hP
  have hproper : L ∉ P := hp
  let d := (affineHilbertPolynomial P).natDegree - 1
  have hbound := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hP hproper hL
  have hd : (affineHilbertPolynomial (B.comap φ)).natDegree ≤ d := hBc.symm ▸ hbound.1
  have hpurity (q : PrimeSpectrum Lower) (hq : q ∈ qs) :
      (affineHilbertPolynomial (q.asIdeal.comap φ)).natDegree + 1 =
        (affineHilbertPolynomial P).natDegree := by
    refine principalCut_natDegree_affineHilbertPolynomial_add_one hproper ?_
    rw [← hBc]
    exact Ideal.minimalPrimes_comap_of_surjective (f := φ.toRingHom) hφ (hmin q hq)
  obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hparent : (affineHilbertPolynomial P).natDegree = d + 1 := by
    have := hpurity q hq
    dsimp [d]
    omega
  have hc := weightedCoeff_le φ hφ B hd qs hmin B le_rfl hfin
  have hmul := mul_le_mul_of_nonneg_left (hc.trans (hBc.symm ▸ hbound.2))
    (Nat.cast_nonneg (α := ℚ) d.factorial)
  calc
    cutCost (chartDegree φ) p (φ L) qs =
        (d.factorial : ℚ) * ∑ q ∈ qs, (localColength q B).toNat *
          (affineHilbertPolynomial (q.asIdeal.comap φ)).coeff d := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hchild : (affineHilbertPolynomial (q.asIdeal.comap φ)).natDegree = d := by
        have := hpurity q hq
        omega
      unfold chartDegree affineDegree
      rw [Polynomial.leadingCoeff, hchild]
      ring
    _ ≤ (d.factorial : ℚ) * ((1 : ℚ) * (affineHilbertPolynomial P).natDegree *
        (affineHilbertPolynomial P).leadingCoeff) := by simpa only [Nat.cast_one] using hmul
    _ = chartDegree φ p := by
      change _ = affineDegree P
      rw [affineDegree, hparent, Nat.factorial_succ, Nat.cast_mul]
      ring
end
end K1_13_7_6_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_2_2_2
noncomputable section
open scoped BigOperators
open K1_13_6_2_4_2_2 (slotDegree sliceCount)
variable {σ : Type}
private def cut (bad : Finset (σ →₀ ℕ)) (v : σ) : ℕ :=
  bad.sup fun b => b v
private abbrev Base (c : σ → ℕ) := ∀ v, Fin (c v + 1)
private def clip (c x : σ → ℕ) : Base c :=
  fun v => ⟨min (x v) (c v), Nat.lt_succ_of_le (min_le_right _ _)⟩
private theorem le_clip_iff {bad : Finset (σ →₀ ℕ)} {b : σ →₀ ℕ}
    (hb : b ∈ bad) (x : σ → ℕ) :
    (∀ v, b v ≤ (clip (cut bad) x v : ℕ)) ↔ ∀ v, b v ≤ x v := by
  refine ⟨fun h v => (h v).trans (min_le_left _ _), fun h v => ?_⟩
  exact le_min (h v) (Finset.le_sup (f := fun b : σ →₀ ℕ => b v) hb)
variable [Fintype σ]
private def free {c : σ → ℕ} (slot : σ → Fin 5) (b : Base c) (i : Fin 5) : Finset σ :=
  Finset.univ.filter fun v => slot v = i ∧ (b v : ℕ) = c v
private theorem mem_free {c : σ → ℕ} {slot : σ → Fin 5} {b : Base c} {i : Fin 5} {v : σ} :
    v ∈ free slot b i ↔ slot v = i ∧ (b v : ℕ) = c v := by
  simp [free]
private def degree (slot : σ → Fin 5) (x : σ → ℕ) (i : Fin 5) : ℕ :=
  ∑ v, if slot v = i then x v else 0
private theorem degree_add (slot : σ → Fin 5) (x y : σ → ℕ) (i : Fin 5) :
    degree slot (x + y) i = degree slot x i + degree slot y i := by
  simp only [degree, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by by_cases h : slot v = i <;> simp [h]
private theorem degree_finsupp (slot : σ → Fin 5) (e : σ →₀ ℕ) (i : Fin 5) :
    degree slot e i = slotDegree slot e i := by
  rw [slotDegree, Finsupp.sum_fintype]
  · rfl
  · intro v
    split <;> rfl
private abbrev shift {c : σ → ℕ} (slot : σ → Fin 5) (b : Base c) (i : Fin 5) : ℕ :=
  degree slot (fun v => (b v : ℕ)) i
private def threshold (bad : Finset (σ →₀ ℕ)) : ℕ := (∑ v, cut bad v) + 1
private theorem shift_lt (slot : σ → Fin 5) {bad : Finset (σ →₀ ℕ)}
    (b : Base (cut bad)) (i : Fin 5) :
    shift slot b i < threshold bad := by
  apply Nat.lt_succ_of_le
  change (∑ v, if slot v = i then (b v : ℕ) else 0) ≤ ∑ v, cut bad v
  exact Finset.sum_le_sum fun v _ => by
    by_cases hv : slot v = i
    · simp only [ite_eq_left hv]
      exact Nat.le_of_lt_succ (b v).isLt
    · simp [hv]
variable [DecidableEq σ]
private def residue {c : σ → ℕ} (slot : σ → Fin 5) (b : Base c)
    (x : ∀ i : Fin 5, free slot b i → ℕ) (v : σ) : ℕ :=
  if h : v ∈ free slot b (slot v) then x (slot v) ⟨v, h⟩ else 0
private theorem residue_at {c : σ → ℕ} (slot : σ → Fin 5) (b : Base c)
    (x : ∀ i : Fin 5, free slot b i → ℕ) (i : Fin 5) (v : free slot b i) :
    residue slot b x v.val = x i v := by
  obtain ⟨v, hv⟩ := v
  have hi := (mem_free.mp hv).1
  subst i
  rw [residue, dite_eq_left hv]
private theorem degree_residue {c : σ → ℕ} (slot : σ → Fin 5) (b : Base c)
    (x : ∀ i : Fin 5, free slot b i → ℕ) (i : Fin 5) :
    degree slot (residue slot b x) i = ∑ v : free slot b i, x i v := by
  calc
    _ = ∑ v ∈ free slot b i, residue slot b x v := by
      rw [degree, free, Finset.sum_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hi : slot v = i
      · by_cases hb : (b v : ℕ) = c v
        · simp [hi, hb]
        · have hv : v ∉ free slot b (slot v) := fun h => hb (mem_free.mp h).2
          have hr : residue slot b x v = 0 := dite_eq_right hv
          simp [hi, hb, hr]
      · simp [hi]
    _ = ∑ v : free slot b i, residue slot b x v.val :=
      Finset.sum_subtype _ (fun _ => Iff.rfl) _
    _ = _ := Finset.sum_congr rfl fun v _ => residue_at slot b x i v
private theorem clip_restore {c : σ → ℕ} (slot : σ → Fin 5) (b : Base c)
    (x : ∀ i : Fin 5, free slot b i → ℕ) :
    clip c ((fun v => (b v : ℕ)) + residue slot b x) = b := by
  funext v
  apply Fin.ext
  change min ((b v : ℕ) + residue slot b x v) (c v) = (b v : ℕ)
  by_cases hb : (b v : ℕ) = c v
  · rw [hb, min_eq_right (Nat.le_add_right _ _)]
  · have hv : v ∉ free slot b (slot v) := fun h => hb (mem_free.mp h).2
    rw [residue, dite_eq_right hv, add_zero, min_eq_left (Nat.le_of_lt_succ (b v).isLt)]
private theorem restore_clip (c : σ → ℕ) (slot : σ → Fin 5) (e : σ → ℕ) :
    (fun v => ((clip c e) v : ℕ)) +
      residue slot (clip c e) (fun _ v => e v.val - ((clip c e) v.val : ℕ)) = e := by
  funext v
  change ((clip c e) v : ℕ) + residue slot (clip c e) _ v = e v
  rw [residue]
  split
  · exact Nat.add_sub_of_le (min_le_left _ _)
  · rename_i hv
    have hlt : min (e v) (c v) < c v := lt_of_le_of_ne (min_le_right _ _)
      (fun h => hv (mem_free.mpr ⟨rfl, h⟩))
    have hle : e v ≤ c v := by omega
    change min (e v) (c v) + 0 = e v
    rw [min_eq_left hle, add_zero]
private abbrev GoodBase (slot : σ → Fin 5) (bad : Finset (σ →₀ ℕ)) :=
  {b : Base (cut bad) // (∀ q ∈ bad, ¬ ∀ v, q v ≤ (b v : ℕ)) ∧
    ∀ i, (free slot b i).Nonempty}
private abbrev Slice (slot : σ → Fin 5) (bad : Finset (σ →₀ ℕ)) (u : Fin 5 → ℕ) :=
  {e : σ →₀ ℕ // slotDegree slot e = u ∧ ∀ q ∈ bad, ¬ q ≤ e}
private abbrev Fiber (slot : σ → Fin 5) (u : Fin 5 → ℕ) {c : σ → ℕ} (b : Base c) :=
  ∀ i : Fin 5, {x : free slot b i → ℕ // ∑ v, x v = u i - shift slot b i}
private def assemble (slot : σ → Fin 5) (bad : Finset (σ →₀ ℕ)) (u : Fin 5 → ℕ)
    (hu : ∀ i, threshold bad ≤ u i) :
    (Σ b : GoodBase slot bad, Fiber slot u b.val) → Slice slot bad u
  | ⟨b, x⟩ => by
    let e : σ → ℕ := (fun v => (b.val v : ℕ)) + residue slot b.val (fun i => (x i).val)
    refine ⟨Finsupp.equivFunOnFinite.symm e, ?_, ?_⟩
    · funext i
      rw [← degree_finsupp]
      change degree slot ((fun v => (b.val v : ℕ)) +
        residue slot b.val (fun i => (x i).val)) i = u i
      rw [degree_add, degree_residue, (x i).property]
      exact Nat.add_sub_of_le ((shift_lt slot b.val i).le.trans (hu i))
    · intro q hq hle
      refine b.property.1 q hq ?_
      have hc := le_clip_iff hq e |>.mpr (fun v => hle v)
      rwa [show clip (cut bad) e = b.val from clip_restore slot b.val _] at hc
private theorem assemble_bijective (slot : σ → Fin 5) (bad : Finset (σ →₀ ℕ))
    (u : Fin 5 → ℕ) (hu : ∀ i, threshold bad ≤ u i) :
    Function.Bijective (assemble slot bad u hu) := by
  constructor
  · rintro ⟨b, x⟩ ⟨c, y⟩ h
    have hb (b : GoodBase slot bad) (x : Fiber slot u b.val) :
        clip (cut bad) (assemble slot bad u hu ⟨b, x⟩).val = b.val :=
      clip_restore slot b.val _
    have hbc : b = c := Subtype.ext ((hb b x).symm.trans
      ((congrArg (fun e : Slice slot bad u => clip (cut bad) e.val) h).trans (hb c y)))
    subst c
    have hxy : x = y := by
      funext i
      apply Subtype.ext
      funext v
      have he := congrArg (fun e : Slice slot bad u => e.val v.val) h
      change (b.val v.val : ℕ) + residue slot b.val (fun j => (x j).val) v.val =
        (b.val v.val : ℕ) + residue slot b.val (fun j => (y j).val) v.val at he
      have hr := Nat.add_left_cancel he
      rwa [residue_at slot b.val _ i v, residue_at slot b.val _ i v] at hr
    subst y
    rfl
  · intro e
    let b := clip (cut bad) e.val
    let x (i : Fin 5) (v : free slot b i) := e.val v.val - (b v.val : ℕ)
    have hrestore : (fun v => (b v : ℕ)) + residue slot b x = e.val :=
      restore_clip (cut bad) slot e.val
    have hsum (i : Fin 5) : shift slot b i + (∑ v, x i v) = u i := by
      rw [← degree_residue, ← degree_add, hrestore, degree_finsupp, e.property.1]
    have hfree (i : Fin 5) : (free slot b i).Nonempty := by
      by_contra h
      have : IsEmpty (free slot b i) := ⟨fun v => h ⟨v.val, v.property⟩⟩
      have hs := hsum i
      rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hs
      exact ((shift_lt slot b i).trans_le (hu i)).ne hs
    have hok (q : σ →₀ ℕ) (hq : q ∈ bad) :
        ¬ ∀ v, q v ≤ (b v : ℕ) :=
      fun h => e.property.2 q hq ((le_clip_iff hq e.val).mp h)
    let b' : GoodBase slot bad := ⟨b, hok, hfree⟩
    let x' : Fiber slot u b'.val := fun i => ⟨x i, by
      change (∑ v, x i v) = u i - shift slot b i
      have hs := hsum i
      omega⟩
    refine ⟨⟨b', x'⟩, Subtype.ext ?_⟩
    change Finsupp.equivFunOnFinite.symm
      ((fun v => (b v : ℕ)) + residue slot b x) = e.val
    rw [hrestore, Finsupp.equivFunOnFinite_symm_coe]
private def compositionsEquiv (s : Finset σ) (n : ℕ) :
    s.finsuppAntidiag n ≃ {f : s → ℕ // ∑ v, f v = n} :=
  (Finset.finsuppAntidiagEquiv s n).trans (Sym.equivNatSumOfFintype s n)
omit [Fintype σ] in
private theorem eval_fiber (s : Finset σ) (hs : s.Nonempty)
    {u k : ℕ} (hk : k ≤ u) :
    ((s.finsuppAntidiag (u - k)).card : ℚ) =
      (Polynomial.preHilbertPoly ℚ (s.card - 1) k).eval (u : ℚ) := by
  rw [Finset.card_finsuppAntidiag_nat_eq_choose,
    Polynomial.preHilbertPoly_eq_choose_add_sub ℚ (s.card - 1) (k := k) (n := u) (by omega)]
  apply congrArg (fun n : ℕ => (n : ℚ))
  have hpos := Finset.card_pos.mpr hs
  rw [Nat.choose_symm_of_eq_add (a := u - k) (b := s.card - 1) (by omega)]
  congr 1
  omega
theorem proof : K1_13_6_2_4_2_2.c2 := by
  classical
  intro σ _ slot bad
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype (GoodBase slot bad) := Fintype.ofFinite _
  let m := Fintype.card (GoodBase slot bad)
  let idx : GoodBase slot bad ≃ Fin m := Fintype.equivFin _
  let p (a : Fin m) (i : Fin 5) :=
    Polynomial.preHilbertPoly ℚ ((free slot (idx.symm a).val i).card - 1)
      (shift slot (idx.symm a).val i)
  refine ⟨m, p, ?_, threshold bad, ?_⟩
  · intro a i
    dsimp only [p]
    rw [Polynomial.leadingCoeff_preHilbertPoly]
    positivity
  · intro u hu
    let e : Slice slot bad u ≃
        Σ b : GoodBase slot bad, ∀ i : Fin 5,
          (free slot b.val i).finsuppAntidiag (u i - shift slot b.val i) :=
      (Equiv.ofBijective _ (assemble_bijective slot bad u hu)).symm.trans
        (Equiv.sigmaCongrRight fun b =>
          Equiv.piCongrRight fun i =>
            (compositionsEquiv (free slot b.val i) (u i - shift slot b.val i)).symm)
    rw [sliceCount, ← Nat.card_coe_set_eq]
    change (Nat.card (Slice slot bad u) : ℚ) = _
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    simp only [Fintype.card_sigma, Fintype.card_pi, Fintype.card_coe, Nat.cast_sum, Nat.cast_prod]
    rw [← idx.sum_comp (fun a => ∏ i, (p a i).eval (u i : ℚ))]
    refine Finset.sum_congr rfl fun b _ => Finset.prod_congr rfl fun i _ => ?_
    simpa only [p, Equiv.symm_apply_apply] using
      eval_fiber (free slot b.val i) (b.property.2 i) ((shift_lt slot b.val i).le.trans (hu i))
end
end K1_13_6_2_4_2_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_2_2_1
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 K1_13_6_2_4_2_2 MvPolynomial
section Coefficients
variable {σ τ k R : Type} [Field k] [CommRing R] [Algebra k R]
private def coefficientMap (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ R)
    (u : τ →₀ ℕ) : MvPolynomial σ k →ₗ[k] R :=
  ((lcoeff R u).restrictScalars k).comp f.toLinearMap
private theorem coefficientMap_monomial
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ R)
    (tag : (σ →₀ ℕ) → (τ →₀ ℕ)) (a : (σ →₀ ℕ) → R)
    (hf : ∀ e, f (monomial e 1) = monomial (tag e) (a e)) (u : τ →₀ ℕ)
    (e : σ →₀ ℕ) [DecidableEq τ] :
    coefficientMap f u (monomial e 1) = if tag e = u then a e else 0 := by
  change (f (monomial e 1)).coeff u = _
  rw [hf, coeff_monomial]
private theorem map_support_matching_tag
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ R)
    (tag : (σ →₀ ℕ) → (τ →₀ ℕ)) (a : (σ →₀ ℕ) → R)
    (hf : ∀ e, f (monomial e 1) = monomial (tag e) (a e)) (u : τ →₀ ℕ)
    (S : Set (σ →₀ ℕ)) :
    (restrictSupport k {e | tag e = u ∧ e ∈ S}).map (coefficientMap f u) =
      (restrictSupport k S).map (coefficientMap f u) := by
  classical
  apply le_antisymm
  · exact Submodule.map_mono (restrictSupport_mono k fun _ he => he.2)
  · rw [restrictSupport_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    by_cases h : tag e = u
    · exact ⟨monomial e 1, (monomial_mem_restrictSupport k).mpr (Or.inl ⟨h, he⟩), rfl⟩
    · rw [coefficientMap_monomial f tag a hf, ite_eq_right h]
      exact Submodule.zero_mem _
private theorem finrank_coefficient_range
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ R)
    (tag : (σ →₀ ℕ) → (τ →₀ ℕ)) (a : (σ →₀ ℕ) → R)
    (hf : ∀ e, f (monomial e 1) = monomial (tag e) (a e))
    (o : MonomialOrder.{0, 0} σ) (u : τ →₀ ℕ) :
    Module.finrank k (LinearMap.range (coefficientMap f u)) =
      {e | tag e = u ∧ e ∈ o.standardExponents (RingHom.ker f.toRingHom)}.ncard := by
  classical
  let I := RingHom.ker f.toRingHom
  let S := {e | tag e = u ∧ e ∈ o.standardExponents I}
  let W := restrictSupport k S
  have hstandard : (o.standardSpace I).map (coefficientMap f u) =
      LinearMap.range (coefficientMap f u) := by
    refine le_antisymm LinearMap.map_le_range ?_
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq, hpq, _⟩ := o.exists_mem_standardSpace_sub_mem I p
    have heq : f p = f q := by
      change f (p - q) = 0 at hpq
      exact sub_eq_zero.mp (by simpa only [map_sub] using hpq)
    exact ⟨q, hq, by
      change (f q).coeff u = (f p).coeff u
      rw [heq]⟩
  have himage : W.map (coefficientMap f u) = LinearMap.range (coefficientMap f u) :=
    (map_support_matching_tag f tag a hf u (o.standardExponents I)).trans hstandard
  have hhomogeneous :
      W ≤ ((restrictSupport R {u}).restrictScalars k).comap f.toLinearMap := by
    change restrictSupport k S ≤ _
    rw [restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    change f (monomial e 1) ∈ restrictSupport R {u}
    rw [hf, monomial_mem_restrictSupport]
    exact Or.inl he.1
  let g := (coefficientMap f u).domRestrict W
  have hg : Function.Injective g := by
    apply (injective_iff_map_eq_zero g).mpr
    intro p hp
    have hs : ∀ e ∈ (f p.val).support, e = u :=
      (mem_restrictSupport_iff R).mp (hhomogeneous p.property)
    have hz : f p.val = 0 := by
      rw [eq_monomial_of_support_subset_singleton hs]
      change (f p.val).coeff u = 0 at hp
      rw [hp, monomial_zero]
    apply Subtype.ext
    exact o.eq_zero_of_mem_standardSpace_of_mem
      (restrictSupport_mono k (fun e (he : e ∈ S) => he.2) p.property) hz
  rw [← himage, ← LinearMap.range_domRestrict,
    ← (LinearEquiv.ofInjective g hg).finrank_eq,
    Module.finrank_eq_nat_card_basis (basisRestrictSupport k S), Nat.card_coe_set_eq]
end Coefficients
private theorem range_slot_coeff (B : Boxes) (P : Ideal GeoJets5) (u : Fin 5 → ℕ) :
    LinearMap.range (coefficientMap (slotMap B P) (Finsupp.equivFunOnFinite.symm u)) =
      slotPiece B P u := by
  classical
  let t : Exponent := Finsupp.equivFunOnFinite.symm u
  let f := slotMap B P
  let a := fun e => Ideal.Quotient.mk P (monomial (affineExponent B e) 1)
  let L := coefficientMap f t
  change LinearMap.range L = _
  have hmap :
      (restrictSupport GeoField {e | tagExponent B e = t}).map L = LinearMap.range L := by
    simpa only [Set.mem_univ, and_true, restrictSupport_univ, Submodule.map_top] using
      map_support_matching_tag f (tagExponent B) a (slotMap_monomial B P) t Set.univ
  have hL (e : SlotVars B →₀ ℕ) (he : tagExponent B e = t) :
      L (monomial e 1) = a e := by
    rw [show L = coefficientMap f t from rfl,
      coefficientMap_monomial f (tagExponent B) a (slotMap_monomial B P), ite_eq_left he]
  rw [← hmap, slotPiece, restrictSupport_eq_span, restrictSupport_eq_span,
    Submodule.map_span, Submodule.map_span]
  congr 1
  rw [Set.image_image, Set.image_image, diagonal_eq_image B u, Set.image_image]
  exact Set.image_congr hL
private def finiteOrder (σ : Type) [Finite σ] : MonomialOrder.{0, 0} σ := by
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact MonomialOrder.degLex
theorem proof : K1_13_6_2_4_2_2.c1 := by
  classical
  intro B P
  let o := finiteOrder (SlotVars B)
  refine ⟨o, fun u => ?_⟩
  rw [← range_slot_coeff]
  rw [finrank_coefficient_range (slotMap B P) (tagExponent B)
    (fun e => Ideal.Quotient.mk P (monomial (affineExponent B e) 1)) (slotMap_monomial B P) o]
  simp only [tagExponent_eq_iff]
end
end K1_13_6_2_4_2_2_1
end
section
namespace K1_13_7_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_7
open scoped BigOperators
def c4 : Prop :=
  ∀ f : Row 4, SmallFactor f → ∀ surface : Ideal GeoJets, surface.IsPrime → surface.height = 2 →
    toGeneric f ∈ surface → toGeneric (separant f) ∉ surface →
    Invariant f surface → toGeneric (membershipTest f) ∈ surface →
    ∀ S : (Polynomial Geom), surface ≤ markIdeal S → RegularAt f S → S.natDegree ≤ 133671 →
      IntegratedMark f S
private theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
theorem mem_markIdeal {P : Row 4} {S : (Polynomial Geom)} :
    toGeneric P ∈ markIdeal S ↔ atJet P S = 0 := by
  unfold markIdeal
  rw [RingHom.mem_ker]
  change MvPolynomial.eval _ (MvPolynomial.map genericCoeffs P) = 0 ↔ _
  rw [MvPolynomial.eval_map]
  change MvPolynomial.eval₂ genericCoeffs (⇑genericCoeffs ∘ jet S) P = 0 ↔ _
  rw [← MvPolynomial.eval₂_comp]
  exact map_eq_zero_iff _ genericCoeffs_injective
@[simp] theorem eval_liftLower (q : Row 3) (S : (Polynomial Geom)) :
    atJet (liftLower q) S = atJet q S := by
  rw [atJet, liftLower, MvPolynomial.eval_rename]
  rfl
theorem eval_lowerFlow {q : Row 3} {f : Row 4} {S : (Polynomial Geom)}
    (hf : atJet f S = 0) (hreg : RegularAt f S) (hq : atJet q S = 0) :
    atJet (lowerFlow q) S = 0 := by
  have htop : separant (liftLower q) = 0 := by
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hv
    obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename Fin.castSucc q hv
    exact Fin.castSucc_ne_last i hi
  have h := eval_flowNumerator f (liftLower q) S hf
  rw [eval_liftLower, hq, map_zero, mul_zero] at h
  simp only [flowNumerator, htop, mul_zero, sub_zero] at h
  change MvPolynomial.eval (jet S) (_ * _) = 0 at h
  rw [map_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hreg
theorem evalTrajectory_geom (P : Row 4) (S : (Polynomial Geom)) :
    evalTrajectory P S = atJet P S := by
  have he : Polynomial.mapRingHom (algebraMap Geom Geom) = RingHom.id (Polynomial Geom) := by
    apply RingHom.ext
    intro p
    change p.map (algebraMap Geom Geom) = p
    simp
  unfold evalTrajectory atJet
  rw [he, MvPolynomial.eval₂_id]
  rfl
theorem lifted_at_mark {f : Row 4} {q : Row 3} {S : (Polynomial Geom)}
    (hf : OnFactor f S) (hr : RegularAt f S) (hq : atJet q S = 0) :
    ∃ surface, LiftedSurface f q surface ∧ surface ≤ markIdeal S := by
  have hl : intersectionIdeal f (liftLower q) ≤ markIdeal S := by
    apply Ideal.span_le.mpr
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl
    · exact mem_markIdeal.mpr hf.1
    · exact mem_markIdeal.mpr ((eval_liftLower q S).trans hq)
  have : (markIdeal S).IsPrime := RingHom.ker_isPrime (evalGeneric S)
  obtain ⟨surface, hZ, hle⟩ := Ideal.exists_minimalPrimes_le hl
  refine ⟨surface, ⟨hZ, ?_, ?_⟩, hle⟩
  · intro hz
    have h := mem_markIdeal.mp (hle hz)
    rw [eval_liftLower, K1_13_1.eval_anchorLead] at h
    exact hf.2 h
  · exact fun hz => hr (mem_markIdeal.mp (hle hz))
end
end K1_13_7_2
end
section
namespace K1_13_7_2_3
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_1 K1_13_7 K1_13_7_1 K1_13_7_2
open scoped BigOperators
def c1 : Prop :=
  ∀ (p q r h : Shape), Chamber p → Chamber q → Chamber r → Chamber h → 0 < h.t →
    ∀ F Q : GeoJets, IsRelPrime F Q → GeoFits F p → GeoFits Q q →
      ∀ (cut : Ideal GeoJets → GeoJets) (curves : Finset (Ideal GeoJets)),
        (∀ C ∈ curves, ∃ surface, (Ideal.span {F, Q}).IsMinimalPrime surface ∧
          ProperComponent surface (cut surface) C ∧ GeoFits (cut surface) r) →
        32 * (∑ C ∈ curves, sectionDegree C (h.scale 6)) ≤ 6 * mixed32 p q r h
def c2 : Prop :=
  ∀ a : Shape, Chamber a → 0 < a.t →
    ∀ (surface : Ideal GeoJets) (P : GeoJets) (C : Ideal GeoJets),
      ProperComponent surface P C →
      6 ≤ sectionDegree C (a.scale 6) ∧
      ∀ (U : GeoJets) (points : Finset GeoPoint), GeoFits U a → U ∉ C →
        (∀ y ∈ points, C ≤ RingHom.ker (MvPolynomial.eval y) ∧ MvPolynomial.eval y U = 0) →
        6 * points.card ≤ sectionDegree C (a.scale 6)
end
end K1_13_7_2_3
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_2 K1_13_6_2_3 K1_13_7_1 K1_13_7_2_3
open scoped BigOperators
def c1 : Prop :=
  ∀ (J : Ideal GeoJets) (p : Shape) (boxes : List Shape),
    Chamber p → (∀ q ∈ boxes, Chamber q) → boxes.length ≤ 3 →
    dimension J ≤ boxes.length + 1 →
    ∀ D : GeoJets, Box4 p D → IsLeftRegular (Ideal.Quotient.mk J D) →
      mixedDegree (J ⊔ Ideal.span {D}) boxes ≤ mixedDegree J (p :: boxes)
def c2 : Prop :=
  ∀ (J : Ideal GeoJets) (boxes : List Shape),
    (∀ q ∈ boxes, Chamber q) → boxes.length ≤ 2 → dimension J ≤ boxes.length →
    ∀ S : Finset (Ideal GeoJets), (∀ P ∈ S, J.IsMinimalPrime P) →
      (∑ P ∈ S, mixedDegree P boxes) ≤ mixedDegree J boxes
def c3 : Prop :=
  ∀ (C : Ideal GeoJets) (h : Shape), C.IsPrime → dimension C = 1 →
    Chamber h → 0 < h.t →
    (sectionDegree C (h.scale 6) : ℚ) ≤ 6 * mixedDegree C [h]
private theorem chamberBox_plus {p q : Shape} (hp : ChamberBox p) (hq : Chamber q) :
    ChamberBox (p.plus q) := by
  obtain ⟨hb, hj, ht⟩ := hp
  obtain ⟨hb', hj'⟩ := hq
  exact ⟨Nat.add_le_add hb hb', by dsimp [Shape.plus]; omega, by dsimp [Shape.plus]; omega⟩
private theorem polarize_chamber_congr {A B : Shape → ℚ}
    (h : ∀ p, ChamberBox p → A p = B p) {boxes : List Shape}
    (hboxes : ∀ q ∈ boxes, Chamber q) {p : Shape} (hp : ChamberBox p) :
    polarize A boxes p = polarize B boxes p := by
  induction boxes generalizing p with
  | nil => exact h p hp
  | cons q boxes ih =>
    have hq := hboxes q List.mem_cons_self
    have hr := fun r hr => hboxes r (List.mem_cons_of_mem _ hr)
    simp only [polarize, ih hr (chamberBox_plus hp hq), ih hr hp]
private theorem ambient_bound {p q r h : Shape}
    (hboxes : ∀ u ∈ [p,q,r,h], Chamber u) :
    mixedDegree (⊥ : Ideal GeoJets) [p,q,r,h] ≤ (mixed32 p q r h : ℚ) / 32 := by
  have hb : ChamberBox ⟨3, 3, 1⟩ := ⟨by decide, by decide, by decide⟩
  unfold mixedDegree
  change polarize (capCoeff ⊥ 4) [p,q,r,h] ⟨3,3,1⟩ / (2 : ℚ)^4 ≤ _
  rw [polarize_chamber_congr K1_13_6_2_3_1.proof hboxes hb]
  let n := difference (difference (difference (difference volume32 p) q) r) h ⟨0,0,0⟩
  have hpoly : polarize (fun x => 16 * (volume32 x : ℚ) / 32) [p,q,r,h] ⟨3,3,1⟩ /
      (2 : ℚ)^4 = (n : ℚ) / 32 := by
    simp only [n, polarize, difference, volume32, Shape.plus]
    push_cast
    ring
  rw [hpoly]
  have hn : n ≤ (n.toNat : ℤ) := by omega
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast hn
private theorem pair_span (F Q : GeoJets) :
    (Ideal.span {F, Q} : Ideal GeoJets) = Ideal.span {F} ⊔ Ideal.span {Q} := by
  rw [← Ideal.span_union]
  rfl
private theorem relative_regular {F Q : GeoJets} (h : IsRelPrime F Q) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {F}) Q) := by
  apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
  intro x hx
  obtain ⟨D, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h.dvd_of_dvd_mul_left hx))
private theorem surface_dimension {F Q : GeoJets} (hF : F ≠ 0) (hrel : IsRelPrime F Q)
    {S : Ideal GeoJets} (hS : (Ideal.span {F, Q}).IsMinimalPrime S) : dimension S = 2 := by
  have := hS.isPrime
  rw [pair_span] at hS
  obtain ⟨P, hP, hPS⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hS.le)
  have := hP.isPrime
  have hdim := MvPolynomial.natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hP
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hdim
  have hPne : P ≠ ⊥ := by
    intro heq
    exact hF (Ideal.mem_bot.mp (heq ▸ hP.le (Ideal.mem_span_singleton_self F)))
  have hheight : P.height = 1 :=
    le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP) (by
      simpa [Ideal.height_bot] using Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hPne))
  obtain ⟨a, ha⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight).principal
  change P = Ideal.span {a} at ha
  have hQ : Q ∉ P := by
    intro hmem
    have haF : a ∣ F := Ideal.mem_span_singleton.mp (ha ▸ hP.le (Ideal.mem_span_singleton_self F))
    have haQ : a ∣ Q := Ideal.mem_span_singleton.mp (ha ▸ hmem)
    exact hP.isPrime.ne_top (ha.trans (Ideal.span_singleton_eq_top.mpr (hrel haF haQ)))
  have hmin : S ∈ (P ⊔ Ideal.span {Q}).minimalPrimes := by
    refine ⟨⟨hS.isPrime, sup_le hPS (le_sup_right.trans hS.le)⟩, fun U hU hUS => ?_⟩
    exact hS.2 ⟨hU.1, sup_le (hP.le.trans (le_sup_left.trans hU.2)) (le_sup_right.trans hU.2)⟩ hUS
  have h := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hQ hmin
  change dimension S + 1 = dimension P at h
  change dimension P + 1 = 4 at hdim
  omega
private theorem sum_on_surface (hcut : c1) (hcomp : c2) (hdeg : c3)
    {r h : Shape} (hr : Chamber r) (hh : Chamber h) (ht : 0 < h.t)
    {S : Ideal GeoJets} {D : GeoJets} (hD : GeoFits D r)
    (hS : dimension S = 2) (T : Finset (Ideal GeoJets)) (hn : T.Nonempty)
    (hT : ∀ C ∈ T, ProperComponent S D C) :
    (∑ C ∈ T, (sectionDegree C (h.scale 6) : ℚ) / 6) ≤ mixedDegree S [r,h] := by
  obtain ⟨C₀, hm⟩ := hn
  have base := hT C₀ hm
  have hreg := regular_cut base.prime base.proper
  have hJ : dimension (S ⊔ Ideal.span {D}) ≤ 1 := (cut_dimension hreg).trans (by omega)
  have hsingle : ∀ q ∈ [h], Chamber q := by simpa using hh
  calc
    _ ≤ ∑ C ∈ T, mixedDegree C [h] := by
      apply Finset.sum_le_sum
      intro C hc
      have info := hT C hc
      have := info.prime
      have hd := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one
        info.proper info.component
      change dimension C + 1 = dimension S at hd
      have hC : dimension C = 1 := by omega
      apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 6)).mpr
      simpa only [mul_comm] using hdeg C h info.component.isPrime hC hh ht
    _ ≤ mixedDegree (S ⊔ Ideal.span {D}) [h] :=
      hcomp _ [h] hsingle (by simp) (by simpa using hJ) T (fun C hc => (hT C hc).component)
    _ ≤ mixedDegree S [r,h] :=
      hcut S r [h] hr hsingle (by simp) (by simpa using hS.le) D
        (K1_13_6_2_1.oldBox_of_fits hD) hreg
theorem of_children (hcut : c1) (hcomp : c2) (hdeg : c3) : K1_13_7_2_3.c1 := by
  classical
  intro p q r h hp hq hr hh ht F Q hrel hF hQ cut curves hcurves
  rcases curves.eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  let H := Ideal.span {F}
  let J := Ideal.span {F,Q}
  have hpair : J = H ⊔ Ideal.span {Q} := pair_span F Q
  have hF0 : F ≠ 0 := by
    intro hzero
    obtain ⟨C, hc⟩ := hne
    obtain ⟨S, hs, _⟩ := hcurves C hc
    have hu : IsUnit Q := hrel (hzero ▸ dvd_zero Q) dvd_rfl
    have hm : Q ∈ S := hs.le (Ideal.subset_span (by simp))
    exact hs.isPrime.ne_top (S.eq_top_of_isUnit_mem hm hu)
  have hregF : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets) F) :=
    regular_cut Ideal.isPrime_bot (by simpa using hF0)
  have hregQ : IsLeftRegular (Ideal.Quotient.mk H Q) := relative_regular hrel
  have hH : dimension H ≤ 3 := by
    simpa [H, dimension_bot] using cut_dimension hregF
  have hJ : dimension J ≤ 2 := by
    rw [hpair]
    exact (cut_dimension hregQ).trans (by omega)
  have hall : ∀ C : Ideal GeoJets, ∃ S : Ideal GeoJets, C ∈ curves →
      J.IsMinimalPrime S ∧ ProperComponent S (cut S) C ∧ GeoFits (cut S) r := by
    intro C
    by_cases hc : C ∈ curves
    · obtain ⟨S, hs⟩ := hcurves C hc
      exact ⟨S, fun _ => hs⟩
    · exact ⟨⊥, fun hm => (hc hm).elim⟩
  choose surface hsurface using hall
  let surfaces := curves.image surface
  let fibre (S : Ideal GeoJets) := curves.filter fun C => surface C = S
  let cost (C : Ideal GeoJets) := (sectionDegree C (h.scale 6) : ℚ) / 6
  have hs (S : Ideal GeoJets) (hm : S ∈ surfaces) :
      J.IsMinimalPrime S ∧ (∑ C ∈ fibre S, cost C) ≤ mixedDegree S [r,h] := by
    obtain ⟨C, hc, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hmin, _, hfit⟩ := hsurface C hc
    refine ⟨hmin, sum_on_surface hcut hcomp hdeg hr hh ht hfit
      (surface_dimension hF0 hrel hmin)
      _ ⟨C, Finset.mem_filter.mpr ⟨hc, rfl⟩⟩ ?_⟩
    intro C' hc'
    obtain ⟨hm', heq⟩ := Finset.mem_filter.mp hc'
    exact heq ▸ (hsurface C' hm').2.1
  have hrh : ∀ a ∈ [r,h], Chamber a := by simp [hr, hh]
  have hqrh : ∀ a ∈ [q,r,h], Chamber a := by simp [hq, hr, hh]
  have hpqrh : ∀ a ∈ [p,q,r,h], Chamber a := by simp [hp, hq, hr, hh]
  have hsum : (∑ C ∈ curves, cost C) ≤ (mixed32 p q r h : ℚ) / 32 := by
    calc
      _ = ∑ S ∈ surfaces, ∑ C ∈ fibre S, cost C :=
        (Finset.sum_fiberwise_of_maps_to (fun _ hc => Finset.mem_image_of_mem _ hc) cost).symm
      _ ≤ ∑ S ∈ surfaces, mixedDegree S [r,h] :=
        Finset.sum_le_sum fun S hm => (hs S hm).2
      _ ≤ mixedDegree J [r,h] :=
        hcomp J [r,h] hrh (by simp) (by simpa using hJ) surfaces (fun S hm => (hs S hm).1)
      _ ≤ mixedDegree H [q,r,h] := by
        rw [hpair]
        exact hcut H q [r,h] hq hrh (by simp) (by simpa using hH) Q
          (K1_13_6_2_1.oldBox_of_fits hQ) hregQ
      _ ≤ mixedDegree ⊥ [p,q,r,h] := by
        rw [show H = (⊥ : Ideal GeoJets) ⊔ Ideal.span {F} by simp [H]]
        exact hcut ⊥ p [q,r,h] hp hqrh (by simp) (by simp) F
          (K1_13_6_2_1.oldBox_of_fits hF) hregF
      _ ≤ _ := ambient_bound hpqrh
  dsimp only [cost] at hsum
  rw [← Finset.sum_div] at hsum
  have hfinal : (32 : ℚ) * (∑ C ∈ curves, (sectionDegree C (h.scale 6) : ℚ)) ≤
      6 * (mixed32 p q r h : ℚ) := by
    linarith [(div_le_div_iff₀ (by norm_num : (0 : ℚ) < 6)
      (by norm_num : (0 : ℚ) < 32)).mp hsum]
  exact_mod_cast hfinal
end
end K1_13_7_2_3_1
end
section
set_option maxHeartbeats 600000
namespace K1_13_7_2_4
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_3
def contraction (P : Ideal GeoJets) : Ideal (Row 4) :=
  P.comap (MvPolynomial.map genericCoeffs)
abbrev LocalRows (f : Row 4) := Localization.Away (separant f)
def localRowsMap (f : Row 4) : Row 4 →+* LocalRows f := algebraMap _ _
def localContraction (f : Row 4) (P : Ideal GeoJets) : Ideal (LocalRows f) :=
  (contraction P).map (localRowsMap f)
abbrev ChartRing (f : Row 4) (P : Ideal GeoJets) := LocalRows f ⧸ localContraction f P
def onChart (f : Row 4) (P : Ideal GeoJets) : Row 4 →+* ChartRing f P :=
  (Ideal.Quotient.mk (localContraction f P)).comp (localRowsMap f)
def inverseSeparant (f : Row 4) (P : Ideal GeoJets) : ChartRing f P :=
  Ideal.Quotient.mk (localContraction f P) (IsLocalization.Away.invSelf (separant f))
theorem separant_mul_inverse (f : Row 4) (P : Ideal GeoJets) :
    onChart f P (separant f) * inverseSeparant f P = 1 := by
  change Ideal.Quotient.mk (localContraction f P) (localRowsMap f (separant f)) *
    Ideal.Quotient.mk (localContraction f P) (IsLocalization.Away.invSelf (separant f)) = 1
  rw [← map_mul, show localRowsMap f (separant f) * IsLocalization.Away.invSelf (separant f) = 1
    from IsLocalization.Away.mul_invSelf (separant f), map_one]
def chartConstants (f : Row 4) (P : Ideal GeoJets) : Geom →+* ChartRing f P :=
  (onChart f P).comp (MvPolynomial.C.comp Polynomial.C)
instance chartAlgebra (f : Row 4) (P : Ideal GeoJets) : Algebra Geom (ChartRing f P) :=
  (chartConstants f P).toAlgebra
def chartCenter (f : Row 4) (P : Ideal GeoJets) : ChartRing f P :=
  onChart f P (MvPolynomial.C Polynomial.X)
def chartJet (f : Row 4) (P : Ideal GeoJets) (i : Fin taylorLength) : ChartRing f P :=
  if hi : i.val < 4 then onChart f P (MvPolynomial.X ⟨i.val, hi⟩)
  else chartConstants f P (↑i.val.factorial : Geom)⁻¹ *
    (inverseSeparant f P) ^ (2 * i.val) * onChart f P (jetNumerator f i.val)
def chartPolynomial (f : Row 4) (P : Ideal GeoJets) : (Polynomial (ChartRing f P)) :=
  taylor (-chartCenter f P) (∑ i : Fin taylorLength, monomial i.val (chartJet f P i))
def FollowsFlow (f : Row 4) (P : Ideal GeoJets)
    (δ : Derivation Geom (ChartRing f P) (ChartRing f P)) : Prop :=
  ∀ Q : Row 4, δ (onChart f P Q) = inverseSeparant f P * onChart f P (flowNumerator f Q)
private def liftLocalRows {R : Type} [CommRing R] {f : Row 4} (e : Row 4 →+* R)
    (hs : IsUnit (e (separant f))) : LocalRows f →+* R :=
  IsLocalization.Away.lift (separant f) hs
@[simp] private theorem liftLocalRows_apply {R : Type} [CommRing R] {f : Row 4}
    (e : Row 4 →+* R) (hs : IsUnit (e (separant f))) (Q : Row 4) :
    liftLocalRows e hs (localRowsMap f Q) = e Q :=
  IsLocalization.Away.lift_eq (separant f) hs Q
def chartLift {R : Type} [CommRing R] {f : Row 4} {P : Ideal GeoJets} (e : Row 4 →+* R)
    (he : ∀ Q ∈ contraction P, e Q = 0) (hs : IsUnit (e (separant f))) : ChartRing f P →+* R :=
  Ideal.Quotient.lift (localContraction f P) (liftLocalRows e hs) (by
    change (contraction P).map (localRowsMap f) ≤ RingHom.ker (liftLocalRows e hs)
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQ
    change liftLocalRows e hs (localRowsMap f Q) = 0
    rw [liftLocalRows_apply, he Q hQ])
@[simp] theorem chartLift_onChart {R : Type} [CommRing R] {f : Row 4} {P : Ideal GeoJets}
    (e : Row 4 →+* R) (he : ∀ Q ∈ contraction P, e Q = 0) (hs : IsUnit (e (separant f)))
    (Q : Row 4) : chartLift e he hs (onChart f P Q) = e Q := by
  change liftLocalRows e hs (localRowsMap f Q) = e Q
  exact liftLocalRows_apply e hs Q
private theorem chartLift_injective {R : Type} [CommRing R] {f : Row 4} {P : Ideal GeoJets}
    (e : Row 4 →+* R) (he : ∀ Q ∈ contraction P, e Q = 0) (hs : IsUnit (e (separant f)))
    (hker : RingHom.ker e ≤ contraction P) : Function.Injective (chartLift e he hs) := by
  unfold chartLift
  apply RingHom.lift_injective_of_ker_le_ideal
  intro a ha
  have ha0 : liftLocalRows e hs a = 0 := ha
  obtain ⟨n, Q, hQ⟩ := IsLocalization.Away.surj (separant f) a
  change a * localRowsMap f (separant f) ^ n = localRowsMap f Q at hQ
  have hQ0 := congrArg (liftLocalRows e hs) hQ
  rw [map_mul, ha0, zero_mul, liftLocalRows_apply] at hQ0
  have hmem : localRowsMap f Q ∈ localContraction f P :=
    Ideal.mem_map_of_mem _ (hker (RingHom.mem_ker.mpr hQ0.symm))
  have hunit : IsUnit (localRowsMap f (separant f) ^ n) :=
    IsLocalization.Away.algebraMap_pow_isUnit (separant f) n
  obtain ⟨u, hu⟩ := hunit
  rw [← hQ, ← hu] at hmem
  have h := (localContraction f P).mul_mem_left (↑u⁻¹ : LocalRows f) hmem
  simpa only [mul_comm a (↑u : LocalRows f), Units.inv_mul_cancel_left] using h
private def componentRows (P : Ideal GeoJets) : Row 4 →+* JetField P :=
  (onComponent P).comp (MvPolynomial.map genericCoeffs)
private theorem componentRows_zero {P : Ideal GeoJets} [P.IsPrime] {Q : Row 4} :
    componentRows P Q = 0 ↔ toGeneric Q ∈ P :=
  (map_eq_zero_iff _ (IsFractionRing.injective (GeoJets ⧸ P) (JetField P))).trans
    Ideal.Quotient.eq_zero_iff_mem
def genericLift (f : Row 4) (P : Ideal GeoJets) [P.IsPrime]
    (hs : toGeneric (separant f) ∉ P) : ChartRing f P →+* JetField P :=
  chartLift (componentRows P) (fun _ h => componentRows_zero.mpr h)
    (isUnit_iff_ne_zero.mpr fun h => hs (componentRows_zero.mp h))
@[simp] theorem genericLift_onChart (f : Row 4) (P : Ideal GeoJets) [P.IsPrime]
    (hs : toGeneric (separant f) ∉ P) (Q : Row 4) :
    genericLift f P hs (onChart f P Q) = onComponent P (toGeneric Q) :=
  chartLift_onChart _ _ _ _
theorem genericLift_injective (f : Row 4) (P : Ideal GeoJets) [P.IsPrime]
    (hs : toGeneric (separant f) ∉ P) : Function.Injective (genericLift f P hs) :=
  chartLift_injective _ _ _ (fun _ h => componentRows_zero.mp h)
end
end K1_13_7_2_4
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace K1_13_7_2_4
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_3 K1_13_7 K1_13_7_2
private theorem coeff_jetSum {R : Type} [CommRing R] {M : ℕ} (a : Fin M → R) (n : ℕ) :
    (∑ i : Fin M, monomial i.val (a i)).coeff n =
      if hn : n < M then a ⟨n, hn⟩ else 0 := by
  classical
  rw [Polynomial.finsetSum_coeff]
  split_ifs with hn
  · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin M)]
    · exact coeff_monomial_same _ _
    · intro i _ hi
      exact coeff_monomial_of_ne _ (fun he => hi (Fin.ext he.symm))
    · simp
  · exact Finset.sum_eq_zero fun i _ => coeff_monomial_of_ne _ (fun he => hn (he.symm ▸ i.isLt))
theorem sum_monomial_eq_of_coeffs {R : Type} [CommRing R] {M : ℕ}
    (a : Fin M → R) (U : (Polynomial R)) (hdegree : U.natDegree < M)
    (hcoeff : ∀ i, a i = U.coeff i.val) : (∑ i : Fin M, monomial i.val (a i)) = U := by
  ext n
  rw [coeff_jetSum]
  split_ifs with hn
  · exact hcoeff ⟨n, hn⟩
  · exact (coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (Nat.not_lt.mp hn))).symm
private theorem eval_hasse_of_taylor_eq_sum {R : Type} [CommRing R] {M : ℕ}
    {U : (Polynomial R)} {x : R} {a : Fin M → R}
    (h : taylor x U = ∑ i : Fin M, monomial i.val (a i)) (i : Fin M) :
    (hasseDeriv i.val U).eval x = a i := by
  rw [← taylor_coeff, h, coeff_jetSum, dite_eq_left i.isLt]
theorem mapped_chartPolynomial_degree {R : Type} [CommRing R] {f : Row 4} {P : Ideal GeoJets}
    (φ : ChartRing f P →+* R) : ((chartPolynomial f P).map φ).natDegree < taylorLength := by
  rw [chartPolynomial, Polynomial.map_taylor, natDegree_taylor, Polynomial.map_sum]
  simp only [map_monomial]
  apply Nat.lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := 133671) ?_)
    (by decide : 133671 < taylorLength)
  intro i _
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ i.isLt)
private theorem taylor_mapped_chartPolynomial {R : Type} [CommRing R]
    {f : Row 4} {P : Ideal GeoJets} (φ : ChartRing f P →+* R) :
    taylor (φ (chartCenter f P)) ((chartPolynomial f P).map φ) =
      ∑ i : Fin taylorLength, monomial i.val (φ (chartJet f P i)) := by
  rw [chartPolynomial, Polynomial.map_taylor, map_neg, taylor_taylor, add_neg_cancel, taylor_zero,
    Polynomial.map_sum]
  simp only [map_monomial]
theorem eval_hasse_chartPolynomial {R : Type} [CommRing R]
    {f : Row 4} {P : Ideal GeoJets} (φ : ChartRing f P →+* R) (i : Fin 4) :
    (hasseDeriv i.val ((chartPolynomial f P).map φ)).eval (φ (chartCenter f P)) =
      φ (onChart f P (MvPolynomial.X i)) := by
  let j : Fin taylorLength := ⟨i.val, i.isLt.trans (by decide : 4 < taylorLength)⟩
  calc
    _ = φ (chartJet f P j) := eval_hasse_of_taylor_eq_sum (taylor_mapped_chartPolynomial φ) j
    _ = _ := by
      rw [chartJet, dite_eq_left i.isLt]
private theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
private def markRows (S : (Polynomial Geom)) : Row 4 →+* GeoField :=
  genericCoeffs.comp (MvPolynomial.eval (jet S))
private theorem markRows_separant_ne {f : Row 4} {S : (Polynomial Geom)} (hr : RegularAt f S) :
    markRows S (separant f) ≠ 0 := (map_ne_zero_iff _ genericCoeffs_injective).mpr hr
private def markLift {f : Row 4} {P : Ideal GeoJets} {S : (Polynomial Geom)}
    (hP : P ≤ markIdeal S) (hr : RegularAt f S) : ChartRing f P →+* GeoField :=
  chartLift (markRows S) (fun Q hQ => by
    change genericCoeffs (atJet Q S) = 0
    rw [mem_markIdeal.mp (hP hQ), map_zero]) (markRows_separant_ne hr).isUnit
private theorem markLift_row {f : Row 4} {P : Ideal GeoJets} {S : (Polynomial Geom)}
    (hP : P ≤ markIdeal S) (hr : RegularAt f S) (Q : Row 4) :
    markLift hP hr (onChart f P Q) = genericCoeffs (atJet Q S) :=
  chartLift_onChart _ _ _ _
private theorem markLift_inverse {f : Row 4} {P : Ideal GeoJets} {S : (Polynomial Geom)}
    (hP : P ≤ markIdeal S) (hr : RegularAt f S) :
    markLift hP hr (inverseSeparant f P) = (genericCoeffs (atJet (separant f) S))⁻¹ := by
  have hmul : onChart f P (separant f) * inverseSeparant f P = 1 :=
    separant_mul_inverse f P
  have hm := congrArg (markLift hP hr) hmul
  rw [map_mul, markLift_row, map_one] at hm
  exact ((mul_eq_one_iff_inv_eq₀ (markRows_separant_ne hr)).mp hm).symm
private theorem markLift_constants {f : Row 4} {P : Ideal GeoJets} {S : (Polynomial Geom)}
    (hP : P ≤ markIdeal S) (hr : RegularAt f S) (a : Geom) :
    markLift hP hr (chartConstants f P a) = geomConstants a := by
  simp [chartConstants, markLift_row, atJet, geomConstants]
private theorem markLift_jet {f : Row 4} {P : Ideal GeoJets} {S : (Polynomial Geom)}
    (hP : P ≤ markIdeal S) (hr : RegularAt f S) (hf : atJet f S = 0) (i : Fin taylorLength) :
    markLift hP hr (chartJet f P i) = genericCoeffs (hasseDeriv i.val S) := by
  unfold chartJet
  split_ifs with hi
  · rw [markLift_row]
    simp [atJet, jet]
  · have ho : derivative^[i.val] S = C (↑i.val.factorial : Geom) * hasseDeriv i.val S := by
      have h := congrFun (factorial_smul_hasseDeriv (R := Geom) (k := i.val)) S
      change i.val.factorial • (hasseDeriv i.val S) = derivative^[i.val] S at h
      simpa only [nsmul_eq_mul, C_eq_natCast] using h.symm
    have hs := markRows_separant_ne hr
    have hfact : (i.val.factorial : Geom) ≠ 0 :=
      K1_13_7_1.factorial_cast_ne_zero (i.isLt.trans (by decide : taylorLength < K1.p))
    simp only [map_mul, map_pow, markLift_constants, markLift_inverse, markLift_row,
      eval_jetNumerator _ _ hf, ho]
    change geomConstants (↑i.val.factorial : Geom)⁻¹ * (markRows S (separant f))⁻¹ ^ (2 * i.val) *
      ((markRows S (separant f)) ^ (2 * i.val) *
        (geomConstants (↑i.val.factorial : Geom) * genericCoeffs (hasseDeriv i.val S))) = _
    rw [← mul_assoc, mul_assoc (geomConstants _), ← mul_pow, inv_mul_cancel₀ hs, one_pow,
      mul_one, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hfact, map_one, one_mul]
private theorem markLift_center {f : Row 4} {P : Ideal GeoJets} {S : (Polynomial Geom)}
    (hP : P ≤ markIdeal S) (hr : RegularAt f S) :
    markLift hP hr (chartCenter f P) = genericArgument := by
  simp [chartCenter, markLift_row, atJet, genericArgument]
private theorem markLift_polynomial {f : Row 4} {P : Ideal GeoJets} {S : (Polynomial Geom)}
    (hP : P ≤ markIdeal S) (hr : RegularAt f S) (hf : atJet f S = 0)
    (hd : S.natDegree ≤ 133671) :
    (chartPolynomial f P).map (markLift hP hr) = S.map geomConstants := by
  apply taylor_injective genericArgument
  rw [← markLift_center hP hr, taylor_mapped_chartPolynomial, markLift_center hP hr]
  apply sum_monomial_eq_of_coeffs
  · rw [natDegree_taylor]
    exact natDegree_map_le.trans_lt (hd.trans_lt (by decide : 133671 < taylorLength))
  · intro i
    rw [markLift_jet hP hr hf, taylor_coeff, hasseDeriv_map]
    change genericCoeffs (hasseDeriv i.val S) = (evalRingHom genericArgument)
      (mapRingHom geomConstants (hasseDeriv i.val S))
    have hc : (evalRingHom genericArgument).comp (mapRingHom geomConstants) = genericCoeffs := by
      apply Polynomial.ringHom_ext <;> simp [geomConstants, genericArgument]
    exact (RingHom.congr_fun hc _).symm
private theorem comp_eval_coeffs {R : Type} [CommRing R] {T : Type} [CommRing T]
    (h : R →+* T) (a : Geom →+* R) (U : (Polynomial R)) :
    h.comp (MvPolynomial.eval₂Hom a (fun i : Fin taylorLength => U.coeff i.val)) =
      MvPolynomial.eval₂Hom (h.comp a) (fun i : Fin taylorLength => (U.map h).coeff i.val) := by
  rw [MvPolynomial.comp_eval₂Hom]
  simp only [coeff_map]
theorem specializes {f : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    (hs : toGeneric (separant f) ∉ P) {S : (Polynomial Geom)} (hP : P ≤ markIdeal S)
    (hr : RegularAt f S) (hf : atJet f S = 0) (hd : S.natDegree ≤ 133671) :
    coefficientKernel (componentConstants P) ((chartPolynomial f P).map (genericLift f P hs)) ≤
      coefficientPointIdeal S := by
  let e := MvPolynomial.eval₂Hom (chartConstants f P)
    (fun i : Fin taylorLength => (chartPolynomial f P).coeff i.val)
  have hgen : (genericLift f P hs).comp (chartConstants f P) = componentConstants P := by
    ext a
    change genericLift f P hs (onChart f P (MvPolynomial.C (C a))) = _
    rw [genericLift_onChart]
    simp [componentConstants, geomConstants, toGeneric]
  have hmark : (markLift hP hr).comp (chartConstants f P) = geomConstants :=
    RingHom.ext (markLift_constants hP hr)
  have hm := comp_eval_coeffs (markLift hP hr) (chartConstants f P) (chartPolynomial f P)
  rw [hmark, markLift_polynomial hP hr hf hd] at hm
  have hm' : (markLift hP hr).comp e = (geomConstants.comp (MvPolynomial.eval
      (fun i : Fin taylorLength => S.coeff i.val))) := by
    rw [hm, MvPolynomial.eval, MvPolynomial.comp_eval₂Hom]
    simp only [RingHom.comp_id, coeff_map]
  have hg := comp_eval_coeffs (genericLift f P hs) (chartConstants f P) (chartPolynomial f P)
  rw [hgen] at hg
  intro Q hQ
  have haux : genericLift f P hs (e Q) = 0 := by
    change ((genericLift f P hs).comp e) Q = 0
    rw [hg]
    unfold coefficientKernel at hQ
    have hQ' := RingHom.mem_ker.mp hQ
    convert hQ' using 2
  have he0 : e Q = 0 := by
    apply genericLift_injective f P hs
    simpa only [map_zero] using haux
  have hzero : (markLift hP hr).comp e Q = 0 := by simp [he0]
  rw [hm'] at hzero
  change MvPolynomial.eval (fun i : Fin taylorLength => S.coeff i.val) Q = 0
  exact (map_eq_zero_iff _ geomConstants.injective).mp hzero
end
end K1_13_7_2_4
end
section
namespace K1_13_7_2_1
noncomputable section
open K1_13 K1_13_1 K1_13_6 K1_13_7 K1_13_7_2 K1_13_7_1 MvPolynomial
@[simp] private theorem coeff_coefficientDerivative (P : Row 4) (m : Fin 4 →₀ ℕ) :
    (coefficientDerivative P).coeff m = Polynomial.derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coefficientDerivative_add (P Q : Row 4) :
    coefficientDerivative (P + Q) = coefficientDerivative P + coefficientDerivative Q := by
  ext m
  simp
private theorem coefficientDerivative_mul (P Q : Row 4) :
    coefficientDerivative (P * Q) = P * coefficientDerivative Q + Q * coefficientDerivative P := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [mul_comm Q, coeff_coefficientDerivative, coeff_mul]
  change _ = lcoeff (Polynomial Geom) m (_ + _)
  rw [map_add]
  simp only [lcoeff_apply, coeff_mul, map_sum, Polynomial.derivative_mul,
    coeff_coefficientDerivative, Finset.sum_add_distrib]
  exact add_comm _ _
private theorem partialFlow_add (P Q : Row 4) :
    partialFlow (P + Q) = partialFlow P + partialFlow Q := by
  simp only [partialFlow, coefficientDerivative_add, map_add, mul_add, Finset.sum_add_distrib]
  abel
private theorem partialFlow_mul (P Q : Row 4) :
    partialFlow (P * Q) = P * partialFlow Q + Q * partialFlow P := by
  let c (i : Fin 3) : Row 4 :=
    MvPolynomial.C (Polynomial.C ((i.val + 1 : ℕ) : Geom)) * MvPolynomial.X i.succ
  have hs : (∑ i : Fin 3, c i * pderiv i.castSucc (P * Q)) =
      P * (∑ i : Fin 3, c i * pderiv i.castSucc Q) +
        Q * (∑ i : Fin 3, c i * pderiv i.castSucc P) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pderiv_mul]
    ring
  unfold partialFlow
  rw [coefficientDerivative_mul, hs, mul_add, mul_add]
  exact add_add_add_comm _ _ _ _
theorem flow_add (f P Q : Row 4) :
    flowNumerator f (P + Q) = flowNumerator f P + flowNumerator f Q := by
  simp only [flowNumerator, partialFlow_add, separant, map_add, mul_add]
  ring
theorem flow_mul (f P Q : Row 4) :
    flowNumerator f (P * Q) = P * flowNumerator f Q + Q * flowNumerator f P := by
  simp only [flowNumerator, partialFlow_mul, separant, pderiv_mul]
  ring
@[simp] theorem flow_self (f : Row 4) : flowNumerator f f = 0 := by
  simp only [flowNumerator, mul_comm (separant f), sub_self]
@[simp] theorem separant_liftLower (q : Row 3) : separant (liftLower q) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename Fin.castSucc q hv
  exact Fin.castSucc_ne_last i hi
private theorem coeffDerivative_weight (w : Fin 4 → ℕ) (P : Row 4) :
    (coefficientDerivative P).weightedTotalDegree w ≤ P.weightedTotalDegree w := by
  apply weight_le_of_support_subset
  intro m hm
  contrapose! hm
  simp [MvPolynomial.notMem_support_iff.mp hm]
theorem partialFlow_weight (w : Fin 4 → ℕ) (d Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    (hw : ∀ i : Fin 3, w i.castSucc ≤ d) (P : Row 4)
    (hP : P.weightedTotalDegree w ≤ d) : (partialFlow P).weightedTotalDegree w ≤ d + Δ := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  unfold partialFlow
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((coeffDerivative_weight w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    apply (weight_const_mul_le w _ _).trans
    have hp := (weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
      (Nat.sub_le_sub_right hP (w i.castSucc))
    have he := hshift i
    have hi := hw i
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add (weight_X_le w _) hp).trans (by omega))
theorem degreeOf_liftLower (q : Row 3) : (liftLower q).degreeOf 3 = 0 := by
  rw [← weightedTotalDegree_piSingle, liftLower,
    weightedTotalDegree_rename_of_injective (Fin.castSucc_injective 3)]
  have hw : (Pi.single (3 : Fin 4) 1 : Fin 4 → ℕ) ∘ Fin.castSucc = (0 : Fin 3 → ℕ) := by
    funext i
    have hi : i.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last i
    simp [hi]
  rw [hw]
  simp [weightedTotalDegree, Finsupp.weight_apply]
end
end K1_13_7_2_1
end
section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace K1_13_7_2_4
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_3 K1_13_7_2
def c1 : Prop :=
  ∀ (f : Row 4) (P : Ideal GeoJets), P.IsPrime →
    toGeneric (separant f) ∉ P → Invariant f P →
    ∃ δ : Derivation Geom (ChartRing f P) (ChartRing f P), FollowsFlow f P δ
def c2 : Prop :=
  ∀ (f : Row 4) (P : Ideal GeoJets) (hp : P.IsPrime)
    (hs : toGeneric (separant f) ∉ P),
    TrueWeightLE f (90 * 180265 - 1) → toGeneric f ∈ P →
    toGeneric (membershipTest f) ∈ P →
    ∀ δ : Derivation Geom (ChartRing f P) (ChartRing f P),
      FollowsFlow f P δ →
      trajectory (componentConstants P) f
        ((chartPolynomial f P).map (@genericLift f P hp hs)) = 0
def c3 : Prop :=
  ∀ (P : Ideal GeoJets) (_hp : P.IsPrime) (U : (Polynomial (JetField P))),
    P.height = 2 → U.natDegree < taylorLength →
    (∀ i : Fin 4, (hasseDeriv i.val U).eval (onComponent P (MvPolynomial.C genericArgument)) =
      onComponent P (MvPolynomial.X i)) →
    2 ≤ (MvPolynomial.affineHilbertPolynomial (coefficientKernel (componentConstants P) U)).natDegree
theorem trajectory_at_component (P : Ideal GeoJets) [P.IsPrime]
    (U : (Polynomial (JetField P))) (Q : Row 4)
    (hU : ∀ i : Fin 4, (hasseDeriv i.val U).eval (onComponent P (MvPolynomial.C genericArgument)) =
      onComponent P (MvPolynomial.X i)) :
    (trajectory (componentConstants P) Q U).eval (onComponent P (MvPolynomial.C genericArgument)) =
      onComponent P (toGeneric Q) := by
  let x := onComponent P (MvPolynomial.C genericArgument)
  let e := (evalRingHom x).comp (mapRingHom (componentConstants P))
  have he : e = (onComponent P).comp (MvPolynomial.C.comp genericCoeffs) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [e, componentConstants, geomConstants]
    · simp [e, x, genericArgument]
  change (evalRingHom x) (MvPolynomial.eval₂ (mapRingHom (componentConstants P))
    (fun i : Fin 4 => hasseDeriv i.val U) Q) = _
  rw [MvPolynomial.hom_eval₂]
  have h : MvPolynomial.eval₂Hom e (fun i => (evalRingHom x) (hasseDeriv i.val U)) =
      (onComponent P).comp (MvPolynomial.map genericCoeffs) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C] using
        RingHom.congr_fun he c
    · intro i
      simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
        coe_evalRingHom, x] using hU i
  exact RingHom.congr_fun h Q
theorem component_ne_zero {P : Ideal GeoJets} [P.IsPrime] {Q : GeoJets}
    (h : Q ∉ P) : onComponent P Q ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (GeoJets ⧸ P) (JetField P))).mpr
    (fun he => h (Ideal.Quotient.eq_zero_iff_mem.mp he))
end
end K1_13_7_2_4
end
section
set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 800000
namespace K1_13_7_2_4_1
noncomputable section
open K1_13 K1_13_6 K1_13_7_2_4 K1_13_7_2_1
private theorem flow_constant (f : Row 4) (a : Geom) :
    flowNumerator f (MvPolynomial.C (Polynomial.C a)) = 0 := by
  have h : coefficientDerivative (MvPolynomial.C (Polynomial.C a)) = 0 := by
    classical
    rw [coefficientDerivative]
    apply Finset.sum_eq_zero
    intro m _
    rw [MvPolynomial.coeff_C]
    split <;> simp
  simp [flowNumerator, partialFlow, separant, h]
private def rowDual (f : Row 4) (P : Ideal GeoJets) : Row 4 →+* DualNumber (ChartRing f P) where
  toFun Q := (onChart f P Q, inverseSeparant f P * onChart f P (flowNumerator f Q))
  map_zero' := by
    apply TrivSqZeroExt.ext
    · exact map_zero (onChart f P)
    · have h : flowNumerator f 0 = 0 := by
        simpa only [map_zero] using flow_constant f 0
      change inverseSeparant f P * onChart f P (flowNumerator f 0) = 0
      rw [h, map_zero, mul_zero]
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one (onChart f P)
    · have h : flowNumerator f 1 = 0 := by
        simpa only [map_one] using flow_constant f 1
      change inverseSeparant f P * onChart f P (flowNumerator f 1) = 0
      rw [h, map_zero, mul_zero]
  map_add' Q R := by
    apply TrivSqZeroExt.ext
    · exact map_add (onChart f P) Q R
    · change inverseSeparant f P * onChart f P (flowNumerator f (Q + R)) =
        inverseSeparant f P * onChart f P (flowNumerator f Q) +
          inverseSeparant f P * onChart f P (flowNumerator f R)
      rw [flow_add, map_add, mul_add]
  map_mul' Q R := by
    apply TrivSqZeroExt.ext
    · exact map_mul (onChart f P) Q R
    · change inverseSeparant f P * onChart f P (flowNumerator f (Q * R)) =
        onChart f P Q * (inverseSeparant f P * onChart f P (flowNumerator f R)) +
          (inverseSeparant f P * onChart f P (flowNumerator f Q)) * onChart f P R
      simp only [flow_mul, map_add, map_mul]
      ring
private theorem onChart_eq_zero {f : Row 4} {P : Ideal GeoJets} {Q : Row 4}
    (h : Q ∈ contraction P) : onChart f P Q = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem (localRowsMap f) h)
theorem proof : K1_13_7_2_4.c1 := by
  intro f P _hp _hs hinv
  let _ : CommRing (DualNumber (ChartRing f P)) := inferInstance
  have hzero (Q : Row 4) (hQ : Q ∈ contraction P) : rowDual f P Q = 0 := by
    apply TrivSqZeroExt.ext
    · exact onChart_eq_zero hQ
    · change inverseSeparant f P * onChart f P (flowNumerator f Q) = 0
      rw [onChart_eq_zero (hinv Q hQ), mul_zero]
  have hunit : IsUnit (rowDual f P (separant f)) := by
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    change IsUnit (onChart f P (separant f))
    exact isUnit_iff_exists_inv.mpr ⟨inverseSeparant f P, separant_mul_inverse f P⟩
  let e : ChartRing f P →+* DualNumber (ChartRing f P) :=
    chartLift (f := f) (P := P) (rowDual f P) hzero hunit
  have he (Q : Row 4) : e (onChart f P Q) = rowDual f P Q :=
    chartLift_onChart _ _ _ Q
  have hefst (a : ChartRing f P) : (e a).fst = a := by
    have h : (TrivSqZeroExt.fstHom (ChartRing f P) (ChartRing f P)
        (ChartRing f P)).toRingHom.comp e = RingHom.id (ChartRing f P) := by
      apply Ideal.Quotient.ringHom_ext
      apply IsLocalization.ringHom_ext (Submonoid.powers (separant f))
      apply RingHom.ext
      intro Q
      change (e (onChart f P Q)).fst = onChart f P Q
      exact congrArg TrivSqZeroExt.fst (he Q)
    exact RingHom.congr_fun h a
  have hsnd_mul (a b : ChartRing f P) :
      (e (a * b)).snd = a * (e b).snd + (e a).snd * b := by
    rw [map_mul]
    change (e a).fst * (e b).snd + (e a).snd * (e b).fst = _
    simp only [hefst]
  have hconst (a : Geom) : (e (algebraMap Geom (ChartRing f P) a)).snd = 0 := by
    change (e (onChart f P (MvPolynomial.C (Polynomial.C a)))).snd = 0
    rw [he]
    change inverseSeparant f P * onChart f P (flowNumerator f (MvPolynomial.C (Polynomial.C a))) = 0
    rw [flow_constant, map_zero, mul_zero]
  have hsmul (a : Geom) (b : ChartRing f P) :
      a • b = algebraMap Geom (ChartRing f P) a * b :=
    @Algebra.smul_def Geom (ChartRing f P) _ _
      (Ideal.Quotient.algebra Geom (I := localContraction f P)) a b
  have hadd (a b : ChartRing f P) : (e (a + b)).snd = (e a).snd + (e b).snd := by
    rw [map_add] <;> rfl
  have hlinear (a : Geom) (b : ChartRing f P) :
      (e (algebraMap Geom (ChartRing f P) a * b)).snd = a • (e b).snd := by
    rw [hsnd_mul, hconst, zero_mul, add_zero, hsmul]
  let D := @LinearMap.mk Geom Geom _ _ (RingHom.id Geom) (ChartRing f P) (ChartRing f P) _ _
    (@Algebra.toModule Geom (ChartRing f P) _ _ (chartAlgebra f P))
    (Submodule.Quotient.module' (localContraction f P))
    ⟨fun a => (e a).snd, hadd⟩ hlinear
  refine ⟨Derivation.mk' D ?_, ?_⟩
  · intro a b
    change (e (a * b)).snd = a * (e b).snd + b * (e a).snd
    rw [hsnd_mul, mul_comm b]
  · intro Q
    change (e (onChart f P Q)).snd = _
    exact congrArg TrivSqZeroExt.snd (he Q)
end
end K1_13_7_2_4_1
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace K1_13_7_2_4_2
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_7_2_4
theorem onChart_zero {f : Row 4} {P : Ideal GeoJets} {Q : Row 4}
    (hQ : toGeneric Q ∈ P) : onChart f P Q = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hQ)
private theorem coefficientDerivative_C (c : (Polynomial Geom)) :
    coefficientDerivative (MvPolynomial.C c) = MvPolynomial.C (derivative c) := by
  classical
  ext m
  rw [coefficientDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', MvPolynomial.coeff_C]
  split_ifs <;> simp_all [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C]
private theorem coefficientDerivative_X (i : Fin 4) :
    coefficientDerivative (MvPolynomial.X i) = 0 := by
  classical
  simp [coefficientDerivative, MvPolynomial.support_X]
private theorem derivation_of_partial {f : Row 4} {P : Ideal GeoJets}
    {δ : Derivation Geom (ChartRing f P) (ChartRing f P)} (hδ : FollowsFlow f P δ)
    {Q : Row 4} (hQ : separant Q = 0) :
    δ (onChart f P Q) = onChart f P (partialFlow Q) := by
  rw [hδ, flowNumerator, hQ, mul_zero, sub_zero, map_mul, ← mul_assoc,
    mul_comm (inverseSeparant f P), separant_mul_inverse, one_mul]
theorem chartCenter_deriv {f : Row 4} {P : Ideal GeoJets}
    {δ : Derivation Geom (ChartRing f P) (ChartRing f P)} (hδ : FollowsFlow f P δ) :
    δ (chartCenter f P) = 1 := by
  rw [chartCenter, derivation_of_partial hδ (by simp [separant])]
  simp [partialFlow, coefficientDerivative_C]
theorem chartConstants_deriv {f : Row 4} {P : Ideal GeoJets}
    {δ : Derivation Geom (ChartRing f P) (ChartRing f P)} (hδ : FollowsFlow f P δ) (a : Geom) :
    δ (chartConstants f P a) = 0 := by
  change δ (onChart f P (MvPolynomial.C (C a))) = 0
  rw [derivation_of_partial hδ (by simp [separant])]
  simp [partialFlow, coefficientDerivative_C]
private theorem chart_shift {f : Row 4} {P : Ideal GeoJets}
    {δ : Derivation Geom (ChartRing f P) (ChartRing f P)} (hδ : FollowsFlow f P δ)
    (i : Fin 3) :
    δ (onChart f P (MvPolynomial.X i.castSucc)) =
      (↑(i.val + 1) : ChartRing f P) * onChart f P (MvPolynomial.X i.succ) := by
  have hc (a : ℕ) : MvPolynomial.C (C (a : Geom)) = (a : Row 4) := by simp
  rw [derivation_of_partial hδ (by
    rw [separant, show (3 : Fin 4) = Fin.last 3 by decide]
    exact MvPolynomial.pderiv_X_of_ne (Fin.castSucc_ne_last i))]
  fin_cases i <;>
    norm_num [partialFlow, coefficientDerivative_X, Fin.sum_univ_three, MvPolynomial.pderiv_X,
      Pi.single_apply, Fin.castSucc, Fin.succ, hc] <;> rw [map_ofNat]
private theorem flow_image {f : Row 4} {P : Ideal GeoJets}
    {δ : Derivation Geom (ChartRing f P) (ChartRing f P)} (hδ : FollowsFlow f P δ)
    (Q : Row 4) :
    onChart f P (flowNumerator f Q) = onChart f P (separant f) * δ (onChart f P Q) := by
  rw [hδ, ← mul_assoc, separant_mul_inverse, one_mul]
set_option linter.overlappingInstances false in
private theorem cleared_rule {R k : Type*} [CommRing R] [CommRing k] [Algebra k R] [Module k R]
    (δ : Derivation k R R) (s v : R) (a : ℕ) :
    s * (s * δ (s ^ a * v)) - (a : R) * (s * δ s) * (s ^ a * v) =
      s ^ (a + 2) * δ v := by
  cases a with
  | zero => simp [pow_two, mul_assoc]
  | succ a =>
    rw [δ.leibniz, δ.leibniz_pow, Nat.succ_sub_one, pow_add s (a+1) 2, pow_succ' s a]
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
private theorem chart_iterate {f : Row 4} {P : Ideal GeoJets}
    {δ : Derivation Geom (ChartRing f P) (ChartRing f P)} (hδ : FollowsFlow f P δ)
    (n : ℕ) :
    onChart f P (jetNumerator f n) =
      onChart f P (separant f) ^ (2*n) * (δ^[n]) (onChart f P (MvPolynomial.X 0)) := by
  induction n with
  | zero => simp [jetNumerator]
  | succ n ih =>
    simp only [jetNumerator, clearedStep, map_sub, map_mul, map_natCast, flow_image hδ]
    rw [ih, show 2*(n+1) = 2*n+2 by omega, Function.iterate_succ_apply']
    exact cleared_rule (k := Geom) (R := ChartRing f P) δ _ _ (2*n)
theorem chart_factorial_unit (f : Row 4) (P : Ideal GeoJets) {n : ℕ}
    (hn : n < K1.p) : IsUnit (↑n.factorial : ChartRing f P) := by
  rw [← map_natCast (chartConstants f P)]
  exact (K1_13_7_1.factorial_cast_ne_zero hn).isUnit.map (chartConstants f P)
private theorem chart_iterate_small {f : Row 4} {P : Ideal GeoJets}
    {δ : Derivation Geom (ChartRing f P) (ChartRing f P)} (hδ : FollowsFlow f P δ)
    {n : ℕ} (hn : n < 4) :
    (δ^[n]) (onChart f P (MvPolynomial.X 0)) =
      (↑n.factorial : ChartRing f P) * onChart f P (MvPolynomial.X ⟨n, hn⟩) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n < 3 := by omega
    rw [Function.iterate_succ_apply', ih (by omega), δ.leibniz, δ.map_natCast]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rw [show (⟨n, by omega⟩ : Fin 4) = (⟨n, hn'⟩ : Fin 3).castSucc by rfl,
      chart_shift hδ, Nat.factorial_succ, Nat.cast_mul]
    rw [show (⟨n, hn'⟩ : Fin 3).succ = (⟨n+1, hn⟩ : Fin 4) by exact Fin.ext rfl]
    change _ * ((↑(n+1) : ChartRing f P) * _) = (↑(n+1) : ChartRing f P) * _ * _
    ring
private theorem chart_iterate_jet {f : Row 4} {P : Ideal GeoJets}
    {δ : Derivation Geom (ChartRing f P) (ChartRing f P)} (hδ : FollowsFlow f P δ)
    (i : Fin taylorLength) :
    (δ^[i.val]) (onChart f P (MvPolynomial.X 0)) =
      (↑i.val.factorial : ChartRing f P) * chartJet f P i := by
  rw [chartJet]
  split_ifs with hi
  · exact chart_iterate_small hδ hi
  · rw [chart_iterate hδ]
    have hmul : inverseSeparant f P * onChart f P (separant f) = 1 := by
      rw [mul_comm, separant_mul_inverse]
    have hc : (↑i.val.factorial : ChartRing f P) *
        chartConstants f P (↑i.val.factorial : Geom)⁻¹ = 1 := by
      rw [← map_natCast (chartConstants f P), ← map_mul,
        mul_inv_cancel₀ (K1_13_7_1.factorial_cast_ne_zero
          (i.isLt.trans (by decide : taylorLength < K1.p))), map_one]
    have hpow : inverseSeparant f P ^ (2*i.val) * onChart f P (separant f) ^ (2*i.val) = 1 := by
      rw [← mul_pow, hmul, one_pow]
    symm
    calc
      _ = ((↑i.val.factorial : ChartRing f P) * chartConstants f P (↑i.val.factorial : Geom)⁻¹) *
          (inverseSeparant f P ^ (2*i.val) * onChart f P (separant f) ^ (2*i.val)) *
          (δ^[i.val]) (onChart f P (MvPolynomial.X 0)) := by ring
      _ = _ := by rw [hc, hpow, mul_one, one_mul]
private theorem coeff_jet_sum {R : Type*} [CommRing R] {M : ℕ} (a : Fin M → R) (i : Fin M) :
    (∑ j : Fin M, monomial j.val (a j)).coeff i.val = a i := by
  classical
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · exact coeff_monomial_same _ _
  · intro j _ hj
    exact coeff_monomial_of_ne _ (fun h => hj (Fin.ext h.symm))
  · simp
private theorem eval_hasse_of_taylor_eq_sum {R : Type*} [CommRing R] {M : ℕ}
    {U : (Polynomial R)} {x : R} {a : Fin M → R}
    (h : taylor x U = ∑ i : Fin M, monomial i.val (a i)) (i : Fin M) :
    (hasseDeriv i.val U).eval x = a i := by
  rw [← taylor_coeff, h, coeff_jet_sum]
private theorem eval_hasse_chartJet {f : Row 4} {P : Ideal GeoJets} (i : Fin taylorLength) :
    (hasseDeriv i.val (chartPolynomial f P)).eval (chartCenter f P) = chartJet f P i := by
  refine eval_hasse_of_taylor_eq_sum ?_ i
  rw [chartPolynomial, taylor_taylor, add_neg_cancel, taylor_zero]
theorem chartPolynomial_degree (f : Row 4) (P : Ideal GeoJets) :
    (chartPolynomial f P).natDegree < taylorLength := by
  simpa only [Polynomial.map_id] using mapped_chartPolynomial_degree
    (RingHom.id (ChartRing f P))
private theorem terminated_iterate {f : Row 4} {P : Ideal GeoJets}
    {δ : Derivation Geom (ChartRing f P) (ChartRing f P)} (hδ : FollowsFlow f P δ)
    (hmem : toGeneric (membershipTest f) ∈ P) :
    (δ^[taylorLength]) (onChart f P (MvPolynomial.X 0)) = 0 := by
  have h := onChart_zero (f := f) hmem
  rw [membershipTest, chart_iterate hδ, ← mul_zero (onChart f P (separant f) ^ (2*taylorLength))]
    at h
  exact ((IsUnit.of_mul_eq_one _ (separant_mul_inverse f P)).pow _).mul_left_cancel h
theorem chartTaylor_shift {f : Row 4} {P : Ideal GeoJets}
    {δ : Derivation Geom (ChartRing f P) (ChartRing f P)} (hδ : FollowsFlow f P δ)
    (hmem : toGeneric (membershipTest f) ∈ P) (n : ℕ) :
    δ ((hasseDeriv n (chartPolynomial f P)).eval (chartCenter f P)) =
      (↑(n + 1) : ChartRing f P) *
        (hasseDeriv (n+1) (chartPolynomial f P)).eval (chartCenter f P) := by
  let U := chartPolynomial f P
  let x := chartCenter f P
  let y := onChart f P (MvPolynomial.X 0)
  have hdeg : U.natDegree < taylorLength := chartPolynomial_degree f P
  change δ ((hasseDeriv n U).eval x) = (↑(n+1) : ChartRing f P) * (hasseDeriv (n+1) U).eval x
  by_cases hn : n < taylorLength
  · have hit (i : ℕ) (hi : i ≤ taylorLength) :
        (δ^[i]) y = (↑i.factorial : ChartRing f P) * (hasseDeriv i U).eval x := by
      rcases lt_or_eq_of_le hi with hi | rfl
      · rw [eval_hasse_chartJet (⟨i, hi⟩ : Fin taylorLength)]
        exact chart_iterate_jet hδ ⟨i, hi⟩
      · rw [hasseDeriv_eq_zero_of_lt_natDegree U _ hdeg, eval_zero, mul_zero]
        exact terminated_iterate hδ hmem
    have h := hit (n+1) (by omega)
    rw [Function.iterate_succ_apply', hit n hn.le, δ.leibniz, δ.map_natCast,
      Nat.factorial_succ, Nat.cast_mul] at h
    simp only [smul_eq_mul, mul_zero, add_zero, mul_assoc] at h
    rw [mul_left_comm (↑(n+1) : ChartRing f P)] at h
    exact (chart_factorial_unit f P (hn.trans (by decide : taylorLength < K1.p))).mul_left_cancel h
  · rw [hasseDeriv_eq_zero_of_lt_natDegree U n (by omega),
      hasseDeriv_eq_zero_of_lt_natDegree U (n+1) (by omega), eval_zero, map_zero, mul_zero]
end
end K1_13_7_2_4_2
end
section
namespace K1_13_7_2_5
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_7_2 MvPolynomial
structure FreshChart (f : Row 4) (T : FatTaylor f) (A : CoeffIdeal) : Prop where
  extended_prime : (extendIdeal A).IsPrime
  dimension_eq : dimension (freshImage A) = dimension A
  factor : toGeneric f ∈ freshImage A
  regular : toGeneric (separant f) ∉ freshImage A
  test : toGeneric T.test ∈ freshImage A
  denom : toGeneric T.denom ∉ freshImage A
  recovers : ∀ i, MvPolynomial.X i * freshJetMap (toGeneric T.denom) -
    freshJetMap (toGeneric (T.numer i)) ∈ extendIdeal A
def wholeComponents (f : Row 4) : Finset JetIdeal :=
  (Ideal.span {toGeneric f}).minimalPrimesFinset
def properComponents (f E : Row 4) : Finset JetIdeal := by
  classical
  exact ((wholeComponents f).filter (fun component => toGeneric E ∉ component)).biUnion
    (fun component => (divisorIdeal component E).minimalPrimesFinset)
end
end K1_13_7_2_5
end
section
set_option autoImplicit false
namespace K1_13_7_2_5_4
noncomputable section
open K1_13 K1_13_6_3 K1_13_6_3_4 MvPolynomial
structure CoeffHyperplane where
  offset : Geom
  slope : Fin taylorLength → Geom
def CoeffHyperplane.form (H : CoeffHyperplane) : K1_13_6_3.CoeffRing :=
  MvPolynomial.C H.offset + ∑ i, MvPolynomial.C (H.slope i) * MvPolynomial.X i
def CoeffHyperplane.freshForm (H : CoeffHyperplane) : FreshCoeffRing :=
  MvPolynomial.map geomConstants H.form
def cut {R : Type*} [CommRing R] (I : Ideal R) (p : R) : Ideal R :=
  I ⊔ Ideal.span {p}
def saturate {R : Type*} [CommRing R] (I : Ideal R) (d : R) : Ideal R :=
  let ι := algebraMap R (Localization.Away d)
  (I.map ι).comap ι
def coefficientSurface (A : CoeffIdeal) (H : CoeffHyperplane) : CoeffIdeal :=
  cut A H.form
def coefficientCurve (A : CoeffIdeal) (H G : CoeffHyperplane) : CoeffIdeal :=
  cut (coefficientSurface A H) G.form
def retainedSurface (A : CoeffIdeal) (d : FreshCoeffRing) (H : CoeffHyperplane) :
    Ideal FreshCoeffRing :=
  saturate (extendIdeal (coefficientSurface A H)) d
def retainedCurve (A : CoeffIdeal) (d : FreshCoeffRing) (H G : CoeffHyperplane) :
    Ideal FreshCoeffRing :=
  saturate (extendIdeal (coefficientCurve A H G)) d
structure TwoSlices (A : CoeffIdeal) (d : FreshCoeffRing) where
  first : CoeffHyperplane
  second : CoeffHyperplane
  first_proper : first.freshForm ∉ extendIdeal A
  second_regular : IsLeftRegular (Ideal.Quotient.mk (retainedSurface A d first) second.freshForm)
  curve_dimension : dimension (retainedCurve A d first second) = 1
  curve_degree : affineDegree (retainedCurve A d first second) = affineDegree A
  boundary_finite : ∀ i, dimension (boundaryChart (coefficientCurve A first second) i) = 0
end
end K1_13_7_2_5_4
end
section
set_option autoImplicit false
namespace K1_13_7_2_5_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_7 K1_13_7_2 K1_13_7_2_5 MvPolynomial
theorem le_cut {R : Type*} [CommRing R] (I : Ideal R) (p : R) : I ≤ cut I p :=
  le_sup_left
theorem mem_cut {R : Type*} [CommRing R] (I : Ideal R) (p : R) : p ∈ cut I p :=
  Ideal.mem_sup_right (Ideal.mem_span_singleton_self p)
theorem le_saturate {R : Type*} [CommRing R] (I : Ideal R) (d : R) : I ≤ saturate I d :=
  fun _ hx ↦ Ideal.mem_map_of_mem (algebraMap R (Localization.Away d)) hx
theorem saturate_mono {R : Type*} [CommRing R] {I J : Ideal R} (h : I ≤ J) (d : R) :
    saturate I d ≤ saturate J d :=
  Ideal.comap_mono (Ideal.map_mono h)
private theorem mem_saturate_iff {R : Type*} [CommRing R] (I : Ideal R) (d x : R) :
    x ∈ saturate I d ↔ ∃ n : ℕ, d ^ n * x ∈ I := by
  change algebraMap R (Localization.Away d) x ∈ I.map _ ↔ _
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers d)]
  simp only [Submonoid.mem_powers_iff]
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨d ^ n, ⟨n, rfl⟩, hn⟩
theorem regular_saturate {R : Type*} [CommRing R] (I : Ideal R) (d : R) :
    IsLeftRegular (Ideal.Quotient.mk (saturate I d) d) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, mem_saturate_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_saturate_iff]
  exact ⟨n + 1, by rwa [pow_succ, mul_assoc]⟩
theorem regular_cut_bound {I J : JetIdeal} {p : GeoJets} {b : ℕ}
    (hIJ : cut I p ≤ J) (hreg : IsLeftRegular (Ideal.Quotient.mk I p))
    (hb : p.totalDegree ≤ b) :
    dimension J ≤ dimension I - 1 ∧
      (dimension J + 1 = dimension I → affineDegree J ≤ (b : ℚ) * affineDegree I) := by
  have h := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hreg hb
  change dimension (cut I p) ≤ dimension I - 1 ∧ _ at h
  have hmon := natDegree_affineHilbertPolynomial_le_of_le hIJ
  change dimension J ≤ dimension (cut I p) at hmon
  have hdim := hmon.trans h.1
  refine ⟨hdim, fun hd ↦ ?_⟩
  have hsame : dimension J = dimension (cut I p) := by omega
  have hsucc : dimension I = dimension (cut I p) + 1 := by omega
  have hsub : dimension I - 1 = dimension (cut I p) := by omega
  have hc := h.2
  change (affineHilbertPolynomial (cut I p)).coeff (dimension I - 1) ≤ _ at hc
  rw [hsub] at hc
  calc
    affineDegree J ≤ affineDegree (cut I p) := affineDegree_le_of_le hIJ hsame
    _ ≤ (dimension (cut I p)).factorial *
        ((b : ℚ) * dimension I * (affineHilbertPolynomial I).leadingCoeff) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (b : ℚ) * affineDegree I := by
      change _ = (b : ℚ) * ((dimension I).factorial * (affineHilbertPolynomial I).leadingCoeff)
      rw [hsucc, Nat.factorial_succ, Nat.cast_mul]
      ring
end
end K1_13_7_2_5_4
end
section
set_option autoImplicit false
namespace K1_13_7_2_5_4_1
open MvPolynomial
def EventuallyRegularHomogeneous {k σ : Type*} [Field k]
    (B : Ideal (MvPolynomial σ k)) (ℓ : MvPolynomial σ k) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ q : MvPolynomial σ k, q.IsHomogeneous n → ℓ * q ∈ B → q ∈ B
end K1_13_7_2_5_4_1
end
section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
namespace K1_13_7_2_5_4_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_4 K1_13_7_2_5_4 MvPolynomial
section Parameters
variable {k E σ : Type*} [Field k] [Field E] [Algebra k E] [Fintype σ]
def slopeMap : (k × (σ → k)) →ₗ[k] MvPolynomial σ E :=
  ∑ i : σ, ((LinearMap.proj i).comp (LinearMap.snd k k (σ → k))).smulRight
    (MvPolynomial.X i)
def formMap : (k × (σ → k)) →ₗ[k] MvPolynomial σ E :=
  (LinearMap.fst k k (σ → k)).smulRight 1 + slopeMap
theorem slopeMap_apply (v : k × (σ → k)) :
    slopeMap (E := E) v = ∑ i : σ, C (algebraMap k E (v.2 i)) * MvPolynomial.X i := by
  simp only [slopeMap, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.snd_apply, Algebra.smul_def,
    IsScalarTower.algebraMap_eq k E (MvPolynomial σ E), RingHom.comp_apply, MvPolynomial.algebraMap_eq]
theorem formMap_apply (v : k × (σ → k)) :
    formMap (E := E) v = C (algebraMap k E v.1) + slopeMap (E := E) v := by
  simp only [formMap, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
    Algebra.smul_def, IsScalarTower.algebraMap_eq k E (MvPolynomial σ E),
    RingHom.comp_apply, MvPolynomial.algebraMap_eq, mul_one]
theorem exists_parameters [Infinite k] (I J B : Ideal (MvPolynomial σ E)) :
    ∃ v : k × (σ → k),
      (∀ P ∈ associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ I), formMap v ∉ P) ∧
      (∀ P ∈ associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ J), formMap v ∉ P) ∧
      (∀ P ∈ associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ B),
        (∃ i : σ, MvPolynomial.X i ∉ P) → slopeMap v ∉ P) := by
  classical
  let S := associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ I) ∪
    associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ J)
  let T := {P ∈ associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ B) |
    ∃ i : σ, MvPolynomial.X i ∉ P}
  have hS : S.Finite := (associatedPrimes.finite _ _).union (associatedPrimes.finite _ _)
  have hT : T.Finite := (associatedPrimes.finite _ _).subset fun _ hp ↦ hp.1
  let : Finite S := hS.to_subtype
  let : Finite T := hT.to_subtype
  let bad : S ⊕ T → Submodule k (k × (σ → k)) :=
    Sum.elim
      (fun P ↦ (P.val.restrictScalars k).comap formMap)
      (fun P ↦ (P.val.restrictScalars k).comap slopeMap)
  have hbad : ∀ t, bad t ≠ ⊤ := by
    intro t htop
    cases t with
    | inl P =>
      have hprime : P.val.IsPrime := P.property.elim (·.isPrime) (·.isPrime)
      have hmem : ((1 : k), (0 : σ → k)) ∈ bad (.inl P) := htop ▸ Submodule.mem_top
      change formMap (1, 0) ∈ P.val at hmem
      rw [formMap_apply, slopeMap_apply] at hmem
      apply hprime.ne_top
      apply P.val.eq_top_of_isUnit_mem _ isUnit_one
      simpa only [map_one, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, add_zero] using hmem
    | inr P =>
      obtain ⟨i, hi⟩ := P.property.2
      let v : σ → k := fun j ↦ if j = i then 1 else 0
      have hmem : ((0 : k), v) ∈ bad (.inr P) := htop ▸ Submodule.mem_top
      change slopeMap (0, v) ∈ P.val at hmem
      rw [slopeMap_apply] at hmem
      have hv : (∑ j : σ, C (algebraMap k E (v j)) * MvPolynomial.X j) = MvPolynomial.X i := by
        rw [Finset.sum_eq_single i]
        · simp [v]
        · intro j _ hji
          simp [v, hji]
        · simp
      exact hi (hv ▸ hmem)
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨v, fun P hP ↦ hv (.inl ⟨P, Or.inl hP⟩), fun P hP ↦ hv (.inl ⟨P, Or.inr hP⟩),
    fun P hP hi ↦ hv (.inr ⟨P, hP, hi⟩)⟩
end Parameters
theorem linearForm_homogeneous {F σ : Type*} [Field F] [Fintype σ] (a : σ → F) :
    (∑ i : σ, C (a i) * MvPolynomial.X i).IsHomogeneous 1 :=
  (homogeneousSubmodule σ F 1).sum_mem fun i _ ↦ isHomogeneous_C_mul_X (a i) i
theorem regular_of_avoids_associated {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (f : R) (h : ∀ P ∈ associatedPrimes R (R ⧸ I), f ∉ P) :
    IsLeftRegular (Ideal.Quotient.mk I f) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro x hx
  by_contra hn
  have hz : f ∈ {r : R | ∃ z : R ⧸ I, z ≠ 0 ∧ r • z = 0} := ⟨x, hn, hx⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors] at hz
  obtain ⟨P, hP, hf⟩ := Set.mem_iUnion₂.mp hz
  exact h P hP hf
private theorem cut_mem_iff {R : Type*} [CommRing R] (I : Ideal R) (f p : R) :
    p ∈ cut I f ↔ ∃ q, p - f * q ∈ I := by
  rw [cut, sup_comm, Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨q, a, ha, rfl⟩
    refine ⟨q, ?_⟩
    simpa [mul_comm q f] using ha
  · rintro ⟨q, hq⟩
    exact ⟨q, p - f * q, hq, by rw [mul_comm q f, add_sub_cancel]⟩
theorem denominator_regular_after_cut {R : Type*} [CommRing R] (I : Ideal R) (d f : R)
    (hd : IsLeftRegular (Ideal.Quotient.mk I d))
    (hf : IsLeftRegular (Ideal.Quotient.mk (cut I d) f)) :
    IsLeftRegular (Ideal.Quotient.mk (cut I f) d) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, cut_mem_iff] at hx
  obtain ⟨q, hq⟩ := hx
  have hq' : f * q ∈ cut I d := by
    rw [cut_mem_iff]
    exact ⟨p, by simpa only [neg_sub] using I.neg_mem hq⟩
  have hz : Ideal.Quotient.mk (cut I d) q = 0 := by
    apply isLeftRegular_iff_right_eq_zero_of_mul.mp hf
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hq'
  rw [Ideal.Quotient.eq_zero_iff_mem, cut_mem_iff] at hz
  obtain ⟨r, hr⟩ := hz
  have hmul : d * (p - f * r) ∈ I := by
    convert I.add_mem hq (I.mul_mem_left f hr) using 1
    ring
  have hzero : Ideal.Quotient.mk I (p - f * r) = 0 := by
    apply isLeftRegular_iff_right_eq_zero_of_mul.mp hd
    rwa [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  rw [Ideal.Quotient.eq_zero_iff_mem, cut_mem_iff]
  exact ⟨r, Ideal.Quotient.eq_zero_iff_mem.mp hzero⟩
theorem saturate_eq_of_regular {R : Type*} [CommRing R] (I : Ideal R) (d : R)
    (hd : IsLeftRegular (Ideal.Quotient.mk I d)) : saturate I d = I := by
  apply le_antisymm _ (le_saturate I d)
  intro p hp
  change algebraMap R (Localization.Away d) p ∈ I.map _ at hp
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers d)] at hp
  obtain ⟨s, hs, hsp⟩ := hp
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff s d).mp hs
  have hn : IsLeftRegular (Ideal.Quotient.mk I d ^ n) := hd.pow n
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply isLeftRegular_iff_right_eq_zero_of_mul.mp hn
  rwa [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
end
end K1_13_7_2_5_4_1
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace K1_13_7_2_4_2
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_3 K1_13_7_2_4
section PolynomialFlow
variable {R : Type*} [CommRing R]
def intDerivation (d : R →+ R) (h₁ : d 1 = 0)
    (hmul : ∀ a b, d (a * b) = a * d b + b * d a) : Derivation ℤ R R where
  toLinearMap := d.toIntLinearMap
  map_one_eq_zero' := h₁
  leibniz' := hmul
def coeffDeriv (δ : Derivation ℤ R R) : Derivation ℤ (Polynomial R) (Polynomial R) :=
  PolynomialModule.equivPolynomialSelf.compDer δ.mapCoeffs
@[simp] private theorem coeff_coeffDeriv (δ : Derivation ℤ R R) (U : (Polynomial R)) (n : ℕ) :
    (coeffDeriv δ U).coeff n = δ (U.coeff n) := rfl
private theorem coeffDeriv_hasse (δ : Derivation ℤ R R) (U : (Polynomial R)) (n : ℕ) :
    coeffDeriv δ (hasseDeriv n U) = hasseDeriv n (coeffDeriv δ U) := by
  ext j
  simp [hasseDeriv_coeff, δ.leibniz, smul_eq_mul]
private theorem deriv_eval (δ : Derivation ℤ R R) (x : R) (U : (Polynomial R)) :
    δ (U.eval x) = (coeffDeriv δ U).eval x + (derivative U).eval x * δ x := by
  have h := PolynomialModule.aeval_equivPolynomial (δ.mapCoeffs U) x
  have he : (coeffDeriv δ U).eval x = PolynomialModule.eval x (δ.mapCoeffs U) := by
    simpa [coeffDeriv, aeval_def] using h
  rw [δ.apply_eval_eq, he, smul_eq_mul]
private theorem derivative_hasse (U : (Polynomial R)) (n : ℕ) :
    derivative (hasseDeriv n U) = C (↑(n+1) : R) * hasseDeriv (n+1) U := by
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := R) 1 n) U
  simpa [hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul, C_eq_natCast,
    Nat.add_comm, add_mul] using h
private theorem deriv_eval_hasse (δ : Derivation ℤ R R) (x : R) (hx : δ x = 1)
    (U : (Polynomial R)) (n : ℕ) :
    δ ((hasseDeriv n U).eval x) =
      (hasseDeriv n (coeffDeriv δ U)).eval x +
        (↑(n+1) : R) * (hasseDeriv (n+1) U).eval x := by
  rw [deriv_eval, coeffDeriv_hasse, hx, mul_one, derivative_hasse, eval_mul, eval_C]
theorem coeffDeriv_zero_of_shift (δ : Derivation ℤ R R) (x : R) (hx : δ x = 1) (U : (Polynomial R))
    (h : ∀ n, δ ((hasseDeriv n U).eval x) =
      (↑(n+1) : R) * (hasseDeriv (n+1) U).eval x) : coeffDeriv δ U = 0 := by
  apply eq_zero_of_hasseDeriv_eq_zero _ x
  intro n
  have he := deriv_eval_hasse δ x hx U n
  rw [h] at he
  exact add_right_cancel (he.symm.trans (zero_add _).symm)
private theorem coeffDeriv_iterate (δ : Derivation ℤ R R) {V : (Polynomial R)}
    (hV : coeffDeriv δ V = 0) (n : ℕ) : coeffDeriv δ ((derivative^[n]) V) = 0 := by
  induction n with
  | zero => exact hV
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hasseDeriv_one', coeffDeriv_hasse, ih, map_zero]
theorem zero_of_stationary_eval (δ : Derivation ℤ R R) (x : R) (hx : δ x = 1)
    (V : (Polynomial R)) (hV : coeffDeriv δ V = 0) (he : V.eval x = 0)
    (hunit : ∀ n ≤ V.natDegree, IsUnit (↑n.factorial : R)) : V = 0 := by
  have hderiv (n : ℕ) : ((derivative^[n]) V).eval x = 0 := by
    induction n with
    | zero => exact he
    | succ n ih =>
      have h := deriv_eval δ x ((derivative^[n]) V)
      rw [ih, map_zero, coeffDeriv_iterate δ hV n, eval_zero, zero_add, hx, mul_one] at h
      rw [Function.iterate_succ_apply']
      exact h.symm
  apply eq_zero_of_hasseDeriv_eq_zero _ x
  intro n
  by_cases hn : n ≤ V.natDegree
  · have hh : n.factorial • hasseDeriv n V = (derivative^[n]) V :=
      congrFun (factorial_smul_hasseDeriv (R := R) n) V
    have h := congrArg (evalRingHom x) hh
    rw [map_nsmul] at h
    change n.factorial • (hasseDeriv n V).eval x = ((derivative^[n]) V).eval x at h
    rw [nsmul_eq_mul, hderiv] at h
    exact (hunit n hn).mul_left_cancel (h.trans (mul_zero _).symm)
  · rw [hasseDeriv_eq_zero_of_lt_natDegree V _ (Nat.lt_of_not_ge hn), eval_zero]
end PolynomialFlow
def rowTrajectory {R : Type*} [CommRing R]
    (k : Geom →+* R) (Q : Row 4) (U : (Polynomial R)) : (Polynomial R) :=
  MvPolynomial.eval₂ (mapRingHom k) (fun i => hasseDeriv i.val U) Q
theorem rowTrajectory_stationary {R : Type*} [CommRing R]
    (δ : Derivation ℤ R R) (k : Geom →+* R) (hc : ∀ a, δ (k a) = 0)
    (Q : Row 4) (U : (Polynomial R)) (hU : coeffDeriv δ U = 0) :
    coeffDeriv δ (rowTrajectory k Q U) = 0 := by
  let e := MvPolynomial.eval₂Hom (mapRingHom k)
    (fun i : Fin 4 => hasseDeriv i.val U)
  change coeffDeriv δ (e Q) = 0
  induction Q using MvPolynomial.induction_on with
  | C c =>
    ext n
    rw [MvPolynomial.eval₂Hom_C, coeff_coeffDeriv, coe_mapRingHom, coeff_map, coeff_zero]
    exact hc (c.coeff n)
  | add a b ha hb => simp [map_add, ha, hb]
  | mul_X a i ha =>
    rw [map_mul, MvPolynomial.eval₂Hom_X', (coeffDeriv δ).leibniz, coeffDeriv_hasse, ha, hU]
    simp
theorem eval_chartTrajectory (f : Row 4) (P : Ideal GeoJets) (Q : Row 4) :
    (rowTrajectory (chartConstants f P) Q (chartPolynomial f P)).eval (chartCenter f P) =
      onChart f P Q := by
  let e := (evalRingHom (chartCenter f P)).comp (mapRingHom (chartConstants f P))
  have he : e = (onChart f P).comp MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [e, chartConstants]
    · simp [e, chartCenter]
  change (evalRingHom (chartCenter f P)) (MvPolynomial.eval₂ (mapRingHom (chartConstants f P))
    (fun i : Fin 4 => hasseDeriv i.val (chartPolynomial f P)) Q) = _
  rw [MvPolynomial.hom_eval₂, show (evalRingHom (chartCenter f P)).comp
    (mapRingHom (chartConstants f P)) = e from rfl]
  have h : MvPolynomial.eval₂Hom e (fun i : Fin 4 =>
      (evalRingHom (chartCenter f P)) (hasseDeriv i.val (chartPolynomial f P))) = onChart f P := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply] using RingHom.congr_fun he c
    · intro i
      simpa only [MvPolynomial.eval₂Hom_X', coe_evalRingHom, RingHom.id_apply, Polynomial.map_id] using
        eval_hasse_chartPolynomial (RingHom.id (ChartRing f P)) i
  exact RingHom.congr_fun h Q
end
end K1_13_7_2_4_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace K1_13_7_2_5_4_1
noncomputable section
open K1_13_6_3 K1_13_6_3_4 MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]
theorem boundary_homogeneous (I : Ideal (MvPolynomial σ k)) :
    (boundaryIdeal I).IsHomogeneous (homogeneousSubmodule σ k) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨p, n, _, _, rfl⟩
  exact ⟨n, homogeneousComponent_mem n p⟩
private theorem boundary_eq (I : Ideal (MvPolynomial σ k)) :
    boundaryIdeal I = K1_13_6_3_5.boundaryIdeal I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, n, hp, hn, rfl⟩
    exact K1_13_6_3_5_4.component_mem_boundary hp hn
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    exact Ideal.subset_span ⟨p, p.totalDegree, hp, le_rfl, rfl⟩
private theorem decompose_apply (p : MvPolynomial σ k) (n : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule σ k) p n : MvPolynomial σ k) =
      homogeneousComponent n p :=
  decomposition.decompose'_apply p n
theorem component_mul_linear {ℓ p : MvPolynomial σ k}
    (hℓ : ℓ.IsHomogeneous 1) (n : ℕ) :
    homogeneousComponent (n + 1) (ℓ * p) = ℓ * homogeneousComponent n p := by
  simpa only [decompose_apply, Nat.succ_sub_one] using
    (DirectSum.coe_decompose_mul_of_left_mem_of_le
      (𝒜 := homogeneousSubmodule σ k) (b := p) hℓ (Nat.succ_le_succ (Nat.zero_le n)))
private theorem chart_form_regular (B : Ideal (MvPolynomial σ k))
    (hB : B.IsHomogeneous (homogeneousSubmodule σ k)) (i : σ) :
    IsLeftRegular (Ideal.Quotient.mk B (MvPolynomial.X i - 1)) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hz
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hX : IsHomogeneous (MvPolynomial.X i : MvPolynomial σ k) 1 := isHomogeneous_X k i
  have hprod (n : ℕ) :
      homogeneousComponent n ((MvPolynomial.X i - 1) * p) ∈ B := by
    simpa only [decompose_apply] using (hB.mem_iff.mp hz n)
  have h0 : homogeneousComponent 0 (MvPolynomial.X i * p) = 0 := by
    simpa only [decompose_apply] using
      (DirectSum.coe_decompose_mul_of_left_mem_of_not_le
        (𝒜 := homogeneousSubmodule σ k) (b := p) hX (Nat.not_succ_le_zero 0))
  suffices hc : ∀ n, homogeneousComponent n p ∈ B by
    exact hB.mem_iff.mpr (fun n ↦ by simpa only [decompose_apply] using hc n)
  intro n
  induction n with
  | zero =>
    have h := hprod 0
    rw [sub_mul, one_mul, map_sub, h0, zero_sub] at h
    exact (B.neg_mem_iff).mp h
  | succ n ih =>
    have h := hprod (n + 1)
    rw [sub_mul, one_mul, map_sub, component_mul_linear hX] at h
    exact (B.sub_mem_iff_right (B.mul_mem_left _ ih)).mp h
theorem boundary_charts_of_curve [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : dimension I = 1) (i : σ) :
    dimension (boundaryChart I i) = 0 := by
  have hB : dimension (boundaryIdeal I) ≤ 1 := by
    rw [boundary_eq, ← hI]
    exact K1_13_6_3_5_4.boundary_dimension_le I
  have hd : (MvPolynomial.X i - 1 : MvPolynomial σ k).totalDegree ≤ 1 := by
    simpa only [totalDegree_X, totalDegree_one, Nat.max_zero] using
      (totalDegree_sub (MvPolynomial.X i : MvPolynomial σ k) 1)
  have h := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (chart_form_regular (boundaryIdeal I) (boundary_homogeneous I) i) hd).1
  change dimension (boundaryChart I i) ≤ dimension (boundaryIdeal I) - 1 at h
  omega
end
end K1_13_7_2_5_4_1
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_7_1 K1_13_6_2_3_1 K1_13_6_2_3_2 K1_13_6_2_3_2_5 MvPolynomial
open scoped BigOperators Pointwise
theorem weak_cap_add {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    capExponents p + capExponents q = capExponents (p.plus q) := by
  ext e
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [cap_coords, Shape.plus, Finsupp.add_apply] at *
    omega
  · intro he
    obtain ⟨hpb, hpj⟩ := hp
    obtain ⟨hqb, hqj⟩ := hq
    rw [cap_coords] at he
    simp only [Shape.plus] at he
    let z := min (e 3) (2 * p.t)
    let z' := e 3 - z
    have hz : z + z' = e 3 ∧ z ≤ 2 * p.t ∧ z' ≤ 2 * q.t := by dsimp [z, z']; omega
    let w := 2 * p.j - 3 * z
    let w' := 2 * q.j - 3 * z'
    have hw : w + 3 * z = 2 * p.j ∧ w' + 3 * z' = 2 * q.j := by
      dsimp [w, w']
      omega
    have hhalf : (w + w') / 2 = w / 2 + w' / 2 := by
      by_cases h : e 3 ≤ 2 * p.t
      · have hz' : z' = 0 := by dsimp [z, z']; omega
        omega
      · have hze : z = 2 * p.t := min_eq_right (by omega)
        omega
    let y := min (e 2) (w / 2)
    let y' := e 2 - y
    have hy : y + y' = e 2 ∧ 2 * y ≤ w ∧ 2 * y' ≤ w' := by dsimp [y, y']; omega
    let x := min (e 1) (w - 2 * y)
    let x' := e 1 - x
    have hx : x + x' = e 1 ∧ x + 2 * y ≤ w ∧ x' + 2 * y' ≤ w' := by
      dsimp [x, x']
      omega
    let u := min (e 0) (2 * p.b - (x + y + z))
    let u' := e 0 - u
    have hu : u + u' = e 0 ∧ u + x + y + z ≤ 2 * p.b ∧
        u' + x' + y' + z' ≤ 2 * q.b := by
      dsimp [u, u']
      omega
    let a : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u, x, y, z]
    let b : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u', x', y', z']
    refine ⟨a, (cap_coords p a).mpr ?_, b, (cap_coords q b).mpr ?_, ?_⟩
    · change u + x + y + z ≤ 2 * p.b ∧ x + 2 * y + 3 * z ≤ 2 * p.j ∧ z ≤ 2 * p.t
      omega
    · change u' + x' + y' + z' ≤ 2 * q.b ∧ x' + 2 * y' + 3 * z' ≤ 2 * q.j ∧ z' ≤ 2 * q.t
      omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx.1
      · exact hy.1
      · exact hz.1
theorem cap_surjective (p : Shape) (hp : ChamberBox p) :
    Function.Surjective (monomialMap GeoField (capExponents p)) := by
  apply monomialMap_surjective
  intro i
  have ⟨hb, hj, ht⟩ := hp
  fin_cases i <;> norm_num [cap_coords, Finsupp.single_apply] <;> omega
theorem cap_filtration (J : Ideal GeoJets) (p : Shape) (hp : ChamberBox p) (n : ℕ) :
    affineHilbertFunction
        (J.comap (monomialMap GeoField (capExponents p)).toRingHom) n =
      supportRank J (capExponents (p.scale n)) := by
  rw [K1_13_6_2_3_2_4.proof J p n, K1_13_6_2_3_2_2.proof
    (fun _ : Unit => p) (fun _ => hp) (fun _ => n)]
  simp [shapeSum, Shape.scale]
theorem shapeSum_chamber {ι : Type} [Fintype ι] (s : ι → Shape)
    (hs : ∀ i, Chamber (s i)) (a : ι → ℕ) : Chamber (shapeSum s a) := by
  refine ⟨Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hs i).1), ?_⟩
  change 3 * (∑ i, a i * (s i).t) ≤ ∑ i, a i * (s i).j
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [Nat.mul_left_comm 3]
    exact Nat.mul_le_mul_left _ (hs i).2
private theorem cap_zero : capExponents ⟨0, 0, 0⟩ = (0 : Set (Fin 4 →₀ ℕ)) := by
  simpa only [Shape.scale, zero_mul, zero_smul] using
    (nsmul_cap ⟨3, 3, 1⟩ ⟨by decide, by decide, by decide⟩ 0).symm
private theorem step_sum {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    ∑ j, step i j = 1 := by
  simp [step, Pi.single_apply]
private theorem exists_slot_of_weight_pos {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι → Shape) (e : CapVar s →₀ ℕ) (i : ι)
    (hi : 0 < Finsupp.weight (step ∘ capSlot s) e i) :
    ∃ v : CapVar s, v.1 = i ∧ e v ≠ 0 := by
  classical
  let _ : Fintype (CapVar s) := Fintype.ofFinite _
  rw [Finsupp.weight_eq_sum, Finset.sum_apply] at hi
  obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi.ne'
  change e v * Pi.single (M := fun _ : ι => ℕ) v.1 1 i ≠ 0 at hv
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at hv
  by_cases h : v.1 = i
  · exact ⟨v, h, by simpa [h, eq_comm] using hv⟩
  · have hn : i ≠ v.1 := Ne.symm h
    simp [hn] at hv
private theorem product_add_step {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι → Shape) (a : ι → ℕ) (i : ι) :
    productExponents s (a + step i) = productExponents s a + capExponents (s i) := by
  classical
  ext m
  constructor
  · rintro ⟨e, he, rfl⟩
    have hi : 0 < Finsupp.weight (step ∘ capSlot s) e i := by
      rw [he]
      simp [step, Pi.add_apply]
    obtain ⟨v, hv, hv0⟩ := exists_slot_of_weight_pos s e i hi
    have hw₁ := Finsupp.weight_sub_single_add (w := step ∘ capSlot s) hv0
    have hw₂ := Finsupp.weight_sub_single_add (w := fun v : CapVar s => v.2.val) hv0
    have hw : Finsupp.weight (step ∘ capSlot s) (e - Finsupp.single v 1) = a := by
      change _ + step v.1 = _ at hw₁
      rw [he, hv] at hw₁
      exact add_right_cancel hw₁
    refine ⟨_, ⟨_, hw, rfl⟩, v.2.val, ?_, hw₂⟩
    exact hv ▸ v.2.property
  · rintro ⟨m, ⟨e, he, rfl⟩, x, hx, rfl⟩
    let v : CapVar s := ⟨i, ⟨x, hx⟩⟩
    refine ⟨e + Finsupp.single v 1, ?_, ?_⟩
    · rw [map_add, Finsupp.weight_single, he, one_smul]
      rfl
    · rw [map_add, Finsupp.weight_single, one_smul]
private theorem product_zero {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → Shape) :
    productExponents s 0 = (0 : Set (Fin 4 →₀ ℕ)) := by
  classical
  ext m
  constructor
  · rintro ⟨e, he, rfl⟩
    have he0 : e = 0 := by
      by_contra hn
      obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.mpr hn
      have hv' := Finsupp.mem_support_iff.mp hv
      let _ : Fintype (CapVar s) := Fintype.ofFinite _
      have hle : e v ≤ Finsupp.weight (step ∘ capSlot s) e v.1 := by
        rw [Finsupp.weight_eq_sum, Finset.sum_apply]
        have key := Finset.single_le_sum
          (f := fun u : CapVar s => (e u • (step ∘ capSlot s) u) v.1)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
        simpa [step, capSlot] using key
      rw [he] at hle
      exact hv' (Nat.eq_zero_of_le_zero hle)
    simp [he0]
  · intro h
    have hm := Set.mem_zero.mp h
    subst m
    exact ⟨0, map_zero _, map_zero _⟩
theorem product_eq_cap {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → Shape)
    (hs : ∀ i, Chamber (s i)) (a : ι → ℕ) :
    productExponents s a = capExponents (shapeSum s a) := by
  classical
  generalize hn : ∑ i, a i = n
  induction n using Nat.strong_induction_on generalizing a with
  | ind n ih =>
    by_cases ha : a = 0
    · subst a
      rw [product_zero, show shapeSum s 0 = ⟨0, 0, 0⟩ by simp [shapeSum], cap_zero]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
      let b : ι → ℕ := fun j => a j - step i j
      have hb : a = b + step i := by
        funext j
        by_cases hji : j = i
        · subst j
          simp only [b, Pi.add_apply, step, Pi.single_eq_same]
          have : a i ≠ 0 := hi
          omega
        · simp [b, step, Pi.single_apply, hji]
      have hsum : (∑ j, b j) + 1 = n := by
        rw [hb, Pi.add_def, Finset.sum_add_distrib, step_sum] at hn
        exact hn
      have hprev := ih _ (by omega) b rfl
      rw [hb, product_add_step, hprev, shapeSum_add, shapeSum_step,
        weak_cap_add (shapeSum_chamber s hs b) (hs i)]
end
end K1_13_7_2_3_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_7_1 MvPolynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ (J Q : Ideal GeoJets) (a : GeoJets), a ∉ J → Q.IsPrime →
    (∀ x : GeoJets, x * a ∈ J ↔ x ∈ Q) →
    ∀ (d : ℕ), dimension J ≤ d → d ≤ 2 →
    ∀ p : Shape, ChamberBox p →
      capCoeff J d p ≤ capCoeff (J ⊔ Ideal.span {a}) d p + capCoeff Q d p
def c2 : Prop :=
  ∀ (P : Ideal GeoJets), P.IsPrime → dimension P = 2 →
    ∀ p q : Shape, Chamber p → Chamber q → 0 ≤ mixedDegree P [p, q]
private abbrev baseline : Shape := ⟨3, 3, 1⟩
private theorem baseline_box : ChamberBox baseline := ⟨by decide, by decide, by decide⟩
private theorem plus_box {p q : Shape} (hp : ChamberBox p) (hq : Chamber q) :
    ChamberBox (p.plus q) := by
  obtain ⟨hb, hj, ht⟩ := hp
  obtain ⟨hb', hj'⟩ := hq
  exact ⟨Nat.add_le_add hb hb', by dsimp [Shape.plus]; omega, by dsimp [Shape.plus]; omega⟩
private abbrev capMap (p : Shape) := monomialMap GeoField (capExponents p)
private theorem capMap_surjective {p : Shape} (hp : ChamberBox p) :
    Function.Surjective (capMap p) := by
  obtain ⟨hb, hj, ht⟩ := hp
  apply monomialMap_surjective
  intro i
  fin_cases i <;> simp [capExponents, Fin.sum_univ_four] <;> omega
private theorem cap_dimension (J : Ideal GeoJets) {p : Shape} (hp : ChamberBox p) :
    (affineHilbertPolynomial (J.comap (capMap p).toRingHom)).natDegree = dimension J :=
  natDegree_affineHilbertPolynomial_comap_of_surjective (capMap p) (capMap_surjective hp) J
private theorem cap_step (hupper : c1) {J Q : Ideal GeoJets} {a : GeoJets}
    (ha : a ∉ J) (hQ : Q.IsPrime) (hann : ∀ x : GeoJets, x * a ∈ J ↔ x ∈ Q)
    {d : ℕ} (hd : dimension J ≤ d) (hd' : d ≤ 2) {p : Shape} (hp : ChamberBox p) :
    capCoeff J d p = capCoeff (J ⊔ Ideal.span {a}) d p + capCoeff Q d p := by
  apply le_antisymm (hupper J Q a ha hQ hann d hd hd' p hp)
  let K : Ideal GeoJets := J ⊔ Ideal.span {a}
  let f := capMap p
  obtain ⟨A, hA⟩ := capMap_surjective hp a
  have hAK : A ∈ K.comap f.toRingHom := by
    change f A ∈ K
    rw [hA]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  change (affineHilbertPolynomial (K.comap f.toRingHom)).coeff d +
    (affineHilbertPolynomial (Q.comap f.toRingHom)).coeff d ≤
    (affineHilbertPolynomial (J.comap f.toRingHom)).coeff d
  refine K1_13_7_6_1.hilbertCoeff_step (Ideal.comap_mono le_sup_left) hAK (fun x => ?_) ?_
  · change f (x * A) ∈ J ↔ f x ∈ Q
    rw [map_mul, show f A = a from hA, hann]
  · exact (cap_dimension J hp).trans_le hd
private theorem polarize_congr {F G : Shape → ℚ} (heq : ∀ r, ChamberBox r → F r = G r)
    {boxes : List Shape} (hboxes : ∀ r ∈ boxes, Chamber r) {p : Shape} (hp : ChamberBox p) :
    polarize F boxes p = polarize G boxes p := by
  induction boxes generalizing p with
  | nil => exact heq p hp
  | cons r boxes ih =>
    have hr := hboxes r List.mem_cons_self
    have hrest := fun q hq => hboxes q (List.mem_cons_of_mem _ hq)
    simp only [polarize, ih hrest (plus_box hp hr), ih hrest hp]
private theorem polarize_add (F G : Shape → ℚ) (boxes : List Shape) (p : Shape) :
    polarize (fun r => F r + G r) boxes p = polarize F boxes p + polarize G boxes p := by
  induction boxes generalizing p with
  | nil => rfl
  | cons r boxes ih =>
    simp only [polarize, ih]
    ring
private theorem polarize_zero (boxes : List Shape) (p : Shape) :
    polarize (fun _ => 0) boxes p = 0 := by
  induction boxes generalizing p with
  | nil => rfl
  | cons r boxes ih => simp only [polarize, ih, sub_self]
private theorem mixed_step (hupper : c1) {J Q : Ideal GeoJets} {a : GeoJets}
    (ha : a ∉ J) (hQ : Q.IsPrime) (hann : ∀ x : GeoJets, x * a ∈ J ↔ x ∈ Q)
    {boxes : List Shape} (hb : ∀ q ∈ boxes, Chamber q) (hsmall : boxes.length ≤ 2)
    (hd : dimension J ≤ boxes.length) :
    mixedDegree J boxes = mixedDegree (J ⊔ Ideal.span {a}) boxes + mixedDegree Q boxes := by
  unfold mixedDegree
  rw [polarize_congr (fun _ => cap_step hupper ha hQ hann hd hsmall) hb baseline_box,
    polarize_add, add_div]
private theorem capCoeff_le_of_subset (J : Ideal GeoJets) {p q : Shape}
    (hp : ChamberBox p) (hq : ChamberBox q) (hsub : capExponents p ⊆ capExponents q)
    {d : ℕ} (hd : dimension J ≤ d) :
    capCoeff J d p ≤ capCoeff J d q := by
  let incl (i : capExponents p) : capExponents q := ⟨i.val, hsub i.property⟩
  let f := MvPolynomial.rename (R := GeoField) incl
  have hf : (capMap q).comp f = capMap p := by
    ext i
    simp [f, incl, monomialMap_X]
  let I := J.comap (capMap p).toRingHom
  let K := J.comap (capMap q).toRingHom
  have heq : K.comap f.toRingHom = I := by
    change (J.comap (capMap q).toRingHom).comap f.toRingHom = _
    rw [Ideal.comap_comap]
    change J.comap ((capMap q).comp f).toRingHom = I
    rw [hf]
  let g := Ideal.quotientMapₐ K f heq.ge
  have hg : Function.Injective g := Ideal.quotientMap_injective' (H := heq.ge) heq.le
  have hgen (i : capExponents p) :
      g (Ideal.Quotient.mk I (MvPolynomial.X i)) ∈ quotientDegreeLE K 1 := by
    rw [show g (Ideal.Quotient.mk I (MvPolynomial.X i)) =
        Ideal.Quotient.mk K (MvPolynomial.X (incl i)) by
          change Ideal.quotientMap K f.toRingHom heq.ge
            (Ideal.Quotient.mk I (MvPolynomial.X i)) = _
          rw [Ideal.quotientMap_mk]
          change Ideal.Quotient.mk K (MvPolynomial.rename incl (MvPolynomial.X i)) = _
          rw [MvPolynomial.rename_X]]
    exact mk_X_mem_quotientDegreeLE K _
  change (affineHilbertPolynomial I).coeff d ≤ (affineHilbertPolynomial K).coeff d
  refine Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    ((cap_dimension J hp).trans_le hd) ((cap_dimension J hq).trans_le hd) ?_
  filter_upwards [eventually_eval_affineHilbertPolynomial I,
    eventually_eval_affineHilbertPolynomial K] with n hI hK
  rw [hI, hK]
  have h : affineHilbertFunction I n ≤ affineHilbertFunction K n := by
    simpa only [one_mul] using affineHilbertFunction_le_of_injective g hg hgen n
  exact_mod_cast h
private theorem mixed_nonneg (hpos : c2) {Q : Ideal GeoJets} (hQ : Q.IsPrime)
    {boxes : List Shape} (hb : ∀ q ∈ boxes, Chamber q) (hsmall : boxes.length ≤ 2)
    (hd : dimension Q ≤ boxes.length) :
    0 ≤ mixedDegree Q boxes := by
  rcases hd.lt_or_eq with hlt | heq
  · have hz (p : Shape) (hp : ChamberBox p) : capCoeff Q boxes.length p = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt ((cap_dimension Q hp).trans_lt hlt)
    unfold mixedDegree
    rw [polarize_congr hz hb baseline_box, polarize_zero, zero_div]
  · match boxes with
    | [] =>
      change 0 ≤ capCoeff Q 0 baseline / (2 : ℚ) ^ 0
      apply div_nonneg _ (by norm_num)
      exact Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
        ((cap_dimension Q baseline_box).trans_le heq.le)
        (eventually_eval_affineHilbertPolynomial_nonneg _)
    | [p] =>
      have hp := hb p List.mem_cons_self
      have hsub : capExponents baseline ⊆ capExponents (baseline.plus p) := by
        intro e hm
        exact ⟨hm.1.trans (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)),
          hm.2.1.trans (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)),
          hm.2.2.trans (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _))⟩
      change 0 ≤ (capCoeff Q 1 (baseline.plus p) - capCoeff Q 1 baseline) / (2 : ℚ) ^ 1
      exact div_nonneg (sub_nonneg.mpr
        (capCoeff_le_of_subset Q baseline_box (plus_box baseline_box hp) hsub heq.le))
        (by norm_num)
    | [p, q] =>
      exact hpos Q hQ heq p q (hb p (by simp)) (hb q (by simp))
    | _ :: _ :: _ :: rest =>
      simp at hsmall
private theorem minimal_over_cut {J Q P : Ideal GeoJets} {a : GeoJets}
    (hQ : Q.IsPrime) (hann : ∀ x : GeoJets, x * a ∈ J ↔ x ∈ Q)
    (hP : J.IsMinimalPrime P) (hne : P ≠ Q) :
    (J ⊔ Ideal.span {a}).IsMinimalPrime P := by
  have haP : a ∈ P := by
    by_contra haP
    have hQP : Q ≤ P := fun x hx =>
      (hP.isPrime.mem_or_mem (hP.le ((hann x).mpr hx))).resolve_right haP
    have hJQ : J ≤ Q := fun x hx => (hann x).mp (J.mul_mem_right _ hx)
    exact hne (hQP.antisymm (hP.2 ⟨hQ, hJQ⟩ hQP)).symm
  refine ⟨⟨hP.isPrime, sup_le hP.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haP))⟩, ?_⟩
  intro U hU hUP
  exact hP.2 ⟨hU.1, le_sup_left.trans hU.2⟩ hUP
set_option maxHeartbeats 800000 in
theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_2_3_1.c2 := by
  classical
  intro J boxes hb hsmall hd S hS
  revert hd S hS
  induction J using WellFounded.induction (wellFounded_gt (α := Ideal GeoJets)) with
  | h J ih =>
    intro hd S hS
    by_cases hJ : J = ⊤
    · subst J
      have hS0 : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun P hP =>
        (hS P hP).isPrime.ne_top (top_le_iff.mp (hS P hP).le)
      have hz (p : Shape) (_ : ChamberBox p) : capCoeff (⊤ : Ideal GeoJets) boxes.length p = 0 := by
        simp [capCoeff, Ideal.comap_top, affineHilbertPolynomial_top]
      rw [hS0, Finset.sum_empty]
      unfold mixedDegree
      rw [polarize_congr hz hb baseline_box, polarize_zero, zero_div]
    obtain ⟨a, Q, ha, hQ, hann⟩ := K1_13_7_6_1.exists_prime_factor hJ
    let K : Ideal GeoJets := J ⊔ Ideal.span {a}
    have hJK : J ≤ K := le_sup_left
    have haK : a ∈ K := Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < K := lt_of_le_of_ne hJK fun he => ha (he ▸ haK)
    have hJQ : J ≤ Q := fun x hx => (hann x).mp (J.mul_mem_right _ hx)
    have hKd := (natDegree_affineHilbertPolynomial_le_of_le hJK).trans hd
    have hQd := (natDegree_affineHilbertPolynomial_le_of_le hJQ).trans hd
    have hrest (P : Ideal GeoJets) (hP : P ∈ S.erase Q) : K.IsMinimalPrime P :=
      minimal_over_cut hQ hann (hS P (Finset.mem_of_mem_erase hP)) (Finset.ne_of_mem_erase hP)
    have hrec := ih K hlt hKd (S.erase Q) hrest
    rw [mixed_step h1 ha hQ hann hb hsmall hd]
    change _ ≤ mixedDegree K boxes + mixedDegree Q boxes
    by_cases hQS : Q ∈ S
    · rw [← Finset.sum_erase_add _ _ hQS]
      exact add_le_add hrec le_rfl
    · rw [Finset.erase_eq_of_notMem hQS] at hrec
      exact hrec.trans (le_add_of_nonneg_right (mixed_nonneg h2 hQ hb hsmall hQd))
end
end K1_13_7_2_3_1_2
end
section
set_option autoImplicit false
namespace K1_13_7_2_5_4_2
noncomputable section
open Filter MvPolynomial Polynomial
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_4
section Filtration
variable {k σ τ : Type*} [Field k]
variable {I : Ideal (MvPolynomial σ k)} {J : Ideal (MvPolynomial τ k)}
private theorem clear_denominators
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I))
    (d : MvPolynomial τ k ⧸ J)
    (hgen : ∀ i, ∃ a, g d * Ideal.Quotient.mk I (MvPolynomial.X i) = g a)
    (x : MvPolynomial σ k ⧸ I) :
    ∃ (e : ℕ) (a : MvPolynomial τ k ⧸ J), g d ^ e * x = g a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, algebraMap k _ c, ?_⟩
    rw [pow_zero, one_mul]
    exact (g.commutes c).symm
  | add p q hp hq =>
    obtain ⟨e, a, ha⟩ := hp
    obtain ⟨f, b, hb⟩ := hq
    refine ⟨e + f, d ^ f * a + d ^ e * b, ?_⟩
    simp only [map_add, map_mul, map_pow, pow_add, mul_add]
    calc
      _ = g d ^ f * (g d ^ e * Ideal.Quotient.mk I p) +
          g d ^ e * (g d ^ f * Ideal.Quotient.mk I q) := by ac_rfl
      _ = _ := by rw [ha, hb]
  | mul_X p i hp =>
    obtain ⟨e, a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hgen i
    refine ⟨e + 1, a * b, ?_⟩
    simp only [map_mul, pow_succ]
    calc
      _ = (g d ^ e * Ideal.Quotient.mk I p) *
          (g d * Ideal.Quotient.mk I (MvPolynomial.X i)) := by ac_rfl
      _ = _ := by rw [ha, hb]
private abbrev imagePiece
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (n : ℕ) :=
  (quotientDegreeLE J n).map g.toLinearMap
variable [Finite σ] [Finite τ]
theorem hilbert_le_shift
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I))
    (d : MvPolynomial τ k ⧸ J) (hd : IsLeftRegular (g d))
    (hgen : ∀ j, ∃ a, g d * Ideal.Quotient.mk I (MvPolynomial.X j) = g a)
    (i : τ) {ℓ : MvPolynomial σ k}
    (hℓ : g (Ideal.Quotient.mk J (MvPolynomial.X i)) = Ideal.Quotient.mk I ℓ)
    (hred : ValueReduction I ℓ) :
    ∃ C : ℕ, ∀ n : ℕ, affineHilbertFunction I n ≤ affineHilbertFunction J (n + C) := by
  classical
  obtain ⟨N, hN⟩ := hred
  let B := Module.finBasis k (quotientDegreeLE I N)
  choose e a ha using fun j ↦ clear_denominators g d hgen (B j : MvPolynomial σ k ⧸ I)
  obtain ⟨E, hE⟩ := Finite.exists_le e
  let numer := fun j ↦ d ^ (E - e j) * a j
  have hclear (j : Fin (Module.finrank k (quotientDegreeLE I N))) :
      g d ^ E * (B j : MvPolynomial σ k ⧸ I) = g (numer j) := by
    calc
      _ = g d ^ (E - e j) * (g d ^ e j * (B j : MvPolynomial σ k ⧸ I)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hE j)]
      _ = _ := by rw [ha j]; simp only [numer, map_mul, map_pow]
  choose levels hlevels using fun j ↦ exists_mem_quotientDegreeLE J (numer j)
  obtain ⟨C, hC⟩ := Finite.exists_le levels
  have hbase (x : MvPolynomial σ k ⧸ I) (hx : x ∈ quotientDegreeLE I N) :
      g d ^ E * x ∈ imagePiece g C := by
    let z : quotientDegreeLE I N := ⟨x, hx⟩
    have hz : (∑ j, (B.repr z j) • (B j : MvPolynomial σ k ⧸ I)) = x := by
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using
        congrArg (quotientDegreeLE I N).subtype (B.sum_repr z)
    rw [← hz, Finset.mul_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [show g d ^ E * ((B.repr z j) • (B j : MvPolynomial σ k ⧸ I)) =
      (B.repr z j) • (g d ^ E * (B j : MvPolynomial σ k ⧸ I)) from
        Algebra.mul_smul_comm (B.repr z j) (g d ^ E) (B j : MvPolynomial σ k ⧸ I), hclear j]
    apply Submodule.smul_mem
    exact Submodule.mem_map.mpr ⟨_, quotientDegreeLE_mono J (hC j) (hlevels j), rfl⟩
  have hall (n : ℕ) : ∀ x ∈ quotientDegreeLE I n, g d ^ E * x ∈ imagePiece g (n + C) := by
    induction n with
    | zero =>
      intro x hx
      simpa using hbase x (quotientDegreeLE_mono I (Nat.zero_le N) hx)
    | succ n ih =>
      intro x hx
      by_cases hn : N ≤ n
      · obtain ⟨u, hu, v, hv, rfl⟩ := hN n hn x hx
        obtain ⟨s, hs, he⟩ := Submodule.mem_map.mp (ih v hv)
        change g s = g d ^ E * v at he
        rw [mul_add, mul_left_comm (g d ^ E), ← hℓ]
        apply Submodule.add_mem
        · exact Submodule.map_mono (quotientDegreeLE_mono J (by omega)) (ih u hu)
        · change g _ * (g d ^ E * v) ∈ _
          rw [← he, ← map_mul]
          exact Submodule.mem_map.mpr ⟨_, by
            simpa only [Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using
              mul_mem_quotientDegreeLE (mk_X_mem_quotientDegreeLE J i) hs, rfl⟩
      · exact Submodule.map_mono (quotientDegreeLE_mono J (Nat.le_add_left C _))
          (hbase x (quotientDegreeLE_mono I (by omega) hx))
  refine ⟨C, fun n ↦ ?_⟩
  let mult := (LinearMap.mulLeft k (g d ^ E)).comp (quotientDegreeLE I n).subtype
  let m : quotientDegreeLE I n →ₗ[k] imagePiece g (n + C) :=
    mult.codRestrict (imagePiece g (n + C)) (fun x ↦ hall n x x.property)
  have hm : Function.Injective m := by
    intro x y hxy
    exact Subtype.ext ((hd.pow E) (congrArg Subtype.val hxy))
  have hfin : Module.Finite k (imagePiece g (n + C)) := by
    unfold imagePiece
    infer_instance
  exact (LinearMap.finrank_le_finrank_of_injective hm).trans (Submodule.finrank_map_le _ _)
theorem degree_le_of_shift
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (hg : Function.Injective g)
    {C : ℕ} (hupper : ∀ n : ℕ, affineHilbertFunction I n ≤ affineHilbertFunction J (n + C)) :
    dimension J = dimension I ∧ affineDegree I ≤ affineDegree J := by
  let P := affineHilbertPolynomial I
  let Q := affineHilbertPolynomial J
  have hshift : Tendsto (fun n : ℕ ↦ n + C) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_add_right n C) tendsto_id
  have hbound : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ (taylor (C : ℚ) Q).eval (n : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial I,
      hshift.eventually (eventually_eval_affineHilbertPolynomial J)] with n hn hnC
    rw [taylor_eval, ← Nat.cast_add, hn, hnC]
    exact_mod_cast hupper n
  have hle := natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg I) hbound
  have hdeg : P.natDegree = Q.natDegree :=
    (hle.1.trans_eq (natDegree_taylor Q _)).antisymm
      (natDegree_affineHilbertPolynomial_le_of_injective g hg)
  have hlc : P.leadingCoeff ≤ Q.leadingCoeff := by
    simpa only [leadingCoeff_taylor] using hle.2 (hdeg.trans (natDegree_taylor Q _).symm)
  refine ⟨hdeg.symm, ?_⟩
  change (P.natDegree.factorial : ℚ) * P.leadingCoeff ≤
    (Q.natDegree.factorial : ℚ) * Q.leadingCoeff
  rw [hdeg]
  exact mul_le_mul_of_nonneg_left hlc (by positivity)
end Filtration
end
end K1_13_7_2_5_4_2
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 MvPolynomial
theorem proof : K1_13_7_2_3_1_2.c1 := by
  intro J Q a _ _ hann d hd _ p hp
  let f := monomialMap GeoField (capExponents p)
  have hf : Function.Surjective f := by
    obtain ⟨hb, hj, ht⟩ := hp
    apply monomialMap_surjective
    intro i
    fin_cases i <;> simp [capExponents, Fin.sum_univ_four] <;> omega
  obtain ⟨A, hA⟩ := hf a
  have hcut : (J ⊔ Ideal.span {a}).comap f.toRingHom =
      J.comap f.toRingHom ⊔ Ideal.span {A} := by
    have hmap : (J.comap f.toRingHom ⊔ Ideal.span {A}).map f.toRingHom =
        J ⊔ Ideal.span {a} := by
      rw [Ideal.map_sup, Ideal.map_comap_of_surjective f.toRingHom hf, Ideal.map_span,
        Set.image_singleton, show f.toRingHom A = a from hA]
    rw [← hmap, Ideal.comap_map_of_surjective f.toRingHom hf]
    exact sup_eq_left.mpr ((Ideal.comap_mono (f := f.toRingHom) bot_le).trans le_sup_left)
  have hann' (x : MvPolynomial (capExponents p) GeoField) :
      x * A ∈ J.comap f.toRingHom ↔ x ∈ Q.comap f.toRingHom := by
    change f (x * A) ∈ J ↔ f x ∈ Q
    rw [map_mul, hA, hann]
  have hd' : (affineHilbertPolynomial (J.comap f.toRingHom)).natDegree ≤ d :=
    (natDegree_affineHilbertPolynomial_comap_of_surjective f hf J).trans_le hd
  change (affineHilbertPolynomial (J.comap f.toRingHom)).coeff d ≤
    (affineHilbertPolynomial ((J ⊔ Ideal.span {a}).comap f.toRingHom)).coeff d +
      (affineHilbertPolynomial (Q.comap f.toRingHom)).coeff d
  rw [hcut]
  exact K1_13_6_2_4_2_1.proof _ _ A hann' d hd'
end
end K1_13_7_2_3_1_2_1
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_2 K1_13_6_2_3_2_5 K1_13_7_1
open Filter Polynomial
open scoped BigOperators
private theorem shapeSum_nsmul {ι : Type} [Fintype ι]
    (s : ι → Shape) (v : ι → ℕ) (n : ℕ) :
    shapeSum s (n • v) = (shapeSum s v).scale n := by
  simp [shapeSum, Shape.scale, Pi.smul_apply, mul_assoc, Finset.mul_sum]
private theorem supportRank_le {J : Ideal GeoJets} {p q : Shape}
    (hb : p.b ≤ q.b) (hj : p.j ≤ q.j) (ht : p.t ≤ q.t) :
    supportRank J (capExponents p) ≤ supportRank J (capExponents q) := by
  have hsub : capExponents p ⊆ capExponents q :=
    fun _ hm => ⟨hm.1.trans (Nat.mul_le_mul_left _ hb),
      hm.2.1.trans (Nat.mul_le_mul_left _ hj), hm.2.2.trans (Nat.mul_le_mul_left _ ht)⟩
  let : Module.Finite GeoField (MvPolynomial.restrictSupport GeoField (capExponents q)) :=
    MvPolynomial.restrictSupport_finite (Set.toFinite _)
  exact Submodule.finrank_mono (Submodule.map_mono (MvPolynomial.restrictSupport_mono _ hsub))
theorem ray_degree_and_coefficient {ι : Type} [Fintype ι] (s : ι → Shape)
    (hs : ∀ i, Chamber (s i)) (J : Ideal GeoJets) (P : MvPolynomial ι ℚ)
    (u v : ι → ℕ) (hv : 0 < (shapeSum s v).t)
    (hP : ∀ a ≥ u, MvPolynomial.eval (fun i => (a i : ℚ)) P =
      (supportRank J (capExponents (shapeSum s a)) : ℚ))
    (d : ℕ) (hd : dimension J ≤ d) :
    (ray P u v).natDegree ≤ d ∧
      (ray P u v).coeff d = capCoeff J d (shapeSum s v) := by
  let q := shapeSum s v
  let w := shapeSum s u
  let I := J.comap (MvPolynomial.monomialMap GeoField (capExponents q)).toRingHom
  let A := MvPolynomial.affineHilbertPolynomial I
  let Q := ray P u v
  let c := w.b + w.j + w.t
  let B := Polynomial.taylor (c : ℚ) A
  have hq : ChamberBox q := ⟨(shapeSum_chamber s hs v).1, (shapeSum_chamber s hs v).2, hv⟩
  have hqt : 1 ≤ q.t := hv
  have hj : 3 * q.t ≤ q.j := hq.2.1
  have hb : q.j ≤ q.b := hq.1
  have hqb : 1 ≤ q.b := by omega
  have hqj : 1 ≤ q.j := by omega
  have hshift (n : ℕ) {x y : ℕ} (hx : x ≤ c) (hy : 1 ≤ y) :
      x + n * y ≤ (n + c) * y := by
    rw [Nat.add_mul, add_comm (n * y)]
    exact Nat.add_le_add_right (hx.trans (by simpa using Nat.mul_le_mul_left c hy)) _
  have hQ (n : ℕ) : Q.eval (n : ℚ) =
      (supportRank J (capExponents (w.plus (q.scale n))) : ℚ) := by
    rw [ray_eval]
    change MvPolynomial.eval (fun i => (((u + n • v) i : ℕ) : ℚ)) P = _
    rw [hP _ (le_add_of_nonneg_right zero_le), shapeSum_add, shapeSum_nsmul]
  have hA : ∀ᶠ n : ℕ in atTop,
      A.eval (n : ℚ) = (supportRank J (capExponents (q.scale n)) : ℚ) := by
    filter_upwards [MvPolynomial.eventually_eval_affineHilbertPolynomial I] with n hn
    rw [hn, cap_filtration J q hq]
  have hB : ∀ᶠ n : ℕ in atTop,
      B.eval (n : ℚ) = (supportRank J (capExponents (q.scale (n + c))) : ℚ) := by
    obtain ⟨m, hm⟩ := eventually_atTop.mp hA
    refine eventually_atTop.mpr ⟨m, fun n hn => ?_⟩
    change (Polynomial.taylor (c : ℚ) A).eval (n : ℚ) = _
    rw [Polynomial.taylor_eval]
    simpa [add_comm] using hm (n + c) (hn.trans (Nat.le_add_right n c))
  have hlo : ∀ᶠ n : ℕ in atTop, A.eval (n : ℚ) ≤ Q.eval (n : ℚ) := by
    filter_upwards [hA] with n hn
    rw [hn, hQ]
    exact_mod_cast (supportRank_le (J := J) (p := q.scale n) (q := w.plus (q.scale n))
      (Nat.le_add_left ..) (Nat.le_add_left ..) (Nat.le_add_left ..))
  have hhi : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) ≤ B.eval (n : ℚ) := by
    filter_upwards [hB] with n hn
    rw [hQ, hn]
    exact_mod_cast (supportRank_le (J := J) (p := w.plus (q.scale n)) (q := q.scale (n + c))
      (hshift n (by dsimp [c]; omega : w.b ≤ c) hqb)
      (hshift n (by dsimp [c]; omega : w.j ≤ c) hqj)
      (hshift n (by dsimp [c]; omega : w.t ≤ c) hqt))
  have hdim : A.natDegree = dimension J :=
    MvPolynomial.natDegree_affineHilbertPolynomial_comap_of_surjective _ (cap_surjective q hq) J
  have hAd : A.natDegree ≤ d := hdim.trans_le hd
  have hBd : B.natDegree ≤ d := (Polynomial.natDegree_taylor A _).trans_le hAd
  have hQd : Q.natDegree ≤ d :=
    ((Polynomial.natDegree_le_of_eventually_eval_natCast_le
      (Filter.Eventually.of_forall fun n => by rw [hQ]; positivity) hhi).1).trans hBd
  refine ⟨hQd, le_antisymm ?_ ?_⟩
  · have h := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hQd hBd hhi
    change Q.coeff d ≤ (Polynomial.taylor (c : ℚ) A).coeff d at h
    rwa [Polynomial.coeff_taylor_of_natDegree_le _ hAd] at h
  · exact Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hAd hQd hlo
theorem deltas_congr_on_upper {ι : Type} [DecidableEq ι] (used : List ι)
    (A B : (ι → ℕ) → ℚ) (a : ι → ℕ) (h : ∀ b ≥ a, A b = B b) :
    deltas used A a = deltas used B a := by
  induction used generalizing a with
  | nil => exact h a le_rfl
  | cons i rest ih =>
    have hshift : ∀ b ≥ a + step i, A b = B b := fun b hb =>
      h b ((le_add_of_nonneg_right zero_le).trans hb)
    simp only [deltas, ih _ hshift, ih _ h]
theorem deltas_shapeSum {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → Shape)
    (F : Shape → ℚ) (used : List ι) (a : ι → ℕ) :
    deltas used (fun v => F (shapeSum s v)) a =
      polarize F (used.map s) (shapeSum s a) := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih =>
    simp only [deltas, List.map_cons, polarize, ih, shapeSum_add, shapeSum_step]
end
end K1_13_7_2_3_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_2
open K1_13 K1_13_6 K1_13_7_1 K1_13_7_2_3 MvPolynomial
private theorem surface_hilbert_dimension {S : Ideal GeoJets} [S.IsPrime]
    (hS : S.height = 2) : (affineHilbertPolynomial S).natDegree = 2 := by
  have hS₀ : (⊥ : Ideal GeoJets) < S :=
    bot_lt_iff_ne_bot.mpr (fun h => by simp [h, Ideal.height_bot] at hS)
  obtain ⟨f, hf, hf₀⟩ := SetLike.exists_of_lt hS₀
  have hfne : f ≠ 0 := fun h => hf₀ (h ▸ Ideal.zero_mem _)
  obtain ⟨D, hD, hDS⟩ :=
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem S).mpr hf)
  let : D.IsPrime := hD.isPrime
  have hD₀ : D ≠ ⊥ := fun h =>
    hfne (Ideal.mem_bot.mp (h ▸ hD.le (Ideal.mem_span_singleton_self f)))
  have hDh : D.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ D hD)
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hD₀))
  have hDS' : D < S := lt_of_le_of_ne hDS (fun h => by simp [h, hS] at hDh)
  obtain ⟨g, hg, hgD⟩ := SetLike.exists_of_lt hDS'
  obtain ⟨E, hE, hES⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hDS ((Ideal.span_singleton_le_iff_mem S).mpr hg))
  let : E.IsPrime := hE.isPrime
  have hDE : D < E := Ideal.lt_of_mem_minimalPrimes_sup_span hgD hE
  have hEh := Ideal.height_add_one_le_of_lt_of_isPrime hDE
  rw [hDh] at hEh
  have hES' : E = S := Ideal.eq_of_le_of_height_le E hES (by
    rw [hS, show (2 : ℕ∞) = 1 + 1 by decide]
    exact hEh)
  have h₁ := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hfne hD
  have h₂ := principalCut_natDegree_affineHilbertPolynomial_add_one hgD hE
  rw [Nat.card_fin] at h₁
  rw [hES'] at h₂
  omega
private theorem normalization_dim {k A : Type*} [Field k] [CommRing A] [IsDomain A]
    {d : ℕ} (g : MvPolynomial (Fin d) k →+* A) (hgi : Function.Injective g)
    (hgf : g.Finite) : ringKrullDim A = (d : WithBot ℕ∞) := by
  let B := MvPolynomial (Fin d) k
  let inst := g.toAlgebra
  let := inst
  let : Module.Finite B A := hgf
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hgi
  have hB : ringKrullDim B = (d : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [← hB]
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B A))
    intro x y hxy
    exact Ideal.IsIntegral.under_lt_under (show x.asIdeal < y.asIdeal from hxy)
  · obtain ⟨b, hb, hbh⟩ := Ideal.exists_isPrime_le_height (n := d) hB.ge
    obtain ⟨z, hz⟩ := Algebra.IsIntegral.comap_surjective B A (⟨b, hb⟩ : PrimeSpectrum B)
    have hz' : z.asIdeal.under B = b := congrArg PrimeSpectrum.asIdeal hz
    have hle := Ideal.height_under_le_height (R := B) z.asIdeal
    rw [hz'] at hle
    calc
      ringKrullDim B = (d : WithBot ℕ∞) := hB
      _ ≤ (z.asIdeal.height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr (hbh.trans hle)
      _ ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_isPrime
theorem component_curve {S : Ideal GeoJets} {P : GeoJets} {C : Ideal GeoJets}
    (hC : ProperComponent S P C) : C.IsPrime ∧ ringKrullDim (GeoJets ⧸ C) = 1 := by
  let : S.IsPrime := hC.prime
  let : C.IsPrime := hC.component.isPrime
  have hS := surface_hilbert_dimension hC.height
  have hcut := principalCut_natDegree_affineHilbertPolynomial_add_one hC.proper hC.component
  have hdeg : (affineHilbertPolynomial C).natDegree = 1 := by omega
  obtain ⟨d, g, hgi, hgf⟩ := exists_finite_inj_algHom_of_fg GeoField (GeoJets ⧸ C)
  have hd := natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hgf hgi
  rw [hdeg, Nat.card_fin] at hd
  refine ⟨hC.component.isPrime, ?_⟩
  simpa [← hd] using normalization_dim g.toRingHom hgi hgf
theorem chamber_has_simplex {a : Shape} (ha : Chamber a) (ht : 0 < a.t) :
    InBox ⟨1, 3, 1⟩ a := by
  obtain ⟨hb, hj⟩ := ha
  change 1 ≤ a.b ∧ 3 ≤ a.j ∧ 1 ≤ a.t
  omega
end K1_13_7_2_3_2
end
section
namespace K1_13_1_1
end K1_13_1_1
end
section
namespace K1_13_7_5
noncomputable section
open Polynomial Finset K1 K1_13 K1_13_7
open scoped BigOperators
theorem supported_sub {H : Shape} {F G : Jets}
    (hF : Supported H F) (hG : Supported H G) : Supported H (F - G) := by
  intro m hm
  rcases mem_union.mp (MvPolynomial.support_sub _ _ _ hm) with hm | hm
  · exact hF m hm
  · exact hG m hm
theorem supported_C_mul {H : Shape} {F : Jets} (hF : Supported H F)
    (a : GeometricX) : Supported H (MvPolynomial.C a * F) := by
  intro m hm
  apply hF m
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  rw [MvPolynomial.coeff_C_mul] at hm
  exact right_ne_zero_of_mul hm
theorem supported_C (H : Shape) (a : GeometricX) : Supported H (MvPolynomial.C a) := by
  classical
  by_cases ha : a = 0
  · simp [ha, Supported]
  intro m hm
  rw [MvPolynomial.support_C, ite_eq_right (fun h => (ha h).elim), mem_singleton] at hm
  subst m
  simp
theorem supported_X {H : Shape} (hb : 1 ≤ H.b) (hj : 3 ≤ H.j) (ht : 1 ≤ H.t)
    (i : Fin 4) : Supported H (MvPolynomial.X i) := by
  intro m hm
  rw [MvPolynomial.support_X, mem_singleton] at hm
  subst m
  have hi : i.val ≤ H.j := (show i.val ≤ 3 by omega).trans hj
  refine ⟨by simpa, by simpa, ?_⟩
  simpa only [Finsupp.single_apply] using (show (if i = (3 : Fin 4) then 1 else 0) ≤ H.t by
    split <;> omega)
theorem exists_coordinate_cut {r : PrimeSpectrum Jets} {y : JetPoint}
    (h : r.asIdeal < jetPointIdeal y) :
    ∃ i : Fin 4, MvPolynomial.X i - MvPolynomial.C (y i) ∉ r.asIdeal := by
  by_contra! hmem
  let π := Ideal.Quotient.mk r.asIdeal
  have hmaps : π = π.comp (MvPolynomial.C.comp (MvPolynomial.eval y)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      have heq := Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
      rw [map_sub, sub_eq_zero] at heq
      simpa using heq
  apply not_le_of_gt h
  intro F hF
  have hz : MvPolynomial.eval y F = 0 := RingHom.mem_ker.mp hF
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π F = 0
  calc
    π F = π (MvPolynomial.C (MvPolynomial.eval y F)) := RingHom.congr_fun hmaps F
    _ = 0 := by rw [hz, map_zero, map_zero]
theorem jetPoint_injective : Function.Injective jetPoint := by
  intro S T h
  have h0 := congrFun h (0 : Fin 4)
  have hi : Function.Injective genericCoeff :=
    (algebraMap GenericX GeometricX).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericX)
  exact hi (by simpa [jetPoint, jet, Polynomial.hasseDeriv_zero'] using h0)
theorem chart_section {H : Shape} (C : ValueChart H) (i : I) (a : K) :
    Supported H (C.numerator i - MvPolynomial.C (constantCoeff a) * C.denominator) :=
  supported_sub (C.numerator_supported i) (supported_C_mul C.denominator_supported _)
theorem eval_chart_section {H : Shape} {C : ValueChart H} {S : (Polynomial K)}
    (hS : C.recovers S) (i : I) (a : K) :
    MvPolynomial.eval (jetPoint (extend S))
        (C.numerator i - MvPolynomial.C (constantCoeff a) * C.denominator) = 0 ↔
      S.eval (node i) = a := by
  have hinj : Function.Injective constantCoeff := constantCoeff.injective
  rw [map_sub, map_mul, MvPolynomial.eval_C, hS.2 i, sub_eq_zero]
  exact ⟨fun h => hinj (mul_right_cancel₀ hS.1 h), fun h => by rw [h]⟩
theorem weighted_ceil (weight gain gap : ℕ) {n a b capA capB : ℕ}
    (hpos : 0 < weight * gap) (h : gap * n ≤ gain * a + gap * b)
    (ha : weight * a ≤ capA) (hb : weight * b ≤ capB) :
    n ≤ ceilDiv (gain * capA + gap * capB) (weight * gap) := by
  have hscaled : n * (weight * gap) ≤ gain * capA + gap * capB := calc
    _ = weight * (gap * n) := by ac_rfl
    _ ≤ weight * (gain * a + gap * b) := Nat.mul_le_mul_left _ h
    _ = gain * (weight * a) + gap * (weight * b) := by
      rw [Nat.mul_add]
      congr 1 <;> ac_rfl
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ ha) (Nat.mul_le_mul_left _ hb)
  unfold ceilDiv
  exact (Nat.le_div_iff_mul_le hpos).mpr (by omega)
end
end K1_13_7_5
end
section
namespace K1_13_7_5_3
noncomputable section
open K1_13 K1_13_7_1 K1_13_7_5
open scoped BigOperators Pointwise
def SectionPoints (r : PrimeSpectrum Jets) (D : Jets) (T : Finset JetPoint) : Prop :=
  D ∉ r.asIdeal ∧ ∀ y ∈ T, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y D = 0
def pointPrime (y : JetPoint) : PrimeSpectrum Jets :=
  ⟨jetPointIdeal y, RingHom.ker_isPrime (MvPolynomial.eval y)⟩
def cutIdeal (J : Ideal Jets) (D : Jets) : Ideal Jets :=
  J ⊔ Ideal.span {D}
def IsolatedLengthGE (J : Ideal Jets) (m : ℕ) (y : JetPoint) : Prop :=
  jetPointIdeal y ∈ J.minimalPrimes ∧ (m : ℕ∞) ≤ liftLength (pointPrime y) J
def CurveOpen (J : Ideal Jets) (r : PrimeSpectrum Jets) (a : Jets) : Prop :=
  a ∉ r.asIdeal ∧
  (∀ q ∈ J.minimalPrimes, q ≠ r.asIdeal → a ∈ q) ∧
  ∀ D : Jets, D ∉ r.asIdeal →
    ∀ y : JetPoint, r.asIdeal ≤ jetPointIdeal y → MvPolynomial.eval y a ≠ 0 →
      MvPolynomial.eval y D = 0 →
      jetPointIdeal y ∈ (cutIdeal J D).minimalPrimes ∧
      liftLength r J ≤ liftLength (pointPrime y) (cutIdeal J D)
abbrev RealJets := Fin 4 → ℝ
def capBody (p : Shape) : Set RealJets :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ p.b ∧
    (∑ i : Fin 4, (i.val : ℝ) * x i) ≤ p.j ∧ x 3 ≤ p.t}
def capVolume (x : Set RealJets) : ℝ :=
  (MeasureTheory.volume x).toReal
def capDifference (F : Set RealJets → ℝ) (a x : Set RealJets) : ℝ :=
  F (x + a) - F x
def capMixed (p q r s : Shape) : ℝ :=
  capDifference (capDifference (capDifference (capDifference capVolume (capBody p))
    (capBody q)) (capBody r)) (capBody s) {0}
theorem capBody_zero : capBody ⟨0, 0, 0⟩ = ({0} : Set RealJets) := by
  ext x
  constructor
  · intro hx
    have hsum : (∑ i, x i) ≤ 0 := by simpa using hx.2.1
    apply Set.mem_singleton_iff.mpr
    funext i
    have hle : x i ≤ ∑ k, x k :=
      Finset.single_le_sum (fun k _ => hx.1 k) (Finset.mem_univ i)
    exact le_antisymm (hle.trans hsum) (hx.1 i)
  · intro hx
    rw [Set.mem_singleton_iff.mp hx]
    simp [capBody]
private theorem mem_capBody (p : Shape) (x : RealJets) :
    x ∈ capBody p ↔ (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 + x 3 ≤ p.b ∧
      x 1 + 2 * x 2 + 3 * x 3 ≤ p.j ∧ x 3 ≤ p.t := by
  norm_num [capBody, Fin.sum_univ_four]
private theorem sub_min_le {x a b : ℝ} (hb : 0 ≤ b) (hx : x ≤ a + b) :
    x - min x a ≤ b := by
  rw [min_def]
  split <;> linarith
theorem capBody_plus (p q : Shape) (hp : Chamber p) (hq : Chamber q) :
    capBody (p.plus q) = capBody p + capBody q := by
  ext x
  rw [mem_capBody]
  change _ ↔ ∃ u ∈ capBody p, ∃ v ∈ capBody q, u + v = x
  constructor
  · rintro ⟨hx, htotal, hindex, htop⟩
    simp only [Shape.plus, Nat.cast_add] at htotal hindex htop
    have hpj : (p.j : ℝ) ≤ p.b := by exact_mod_cast hp.1
    have hqj : (q.j : ℝ) ≤ q.b := by exact_mod_cast hq.1
    have hpt : 3 * (p.t : ℝ) ≤ p.j := by exact_mod_cast hp.2
    have hqt : 3 * (q.t : ℝ) ≤ q.j := by exact_mod_cast hq.2
    let u3 := min (x 3) (p.t : ℝ)
    let v3 := x 3 - u3
    have hu3 : 0 ≤ u3 := le_min (hx 3) (Nat.cast_nonneg _)
    have hpu3 : u3 ≤ p.t := min_le_right _ _
    have hv3 : 0 ≤ v3 := sub_nonneg.mpr (min_le_left _ _)
    have hqv3 : v3 ≤ q.t := sub_min_le (Nat.cast_nonneg _) htop
    let jp := (p.j : ℝ) - 3 * u3
    let jq := (q.j : ℝ) - 3 * v3
    have hjp : 0 ≤ jp := by dsimp only [jp]; linarith
    have hjq : 0 ≤ jq := by dsimp only [jq]; linarith
    have hcharge : x 1 + 2 * x 2 ≤ jp + jq := by
      dsimp only [jp, jq, v3]
      linarith
    let u1 := min (x 1) jp
    let u2 := min (x 2) ((jp - u1) / 2)
    have hu1 : 0 ≤ u1 := le_min (hx 1) hjp
    have hpu1 : u1 ≤ jp := min_le_right _ _
    have hu2 : 0 ≤ u2 := le_min (hx 2) (by linarith)
    have hv1 : 0 ≤ x 1 - u1 := sub_nonneg.mpr (min_le_left _ _)
    have hv2 : 0 ≤ x 2 - u2 := sub_nonneg.mpr (min_le_left _ _)
    have hspent : u1 + 2 * u2 = min (x 1 + 2 * x 2) jp := by
      dsimp only [u1, u2]
      simp only [min_def]
      split_ifs <;> linarith [hx 2]
    have hpu : u1 + 2 * u2 ≤ jp := hspent.le.trans (min_le_right _ _)
    have hqv : (x 1 - u1) + 2 * (x 2 - u2) ≤ jq := by
      linarith [sub_min_le hjq hcharge]
    dsimp only [jp] at hpu
    dsimp only [jq] at hqv
    let bp := (p.b : ℝ) - u3 - u1 - u2
    let bq := (q.b : ℝ) - v3 - (x 1 - u1) - (x 2 - u2)
    have hbp : 0 ≤ bp := by dsimp only [bp]; linarith
    have hbq : 0 ≤ bq := by dsimp only [bq]; linarith
    have hfree : x 0 ≤ bp + bq := by dsimp only [bp, bq, v3]; linarith
    let u0 := min (x 0) bp
    have hu0 : 0 ≤ u0 := le_min (hx 0) hbp
    have hv0 : 0 ≤ x 0 - u0 := sub_nonneg.mpr (min_le_left _ _)
    have hpu0 : u0 ≤ bp := min_le_right _ _
    have hqv0 : x 0 - u0 ≤ bq := sub_min_le hbq hfree
    dsimp only [bp] at hpu0
    dsimp only [bq] at hqv0
    let u : RealJets := ![u0, u1, u2, u3]
    let v : RealJets := x - u
    refine ⟨u, (mem_capBody p u).mpr ?_, v, (mem_capBody q v).mpr ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, hpu3⟩
      · intro i
        fin_cases i <;> assumption
      · change u0 + u1 + u2 + u3 ≤ (p.b : ℝ)
        linarith
      · change u1 + 2 * u2 + 3 * u3 ≤ (p.j : ℝ)
        linarith
    · refine ⟨?_, ?_, ?_, hqv3⟩
      · intro i
        fin_cases i <;> assumption
      · change (x 0 - u0) + (x 1 - u1) + (x 2 - u2) + v3 ≤ (q.b : ℝ)
        linarith
      · change (x 1 - u1) + 2 * (x 2 - u2) + 3 * v3 ≤ (q.j : ℝ)
        linarith
    · change u + (x - u) = x
      abel
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨hu, hub, huj, hut⟩ := (mem_capBody p u).mp hu
    obtain ⟨hv, hvb, hvj, hvt⟩ := (mem_capBody q v).mp hv
    refine ⟨fun i => add_nonneg (hu i) (hv i), ?_, ?_, ?_⟩ <;>
      simp only [Pi.add_apply, Shape.plus, Nat.cast_add] <;> linarith
end
end K1_13_7_5_3
end
section
namespace K1_13_7_5_3
noncomputable section
open K1_13 K1_13_7 K1_13_7_1 K1_13_7_5
open scoped BigOperators Pointwise
def c1 : Prop :=
  ∀ H : Shape, (∀ i : Fin 4, Supported H (MvPolynomial.X i)) →
    ∀ (R : Finset (PrimeSpectrum Jets)), (∀ r ∈ R, r.asIdeal.height = 3) →
    ∀ (guard : PrimeSpectrum Jets → Jets), (∀ r ∈ R, guard r ∉ r.asIdeal) →
    ∀ (cut : PrimeSpectrum Jets → Jets) (points : PrimeSpectrum Jets → Finset JetPoint),
      (∀ r ∈ R, Supported H (cut r) ∧ SectionPoints r (cut r) (points r)) →
      ∃ (D : Jets) (selected : PrimeSpectrum Jets → Finset JetPoint),
        Supported H D ∧
        ∀ r ∈ R, (points r).card ≤ (selected r).card ∧ SectionPoints r D (selected r) ∧
          ∀ y ∈ selected r, MvPolynomial.eval y (guard r) ≠ 0
def c2 : Prop :=
  ∀ (J : Ideal Jets) (r : PrimeSpectrum Jets),
    r.asIdeal ∈ J.minimalPrimes → r.asIdeal.height = 3 → liftLength r J < ⊤ →
    ∃ a : Jets, CurveOpen J r a
def c3 : Prop :=
  ∀ (p q H : Shape), Chamber p → Chamber q → Chamber H →
    ∀ (F G L D : Jets), Supported p F → Supported q G → Supported q L → Supported H D →
      ∀ (m : ℕ) (points : Finset JetPoint),
        (∀ y ∈ points, IsolatedLengthGE (cutIdeal (Ideal.span {F, G, L}) D) m y) →
        ((32 * m * points.card : ℕ) : ℝ) ≤ 32 * capMixed p q q H
def c4 : Prop :=
  ∀ p : Shape, Chamber p → 32 * capVolume (capBody p) = (volume32 p : ℝ)
theorem supported_anchor (f : Row 4) : Supported (shape f).chamber (geometricFactor f) := by
  intro m hm
  have hm' : m ∈ f.support := MvPolynomial.support_map_subset genericCoeff f hm
  refine ⟨(MvPolynomial.le_totalDegree hm').trans (le_max_left _ _), ?_,
    MvPolynomial.le_degreeOf_of_mem_support 3 hm'⟩
  exact Finset.le_sup (f := fun m : Fin 4 →₀ ℕ => m.sum (fun i a => i.val * a)) hm'
theorem supported_lower {P : Row 3} (hP : LowerCaps P lowerBox.b lowerBox.j) :
    Supported lowerBox (liftRow P) := by
  classical
  intro m hm
  change m ∈ (MvPolynomial.rename Fin.castSucc (genericRow P)).support at hm
  rw [MvPolynomial.support_rename_of_injective (Fin.castSucc_injective 3), Finset.mem_image] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  have hn' : n ∈ P.support := MvPolynomial.support_map_subset genericCoeff P hn
  refine ⟨?_, ?_, ?_⟩
  · rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact (MvPolynomial.le_totalDegree hn').trans hP.1
  · rw [Finsupp.sum_mapDomain_index (fun _ => Nat.mul_zero _) (fun _ _ _ => Nat.mul_add ..)]
    exact (Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => m.sum (fun i a => i.val * a)) hn').trans hP.2
  · have hlast : (3 : Fin 4) ∉ Set.range (@Fin.castSucc 3) := by
      rintro ⟨i, hi⟩
      exact Fin.castSucc_ne_last i hi
    exact (Finsupp.mapDomain_of_notMem_range n _ hlast).le
theorem supported_coordinate {H : Shape} (hc : Chamber H) (ht : 1 ≤ H.t)
    (i : Fin 4) : Supported H (MvPolynomial.X i) := by
  obtain ⟨hb, hj⟩ := hc
  have hi : i.val ≤ 3 := by omega
  intro m hm
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst m
  refine ⟨by simpa using (show 1 ≤ H.b by omega), by simpa using (show i.val ≤ H.j by omega), ?_⟩
  simpa only [Finsupp.single_apply] using
    (show (if i = (3 : Fin 4) then 1 else 0) ≤ H.t by split <;> omega)
private theorem chamber_plus {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    Chamber (p.plus q) := by
  obtain ⟨hb, hj⟩ := hp
  obtain ⟨hb', hj'⟩ := hq
  change p.j + q.j ≤ p.b + q.b ∧ 3 * (p.t + q.t) ≤ p.j + q.j
  omega
private theorem difference_matches {a : Shape} (ha : Chamber a)
    {F : Set RealJets → ℝ} {G : Shape → ℤ}
    (h : ∀ x, Chamber x → 32 * F (capBody x) = (G x : ℝ)) :
    ∀ x, Chamber x →
      32 * capDifference F (capBody a) (capBody x) = (difference G a x : ℝ) := by
  intro x hx
  rw [capDifference, mul_sub, ← capBody_plus x a hx ha, h _ (chamber_plus hx ha), h x hx]
  simp [difference]
theorem mixed_matches (hvol : c4) {p q r s : Shape}
    (hp : Chamber p) (hq : Chamber q) (hr : Chamber r) (hs : Chamber s) :
    32 * capMixed p q r s =
      (difference (difference (difference (difference volume32 p) q) r) s ⟨0, 0, 0⟩ : ℝ) := by
  unfold capMixed
  rw [← capBody_zero]
  exact difference_matches hs
    (difference_matches hr (difference_matches hq (difference_matches hp hvol)))
      ⟨0, 0, 0⟩ ⟨le_rfl, le_rfl⟩
end
end K1_13_7_5_3
end
section
namespace K1_13_7_5_3_3
noncomputable section
open K1_13 K1_13_7_5 K1_13_7_5_3
open scoped BigOperators
abbrev Exponent := K1_13_5_4_2_4.Exponent
def Fits (s : Shape) (a : Exponent) : Prop :=
  (∑ i, a i) ≤ s.b ∧ (∑ i : Fin 4, i.val * a i) ≤ s.j ∧ a 3 ≤ s.t
def doubledSupport (s : Shape) : Finset Exponent :=
  ((Finsupp.finite_of_degree_le (s.scale 2).b).subset
    (show {a | Fits (s.scale 2) a} ⊆ {a | a.degree ≤ (s.scale 2).b} by
      intro a ha
      change a.degree ≤ (s.scale 2).b
      rw [Finsupp.degree_eq_sum]
      exact ha.1)).toFinset
def supports (p q H : Shape) : Fin 4 → Finset Exponent :=
  ![doubledSupport p, doubledSupport q, doubledSupport q, doubledSupport H]
abbrev PointLocal (y : JetPoint) := Localization.AtPrime (pointPrime y).asIdeal
end
end K1_13_7_5_3_3
end
section
namespace K1_13_7_5_1
open Polynomial K1_13 K1_13_7 K1_13_7_5
noncomputable section
def lastJetEquiv (R : Type*) [CommSemiring R] :
    MvPolynomial (Fin 4) R ≃ₐ[R] (Polynomial (MvPolynomial (Fin 3) R)) :=
  (MvPolynomial.renameEquiv R finSuccEquivLast).trans (MvPolynomial.optionEquivLeft R (Fin 3))
private theorem lastJetEquiv_C {R : Type*} [CommSemiring R] (a : R) :
    lastJetEquiv R (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  simp [lastJetEquiv, MvPolynomial.algebraMap_eq]
private theorem lastJetEquiv_X_last {R : Type*} [CommSemiring R] :
    lastJetEquiv R (MvPolynomial.X (3 : Fin 4)) = Polynomial.X := by
  change MvPolynomial.optionEquivLeft R (Fin 3)
    (MvPolynomial.rename finSuccEquivLast (MvPolynomial.X (Fin.last 3))) = _
  rw [MvPolynomial.rename_X, finSuccEquivLast_last, MvPolynomial.optionEquivLeft_X_none]
private theorem lastJetEquiv_X_lower {R : Type*} [CommSemiring R] (i : Fin 3) :
    lastJetEquiv R (MvPolynomial.X i.castSucc) = Polynomial.C (MvPolynomial.X i) := by
  simp [lastJetEquiv]
theorem lastJetEquiv_rename {R : Type*} [CommSemiring R] (P : MvPolynomial (Fin 3) R) :
    lastJetEquiv R (MvPolynomial.rename Fin.castSucc P) = Polynomial.C P := by
  have h : (lastJetEquiv R).toRingHom.comp (MvPolynomial.rename Fin.castSucc).toRingHom =
      Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lastJetEquiv_C]
    · intro i
      simp [lastJetEquiv_X_lower]
  exact RingHom.congr_fun h P
private theorem lastJetEquiv_natDegree {R : Type*} [CommSemiring R] (F : MvPolynomial (Fin 4) R) :
    (lastJetEquiv R F).natDegree = F.degreeOf (Fin.last 3) := by
  change (MvPolynomial.optionEquivLeft R (Fin 3) (MvPolynomial.rename finSuccEquivLast F)).natDegree = _
  rw [MvPolynomial.natDegree_optionEquivLeft, ← finSuccEquivLast_last,
    MvPolynomial.degreeOf_rename_of_injective finSuccEquivLast.injective]
def polynomialPoint (y : JetPoint) : (Polynomial Lower) →+* GeometricX :=
  Polynomial.eval₂RingHom (MvPolynomial.eval (y ∘ Fin.castSucc)) (y (Fin.last 3))
theorem polynomialPoint_comp (y : JetPoint) :
    (polynomialPoint y).comp (lastJetEquiv GeometricX).toRingHom = MvPolynomial.eval y := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [polynomialPoint, lastJetEquiv_C]
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [polynomialPoint, lastJetEquiv_X_last]
    · simp [polynomialPoint, lastJetEquiv_X_lower]
def upperPolynomial (f : Row 4) : (Polynomial Lower) :=
  lastJetEquiv GeometricX (geometricFactor f)
private theorem genericCoeff_injective : Function.Injective genericCoeff :=
  (algebraMap GenericX GeometricX).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericX)
private theorem upperPolynomial_natDegree (f : Row 4) :
    (upperPolynomial f).natDegree = (shape f).t := by
  change (lastJetEquiv GeometricX (MvPolynomial.map genericCoeff f)).natDegree =
    f.degreeOf (Fin.last 3)
  rw [lastJetEquiv_natDegree, MvPolynomial.degreeOf_eq_sup, MvPolynomial.degreeOf_eq_sup,
    MvPolynomial.support_map_of_injective _ genericCoeff_injective]
theorem upperPolynomial_vanishes {f : Row 4} {S : (Polynomial Geom)} (hf : OnFactor f S) :
    polynomialPoint (jetPoint S) (upperPolynomial f) = 0 := by
  change ((polynomialPoint (jetPoint S)).comp (lastJetEquiv GeometricX).toRingHom)
    (geometricFactor f) = 0
  rw [polynomialPoint_comp, geometricFactor, MvPolynomial.eval_map]
  change MvPolynomial.eval₂ genericCoeff (fun i : Fin 4 => genericCoeff (jet S i)) f = 0
  rw [show MvPolynomial.eval₂ genericCoeff
      (fun i : Fin 4 => genericCoeff (jet S i)) f = genericCoeff (atJet f S) from
    (MvPolynomial.hom_eval₂ f (RingHom.id _) genericCoeff (jet S)).symm,
    hf.1, map_zero]
theorem upperPolynomial_lead_nonzero {f : Row 4} {S : (Polynomial Geom)} (hf : OnFactor f S) :
    MvPolynomial.eval (lowerPoint S) (upperPolynomial f).leadingCoeff ≠ 0 := by
  have h : (Polynomial.mapRingHom (MvPolynomial.eval (lowerPoint S))).comp
      ((lastJetEquiv GeometricX).toRingHom.comp (MvPolynomial.map genericCoeff)) =
    (Polynomial.mapRingHom genericCoeff).comp
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i : Fin 4 => if i = 3 then Polynomial.X else Polynomial.C (jet S i))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lastJetEquiv_C]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [lastJetEquiv_X_last, show Fin.last 3 = (3 : Fin 4) by decide]
      · have hj : j.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last j
        simp [lastJetEquiv_X_lower, hj, lowerPoint, jet]
  rw [Polynomial.leadingCoeff, upperPolynomial_natDegree]
  have hc := congrArg (fun p : (Polynomial GeometricX) => p.coeff (shape f).t) (RingHom.congr_fun h f)
  change ((upperPolynomial f).map (MvPolynomial.eval (lowerPoint S))).coeff (shape f).t =
    ((MvPolynomial.eval₂ Polynomial.C
      (fun i : Fin 4 => if i = 3 then Polynomial.X else Polynomial.C (jet S i)) f).map
      genericCoeff).coeff (shape f).t at hc
  rw [Polynomial.coeff_map, Polynomial.coeff_map] at hc
  rw [hc]
  exact (map_ne_zero_iff _ genericCoeff_injective).mpr hf.2
end
end K1_13_7_5_1
end
section
namespace K1_13_7_5_1
open Polynomial K1_13 K1_13_7 K1_13_7_5
noncomputable section
def lowerInclusion : Lower →+* Jets :=
  (MvPolynomial.rename Fin.castSucc).toRingHom
abbrev chartRing (f : Row 4) := LeadingChart (upperPolynomial f)
def hypersurfaceMap (f : Row 4) : Jets →+* AdjoinRoot (upperPolynomial f) :=
  (AdjoinRoot.mk (upperPolynomial f)).comp (lastJetEquiv GeometricX).toRingHom
def chartMap (f : Row 4) : Jets →+* chartRing f :=
  (algebraMap (AdjoinRoot (upperPolynomial f)) (chartRing f)).comp (hypersurfaceMap f)
theorem chartMap_comp_lower (f : Row 4) :
    (chartMap f).comp lowerInclusion = algebraMap Lower (chartRing f) := by
  apply RingHom.ext
  intro x
  change algebraMap (AdjoinRoot (upperPolynomial f)) (chartRing f)
    (AdjoinRoot.mk (upperPolynomial f)
      (lastJetEquiv GeometricX (MvPolynomial.rename Fin.castSucc x))) = _
  rw [lastJetEquiv_rename]
  rfl
theorem chartMap_factor (f : Row 4) : chartMap f (geometricFactor f) = 0 := by
  change algebraMap (AdjoinRoot (upperPolynomial f)) (chartRing f)
    (AdjoinRoot.mk (upperPolynomial f) (upperPolynomial f)) = 0
  rw [AdjoinRoot.mk_self, map_zero]
theorem liftIdeal_eq (f : Row 4) (P Q : Row 3) :
    liftIdeal f P Q = Ideal.span {geometricFactor f} ⊔ (pairIdeal P Q).map lowerInclusion := by
  rw [pairIdeal, Ideal.map_span, ← Ideal.span_union, Set.image_pair,
    Set.singleton_union]
  rfl
theorem chartMap_liftIdeal (f : Row 4) (P Q : Row 3) :
    (liftIdeal f P Q).map (chartMap f) = (pairIdeal P Q).map (algebraMap Lower (chartRing f)) := by
  rw [liftIdeal_eq, Ideal.map_sup, Ideal.map_span, Set.image_singleton, chartMap_factor,
    Ideal.span_singleton_zero, bot_sup_eq, Ideal.map_map, chartMap_comp_lower]
private theorem hypersurfaceMap_ker (f : Row 4) :
    RingHom.ker (hypersurfaceMap f) = Ideal.span {geometricFactor f} := by
  let e := (lastJetEquiv GeometricX).toRingEquiv
  change RingHom.ker ((Ideal.Quotient.mk (Ideal.span {upperPolynomial f})).comp e.toRingHom) = _
  rw [← RingHom.comap_ker, Ideal.mk_ker,
    show ({upperPolynomial f} : Set (Polynomial Lower)) = e.toRingHom '' {geometricFactor f} by
      simp [e, upperPolynomial],
    ← Ideal.map_span, Ideal.comap_map_of_bijective e.toRingHom e.bijective]
theorem hypersurfaceMap_surjective (f : Row 4) :
    Function.Surjective (hypersurfaceMap f) :=
  (AdjoinRoot.mk_surjective (g := upperPolynomial f)).comp (lastJetEquiv GeometricX).surjective
private theorem chart_minimalPrime {f : Row 4} {P Q : Row 3} {p : Ideal (chartRing f)}
    (hp : p ∈ ((liftIdeal f P Q).map (chartMap f)).minimalPrimes) :
    p.comap (chartMap f) ∈ (liftIdeal f P Q).minimalPrimes := by
  let F := upperPolynomial f
  let J := liftIdeal f P Q
  let v := hypersurfaceMap f
  let k := algebraMap (AdjoinRoot F) (chartRing f)
  have hk : p.comap k ∈ (J.map v).minimalPrimes := by
    change p ∈ Ideal.under (AdjoinRoot F) ⁻¹' (J.map v).minimalPrimes
    rw [← IsLocalization.minimalPrimes_map (Submonoid.powers (AdjoinRoot.of F F.leadingCoeff)),
      Ideal.map_map]
    exact hp
  have hm := Ideal.minimalPrimes_comap_of_surjective (hypersurfaceMap_surjective f) hk
  have hker : RingHom.ker v ≤ J := by
    change RingHom.ker (hypersurfaceMap f) ≤ liftIdeal f P Q
    rw [hypersurfaceMap_ker, liftIdeal_eq]
    exact le_sup_left
  change (p.comap k).comap v ∈ J.minimalPrimes
  rwa [Ideal.comap_map_of_surjective v (hypersurfaceMap_surjective f),
    ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker] at hm
private theorem chart_point {f : Row 4} {S : (Polynomial Geom)} (hf : OnFactor f S) :
    ∃ ev : chartRing f →+* GeometricX, ev.comp (chartMap f) = MvPolynomial.eval (jetPoint S) := by
  let F := upperPolynomial f
  let y := jetPoint S
  let x := MvPolynomial.eval (lowerPoint S)
  let z := y (Fin.last 3)
  have hz : F.eval₂ x z = 0 := upperPolynomial_vanishes hf
  let v : AdjoinRoot F →+* GeometricX := AdjoinRoot.lift x z hz
  have hunit : IsUnit (v (AdjoinRoot.of F F.leadingCoeff)) := by
    change IsUnit (AdjoinRoot.lift x z hz (AdjoinRoot.of F F.leadingCoeff))
    rw [AdjoinRoot.lift_of]
    exact isUnit_iff_ne_zero.mpr (upperPolynomial_lead_nonzero hf)
  let ev : chartRing f →+* GeometricX := IsLocalization.Away.lift _ hunit
  refine ⟨ev, ?_⟩
  rw [← polynomialPoint_comp y]
  apply RingHom.ext
  intro G
  change ev (algebraMap (AdjoinRoot F) (chartRing f)
    (AdjoinRoot.mk F (lastJetEquiv GeometricX G))) =
      polynomialPoint y (lastJetEquiv GeometricX G)
  rw [show ∀ t, ev (algebraMap (AdjoinRoot F) (chartRing f) t) = v t from
    IsLocalization.Away.lift_eq _ _]
  exact AdjoinRoot.lift_mk hz _
private theorem chart_eval_lower (S : (Polynomial Geom)) :
    (MvPolynomial.eval (jetPoint S)).comp lowerInclusion = MvPolynomial.eval (lowerPoint S) := by
  apply RingHom.ext
  intro x
  exact MvPolynomial.eval_rename Fin.castSucc (jetPoint S) x
theorem exists_ambient_component {f : Row 4} {P Q : Row 3} {S : (Polynomial Geom)}
    (hf : OnFactor f S) {q : PrimeSpectrum Lower}
    (hq : q.asIdeal ∈ (pairIdeal P Q).minimalPrimes) (hy : q.asIdeal ≤ pointIdeal (lowerPoint S)) :
    ∃ p : PrimeSpectrum (chartRing f), p.asIdeal.LiesOver q.asIdeal ∧
      p.asIdeal.comap (chartMap f) ∈ (liftIdeal f P Q).minimalPrimes ∧
      p.asIdeal.comap (chartMap f) ≤ jetPointIdeal (jetPoint S) := by
  let D := chartRing f
  have hlead := upperPolynomial_lead_nonzero hf
  let : Module.Flat Lower D := leadingChart_flat _ (fun h => hlead (by rw [h, map_zero]))
  obtain ⟨ev, hev⟩ := chart_point hf
  let M := RingHom.ker ev
  have : M.IsPrime := RingHom.ker_isPrime ev
  have : (pointIdeal (lowerPoint S)).IsPrime := RingHom.ker_isPrime _
  have : M.LiesOver (pointIdeal (lowerPoint S)) := ⟨by
    change RingHom.ker (MvPolynomial.eval (lowerPoint S)) =
      (RingHom.ker ev).comap (algebraMap Lower D)
    rw [RingHom.comap_ker, ← chartMap_comp_lower, ← RingHom.comp_assoc, hev, chart_eval_lower]⟩
  obtain ⟨p₀, hp₀M, hp₀, hover⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := q.asIdeal) (q := pointIdeal (lowerPoint S)) M hy
  let J := (liftIdeal f P Q).map (chartMap f)
  have hJ : J ≤ p₀ := by
    change (liftIdeal f P Q).map (chartMap f) ≤ p₀
    rw [chartMap_liftIdeal, Ideal.map_le_iff_le_comap]
    change pairIdeal P Q ≤ p₀.under Lower
    rw [← hover.over]
    exact hq.le
  obtain ⟨p, hp, hpp₀⟩ := Ideal.exists_minimalPrimes_le hJ
  have hc : p.under Lower = q.asIdeal := by
    have hle : p.under Lower ≤ q.asIdeal := (Ideal.comap_mono hpp₀).trans_eq hover.over.symm
    have hpair : pairIdeal P Q ≤ p.under Lower := by
      rw [Ideal.under_def, ← Ideal.map_le_iff_le_comap, ← chartMap_liftIdeal]
      exact hp.le
    exact le_antisymm hle (hq.2 ⟨hp.isPrime.comap _, hpair⟩ hle)
  refine ⟨⟨p, hp.isPrime⟩, ⟨hc.symm⟩, chart_minimalPrime hp, ?_⟩
  change p.comap (chartMap f) ≤ RingHom.ker (MvPolynomial.eval (jetPoint S))
  rw [← hev, ← RingHom.comap_ker]
  exact Ideal.comap_mono (hpp₀.trans hp₀M)
private theorem eval_height {k : Type*} [Field k] :
    ∀ n (y : Fin n → k), (RingHom.ker (MvPolynomial.eval y)).height = n := by
  intro n
  induction n with
  | zero =>
    intro y
    rw [show RingHom.ker (MvPolynomial.eval y) = ⊥ by
      ext G
      simp only [RingHom.mem_ker, Ideal.mem_bot]
      constructor
      · obtain ⟨a, rfl⟩ := (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.surjective G
        simp
      · rintro rfl; simp]
    simp
  | succ n ih =>
    intro y
    let e := MvPolynomial.finSuccEquiv k n
    let l := MvPolynomial.eval (fun i : Fin n => y i.succ)
    let v := Polynomial.eval₂RingHom l (y 0)
    have hv : v.comp e.toRingHom = MvPolynomial.eval y := by
      apply RingHom.ext
      intro G
      change Polynomial.eval₂ l (y 0) (e G) = MvPolynomial.eval y G
      rw [← Polynomial.eval_map, ← MvPolynomial.eval_eq_eval_mv_eval']
      exact congrArg (fun z => MvPolynomial.eval z G) (Fin.cons_self_tail y)
    let p := RingHom.ker l
    let M := RingHom.ker v
    have : M.IsMaximal := RingHom.ker_isMaximal_of_surjective v (fun a =>
      ⟨Polynomial.C (MvPolynomial.C a), by simp [v, l]⟩)
    have : M.LiesOver p := ⟨by
      change RingHom.ker l = (RingHom.ker v).comap Polynomial.C
      rw [RingHom.comap_ker, show v.comp Polynomial.C = l from Polynomial.eval₂RingHom_comp_C _ _]⟩
    rw [← hv, ← RingHom.comap_ker]
    change (M.comap e.toRingEquiv).height = _
    rw [e.toRingEquiv.height_comap, Polynomial.height_eq_height_add_one p M,
      show p.height = n from ih _]
    simp
theorem ambient_component_height_and_strict {f : Row 4} {P Q : Row 3} {S : (Polynomial Geom)}
    (hf : OnFactor f S) {q : PrimeSpectrum Lower} (hq : q.asIdeal.height = 2)
    (hy : q.asIdeal ≤ pointIdeal (lowerPoint S)) {r : PrimeSpectrum Jets}
    (hr : r.asIdeal ∈ (liftIdeal f P Q).minimalPrimes)
    (hle : r.asIdeal ≤ jetPointIdeal (jetPoint S))
    (hc : r.asIdeal.comap lowerInclusion = q.asIdeal) :
    r.asIdeal.height = 3 ∧ r.asIdeal < jetPointIdeal (jetPoint S) := by
  let e := (lastJetEquiv GeometricX).toRingEquiv
  let I : Ideal (Polynomial Lower) := q.asIdeal.map Polynomial.C
  let J := I.comap e.toRingHom
  have : I.IsPrime := Ideal.isPrime_map_C_of_isPrime
  have : J.IsPrime := Ideal.IsPrime.comap _
  have he : e.toRingHom.comp lowerInclusion = Polynomial.C := by
    apply RingHom.ext
    exact lastJetEquiv_rename
  have hd : I.under Lower = q.asIdeal := by
    ext x
    change Polynomial.C x ∈ q.asIdeal.map Polynomial.C ↔ x ∈ q.asIdeal
    constructor
    · exact fun h => by simpa using Ideal.mem_map_C_iff.mp h 0
    · exact Ideal.mem_map_of_mem _
  have hJheight : q.asIdeal.height ≤ J.height := by
    change _ ≤ (I.comap e).height
    rw [e.height_comap, ← hd]
    exact Ideal.height_under_le_height (R := Lower) I
  have hJ : J = q.asIdeal.map lowerInclusion := by
    change (q.asIdeal.map Polynomial.C).comap e.toRingHom = _
    rw [← he, ← Ideal.map_map, Ideal.comap_map_of_bijective e.toRingHom e.bijective]
  have hJle : J ≤ r.asIdeal := by
    rw [hJ, Ideal.map_le_iff_le_comap, hc]
  have hproper : J < r.asIdeal := by
    refine lt_of_le_of_ne hJle (fun h => ?_)
    have hmem : upperPolynomial f ∈ I := by
      change geometricFactor f ∈ J
      rw [h]
      exact hr.le (Ideal.subset_span (by simp))
    have ha : (upperPolynomial f).leadingCoeff ∈ q.asIdeal := Ideal.mem_map_C_iff.mp hmem _
    exact upperPolynomial_lead_nonzero hf (RingHom.mem_ker.mp (hy ha))
  have hlow : (3 : ℕ∞) ≤ r.asIdeal.height := by
    have h : q.asIdeal.height + 1 ≤ J.height + 1 := by gcongr
    have h' := h.trans (Ideal.height_add_one_le_of_lt_of_isPrime hproper)
    rw [hq] at h'
    rw [show (3 : ℕ∞) = 2 + 1 by decide]
    exact h'
  have hu : r.asIdeal.height ≤ 3 := by
    have hcard : ({geometricFactor f, liftRow P, liftRow Q} : Set Jets).ncard ≤ 3 :=
      (Set.ncard_insert_le _ _).trans (by
        simpa using Nat.succ_le_succ (Set.ncard_insert_le (liftRow P) {liftRow Q}))
    exact (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hr).trans (by
      exact_mod_cast hcard)
  have ht := le_antisymm hu hlow
  refine ⟨ht, lt_of_le_of_ne hle (fun h => ?_)⟩
  have hpt : (jetPointIdeal (jetPoint S)).height = 4 := eval_height 4 _
  rw [h, hpt] at ht
  exact (by decide : (4 : ℕ∞) ≠ 3) ht
end
end K1_13_7_5_1
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_1
noncomputable section
open K1_13 K1_13_7 K1_13_7_5 MvPolynomial
open scoped Pointwise
def sectionExponents (H : Shape) : Set (Fin 4 →₀ ℕ) :=
  {m | m.degree ≤ H.b ∧ m.sum (fun i a => i.val * a) ≤ H.j ∧ m 3 ≤ H.t}
instance (H : Shape) : Finite (sectionExponents H) :=
  ((Finsupp.finite_of_degree_le H.b).subset
    (fun _ h => h.1 : sectionExponents H ⊆ {m | m.degree ≤ H.b})).to_subtype
abbrev SectionRing (H : Shape) := MvPolynomial (sectionExponents H) GeometricX
abbrev SectionPoint (H : Shape) := sectionExponents H → GeometricX
abbrev sectionMap (H : Shape) := monomialMap GeometricX (sectionExponents H)
theorem supported_iff {H : Shape} {f : Jets} :
    Supported H f ↔ f ∈ restrictSupport GeometricX (sectionExponents H) := by
  rfl
theorem sectionExponents_single {H : Shape} (hH : ∀ i : Fin 4, Supported H (MvPolynomial.X i))
    (i : Fin 4) : Finsupp.single i 1 ∈ sectionExponents H :=
  supported_iff.mp (hH i) (by simp)
theorem supported_sectionMap {H : Shape} {F : SectionRing H} (hF : F.totalDegree ≤ 1) :
    Supported H (sectionMap H F) := by
  have hz : (0 : Fin 4 →₀ ℕ) ∈ sectionExponents H := by simp [sectionExponents]
  have h := monomialMap_mem_restrictSupport_nsmul hz hF
  rw [one_nsmul] at h
  exact supported_iff.mpr h
theorem eval_sectionMap {H : Shape} (y : JetPoint) (F : SectionRing H) :
    eval y (sectionMap H F) = aeval (monomialPoint (sectionExponents H) y) F := by
  simpa only [aeval_eq_eval] using (aeval_monomialPoint y F).symm
theorem base_point_iff (r : PrimeSpectrum Jets) (y : JetPoint) :
    y ∈ zeroLocus GeometricX r.asIdeal ↔ r.asIdeal ≤ jetPointIdeal y := by
  simp only [mem_zeroLocus_iff, aeval_eq_eval, jetPointIdeal]
  rfl
def projectPoint {H : Shape} (hH : ∀ i : Fin 4, Supported H (MvPolynomial.X i)) (z : SectionPoint H) :
    JetPoint := fun i => z ⟨Finsupp.single i 1, sectionExponents_single hH i⟩
theorem monomialPoint_projectPoint {H : Shape} (hH : ∀ i : Fin 4, Supported H (MvPolynomial.X i))
    {r : PrimeSpectrum Jets} {z : SectionPoint H}
    (hz : z ∈ zeroLocus GeometricX (r.asIdeal.comap (sectionMap H))) :
    monomialPoint (sectionExponents H) (projectPoint hH z) = z := by
  have hle : RingHom.ker (sectionMap H) ≤ r.asIdeal.comap (sectionMap H) :=
    fun f hf => show sectionMap H f ∈ r.asIdeal from
      (RingHom.mem_ker.mp hf).symm ▸ r.asIdeal.zero_mem
  obtain ⟨y, hy⟩ := exists_monomialPoint_eq_of_mem_zeroLocus_ker
    (sectionExponents_single hH) (zeroLocus_anti_mono hle hz)
  rw [← hy, show projectPoint hH (monomialPoint (sectionExponents H) y) = y from
    funext fun i => monomialPoint_single y (sectionExponents_single hH i)]
private theorem hilbert_degree_add_height {k σ : Type} [Field k] [Finite σ] :
    ∀ (n : ℕ) (p : PrimeSpectrum (MvPolynomial σ k)), p.asIdeal.height = n →
      (affineHilbertPolynomial p.asIdeal).natDegree + n = Nat.card σ := by
  intro n
  induction n with
  | zero =>
    intro p hp
    rw [Ideal.height_eq_zero_iff_eq_bot.mp hp, Nat.add_zero,
      natDegree_affineHilbertPolynomial_bot]
  | succ n ih =>
    intro p hp
    have hheight : Order.height p = (n : ℕ∞) + 1 := by
      rw [← p.height_eq_orderHeight, hp, Nat.cast_succ]
    obtain ⟨_, ⟨q, hqp, hq⟩, hbound⟩ := Order.height_eq_coe_add_one_iff.mp hheight
    have hnot : ¬ p.asIdeal ≤ q.asIdeal := not_le_of_gt hqp
    obtain ⟨f, hfp, hfq⟩ : ∃ f, f ∈ p.asIdeal ∧ f ∉ q.asIdeal := by
      by_contra! h
      exact hnot h
    have hmin : p.asIdeal ∈ (q.asIdeal ⊔ Ideal.span {f}).minimalPrimes := by
      refine ⟨⟨p.isPrime, sup_le hqp.le ((Ideal.span_singleton_le_iff_mem _).mpr hfp)⟩, ?_⟩
      intro J hJ hJp
      by_contra hn
      let j : PrimeSpectrum (MvPolynomial σ k) := ⟨J, hJ.1⟩
      have hjp : j < p := lt_of_le_not_ge hJp hn
      have hqj : q < j := by
        refine lt_of_le_of_ne (le_sup_left.trans hJ.2) ?_
        intro heq
        have hjmem : f ∈ j.asIdeal := hJ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
        exact hfq ((congrArg PrimeSpectrum.asIdeal heq).symm ▸ hjmem)
      have hstep := Order.height_add_one_le hqj
      rw [hq] at hstep
      have hcontr := hstep.trans (hbound j hjp)
      norm_cast at hcontr
      omega
    let := q.isPrime
    have hcut := principalCut_natDegree_affineHilbertPolynomial_add_one hfq hmin
    have hprev := ih q (q.height_eq_orderHeight.trans hq)
    omega
theorem embedded_hilbert_degree {H : Shape} (hH : ∀ i : Fin 4, Supported H (MvPolynomial.X i))
    (r : PrimeSpectrum Jets) (hr : r.asIdeal.height = 3) :
    (affineHilbertPolynomial (r.asIdeal.comap (sectionMap H))).natDegree = 1 := by
  rw [natDegree_affineHilbertPolynomial_comap_of_surjective (sectionMap H)
    (monomialMap_surjective (sectionExponents_single hH))]
  have h := hilbert_degree_add_height 3 r hr
  rw [Nat.card_fin] at h
  omega
theorem cut_dimension_and_degree {σ : Type} [Finite σ]
    {I : Ideal (MvPolynomial σ GeometricX)} (hp : I.IsPrime)
    (hd : (affineHilbertPolynomial I).natDegree = 1) {f : MvPolynomial σ GeometricX}
    (hf : f ∉ I) {b : ℕ} (hb : f.totalDegree ≤ b) :
    (affineHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree = 0 ∧
      affineDegree (I ⊔ Ideal.span {f}) ≤ (b : ℚ) * affineDegree I := by
  have h := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime hp hf hb
  have hz : (affineHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree = 0 := by
    simpa [hd] using h.1
  exact ⟨hz, by simpa [affineDegree, Polynomial.leadingCoeff, hd, hz] using h.2⟩
theorem old_section_bound {H : Shape} (hH : ∀ i : Fin 4, Supported H (MvPolynomial.X i))
    (r : PrimeSpectrum Jets) (hr : r.asIdeal.height = 3) {f : Jets} {T : Finset JetPoint}
    (hf : Supported H f) (hT : K1_13_7_5_3.SectionPoints r f T) :
    (T.card : ℚ) ≤ affineDegree (r.asIdeal.comap (sectionMap H)) := by
  classical
  let I := r.asIdeal.comap (sectionMap H)
  let F := monomialLift f (supported_iff.mp hf)
  have hF : sectionMap H F = f := monomialMap_monomialLift f (supported_iff.mp hf)
  have hnot : F ∉ I := by
    change sectionMap H F ∉ r.asIdeal
    simpa only [hF] using hT.1
  obtain ⟨hd, hdeg⟩ := cut_dimension_and_degree (r.isPrime.comap (sectionMap H))
    (embedded_hilbert_degree hH r hr) hnot (totalDegree_monomialLift_le_one f (supported_iff.mp hf))
  obtain ⟨hfinite, hbound⟩ := finite_zeroLocus_and_ncard_le_affineDegree
    (K := GeometricX) (I ⊔ Ideal.span {F}) hd
  let embed := monomialPoint (E := GeometricX) (sectionExponents H)
  have hsubset : (T.image embed : Set (SectionPoint H)) ⊆
      zeroLocus GeometricX (I ⊔ Ideal.span {F}) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
    obtain ⟨hcurve, hzero⟩ := hT.2 y hy
    apply mem_zeroLocus_sup_span_singleton_iff.mpr
    refine ⟨(monomialPoint_mem_zeroLocus_comap_iff (sectionExponents_single hH) _ _).mpr
      ((base_point_iff r y).mpr hcurve), ?_⟩
    rw [← eval_sectionMap y F, hF, hzero]
  have hcard := Set.ncard_le_ncard hsubset hfinite
  rw [Set.ncard_coe_finset,
    Finset.card_image_of_injective _ (monomialPoint_injective (sectionExponents_single hH))] at hcard
  exact (Nat.cast_le.mpr hcard).trans (hbound.trans (by simpa using hdeg))
end
end K1_13_7_5_3_1
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_1
noncomputable section
open K1_13 K1_13_7 K1_13_7_5 MvPolynomial
open K1_13_5_4_2_2 (linearForm fiberIdeal projection zeroLocus_fiber_iff
  totalDegree_hyperplane_le_one ncard_eq_affineDegree_of_radical)
def c1 : Prop :=
  ∀ (σ : Type) [Finite σ] (I : Ideal (MvPolynomial σ GeometricX)), I.IsPrime →
    (affineHilbertPolynomial I).natDegree = 1 →
    ∃ bad : Finset (Submodule GeometricX (σ → GeometricX)),
      (∀ B ∈ bad, B ≠ ⊤) ∧
      ∀ (a : σ → GeometricX), (∀ B ∈ bad, a ∉ B) →
        (projection I a).Finite ∧
        ∀ t : GeometricX, (affineHilbertPolynomial (fiberIdeal I a t)).natDegree = 0 ∧
          affineDegree (fiberIdeal I a t) = affineDegree I
def c2 : Prop :=
  ∀ (σ : Type) [Finite σ] (I : Ideal (MvPolynomial σ GeometricX)), I.IsPrime →
    (affineHilbertPolynomial I).natDegree = 1 →
    ∃ B : Submodule GeometricX (σ → GeometricX), B ≠ ⊤ ∧
      ∀ (a : σ → GeometricX), a ∉ B → (projection I a).Finite →
        ∃ bad : Finset GeometricX, ∀ t ∉ bad, (fiberIdeal I a t).IsRadical
private theorem guard_points_finite {H : Shape} (hH : ∀ i : Fin 4, Supported H (MvPolynomial.X i))
    (r : PrimeSpectrum Jets) (hr : r.asIdeal.height = 3)
    (g : Jets) (hg : g ∉ r.asIdeal) :
    {z | z ∈ zeroLocus GeometricX (r.asIdeal.comap (sectionMap H)) ∧
      eval (projectPoint hH z) g = 0}.Finite := by
  obtain ⟨G, hG⟩ := monomialMap_surjective (sectionExponents_single hH) g
  let I := r.asIdeal.comap (sectionMap H)
  have hGnot : G ∉ I := by
    change sectionMap H G ∉ r.asIdeal
    rwa [hG]
  have hcut := (cut_dimension_and_degree (r.isPrime.comap (sectionMap H))
    (embedded_hilbert_degree hH r hr) hGnot le_rfl).1
  refine (finite_zeroLocus_and_ncard_le_affineDegree
    (K := GeometricX) (I ⊔ Ideal.span {G}) hcut).1.subset ?_
  intro z hz
  refine mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hz.1, ?_⟩
  rw [← monomialPoint_projectPoint hH (r := r) hz.1, ← eval_sectionMap, hG]
  exact hz.2
theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_5_3.c1 := by
  classical
  intro H hH R hheight guard hguard cut points hpoints
  let I (r : R) := r.val.asIdeal.comap (sectionMap H)
  have hcurve (r : R) : (I r).IsPrime ∧ (affineHilbertPolynomial (I r)).natDegree = 1 :=
    ⟨r.val.isPrime.comap (sectionMap H), embedded_hilbert_degree hH r.val (hheight r.val r.property)⟩
  obtain ⟨degreeBad, hdegreeBad⟩ := Classical.skolem.mp fun r : R =>
    h1 (sectionExponents H) (I r) (hcurve r).1 (hcurve r).2
  obtain ⟨reduceBad, hreduceBad⟩ := Classical.skolem.mp fun r : R =>
    h2 (sectionExponents H) (I r) (hcurve r).1 (hcurve r).2
  let bad := Finset.univ.biUnion fun r : R => insert (reduceBad r) (degreeBad r)
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun B : bad => B.val) (by
      intro B
      obtain ⟨r, _, hB⟩ := Finset.mem_biUnion.mp B.property
      rcases Finset.mem_insert.mp hB with h | h
      · rw [h]
        exact (hreduceBad r).1
      · exact (hdegreeBad r).1 _ h)
  have havail (r : R) (B : Submodule GeometricX (SectionPoint H))
      (hB : B ∈ insert (reduceBad r) (degreeBad r)) : a ∉ B :=
    ha ⟨B, Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hB⟩⟩
  have hdegree (r : R) :=
    (hdegreeBad r).2 a (fun B hB => havail r B (Finset.mem_insert_of_mem hB))
  obtain ⟨valueBad, hvalueBad⟩ := Classical.skolem.mp fun r : R =>
    (hreduceBad r).2 a (havail r _ (Finset.mem_insert_self _ _)) (hdegree r).1
  let forbidden (r : R) := guard_points_finite hH r.val (hheight r.val r.property)
    (guard r.val) (hguard r.val r.property)
  let value (z : SectionPoint H) := aeval z (linearForm a)
  let exclusions := Finset.univ.biUnion fun r : R =>
    valueBad r ∪ (forbidden r).toFinset.image value
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset exclusions
  have htmiss (r : R) : t ∉ valueBad r ∪ (forbidden r).toFinset.image value :=
    fun h => ht (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, h⟩)
  let L := linearForm a - MvPolynomial.C t
  let J (r : R) := fiberIdeal (I r) a t
  have hfiber (r : R) : (affineHilbertPolynomial (J r)).natDegree = 0 ∧
      affineDegree (J r) = affineDegree (I r) := (hdegree r).2 t
  have hradical (r : R) : (J r).IsRadical :=
    hvalueBad r t (fun h => htmiss r (Finset.mem_union_left _ h))
  have hproper (r : R) : sectionMap H L ∉ r.val.asIdeal := by
    intro h
    have hL : L ∈ I r := h
    have heq : J r = I r := sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hL)
    have hz := (hfiber r).1
    rw [heq, (hcurve r).2] at hz
    omega
  have hfinite (r : R) : (zeroLocus GeometricX (J r)).Finite :=
    (finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) _ (hfiber r).1).1
  let selected (r : PrimeSpectrum Jets) : Finset JetPoint :=
    if hr : r ∈ R then (hfinite ⟨r, hr⟩).toFinset.image (projectPoint hH) else ∅
  refine ⟨sectionMap H L, selected, supported_sectionMap (totalDegree_hyperplane_le_one a t), ?_⟩
  intro r hr
  let q : R := ⟨r, hr⟩
  have hreconstruct {z : SectionPoint H} (hz : z ∈ zeroLocus GeometricX (J q)) :
      monomialPoint (sectionExponents H) (projectPoint hH z) = z :=
    monomialPoint_projectPoint hH (r := r) (zeroLocus_fiber_iff.mp hz).1
  have hb (y : JetPoint) (hy : y ∈ selected r) :
      (r.asIdeal ≤ jetPointIdeal y ∧ eval y (sectionMap H L) = 0) ∧
        eval y (guard r) ≠ 0 := by
    simp only [selected, dite_eq_left hr] at hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzJ : z ∈ zeroLocus GeometricX (J q) := (Set.Finite.mem_toFinset _).mp hz
    obtain ⟨hzI, hzt⟩ := zeroLocus_fiber_iff.mp hzJ
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply (base_point_iff r _).mp
      apply (monomialPoint_mem_zeroLocus_comap_iff (sectionExponents_single hH) _ _).mp
      rw [hreconstruct hzJ]
      exact hzI
    · rw [eval_sectionMap, hreconstruct hzJ]
      exact (mem_zeroLocus_sup_span_singleton_iff.mp hzJ).2
    · intro hzero
      exact htmiss q (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨z, (Set.Finite.mem_toFinset _).mpr ⟨hzI, hzero⟩, hzt⟩))
  refine ⟨?_, ⟨hproper q, fun y hy => (hb y hy).1⟩, fun y hy => (hb y hy).2⟩
  have hinj : Set.InjOn (projectPoint hH) (zeroLocus GeometricX (J q)) := by
    intro z hz w hw heq
    rw [← hreconstruct hz, ← hreconstruct hw, heq]
  have hcard : ((selected r).card : ℚ) = affineDegree (I q) := by
    simp only [selected, dite_eq_left hr]
    change (((hfinite q).toFinset.image (projectPoint hH)).card : ℚ) = _
    rw [Finset.card_image_of_injOn (by simpa using hinj),
      ← Set.ncard_eq_toFinset_card _ (hfinite q)]
    exact (ncard_eq_affineDegree_of_radical (J q) (hfiber q).1 (hradical q)).trans (hfiber q).2
  exact_mod_cast (old_section_bound hH r (hheight r hr) (hpoints r hr).1
    (hpoints r hr).2).trans_eq hcard.symm
theorem degree_of_shared (h : K1_13_5_4_2_2.c1) : c1 := by
  intro σ _ I hp hd
  exact h GeometricX σ I hp hd
theorem reduced_of_shared (hSep : K1_13_5_4_2_2.c2) (hRed : K1_13_5_4_2_2.c3) : c2 := by
  intro σ _ I hp hd
  obtain ⟨B, hB, hSepB⟩ := hSep GeometricX σ I hp hd
  exact ⟨B, hB, fun a ha hfin => hRed GeometricX σ I hp a hfin (hSepB a ha)⟩
end
end K1_13_7_5_3_1
end
section
namespace K1_13_7_5_3_4
open K1_13 (Shape volume32)
open K1_13_7_1 (Chamber)
open K1_13_7_5_3 (RealJets capBody capVolume)
open MeasureTheory Set
noncomputable section
private theorem volume_by_last {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
    {t : ℝ} {f : ℝ → ℝ} (hS : MeasurableSet S) (ht : 0 ≤ t)
    (hf : Continuous f) (hn : ∀ z ∈ Icc 0 t, 0 ≤ f z)
    (T : ℝ → Set (Fin n → ℝ))
    (hmem : ∀ z y, Fin.snoc y z ∈ S ↔ z ∈ Icc 0 t ∧ y ∈ T z)
    (hT : ∀ z ∈ Icc 0 t, volume (T z) = ENNReal.ofReal (f z)) :
    volume S = ENNReal.ofReal (∫ z in (0 : ℝ)..t, f z) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have he : MeasurePreserving e :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hsnoc (z : ℝ) (y : Fin n → ℝ) : e.symm (z, y) = Fin.snoc y z := by
    change Fin.insertNth (α := fun _ => ℝ) (Fin.last n) z y = _
    exact Fin.insertNth_last' z y
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc 0 t)] f :=
    (ae_restrict_mem measurableSet_Icc).mono hn
  have hi : IntegrableOn f (Icc 0 t) := hf.continuousOn.integrableOn_compact isCompact_Icc
  rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hi hnonneg,
    ← lintegral_indicator measurableSet_Icc]
  calc
    volume S = volume (e.symm ⁻¹' S) := by
      rw [← e.symm.map_apply, (he.symm e).map_eq]
    _ = ∫⁻ z, volume (Prod.mk z ⁻¹' (e.symm ⁻¹' S)) := by
      exact Measure.prod_apply (e.symm.measurable hS)
    _ = _ := by
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ Icc 0 t
      · have hsec : Prod.mk z ⁻¹' (e.symm ⁻¹' S) = T z := by
          ext y
          change e.symm (z, y) ∈ S ↔ y ∈ T z
          simp only [hsnoc, hmem, hz, true_and]
        rw [hsec, hT z hz, indicator_of_mem hz]
      · have hsec : Prod.mk z ⁻¹' (e.symm ⁻¹' S) = ∅ := by
          ext y
          change e.symm (z, y) ∈ S ↔ y ∈ (∅ : Set (Fin n → ℝ))
          simp only [hsnoc, hmem, hz, false_and, mem_empty_iff_false]
        rw [hsec, measure_empty, indicator_of_notMem hz]
private theorem integral_cubic (a b c d t : ℝ) :
    (∫ x in (0 : ℝ)..t, a + b * x + c * x ^ 2 + d * x ^ 3) =
      a * t + b * t ^ 2 / 2 + c * t ^ 3 / 3 + d * t ^ 4 / 4 := by
  have hcont : Continuous (fun x : ℝ => a + b * x + c * x ^ 2 + d * x ^ 3) := by
    fun_prop
  have hD (x : ℝ) :
      HasDerivAt (fun x => a * x + b * x ^ 2 / 2 + c * x ^ 3 / 3 + d * x ^ 4 / 4)
        (a + b * x + c * x ^ 2 + d * x ^ 3) x := by
    have hx := hasDerivAt_id' x
    convert (((hx.const_mul a).add (((hx.pow 2).const_mul b).div_const 2)).add
      (((hx.pow 3).const_mul c).div_const 3)).add (((hx.pow 4).const_mul d).div_const 4)
      using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x)
    (hcont.intervalIntegrable _ _)]
  ring
private theorem integral_affine (a b t : ℝ) :
    (∫ x in (0 : ℝ)..t, a + b * x) = a * t + b * t ^ 2 / 2 := by
  simpa only [zero_mul, zero_div, add_zero] using integral_cubic a b 0 0 t
private def oneBody (b : ℝ) : Set (Fin 1 → ℝ) :=
  {x | x 0 ∈ Icc 0 b}
private theorem one_volume (b : ℝ) : volume (oneBody b) = ENNReal.ofReal b := by
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have he : MeasurePreserving e := volume_preserving_funUnique (Fin 1) ℝ
  have hS : oneBody b = e ⁻¹' Icc 0 b := rfl
  rw [hS, ← e.map_apply, he.map_eq, Real.volume_Icc, sub_zero]
private def twoBody (b j : ℝ) : Set (Fin 2 → ℝ) :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ b ∧ x 1 ≤ j}
private theorem two_volume {b j : ℝ} (hj : 0 ≤ j) (hjb : j ≤ b) :
    volume (twoBody b j) = ENNReal.ofReal (b * j - j ^ 2 / 2) := by
  have hS : MeasurableSet (twoBody b j) := by
    unfold twoBody
    measurability
  have hvol := volume_by_last hS hj (f := fun x => b - x)
    (by fun_prop) (fun x hx => sub_nonneg.mpr (hx.2.trans hjb))
    (fun x => oneBody (b - x)) ?_ (fun x _ => one_volume (b - x))
  · rw [hvol]
    congr 1
    calc
      (∫ x in (0 : ℝ)..j, b - x) = ∫ x in (0 : ℝ)..j, b + (-1) * x := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = b * j - j ^ 2 / 2 := by rw [integral_affine]; ring
  · intro z x
    change (0 ≤ x 0 ∧ 0 ≤ z ∧ x 0 + z ≤ b ∧ z ≤ j) ↔
      (0 ≤ z ∧ z ≤ j) ∧ 0 ≤ x 0 ∧ x 0 ≤ b - z
    constructor
    · rintro ⟨hx, hz, hb, hj'⟩
      exact ⟨⟨hz, hj'⟩, hx, by linarith⟩
    · rintro ⟨⟨hz, hj'⟩, hx, hb⟩
      exact ⟨hx, hz, by linarith, hj'⟩
private def threeBody (b j : ℝ) : Set (Fin 3 → ℝ) :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧
    x 0 + x 1 + x 2 ≤ b ∧ x 1 + 2 * x 2 ≤ j}
private theorem three_volume {b j : ℝ} (hj : 0 ≤ j) (hjb : j ≤ b) :
    volume (threeBody b j) = ENNReal.ofReal (j ^ 2 * (2 * b - j) / 8) := by
  have hS : MeasurableSet (threeBody b j) := by
    unfold threeBody
    measurability
  have hvol := volume_by_last hS (show 0 ≤ j / 2 by linarith)
    (f := fun x => (b - j / 2) * (j - 2 * x)) (by fun_prop)
    (fun x hx => mul_nonneg (by linarith) (by linarith [hx.2]))
    (fun x => twoBody (b - x) (j - 2 * x)) ?_ ?_
  · rw [hvol]
    congr 1
    calc
      (∫ x in (0 : ℝ)..(j / 2), (b - j / 2) * (j - 2 * x)) =
          ∫ x in (0 : ℝ)..(j / 2), (b - j / 2) * j + (-2 * (b - j / 2)) * x := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = j ^ 2 * (2 * b - j) / 8 := by rw [integral_affine]; ring
  · intro z x
    change (0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ z ∧ x 0 + x 1 + z ≤ b ∧ x 1 + 2 * z ≤ j) ↔
      (0 ≤ z ∧ z ≤ j / 2) ∧ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧
        x 0 + x 1 ≤ b - z ∧ x 1 ≤ j - 2 * z
    constructor
    · rintro ⟨h0, h1, hz, hb, hj'⟩
      exact ⟨⟨hz, by linarith⟩, h0, h1, by linarith, by linarith⟩
    · rintro ⟨⟨hz, _⟩, h0, h1, hb, hj'⟩
      exact ⟨h0, h1, hz, by linarith, by linarith⟩
  · intro z hz
    rw [two_volume (show 0 ≤ j - 2 * z by linarith [hz.2])
      (show j - 2 * z ≤ b - z by linarith [hz.1])]
    congr 1
    ring
private theorem capBody_coordinates (p : Shape) (x : RealJets) :
    x ∈ capBody p ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧ 0 ≤ x 3 ∧ x 0 + x 1 + x 2 + x 3 ≤ p.b ∧
        x 1 + 2 * x 2 + 3 * x 3 ≤ p.j ∧ x 3 ≤ p.t := by
  have h : x ∈ capBody p ↔ (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 + x 3 ≤ p.b ∧
      x 1 + 2 * x 2 + 3 * x 3 ≤ p.j ∧ x 3 ≤ p.t := by
    norm_num [capBody, Fin.sum_univ_four]
  rw [h]
  constructor
  · rintro ⟨hx, hb, hj, ht⟩
    exact ⟨hx 0, hx 1, hx 2, hx 3, hb, hj, ht⟩
  · rintro ⟨h0, h1, h2, h3, hb, hj, ht⟩
    refine ⟨?_, hb, hj, ht⟩
    intro i
    fin_cases i <;> assumption
private def sliceDensity (b j z : ℝ) : ℝ := (j - 3 * z) ^ 2 * (2 * b - j + z) / 8
private theorem cap_volume_integral (p : Shape) (hp : Chamber p) :
    capVolume (capBody p) =
      ∫ z in (0 : ℝ)..(p.t : ℝ), sliceDensity p.b p.j z := by
  have hjb : (p.j : ℝ) ≤ p.b := by exact_mod_cast hp.1
  have hjt : 3 * (p.t : ℝ) ≤ p.j := by exact_mod_cast hp.2
  have ht : (0 : ℝ) ≤ p.t := Nat.cast_nonneg _
  have hS : MeasurableSet (capBody p) := by
    have heq : capBody p = {x : RealJets |
        0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧ 0 ≤ x 3 ∧ x 0 + x 1 + x 2 + x 3 ≤ p.b ∧
          x 1 + 2 * x 2 + 3 * x 3 ≤ p.j ∧ x 3 ≤ p.t} := by
      ext x
      exact capBody_coordinates p x
    rw [heq]
    measurability
  have hnonneg (z : ℝ) (hz : z ∈ Icc 0 (p.t : ℝ)) : 0 ≤ sliceDensity p.b p.j z := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith [hz.1])) (by norm_num)
  have hVol := volume_by_last hS ht (f := sliceDensity p.b p.j)
    (by unfold sliceDensity; fun_prop) hnonneg
    (fun z => threeBody ((p.b : ℝ) - z) ((p.j : ℝ) - 3 * z)) ?_ ?_
  · rw [capVolume, hVol, ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg ht hnonneg)]
  · intro z x
    rw [capBody_coordinates]
    change (0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧ 0 ≤ z ∧ x 0 + x 1 + x 2 + z ≤ p.b ∧
        x 1 + 2 * x 2 + 3 * z ≤ p.j ∧ z ≤ p.t) ↔
      (0 ≤ z ∧ z ≤ p.t) ∧ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧
        x 0 + x 1 + x 2 ≤ (p.b : ℝ) - z ∧ x 1 + 2 * x 2 ≤ (p.j : ℝ) - 3 * z
    constructor
    · rintro ⟨h0, h1, h2, hz, hb, hj, ht'⟩
      exact ⟨⟨hz, ht'⟩, h0, h1, h2, by linarith, by linarith⟩
    · rintro ⟨⟨hz, ht'⟩, h0, h1, h2, hb, hj⟩
      exact ⟨h0, h1, h2, hz, by linarith, by linarith, ht'⟩
  · intro z hz
    rw [three_volume (show 0 ≤ (p.j : ℝ) - 3 * z by linarith [hz.2])
      (show (p.j : ℝ) - 3 * z ≤ (p.b : ℝ) - z by linarith [hz.1])]
    congr 1
    unfold sliceDensity
    ring
theorem proof : K1_13_7_5_3.c4 := by
  intro p hp
  rw [cap_volume_integral p hp, ← intervalIntegral.integral_const_mul]
  let b : ℝ := p.b
  let j : ℝ := p.j
  let t : ℝ := p.t
  calc
    (∫ z in (0 : ℝ)..t, 32 * sliceDensity b j z) =
        ∫ z in (0 : ℝ)..t, (8 * b * j ^ 2 - 4 * j ^ 3) +
          (-48 * b * j + 28 * j ^ 2) * z + (72 * b - 60 * j) * z ^ 2 + 36 * z ^ 3 := by
      apply intervalIntegral.integral_congr
      intro z _
      unfold sliceDensity
      ring
    _ = _ := by
      rw [integral_cubic]
      push_cast [volume32]
      dsimp only [b, j, t]
      ring
end
end K1_13_7_5_3_4
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_2
noncomputable section
open K1_13_7_5 K1_13_7_5_3
open scoped BigOperators
private theorem exists_component_guard (J : Ideal Jets) (r : PrimeSpectrum Jets)
    (hr : r.asIdeal ∈ J.minimalPrimes) :
    ∃ b : Jets, b ∉ r.asIdeal ∧ ∀ q ∈ J.minimalPrimes, q ≠ r.asIdeal → b ∈ q := by
  classical
  have hchoose (q : Ideal Jets) :
      ∃ x : Jets, x ∉ r.asIdeal ∧ (q ∈ J.minimalPrimes → q ≠ r.asIdeal → x ∈ q) := by
    by_cases hq : q ∈ J.minimalPrimes ∧ q ≠ r.asIdeal
    · have hn : ¬ q ≤ r.asIdeal := fun hle => hq.2 (hle.antisymm (hr.2 hq.1.1 hle))
      obtain ⟨x, hx, hxr⟩ := Set.not_subset.mp hn
      exact ⟨x, hxr, fun _ _ => hx⟩
    · exact ⟨1, r.asIdeal.ne_top_iff_one.mp r.isPrime.ne_top, fun h hne => (hq ⟨h, hne⟩).elim⟩
  choose x hx using hchoose
  let t := J.finite_minimalPrimes_of_isNoetherianRing
  refine ⟨∏ q ∈ t.toFinset, x q, ?_, ?_⟩
  · have hprod (s : Finset (Ideal Jets)) : (∏ q ∈ s, x q) ∉ r.asIdeal := by
      induction s using Finset.induction_on with
      | empty => simpa using r.asIdeal.ne_top_iff_one.mp r.isPrime.ne_top
      | insert q s hqs ih =>
        rw [Finset.prod_insert hqs]
        exact fun h => (r.isPrime.mem_or_mem h).elim (hx q).1 ih
    exact hprod t.toFinset
  · intro q hq hqr
    exact q.prod_mem (t.mem_toFinset.mpr hq) ((hx q).2 hq hqr)
private theorem height_le_four (q : Ideal Jets) [q.IsPrime] : q.height ≤ 4 := by
  have h := Ideal.height_le_ringKrullDim_of_isPrime (I := q)
  have hd : ringKrullDim Jets = 4 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [hd] at h
  exact WithBot.coe_le_coe.mp h
private theorem isolated_section {J : Ideal Jets} {r p : PrimeSpectrum Jets} {b D : Jets}
    (hr : r.asIdeal ∈ J.minimalPrimes) (hh : r.asIdeal.height = 3)
    (hb : ∀ q ∈ J.minimalPrimes, q ≠ r.asIdeal → b ∈ q)
    (hrp : r.asIdeal ≤ p.asIdeal) (hbp : b ∉ p.asIdeal)
    (hD : D ∉ r.asIdeal) (hDp : D ∈ p.asIdeal) :
    p.asIdeal ∈ (cutIdeal J D).minimalPrimes := by
  have hcut : cutIdeal J D ≤ p.asIdeal :=
    sup_le (hr.le.trans hrp) ((Ideal.span_singleton_le_iff_mem _).mpr hDp)
  refine ⟨⟨p.isPrime, hcut⟩, ?_⟩
  intro q hq hqp
  let : q.IsPrime := hq.1
  have hJq : J ≤ q := le_sup_left.trans hq.2
  obtain ⟨s, hs, hsq⟩ := Ideal.exists_minimalPrimes_le hJq
  have hsr : s = r.asIdeal := by
    by_contra h
    exact hbp (hqp (hsq (hb s hs h)))
  have hrq : r.asIdeal ≤ q := hsr ▸ hsq
  have hDq : D ∈ q := hq.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self D))
  have hrlt : r.asIdeal < q := lt_of_le_of_ne hrq (fun h => hD (h ▸ hDq))
  have hfour : (4 : ℕ∞) ≤ q.height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hrlt
    rw [hh] at h
    exact h
  have heq : q = p.asIdeal :=
    Ideal.eq_of_le_of_height_le q hqp ((height_le_four p.asIdeal).trans hfour)
  exact heq.ge
theorem proof : K1_13_7_5_3.c2 := by
  intro J r hr hh _
  obtain ⟨g, hgr, hg⟩ := exists_weight_guard J r hr
  obtain ⟨b, hbr, hb⟩ := exists_component_guard J r hr
  refine ⟨g * b, fun h => (r.isPrime.mem_or_mem h).elim hgr hbr,
    fun q hq hqr => q.mul_mem_left g (hb q hq hqr), ?_⟩
  intro D hD y hry ha hDy
  let p := pointPrime y
  have ha' : g * b ∉ p.asIdeal := ha
  have hg' : g ∉ p.asIdeal := fun h => ha' (p.asIdeal.mul_mem_right b h)
  have hb' : b ∉ p.asIdeal := fun h => ha' (p.asIdeal.mul_mem_left g h)
  exact ⟨isolated_section hr hh hb hry hb' hD hDy, hg p hry hg' D hD hDy⟩
end
end K1_13_7_5_3_2
end
section
namespace K1_13_7_5_1
open Polynomial K1_13 K1_13_7 K1_13_7_5
noncomputable section
private theorem chartMap_surjectiveOnStalks (f : Row 4) :
    (chartMap f).SurjectiveOnStalks := by
  let F := upperPolynomial f
  let a := AdjoinRoot.of F F.leadingCoeff
  apply RingHom.SurjectiveOnStalks.comp _ (RingHom.surjectiveOnStalks_of_surjective
    (hypersurfaceMap_surjective f))
  apply RingHom.surjectiveOnStalks_of_exists_div
  intro z
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj a z
  refine ⟨b, a ^ n, ?_, ?_⟩
  · rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit a).pow n
  · rwa [map_pow, mul_comm]
theorem lift_length_ge {f : Row 4} {P Q : Row 3} {r : PrimeSpectrum Jets}
    {q : PrimeSpectrum Lower} (p : PrimeSpectrum (chartRing f)) [p.asIdeal.LiesOver q.asIdeal]
    (hp : p.asIdeal.comap (chartMap f) = r.asIdeal)
    (ha : (upperPolynomial f).leadingCoeff ≠ 0) :
    localColength q (pairIdeal P Q) ≤ liftLength r (liftIdeal f P Q) := by
  let D := chartRing f
  let : Module.Flat Lower D := leadingChart_flat _ ha
  let A := Localization.AtPrime q.asIdeal
  let B := Localization.AtPrime p.asIdeal
  let U := Localization.AtPrime r.asIdeal
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  have : IsLocalHom (algebraMap A B) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  let J := (pairIdeal P Q).map (algebraMap Lower A)
  let JB := J.map (algebraMap A B)
  let G := (liftIdeal f P Q).map (algebraMap Jets U)
  let φ := Localization.localRingHom r.asIdeal p.asIdeal (chartMap f) hp.symm
  let : Algebra U B := φ.toAlgebra
  have hφ : Function.Surjective (algebraMap U B) :=
    (chartMap_surjectiveOnStalks f).localRingHom_surjective _ _ hp.symm
  have hmap : G ≤ JB.comap (algebraMap U B) := by
    have hcomp : (algebraMap U B).comp (algebraMap Jets U) =
        (algebraMap D B).comp (chartMap f) :=
      RingHom.ext (Localization.localRingHom_to_map _ _ _ hp.symm)
    rw [← Ideal.map_le_iff_le_comap]
    change ((liftIdeal f P Q).map (algebraMap Jets U)).map (algebraMap U B) ≤ JB
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, chartMap_liftIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq Lower D B]
    change _ ≤ ((pairIdeal P Q).map (algebraMap Lower A)).map (algebraMap A B)
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq Lower A B]
  let ψ := Ideal.quotientMapₐ JB (Algebra.ofId U B) hmap
  have hψ : Function.Surjective ψ := by
    change Function.Surjective (Ideal.quotientMap JB (algebraMap U B) hmap)
    exact Ideal.quotientMap_surjective hφ
  have hlength : Module.length B (B ⧸ JB) ≤ Module.length U (U ⧸ G) := by
    rw [← Module.length_eq_of_surjective (M := B ⧸ JB) hφ]
    exact Module.length_le_of_surjective ψ.toLinearMap hψ
  have hproper := IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)
  have : Nontrivial (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper.ne
  have hpos := Module.length_pos (R := B)
    (M := B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
  have hl : Module.length B (B ⧸ JB) = Module.length B (TensorProduct A B (A ⧸ J)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toLinearEquiv.length_eq
  rw [IsLocalRing.length_baseChange] at hl
  exact (ENat.self_le_mul_right _ hpos.ne').trans (hl.ge.trans hlength)
theorem lift_length_finite {r : PrimeSpectrum Jets} {I : Ideal Jets}
    (hr : r.asIdeal ∈ I.minimalPrimes) : liftLength r I < ⊤ := by
  let A := Localization.AtPrime r.asIdeal
  let L := I.map (algebraMap Jets A)
  have hmin : IsLocalRing.maximalIdeal A ∈ L.minimalPrimes := by
    change IsLocalRing.maximalIdeal A ∈ (I.map (algebraMap Jets A)).minimalPrimes
    rw [IsLocalization.minimalPrimes_map r.asIdeal.primeCompl A, Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A r.asIdeal]
    exact hr
  have : IsArtinianRing (A ⧸ L) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing L hmin
  exact lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_quotient L, isArtinian_of_surjective_algebraMap
        (Ideal.Quotient.mk_surjective (I := L))⟩))
end
end K1_13_7_5_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace K1_14_3_2_4
noncomputable section
open K1_14 K1_14_3 Polynomial
@[simp] private theorem eval_seedVar (s : Slice) (i : Fin 2) :
    sectionEval s (seedVar i) = seedValues s i := by
  simp [sectionEval, seedVar]
@[simp] private theorem eval_ordinateVar (s : Slice) :
    sectionEval s ordinateVar = ordinateValue s := by
  simp [sectionEval, ordinateVar]
@[simp] private theorem eval_derivativeVar (s : Slice) :
    sectionEval s derivativeVar = derivativeValue s := by
  simp [sectionEval, derivativeVar]
@[simp] private theorem eval_scalar (s : Slice) (i : Fin 4) :
    sectionEval s (sectionScalar i) = MvPolynomial.C (parameter i) :=
  (sectionEval s).commutes (parameter i)
end
end K1_14_3_2_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_3_2_4_1
noncomputable section
open K1_14 K1_14_3 K1_14_3_2_4 Polynomial
private abbrev Parameters := MvPolynomial (Fin 4) FX
private abbrev BeforeCut := MvPolynomial (Fin 2) Jet
private abbrev AfterCut := MvPolynomial (Fin 2) Parameters
local instance : Algebra AfterCut Plane := MvPolynomial.algebraMvPolynomial
private def seed (i : Fin 2) : Jet := C (C (MvPolynomial.X i))
private def ord : Jet := C (Polynomial.X (R := Seeds))
private def der : Jet := Polynomial.X
private def seedIn (i : Fin 2) : BeforeCut := MvPolynomial.C (seed i)
private def ordIn : BeforeCut := MvPolynomial.C ord
private def derIn : BeforeCut := MvPolynomial.C der
private def slope (i : Fin 2) : BeforeCut := MvPolynomial.X i
private def genericCut (s : Slice) : BeforeCut →+* Plane :=
  MvPolynomial.eval₂Hom ((sectionEval s).toRingHom.comp sectionMap)
    ![MvPolynomial.C (parameter 0), MvPolynomial.C (parameter 1)]
@[simp] private theorem genericCut_seed (s : Slice) (i : Fin 2) :
    genericCut s (seedIn i) = seedValues s i := by
  simp [genericCut, seedIn, seed, sectionMap, sectionEval]
@[simp] private theorem genericCut_ord (s : Slice) :
    genericCut s ordIn = ordinateValue s := by
  simp [genericCut, ordIn, ord, sectionMap, sectionEval]
@[simp] private theorem genericCut_der (s : Slice) :
    genericCut s derIn = derivativeValue s := by
  simp [genericCut, derIn, der, sectionMap, sectionEval]
@[simp] private theorem genericCut_slope_zero (s : Slice) :
    genericCut s (slope 0) = MvPolynomial.C (parameter 0) := by
  simp [genericCut, slope]
@[simp] private theorem genericCut_slope_one (s : Slice) :
    genericCut s (slope 1) = MvPolynomial.C (parameter 1) := by
  simp [genericCut, slope]
end
end K1_14_3_2_4_1
end
