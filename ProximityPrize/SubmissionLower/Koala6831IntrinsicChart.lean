import ProximityPrize.SubmissionLower.LowerFoundation
import ProximityPrize.SubmissionLower.Koala6831IntrinsicRegular


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open MvPolynomial RCN055 RCN077 RCN135 RCN136 RCN159 RCN186 RCN188 RCN218 RCN219
  RCN230 RCN270 IsLocalRing

noncomputable section

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 250000
set_option maxRecDepth 10000
set_option linter.style.haveILetI false

variable {K : Type} [Field K]

private theorem quotient_height_one (F : Carrier K) (p : Ideal (Carrier K))
    [p.IsPrime] [(factorIdeal F).IsPrime] [(quotientPrime (factorIdeal F) p).IsPrime]
    (hF : Irreducible F) (hle : factorIdeal F ≤ p) (hpheight : p.height = 2) :
    (quotientPrime (factorIdeal F) p).height = 1 := by
  let I := factorIdeal F
  have hiheight : I.height = 1 := by
    change (Ideal.span ({F} : Set (Carrier K))).height = 1
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (by simpa [mem_nonZeroDivisors_iff_ne_zero] using hF.ne_zero) hF.not_isUnit
  have hip : I ≠ p := by
    intro heq
    have hh := congrArg Ideal.height heq
    rw [hiheight, hpheight] at hh
    norm_num at hh
  have hilt := lt_of_le_of_ne hle hip
  obtain ⟨x, hxp, hxI⟩ := SetLike.exists_of_lt hilt
  have hmin : p ∈ (I ⊔ Ideal.span {x}).minimalPrimes := by
    refine ⟨⟨inferInstance, sup_le hle (Ideal.span_le.2 (by simpa))⟩, ?_⟩
    intro r hr hrp
    rcases hr with ⟨hrprime, hle_r⟩
    letI : r.IsPrime := hrprime
    have hir : I ≤ r := le_sup_left.trans hle_r
    have hne : I ≠ r := by
      intro heq
      apply hxI
      change x ∈ I
      rw [heq]
      exact hle_r ((show Ideal.span {x} ≤ I ⊔ Ideal.span {x} from le_sup_right)
        (Ideal.mem_span_singleton_self x))
    by_contra hnot
    have hrplt := lt_of_le_of_ne hrp (Ne.symm (ne_of_not_le hnot))
    have hchain : (3 : ℕ∞) ≤ p.height := by
      calc
        3 = I.height + 1 + 1 := by rw [hiheight]; norm_num
        _ ≤ r.height + 1 := by
          simpa [add_comm, add_assoc, add_left_comm] using add_le_add_left
            (Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hir hne)) 1
        _ ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hrplt
    rw [hpheight] at hchain
    norm_num at hchain
  apply le_antisymm
  · exact Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  · rw [Order.one_le_iff_ne_zero]
    intro hz
    have hqbot := Ideal.height_eq_zero_iff_eq_bot.mp hz
    have hcomap := quotientPrime_comap_quotientMk I p hle
    rw [hqbot] at hcomap
    change RingHom.ker (Ideal.Quotient.mk I) = p at hcomap
    rw [Ideal.mk_ker] at hcomap
    exact hip hcomap

private theorem local_isDVR (F : Carrier K) (p : Ideal (Carrier K))
    [p.IsPrime] [(factorIdeal F).IsPrime] [(quotientPrime (factorIdeal F) p).IsPrime]
    (hF : Irreducible F) (hle : factorIdeal F ≤ p) (hpheight : p.height = 2)
    (hS : implicitRegularity F ∉ p) :
    IsDiscreteValuationRing (FactorLocal F p hle) := by
  have hdim : ringKrullDim (FactorLocal F p hle) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (quotientPrime (factorIdeal F) p) (FactorLocal F p hle)]
    exact_mod_cast quotient_height_one F p hF hle hpheight
  let A := Localization.AtPrime p
  letI : IsRegularLocalRing A := mvPolynomial_atPrime_isRegularLocalRing p
  let f : A := algebraMap (Carrier K) A F
  have hdimA : ringKrullDim A = 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p A, hpheight]
    norm_num
  have hf : f ∈ maximalIdeal A :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A p F).mpr
      (hle (Ideal.mem_span_singleton_self F))
  have hfsq : f ∉ maximalIdeal A ^ 2 := by
    intro hf2
    let D : Derivation K A A := localizationDerivation p.primeCompl (pderiv (1 : Fin 4))
    have hd : D f ∈ maximalIdeal A := derivation_mem_maximal_of_mem_sq D f hf2
    have hDF : D f = algebraMap (Carrier K) A (implicitRegularity F) :=
      localizationDerivation_algebraMap p.primeCompl _ F
    rw [hDF] at hd
    exact hS ((IsLocalization.AtPrime.to_map_mem_maximal_iff A p _).mp hd)
  let e := factorAmbientQuotientEquiv F p hle
  have hdimQ : ringKrullDim (A ⧸ Ideal.span {f}) = 1 :=
    (ringKrullDim_eq_of_ringEquiv e).trans hdim
  letI : IsRegularLocalRing (A ⧸ Ideal.span {f}) :=
    quotient_span_singleton_isRegularLocalRing f hf hfsq hdimA hdimQ
  letI : IsRegularLocalRing (FactorLocal F p hle) :=
    IsRegularLocalRing.of_ringEquiv (R := A ⧸ Ideal.span {f}) e
  exact RCN324.isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one hdim

private def clearedDerivation (F : Carrier K) : Derivation K (Carrier K) (Carrier K) :=
  implicitRegularity F • pderiv 0 - (pderiv 0 F : Carrier K) • pderiv 1

private theorem clearedDerivation_apply (F A : Carrier K) :
    clearedDerivation F A = clearedImplicit F A := by
  simp only [clearedDerivation, clearedImplicit, Derivation.sub_apply,
    Derivation.smul_apply, smul_eq_mul]

private theorem clearedDerivation_preserves (F : Carrier K) :
    ∀ A ∈ factorIdeal F, clearedDerivation F A ∈ factorIdeal F := by
  intro A hA
  rw [factorIdeal, Ideal.mem_span_singleton] at hA ⊢
  obtain ⟨B, rfl⟩ := hA
  have hF : clearedDerivation F F = 0 := by
    rw [clearedDerivation_apply, clearedImplicit, implicitRegularity]
    ring
  refine ⟨clearedDerivation F B, ?_⟩
  rw [(clearedDerivation F).leibniz, hF]
  simp

private def quotientCleared (F : Carrier K) :
    Derivation K (Carrier K ⧸ factorIdeal F) (Carrier K ⧸ factorIdeal F) :=
  quotientDerivation (clearedDerivation F) (factorIdeal F) (clearedDerivation_preserves F)

section Local

variable (F : Carrier K) (p : Ideal (Carrier K)) [p.IsPrime]
  [(factorIdeal F).IsPrime] [(quotientPrime (factorIdeal F) p).IsPrime]
  (hle : factorIdeal F ≤ p)

private def localCleared :
    Derivation K (FactorLocal F p hle) (FactorLocal F p hle) :=
  localizationDerivation (K := K) (R := Carrier K ⧸ factorIdeal F) (S := FactorLocal F p hle)
    (quotientPrime (factorIdeal F) p).primeCompl (quotientCleared F)

private def localMap : Carrier K →+* FactorLocal F p hle :=
  (algebraMap (Carrier K ⧸ factorIdeal F) (FactorLocal F p hle)).comp
    (Ideal.Quotient.mk (factorIdeal F))

omit [(factorIdeal F).IsPrime] in
private theorem localCleared_map (A : Carrier K) :
    localCleared F p hle (localMap F p hle A) = localMap F p hle (clearedImplicit F A) := by
  simp only [localMap, RingHom.comp_apply, localCleared, localizationDerivation_algebraMap]
  have h := quotientDerivation_mk (clearedDerivation F) (factorIdeal F)
    (clearedDerivation_preserves F) A
  rw [clearedDerivation_apply] at h
  exact congrArg (algebraMap (Carrier K ⧸ factorIdeal F) (FactorLocal F p hle)) h

private theorem localMap_ne_zero (A : Carrier K) (hA : ¬ F ∣ A) :
    localMap F p hle A ≠ 0 := by
  intro hz
  have he := IsLocalization.injective (FactorLocal F p hle)
    ((quotientPrime (factorIdeal F) p).primeCompl_le_nonZeroDivisors)
  have hQ : Ideal.Quotient.mk (factorIdeal F) A = 0 := by
    apply he
    simpa only [localMap, RingHom.comp_apply, map_zero] using hz
  exact hA (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hQ))

omit [(factorIdeal F).IsPrime] in
private theorem localMap_isUnit_iff (A : Carrier K) :
    IsUnit (localMap F p hle A) ↔ A ∉ p := by
  change IsUnit (algebraMap (Carrier K ⧸ factorIdeal F) (FactorLocal F p hle)
    (Ideal.Quotient.mk (factorIdeal F) A)) ↔ A ∉ p
  rw [IsLocalization.AtPrime.isUnit_to_map_iff
    (FactorLocal F p hle) (quotientPrime (factorIdeal F) p)]
  change (A ∉ (quotientPrime (factorIdeal F) p).comap
    (Ideal.Quotient.mk (factorIdeal F))) ↔ A ∉ p
  rw [quotientPrime_comap_quotientMk _ _ hle]

end Local

structure CurveChartData (F : Carrier K) (w : ℕ)
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) : Prop where
  height_le : C.height ≤ 2
  irreducible : Irreducible F
  carrier_mem : surfaceMap (polynomialEmbedding K) F ∈ C
  separant_not_mem : surfaceMap (polynomialEmbedding K) (implicitRegularity F) ∉ C
  first_tail_mem : surfaceMap (polynomialEmbedding K) (tailNumerator F w) ∈ C
  first_tail_proper : ¬ F ∣ tailNumerator F w

theorem curveChartData_of_regularComponent (F : Carrier K) (w : ℕ)
    {G : MvPolynomial (Fin 3) (GenericField K)}
    (hirr : Irreducible F) (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hproper : ¬ G ∣ surfaceMap (polynomialEmbedding K) (tailNumerator F w))
    (C : RCN264.RegularComponent (GenericField K) G
      (surfaceMap (polynomialEmbedding K) (tailNumerator F w))
      (surfaceMap (polynomialEmbedding K) (implicitRegularity F))) :
    CurveChartData F w C.1 := by
  refine ⟨?_, hirr, ?_, ?_, ?_, ?_⟩
  · exact RCN072.component_height_le_two _ _ _ C.1 (RCN264.regularComponent_mem _ _ _ _ C)
  · obtain ⟨Q, hQ⟩ := hdiv
    rw [hQ]
    exact C.1.mul_mem_right Q (RCN264.regularComponent_G_mem _ _ _ _ C)
  · exact RCN264.regularComponent_H_not_mem _ _ _ _ C
  · exact RCN264.regularComponent_T_mem _ _ _ _ C
  · intro h
    exact hproper (hdiv.trans (map_dvd (surfaceMap (polynomialEmbedding K)) h))

private theorem CurveChartData.le_prime {F : Carrier K} {w : ℕ}
    {C : Ideal (MvPolynomial (Fin 3) (GenericField K))}
    (h : CurveChartData F w C) :
    factorIdeal F ≤ originalPrime C := by
  apply Ideal.span_le.2
  intro A hA
  rw [Set.mem_singleton_iff.mp hA]
  exact (mem_originalPrime_iff C F).2 h.carrier_mem

private theorem CurveChartData.prime_height {F : Carrier K} {w : ℕ}
    {C : Ideal (MvPolynomial (Fin 3) (GenericField K))} [C.IsPrime]
    (h : CurveChartData F w C) :
    (originalPrime C).height = 2 :=
  originalPrime_height_eq_two C h.height_le F (tailNumerator F w) h.irreducible
    h.carrier_mem h.first_tail_mem h.first_tail_proper

private theorem CurveChartData.separant_avoids_prime {F : Carrier K} {w : ℕ}
    {C : Ideal (MvPolynomial (Fin 3) (GenericField K))}
    (h : CurveChartData F w C) :
    implicitRegularity F ∉ originalPrime C :=
  fun hmem => h.separant_not_mem ((mem_originalPrime_iff C _).1 hmem)

def curveTailOrder (F : Carrier K) (w : ℕ)
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (h : CurveChartData F w C) : ℕ := by
  let p := originalPrime C
  letI : (factorIdeal F).IsPrime := factorIdeal_isPrime F h.irreducible
  letI : (quotientPrime (factorIdeal F) p).IsPrime := quotientPrime_isPrime _ _ h.le_prime
  let R := FactorLocal F p h.le_prime
  letI : IsDiscreteValuationRing R :=
    local_isDVR F p h.irreducible h.le_prime h.prime_height h.separant_avoids_prime
  exact (IsDiscreteValuationRing.addVal R (localMap F p h.le_prime (tailNumerator F w))).toNat

theorem curve_intrinsic_tail_dichotomy
    (F : Carrier K) (w pchar : ℕ) [CharP K pchar] (hpchar : pchar.Prime)
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (h : CurveChartData F w C) :
    let μ := curveTailOrder F w C h
    1 ≤ μ ∧
      ((∃ delay, 1 ≤ delay ∧ delay ≤ μ ∧
        surfaceMap (polynomialEmbedding K) (tailNumerator F (w + delay)) ∉ C) ∨
       (∀ delay, surfaceMap (polynomialEmbedding K) (tailNumerator F (w + delay)) ∈ C)) := by
  let p := originalPrime C
  letI : (factorIdeal F).IsPrime := factorIdeal_isPrime F h.irreducible
  let hle : factorIdeal F ≤ p := h.le_prime
  letI : (quotientPrime (factorIdeal F) p).IsPrime := quotientPrime_isPrime _ _ hle
  let R := FactorLocal F p hle
  letI : IsDiscreteValuationRing R :=
    local_isDVR F p h.irreducible hle h.prime_height h.separant_avoids_prime
  letI : CharP R pchar := charP_of_injective_algebraMap
    (algebraMap K R).injective pchar
  let ρ := localMap F p hle
  let D := localCleared F p hle
  let H := ρ (implicitRegularity F)
  let N := fun j : ℕ => ρ (tailNumerator F (w + j))
  have hrec (j : ℕ) :
      N (j + 1) = H * D (N j) - ((2 * (w + j) + 1 : ℕ) : R) * N j * D H := by
    unfold N H ρ D
    rw [show w + (j + 1) = (w + j) + 1 by omega, tailNumerator]
    simp only [map_sub, map_mul, map_natCast, localCleared_map]
  have hHunit : IsUnit H := (localMap_isUnit_iff F p hle _).2 h.separant_avoids_prime
  have hN0ne : N 0 ≠ 0 := by
    simpa only [N, Nat.add_zero] using localMap_ne_zero F p hle _ h.first_tail_proper
  have hN0nonunit : ¬ IsUnit (N 0) := by
    intro hu
    have hn := (localMap_isUnit_iff F p hle (tailNumerator F w)).1
      (by simpa only [N, Nat.add_zero] using hu)
    exact hn ((mem_originalPrime_iff C _).2 h.first_tail_mem)
  obtain ⟨hμ, hcase⟩ :=
    RCN073.recurrence_unit_or_persistent D H (D H)
      (fun j => ((2 * (w + j) + 1 : ℕ) : R)) N pchar hpchar hrec hHunit hN0ne hN0nonunit
  have horder : (IsDiscreteValuationRing.addVal R (N 0)).toNat =
      curveTailOrder F w C h := by simp only [N, Nat.add_zero, curveTailOrder]; rfl
  rw [horder] at hμ hcase
  refine ⟨hμ, ?_⟩
  rcases hcase with ⟨delay, hd, hdμ, hu⟩ | hpersist
  · exact Or.inl ⟨delay, hd, hdμ, fun hc =>
      ((localMap_isUnit_iff F p hle _).1 hu) ((mem_originalPrime_iff C _).2 hc)⟩
  · exact Or.inr (fun delay =>
      (mem_originalPrime_iff C _).1 (not_not.mp
        (fun h => hpersist delay ((localMap_isUnit_iff F p hle _).2 h))))

theorem curve_tail_order_multiplier
    (F : Carrier K) (w pchar : ℕ) [CharP K pchar] (hpchar : pchar.Prime)
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (h : CurveChartData F w C) :
    ∃ s : Carrier K, s ∉ originalPrime C ∧
      s * tailNumerator F w ∈ factorIdeal F ⊔ (originalPrime C) ^ curveTailOrder F w C h := by
  let p := originalPrime C
  letI : (factorIdeal F).IsPrime := factorIdeal_isPrime F h.irreducible
  let hle : factorIdeal F ≤ p := h.le_prime
  letI : (quotientPrime (factorIdeal F) p).IsPrime := quotientPrime_isPrime _ _ hle
  let R := FactorLocal F p hle
  letI : IsDiscreteValuationRing R :=
    local_isDVR F p h.irreducible hle h.prime_height h.separant_avoids_prime
  let N := tailNumerator F w
  let μ := curveTailOrder F w C h
  have hμ : 1 ≤ μ := (curve_intrinsic_tail_dichotomy F w pchar hpchar C h).1
  have horder : IsDiscreteValuationRing.addVal R (localMap F p hle N) = μ := by
    change IsDiscreteValuationRing.addVal R (localMap F p hle N) =
      (IsDiscreteValuationRing.addVal R (localMap F p hle N)).toNat
    apply (ENat.natCast_toNat ?_).symm
    intro ht
    change 1 ≤ (IsDiscreteValuationRing.addVal R (localMap F p hle N)).toNat at hμ
    rw [ht] at hμ
    simp at hμ
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hdvd : (u ^ μ : R) ∣ (localMap F p hle N : R) := by
    apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
    rw [hu.addVal_pow, horder]
  have hmem : localMap F p hle N ∈ maximalIdeal R ^ μ := by
    rw [hu.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hdvd
  exact RCN310.exists_multiplier_mem_sup_pow_of_localized_mem
    (factorIdeal F) p hle (quotientPrime (factorIdeal F) p) rfl N μ hmem

theorem curve_tail_mem_projected_primary
    (F : Carrier K) (w pchar : ℕ) [CharP K pchar] (hpchar : pchar.Prime)
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (h : CurveChartData F w C)
    {A : Type*} [CommRing A] (f : Carrier K →+* A)
    (surface : A) (J : Ideal A) [J.IsMaximal]
    (hcarrier : f F ∈ Ideal.span {surface}) (hsurface : surface ∈ J)
    (hcontract : J.comap f = originalPrime C) :
    f (tailNumerator F w) ∈ Ideal.span {surface} ⊔ J ^ curveTailOrder F w C h := by
  let p := originalPrime C
  let μ := curveTailOrder F w C h
  obtain ⟨s, hsnot, hsN⟩ := curve_tail_order_multiplier F w pchar hpchar C h
  have hmapF : Ideal.map f (factorIdeal F) ≤ Ideal.span {surface} := by
    rw [factorIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_le]
    exact Set.singleton_subset_iff.mpr hcarrier
  have hmapP : Ideal.map f p ≤ J := by
    rw [Ideal.map_le_iff_le_comap, hcontract]
  have hmapPow : Ideal.map f (p ^ μ) ≤ J ^ μ := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmapP μ
  have htarget : Ideal.map f (factorIdeal F ⊔ p ^ μ) ≤ Ideal.span {surface} ⊔ J ^ μ := by
    rw [Ideal.map_sup]
    exact sup_le (hmapF.trans le_sup_left) (hmapPow.trans le_sup_right)
  have hmul : f s * f (tailNumerator F w) ∈ Ideal.span {surface} ⊔ J ^ μ := by
    rw [← map_mul]
    exact htarget (Ideal.mem_map_of_mem f hsN)
  have hfs : f s ∉ J := by
    intro hmem
    apply hsnot
    rw [← hcontract]
    exact hmem
  exact RCN310.mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
    surface (f (tailNumerator F w)) (f s) J hsurface μ
    (curve_intrinsic_tail_dichotomy F w pchar hpchar C h).1 hfs hmul

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
