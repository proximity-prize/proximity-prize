import ProximityPrize.SubmissionLower.LowerFoundation
import ProximityPrize.SubmissionLower.Koala6831IntrinsicRegular



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic

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

theorem residual_local_order
    (F W : Carrier K) (B N : ℕ → Carrier K) (pchar : ℕ) [CharP K pchar]
    (hpchar : pchar.Prime)
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (height : C.height ≤ 2) (hirr : Irreducible F)
    (carrier_mem : surfaceMap (polynomialEmbedding K) F ∈ C)
    (separant_avoids : surfaceMap (polynomialEmbedding K) (implicitRegularity F) ∉ C)
    (first_mem : surfaceMap (polynomialEmbedding K) (N 0) ∈ C)
    (first_proper : ¬ F ∣ N 0)
    (leading_avoids : surfaceMap (polynomialEmbedding K) W ∉ C)
    (recurrence : ∀ j, N (j+1) = W * clearedImplicit F (N j) - B j * N j) :
    ∃ μ : ℕ, 1 ≤ μ ∧
      (∃ s : Carrier K, s ∉ originalPrime C ∧
        s * N 0 ∈ factorIdeal F ⊔ (originalPrime C)^μ) ∧
      ((∃ delay, 1 ≤ delay ∧ delay ≤ μ ∧ surfaceMap (polynomialEmbedding K) (N delay) ∉ C) ∨
        (∀ delay, surfaceMap (polynomialEmbedding K) (N delay) ∈ C)) := by
  let p := originalPrime C
  letI : (factorIdeal F).IsPrime := factorIdeal_isPrime F hirr
  have hle : factorIdeal F ≤ p := by
    apply Ideal.span_le.mpr
    intro G hG
    rw [Set.mem_singleton_iff.mp hG]
    exact (mem_originalPrime_iff C F).2 carrier_mem
  letI : (quotientPrime (factorIdeal F) p).IsPrime := quotientPrime_isPrime _ _ hle
  let R := FactorLocal F p hle
  have hheight : p.height = 2 :=
    originalPrime_height_eq_two C height F (N 0) hirr carrier_mem first_mem first_proper
  have hS : implicitRegularity F ∉ p :=
    fun hmem => separant_avoids ((mem_originalPrime_iff C _).1 hmem)
  letI : IsDiscreteValuationRing R := local_isDVR F p hirr hle hheight hS
  letI : CharP R pchar := charP_of_injective_algebraMap
    (algebraMap K R).injective pchar
  let ρ := localMap F p hle
  let D := localCleared F p hle
  let A : ℕ → R := fun j => ρ (N j)
  let H : R := ρ W
  have step (j : ℕ) : A (j+1) = H * D (A j) - ρ (B j) * A j * 1 := by
    unfold A H ρ D
    rw [recurrence j]
    simp only [map_mul, map_sub, localCleared_map, mul_one]
  have hunit (G : Carrier K) : IsUnit (ρ G) ↔
      surfaceMap (polynomialEmbedding K) G ∉ C :=
    (localMap_isUnit_iff F p hle G).trans (not_congr (mem_originalPrime_iff C G))
  have hne : A 0 ≠ 0 := localMap_ne_zero F p hle _ first_proper
  have hnonunit : ¬ IsUnit (A 0) := fun h => (hunit (N 0)).mp h first_mem
  let μ := (IsDiscreteValuationRing.addVal R (A 0)).toNat
  obtain ⟨hμ, hcut⟩ := RCN073.recurrence_unit_or_persistent D H 1
    (fun j => ρ (B j)) A pchar hpchar step ((hunit W).mpr leading_avoids) hne hnonunit
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨k, v, hA⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hu
  have heq : μ = k := by
    dsimp only [μ]
    rw [IsDiscreteValuationRing.addVal_def (A 0) v hu k hA]
    simp
  have hpow : A 0 ∈ maximalIdeal R ^ μ := by
    rw [heq, hu.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hA]
    exact dvd_mul_left _ _
  refine ⟨μ, hμ, ?_, ?_⟩
  · exact RCN310.exists_multiplier_mem_sup_pow_of_localized_mem
      (factorIdeal F) p hle (quotientPrime (factorIdeal F) p) rfl (N 0) μ hpow
  · rcases hcut with ⟨d, hd, hdμ, hdu⟩ | hpersist
    · exact Or.inl ⟨d, hd, hdμ, (hunit (N d)).mp hdu⟩
    · exact Or.inr (fun j => not_not.mp (fun h => hpersist j ((hunit (N j)).mpr h)))

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
