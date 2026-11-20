import ProximityPrize.SubmissionLower.Koala6844VirtualHighFiniteProjection
import ProximityPrize.SubmissionLower.Koala6844VirtualHighPowerEnvelope
import Mathlib.FieldTheory.SeparablyGenerated


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open RCN002 RCN004 RCN005 RCN022 RCN129 RCN264 RCN341 Koala6831Intrinsic

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option linter.style.haveILetI false

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable {G T H : MvPolynomial (Fin 3) Ω}

theorem regularComponent_exists_separating_literal
    (p : ℕ) [ExpChar Ω p] [PerfectRing Ω p] (hp : p.Prime)
    (C : RegularComponent Ω G T H) (hG : Irreducible G) (hproper : ¬ G ∣ T) :
    Nonempty (SeparableLiteralCoordinate C.1) := by
  classical
  let P := C.1
  let L := CoordinateField Ω P
  letI : ExpChar L p := expChar_of_injective_algebraMap (algebraMap Ω L).injective p
  obtain ⟨i₀, hi₀⟩ := exists_transcendental_coordinate_of_ne_point_kernel Ω P
    (regularComponent_ne_point Ω G T H C)
  have hFinite (i : Fin 3) (hi : Transcendental Ω (coordinate Ω P i)) :
      letI := rationalBaseAlgebra Ω P i hi
      FiniteDimensional (RatFunc Ω) L := by
    let order := Equiv.swap (0 : Fin 3) i
    have h0 : order 0 = i := Equiv.swap_apply_left 0 i
    have ht : Transcendental Ω (coordinate Ω P (order 0)) := by
      rw [h0]
      exact hi
    have h := finite_literal_projection Ω order P ht G T hG
      (regularComponent_G_mem Ω G T H C) (regularComponent_T_mem Ω G T H C) hproper
    rw [rationalBaseAlgebra_congr Ω P _ _ h0 ht hi] at h
    exact h
  have hTrdeg : Algebra.trdeg Ω L ≤ 1 := by
    letI := rationalBaseAlgebra Ω P i₀ hi₀
    letI := rationalBaseScalarTower Ω P i₀ hi₀
    letI := hFinite i₀ hi₀
    exact trdeg_le_one_of_functionField Ω L
  letI : Algebra.EssFiniteType Ω L :=
    IntermediateField.fg_top_iff.mp
      (adjoin_coordinates_eq_top Ω P ▸
        IntermediateField.fg_adjoin_of_finite (Set.finite_range (coordinate Ω P)))
  obtain ⟨s, sbasis, ssep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField Ω L
  have hn : Nonempty (↑s : Type) :=
    sbasis.nonempty_iff_transcendental.mpr ⟨coordinate Ω P i₀, hi₀⟩
  have hcard : s.card ≤ 1 := by
    have hc := sbasis.cardinalMk_eq_trdeg.trans_le hTrdeg
    rw [Cardinal.mk_fintype, Fintype.card_coe] at hc
    exact_mod_cast hc
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨hn.some.1, hn.some.2⟩
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp (by omega : s.card = 1)
  have ht : Transcendental Ω t := sbasis.1.transcendental ⟨t, by simp⟩
  let A := IntermediateField.adjoin Ω ({t} : Set L)
  letI : Algebra.IsSeparable A L := by
    have hset : (↑({t} : Finset L) : Set L) = ({t} : Set L) := Finset.coe_singleton t
    rw [hset] at ssep
    exact ssep
  let f := elementEmbedding Ω L t ht
  let e : RatFunc Ω ≃ₐ[Ω] A := RatFunc.algEquivOfTranscendental t ht
  have htsep : letI := f.toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) L := by
    letI := f.toRingHom.toAlgebra
    apply Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L)
    apply RingHom.ext
    intro a
    change f (e.symm a) = (a : L)
    rw [show f = A.val.comp e.toAlgHom from elementEmbedding_eq_adjoin_comp Ω L t ht]
    simp
  have htf : letI := f.toRingHom.toAlgebra
      FiniteDimensional (RatFunc Ω) L :=
    finiteDimensional_elementEmbedding Ω L _ (hFinite i₀ hi₀) t ht
  have htNonpower : t ∉ powerField L p := by
    letI := f.toRingHom.toAlgebra
    letI := htsep
    letI : ExpChar (RatFunc Ω) p :=
      expChar_of_injective_algebraMap (algebraMap Ω (RatFunc Ω)).injective p
    have h := separating_ratFunc_coordinate_notin_powerField (K := Ω) (E := L) p hp
    rw [show algebraMap (RatFunc Ω) L RatFunc.X = t from by
      change f RatFunc.X = t
      rw [← RatFunc.algebraMap_X]
      exact elementEmbedding_variable Ω L t ht] at h
    exact h
  have hNonpower : ∃ i, coordinate Ω P i ∉ powerField L p := by
    by_contra! hall
    let S : IntermediateField Ω L :=
      (powerField L p).toIntermediateField (algebraMap_mem_powerField p)
    have hle : IntermediateField.adjoin Ω (Set.range (coordinate Ω P)) ≤ S :=
      IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
    rw [adjoin_coordinates_eq_top] at hle
    exact htNonpower (hle (IntermediateField.mem_top : t ∈ (⊤ : IntermediateField Ω L)))
  obtain ⟨i, hi⟩ := hNonpower
  have hit : Transcendental Ω (coordinate Ω P i) := by
    intro ha
    obtain ⟨a, ha⟩ := coordinate_eq_scalar_of_isAlgebraic Ω P i ha
    exact hi (ha ▸ algebraMap_mem_powerField p a)
  have hisep := separable_affine_projection_from_seed p hp t (coordinate Ω P i)
    ht hit hi htsep (hFinite i hit)
  exact ⟨⟨i, hit, hFinite i hit, hisep⟩⟩

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

