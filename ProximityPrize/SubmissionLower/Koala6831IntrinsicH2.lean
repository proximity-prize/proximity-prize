import ProximityPrize.SubmissionLower.Koala6831IntrinsicLinearProjection
import ProximityPrize.SubmissionLower.Koala6831IntrinsicPDegree
import ProximityPrize.SubmissionLower.Koala6831IntrinsicSeparableCriterion


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open MvPolynomial RCN002 RCN022

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {K E : Type} [Field K] [Field E] [Algebra K E]

theorem separable_affine_projection_from_seed (p : ℕ) [ExpChar K p] [ExpChar E p]
    [PerfectRing K p] (hp : p.Prime) (s u : E) (hs : Transcendental K s)
    (hu : Transcendental K u) (hnonpower : u ∉ powerField E p)
    (seedSeparable : letI : Algebra (RatFunc K) E :=
      (elementEmbedding K E s hs).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) E)
    (affineFinite : letI : Algebra (RatFunc K) E :=
      (elementEmbedding K E u hu).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) E) :
    letI : Algebra (RatFunc K) E := (elementEmbedding K E u hu).toRingHom.toAlgebra
    Algebra.IsSeparable (RatFunc K) E := by
  letI : ExpChar (RatFunc K) p :=
    expChar_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
  have hSeedGen : IntermediateField.adjoin (powerField E p) ({s} : Set E) = ⊤ := by
    letI : Algebra (RatFunc K) E := (elementEmbedding K E s hs).toRingHom.toAlgebra
    letI : Algebra.IsSeparable (RatFunc K) E := seedSeparable
    letI : IsScalarTower K (RatFunc K) E :=
      IsScalarTower.of_algebraMap_eq (fun c => ((elementEmbedding K E s hs).commutes c).symm)
    have hembed : algebraMap (RatFunc K) E (RatFunc.X : RatFunc K) = s := by
      change elementEmbedding K E s hs _ = s
      rw [← RatFunc.algebraMap_X, elementEmbedding_variable]
    have h := adjoin_powerField_singleton_eq_top_of_ratFunc (K := K) (E := E) p
    rwa [hembed] at h
  have hseedNonpower : s ∉ powerField E p := by
    letI : Algebra (RatFunc K) E := (elementEmbedding K E s hs).toRingHom.toAlgebra
    letI : Algebra.IsSeparable (RatFunc K) E := seedSeparable
    have hembed : algebraMap (RatFunc K) E (RatFunc.X : RatFunc K) = s := by
      change elementEmbedding K E s hs _ = s
      rw [← RatFunc.algebraMap_X, elementEmbedding_variable]
    have hh := separating_ratFunc_coordinate_notin_powerField (K := K) (E := E) p hp
    rwa [hembed] at hh
  letI : FiniteDimensional (powerField E p) E := finiteDimensional_powerField p s hSeedGen
  have hdeg := finrank_powerField p hp s hseedNonpower hSeedGen
  have hgen := adjoin_powerField_singleton_eq_top_of_finrank p hp u hnonpower hdeg
  letI : Algebra (RatFunc K) E := (elementEmbedding K E u hu).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc K) E := affineFinite
  have hembed : algebraMap (RatFunc K) E (RatFunc.X : RatFunc K) = u := by
    change elementEmbedding K E u hu _ = u
    rw [← RatFunc.algebraMap_X, elementEmbedding_variable]
  exact isSeparable_of_powerField_single_generator p (RatFunc.X : RatFunc K) (by rwa [hembed])

theorem active_pair_has_nonpower
    (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (p : ℕ) [ExpChar (CoordinateField K P) p] [PerfectRing K p] (hp : p.Prime)
    (hnonpower : coordinate K P 2 ∉ powerField (CoordinateField K P) p)
    (G T : MvPolynomial (Fin 3) K) (hG : Irreducible G) (hGmem : G ∈ P)
    (hTmem : T ∈ P) (hproper : ¬ G ∣ T)
    (hGz : G.degreeOf 2 < p) (hTz : T.degreeOf 2 < p)
    (hactive : Transcendental K (coordinate K P 0) ∨ Transcendental K (coordinate K P 1)) :
    coordinate K P 0 ∉ powerField (CoordinateField K P) p ∨
      coordinate K P 1 ∉ powerField (CoordinateField K P) p := by
  rcases hactive with hY | hZ₀
  · let order : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
    have h0 : order 0 = 0 := by decide
    have h1 : order 1 = 2 := by decide
    have h2 : order 2 = 1 := by decide
    have h := proper_curve_projection_has_nonpower P order (by rwa [h0]) p hp
      (by rwa [h1]) G T hG hGmem hTmem hproper (by rwa [h1]) (by rwa [h1])
    simpa only [h0, h2] using h
  · let order : Fin 3 ≃ Fin 3 := (Equiv.swap 0 2).trans (Equiv.swap 1 2)
    have h0 : order 0 = 1 := by decide
    have h1 : order 1 = 2 := by decide
    have h2 : order 2 = 0 := by decide
    have h := proper_curve_projection_has_nonpower P order (by rwa [h0]) p hp
      (by rwa [h1]) G T hG hGmem hTmem hproper (by rwa [h1]) (by rwa [h1])
    simpa only [h0, h2, or_comm] using h

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
