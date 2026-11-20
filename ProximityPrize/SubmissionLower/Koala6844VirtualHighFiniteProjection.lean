import ProximityPrize.SubmissionLower.LowerFoundation


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open RCN002 RCN004 RCN005 RCN010 RCN011 RCN013 RCN371
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

private theorem finite_of_proper_plane_roots
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (P Q : Polynomial (Polynomial K)) (hirreducible : Irreducible P)
    (hpositive : 0 < P.natDegree) (hproper : ¬ P ∣ Q)
    (y r : L)
    (hP : Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P = 0)
    (hQ : Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q = 0)
    (hgenerate : IntermediateField.adjoin K ({y, r} : Set L) = ⊤) :
    FiniteDimensional K L := by
  classical
  have hresne := RCN362.irreducible_resultant_ne_zero_of_not_dvd
    P Q hirreducible hpositive hproper
  have hresroot := RCN364.resultant_aeval_eq_zero_of_common_root
    P Q P.natDegree Q.natDegree le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpositive)) y r hP hQ
  have hy : IsIntegral K y := isAlgebraic_iff_isIntegral.mp ⟨_, hresne, hresroot⟩
  let S : IntermediateField K L := IntermediateField.adjoin K {y}
  let yS : S := ⟨y, IntermediateField.mem_adjoin_simple_self K y⟩
  letI : FiniteDimensional K S := IntermediateField.adjoin.finiteDimensional hy
  let g : Polynomial K →+* S := Polynomial.eval₂RingHom (algebraMap K S) yS
  let Py : Polynomial S := P.map g
  have hPyne : Py ≠ 0 := by
    have h := RCN360.bimap_specialization_ne_zero
      (algebraMap K S) P (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
    rw [RCN360.bimap_specialization] at h
    exact h
  have hcoefficient : (algebraMap S L).comp g =
      Polynomial.eval₂RingHom (algebraMap K L) y := by
    apply Polynomial.ringHom_ext
    · intro c
      change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS (Polynomial.C c)) =
        Polynomial.eval₂ (algebraMap K L) y (Polynomial.C c)
      rw [Polynomial.eval₂_C, Polynomial.eval₂_C]
      exact (IsScalarTower.algebraMap_apply K S L c).symm
    · change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS Polynomial.X) =
        Polynomial.eval₂ (algebraMap K L) y Polynomial.X
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X]
      rfl
  have hPyroot : Polynomial.aeval r Py = 0 := by
    change Polynomial.eval₂ (algebraMap S L) r (P.map g) = 0
    rw [Polynomial.eval₂_map, hcoefficient]
    exact hP
  have hr : IsIntegral S r := isAlgebraic_iff_isIntegral.mp ⟨Py, hPyne, hPyroot⟩
  have hrK : IsIntegral K r := isIntegral_trans (A := S) r hr
  letI : FiniteDimensional K (IntermediateField.adjoin K ({y, r} : Set L)) :=
    IntermediateField.finiteDimensional_adjoin_pair hy hrK
  letI : FiniteDimensional K (⊤ : IntermediateField K L) := by
    rw [← hgenerate]
    infer_instance
  exact Module.Finite.of_surjective
    (IntermediateField.topEquiv (F := K) (E := L)).toLinearMap
    (IntermediateField.topEquiv (F := K) (E := L)).surjective

theorem finite_literal_projection
    (K : Type) [Field K] (order : Fin 3 ≃ Fin 3)
    (C : Ideal (MvPolynomial (Fin 3) K)) [C.IsPrime]
    (ht : Transcendental K (coordinate K C (order 0)))
    (G T : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (hGmem : G ∈ C) (hTmem : T ∈ C) (hproper : ¬ G ∣ T) :
    letI := rationalBaseAlgebra K C (order 0) ht
    FiniteDimensional (RatFunc K) (CoordinateField K C) := by
  obtain ⟨order', _, sameBase, hpositive⟩ :=
    exists_positive_outer_order K order C G hG hGmem ht
  have ht' : Transcendental K (coordinate K C (order' 0)) := by simpa only [sameBase] using ht
  have bound :
      letI := rationalBaseAlgebra K C (order' 0) ht'
      FiniteDimensional (RatFunc K) (CoordinateField K C) := by
    letI := rationalBaseAlgebra K C (order' 0) ht'
    have hirr := planeMap_irreducible_of_component
      (K := K) (order := order') (P := C) (ht := ht') G hG hGmem
    have hproperPlane : ¬ planeMap K order' G ∣ planeMap K order' T := by
      intro h
      exact hproper ((planeMap_dvd_iff_of_component
        (K := K) (order := order') (P := C) (ht := ht') G T hG hGmem).mp h)
    have rootG : RCN361.planeEval (RatFunc K) (CoordinateField K C)
        (coordinate K C (order' 2)) (coordinate K C (order' 1)) (planeMap K order' G) = 0 :=
      (actualPlane_root_iff K order' C ht' G).mpr hGmem
    have rootT : RCN361.planeEval (RatFunc K) (CoordinateField K C)
        (coordinate K C (order' 2)) (coordinate K C (order' 1)) (planeMap K order' T) = 0 :=
      (actualPlane_root_iff K order' C ht' T).mpr hTmem
    rw [RCN365.planeEval_eq_eval₂] at rootG rootT
    exact finite_of_proper_plane_roots (planeMap K order' G) (planeMap K order' T)
      hirr hpositive hproperPlane (coordinate K C (order' 2)) (coordinate K C (order' 1))
      rootG rootT (actual_generators K order' C ht')
  let summary (alg : Algebra (RatFunc K) (CoordinateField K C)) :=
    letI := alg
    FiniteDimensional (RatFunc K) (CoordinateField K C)
  change summary (rationalBaseAlgebra K C (order 0) ht)
  have sameAlgebra := rationalBaseAlgebra_congr K C (order' 0) (order 0) sameBase ht' ht
  rw [← sameAlgebra]
  exact bound

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

