import ProximityPrize.SubmissionLower.CE
namespace ProximityPrize.SubmissionLower.ContactSylvesterPrimaryDirect6733Research
open scoped Classical BigOperators
open Module
open ContactMatrixCokernelOrder6732Research
open ContactSylvesterCokernelQuotient6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
theorem moduleFinite_quotient_of_monic_mem
   (I:Ideal (Polynomial R)) (M:Polynomial R)
   (hMMonic:M.Monic) (hMmem:M∈I):
   Module.Finite R (Polynomial R ⧸ I):=by
 let hle:Ideal.span {M} ≤ I:=Ideal.span_le.mpr (by simpa)
 let f:(Polynomial R ⧸ Ideal.span {M}) →ₐ[R]
     (Polynomial R ⧸ I):=Ideal.Quotient.factorₐ R hle
 letI:Module.Finite R (Polynomial R ⧸ Ideal.span {M}):=
   hMMonic.finite_quotient
 exact Module.Finite.of_surjective f.toLinearMap
   (Ideal.Quotient.factor_surjective hle)
def rawPiecesMap
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (pieces:J → Ideal (Polynomial R)):
   Polynomial.degreeLT R (m+n) →ₗ[R]
     (∀ j,Polynomial R ⧸ pieces j):=
 LinearMap.pi fun j↦
   ((Submodule.mkQ (pieces j)).restrictScalars R).comp
     (Submodule.subtype (Polynomial.degreeLT R (m+n)))
theorem range_sylvesterMap_le_ker_rawPiecesMap
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j):
   LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap) ≤
     LinearMap.ker (rawPiecesMap P Q m n pieces):=by
 rintro y ⟨v,rfl⟩
 rw [LinearMap.mem_ker]
 funext j
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 apply hcontains j
 change P*(v.2:Polynomial R)+Q*(v.1:Polynomial R)∈
   intersectionIdeal P Q
 exact Ideal.add_mem _
   (Ideal.mul_mem_right _ _
     (Ideal.subset_span (Set.mem_insert P {Q})))
   (Ideal.mul_mem_right _ _
     (Ideal.subset_span (Set.mem_insert_of_mem P (Set.mem_singleton Q))))
def cokerToPieces
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j):
   (Polynomial.degreeLT R (m+n) ⧸
     LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap)) →ₗ[R]
       (∀ j,Polynomial R ⧸ pieces j):=
 (LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap)).liftQ
   (rawPiecesMap P Q m n pieces)
   (range_sylvesterMap_le_ker_rawPiecesMap
     P Q m n hPcap hQcap pieces hcontains)
theorem cokerToPieces_surjective_of_modMax
   [IsLocalRing R]
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   [Module.Finite R (∀ j,Polynomial R ⧸ pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces))):
   Function.Surjective
     (cokerToPieces P Q m n hPcap hQcap pieces hcontains):=by
 let target:=∀ j,Polynomial R ⧸ pieces j
 let maxTarget:=IsLocalRing.maximalIdeal R •
   (⊤:Submodule R target)
 have hraw:Function.Surjective (rawPiecesMap P Q m n pieces):=by
   apply LinearMap.surjective_of_surjective_comp_mkQ
     (rawPiecesMap P Q m n pieces) (IsLocalRing.maximalIdeal R)
     (IsLocalRing.maximalIdeal_le_jacobson ⊥)
   exact hmod
 intro y
 obtain ⟨v,hv⟩:=hraw y
 refine ⟨Submodule.Quotient.mk v,?_⟩
 change rawPiecesMap P Q m n pieces v=y
 exact hv
end
end ProximityPrize.SubmissionLower.ContactSylvesterPrimaryDirect6733Research
