import ProximityPrize.SubmissionLower.CF
namespace ProximityPrize.SubmissionLower.ContactSylvesterModMax6733Research
open scoped Classical
open ContactSylvesterCokernelQuotient6732Research
open ContactSylvesterPrimaryDirect6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [IsLocalRing R]
def fullPiecesRingHom
   {J:Type*} [Fintype J]
   (pieces:J → Ideal (Polynomial R)):
   Polynomial R →+*(∀ j,Polynomial R ⧸ pieces j):=
 RingHom.pi fun j↦Ideal.Quotient.mk (pieces j)
def coefficientMaxIdeal:Ideal (Polynomial R):=
 Ideal.map (Polynomial.C:R →+*Polynomial R)
   (IsLocalRing.maximalIdeal R)
theorem rawPieces_modMax_surjective_of_monic_mod
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (pieces:J → Ideal (Polynomial R))
   (hcoprime:Pairwise fun i j↦IsCoprime (pieces i) (pieces j))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   (M:Polynomial R) (hMMonic:M.Monic)
   (hMmem:M∈intersectionIdeal P Q ⊔ coefficientMaxIdeal (R:=R))
   (hMdegree:M.natDegree ≤ m+n):
   Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces)):=by
 let target:=∀ j,Polynomial R ⧸ pieces j
 let full:=fullPiecesRingHom pieces
 let maxTarget:=IsLocalRing.maximalIdeal R •
   (⊤:Submodule R target)
 have hfullC:full.comp (Polynomial.C:R →+*Polynomial R)=
     algebraMap R target:=by
   ext r j
   rfl
 have hcoeffMap:Ideal.map full (coefficientMaxIdeal (R:=R))=
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
   rw [coefficientMaxIdeal,Ideal.map_map,hfullC]
 have hinterZero:∀ x∈intersectionIdeal P Q,full x=0:=by
   intro x hx
   funext j
   exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcontains j hx)
 have hMmax:full M∈
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
   obtain ⟨a,ha,b,hb,hab⟩:=Submodule.mem_sup.mp hMmem
   have hfa:full a=0:=hinterZero a ha
   have hfb:full b∈
       Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
     rw [←hcoeffMap]
     exact Ideal.mem_map_of_mem full hb
   rw [←hab,map_add,hfa,zero_add]
   exact hfb
 intro ybar
 obtain ⟨y,rfl⟩:=Submodule.mkQ_surjective maxTarget ybar
 obtain ⟨A,hA⟩:=Ideal.pi_mkQ_surjective hcoprime y
 let rem:Polynomial R:=A %ₘ M
 have hremDegree:rem.degree < (m+n:ℕ):=by
   have hlt:=Polynomial.degree_modByMonic_lt A hMMonic
   rw [Polynomial.degree_eq_natDegree hMMonic.ne_zero] at hlt
   exact hlt.trans_le (by exact_mod_cast hMdegree)
 let v:Polynomial.degreeLT R (m+n):=
   ⟨rem,Polynomial.mem_degreeLT.mpr hremDegree⟩
 refine ⟨v,?_⟩
 change maxTarget.mkQ (rawPiecesMap P Q m n pieces v)=maxTarget.mkQ y
 rw [Submodule.mkQ_apply,Submodule.mkQ_apply,Submodule.Quotient.eq]
 have hraw:rawPiecesMap P Q m n pieces v=full rem:=by
   rfl
 have hfullA:full A=y:=hA
 rw [hraw, ←hfullA, ←map_sub]
 have hdiff:rem-A= -(M*(A/ₘ M)):=by
   dsimp only [rem]
   rw [Polynomial.modByMonic_eq_sub_mul_div]
   ring
 rw [hdiff,map_neg,map_mul]
 have hmul:full M*full (A/ₘ M)∈
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=
   Ideal.mul_mem_right _ _ hMmax
 have hmul':full M*full (A/ₘ M)∈maxTarget:=by
   change full M*full (A/ₘ M)∈
     IsLocalRing.maximalIdeal R • (⊤:Submodule R target)
   rw [Ideal.smul_top_eq_map]
   exact hmul
 exact maxTarget.neg_mem hmul'
theorem sum_multiplicities_le_ord_resultant_of_primary_pieces_modMax
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   [Module.Finite R (∀ j,Polynomial R ⧸ pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces)))
   (multiplicity:J → ℕ)
   (hlength:∀ j,(multiplicity j:ℕ∞) ≤
     Module.length R (Polynomial R ⧸ pieces j)):
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
     Ring.ord R (Polynomial.resultant P Q m n):=by
 classical
 letI:DecidableEq (Fin (m+n)):=Classical.decEq _
 let f:=Polynomial.sylvesterMap P Q hPcap hQcap
 have hinj:Function.Injective f:=by
   intro x y hxy
   apply sub_eq_zero.mp
   let z:=x-y
   have hfz:f z=0:=by simp [z,f,hxy]
   have hcomp:=LinearMap.congr_fun
     (Polynomial.adjSylvester_comp_sylveserMap P Q hPcap hQcap) z
   have hscalar:Polynomial.resultant P Q m n • z=0:=by
     rw [LinearMap.comp_apply,hfz,map_zero] at hcomp
     simpa using hcomp.symm
   exact (smul_eq_zero.mp hscalar).resolve_left hresultant
 have hbound:=
   ContactMatrixCokernelOrder6732Research.sum_multiplicities_le_ord_toMatrix_det_of_surjective
     (Polynomial.degreeLT.basisProd R m n)
     (Polynomial.degreeLT.basis R (m+n)) f hinj
     (fun j↦Polynomial R ⧸ pieces j) multiplicity hlength
     (ContactSylvesterPrimaryDirect6733Research.cokerToPieces
       P Q m n hPcap hQcap pieces hcontains)
     (cokerToPieces_surjective_of_modMax P Q m n hPcap hQcap
       pieces hcontains hmod)
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd R m n)
     (Polynomial.degreeLT.basis R (m+n)) f=
       Polynomial.sylvester P Q m n:=by
   ext i j
   obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective j
   simpa [f,Polynomial.degreeLT.basisProd,LinearMap.toMatrix_apply] using
     congr($(Polynomial.toMatrix_sylvesterMap P Q hPcap hQcap) i j)
 calc
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
       Ring.ord R (LinearMap.toMatrix
         (Polynomial.degreeLT.basisProd R m n)
         (Polynomial.degreeLT.basis R (m+n)) f).det:=hbound
   _=Ring.ord R (Polynomial.resultant P Q m n):=by
     rw [hmatrix]
     congr 1
     unfold Polynomial.resultant
     convert! rfl
end
end ProximityPrize.SubmissionLower.ContactSylvesterModMax6733Research
