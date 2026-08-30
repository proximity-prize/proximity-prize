import ProximityPrize.SubmissionLower.FK
import ProximityPrize.SubmissionLower.GB
namespace ProximityPrize.SubmissionLower.RCN143
open scoped Classical BigOperators
open RCN227
open RCN307
open RCN309
open RCN308
open RCN297
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Base:Type} [Field Base] [DecidableEq Base]
variable (primeIdeal:Ideal (Polynomial Base)) [primeIdeal.IsPrime]
variable (factor:Polynomial Base)
abbrev LocalBase:=Localization.AtPrime primeIdeal
theorem grouped_resultant_power_dvd_of_primary_pieces_modMax
   {J:Type*} [Fintype J] (multiplicity:J → ℕ)
   (hprime:primeIdeal=Ideal.span {factor})
   (hfactor:Irreducible factor) (hfactorMonic:factor.Monic)
   (P₀ Q₀:Polynomial (Polynomial Base)) (m n:ℕ)
   (P Q:Polynomial (LocalBase primeIdeal))
   (hPmap:P=P₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hQmap:Q=Q₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P₀ Q₀ m n≠0)
   (C:PrimaryPiecesCertificate P Q multiplicity)
   [Module.Finite (LocalBase primeIdeal)
     (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal (LocalBase primeIdeal) •
         (⊤:Submodule (LocalBase primeIdeal)
           (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j))).mkQ).comp
       (rawPiecesMap P Q m n C.pieces))):
   factor^(∑ j,multiplicity j)∣
     Polynomial.resultant P₀ Q₀ m n:=by
 have hp0:primeIdeal≠⊥:=by
   rw [hprime,ne_eq,Ideal.span_singleton_eq_bot]
   exact hfactor.ne_zero
 letI:IsDiscreteValuationRing (LocalBase primeIdeal):=
   IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
     (Polynomial Base) hp0 _
 have hmappedResultant:Polynomial.resultant P Q m n=
     algebraMap (Polynomial Base) (LocalBase primeIdeal)
       (Polynomial.resultant P₀ Q₀ m n):=by
   rw [hPmap,hQmap,Polynomial.resultant_map_map]
 have hmappedNe:Polynomial.resultant P Q m n≠0:=by
   rw [hmappedResultant]
   simpa only [map_zero] using
     (FaithfulSMul.algebraMap_injective
       (Polynomial Base) (LocalBase primeIdeal)).ne hresultant
 have hlocal:=
   sum_multiplicities_le_ord_resultant_of_primary_pieces_modMax
     P Q m n hPcap hQcap hmappedNe C.pieces C.contains hmod
       multiplicity C.length_le
 have hlocal':
     (((∑ j,multiplicity j:ℕ):ℕ∞)) ≤
       Ring.ord (LocalBase primeIdeal)
         (algebraMap (Polynomial Base) (LocalBase primeIdeal)
           (Polynomial.resultant P₀ Q₀ m n)):=by
   rw [←hmappedResultant]
   exact hlocal
 exact pow_sum_dvd_of_sum_le_localized_ord primeIdeal factor
   (Polynomial.resultant P₀ Q₀ m n) hprime hfactor hfactorMonic
     hresultant multiplicity hlocal'
theorem grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
   {J:Type*} [Fintype J] (multiplicity:J → ℕ)
   (hprime:primeIdeal=Ideal.span {factor})
   (hfactor:Irreducible factor) (hfactorMonic:factor.Monic)
   (P₀ Q₀:Polynomial (Polynomial Base)) (m n:ℕ)
   (P Q:Polynomial (LocalBase primeIdeal))
   (hPmap:P=P₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hQmap:Q=Q₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P₀ Q₀ m n≠0)
   (hPbar:P.map (IsLocalRing.residue (LocalBase primeIdeal))≠0)
   (C:PrimaryPiecesCertificate P Q multiplicity)
   [Module.Finite (LocalBase primeIdeal)
     (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j)]:
   factor^(∑ j,multiplicity j)∣
     Polynomial.resultant P₀ Q₀ m n:=by
 obtain ⟨M,hMMonic,hMmem,hMdegreeP⟩:=
   exists_specialized_monic_reducer P hPbar
 have hspan:Ideal.span {P} ≤ intersectionIdeal P Q:=by
   rw [Ideal.span_le]
   intro x hx
   rw [Set.mem_singleton_iff] at hx
   subst x
   exact Ideal.subset_span (Set.mem_insert P {Q})
 have hMmem':M∈intersectionIdeal P Q ⊔
     coefficientMaxIdeal (R:=LocalBase primeIdeal):=
   (sup_le_sup hspan le_rfl) hMmem
 have hMdegree:M.natDegree ≤ m+n:=
   hMdegreeP.trans (hPcap.trans (Nat.le_add_right m n))
 have hmod:=rawPieces_modMax_surjective_of_monic_mod
   P Q m n C.pieces C.coprime C.contains M hMMonic hMmem' hMdegree
 exact grouped_resultant_power_dvd_of_primary_pieces_modMax
   primeIdeal factor multiplicity hprime hfactor hfactorMonic
     P₀ Q₀ m n P Q hPmap hQmap hPcap hQcap hresultant C hmod
end
end ProximityPrize.SubmissionLower.RCN143
