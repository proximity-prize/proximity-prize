import ProximityPrize.SubmissionLower.GK
namespace ProximityPrize.SubmissionLower.RCN297
open RCN307
open RCN308
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R:Type*} [CommRing R] [IsLocalRing R]
theorem exists_specialized_monic_reducer
   (P:Polynomial R)
   (hPbar:P.map (IsLocalRing.residue R)≠0):
   ∃ M:Polynomial R,
     M.Monic∧
     M∈Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R)∧
     M.natDegree ≤ P.natDegree:=by
 let k:=IsLocalRing.ResidueField R
 let q:R →+*k:=IsLocalRing.residue R
 let Pbar:Polynomial k:=P.map q
 let Mbar:Polynomial k:=Pbar*Polynomial.C Pbar.leadingCoeff⁻¹
 have hMbarMonic:Mbar.Monic:=
   Polynomial.monic_mul_leadingCoeff_inv hPbar
 have hMbarLift:Mbar∈Polynomial.lifts q:=
   Polynomial.mem_lifts_of_surjective (IsLocalRing.residue_surjective) Mbar
 obtain ⟨M,hMmap,hMdegree,hMMonic⟩:=
   Polynomial.lifts_and_natDegree_eq_and_monic hMbarLift hMbarMonic
 obtain ⟨c,hc⟩:=IsLocalRing.residue_surjective Pbar.leadingCoeff⁻¹
 change q c=Pbar.leadingCoeff⁻¹ at hc
 let D:Polynomial R:=M-Polynomial.C c*P
 have hDmap:D.map q=0:=by
   dsimp only [D]
   rw [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
     hMmap,hc]
   dsimp only [Mbar]
   ring
 have hDcoeff:D∈coefficientMaxIdeal (R:=R):=by
   have hker:D∈RingHom.ker (Polynomial.mapRingHom q):=hDmap
   rw [Polynomial.ker_mapRingHom,IsLocalRing.ker_residue] at hker
   exact hker
 have hMmem:M∈Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=by
   have hfirst:Polynomial.C c*P∈Ideal.span {P}:=
     (Ideal.span {P}).mul_mem_left _
       (Ideal.subset_span (Set.mem_singleton P))
   have hfirst':Polynomial.C c*P∈
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=
     (show Ideal.span {P} ≤
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R) from le_sup_left) hfirst
   have hDcoeff':D∈
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=
     (show coefficientMaxIdeal (R:=R) ≤
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R) from le_sup_right) hDcoeff
   have hadd:=(Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R)).add_mem
     hfirst' hDcoeff'
   convert hadd using 1 <;>
     simp only [D] <;> ring
 have hdegreeBar:Mbar.natDegree=Pbar.natDegree:=
   Polynomial.natDegree_mul_leadingCoeff_inv Pbar hPbar
 refine ⟨M,hMMonic,hMmem,?_⟩
 rw [hMdegree,hdegreeBar]
 exact Polynomial.natDegree_map_le
end
end ProximityPrize.SubmissionLower.RCN297
