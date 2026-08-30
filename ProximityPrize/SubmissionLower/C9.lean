import ProximityPrize.SubmissionLower.CF
namespace ProximityPrize.SubmissionLower.RCN197
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [IsLocalRing R]
@[reducible] def relationResidueAlgebra
   (J:Ideal (Polynomial R))
   (hcontract:J.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R):
   Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=
 (Ideal.quotientMap J (Polynomial.C:R →+*Polynomial R) (by
   rw [hcontract])).toAlgebra' (fun _ _ => mul_comm _ _)
theorem exists_monic_mem_maximal_relation
   (J:Ideal (Polynomial R)) [J.IsMaximal]
   (hcontract:J.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hfinite:
     letI:=relationResidueAlgebra J hcontract
     FiniteDimensional (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ J)):
   ∃ H:Polynomial R,H.Monic∧H∈J:=by
 let k:=IsLocalRing.ResidueField R
 let E:=Polynomial R ⧸ J
 let qR:R →+*k:=Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
 let qB:Polynomial R →+*E:=Ideal.Quotient.mk J
 let aResidue:=relationResidueAlgebra J hcontract
 letI:Algebra k E:=aResidue
 let phi:k →+*E:=algebraMap k E
 letI:FiniteDimensional k E:=hfinite
 let y:E:=qB Polynomial.X
 let hbar:Polynomial k:=minpoly k y
 have hbarMonic:hbar.Monic:=
   minpoly.monic (IsIntegral.of_finite k y)
 have hbarLift:hbar∈Polynomial.lifts qR:=
   Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective hbar
 obtain ⟨H,hmap,hdegree,hHMonic⟩:=
   Polynomial.lifts_and_natDegree_eq_and_monic hbarLift hbarMonic
 have hcomp:(Polynomial.eval₂RingHom phi y).comp
     (Polynomial.mapRingHom qR)=qB:=by
   apply Polynomial.ringHom_ext
   · intro r
     simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,
       Polynomial.map_C,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
     change Ideal.Quotient.mk J (Polynomial.C r)=qB (Polynomial.C r)
     rfl
   · simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,
       Polynomial.map_X,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
     rfl
 have hHmem:H∈J:=by
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   change qB H=0
   rw [←hcomp]
   change Polynomial.eval₂ phi y (H.map qR)=0
   rw [hmap]
   change Polynomial.aeval y hbar=0
   exact minpoly.aeval k y
 exact ⟨H,hHMonic,hHmem⟩
theorem moduleFinite_primary_piece_of_maximal_relation
   (J:Ideal (Polynomial R)) [J.IsMaximal]
   (hcontract:J.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hfinite:
     letI:=relationResidueAlgebra J hcontract
     FiniteDimensional (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ J))
   (piece:Ideal (Polynomial R)) (mu:ℕ)
   (hpow:J^mu ≤ piece):
   Module.Finite R (Polynomial R ⧸ piece):=by
 obtain ⟨H,hHMonic,hHJ⟩:=
   exists_monic_mem_maximal_relation J hcontract hfinite
 exact RCN309.moduleFinite_quotient_of_monic_mem
   piece (H^mu) (hHMonic.pow mu) (hpow (Ideal.pow_mem_pow hHJ mu))
end
end ProximityPrize.SubmissionLower.RCN197
