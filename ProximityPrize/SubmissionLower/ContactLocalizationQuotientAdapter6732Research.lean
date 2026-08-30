import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.ContactLocalizationQuotientAdapter6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {A B:Type*} [CommRing A] [CommRing B]
variable (M:Submonoid A) [Algebra A B] [IsLocalization M B]
@[reducible] def quotientAlgebra
    (I:Ideal A) (J:Ideal B) (hIJ:I ≤ J.comap (algebraMap A B)):
    Algebra (A ⧸ I) (B ⧸ J):=
  (Ideal.quotientMap J (algebraMap A B) hIJ).toAlgebra'
    (fun _ _ => mul_comm _ _)
theorem quotient_isLocalization
    (I:Ideal A) (J:Ideal B)
    (hJ:J=I.map (algebraMap A B)):
    let hIJ:I ≤ J.comap (algebraMap A B):=by
      rw [hJ]
      exact Ideal.le_comap_map
    letI:=quotientAlgebra I J hIJ
    IsLocalization (M.map (Ideal.Quotient.mk I)) (B ⧸ J):=by
  let hIJ:I ≤ J.comap (algebraMap A B):=by
    rw [hJ]
    exact Ideal.le_comap_map
  letI:=quotientAlgebra I J hIJ
  let qA:A →+*A ⧸ I:=Ideal.Quotient.mk I
  let qB:B →+*B ⧸ J:=Ideal.Quotient.mk J
  constructor
  constructor
  · rintro ⟨_,⟨m,hm,rfl⟩⟩
    change IsUnit (qB (algebraMap A B m))
    exact (IsLocalization.map_units B ⟨m,hm⟩).map qB
  · intro y
    obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a,m⟩,hb⟩:=IsLocalization.surj M b
    let mbar:M.map qA:=⟨qA m,⟨m,m.property,rfl⟩⟩
    refine ⟨⟨qA a,mbar⟩,?_⟩
    change qB b*qB (algebraMap A B m)=qB (algebraMap A B a)
    simpa only [map_mul] using congrArg qB hb
  · intro x y hxy
    obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective y
    change qB (algebraMap A B a)=qB (algebraMap A B b) at hxy
    have hmem:algebraMap A B (a-b)∈J:=by
      rw [←Ideal.Quotient.eq_zero_iff_mem]
      rw [map_sub]
      change qB (algebraMap A B a-algebraMap A B b)=0
      rw [map_sub,hxy,sub_self]
    rw [hJ,IsLocalization.algebraMap_mem_map_algebraMap_iff M B] at hmem
    obtain ⟨m,hmM,hmI⟩:=hmem
    let mbar:M.map qA:=⟨qA m,⟨m,hmM,rfl⟩⟩
    refine ⟨mbar,?_⟩
    change qA m*qA a=qA m*qA b
    rw [←map_mul, ←map_mul, ←sub_eq_zero, ←map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    simpa only [mul_sub] using hmI
end
end ProximityPrize.SubmissionLower.ContactLocalizationQuotientAdapter6732Research
