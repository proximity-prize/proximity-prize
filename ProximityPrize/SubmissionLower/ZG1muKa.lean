import ProximityPrize.SubmissionLower.H
set_option Elab.async false
set_option autoImplicit true
namespace qmQUdWa
noncomputable section
open aR dN agL vS Dr
private theorem exJ {R:Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A:Ideal R} (hA:A.IsPrime) (hlt:A<IsLocalRing.maximalIdeal R)
    {u:R} {n:ℕ} (hu:u∈IsLocalRing.maximalIdeal R^n) :
    (n:ℕ∞)≤Module.length R (R ⧸ (A ⊔ Ideal.span {u} : Ideal R)) := by
  let m:=IsLocalRing.maximalIdeal R
  let I (i:ℕ) :Ideal R:=A ⊔ m^i
  have hstep (i:ℕ) :I (i+1)<I i:= by
    refine lt_of_le_of_ne (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ i)) _) ?_
    intro he
    have hpow:m^i≤A:= by
      apply Submodule.le_of_le_smul_of_le_jacobson_bot (I:=m) (IsNoetherian.noetherian _)
      · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
      · change m^i≤A ⊔ m•m^i
        rw [smul_eq_mul,← pow_succ']
        change m^i≤I (i+1)
        rw [he]
        exact le_sup_right
    exact hlt.not_ge (fun _ hx=>hA.mem_of_pow_mem i (hpow (Ideal.pow_mem_pow hx i)))
  have hoff (i:ℕ) : (i:ℕ∞)≤Order.coheight (I i:Submodule R R) := by
    induction i with
    | zero=>simp
    | succ i ih =>
      rw [Nat.cast_succ]
      exact (add_le_add_left ih 1).trans
        (Order.coheight_add_one_le (show (I (i+1) :Submodule R R)<I i from hstep i))
  rw [Module.length_quotient]
  exact (hoff n).trans (Order.coheight_anti
    (sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_sup_right hu)) :
      (A ⊔ Ideal.span {u} : Ideal R)≤I n))
theorem evJ {T P:Ideal GeoJets} (hT:T.IsPrime) (hTP:T<P) {D:af 4}
    (hP: (AX T D).IsMinimalPrime P) {n:ℕ}
    (hD:letI:=hP.isPrime; afc P (bC D) n) :
    n≤AN (AX T D) P:= by
  let _:=hP.isPrime
  let L:=Localization.AtPrime P
  let φ:=algebraMap GeoJets L
  let A:=T.map φ
  have hdisj:Disjoint (P.primeCompl:Set GeoJets) T :=
    Set.disjoint_left.mpr fun _ hx hy=>hx (hTP.le hy)
  have hA:A.IsPrime :=IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl L T hT hdisj
  have hlt:A<IsLocalRing.maximalIdeal L:= by
    refine lt_of_le_of_ne (?_) fun h => ?_
    · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P L]
      exact Ideal.map_mono hTP.le
    have hc:=congrArg (Ideal.under GeoJets) h
    rw [show A.under GeoJets=T from IsLocalization.under_map_of_isPrime_disjoint P.primeCompl L hT hdisj,
      IsLocalization.AtPrime.under_maximalIdeal L P] at hc
    exact hTP.ne hc
  apply ENat.natCast_le_natCast.mp
  rw [a9B hP]
  change (n:ℕ∞)≤Module.length L (L ⧸ (AX T D).map φ)
  rw [AX,Ideal.map_sup,Ideal.map_span,Set.image_singleton]
  exact exJ hA hlt hD
end
end qmQUdWa
