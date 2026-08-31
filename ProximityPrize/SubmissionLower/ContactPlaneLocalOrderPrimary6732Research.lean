import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_LocalRing_Length
namespace ProximityPrize.SubmissionLower.ContactPlaneLocalOrderPrimary6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {A:Type*} [CommRing A]
theorem maximalIdeal_pow_succ_lt_pow_of_noetherian_domain
    {S:Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [IsLocalRing S]
    (hmax:IsLocalRing.maximalIdeal S≠⊥) (n:ℕ):
    IsLocalRing.maximalIdeal S^(n+1) <
      IsLocalRing.maximalIdeal S^n:=by
  let m:=IsLocalRing.maximalIdeal S
  have hle:m^(n+1) ≤ m^n:=Ideal.pow_le_pow_right n.le_succ
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hfg:(m^n).FG:=IsNoetherian.noetherian _
  have hsmul:m^n ≤ m • (m^n):=by
    rw [Ideal.smul_eq_mul, ←pow_succ', ←heq]
  have hzero:m^n=⊥:=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m (m^n) hfg hsmul
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  obtain ⟨x,hx,hx0⟩:=SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hmax)
  have hxpow:x^n∈m^n:=Ideal.pow_mem_pow hx n
  rw [hzero,Ideal.mem_bot] at hxpow
  exact pow_ne_zero n (by simpa only [Ideal.mem_bot] using hx0) hxpow
theorem exponent_le_length_local_maximal_pow_of_noetherian_domain
    {S:Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [IsLocalRing S]
    (hmax:IsLocalRing.maximalIdeal S≠⊥) (n:ℕ):
    (n:ℕ∞) ≤ Module.length S
      (S ⧸ IsLocalRing.maximalIdeal S^n):=by
  rw [Module.length_quotient]
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ((n+1:ℕ):ℕ∞)=(n:ℕ∞)+1:=by simp
        _ ≤ Order.coheight (IsLocalRing.maximalIdeal S^n)+1:=
          add_le_add_left ih 1
        _ ≤ Order.coheight (IsLocalRing.maximalIdeal S^(n+1)):=
          Order.coheight_add_one_le
            (maximalIdeal_pow_succ_lt_pow_of_noetherian_domain hmax n)
theorem exponent_mul_residueDegree_le_length_quotient_maximal_pow
    {R S:Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [Algebra R S]
    (p:Ideal S) [p.IsMaximal] (hp:p≠⊥)
    [IsLocalHom (algebraMap R (Localization.AtPrime p))]
    [FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime p))] (n:ℕ):
    ((n*Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime p)):ℕ):ℕ∞) ≤
        Module.length R (S ⧸ p^n):=by
  let L:=Localization.AtPrime p
  let M:=L ⧸ IsLocalRing.maximalIdeal L^n
  have hmaxL:IsLocalRing.maximalIdeal L≠⊥:=by
    intro hbot
    apply hp
    rw [←IsLocalization.AtPrime.under_maximalIdeal L p,hbot]
    exact Ideal.comap_bot_of_injective (algebraMap S L)
      (IsLocalization.injective L p.primeCompl_le_nonZeroDivisors)
  have hlocal:(n:ℕ∞) ≤ Module.length L M:=
    exponent_le_length_local_maximal_pow_of_noetherian_domain hmaxL n
  have hresidue:Module.length (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField L)=
        Module.finrank (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField L):=Module.length_eq_finrank _ _
  have hweighted:((n*Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField L):ℕ):ℕ∞) ≤ Module.length R M:=by
    rw [Nat.cast_mul, ←hresidue,
      IsLocalRing.length_restrictScalars R L M]
    exact mul_le_mul_right' hlocal _
  let e:=IsLocalization.AtPrime.equivQuotMaximalIdealPow p L n
  have heq:Module.length R (S ⧸ p^n)=Module.length R M:=
    (e.toLinearEquiv.restrictScalars R).length_eq
  exact hweighted.trans_eq heq.symm
abbrev SurfaceQuotient (surface:A):=A ⧸ Ideal.span {surface}
theorem exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
    {R:Type*} [CommRing R] [IsLocalRing R] [Algebra R A]
    (surface:A)
    (relation:Ideal A)
    (relationBar:Ideal (SurfaceQuotient surface)) [relationBar.IsMaximal]
    (hrelationBar:relationBar=
      Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) relation)
    [IsDomain (SurfaceQuotient surface)]
    [IsNoetherianRing (SurfaceQuotient surface)]
    (hrelationBarNe:relationBar≠⊥)
    [IsLocalHom (algebraMap R (Localization.AtPrime relationBar))]
    [FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime relationBar))]
    (n:ℕ):
    ((n*Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime relationBar)):ℕ):ℕ∞) ≤
      Module.length R (A ⧸ (Ideal.span {surface} ⊔ relation^n)):=by
  let I:Ideal A:=Ideal.span {surface}
  let q:A →ₐ[R] A ⧸ I:=Ideal.Quotient.mkₐ R I
  have hpow:relationBar^n=Ideal.map q (relation^n):=by
    rw [hrelationBar,Ideal.map_pow]
    rfl
  let e₁:(SurfaceQuotient surface ⧸ relationBar^n) ≃ₐ[R]
      (SurfaceQuotient surface ⧸ Ideal.map q (relation^n)):=
    Ideal.quotientEquivAlgOfEq R hpow
  let e₂:(SurfaceQuotient surface ⧸ Ideal.map q (relation^n)) ≃ₐ[R]
      (A ⧸ (I ⊔ relation^n)):=
    DoubleQuot.quotQuotEquivQuotSupₐ R I (relation^n)
  have hlocal:=
    exponent_mul_residueDegree_le_length_quotient_maximal_pow
      (R:=R) relationBar hrelationBarNe n
  exact hlocal.trans_eq (e₁.trans e₂).toLinearEquiv.length_eq
end
end ProximityPrize.SubmissionLower.ContactPlaneLocalOrderPrimary6732Research
