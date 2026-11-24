import ProximityPrize.SubmissionLower.ZhNzRYc
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, Ideal.Quotient.mk → zVv, Ideal.span → zye, Ideal.span_singleton_le_iff_mem → zvl, IsFractionRing.liftAlgHom → zeU, IsFractionRing.lift_algebraMap → zoc, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.aeval_X → zTw, PowerSeries → zpm, PowerSeries.C → zMG, RingHom.ker → zdq
set_option autoImplicit true
namespace qqpP4De
noncomputable section
open MvPolynomial qQ9yWTb qb0hmCe q1kuFjb
open cu (L)

open scoped WithZero
private theorem arc_kernel {q:Curve} (hq:Irreducible q)
    (a :Fin 2→zpm L) (hq0:MvPolynomial.eval₂ zMG a q=0)
    {i:Fin 2} (hi:PowerSeries.coeff 1 (a i)≠0) :
    zdq (zIe (fun j=>(a j:LaurentSeries L))).toRingHom =
      zye {q} := by
  let g:Curve →ₐ[L] LaurentSeries L:=zIe fun j=>(a j:LaurentSeries L)
  let I:Ideal Curve :=zye {q}
  have hq' : g q=0:= by
    have hC: (HahnSeries.ofPowerSeries ℤ L).comp zMG=algebraMap L (LaurentSeries L) :=
      RingHom.ext fun c=>(HahnSeries.ofPowerSeries_C c).trans (LaurentSeries.algebraMap_apply L c).symm
    have h:=MvPolynomial.hom_eval₂ q zMG (HahnSeries.ofPowerSeries ℤ L) a
    rw [hq0,map_zero,hC] at h
    exact h.symm
  have hI:I≤zdq g.toRingHom:=(zvl _).mpr hq'
  refine le_antisymm (fun r hr => ?_) hI
  by_contra hn
  let J:=I ⊔ zye {r}
  have hP:I.IsPrime :=(Ideal.span_singleton_prime hq.ne_zero).mpr hq.prime
  have hdim: (affineHilbertPolynomial I).natDegree=1 := by
    have h:=natDegree_affineHilbertPolynomial_span_singleton_add_one hq.ne_zero hP.ne_top
    change (affineHilbertPolynomial I).natDegree+1=Nat.card (Fin 2) at h
    simpa [Nat.card_eq_fintype_card] using h
  have hcut:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hP hn (le_refl r.totalDegree)).1
  have hJ: (affineHilbertPolynomial J).natDegree=0 :=
    Nat.eq_zero_of_le_zero (by simpa only [hdim,Nat.sub_self] using hcut)
  let:Module.Finite L (Curve ⧸ J) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
  have hker :J≤zdq g.toRingHom :=
    sup_le hI ((zvl _).mpr hr)
  let b:=Ideal.Quotient.liftₐ J g hker
  have hb:IsIntegral L (b (zVv J (z9v i))) := by
    obtain ⟨p,hp,hz⟩:=IsIntegral.of_finite L (zVv J (z9v i))
    exact ⟨p,hp,(Polynomial.aeval_algHom_apply b _ p).trans
      ((congrArg b hz).trans (map_zero b))⟩
  change IsIntegral L (g (z9v i)) at hb
  rw [show g (z9v i)=(a i:LaurentSeries L) from zTw _ _] at hb
  have hc:=mem_algebraicClosure_iff'.mpr hb
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure L (LaurentSeries L))] at hc
  obtain ⟨c,hc⟩:=IntermediateField.mem_bot.mp hc
  have he : (zMG c:zpm L)=a i :=
    HahnSeries.ofPowerSeries_injective (Γ:=ℤ) (by
      rw [HahnSeries.ofPowerSeries_C,← LaurentSeries.algebraMap_apply]
      exact hc)
  exact hi (by rw [← he,PowerSeries.coeff_C_of_ne_zero (by decide)])
private theorem extend_arc {q:Curve} (Cq:CurveModel q) (a :Fin 2→zpm L)
    (h:zdq (zIe (fun j=>(a j:LaurentSeries L))).toRingHom =
      zye {q}) :
    ∃ w:Cq.E →ₐ[L] LaurentSeries L,∀ j,w (Cq.seed j)=(a j:LaurentSeries L) := by
  let f :Curve →ₐ[L] Cq.E :=zIe Cq.seed
  let g:Curve →ₐ[L] LaurentSeries L:=zIe fun j=>(a j:LaurentSeries L)
  have hf :zdq f.toRingHom=zdq g.toRingHom:=Cq.equation.trans h.symm
  have hle :zdq f.rangeRestrict.toRingHom≤zdq g.toRingHom :=
    (f.ker_rangeRestrict.trans hf).le
  let g' := f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective g hle
  have hg' : zq4 g' := by
    apply (injective_iff_map_eq_zero' _).mpr
    intro x
    obtain ⟨r,rfl⟩:=f.rangeRestrict_surjective x
    simp only [g',AlgHom.liftOfSurjective_apply,← RingHom.mem_ker,AlgHom.ker_rangeRestrict]
    change r∈zdq g.toRingHom↔r∈zdq f.toRingHom
    rw [hf]
  let F:=FractionRing f.range
  have hinj:zq4 f.range.val :=Subtype.val_injective
  let b:F →ₐ[L] Cq.E :=zeU hinj
  have hb:b.fieldRange = ⊤ := by
    rw [IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq hinj
      (f.range.range_val.trans (Algebra.adjoin_range_eq_range_aeval L Cq.seed).symm)]
    exact Cq.generates
  let e :F ≃ₐ[L] Cq.E :=AlgEquiv.ofBijective b ⟨b.injective,AlgHom.fieldRange_eq_top.mp hb⟩
  let d:F →ₐ[L] LaurentSeries L:=zeU hg'
  refine ⟨d.comp e.symm.toAlgHom,fun j => ?_⟩
  let x :=f.rangeRestrict (z9v j)
  have hx :e (algebraMap f.range F x)=Cq.seed j:= by
    change b (algebraMap f.range F x)= _
    exact (zoc (K:=F) (g:=f.range.val.toRingHom) hinj x).trans
      (zTw _ _)
  change d (e.symm (Cq.seed j))= _
  rw [← hx,e.symm_apply_apply]
  dsimp only [d]
  rw [IsFractionRing.liftAlgHom_apply,zoc]
  exact (AlgHom.liftOfSurjective_apply _ _ _ _ _).trans (zTw _ _)
end
end qqpP4De
