import ProximityPrize.SubmissionLower.B5
set_option Elab.async false
set_option autoImplicit true
namespace P0_9_6_3
noncomputable section
open aR dN rW MvPolynomial
open scoped Polynomial
private theorem ceQ (rec:bas.c2) (g:af 4) (h:mK) :
    ∃ (u:GeoJets) (e :ℕ),∀ A:kT,A.IsPrime→(gN A).IsPrime →
      bC g∈lA A→bC (separant g)∉lA A →
      h*mS (bC (separant g))^e - mS u∈gN A:= by
  let s :=bC (separant g)
  induction h using MvPolynomial.induction_on with
  | C a =>
    refine ⟨MvPolynomial.C a,0,fun A _ _ _ _ => ?_⟩
    simp [mS]
  | add h h' ih ih' =>
    obtain ⟨u,e,hu⟩:=ih
    obtain ⟨v,d,hv⟩:=ih'
    refine ⟨u*s^d+v*s^e,e+d,fun A hp he hg hs => ?_⟩
    let q:=Ideal.Quotient.mk (gN A)
    have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr (hu A hp he hg hs)
    have hv' := Ideal.Quotient.eq_zero_iff_mem.mpr (hv A hp he hg hs)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (h*mS s^e - mS u)=0 at hu'
    change q (h' * mS s^d - mS v)=0 at hv'
    change q ((h+h')*mS s^(e+d) - mS
      (u*s^d+v*s^e))=0
    simp only [map_add,map_mul,map_sub,map_pow,pow_add] at hu' hv' ⊢
    linear_combination q (mS s)^d*hu' + q (mS s)^e*hv'
  | mul_X h i ih =>
    obtain ⟨u,e,hu⟩:=ih
    obtain ⟨v,d,hv⟩:=rec g i
    refine ⟨u*v,e+d,fun A hp he hg hs => ?_⟩
    let q:=Ideal.Quotient.mk (gN A)
    have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr (hu A hp he hg hs)
    have hv' := Ideal.Quotient.eq_zero_iff_mem.mpr (hv A hp he hg hs)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (h*mS s^e - mS u)=0 at hu'
    change q (MvPolynomial.X i*mS s^d - mS v)=0 at hv'
    change q ((h*MvPolynomial.X i)*mS s^(e+d) - mS
      (u*v))=0
    simp only [map_mul,map_sub,map_pow,pow_add,sub_eq_zero] at hu' hv' ⊢
    calc
      _=(q h*q (mS s)^e) *
          (q (MvPolynomial.X i)*q (mS s)^d) := by ac_rfl
      _ = _:= by rw [hu',hv']
private theorem cVk (base :bas.c1) (rec:bas.c2) (f :af 4) :
    Set.InjOn lA {A | A.IsPrime∧bQ1 f A} := by
  intro A hA B hB himage
  obtain ⟨hAp,hAr⟩:=hA
  obtain ⟨hBp,_⟩:=hB
  obtain ⟨hAe,_,hAc⟩:=base A hAp
  obtain ⟨hBe,_,hBc⟩:=base B hBp
  obtain ⟨r,hgA,hsA⟩:=hAr
  let g:=(separant^[r]) f
  have hgB:bC g∈lA B:=himage ▸ hgA
  have hsB:bC (separant g)∉lA B:=himage ▸ hsA
  have hEq:gN A=gN B:= by
    ext h
    obtain ⟨u,e,hrel⟩:=ceQ rec g h
    let s :=mS (bC (separant g))
    have transfer (D:kT) (hDp:D.IsPrime) (hDe : (gN D).IsPrime)
        (hgD:bC g∈lA D) (hsD:bC (separant g)∉lA D) :
        h∈gN D↔u∈lA D:= by
      have hdiff :h*s^e - mS u∈gN D:=hrel D hDp hDe hgD hsD
      have hn:s^e∉gN D:= fun hp=>hsD (hDe.mem_of_pow_mem e hp)
      change _↔mS u∈gN D
      constructor
      · intro hh
        have hm:=Ideal.mul_mem_right (s^e) (gN D) hh
        exact ((gN D).sub_mem_iff_right hm).1 hdiff
      · intro hu
        have hm:=((gN D).sub_mem_iff_left hu).1 hdiff
        exact (hDe.mem_or_mem hm).resolve_right hn
    rw [transfer A hAp hAe hgA hsA,transfer B hBp hBe hgB hsB,himage]
  rw [← hAc,← hBc,hEq]
theorem freshImage_injective (f :af 4) :
    Set.InjOn lA {A | A.IsPrime∧bQ1 f A} :=
  cVk bRp.proof bRq.proof f
end
end P0_9_6_3
