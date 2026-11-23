import ProximityPrize.SubmissionLower.ZOGAUga
import ProximityPrize.SubmissionLower.ZX4kd1a
set_option Elab.async false
set_option autoImplicit true
namespace qf24IRb
noncomputable section
open Polynomial
open aR (af ao embed Shape shape aO)
open P6_6 (tB gZ literalBody)
open agL (BV Uz EY a4B)
open private aDq from ProximityPrize.SubmissionLower.BF
open private cNq from ProximityPrize.SubmissionLower.AB
open private amc hasse_zero from ProximityPrize.SubmissionLower.ZX4kd1a
open scoped BigOperators
private abbrev Exp:=Fin 4 →₀ ℕ
private theorem axis_injective (i:Fin 4) :Function.Injective (fun _:Unit=>i) :=
  fun _ _ _=>Subsingleton.elim _ _
private def translate (i:Fin 4) :af 4 →+* Polynomial (af 4) :=
  (MvPolynomial.uniqueAlgEquiv (af 4) Unit).toAlgHom.toRingHom.comp
    ((MvPolynomial.killCompl (axis_injective i)).toRingHom.comp Uz)
private theorem translate_coeff (i:Fin 4) (Q:af 4) (a :ℕ) :
    (translate i Q).coeff a=BV (Finsupp.single i a) Q:= by
  change ((MvPolynomial.uniqueAlgEquiv (af 4) Unit)
    (MvPolynomial.killCompl (axis_injective i) (Uz Q))).coeff a= _
  rw [MvPolynomial.coeff_uniqueAlgEquiv,MvPolynomial.coeff_killCompl,
    Finsupp.mapDomain_single,agL.taylor_coeff]
private theorem coeff_hasse (Q:af 4) (a m:Exp) :
    (BV a Q).coeff m= Q.coeff (m+a) *
      ∏ i:Fin 4,(((m+a) i).choose (a i) :ao[X]) := by
  classical
  have vanish (v :Exp) (hn:v≠m+a) :
      (MvPolynomial.monomial (v-a) (Q.coeff v *
        ∏ i:Fin 4,((v i).choose (a i) :ao[X]))).coeff m=0:= by
    rw [MvPolynomial.coeff_monomial]
    split_ifs with he
    · by_cases h:a≤v
      · exact (hn ((tsub_add_cancel_of_le h).symm.trans (congrArg (· + a) he))).elim
      · rw [amc h,mul_zero]
    · rfl
  rw [BV,MvPolynomial.coeff_sum]
  by_cases hm:m+a∈Q.support
  · rw [Finset.sum_eq_single_of_mem _ hm (fun v _ hv=>vanish v hv)]
    simp [MvPolynomial.coeff_monomial]
  · rw [MvPolynomial.notMem_support_iff.mp hm,zero_mul]
    exact Finset.sum_eq_zero fun v hv=>vanish v (fun h=>hm (h ▸ hv))
private theorem hasse_one (i:Fin 4) (Q:af 4) :
    BV (Finsupp.single i 1) Q=MvPolynomial.pderiv i Q:= by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_hasse,MvPolynomial.coeff_pderiv]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp [Finsupp.add_apply,Nat.choose_one_right]
  · intro j _ hji
    simp [Finsupp.single_eq_of_ne hji]
  · simp
private theorem hasse_weight {Q:af 4} {T:ℕ} (a :Exp)
    (h:tB Q T) :tB (BV a Q) T:= by
  intro m hm
  rw [MvPolynomial.mem_support_iff,coeff_hasse] at hm
  have hQ:=h _ (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm))
  rw [coeff_hasse,← Nat.cast_prod]
  have hc:=Polynomial.natDegree_mul_le (p:= Q.coeff (m+a))
    (q := ∏ i:Fin 4,(((m+a) i).choose (a i) :ao[X]))
  rw [← Nat.cast_prod,Polynomial.natDegree_natCast,Nat.add_zero] at hc
  have hw:m.sum (fun i k=>(gZ - i.val)*k) ≤
      (m+a).sum (fun i k=>(gZ - i.val)*k) := by
    rw [Finsupp.sum_add_index' (fun _=>Nat.mul_zero _) (fun _=>Nat.mul_add _)]
    exact Nat.le_add_right _ _
  exact (Nat.add_le_add hc hw).trans hQ
private theorem clip {Q:af 4} {q:Shape} (h:aO (shape Q) q) :
    aO (shape Q) (literalBody q).iU:= by
  obtain ⟨hb,hj,ht⟩:=h
  obtain ⟨hi,hjb⟩:=aDq Q
  have hj' : (shape Q).j≤ min q.j (3*q.b) :=le_min hj (hjb.trans (Nat.mul_le_mul_left _ hb))
  have ht' : (shape Q).t≤q.b:=(MvPolynomial.degreeOf_le_totalDegree Q 3).trans hb
  exact ⟨hb.trans (le_max_left _ _),hj',le_min ht (le_min ht' (by omega))⟩
private theorem bFB {R:af 4} (hR:R≠0)
    (hpos :0<R.totalDegree) (hsmall:R.totalDegree<K1.p) :
    ∃ i:Fin 4,¬ R∣(translate i R).coeff 1 := by
  classical
  have hv :R.vars.Nonempty := by
    by_contra h
    have hC:=MvPolynomial.vars_eq_empty_iff_eq_C.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    rw [hC,MvPolynomial.totalDegree_C] at hpos
    exact (Nat.lt_irrefl 0) hpos
  obtain ⟨i,hi⟩:=hv
  have hdeg:=Nat.pos_of_ne_zero (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi)
  have hlt:=(MvPolynomial.degreeOf_le_totalDegree R i).trans_lt hsmall
  let _:CharP ao K1.p:=charP_of_injective_ringHom embed.injective K1.p
  let _:CharP ao[X] K1.p:=charP_of_injective_ringHom Polynomial.C_injective K1.p
  have hc: (R.degreeOf i:ao[X])≠0:= by
    intro hz
    exact (not_le_of_gt hlt)
      (Nat.le_of_dvd hdeg ((CharP.cast_eq_zero_iff ao[X] K1.p _).mp hz))
  have hD:=MvPolynomial.pderiv_ne_zero_of_natCast_ne_zero i R hc
  refine ⟨i,?_⟩
  rw [translate_coeff,hasse_one]
  rintro ⟨V,hV⟩
  have hV0:V≠0:= fun h=>hD (by rw [hV,h,mul_zero])
  have hd:=MvPolynomial.degreeOf_pderiv_le_sub_one i R
  rw [hV,MvPolynomial.degreeOf_mul_eq hR hV0] at hd
  omega
theorem proof :P6_6_3.c4 := by
  intro Δ s Q R q d a hR hq hb hw hord _ hd hx
  by_cases ha :a=0
  · subst a
    exact ⟨Q,by simpa only [zero_add,pow_one] using hx,clip hb,hw,
      by simpa only [Nat.sub_zero] using hord⟩
  have hn:Q≠0:= fun h=>hx (h ▸ dvd_zero _)
  have hRQ:R∣Q:=(dvd_pow_self R ha).trans hd
  have hsmall:R.totalDegree<K1.p :=
    ((MvPolynomial.totalDegree_le_of_dvd_of_isDomain hRQ hn).trans (hb.1.trans hq.1)).trans_lt
      (show (4025:ℕ)<K1.p by decide)
  obtain ⟨i,hi⟩:=bFB hR.1.ne_zero hR.2.1.1 hsmall
  have h0 (G:af 4) : (translate i G).coeff 0=G:= by
    rw [translate_coeff,Finsupp.single_zero,hasse_zero]
  have hprime :=UniqueFactorizationMonoid.irreducible_iff_prime.mp hR.1
  have hproper :=cNq (translate i) h0 R Q a hprime hi hd hx
  rw [translate_coeff] at hproper
  refine ⟨_,hproper,clip (a4B _ hb),hasse_weight _ hw,fun γ hγ => ?_⟩
  have horder :EY (Finsupp.single i a)=a := by
    simp [EY,Finsupp.sum_single_index]
  simpa only [horder] using q8NBBre.cUA Q _ (Finsupp.single i a) d (hord γ hγ)
end
end qf24IRb
