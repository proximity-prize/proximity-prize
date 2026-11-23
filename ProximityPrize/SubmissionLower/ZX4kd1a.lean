import ProximityPrize.SubmissionLower.ZfVU1Oc
set_option Elab.async false
section
set_option autoImplicit true
namespace q8NBBre
noncomputable section
open Polynomial
open aR (af ao jet wU shape)
open dN (GeoJets bC)

open agL (Uz BV EY)
open P6_6_7
open scoped BigOperators
private def IM (S:ao[X]) :af 4 →+* af 4 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i=>MvPolynomial.X i+MvPolynomial.C (jet S i))
private theorem gqf (S:ao[X]) (F:af 4) (a :Exponent) :
    IM S (BV a F)=BV a (IM S F) := by
  have h: (MvPolynomial.map (IM S)).comp Uz=Uz.comp (IM S) := by
    apply MvPolynomial.ringHom_ext <;> intro x
    · simp [IM,Uz]
    · simp only [RingHom.comp_apply,IM,Uz,MvPolynomial.eval₂Hom_X',
        map_add,MvPolynomial.eval₂Hom_C,MvPolynomial.map_C,MvPolynomial.map_X]
      ac_rfl
  have hc:=congrArg (fun P:MvPolynomial (Fin 4) (af 4)=>P.coeff a)
    (RingHom.congr_fun h F)
  simpa only [RingHom.comp_apply,MvPolynomial.coeff_map,agL.taylor_coeff] using hc
private theorem order_add (a b:Exponent) :EY (a+b)=EY a+EY b:= by
  exact Finsupp.degree.map_add a b
private theorem amc {a v :Exponent} (ha : ¬ a≤v) :
    (∏ i:Fin 4,((v i).choose (a i) :ao[X]))=0:= by
  have ⟨i,hi⟩ : ∃ i,v i<a i:= by simpa [Finsupp.le_def,not_forall] using ha
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt hi])
theorem cUA (F:af 4) (S:ao[X]) (a :Exponent) (d:ℕ)
    (hF:wU F S d) :wU (BV a F) S (d-EY a) := by
  classical
  intro m hm
  change m∈(IM S (BV a F)).support at hm
  rw [gqf] at hm
  change d-EY a≤EY m
  by_contra! hd
  apply (MvPolynomial.mem_support_iff.mp hm)
  unfold BV
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro v hv
  rw [MvPolynomial.coeff_monomial]
  split_ifs with he
  · by_cases ha :a≤v
    · have hvd:d≤EY v :=hF v hv
      have hea :a+m=v :=he ▸ add_tsub_cancel_of_le ha
      rw [← hea,order_add] at hvd
      omega
    · rw [amc ha,mul_zero]
  · rfl
private theorem hasse_zero (F:af 4) :BV 0 F=F:= by
  classical
  unfold BV
  simpa using (MvPolynomial.as_sum F).symm
private theorem top_partial {F:af 4} (hF:F≠0) :
    ∃ a :Exponent,EY a≤(shape F).b ∧
      ∃ c:ao[X],c≠0∧BV a F=MvPolynomial.C c:= by
  classical
  obtain ⟨a,ha,hmax⟩:=F.support.exists_max_image EY
    (MvPolynomial.support_nonempty.mpr hF)
  refine ⟨a,MvPolynomial.le_totalDegree ha,F.coeff a,MvPolynomial.mem_support_iff.mp ha,?_⟩
  unfold BV
  rw [Finset.sum_eq_single_of_mem a ha]
  · simp only [tsub_self,Nat.choose_self,Nat.cast_one,Finset.prod_const_one,mul_one,
      MvPolynomial.monomial_zero']
  · intro v hv hn
    by_cases hav :a≤v
    · have he :a+(v-a)=v :=add_tsub_cancel_of_le hav
      have hm:=hmax v hv
      rw [← he,order_add] at hm
      have hz :EY (v-a)=0:= by omega
      have hv0:v-a=0:=(Finsupp.degree_eq_zero_iff _).mp hz
      exact (hn (by simpa [hv0] using he.symm)).elim
    · rw [amc hav,mul_zero,map_zero]
theorem cSn (F:af 4) (P:Ideal GeoJets) (hp:P.IsPrime) (hF:F≠0) :
    ∃ a :Exponent,EY a=genericOrder F P∧bC (BV a F)∉P:= by
  classical
  let:=hp
  let pred (n:ℕ) := ∀ a :Exponent,EY a<n→bC (BV a F)∈P
  let d:=genericOrder F P
  have hd:d=Nat.findGreatest pred (shape F).b:=rfl
  have hb:d≤(shape F).b:=Nat.findGreatest_le _
  have hex : ∃ a :Exponent,EY a≤(shape F).b∧bC (BV a F)∉P:= by
    obtain ⟨a,ha,c,hc,h⟩:=top_partial hF
    refine ⟨a,ha,?_⟩
    rw [h]
    apply P.notMem_of_isUnit
    change IsUnit (MvPolynomial.map dN.j8 (MvPolynomial.C c))
    rw [MvPolynomial.map_C]
    have hinj:Function.Injective dN.j8 :=
      (algebraMap dN.lN dN.GeoField).injective.comp
        (IsFractionRing.injective ao[X] dN.lN)
    exact (isUnit_iff_ne_zero.mpr (fun h=>hc (hinj (h.trans (map_zero _).symm)))).map MvPolynomial.C
  have hsmall : ¬ pred (d+1) := by
    by_cases h:d<(shape F).b
    · exact Nat.findGreatest_is_greatest (by rw [← hd]; omega) (by omega)
    · obtain ⟨a,ha,hp'⟩:=hex
      exact fun had=>hp' (had a (by omega))
  have hw : ∃ a :Exponent,EY a<d+1∧bC (BV a F)∉P:= by
    by_contra! hn
    exact hsmall hn
  obtain ⟨a,ha,hP⟩:=hw
  refine ⟨a,le_antisymm (Nat.lt_succ_iff.mp ha) ?_,hP⟩
  apply Nat.le_of_not_gt
  exact mt (Nat.findGreatest_spec (P:=pred)
    (Nat.zero_le (shape F).b) (fun _ h=>(Nat.not_lt_zero _ h).elim) a) hP
theorem generic_positive {F:af 4} {P:Ideal GeoJets} (hp:P.IsPrime)
    (hF:F≠0) (hmem:bC F∈P) :0<genericOrder F P:= by
  classical
  obtain ⟨a,ha,hnot⟩:=cSn F P hp hF
  by_contra! hz
  have ho:EY a=0:=Nat.eq_zero_of_le_zero (ha.trans_le hz)
  have hzero :a=0:=(Finsupp.degree_eq_zero_iff _).mp ho
  exact hnot (by simpa only [hzero,hasse_zero] using hmem)
end
end q8NBBre
end
section
set_option autoImplicit true
namespace q8kxiJa
noncomputable section
open IsLocalRing
open aR (af)
open dN (GeoJets bC AX)
open agL (afc BV EY bft)
open Dr (AN a9B)
open P6_6_7 (genericOrder)
private theorem evJ {R:Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P:Ideal R) (hp:P.IsPrime) (hlt:P< maximalIdeal R) {u:R} {n:ℕ}
    (hu:u∈maximalIdeal R^n) :
    (n:ℕ∞)≤Module.length R (R ⧸ (P ⊔ Ideal.span {u} : Ideal R)) := by
  let m:=maximalIdeal R
  have hno (i:ℕ) : ¬ m^i≤P :=
    fun h=>(not_le_of_gt hlt) (fun x hx=>hp.mem_of_pow_mem i (h (Ideal.pow_mem_pow hx i)))
  let I (i:ℕ) :Ideal R:=P ⊔ m^i
  have hstep (i:ℕ) :I (i+1)<I i:= by
    refine lt_of_le_of_ne (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ i)) _) ?_
    intro he
    apply hno i
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I:=m) (IsNoetherian.noetherian _)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · change m^i≤P ⊔ m•m^i
      rw [smul_eq_mul,← pow_succ']
      change m^i≤I (i+1)
      rw [he]
      exact le_sup_right
  have hcoheight (i:ℕ) : (i:ℕ∞)≤Order.coheight (I i:Submodule R R) := by
    induction i with
    | zero=>simp
    | succ i ih =>
      rw [Nat.cast_succ]
      exact (add_le_add_left ih 1).trans (Order.coheight_add_one_le (hstep i))
  rw [Module.length_quotient]
  exact (hcoheight n).trans
    (Order.coheight_anti (sup_le_sup_left ((Ideal.span_singleton_le_iff_mem (I:=m^n)).mpr hu) P))
theorem local_order_le {z T:Ideal GeoJets} {U:af 4} (hZ:z.IsPrime)
    (hU:bC U∉z) (hT: (AX z U).IsMinimalPrime T) :
    genericOrder U T≤AN (AX z U) T:= by
  classical
  let:=hZ
  let:=hT.isPrime
  let L:=Localization.AtPrime T
  let φ:=algebraMap GeoJets L
  have hZT:z≤T:=le_sup_left.trans hT.le
  have hne :z≠T:= by
    intro he
    apply hU
    rw [he]
    exact hT.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hmap :z.map φ< maximalIdeal L:= by
    refine lt_of_le_of_ne ?_ ?_
    · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal T L]
      exact Ideal.map_mono hZT
    · intro he
      apply hne
      rw [← Ideal.under_map_of_isLocalizationAtPrime (S:=L) T hZT,
        show z.map φ=maximalIdeal L from he,IsLocalization.AtPrime.under_maximalIdeal L T]
  have hm (a :Fin 4 →₀ ℕ) (ha :EY a<genericOrder U T) :
      bC (BV a U)∈T :=
    Nat.findGreatest_spec
      (P:= fun d => ∀ a,EY a<d→bC (BV a U)∈T)
      (Nat.zero_le _) (fun _ hx=>(Nat.not_lt_zero _ hx).elim) a ha
  have hv :afc T (bC U) (genericOrder U T) := by
    apply bRn.gK5
    intro a ha
    change BV a (MvPolynomial.map dN.j8 U)∈T
    rw [← bft]
    exact hm a ha
  apply ENat.natCast_le_natCast.mp
  rw [a9B hT]
  change (genericOrder U T:ℕ∞)≤Module.length L (L ⧸ (AX z U).map φ)
  rw [AX,Ideal.map_sup,Ideal.map_span,Set.image_singleton]
  exact evJ (z.map φ) (Ideal.isPrime_map_of_isLocalizationAtPrime T hZT) hmap hv
end
end q8kxiJa
end
