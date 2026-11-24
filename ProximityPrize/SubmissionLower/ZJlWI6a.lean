import ProximityPrize.SubmissionLower.ZqzGq1b
import ProximityPrize.SubmissionLower.Z1mibXd
import ProximityPrize.SubmissionLower.ZAMeR1b
import ProximityPrize.SubmissionLower.Ztd61Ce
set_option Elab.async false
section
set_option autoImplicit true
namespace qe9q5Za
noncomputable section
open we (eT cH DO)
open yz (oe S3 F3)
open ac0 (P5 auW bxW aYo
  bJD)
open P6_6 (bf)
open qeu0RUc (yD RY Wa afR i9 pN)
open MvPolynomial
open scoped Pointwise
private theorem enz {v :ℕ} (a :aRt v) (t:cH) :
    DO (afR v (P5 a-MvPolynomial.C t)) (RY v) bf := by
  have hz : (0:Fin 4 →₀ ℕ)∈Wa v := by
    change 0+0+0≤(RY v).b∧0+2*0≤(RY v).j∧0≤(RY v).t∧0≤bf
    simp
  have h:=monomialMap_mem_restrictSupport_nsmul hz (bxW a t)
  rw [one_nsmul] at h
  exact h
theorem proof :qeu0RUc.c1 := by
  classical
  intro v _ f hC
  have h1 :=aYZ.proof
  have h2 :=bRg.proof
  have h3:=bRh.proof
  let I (P:yD f) :=i9 v f P.val
  obtain ⟨degreeBad,hdegreeBad⟩:=Classical.skolem.mp fun P:yD f =>
    h1 cH (Wa v) (I P) (hC P.val P.property).1 (hC P.val P.property).2
  obtain ⟨separationBad,hseparationBad⟩:=Classical.skolem.mp fun P:yD f =>
    h2 cH (Wa v) (I P) (hC P.val P.property).1 (hC P.val P.property).2
  let bad:=Finset.univ.biUnion fun P=>insert (separationBad P) (degreeBad P)
  obtain ⟨a,ha⟩:=Submodule.exists_forall_notMem_of_forall_ne_top
    (fun V:bad=>V.val) (by
      intro V
      obtain ⟨P,_,hV⟩:=Finset.mem_biUnion.mp V.property
      rcases Finset.mem_insert.mp hV with h | h
      · rw [h]
        exact (hseparationBad P).1
      · exact (hdegreeBad P).1 _ h)
  have havoid (P:yD f) (V:Submodule cH (aRt v))
      (hV:V∈insert (separationBad P) (degreeBad P)) :a∉V :=
    ha ⟨V,Finset.mem_biUnion.mpr ⟨P,Finset.mem_univ _,hV⟩⟩
  have hdegree (P:yD f) :=
    (hdegreeBad P).2 a (fun V hV=>havoid P V (Finset.mem_insert_of_mem hV))
  obtain ⟨valueBad,hvalueBad⟩:=Classical.skolem.mp fun P:yD f =>
    h3 cH (Wa v) (I P) (hC P.val P.property).1 a (hdegree P).1
      ((hseparationBad P).2 a (havoid P _ (Finset.mem_insert_self _ _)))
  obtain ⟨pointsBad,hpointsBad⟩:=Classical.skolem.mp fun P:yD f =>
    d4a P.property (hC P.val P.property)
  let value (z :aRt v) :=aeval z (P5 a)
  let excludedValues :=Finset.univ.biUnion fun P=>valueBad P∪(pointsBad P).image value
  obtain ⟨t,ht⟩:=Infinite.exists_notMem_finset excludedValues
  have hmiss (P:yD f) :t∉valueBad P∪(pointsBad P).image value :=
    fun h=>ht (Finset.mem_biUnion.mpr ⟨P,Finset.mem_univ _,h⟩)
  let L:=P5 a-MvPolynomial.C t
  let J (P:Ideal (eT 3)) :=auW (i9 v f P) a t
  have hcut (P) (hP:P∈yD f) :
      (affineHilbertPolynomial (J P)).natDegree=0 ∧
        affineDegree (J P)=pN v f P :=
    (hdegree ⟨P,hP⟩).2 t
  have hproper (P) (hP:P∈yD f) :afR v L∉F3 f P:= by
    intro hmem
    have heq :J P=i9 v f P :=
      sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    have hz :=(hcut P hP).1
    rw [heq,(hC P hP).2] at hz
    exact Nat.one_ne_zero hz
  have hfinite (P) (hP:P∈yD f) : (zeroLocus cH (J P)).Finite :=
    (finite_zeroLocus_and_ncard_le_affineDegree (K:=cH) _ (hcut P hP).1).1
  let points (P:Ideal (eT 3)) :Finset oe :=
    if hP:P∈yD f then (hfinite P hP).toFinset.image ave else ∅
  have hpoint (P) (hP:P∈yD f) (y) (hy :y∈points P) :
      y∈S3 f P∧eval y (afR v L)=0 ∧
        ∀ Q∈yD f,P≠Q→y∉S3 f Q:= by
    simp only [points,dite_eq_left hP] at hy
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hy
    have hz' := (Set.Finite.mem_toFinset _).mp hz
    obtain ⟨hzC,hzt⟩:=aYo.mp hz'
    have ⟨hgraph,hoff⟩:=hpointsBad ⟨P,hP⟩ z hzC
      (fun hbad=>hmiss ⟨P,hP⟩ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨z,hbad,hzt⟩)))
    have hev :=(mem_zeroLocus_sup_span_singleton_iff.mp hz').2
    rw [← bsL hzC,
      aeval_monomialPoint,aeval_eq_eval] at hev
    exact ⟨hgraph,hev,hoff⟩
  refine ⟨⟨afR v L,enz a t,points,?_,hproper,?_,?_⟩⟩
  · intro P hP
    have hrad:=hvalueBad ⟨P,hP⟩ t (fun ht' => hmiss ⟨P,hP⟩ (Finset.mem_union_left _ ht'))
    have hinj:Set.InjOn ave (zeroLocus cH (J P)) := by
      intro x hx y hy hxy
      rw [← bsL (aYo.mp hx).1,
        ← bsL (aYo.mp hy).1,hxy]
    simp only [points,dite_eq_left hP]
    rw [Finset.card_image_of_injOn (by simpa using hinj),
      ← Set.ncard_eq_toFinset_card _ (hfinite P hP)]
    exact (bJD (J P) (hcut P hP).1 hrad).trans (hcut P hP).2
  · intro P hP y hy
    exact ⟨(hpoint P hP y hy).1,(hpoint P hP y hy).2.1⟩
  · intro P hP Q hQ hne y hy
    exact (hpoint P hP y hy).2.2 Q hQ hne
end
end qe9q5Za
end
section
set_option autoImplicit true
set_option maxHeartbeats 900000
namespace qgLc7la
noncomputable section
open aR (af ao)
open oR (qg)
open we (eT cH fW Of zq D7)
open aeC
open aFQ
open aiJ (aM6)
open P6_6 (gZ bf tB aWx)
open q6t08kb (freshBudget)
open qSCPCwb (Dm BW aGt acU Bk afs)
open qeu0RUc (yD avw cfr)
open qowZxPd (gAt c1T)
open Polynomial
open scoped BigOperators
open private cTd cVh from ProximityPrize.SubmissionLower.C
open private cqu dfd from ProximityPrize.SubmissionLower.C
open private ctW gqV from ProximityPrize.SubmissionLower.ZAMeR1b
open private dR0 from ProximityPrize.SubmissionLower.ZWZGjEc
private theorem guE {f :af 3} {P:Ideal (eT 3)}
    (hf :tB f aWx) (hc:BW f≤P)
    (h:aqG f P) {y :Fin 3→cH} (hy :y∈D7 f P) :
    (aac f (Bt y)).natDegree≤gZ ∧
      Of f (aac f (Bt y))=0:= by
  have hrow:fW f∈P:=hc (Ideal.subset_span (by simp))
  have hcut:fW (Dm f)∈P:=hc (Ideal.subset_span (by simp))
  have hold:we.BW f≤P:= by
    rw [we.BW,Ideal.span_insert]
    exact sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hrow)
      ((Ideal.span_singleton_le_iff_mem P).mpr (c1T h hcut (by change 133423≤133669; decide)))
  have hU: (aot f P).natDegree≤gZ:= by
    rw [aot,natDegree_taylor,natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have hsmall:3≤j:= by
      change 133425<j at hj
      omega
    obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le hsmall
    rw [Nat.add_comm 3 n,aMK,bCW]
    have hn:bf-3≤n:= by
      change 133425<3+n at hj
      change 133423≤n
      omega
    have hz :Ub f P (n+3)=0:= by
      rw [Ub,bm2 f P (c1T h hcut hn),mul_zero,zero_mul,zero_mul]
    split_ifs with hj'
    · exact hz
    · rfl
  refine ⟨by rw [← cqu hy]; exact natDegree_map_le.trans hU,?_⟩
  have hOne :delta h (1 :Chart f P)=0:= by
    simpa only [map_one] using bD2 h (1 :ao)
  have hShift:taylor (KM f P (MvPolynomial.C Polynomial.X)) (aot f P) =
      aMK f P:= by
    rw [aot,taylor_taylor,add_neg_cancel,taylor_zero]
  have hidentity :=cTd (delta h) hOne (aT8 h) (constants (KM f P))
    (bD2 h) _ (dVV h) f (aot f P) (aMK f P) hShift
    (dGI h hold) (cVh hold)
    ((ctW _ _ _ hU hf).trans_lt (by decide :aWx<K1.p))
    (fun n hn hp=> by
      rw [← map_natCast (constants (KM f P))]
      exact (b9C hn hp).isUnit.map _)
  rw [← dfd hy,hidentity,Polynomial.map_zero]
theorem guz {a f P} (hf :FactorBox a f) (hw:tB f aWx)
    (hP:P∈yD f) (hs :aGt f P) :
    ∃ Q:Bk,acU f Q ∧
      ∀ S:ao[X],S.natDegree≤gZ→qg 2 f S →
        zq S∈D7 f P →
          afs S∈MvPolynomial.zeroLocus cH Q:= by
  obtain ⟨hmin,hsep⟩:=Ideal.mem_retainedMinimalPrimes.mp (avw.mp hP).2
  have hp:=hmin.isPrime
  have hstable :=gAt hp hmin.le hsep hs
  obtain ⟨hprime,hcurve⟩ :=
    cxX.proof f P hp hsep (cfr hf.irreducible hP)
  have hTaylor := fun y hy=>guE hw hmin.le hstable (y :=y) hy
  refine ⟨aHk f P,⟨⟨hprime,hcurve,deO _ _ (fun y hy =>
    (hTaylor y hy).2),?_⟩,gqV _ _ (fun y hy=>(hTaylor y hy).1)⟩,?_⟩
  · obtain ⟨y,hy⟩:=c7O f P hp hsep
    refine ⟨aWP f y,cb0 _ _ hy,?_⟩
    intro hz
    apply hy.2
    rw [← cNc f,← bCY,
      hz,Polynomial.eval_zero]
  · intro S hS hr hy
    have hS' : S.natDegree≤133671 :=hS.trans (by decide :gZ≤133671)
    rw [← c7y f S hS' hr]
    exact cb0 _ _ hy
theorem ed8 {a f} (hf :FactorBox a f) (C:Finset Bk)
    (hC : ∀ Q∈C,acU f Q) :
    ∃ d:Bk→ℕ,
      (∀ Q∈C,0<d Q∧MvPolynomial.affineDegree Q=(d Q:ℚ)) ∧
        (∑ Q∈C,d Q)≤freshBudget a := by
  classical
  have hex (Q:Bk) : ∃ d:ℕ,Q∈C→0<d ∧
      MvPolynomial.affineDegree Q=(d:ℚ) := by
    by_cases hQ:Q∈C
    · let h:=(hC Q hQ).solution
      obtain ⟨d,hd,he⟩:=aM6 Q h.prime h.dimension
      exact ⟨d,fun _=>⟨hd,he⟩⟩
    · exact ⟨0,fun h=>False.elim (hQ h)⟩
  let d (Q:Bk) :=(hex Q).choose
  have hd (Q) (hQ:Q∈C) :=(hex Q).choose_spec hQ
  have hc: (Dm f).totalDegree≤1+(2*bf - 5)*(a.b - 1) := by
    apply (qSCPCwb.btd f).trans
    rw [show 2*(bf+1) - 7=2*bf - 5 by decide]
    gcongr
    exact hf.total
  have hb:f.totalDegree*(Dm f).totalDegree≤freshBudget a :=
    Nat.mul_le_mul hf.total hc
  refine ⟨d,hd,?_⟩
  have hsum: (∑ Q∈C,(d Q:ℚ))≤(freshBudget a :ℚ) :=
    (Finset.sum_congr rfl fun Q hQ=>(hd Q hQ).2.symm).trans_le
      ((dR0 f hf.irreducible hf.proper C hC).trans (Nat.cast_le.mpr hb))
  exact_mod_cast hsum
end
end qgLc7la
end
