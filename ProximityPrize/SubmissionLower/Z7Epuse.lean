import ProximityPrize.SubmissionLower.ZlfuKwd
import ProximityPrize.SubmissionLower.Z6IMoUa
import ProximityPrize.SubmissionLower.ZQmiAIb
import ProximityPrize.SubmissionLower.ZkMhvdb
import ProximityPrize.SubmissionLower.ZGa2w7a
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qbIP9ia
noncomputable section
open Polynomial
open cu (L FX aZ j9)
open Qt (Qc)
open P5 (K p)
open P5_7_1 (Input degree emz aic)
open qHEUR1a (Raw embed height Zk)
open Y3 (aka ek)
open private azZ abn cZx fTI from ProximityPrize.SubmissionLower.BJ
private theorem embed_coeff (F:Raw) (j:ℕ) :
  (embed F).coeff j=MvPolynomial.map (algebraMap L[X] FX) (F.coeff j) := by
 change (F.map (MvPolynomial.map (algebraMap L[X] FX))).coeff j= _
 rw [coeff_map]
theorem flat_deg {F:Raw} {m:Exps} (hm:m∈(flatten F).support) :
  m none≤F.natDegree ∧ ∀ i,m (seed i)≤height F:= by
 have h:=MvPolynomial.mem_support_iff.mp hm
 rw [flat_coeff'] at h
 have hR: (F.coeff (m none)).coeff (ao8 m)≠0 :=
  fun hz=>h (by rw [hz,coeff_zero])
 have hF:F.coeff (m none)≠0:= fun hz=>hR (by simp only [hz,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply])
 refine ⟨le_natDegree_of_ne_zero hF,fun i => ?_⟩
 have hcoeff :=(Qc _ _).mp (le_refl (height F)) (m none)
 have hm' : ao8 m∈((embed F).coeff (m none)).support := by
  apply MvPolynomial.mem_support_iff.mpr
  rw [embed_coeff,MvPolynomial.coeff_map]
  exact (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr hR
 exact (MvPolynomial.le_degreeOf_of_mem_support i hm').trans
  ((MvPolynomial.degreeOf_le_totalDegree _ _).trans hcoeff)
theorem physical_not_dvd {F:Raw} (hi:Irreducible F) (hpos :0<F.natDegree) :
  ¬ MvPolynomial.X amm∣flatten F:= by
 intro hd
 rw [← flatten_X] at hd
 have hd' : aka (Polynomial.X:L[X])∣F :=
  by simpa only [RingEquiv.symm_apply_apply] using map_dvd flatten.symm hd
 have hunit :=(isPrimitive_iff_isUnit_of_C_dvd.mp (hi.isPrimitive hpos.ne')) _ hd'
 have h' : IsUnit (aka (Polynomial.X:L[X])) :=hunit.map Polynomial.C
 have hh:=h'.map flatten
 rw [flatten_X] at hh
 exact (MvPolynomial.X_prime (i:=amm)).not_isUnit hh
theorem output_bounds {G:Raw} {n a b:ℕ}
   (h : ∀ m∈(flatten G).support,m none≤n∧m (seed 0)≤a∧m (seed 1)≤b) :
   (embed G).natDegree≤n ∧ ∀ j (i:Fin 2),((embed G).coeff j).degreeOf i ≤
     if i=0 then a else b:= by
 have hkey {j} {m:Fin 2 →₀ ℕ} (hm: (G.coeff j).coeff m≠0) :
     j≤n∧m 0≤a∧m 1≤b:= by
   have he :exps j ((G.coeff j).coeff m).natDegree m∈(flatten G).support :=
     MvPolynomial.mem_support_iff.mpr (by rw [flat_coeff]; exact leadingCoeff_ne_zero.mpr hm)
   simpa only [exps_y,exps_s] using h _ he
 refine ⟨natDegree_map_le.trans (natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_),?_⟩
 · apply MvPolynomial.ext
   intro m
   simp only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
   exact not_ne_iff.mp (fun hm=>hj.not_ge (hkey hm).1)
 · intro j i
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro m hm
   rw [embed_coeff] at hm
   have hm' : (G.coeff j).coeff m≠0:=MvPolynomial.mem_support_iff.mp
     (MvPolynomial.support_map_subset _ _ hm)
   fin_cases i
   · simpa using (hkey hm').2.1
   · simpa using (hkey hm').2.2
private theorem rawAt_deg {d n:ℕ} {G:Raw} (hn:0<n) (hg:wt d (flatten G)<n)
   (t:Fin 2→L) {S:K[X]} (hS:S.natDegree≤d) :
   (azZ t S G).natDegree<n:= by
 classical
 apply Nat.lt_of_le_pred hn
 change (G.eval₂ (MvPolynomial.eval (C ∘ t)) (j9 S)).natDegree≤n-1
 rw [eval₂_eq_sum,Polynomial.sum_def]
 apply natDegree_sum_le_of_forall_le
 intro j _
 rw [MvPolynomial.eval_eq,Finset.sum_mul]
 apply natDegree_sum_le_of_forall_le
 intro m hm
 rw [show (∏ i∈m.support,(C ∘ t) i^m i)=C (∏ i∈m.support,t i^m i) by
   simp only [Function.comp_apply,map_prod,map_pow]]
 have he :exps j ((G.coeff j).coeff m).natDegree m∈(flatten G).support :=
   MvPolynomial.mem_support_iff.mpr (by
     rw [flat_coeff]
     exact leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm))
 have hbound:=(wt_term d he).trans_lt hg
 rw [exps_x,exps_y] at hbound
 have hpow: ((j9 S)^j).natDegree≤j*d :=
   natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_map_le.trans hS))
 exact (natDegree_mul_le_of_le (natDegree_mul_C_le ((G.coeff j).coeff m) _) hpow).trans
   (Nat.le_pred_of_lt hbound)
theorem transfer {n:ℕ} (hn:0<n) {F G H B:Flat}
  (he :H*F=G+MvPolynomial.X amm^n*B) (hw:wt degree G<n)
  (x :Input) {γ:K} (hγ:γ∈x.Γ) (hr :Zk x (embed (flatten.symm F)) γ) :
  Zk x (embed (flatten.symm G)) γ:= by
 let z :=x.M.label γ
 let S:=x.F.scalar γ
 let ev :=azZ (abn z p) S
 have hD:S.natDegree≤degree :=
  (aic hγ).trans (Nat.add_le_add_left (emz x).2 _)
 have hF:ev (flatten.symm F)=0 :=
  (IsFractionRing.injective L[X] FX) (by rw [cZx,map_zero]; exact hr)
 let E :Flat →+* Polynomial L:=ev.comp flatten.symm.toRingHom
 have hX:E (MvPolynomial.X amm)=Polynomial.X:= by
  change ev (flatten.symm (MvPolynomial.X amm))= _
  rw [← flatten_X,RingEquiv.symm_apply_apply,fTI]
 have hF' : E F=0:=hF
 have hrel :=congrArg E he
 rw [map_mul,map_add,map_mul,map_pow,hX,hF',mul_zero] at hrel
 have hdvd: (Polynomial.X:L[X])^n∣ev (flatten.symm G) :=
  ⟨-ev (flatten.symm B),by rw [mul_neg]; exact eq_neg_of_add_eq_zero_left hrel.symm⟩
 have hzero :ev (flatten.symm G)=0:= by
  by_contra hne
  have hle :=natDegree_le_of_dvd hdvd hne
  rw [natDegree_X_pow] at hle
  exact (rawAt_deg hn (by simpa only [RingEquiv.apply_symm_apply] using hw) _ hD).not_ge hle
 unfold Zk
 rw [← cZx,hzero,map_zero]
theorem nonzero_resultant {F G:Raw}
  (h:IsCoprime (ek (embed F)) (ek (embed G))) :
  (embed F).resultant (embed G)≠0:= by
 let ι:=algebraMap aZ (FractionRing aZ)
 have hi:=IsFractionRing.injective aZ (FractionRing aZ)
 have h' : IsCoprime ((embed F).map ι) ((embed G).map ι) :=h
 have hne :=resultant_ne_zero _ _ h'
 rw [natDegree_map_eq_of_injective hi,natDegree_map_eq_of_injective hi,resultant_map_map] at hne
 exact fun hz=>hne (by rw [hz,map_zero])
end
end qbIP9ia
end
section
set_option autoImplicit true
namespace qpjPzMc
open P5_7_2 (Aux fO Ls jX stages introduction)
open qMNIwTb (CJ)
private instance (b:fO) (moving:Bool) (a :Aux) :Decidable (CJ b moving a) := by
 unfold CJ
 split <;> infer_instance
private def OK (b:fO) (moving:Bool) (a :Aux) :Prop :=
 (decide (CJ b moving a) || check (jX b).lo (jX b).hi a moving)=true
private theorem checked {b:fO} {moving:Bool} {a :Aux}
  (hc:OK b moving a) (hp : ¬ CJ b moving a) :
  check (jX b).lo (jX b).hi a moving=true := by
 simpa only [OK,decide_eq_false hp,Bool.false_or] using hc
private theorem aux_cons {b:fO} {a :Aux} {as :List Aux}
  (ha :OK b false a) (hs : ∀ x∈as,OK b false x) :
  ∀ x∈a :: as,OK b false x :=
 List.forall_mem_cons.mpr ⟨ha,hs⟩
private theorem stage_cons {b:fO} {s :Ls} {ss :List Ls}
  (hf :OK b false ⟨s.dI,s.free⟩) (hm:OK b true ⟨s.dI,s.moving⟩)
  (ht : ∀ x∈ss,OK b false ⟨x.dI,x.free⟩∧OK b true ⟨x.dI,x.moving⟩) :
  ∀ x∈s :: ss,OK b false ⟨x.dI,x.free⟩∧OK b true ⟨x.dI,x.moving⟩ :=
 List.forall_mem_cons.mpr ⟨⟨hf,hm⟩,ht⟩
set_option maxHeartbeats 5000000 in
private theorem aux_checks (b:fO) (hb:b.val<12) : ∀ x∈introduction b,OK b false x := by
 fin_cases b
 all_goals first | exact (Nat.not_lt_of_ge (by decide) hb).elim | skip
 all_goals simp only [introduction,List.map_cons,List.map_nil]
 all_goals repeat' first
  | exact (fun _ h=>(List.not_mem_nil h).elim)
  | refine aux_cons (by rfl) ?_
set_option maxHeartbeats 5000000 in
private theorem bOp (b:fO) (hb:b.val<12) :
  ∀ s∈stages b,OK b false ⟨s.dI,s.free⟩∧OK b true ⟨s.dI,s.moving⟩:= by
 fin_cases b
 all_goals first | exact (Nat.not_lt_of_ge (by decide) hb).elim | skip
 all_goals simp only [stages,List.map_cons,List.map_nil]
 all_goals repeat' first
  | exact (fun _ h=>(List.not_mem_nil h).elim)
  | refine stage_cons (by rfl) (by rfl) ?_
theorem proof :qMNIwTb.c2 := by
 intro b h hl hu hb moving a ha hp
 apply test hl hu
 apply checked _ hp
 rcases ha with ⟨rfl,ha⟩ | ⟨s,hs,rfl⟩
 · exact aux_checks b hb a ha
 · cases moving
   · exact (bOp b hb s hs).1
   · exact (bOp b hb s hs).2
end qpjPzMc
end
