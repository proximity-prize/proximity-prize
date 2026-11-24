import ProximityPrize.SubmissionLower.ZGa2w7a
import ProximityPrize.SubmissionLower.ZlfuKwd
import ProximityPrize.SubmissionLower.ZsWhgLc
import ProximityPrize.SubmissionLower.Z35X4Rc
set_option Elab.async false
section
set_option autoImplicit true
namespace qPQ4nYa
noncomputable section
open aR (ao)
open Rj (kJ)
open qlc9qed (Bank)
def c1 :Prop :=
  ∀ (b:Bank) (q k :ℕ),q<b.box.b+1→k<b.m+b.box.j → ∀ p:kJ,
    Module.finrank ao (LinearMap.range (af3 b q k))≤xR b q (offset b k) p
def c2 :Prop := ∃ p:ℕ→ℕ→kJ,rankBudget .cheap p≤Bank.cheap.contactRank
def c3:Prop := ∃ p:ℕ→ℕ→kJ,rankBudget .strong p≤Bank.strong.contactRank
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :qlc9qed.c2 := by
 intro b a v V hV hcap
 let:Module.Finite ao V:=hV
 have hb : ∃ p:ℕ→ℕ→kJ,rankBudget b p≤b.contactRank := by
  cases b
  · exact h2
  · exact h3
 obtain ⟨p,hp⟩:=hb
 have hr :=(originRange_le_sum b p (fun q hq k hk=>h1 b q k hq hk (p q k))).trans hp
 exact (codim_le_origin b a v V hcap).trans (Nat.mul_le_mul_left (b.U + 1) hr)
end
end qPQ4nYa
end
section
set_option autoImplicit true
namespace q6AUWfb
noncomputable section
open Polynomial
open aR (ao)
open jA
open acZ (aFf)
open axa (weight)
open P5_7_1 (Input)
open qlc9qed


open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
private def coordinate (m:Exponent) (k :ℕ) :jK →ₗ[ao] ao :=
 (Polynomial.lcoeff ao k).comp ((MvPolynomial.lcoeff ao[X] m).restrictScalars ao)
private instance bqa {x :Input} (P:OnePole x) (t:ℕ) :
  Module.Finite ao (aV P .strong t) := by
 have :Module.Finite ao (Aw .strong x.h t) := by
  rw [qMNQHHc.ambient_eq]
  exact qSxbgdc.finite_ambient _ _ _
 exact Submodule.finiteDimensional_of_le (inf_le_left:aV P .strong t≤Aw .strong x.h t)
private def boundary (h T:ℕ) :jK →ₗ[ao] (Exponent→ao) :=
 LinearMap.pi fun m=>coordinate m (T - weight h m)
private theorem cDm (h T:ℕ) (F:jK) (m:Exponent) :
 boundary h T F m=(F.coeff m).coeff (T - weight h m) :=rfl
private theorem bVx {h T:ℕ} {F:jK}
  (hc:ahb h T F) (hz :boundary h T F=0) {m:Exponent} (hm:m∈F.support) :
  (F.coeff m).natDegree+weight h m<T:= by
 have hle : (F.coeff m).natDegree+weight h m≤T:=hc m hm
 by_contra! hnt
 have he : (F.coeff m).natDegree=T - weight h m:= by omega
 have hn:=congrFun hz m
 rw [cDm,← he,coeff_natDegree] at hn
 exact (leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)) hn
private theorem cU3 {ι:Type*} [Fintype ι] {h T:ℕ} (e :ι→jK)
   (hcut : ∀ i,ahb h T (e i)) (he :LinearIndependent ao (fun i=>boundary h T (e i))) :
   LinearIndependent iP (fun i=>bC (e i)) := by
 apply (LinearIndependent.iff_fractionRing ao[X] iP).mp
 let f :jK →ₗ[ao[X]] ko :=
   (MvPolynomial.mapAlgHom (Algebra.ofId ao[X] iP)).toLinearMap
 suffices hi:LinearIndependent ao[X] e from
   hi.map' f (LinearMap.ker_eq_bot.mpr aFf)
 classical
 rw [Fintype.linearIndependent_iff] at he ⊢
 intro c hc j
 by_contra hj
 let n:=Finset.univ.sup (fun i=>(c i).natDegree)
 have hn (i:ι) : (c i).natDegree≤n :=
   Finset.le_sup (f := fun i=>(c i).natDegree) (Finset.mem_univ i)
 have hd (i:ι) (m:Exponent) : ((e i).coeff m).natDegree≤T - weight h m:= by
   by_cases hm:m∈(e i).support
   · have hh: ((e i).coeff m).natDegree+weight h m≤T:=hcut i m hm
     omega
   · simp [MvPolynomial.notMem_support_iff.mp hm]
 have hz : (∑ i,(c i).coeff n•boundary h T (e i))=0:= by
   funext m
   simpa only [MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,smul_eq_mul,
     Polynomial.finsetSum_coeff,coeff_mul_add_eq_of_natDegree_le (hn _) (hd _ m),
     AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,Polynomial.coeff_zero,
     Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,cDm]
     using congrArg (fun F:jK=>(F.coeff m).coeff (n+(T - weight h m))) hc
 have hlt (i:ι) (hi:c i≠0) : (c i).natDegree<n :=
   lt_of_le_of_ne (hn i) (fun h=>hi (leadingCoeff_eq_zero.mp (by
     rw [← coeff_natDegree,h,he _ hz i])))
 have hpos :=(Nat.zero_le _).trans_lt (hlt j hj)
 have hle :n≤n - 1 :=Finset.sup_le fun i _=> by
   by_cases hi:c i=0
   · simp [hi]
   · have hh:=hlt i hi
     omega
 omega
private theorem power_le_top {G R:ko} {n:ℕ} (hg:0<G.degreeOf (some 2))
  (hr :R≠0) (hd:G^n∣R) :n≤R.degreeOf (some 2) := by
 have hg0:G≠0:= by
  rintro rfl
  simp at hg
 obtain ⟨Q,rfl⟩:=hd
 obtain ⟨hl,hq⟩:=mul_ne_zero_iff.mp hr
 rw [MvPolynomial.degreeOf_mul_eq hl hq,MvPolynomial.degreeOf_pow_eq _ _ _ hg0]
 have h:n≤n*G.degreeOf (some 2) := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left n (Nat.succ_le_of_lt hg)
 exact h.trans (Nat.le_add_right ..)
private def seedSpace :Submodule iP ko :=
 MvPolynomial.restrictWeightedDegree (Pi.single (none :mA) 1) Bank.strong.U
private theorem mem_seedSpace {R:ko} : R∈seedSpace↔gY R≤Bank.strong.U:= by
 rw [seedSpace,MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
  MvPolynomial.weightedTotalDegree_piSingle,gY]
end
end q6AUWfb
end
section
set_option autoImplicit true
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace qGnV2ac
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (p)

open P5_7_7
open cu (L)
def c1 :Prop :=
  ∀ (F:Dg) (l h:ℕ),EquationBounds F l h →
    ∀ (S:Sections F) (x a b:L),a≠0∨b≠0 →
      (S.CF.filter fun γ =>
        (S.P γ).eval x*a=(S.Q γ).eval x*b∧(S.A γ).eval x≠0).card≤nodeRate l*h
def c2 :Prop :=
  ∀ (F:Dg) (l h u s L₀ W:ℕ),EquationBounds F l h →
    2*u+s=L₀→l*L₀≤W→HE F s (W-l*u) →
    (2*l-2)*W-l*(l-1)*L₀<p →
    ∀ S:Sections F,
      ∑ γ∈S.CF,max (S.B γ).natDegree ((S.A γ).natDegree-pN S s γ) ≤
        ((6*l-4)*W-(3*l*l-4*l+2)*L₀)*h
end
end qGnV2ac
end
section
set_option autoImplicit true
open MvPolynomial renaming mem_support_iff→qz0,le_degreeOf_of_mem_support→qz1,uniqueAlgEquiv→qz2,C→qz3
set_option backward.isDefEq.respectTransparency false
namespace qwDXpPd
noncomputable section
open Polynomial
open cu (L)
open qQ9yWTb (Raw)
open q4Pefpa (sk Padded load stock j3)
open qbIP9ia (Exps Flat flatten exps exps_x exps_y flat_coeff flat_coeff' amm seed ao8 wt wt_term Idx rows rows_range mem_coord idx_card)
open private bg6 weights c0Q from ProximityPrize.SubmissionLower.BJ
private def flatAlg:Raw ≃ₐ[L] Flat :=AlgEquiv.ofRingEquiv (f :=flatten) fun c=> by
 apply flatten.symm.injective
 rw [RingEquiv.symm_apply_apply]
 change Polynomial.C (qz3 (Polynomial.C c)) =
  ((MvPolynomial.optionEquivLeft L (Fin 2 ⊕ Unit)) (qz3 c)).map bg6.toRingHom
 rw [MvPolynomial.optionEquivLeft_C,Polynomial.map_C]
 change _=Polynomial.C (MvPolynomial.map (qz2 L Unit).toRingHom
  (MvPolynomial.sumRingEquiv L (Fin 2) Unit (qz3 c)))
 rw [MvPolynomial.sumRingEquiv_C,MvPolynomial.map_C]
 congr 2
 exact ((qz2 L Unit).commutes c).symm
private theorem load_le (a b:ℕ) (F:Raw) :
  load a b F≤wt (b-a) (flatten F)+F.natDegree*a := by
 apply Finset.sup_le fun i _=>Finset.sup_le fun m hm => ?_
 have hc:exps i ((F.coeff i).coeff m).natDegree m∈(flatten F).support :=
  qz0.mpr (by
   rw [flat_coeff]
   exact leadingCoeff_ne_zero.mpr (qz0.mp hm))
 simpa only [exps_x,exps_y,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
  Nat.add_le_add_right (wt_term (b-a) hc) (F.natDegree*a)
private theorem seedCoeff_ne {F:Raw} {v :Exps} (h:v∈(flatten F).support) :
  (F.coeff (v none)).coeff (ao8 v)≠0 :=
 fun hz=>qz0.mp h (by rw [flat_coeff',hz,Polynomial.coeff_zero])
private theorem padded_weight {a b E M:ℕ} {F:Raw} (hF:F≠0)
  (h:Padded a b E M F) :wt (b-a) (flatten F)+E*a<M:= by
 have hnon :=MvPolynomial.support_nonempty.mpr ((map_ne_zero_iff _ flatten.injective).mpr hF)
 obtain ⟨v,hv,he⟩:=Finset.exists_mem_eq_sup _ hnon (Finsupp.weight (weights (b-a)))
 change wt (b-a) (flatten F)=Finsupp.weight (weights (b-a)) v at he
 rw [he,c0Q]
 change v amm+v none*(b-a)+E*a<M
 have hk :v amm≤((F.coeff (v none)).coeff (ao8 v)).natDegree :=
  le_natDegree_of_ne_zero (by simpa only [flat_coeff'] using qz0.mp hv)
 have hh:=h.2 (v none) (ao8 v) (seedCoeff_ne hv)
 omega
private theorem rect_degree {z t:ℕ} {F:Raw} (h:sk z t F) (i:Fin 2) :
  (flatten F).degreeOf (seed i)≤ if i=0 then z else t:= by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro v hv
 exact (qz1 i
  (qz0.mpr (seedCoeff_ne hv))).trans (h i (v none))
private def width (a b m j i:ℕ) :=j*(a+b)-(m*a+i*(b-a))
private theorem quotient_slots {a b E j W z t:ℕ} {q F:Raw}
   (hq:q≠0) (hload :W<load a b q)
   (hpad:Padded a b E (W+1+j*(a+b)) (q*F)) (hrect :sk z t (q*F)) :
   flatten F∈(@rows (E-q.natDegree+1) z t (width a b (E-q.natDegree) j)).range := by
 apply rows_range
 intro v hv
 have hF:F≠0:= fun hz=>qz0.mp hv (by rw [hz,map_zero]; rfl)
 have hq' := (map_ne_zero_iff _ flatten.injective).mpr hq
 have hF' := (map_ne_zero_iff _ flatten.injective).mpr hF
 have htop:=padded_weight (mul_ne_zero hq hF) hpad
 rw [map_mul,show wt (b-a) (flatten q*flatten F) =
     wt (b-a) (flatten q)+wt (b-a) (flatten F) from
   MvPolynomial.weightedTotalDegree_mul _ _ _ hq' hF'] at htop
 have hqwt:=load_le a b q
 have hterm :=wt_term (b-a) hv
 have hY:=hpad.1
 rw [Polynomial.natDegree_mul hq hF] at hY
 have hy :v none≤F.natDegree :=le_natDegree_of_ne_zero fun hz =>
   seedCoeff_ne hv (by simp only [hz,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply])
 have hm:E*a=q.natDegree*a+(E-q.natDegree)*a := by
   rw [← Nat.add_mul,Nat.add_sub_of_le (show q.natDegree≤E by omega)]
 have hs (i:Fin 2) :v (seed i)≤ if i=0 then z else t:= by
   apply (qz1 (seed i) hv).trans
   have hd:=rect_degree hrect i
   rw [map_mul,MvPolynomial.degreeOf_mul_eq hq' hF'] at hd
   exact (Nat.le_add_left _ _).trans hd
 apply mem_coord.mpr
 refine ⟨by omega,?_,by simpa using hs 0,by simpa using hs 1⟩
 dsimp only [width]
 omega
theorem proof :q4Pefpa.c2 := by
 classical
 intro a b e g j W z t hab hj q hq hqe hload V hV hdiv
 let m:=e+g-q.natDegree
 let I:=Idx (m+1) z t (width a b m j)
 let T: (I →₀ L) →ₗ[L] Raw :=
   (LinearMap.mulLeft L q).comp (flatAlg.symm.toLinearMap.comp rows)
 have hsub:V≤T.range := by
   intro G hG
   obtain ⟨F,rfl⟩:=hdiv G hG
   obtain ⟨A,hA⟩:=quotient_slots hq hload (hV _ hG).1 (hV _ hG).2
   refine ⟨A,?_⟩
   change q*flatten.symm (rows A)=q*F
   rw [hA,RingEquiv.symm_apply_apply]
 have hw: (∑ i:Fin (m+1),width a b m j i)≤j3 (a+b) j:= by
   have hl:2*a+(b-a)=a+b:= by omega
   have h:=qZCRTge.tail_count m j a (b-a) (by dsimp [m]; omega)
   simpa only [hl,width,j3] using h
 calc
   _≤Module.finrank L T.range :=Submodule.finrank_mono hsub
   _≤Module.finrank L (I →₀ L) :=T.finrank_range_le
   _=(∑ i:Fin (m+1),width a b m j i)*stock z t:= by
     rw [Module.finrank_finsupp_self,idx_card,stock,Nat.mul_assoc]
   _≤_:= by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (stock z t) hw
end
end qwDXpPd
end
