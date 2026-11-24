import ProximityPrize.SubmissionLower.ZSyXMse
import ProximityPrize.SubmissionLower.ZPs0Sca
import ProximityPrize.SubmissionLower.ZaOaNGc
import ProximityPrize.SubmissionLower.Zqop1Ec
import ProximityPrize.SubmissionLower.ZkOFpKb
set_option Elab.async false
section
set_option autoImplicit true
theorem qBLYDld.proof :qmb8rCe.c3:= fun d h hd _ =>
 qOPkAYa.rank_le_cap _ 27 d h hd
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qZ4UNdb
noncomputable section
open Polynomial Finset
open P5 (K p)
open P5_7_1 (TopRow topLift topConjugate atTop)
open qaySLPd (pe SupportCaps orient topLabel pad RS)
open qh06gse (lift fibreMap fibre_mark numerator denominator descend)
open qCQTZAc (LiftAt)
open cu (L FX aZ Jet kr j9 jz qD)
open DP (Fg)
open ak0 (aTH)
open private rawFibre lift_raw from ProximityPrize.SubmissionLower.ZdjBl5c
open private lastPoly lastPoly_sum lastPoly_derivative eval_lastPoly from ProximityPrize.SubmissionLower.ZLITaXd
open private ctV graph_C marked_derivative from ProximityPrize.SubmissionLower.ZPs0Sca
private theorem fibre_height (f :Jet) (S:K[X]) {d W:ℕ} (hf :LiftAt d W f) (hS:S.natDegree≤d) (hW:W<p) :
    ∃ A:pe[X],∃ u:FX,u≠0 ∧
      lift A=MvPolynomial.C u*RS f S∧A.natDegree<p:= by
  obtain ⟨P,u,hu,hP,hcap⟩:=hf
  refine ⟨rawFibre S P,u,hu,?_,?_⟩
  · rw [lift_raw,hP,map_mul]
    simp [fibreMap,RS]
  have hcoeff (j i:ℕ) (h: (P.coeff j).coeff i≠0) :
      ((P.coeff j).coeff i).natDegree+d*i+(d-1)*j≤W:= by
    have hlead:=leadingCoeff_ne_zero.mpr h
    obtain ⟨e,he⟩:=Finset.nonempty_iff_ne_empty.mpr
      (show ((P.coeff j).coeff i).leadingCoeff.support ≠ ∅ by simpa using hlead)
    exact hcap j i _ e (by
      simpa only [Fg,coeff_natDegree] using MvPolynomial.mem_support_iff.mp he)
  have hy : ((j9 S).map (MvPolynomial.C:L →+* pe)).natDegree≤d :=
    natDegree_map_le.trans (natDegree_map_le.trans hS)
  have hv : ((j9 S.derivative).map (MvPolynomial.C:L →+* pe)).natDegree≤d-1 :=
    natDegree_map_le.trans (natDegree_map_le.trans
      ((natDegree_derivative_le S).trans (Nat.sub_le_sub_right hS _)))
  have hdeg: (rawFibre S P).natDegree≤W:= by
    rw [P.as_sum_support_C_mul_X_pow,map_sum]
    apply natDegree_sum_le_of_forall_le
    intro j hj
    change ((rawFibre S) (C (P.coeff j)*Polynomial.X^j)).natDegree≤_
    rw [map_mul,map_pow]
    simp only [coe_eval₂RingHom,eval₂_C,eval₂_X,coe_evalRingHom,eval_eq_sum,Polynomial.sum_def]
    rw [Finset.sum_mul]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    refine natDegree_mul_le.trans
      ((Nat.add_le_add (natDegree_mul_le.trans
        (Nat.add_le_add_left (natDegree_pow_le.trans ((Nat.mul_le_mul_left i hy).trans_eq (Nat.mul_comm i _))) _))
        (natDegree_pow_le.trans ((Nat.mul_le_mul_left j hv).trans_eq (Nat.mul_comm j _)))).trans ?_)
    exact hcoeff j i (mem_support_iff.mp hi)
  exact hdeg.trans_lt hW
private theorem topShape {B:TopRow} (hB:SupportCaps 87 27 12 0 B) (i:Fin 2)
  (e :Fin 4 →₀ ℕ) (he :e∈(topLift (orient i B)).support) :e 0=0∧e 3≤12 := by
 have ho:=(MvPolynomial.support_map_subset (algebraMap L[X] FX) (orient i B)) he
 have h:e∈B.support := by
  by_cases hi:i=0
  · simpa [orient,hi] using ho
  · simp only [orient,hi,ite_false,topConjugate] at ho
    exact MvPolynomial.support_map_subset _ _ ho
 exact ⟨Nat.le_zero.mp (hB e h).2.2.2,(hB e h).2.2.1⟩
private theorem specialize_pad (f :Jet) (S:K[X]) (B:TopRow) (i:Fin 2) (a :FX)
    (hB:SupportCaps 87 27 12 0 B) :
    fibreMap S (pad f i 12 B) =
      MvPolynomial.eval₂ MvPolynomial.C ![numerator f S,denominator f S]
        ((lastPoly a (kr S) (kr S.derivative) (topLift (orient i B))).homogenize 12) := by
  classical
  unfold pad
  rw [lastPoly_sum,homogenize_finsetSum,← MvPolynomial.coe_eval₂Hom,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨h0,h3⟩:=topShape hB i e he
  rw [homogenize_monomial h3,h0]
  simp only [map_mul,map_pow,map_neg,map_add,map_ofNat,pow_zero,mul_one,
    MvPolynomial.eval₂Hom_monomial,Finsupp.prod_pow,Fin.prod_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  simp [fibreMap,numerator,denominator,Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
  ring
private theorem regular_factor (f :Jet) (B:TopRow) (i:Fin 2) (z :K) (S:K[X])
    (hB:SupportCaps 87 27 12 0 B) (hd:f∣pad f i 12 B)
    (hroot :atTop (orient i B) (topLabel i z) S=0)
    (hsimple :atTop (MvPolynomial.pderiv 3 (orient i B)) (topLabel i z) S≠0)
    (hden:qD z (denominator f S)≠0)
    (hnum :qD z (numerator f S) =
      kr (hasseDeriv 2 S)*qD z (denominator f S)) :
    ∃ b:aZ,qD z b≠0∧RS f S ∣
      b*(numerator f S-MvPolynomial.C (kr (hasseDeriv 2 S))*denominator f S) := by
  let a :=jz (topLabel i z)
  let Q:=lastPoly a (kr S) (kr S.derivative) (topLift (orient i B))
  let w:=kr (hasseDeriv 2 S)
  have hQ:Q.eval w=0:=(eval_lastPoly _ _ _ _ rfl).trans hroot
  have hQ' : Q.derivative.eval w≠0:= by
    simpa only [Q,lastPoly_derivative,topLift,MvPolynomial.pderiv_map] using
      (show (lastPoly a (kr S) (kr S.derivative)
          (topLift (MvPolynomial.pderiv 3 (orient i B)))).eval w≠0 from
        (eval_lastPoly _ _ _ _ rfl).trans_ne hsimple)
  obtain ⟨R,hR⟩:=dvd_iff_isRoot.mpr hQ
  have hR' : R.eval w≠0:= by
    rw [hR,derivative_mul] at hQ'
    simpa using hQ'
  have hdR:R.natDegree≤11 := by
    have hqdeg:Q.natDegree≤12 := by
      dsimp only [Q]
      rw [lastPoly_sum]
      apply natDegree_sum_le_of_forall_le
      intro e he
      exact (natDegree_monomial_le _).trans (topShape hB i e he).2
    have hRne :R≠0:= fun h=>hR' (by simp [h])
    rw [hR,natDegree_mul (X_sub_C_ne_zero w) hRne,natDegree_X_sub_C] at hqdeg
    omega
  let N :=numerator f S
  let H :=denominator f S
  let ev :MvPolynomial (Fin 2) FX →+* aZ:=MvPolynomial.eval₂Hom MvPolynomial.C ![N,H]
  refine ⟨ev (R.homogenize 11),?_,?_⟩
  · have he : (qD z).comp ev =
        MvPolynomial.eval ![w*qD z H,qD z H] := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [ev,qD]
      · intro j
        fin_cases j <;> simp [ev,N,H,w,hnum]
    change ((qD z).comp ev) _≠0
    have hH :qD z H≠0:=hden
    rw [he,eval_homogenize hdR _ hH]
    change R.eval (w*qD z H/qD z H)*(qD z H)^11≠0
    rw [mul_div_cancel_right₀ _ hH]
    exact mul_ne_zero hR' (pow_ne_zero 11 hH)
  · have h:=map_dvd (fibreMap S) hd
    rw [specialize_pad f S B i a hB] at h
    change RS f S∣ev (Q.homogenize 12) at h
    rw [hR,show (12 :ℕ)=1+11 by rfl,
      homogenize_mul _ _ (by simp : (Polynomial.X - C w).natDegree≤1) hdR,
      homogenize_sub,homogenize_X (by decide),homogenize_C] at h
    simpa [ev,mul_comm,Nat.sub_self] using h
theorem proof :qCQTZAc.c2 := by
 intro f B i z S hB hLift _ hS hd hz hv hroot hsimple
 have hmark :qD z (RS f S)=0:=(fibre_mark f S z).trans hz
 by_cases he :RS f S=0
 · exact Or.inl he
 let:CharP FX p:=charP_of_injective_ringHom jz.injective p
 have ht: (2 :FX)≠0:= fun h=>(by decide : ¬ p∣2)
   ((CharP.cast_eq_zero_iff FX p 2).mp h)
 have hden:qD z (denominator f S)≠0:= by
   rw [denominator,map_mul,map_ofNat]
   exact mul_ne_zero ht ((fibre_mark f.derivative S z).trans_ne hv)
 have hc:=ctV f S
 have hnum :qD z (numerator f S) =
     kr (hasseDeriv 2 S)*qD z (denominator f S) := by
   apply sub_eq_zero.mp
   have h:=congrArg (qD z) hc
   rw [map_sub,map_neg,map_mul,graph_C,marked_derivative,hmark,
     map_zero,neg_zero] at h
   exact h
 obtain ⟨b,hb,hbdiv⟩:=regular_factor f B i z S hB hd hroot hsimple hden hnum
 rw [hc,mul_neg b (aTH (RS f S)),dvd_neg] at hbdiv
 obtain ⟨A,u,hu,hA,hdeg⟩:=fibre_height f S hLift hS (by decide)
 exact Or.inr (descend he hu hA hdeg hmark hb hbdiv)
end
end qZ4UNdb
end
section
namespace qZV9OWb
noncomputable section
open Polynomial Finset
open qNu3xvc (Equation)
open qFD8jve (sheetPole)
open qZu9hjc (HE atPair jacobian)
open cu (L)
def rate (d D W:ℕ) :ℕ:=(6*d-2)*W-3*d^2*D
structure ValueSlice {E :Type} [Field E] [Algebra L E] (A:Equation E) where
 g:E[X][X]
 degree :g.natDegree≤A.d
 weight:HE g A.s (A.b+A.d*A.s)
 common : ∀ v :E7.CurvePlace L E,sheetPole v.value g≤ sheetPole v.value A.f
 size :ℕ
 point :Fin size→AlgebraicClosure E×AlgebraicClosure E
 distinct :Function.Injective point
 f_zero : ∀ i,atPair (algebraMap E _) (point i).1 (point i).2 A.f=0
 g_zero : ∀ i,atPair (algebraMap E _) (point i).1 (point i).2 g=0
 simple : ∀ i,jacobian (algebraMap E _) (point i).1 (point i).2 A.f g≠0
 N :E[X]
 monic:N.Monic
 constant_ne :N.coeff 0≠0
 product :N.map (algebraMap E (AlgebraicClosure E)) =
   ∏ i,((Polynomial.X: (AlgebraicClosure E)[X]) -
     Polynomial.C (atPair (algebraMap E _) (point i).1 (point i).2 A.f.derivative))
end
end qZV9OWb
end
section
set_option autoImplicit true
namespace qXrbKzb
open P5_7_2 (fO Ls)
open q7F2qKe
open qB9xHGe (ng)
open qoK3iCb (BandWitness graphRate scalarSlope uq)
open q5oHm3d
open TD (GM bCb)
open cu (Shape)
def alt (b:fO) (dm:ℚ) (g:ℕ) :ℚ :=
 let direct :=graphRate g
 let gap:ℚ:=(weakAgreement-wX b:ℕ)
 if g=1 then (1-dm/direct)*(1+3*262144/gap)
 else if g=2 then (13+8*262144/gap)*(direct-dm)/(direct-16)
 else uq b g*(direct-dm)/(direct-scalarSlope dm g)
def rateTests (b:fO) (dm h:ℚ) (lim:ℕ) :Bool :=
  (List.range lim).all fun i =>
    decide (alt b dm (i+1)≤h) &&
     (decide (i+1<3) || decide (scalarSlope dm (i+1)≤dm))
theorem rate {b:fO} {dm h:ℚ} {lim:ℕ} (hw:BandWitness b)
    (hf :graphRate 55≤dm) (hn:0≤h) (hl:graphRate (lim+1)≤dm)
    (hc:rateTests b dm h lim=true) :aSz b dm dm h:= by
  refine ⟨(by unfold graphRate; positivity :0≤graphRate 55).trans hf,le_rfl,hf,hn,?_⟩
  intro g hg hg54 hd
  have hgl:g≤lim:= by
    by_contra! h
    have hm:graphRate g≤graphRate (lim+1) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (Nat.cast_le.mpr (by omega))
    exact (not_lt_of_ge (hm.trans hl)) hd
  obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hg.ne'
  have hi:i∈List.range lim:=List.mem_range.mpr (by omega)
  have he :=List.all_eq_true.mp hc i hi
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at he
  by_cases h1 :i+1=1
  · exact Or.inr (Or.inl ⟨h1,by simpa only [alt,ite_eq_left h1,graphRate] using he.1⟩)
  by_cases h2 :i+1=2
  · exact Or.inr (Or.inr (Or.inl ⟨h2,
      by simpa only [alt,ite_eq_right h1,ite_eq_left h2,graphRate] using he.1⟩))
  have h3:3≤ i+1 := by omega
  refine Or.inr (Or.inr (Or.inr ⟨h3,false,uq b (i+1),?_,hw _ h3 hg54,?_⟩))
  · simpa only [scalarSlope,Bool.false_eq_true,ite_false,add_zero] using
      he.2.resolve_left (not_lt_of_ge h3)
  · simpa only [alt,ite_eq_right h1,ite_eq_right h2,graphRate,scalarSlope,Bool.false_eq_true,
      ite_false,add_zero] using he.1
def asb (w:ℕ) :ℚ :=
 ((w &&& 0x1ffffffffff :ℕ) :ℚ)/((w >>> 41) &&& 0x1fff :ℕ)
def rowHeight (b:fO) (w:ℕ) :ℚ :=
 alt b (asb w) ((w >>> 54) &&& 31)
def rowLimit (w:ℕ) :ℕ:=w >>> 59
def entry (data n o t:ℕ) :ℕ:=(data >>> (64*(o*n+t))) &&& 0xffffffffffffffff
structure RowTests (b:fO) (o j w:ℕ) :Prop where
 projected:ProjectionCheck b o j (asb w)
 floor :graphRate 55≤asb w
 height:0≤ rowHeight b w
 limit :graphRate (rowLimit w+1)≤asb w
 bgt:rateTests b (asb w) (rowHeight b w) (rowLimit w)=true
 gH : ∀ k,asb w*SS b j 0 k+rowHeight b w*SS b j 1 k≤ng b o j k
def y8 (b:fO) (n:ℕ) :Prop :=
 ∀ (o:Fin 13) (t:Fin n),dqs b o (t.val+9)
theorem grid_of_tests {b:fO} {n data :ℕ} (hw:BandWitness b)
  (hc : ∀ (o:Fin 13) (t:Fin n),RowTests b o (t.val+9) (entry data n o t)) :
  y8 b n:= by
 intro o t
 let w:=entry data n o t
 have h:=hc o t
 exact ⟨asb w,asb w,rowHeight b w,h.projected,
  rate hw h.floor h.height h.limit h.bgt,h.gH⟩
theorem stage_of_ordinate_bound {s :Ls} {d:Shape} {c:GM} {dm:ℚ}
  (hp:project d (bCb c (proper s.free s.moving (s.dI+1)))≤dm)
  (hg:project d (bCb c (graph (jU s (s.dI+1)) (seed s (s.dI+1))))≤dm)
  (hb:d.U*min (c 0) (min s.free.B s.moving.B:ℕ) +
    (d.B-d.J:ℕ)*c 1+d.J*c 2≤dm) :StageCheck s d c dm:= by
 refine ⟨hp,hg,fun n _ _ e _ he _=>peak_of_bound ?_⟩
 intro v _
 have he' : e≤ min s.free.B s.moving.B:=he.trans (Nat.div_le_self _ _)
 have hx :min (c 0) (ordinateCap s n e)≤ min (c 0) (min s.free.B s.moving.B:ℕ) :=
  min_le_min_left _ ((min_le_left _ _).trans (Nat.cast_le.mpr he'))
 exact (add_le_add
  (add_le_add (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _))
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _)))
  (mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _))).trans hb
set_option quotPrecheck false in
scoped notation "checked!" => of_decide_eq_true (by with_unfolding_all rfl)
set_option quotPrecheck false in
scoped notation "az" hp:arg =>
 ⟨hp,checked!,checked!,checked!,(by with_unfolding_all rfl),
   (by intro k; fin_cases k <;> exact checked!)⟩
end qXrbKzb
end
