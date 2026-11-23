import ProximityPrize.SubmissionLower.ZJbAGBd
set_option Elab.async false
open _root_ renaming Fin.castAdd → zVs, Fin.natAdd → zzs, Function.Injective → zq4, IsFractionRing.injective → zxb, MvPolynomial.affineHilbertFunction → ztr, MvPolynomial.quotientDegreeLE → z9e, MvPolynomial.rename → zHw, Polynomial.C → z1z, Polynomial.mapRingHom → zhd, Polynomial.map_injective → zTo, Polynomial.map_map → zoi, Polynomial.map_zero → zgY, Polynomial.resultant → zSp, Submodule.sum_mem → zo3
section
set_option backward.isDefEq.respectTransparency false
namespace qBajpRb
noncomputable section
open quN7Z4a (compressionWidth)
open cu (L)
open gT (kM)
open Cu
private theorem Ep {C₀:sQ} [Fact (Irreducible C₀)]
    {J:Ideal kM} {g n:ℕ} {R:wJ C₀ J g} (A:yI R n) :
    (incl A).comp (Yx A).toRingHom =
      (algebraMap (abz C₀) (oO C₀)).comp
        (Ideal.Quotient.mk (auG C₀)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change incl A (cls A (zHw Sum.inl (MvPolynomial.C a)))= _
    rw [incl_cls]
    simp [ek,zT]
  · intro i
    change incl A (cls A (zHw Sum.inl (MvPolynomial.X i)))= _
    rw [incl_cls]
    simp [ek,Wt]
private theorem rank_plane {C₀:sQ} [Fact (Irreducible C₀)]
   {J:Ideal kM} {g n:ℕ} {R:wJ C₀ J g} (A:yI R n)
   (k :ℕ) :
   Module.finrank L (u7 A k)=ztr (auG C₀) k := by
 let v :abz C₀ →ₐ[L] CurveRing A :=
   Ideal.Quotient.liftₐ _ (Yx A) (by
     intro q hq
     apply incl_injective A
     rw [map_zero]
     change ((incl A).comp (Yx A).toRingHom) q=0
     rw [Ep,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem.mpr hq,map_zero])
 have hcomp: (incl A).comp v.toRingHom =
     algebraMap (abz C₀) (oO C₀) := by
   apply RingHom.ext
   intro x
   obtain ⟨q,rfl⟩:=Ideal.Quotient.mk_surjective x
   exact DFunLike.congr_fun (Ep A) q
 have hinj:zq4 v := by
   intro x y he
   apply zxb (abz C₀) (oO C₀)
   rw [← hcomp]
   exact congrArg (incl A) he
 let U:=z9e (auG C₀) k
 have hU:U.map v.toLinearMap=u7 A k := by
   dsimp only [U,z9e]
   rw [← Submodule.map_comp]
   rfl
 rw [← hU]
 exact (Submodule.equivMapOfInjective v.toLinearMap hinj U).finrank_eq.symm
private theorem small_plane_rank (C₀:sQ) (hn:C₀≠0) {k :ℕ}
  (hk :k<C₀.totalDegree) :
  ztr (auG C₀) k=(k+2).choose 2 := by
 have hc : {e :Fin 2 →₀ ℕ | e.degree≤k}.ncard=(k+2).choose 2 := by
  simpa using Finsupp.ncard_setOf_degree_le (Fin 2) k
 rw [MvPolynomial.affineHilbertFunction_eq_standard_count,← hc]
 congr 1
 ext e
 simp only [Set.mem_ofPred_eq,MonomialOrder.mem_standardExponents_span_singleton _ hn,
  and_iff_right_iff_imp]
 intro he hdiv
 have hh:=Finsupp.degree_mono hdiv
 rw [MonomialOrder.degree_degree_eq_totalDegree
  (fun _ _ ↦ MvPolynomial.degree_le_degree_of_degLex_le)] at hh
 exact (not_le_of_gt hk) (hh.trans he)
theorem lower_rank {C₀:sQ} [hC:Fact (Irreducible C₀)] {J:Ideal kM} {g n:ℕ}
   {R:wJ C₀ J g} (A:yI R n) {d k :ℕ}
   (hd:C₀.totalDegree=d) (hpos :0<d) :
   (k :ℚ)*d+1≤(Module.finrank L (u7 A k) :ℚ)+(d:ℚ)^2/2 := by
 rw [rank_plane A]
 have hc (u:ℕ) : ((u+2).choose 2 :ℚ)=(u+2 :ℚ)*(u+1)/2 := by
   rw [Nat.cast_choose_two,Nat.cast_add,Nat.cast_ofNat]
   ring
 by_cases h:d≤k
 · rw [MvPolynomial.affineHilbertFunction_span_singleton hC.out.ne_zero (hd ▸ h),hd]
   simp only [Nat.card_fin,hc,Nat.cast_sub h]
   have hp: (1 :ℚ)≤d:= by exact_mod_cast hpos
   nlinarith
 · rw [small_plane_rank C₀ hC.out.ne_zero (by omega),hc]
   have hk : (0:ℚ)≤k := by positivity
   nlinarith [sq_nonneg ((k :ℚ) - d)]
theorem row_count (D g:ℕ) :4*aia D g=compressionWidth D g:= by
 have h:=Finset.sum_range_id_mul_two (g+1)
 rw [Nat.add_sub_cancel] at h
 unfold aia compressionWidth
 rw [← Finset.sum_mul]
 calc
  _=2*D*((∑ i:Fin (g+1),i.val)*2) := by ring
  _ = _:= by rw [Fin.sum_univ_eq_sum_range (fun i:ℕ=>i),h]; ring
def multiplierDegree (d H :ℕ) :ℕ:=(H+2*d*d)/(3*d)+1
theorem multiplier_bounds {d H :ℕ} (hd:0<d) :
  (H :ℚ)+2*(d:ℚ)^2<3*(multiplierDegree d H)*d ∧
  (multiplierDegree d H :ℚ)*d≤H/3+2*(d:ℚ)^2/3+d:= by
 have hn:0<3*d:= by positivity
 have hl:=Nat.lt_mul_div_succ (H+2*d*d) hn
 have hu:=Nat.mul_div_le (H+2*d*d) (3*d)
 let k :=(H+2*d*d)/(3*d)
 change H+2*d*d<(3*d)*(k+1) at hl
 change (3*d)*k≤H+2*d*d at hu
 have hlq: (H :ℚ)+2*d*d<(3*d)*((k :ℚ)+1) := by exact_mod_cast hl
 have huq: (3:ℚ)*d*k≤H+2*(d:ℚ)*d:= by exact_mod_cast hu
 have hk : (multiplierDegree d H :ℚ)=(k :ℚ)+1 := by simp [multiplierDegree,k]
 rw [hk]
 constructor <;> nlinarith
end
end qBajpRb
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qBajpRb
noncomputable section
open Polynomial
open quN7Z4a (physicalWeight)
open cu (L)
open gT (kM)
open Cu
variable {C₀:sQ} [Fact (Irreducible C₀)] {J:Ideal kM} {g n:ℕ}
 {R:wJ C₀ J g} (A:yI R n)
theorem equation_degree : (equation A).natDegree=g:= by
 rw [← natDegree_map_eq_of_injective (f :=zhd (incl A))
  (zTo _ (incl_injective A)) (equation A),equation_generic,
  natDegree_C_mul (show C (A.scale :oO C₀)≠0 by simp),R.degree]
theorem equation_nonzero :equation A≠0:= by
 have hR:R.equation≠0:= fun h=>R.irreducible.ne_zero (by rw [h,zgY])
 intro h
 have h' := equation_generic A
 rw [h,zgY] at h'
 exact (mul_ne_zero (by simp) hR) h'.symm
private theorem mul_coeff_mem {P Q: (CurveRing A)[X]} {k j k' j' : ℕ}
  (hP : ∀ a,P.coeff a∈stock A k j) (hQ : ∀ a,Q.coeff a∈stock A k' j') (a :ℕ) :
  (P*Q).coeff a∈stock A (k+k') (j+j') := by
 rw [coeff_mul]
 exact zo3 _ fun x _ =>
  stock_mul A _ _ _ _ (Submodule.mul_mem_mul (hP x.1) (hQ x.2))
private theorem prod_coeff_mem {ι:Type} (U:Finset ι) (P:ι→(CurveRing A)[X]) {k j:ℕ}
    (h : ∀ i∈U,∀ a,(P i).coeff a∈stock A k j) (a :ℕ) :
    (∏ i∈U,P i).coeff a∈stock A (U.card*k) (U.card*j) := by
  classical
  induction U using Finset.induction_on generalizing a with
  | empty =>
      by_cases ha :a=0 <;> simp [Polynomial.coeff_one,ha,one_mem_stock A]
  | @insert i U hi ih =>
      rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.add_mul,
        Nat.one_mul,Nat.one_mul,add_comm (U.card*k),add_comm (U.card*j)]
      exact mul_coeff_mem A (h i (Finset.mem_insert_self ..))
        (fun a=>ih (fun l hl=>h l (Finset.mem_insert_of_mem hl)) a) a
private theorem resultant_coeff {G: (CurveRing A)[X][X]} {k :ℕ}
   (hG : ∀ i a,(G.coeff i).coeff a∈stock A k 1) (a :ℕ) :
   (zSp (R:=(CurveRing A)[X]) (equation A) G g G.natDegree).coeff a∈stock A (g*k) (g+G.natDegree) := by
 classical
 let m:=G.natDegree
 let B:=(equation A).sylvester G g m
 change B.det.coeff a∈_
 rw [Matrix.det_apply',finsetSum_coeff]
 apply zo3
 intro σ _
 rw [← zsmul_eq_mul,coeff_smul]
 apply zsmul_mem
 rw [Fin.prod_univ_add]
 have hleft (j:Fin g) (a :ℕ) : (B (σ (zVs m j)) (zVs m j)).coeff a∈stock A k 1 := by
   simp only [B,sylvester,Matrix.of_apply,Fin.addCases_left]
   split_ifs
   · exact hG _ _
   · simp
 have hright (j:Fin m) (a :ℕ) : (B (σ (zzs g j)) (zzs g j)).coeff a∈stock A 0 1 := by
   simp only [B,sylvester,Matrix.of_apply,Fin.addCases_right]
   split_ifs
   · exact tuple_mem_stock A (equation_coeff A _ _)
   · simp
 have hl (a :ℕ) :
     (∏ j:Fin g,B (σ (zVs m j)) (zVs m j)).coeff a∈stock A (g*k) g:= by
   simpa using prod_coeff_mem A Finset.univ _ (fun j _=>hleft j) a
 have hr (a :ℕ) :
     (∏ j:Fin m,B (σ (zzs g j)) (zzs g j)).coeff a∈stock A 0 m:= by
   simpa using prod_coeff_mem A Finset.univ _ (fun j _=>hright j) a
 simpa only [add_zero] using mul_coeff_mem A hl hr a
private theorem coprime_of_weight {D M:ℕ} (hM:0<M) (hlarge :M≤physicalWeight D R.equation)
   {G: (CurveRing A)[X][X]} (hG0:G≠0) (hGdeg:G.natDegree≤g)
   (hsmall : ∀ i a,(G.coeff i).coeff a≠0→a+i*D <M) :
   IsCoprime ((equation A).map ((F5 C₀).comp (zhd (incl A))))
     (G.map ((F5 C₀).comp (zhd (incl A)))) := by
 let E :=oO C₀
 let ι:=zhd (incl A)
 let G' := G.map ι
 have hi:zq4 ι:=zTo _ (incl_injective A)
 have hG' : G' ≠ 0:=(Polynomial.map_ne_zero_iff (f :=ι) hi).mpr hG0
 have hf :R.equation≠0:= fun h=>R.irreducible.ne_zero (by rw [h,zgY])
 have hsmall' : physicalWeight D G' < M:= by
   apply Nat.lt_of_le_pred hM
   apply Finset.sup_le
   intro i hi
   let a :=(G'.coeff i).natDegree
   have hn: (G'.coeff i).coeff a≠0 :=
     leadingCoeff_ne_zero.mpr (Polynomial.mem_support_iff.mp hi)
   have hn' : (G.coeff i).coeff a≠0:= by
     intro h
     exact hn (by simp [G',ι,coeff_map,h])
   exact Nat.le_pred_of_lt (hsmall i a hn')
 have hcop:IsCoprime (R.equation.map (F5 C₀)) (G'.map (F5 C₀)) := by
   refine (R.irreducible.isCoprime_or_dvd _).resolve_right ?_
   intro hd
   obtain ⟨q,hq⟩:=R.primitive.dvd_of_fraction_map_dvd_fraction_map hd
   have hq0:q≠0:= fun h=>hG' (by rw [hq,h,mul_zero])
   have hqd:q.natDegree=0:= by
     have hb:G'.natDegree≤g:=(natDegree_map_le (p:=G)).trans hGdeg
     rw [hq,natDegree_mul hf hq0,R.degree] at hb
     omega
   let a :=q.coeff 0
   have ha :a≠0:= by
     intro h
     exact hq0 ((eq_C_of_natDegree_eq_zero hqd).trans (by rw [show q.coeff 0=0 from h,C_0]))
   have he :G' = C a*R.equation := by
     rw [hq,eq_C_of_natDegree_eq_zero hqd,mul_comm]
   have hw:physicalWeight D R.equation≤physicalWeight D G' := by
     apply Finset.sup_le
     intro j hj
     have hj0:=Polynomial.mem_support_iff.mp hj
     have hc:G'.coeff j=a*R.equation.coeff j:= by rw [he,coeff_C_mul]
     have hj' := Polynomial.mem_support_iff.mpr (show G'.coeff j≠0 from hc ▸ mul_ne_zero ha hj0)
     refine le_trans ?_ (Finset.le_sup hj')
     rw [hc,natDegree_mul ha hj0]
     omega
   exact (not_le_of_gt hsmall') (hlarge.trans hw)
 have hu:IsUnit (z1z (F5 C₀ (z1z (A.scale :E)))) :=
   A.scale.isUnit.map (Polynomial.C.comp ((F5 C₀).comp z1z))
 rw [← zoi,← zoi,equation_generic,Polynomial.map_mul,map_C]
 exact (isCoprime_mul_unit_left_left hu _ _).mpr hcop
theorem resultant_cut {D M k :ℕ} (hg:0<g) (hM:0<M)
    (hlarge :M≤physicalWeight D R.equation) {G: (CurveRing A)[X][X]} (hG0:G≠0)
    (hGdeg:G.natDegree≤g) (hsmall : ∀ i a,(G.coeff i).coeff a≠0→a+i*D <M)
    (hG : ∀ i a,(G.coeff i).coeff a∈stock A k 1) :
    ∃ q∈stock A (g*k) (g+G.natDegree),q≠0 ∧
      ∀ (φ:CurveRing A →ₐ[L] L) (u:L[X]),
        ((equation A).map (zhd φ.toRingHom)).eval u=0 →
        (G.map (zhd φ.toRingHom)).eval u=0→φ q=0:= by
  let F:=equation A
  let ev :=(F5 C₀).comp (zhd (incl A))
  have hei:zq4 ev :=
    (zxb (oO C₀)[X] (y7 C₀)).comp
      (zTo _ (incl_injective A))
  have hR:=Polynomial.resultant_ne_zero (R:=y7 C₀) (F.map ev) (G.map ev)
    (coprime_of_weight A hM hlarge hG0 hGdeg hsmall)
  have hdF: (F.map ev).natDegree=g :=
    (natDegree_map_eq_of_injective hei F).trans (equation_degree A)
  rw [hdF,natDegree_map_eq_of_injective hei G] at hR
  let f : (CurveRing A)[X] :=zSp F G g G.natDegree
  have hmap :ev f=zSp (R:=y7 C₀)
      (F.map ev) (G.map ev) g G.natDegree :=
    (Polynomial.resultant_map_map (R:=(CurveRing A)[X]) (S:=y7 C₀)
      F G g G.natDegree ev).symm
  have hf :f≠0:= fun h=>hR (hmap.symm.trans (by rw [h,map_zero]))
  let a :=f.natDegree
  refine ⟨f.coeff a,resultant_coeff A hG a,leadingCoeff_ne_zero.mpr hf,?_⟩
  intro φ u hu hv
  have hc:f.map φ.toRingHom=0 :=
    Polynomial.map_resultant_eq_zero_of_common_root (R:=(CurveRing A)[X]) (S:=L[X])
      (m:=g) (n:=G.natDegree) (zhd φ.toRingHom)
      F G (equation_degree A).le le_rfl (Or.inl hg.ne') u hu hv
  have ha :=congrArg (fun P:L[X]=>P.coeff a) hc
  change φ.toRingHom (f.coeff a)=0
  simpa only [coeff_map,coeff_zero] using ha
end
end qBajpRb
end
