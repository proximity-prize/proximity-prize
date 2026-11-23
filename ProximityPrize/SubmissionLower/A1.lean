import ProximityPrize.SubmissionLower.B
import ProximityPrize.SubmissionLower.A0
import ProximityPrize.SubmissionLower.L
import ProximityPrize.SubmissionLower.AH
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.adjoin → zum, CommRing → za6, DFunLike.congr_fun → zmU, Equiv.Perm.sign → zjl, Equiv.apply_symm_apply → zIV, Equiv.sum_comp → z5O, Field → zrb, Fin.last → zym, Fin.lastCases → zsB, Fin.le_last → zO9, Fin.sum_univ_castSucc → zHE, Finset → zJe, Finset.exists_max_image → z6Q, Finset.filter_subset → zT0, Finset.mem_filter → zO0, Finset.mem_univ → zTc, Finset.ne_of_mem_erase → zFe, Finset.prod_congr → zX3, Finset.prod_eq_zero → zue, Finset.prod_erase_mul → zNr, Finset.range → z4x, Finset.single_le_sum → zfK, Finset.subset_univ → ziq, Finset.sum_congr → zUo, Finset.sum_eq_single_of_mem → zpa, Finset.sum_eq_zero → zYF, Finset.sum_le_sum → zQk, Finset.sum_mul → zkq, Finset.sum_sub_distrib → zQq, Finset.sum_update_of_mem → z6q, Finset.sup_le → zf9, Finset.univ → zdB, Finsupp.degree_eq_sum → zFi, Finsupp.weight → ztN, Finsupp.weight_apply → zDM, Fintype → z85, Fintype.card_fin → zgY, Fintype.ofFinite → zQs, Function.Injective → zq4, Function.Surjective → zpX, Function.comp_apply → z3s, Function.iterate_succ_apply' → zLk, Function.update → zWr, Function.update_of_ne → zBg, Function.update_self → zuO, Ideal → znc, Ideal.Quotient.lift_mk → z0R
open _root_ renaming Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.Quotient.mkₐ → zvR, Ideal.comap_comap → zg6, Ideal.comap_injective_of_surjective → zyU, Ideal.comap_mono → zOS, Ideal.quotientMap → z3G, Ideal.quotientMap_injective → zmq, Ideal.quotientMap_surjective → zc0, Ideal.span → zye, Ideal.subset_span → zCn, Int.units_eq_one_or → znm, IsDomain → ztn, IsFractionRing.injective → zxb, IsFractionRing.map → zJ1, IsFractionRing.ringEquivOfRingEquiv → zDt, IsScalarTower.algebraMap_eq → zYY, LinearMap.congr_fun → z5U, LinearMap.ker → z83, LinearMap.mem_ker → zeS, Matrix → z30, Matrix.det_apply → zwK, Matrix.fromCols → zE7, Matrix.map_apply → zAg, Matrix.submatrix_apply → z6T, Module.Finite → zAa, Module.finrank → zsE, Module.finrank_fin_fun → z4H, Module.length_quotient → zSA, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.affineHilbertPolynomial → zIU, MvPolynomial.algebraMap_eq → zKm, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, MvPolynomial.eval_X → zV6, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.eval₂Hom_X' → zrD, MvPolynomial.induction_on → z5i, MvPolynomial.induction_on' → zNP, MvPolynomial.le_weightedTotalDegree → z6P, MvPolynomial.map → zDK, MvPolynomial.ringHom_ext → zXT, MvPolynomial.weightedTotalDegree_zero → z4a, Nat.add_comm → zg2, Nat.add_right_cancel → z8U
open _root_ renaming Nat.eq_zero_of_le_zero → za7, Nat.factorial → zs5, Nat.le_add_right → z8K, Nat.le_of_lt_succ → zeh, Nat.lt_succ_of_le → zB1, Nat.mul_comm → z5A, Nat.mul_le_mul_left → zBI, Nat.sub_add_cancel → zxt, Nat.sub_le_sub_right → zIu, Nat.zero_le → zD0, Polynomial → zM1, Polynomial.C → z1z, Polynomial.C_mul → zPC, Polynomial.C_mul_X_pow_eq_monomial → zoT, Polynomial.X → z7y, Polynomial.algebraMap_eq → zrE, Polynomial.centeredCoefficientPrefix → z0x, Polynomial.coeToPowerSeries.ringHom_apply → zwl, Polynomial.coe_C → zni, Polynomial.coeff_monomial → zQm, Polynomial.coeff_mul_X_pow' → zBK, Polynomial.derivative → zst, Polynomial.derivative_mul → zAh, Polynomial.eval_map_apply → zdm, Polynomial.eval_mul → zbr, Polynomial.hasseDeriv → z75, Polynomial.hasseDeriv_map → zvb, Polynomial.mapRingHom → zhd, Polynomial.map_map → zoi, Polynomial.monomial → zdM, Polynomial.natDegree_zero → zbf, Polynomial.taylor → zcJ, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.coeff → z2o, PowerSeries.map → zS4, PowerSeries.map_C → z2H, PowerSeries.rescale → zpc, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, RingHom.ker → zdq, RingHom.ker_eq_comap_bot → zPx, RingHom.mapMatrix_apply → zcW, Set.mem_image_of_mem → zVS, Set.range → zxp, WithBot → zUi
set_option autoImplicit true
section
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace aiH
noncomputable section
open K1 wT MvPolynomial
def c1 :Prop :=
  ∀ {F:Type} [zrb F] (G:z3y (Fin 4) F) (w E :ℕ),
    2≤E→G.weightedTotalDegree LV≤E →
    ∀ n≤w,(aIS G w n).weightedTotalDegree LV ≤
      (2*w - 1)*(E - 1)+1
def c2 :Prop :=
  ∀ {F:Type} [zrb F] (G:z3y (Fin 4) F) (w:ℕ)
    (D:zM1 F) (s t:F),
    aeval (D9 D s t) G=0 →
    ∀ n≤w,(↑(zs5 n) :F)≠0 →
      aeval (D9 D s t) (aIS G w n) =
        aeval (D9 D s t) (pderiv 1 G)^(2*w - 1) *
          z75 n D
section Field
variable {F:Type} [zrb F]
private abbrev XF (F:Type) [zrb F] :=FractionRing (zM1 F)
private def ξ:XF F:=algebraMap (zM1 F) (XF F) z7y
private def bcg:Fin 4→z3y (Fin 3) (XF F) :=
 ![C (ξ (F:=F)),z9v 0,z9v 1,z9v 2]
private def aaD:z3y (Fin 4) F →ₐ[F] z3y (Fin 3) (XF F) :=
 aeval bcg
private def aMJ (D:zM1 F) (s t:F) :Fin 3→XF F :=
 ![algebraMap (zM1 F) (XF F) D,algebraMap F (XF F) s,algebraMap F (XF F) t]
private theorem bbL (G:z3y (Fin 4) F) :
   (aaD G).totalDegree≤G.weightedTotalDegree LV:= by
 let ι:=algebraMap F (XF F)
 have hm:aeval (R:=XF F) (bcg (F:=F)) (zDK ι G) =
     aaD G:=MvPolynomial.aeval_map_algebraMap (A:=XF F) _ _
 rw [← hm,← weightedTotalDegree_one]
 refine (weightedTotalDegree_aeval_le_of_le LV (1 :Fin 3→ℕ)
   bcg (zDK ι G) ?_).trans ?_
 · intro i
   fin_cases i <;> simp [bcg,LV,weightedTotalDegree_one]
 · exact Finset.sup_mono (support_map_subset _ _)
private theorem c3O (G:z3y (Fin 4) F) :
   pderiv (0:Fin 3) (aaD G)=aaD (pderiv 1 G) := by
 classical
 induction G using z5i with
 | C a=>simp [aaD]
 | add a b ha hb=>simp only [map_add,ha,hb]
 | mul_X a j ha =>
   simp only [map_mul,pderiv_mul,map_add,ha]
   fin_cases j <;> simp [aaD,bcg]
private theorem b1r (a :F) :
  algebraMap (zM1 F) (XF F) (z1z a)=algebraMap F (XF F) a := by
 rw [IsScalarTower.algebraMap_apply F (zM1 F) (XF F),zrE]
private theorem aUo (G:z3y (Fin 4) F)
  (D:zM1 F) (s t:F) :
  zY9 (aMJ D s t) (aaD G) =
    algebraMap (zM1 F) (XF F) (aeval (D9 D s t) G) := by
 have h: (zY9 (aMJ D s t)).comp aaD.toRingHom =
    (algebraMap (zM1 F) (XF F)).comp (aeval (D9 D s t)).toRingHom:= by
  apply zXT
  · intro a
    simp [aaD,zrE,b1r]
  · intro i
    fin_cases i <;> simp [aaD,bcg,aMJ,D9,ξ,b1r]
 exact zLs h G
private theorem d1T (D:zM1 F) :
   (D.map (algebraMap F (XF F))).eval (ξ (F:=F)) =
     algebraMap (zM1 F) (XF F) D:= by
 rw [Polynomial.eval_map]
 have h:Polynomial.eval₂RingHom (algebraMap F (XF F)) ξ =
     algebraMap (zM1 F) (XF F) := by
   apply Polynomial.ringHom_ext
   · intro a
     simp [b1r]
   · simp [ξ]
 exact zLs h D
private theorem cKu (G:z3y (Fin 4) F) (j:ℕ) :
   (aNg G j).weightedTotalDegree LV ≤
     G.weightedTotalDegree LV:= by
 induction j with
 | zero=>exact le_rfl
 | succ j ih =>
     unfold aNg at *
     rw [zLk]
     exact (weightedTotalDegree_pderiv_le _ _ _).trans ih
private def denominator (G:z3y (Fin 4) F) (w:ℕ) :
  z3y (Fin 3) (XF F) :=
 aaD (pderiv 1 G)^(2*w - 1)
private def numerator (G:z3y (Fin 4) F) (w:ℕ) :
  zM1 (z3y (Fin 3) (XF F)) :=
 z0x (C ξ) (fun n=>aaD (aIS G w n)) (w+1)
private theorem b9E {R:Type} [Semiring R]
   {D:zM1 R} {w:ℕ} (h:D.degree < ↑(w+1)) :D.natDegree≤w:= by
 by_cases hz :D =0
 · simp [hz]
 · exact zeh ((Polynomial.natDegree_lt_iff_degree_lt hz).mpr h)
private theorem af0 (G:z3y (Fin 4) F) (w:ℕ) :
  (numerator G w).natDegree≤w :=
 b9E
  (Polynomial.degree_centeredCoefficientPrefix_lt
    (C ξ) (fun n=>aaD (aIS G w n)) (w+1))
private theorem c1S (h1 :c1) (G:z3y (Fin 4) F) (w E :ℕ)
  (hE :2≤E) (hG:G.weightedTotalDegree LV≤E) (x :XF F) :
  ((numerator G w).eval (C x)).totalDegree≤(2*w - 1)*(E - 1)+1 := by
 unfold numerator z0x
 rw [Polynomial.taylor_eval,Polynomial.eval_finsetSum]
 apply totalDegree_finsetSum_le
 intro n _
 rw [Polynomial.eval_monomial,← map_neg,← map_add,← map_pow]
 exact (totalDegree_mul _ _).trans (by
  rw [totalDegree_C,add_zero]
  exact (bbL _).trans (h1 G w E hE hG n (zeh n.isLt)))
private theorem bc6 (G:z3y (Fin 4) F) (w E :ℕ)
  (hG:G.weightedTotalDegree LV≤E) :
  (denominator G w).totalDegree≤(2*w - 1)*(E - 1) := by
 apply (totalDegree_pow _ _).trans
 apply zBI
 exact (bbL _).trans
  ((weightedTotalDegree_pderiv_le_sub LV 1 G).trans
    (zIu hG 1))
private theorem Uj (h2 :c2) (G:z3y (Fin 4) F) (w:ℕ)
    (D:zM1 F) (s t:F) (hD:D.natDegree≤w)
    (hroot :aeval (D9 D s t) G=0)
    (hfactor : ∀ n≤w,(↑(zs5 n) :F)≠0) :
    (numerator G w).map (zY9 (aMJ D s t)) =
      z1z (zY9 (aMJ D s t) (denominator G w)) *
        D.map (algebraMap F (XF F)) := by
  let ev :=zY9 (aMJ D s t)
  change (numerator G w).map ev=z1z (ev (denominator G w))*_
  apply Polynomial.taylor_injective ξ
  ext n
  have hm:=Polynomial.map_taylor (numerator G w) (C (ξ (F:=F))) ev
  change _=zcJ (ev (C ξ)) _ at hm
  rw [z9X] at hm
  rw [← hm,Polynomial.coeff_map,numerator,Polynomial.coeff_taylor_centeredCoefficientPrefix]
  rw [show zcJ ξ (z1z (ev (denominator G w)) *
      D.map (algebraMap F (XF F))) =
      z1z (ev (denominator G w)) *
        zcJ ξ (D.map (algebraMap F (XF F))) by
    calc
      _=zcJ ξ (z1z (ev (denominator G w))) *
          zcJ ξ (D.map (algebraMap F (XF F))) :=
        map_mul (Polynomial.taylorAlgHom ξ) _ _
      _ = _:= by rw [Polynomial.taylor_C]]
  rw [Polynomial.coeff_C_mul]
  split_ifs with hn
  · have h:=h2 G w D s t hroot n (zeh hn) (hfactor n (zeh hn))
    rw [show ev (aaD (aIS G w n))= _ from aUo _ D s t,
      h,map_mul,map_pow,Polynomial.taylor_coeff,zvb,d1T]
    simp only [denominator,map_pow,ev,aUo]
  · have hd: (zcJ ξ (D.map (algebraMap F (XF F)))).natDegree<n:= by
      rw [Polynomial.natDegree_taylor]
      exact Polynomial.natDegree_map_le.trans_lt (hD.trans_lt (by omega))
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd,mul_zero,map_zero]
end Field
end
end aiH
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace aiG
noncomputable section
open Polynomial Matrix gR K1
def c1 :Prop :=
  ∀ (F:Type) [zrb F] (h L s :ℕ)
    (Q:Fin 2×Fin (h+1)→aZ F),
    h+s=L→0<s→Q≠0→aG8 Q →
    let W:=Mc.Sm (Gz Q) L s
    aG8 (Mc.acq W) ∧
      ∀ b i:Fin 2,0<Kn Q b i →
        ∃ rows :Fin s→Fin L,
          (Mc.acq W (fun j=>(b,rows j))).degreeOf i =
            s*Kn Q b i
def c2 :Prop :=
  ∀ (F:Type) [zrb F] (L w s :ℕ)
    (M:z30 (Fin 2×Fin L) (Fin w) (aZ F))
    (W:z30 (Fin 2×Fin L) (Fin s) (aZ F)),
    0<s→s≤L →
    (M.map (algebraMap (aZ F) (CS F))).rank+s=2*L →
    W.transpose*M=0 →
    (∀ b j (i:Fin 2),(M b j).degreeOf i≤ if b.1=i then 1 else 0) →
    aG8 (Mc.acq W) →
    ∀ (b i:Fin 2) (rows :Fin s→Fin L),
      (Mc.acq W (fun j=>(b,rows j))).degreeOf i ≤
        if b=i then L - s else L
end
end aiG
end
section
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace bRc
noncomputable section
open K1 wT Qo MvPolynomial gR
variable {F:Type*} [zrb F]
def ajo (q:ℕ) :z3y (Fin 4) F →ₐ[F] zM1 F :=
 aeval ![0,0,z7y,z7y ^q]
theorem b5F (q:ℕ) (P:z3y (Fin 5) F) :
    graph q P=(finSuccEquiv F 4 P).map (ajo q).toRingHom:= by
  have h:graph (F:=F) q =
      (Polynomial.mapAlgHom (ajo q)).comp (finSuccEquiv F 4).toAlgHom:= by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change graph q (z9v 0) =
        (finSuccEquiv F 4 (z9v 0)).map (ajo q).toRingHom
      simp [graph,finSuccEquiv_X_zero]
    · change graph q (z9v j.succ) =
        (finSuccEquiv F 4 (z9v j.succ)).map (ajo q).toRingHom
      rw [finSuccEquiv_X_succ,Polynomial.map_C]
      fin_cases j <;> simp [graph,ajo]
  exact zmU h P
private def bCZ:Fin 2→Fin 4 := ![2,3]
private theorem cGB:zq4 bCZ:= by
 intro i j h
 fin_cases i <;> fin_cases j <;> first | rfl | contradiction
theorem cGw (q:ℕ) (hq:0<q) (Q:z3y (Fin 4) F)
    (hQ:Q≠0) (h0:Q.degreeOf 0=0) (h1 :Q.degreeOf 1=0)
    (hS:Q.degreeOf 2<q) :ajo q Q≠0:= by
  classical
  obtain ⟨R,rfl⟩:=exists_rename_eq_of_vars_subset_range Q bCZ
    cGB (by
      intro i hi
      have hi' := mem_vars_iff_degreeOf_ne_zero.mp hi
      fin_cases i
      · exact (hi' h0).elim
      · exact (hi' h1).elim
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩)
  have hR:R≠0:= fun h=>hQ (by rw [h,map_zero])
  have hdeg:R.degreeOf 0<q:= by
    rw [← degreeOf_rename_of_injective cGB (0:Fin 2)]
    exact hS
  have he :ajo (F:=F) q (rename bCZ R) =
      cu.Vg q R:= by
    have hv : (![0,0,z7y,z7y ^q] :Fin 4→zM1 F) ∘
        bCZ = ![z7y,z7y ^q] := by
      funext i
      fin_cases i <;> rfl
    rw [ajo,aeval_rename,hv,cu.Vg]
  rw [he]
  exact cu.bG0 q hq R hR hdeg
theorem dMO (q:ℕ) (hq:0<q)
   (P:z3y (Fin 5) F) (hP:yV P)
   (hS:P.degreeOf 3<q) (i:ℕ) (hi: (finSuccEquiv F 4 P).coeff i≠0) :
   ajo q ((finSuccEquiv F 4 P).coeff i)≠0:= by
 apply cGw q hq _ hi
 · exact za7 ((degreeOf_coeff_finSuccEquiv P 0 i).trans hP.1.le)
 · exact za7 ((degreeOf_coeff_finSuccEquiv P 1 i).trans hP.2.le)
 · exact (degreeOf_coeff_finSuccEquiv P 2 i).trans_lt hS
theorem bqM (q:ℕ) (hq:0<q) (P:z3y (Fin 5) F)
   (hP:yV P) (hS:P.degreeOf 3<q) :
   (graph q P).natDegree=P.degreeOf 0:= by
 by_cases hz :P=0
 · simp [hz]
 have hv :finSuccEquiv F 4 P≠0:= by
   intro h
   exact hz ((finSuccEquiv F 4).injective (h.trans (map_zero _).symm))
 rw [b5F,Polynomial.natDegree_map_of_leadingCoeff_ne_zero,natDegree_finSuccEquiv]
 exact dMO q hq P hP hS _
   (Polynomial.leadingCoeff_ne_zero.mpr hv)
theorem gM6 (q:ℕ) (hq:0<q) (P:z3y (Fin 5) F)
   (hP:yV P) (hS:P.degreeOf 3<q) (x :F)
   (h: (graph q P).eval (z1z x)=0) :
   (finSuccEquiv F 4 P).eval (C x)=0:= by
 let Q:=(finSuccEquiv F 4 P).eval (C x)
 have hQ (j:Fin 4) :Q.degreeOf j≤P.degreeOf j.succ:= by
   let V:=finSuccEquiv F 4 P
   change (V.eval (C x)).degreeOf j≤_
   rw [Polynomial.eval_eq_sum_range]
   apply (degreeOf_sum_le _ _ _).trans
   apply zf9
   intro i _
   exact (degreeOf_mul_le j _ _).trans (by
     simpa only [← map_pow,degreeOf_C,add_zero] using degreeOf_coeff_finSuccEquiv P j i)
 have h0:ajo q Q=0:= by
   have hc:ajo q (C x :z3y (Fin 4) F)=z1z x := by
     simp [ajo]
   have he :=zdm (ajo q).toRingHom (C x)
     (p:=finSuccEquiv F 4 P)
   change ((finSuccEquiv F 4 P).map (ajo q).toRingHom).eval
     (ajo q (C x))=ajo q Q at he
   rw [hc,← b5F] at he
   exact he.symm.trans h
 by_contra hn
 exact cGw q hq Q hn
   (za7 ((hQ 0).trans hP.1.le))
   (za7 ((hQ 1).trans hP.2.le))
   ((hQ 2).trans_lt hS) h0
private theorem ex4 (S:zJe I) (P:zM1 (z3y (Fin 4) K))
   (h : ∀ i∈S,P.eval (C (node i))=0) :
   (mL node S).map C∣P:= by
 classical
 let R:=z3y (Fin 4) K
 let f :R →+* FractionRing R:=algebraMap R (FractionRing R)
 have hf :zq4 f :=zxb R (FractionRing R)
 apply (Polynomial.map_dvd_map f hf ((S8 node S).map C)).mp
 rw [zoi,b8d]
 apply kL.bsf _
   ((hf.comp (MvPolynomial.C_injective (Fin 4) K)).comp
     ProximityPrize.Benchmark.IRSProfile.domain.injective)
 intro i hi
 change (P.map f).eval (f (C (node i)))=0
 rw [zdm,h i hi,map_zero]
private def aI0 (S:zJe I) :z3y (Fin 5) K :=
 (finSuccEquiv K 4).symm ((mL node S).map C)
private theorem ekx (S:zJe I) :graph p (aI0 S) =
  jH (mL node S) := by
 rw [b5F,aI0,AlgEquiv.apply_symm_apply,zoi]
 congr 1
 ext a
 simp [ajo]
private theorem aCW {Q P:z3y (Fin 5) F} (hP:P≠0)
  (h:Q∣P) (j:Fin 5) :Q.degreeOf j≤P.degreeOf j:= by
 obtain ⟨E,hE⟩:=h
 have hQ:Q≠0:= fun hz=>hP (by rw [hE,hz,zero_mul])
 have hEn:E≠0:= fun hz=>hP (by rw [hE,hz,mul_zero])
 rw [hE,degreeOf_mul_eq hQ hEn]
 exact z8K _ _
private theorem bJU {Q P:z3y (Fin 5) F} (hP:P≠0)
   (ho:yV P) (h:Q∣P) :yV Q :=
 ⟨za7 ((aCW hP h 1).trans ho.1.le),
   za7 ((aCW hP h 2).trans ho.2.le)⟩
private theorem bsT:0<p:= by decide
private theorem b02 (S:zJe I) (P:z3y (Fin 5) K)
    (Q:nC) (content:zM1 K) (hQ:Q≠0) (hc:content≠0)
    (hP:yV P) (hS:P.degreeOf 3<p)
    (h:graph p P=z1z content*(jH (mL node S)*Q)) :
    ∃ E :z3y (Fin 5) K,P=aI0 S*E∧E≠0 ∧
      graph p E=z1z content*Q:= by
  have hd:=ex4 S (finSuccEquiv K 4 P) (fun i hi=> by
    apply gM6 p bsT P hP hS
    rw [h,zbr,zbr,Aj.ari,
      arK node S i hi,Polynomial.C_0,zero_mul,mul_zero])
  obtain ⟨E',hE'⟩:=hd
  let E :=(finSuccEquiv K 4).symm E'
  have he :P=aI0 S*E := by
    apply (finSuccEquiv K 4).injective
    simpa [aI0,E,map_mul] using hE'
  have hm:jH (mL node S)≠0 :=
    ((S8 node S).map (z1z:K →+* zM1 K)).ne_zero
  have hgE :graph p E=z1z content*Q:= by
    apply mul_left_cancel₀ hm
    calc
      jH (mL node S)*graph p E=graph p P:= by
        rw [he,map_mul,ekx]
      _=jH (mL node S)*(z1z content*Q) :=h.trans (mul_left_comm _ _ _)
  have hen:E≠0:= by
    intro hz
    rw [hz,map_zero] at hgE
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hQ) hgE.symm
  exact ⟨E,he,hen,hgE⟩
private theorem dcS {U V:nC} (hUV:IsCoprime (sZ U) (sZ V))
   {content:zM1 K} (hc:content≠0) :
   IsRelPrime (sZ (z1z content*U))
     (sZ (z1z content*V)) := by
 have hu:IsUnit (z1z (Aj.GC content)) :=
   Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
     ((map_ne_zero_iff _ Aj.aAg).mpr hc))
 have hmap (Q:nC) :sZ (z1z content*Q) =
     z1z (Aj.GC content)*sZ Q:= by
   change (z1z content*Q).map Aj.GC= _ *Q.map Aj.GC
   rw [Polynomial.map_mul,Polynomial.map_C]
 intro d hdU hdV
 rw [hmap,hu.dvd_mul_left] at hdU hdV
 exact hUV.isRelPrime hdU hdV
private theorem c3C {d:z3y (Fin 5) K}
   (ho:yV d) (hx :d.degreeOf 0=0) :
   ∃ q:z3y (Fin 2) K,rename (![3,4] :Fin 2→Fin 5) q=d:= by
 classical
 apply exists_rename_eq_of_vars_subset_range
 · intro i j h
   fin_cases i <;> fin_cases j <;> first | rfl | contradiction
 · intro i hi
   have hi' := mem_vars_iff_degreeOf_ne_zero.mp hi
   fin_cases i
   · exact (hi' hx).elim
   · exact (hi' ho.1).elim
   · exact (hi' ho.2).elim
   · exact ⟨0,rfl⟩
   · exact ⟨1,rfl⟩
end
end bRc
end
section
namespace cxM
open wT aiH MvPolynomial
variable {F:Type} [zrb F]
private theorem cKy (H :z3y (Fin 4) F)
    (D:zM1 F) (s t:F) :
    zst (aeval (D9 D s t) H) =
      aeval (D9 D s t) (pderiv 0 H) +
        aeval (D9 D s t) (pderiv 1 H)*zst D:= by
  induction H using z5i with
  | C a=>simp [Polynomial.algebraMap_eq]
  | add P Q hP hQ =>
    simp only [map_add,hP,hQ]
    ring
  | mul_X P i hP =>
    simp only [map_mul,aeval_X,zAh,pderiv_mul,map_add,hP]
    fin_cases i <;> simp [D9] <;> ring
private theorem cSm (G:z3y (Fin 4) F)
   (D:zM1 F) (s t:F) (hroot :aeval (D9 D s t) G=0) :
   -aeval (D9 D s t) (pderiv 0 G) =
     aeval (D9 D s t) (pderiv 1 G)*zst D:= by
 have h:=cKy G D s t
 rw [hroot,Polynomial.derivative_zero] at h
 exact neg_eq_of_add_eq_zero_right h.symm
private theorem gtU (G:z3y (Fin 4) F)
    (D:zM1 F) (s t:F) (hroot :aeval (D9 D s t) G=0)
    (H :z3y (Fin 4) F) :
    aeval (D9 D s t) (implicitDeriv G H) =
      aeval (D9 D s t) (pderiv 1 G) *
        zst (aeval (D9 D s t) H) := by
  simp only [implicitDeriv,map_sub,map_mul]
  rw [cKy,sub_eq_add_neg,← neg_mul,cSm G D s t hroot]
  ring
private theorem dLN (A V:zM1 F) (m:ℕ) :
    A*(A*zst (A^(m+1)*V)) -
      z1z (↑(m+1) :F)*(A^(m+1)*V) *
        (A*zst A) =
      A^(m+1+2)*zst V:= by
  rw [zAh,Polynomial.derivative_pow_succ,
    pow_succ A (m+1+1),pow_succ A (m+1),pow_succ A m]
  simp only [Nat.cast_add,Nat.cast_one]
  ring
private theorem gtV (G:z3y (Fin 4) F)
    (D:zM1 F) (s t:F) (hroot :aeval (D9 D s t) G=0) (n:ℕ) :
    aeval (D9 D s t) (aN9 G n) =
      aeval (D9 D s t) (pderiv 1 G)^(2*n+1) *
        (zst^[n + 1]) D:= by
  induction n with
  | zero=>simpa [aN9] using cSm G D s t hroot
  | succ n ih =>
    have hm:2*(n+1)+1=2*n+1+2 := by omega
    simp only [aN9,map_sub,map_mul,aeval_C,zrE,
      gtU G D s t hroot,ih]
    rw [hm,zLk zst (n+1) D]
    exact dLN _ _ (2*n)
theorem proof :aiH.c2 := by
  intro F _ G w D s t hroot n hn hfactor
  cases n with
  | zero =>
    simp [aIS,aeval_X,D9,mul_comm]
  | succ n =>
    have hfactorial: (zst^[n + 1]) D =
        z1z (↑(n+1).factorial:F)*z75 (n+1) D:= by
      rw [← Polynomial.factorial_smul_hasseDeriv]
      rw [LinearMap.smul_apply,nsmul_eq_mul,Polynomial.C_eq_natCast]
    have hpad: (2*n+1)+(2*w - 1-(2*n+1))=2*w - 1 := by omega
    simp only [aIS,map_mul,map_pow,aeval_C,zrE,
      gtV G D s t hroot,hfactorial]
    set A:=aeval (D9 D s t) (pderiv 1 G)
    set f :F := ↑(n+1).factorial
    set H :=z75 (n+1) D
    have hcancel:z1z f⁻¹*z1z f=1 := by
      rw [← zPC,inv_mul_cancel₀ hfactor,Polynomial.C_1]
    calc
      _=(z1z f⁻¹*z1z f) *
          (A^(2*n+1)*A^(2*w - 1-(2*n+1)))*H := by ring
      _ = _:= by rw [hcancel,one_mul,← pow_add,hpad]
end cxM
end
section
namespace cxL
open wT aiH MvPolynomial
local notation "deg" => weightedTotalDegree LV
section DegreeBounds
variable {F:Type} [zrb F]
variable {P Q:z3y (Fin 4) F} {a b:ℕ}
private theorem degree_mul_le (hP:deg P≤a) (hQ:deg Q≤b) :
   deg (P*Q)≤a+b :=
 (weightedTotalDegree_mul_le LV P Q).trans (Nat.add_le_add hP hQ)
private theorem degree_sub_le (hP:deg P≤a) (hQ:deg Q≤a) :
  deg (P-Q)≤a := by
 rw [← mem_restrictWeightedDegree_iff_weightedTotalDegree_le] at hP hQ ⊢
 exact (restrictWeightedDegree (R:=F) LV a).sub_mem hP hQ
private theorem cJW (c:F) (P:z3y (Fin 4) F) :
  deg (C c*P)≤deg P:= by
 simpa only [weightedTotalDegree_C,zero_add] using
  weightedTotalDegree_mul_le LV (C c) P
private theorem cJ5 (hP:deg P≤a) :
   deg (pderiv 1 P)≤a - 1 :=
 (weightedTotalDegree_pderiv_le_sub LV 1 P).trans
   (zIu hP 1)
private theorem cUX {G H :z3y (Fin 4) F} {d m:ℕ}
   (hY:deg (pderiv 1 G)≤d) (hX:deg (pderiv 0 G)≤d+1)
   (hH :deg H≤ m) (hm:1≤ m) :
   deg (implicitDeriv G H)≤ m+d:= by
 unfold implicitDeriv
 apply degree_sub_le
 · have hx :=(weightedTotalDegree_pderiv_le LV 0 H).trans hH
   exact (degree_mul_le hY hx).trans_eq (zg2 d m)
 · exact (degree_mul_le hX (cJ5 hH)).trans (by omega)
private theorem enP {G:z3y (Fin 4) F} {d:ℕ}
   (hd:1≤d) (hY:deg (pderiv 1 G)≤d) (hX:deg (pderiv 0 G)≤d+1)
   (n:ℕ) :deg (aN9 G n)≤(2*n+1)*d+1 := by
 have hFlow:=cUX hY hX hY hd
 induction n with
 | zero =>
   simpa only [aN9,weightedTotalDegree,support_neg,mul_zero,zero_add,one_mul]
     using hX
 | succ n ih =>
   rw [aN9]
   apply degree_sub_le
   · have hN :=cUX hY hX ih (by omega)
     exact (degree_mul_le hY hN).trans_eq (by ring)
   · have hN :=(cJW (↑(2*n+1) :F) _).trans ih
     exact (degree_mul_le hN hFlow).trans_eq (by ring)
end DegreeBounds
theorem proof :aiH.c1 := by
  intro F _ G w E hE hG n hn
  let d:=E - 1
  have hd:1≤d:= by dsimp [d]; omega
  have hY:deg (pderiv 1 G)≤d:=cJ5 hG
  have hX:deg (pderiv 0 G)≤d+1 :=
    (weightedTotalDegree_pderiv_le LV 0 G).trans (by dsimp [d]; omega)
  have hPow (k :ℕ) :deg (pderiv 1 G^k)≤k*d :=
    (weightedTotalDegree_pow_le LV _ k).trans (zBI k hY)
  change deg (aIS G w n)≤(2*w - 1)*d+1
  cases n with
  | zero =>
    rw [aIS]
    have h₀:deg (z9v 1 :z3y (Fin 4) F)≤1 :=
      mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
        (X_mem_restrictWeightedDegree LV 1 1 (by rfl))
    exact (degree_mul_le h₀ (hPow _)).trans_eq (zg2 _ _)
  | succ n =>
    rw [aIS]
    have hN :=(cJW ((↑(zs5 (n+1)) :F)⁻¹) _).trans
      (enP hd hY hX n)
    apply (degree_mul_le hN (hPow _)).trans_eq
    have hpad:2*n+1≤2*w - 1 := by omega
    calc
      _=((2*n+1)+(2*w - 1-(2*n+1)))*d+1 := by ring
      _ = _:= by rw [zg2 (2*n+1),zxt hpad]
end cxL
end
section
set_option backward.isDefEq.respectTransparency false
namespace cxK
open Matrix MvPolynomial gR aiG
open scoped BigOperators
private theorem b2j {E row col:Type} [zrb E] [z85 row] [z85 col]
    (N :z30 row col E) :
    ∃ (rows :Fin N.rank→ row) (cols :Fin N.rank→ col),
      (N.submatrix rows cols).det≠0:= by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩:=exists_linearIndependent' E N.col
  let:Finite κ:=Finite.of_injective a ha
  let:z85 κ:=zQs κ
  have hc:Fintype.card κ=N.rank := by
    rw [← finrank_span_eq_card hli,hspan,Matrix.rank_eq_finrank_span_cols]
  let e :=(Fintype.equivFinOfCardEq hc).symm
  let cols :Fin N.rank→ col:=a ∘ e
  have hcols :LinearIndependent E (fun j:Fin N.rank=>N.col (cols j)) :=
    hli.comp e e.injective
  obtain ⟨rows,hpivot⟩:=aRz.bFA (N.submatrix id cols) (by
    intro v hv
    have hsum: (∑ j,v j•N.col (cols j))=0:= by
      funext i
      simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm,
        Matrix.col,Matrix.transpose_apply,Pi.zero_apply,Matrix.mulVec,dotProduct,z6T,
        id_eq] using congrFun hv i
    funext j
    exact Fintype.linearIndependent_iff.mp hcols v hsum j)
  exact ⟨rows,cols,hpivot⟩
private def Tr {R row col:Type} [Zero R] [One R] [DecidableEq row]
  (I:col→ row) :z30 row col R :=
 fun i j=>(Pi.single (I j) 1 :row→R) i
private theorem bx1 {R row col pick :Type}
  [za6 R] [z85 row] [DecidableEq row]
  (W:z30 row col R) (I:pick→ row) :
  W.transpose*Tr I=(W.submatrix I id).transpose := by
 ext i j
 change W.transpose.mulVec (Pi.single (I j) 1) i= _
 rw [Matrix.mulVec_single_one]
 rfl
private theorem duZ {R:Type} [za6 R] {r s :ℕ}
    (C:z30 (Fin r ⊕ Fin s) (Fin r) R)
    (W:z30 (Fin r ⊕ Fin s) (Fin s) R)
    (hWC:W.transpose*C=0)
    (pivot :Fin r→Fin r ⊕ Fin s) (I:Fin s→Fin r ⊕ Fin s) :
    (Matrix.fromRows (Tr pivot:z30 _ _ R).transpose W.transpose).det *
        (zE7 C (Tr I)).det =
      (C.submatrix pivot id).det*(W.submatrix I id).det:= by
  have htop: (Tr pivot:z30 _ _ R).transpose*C =
      C.submatrix pivot id := by
    have h:=congrArg Matrix.transpose (bx1 C pivot)
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using h
  rw [← Matrix.det_mul,Matrix.fromRows_mul_fromCols,htop,hWC,
    bx1 W I,Matrix.det_fromBlocks_zero₂₁,Matrix.det_transpose]
private theorem d5X {R ι:Type} [za6 R] [ztn R]
  [NormalizedGCDMonoid R] [z85 ι] (P A:ι→R) (t d:R)
  (ht:t≠0) (hprim:aG8 P)
  (hdet : ∀ I,t*A I=d*P I) :
  ∃ q:R,∀ I,A I=q*P I:= by
 let g:=Finset.univ.gcd P
 have hg:IsUnit g:=hprim g (fun I=>Finset.gcd_dvd (zTc I))
 have hd:t∣Finset.univ.gcd (fun I=>d*P I) :=
  Finset.dvd_gcd (fun I _=>⟨A I,(hdet I).symm⟩)
 have hgd:t∣d*g:=hd.trans (Finset.gcd_mul_left' zdB P d).dvd
 obtain ⟨q,hq⟩:t∣d:=hgd.trans (by
  simpa only [mul_one] using mul_dvd_mul (dvd_refl d) (isUnit_iff_dvd_one.mp hg))
 refine ⟨q,fun I=>mul_left_cancel₀ ht ?_⟩
 rw [hdet I,hq,mul_assoc]
private theorem du0 {F:Type} [zrb F] {r s :ℕ}
    (C:z30 (Fin r ⊕ Fin s) (Fin r) (aZ F))
    (block :Fin r ⊕ Fin s→Fin 2) (b i:Fin 2)
    (I:Fin s→Fin r ⊕ Fin s) (hI : ∀ j,block (I j)=b)
    (hC : ∀ u j,(C u j).degreeOf i≤ if block u=i then 1 else 0)
    (L:ℕ) (htotal: (∑ u,if block u=i then 1 else 0)=L) :
    (zE7 C (Tr I)).det.degreeOf i≤ if b=i then L - s else L:= by
  classical
  let A:=zE7 C (Tr I)
  let weight (u:Fin r ⊕ Fin s) :ℕ:=if block u=i then 1 else 0
  let saving:Fin r ⊕ Fin s→ℕ:=Sum.elim (fun _=>0) (fun _=>if b=i then 1 else 0)
  change A.det.degreeOf i≤_
  rw [Matrix.det_apply']
  apply (degreeOf_sum_le _ _ _).trans
  apply zf9
  intro σ _
  by_cases hz : (∏ j,A (σ j) j)=0
  · simp [hz]
  have hsign: ((↑↑(zjl σ) :aZ F)).degreeOf i=0:= by
    rw [← map_intCast (znf:F →+* aZ F),degreeOf_C]
  have hpoint (j:Fin r ⊕ Fin s) :
      (A (σ j) j).degreeOf i+saving j≤weight (σ j) := by
    cases j with
    | inl j=>simpa only [A,Matrix.fromCols_apply_inl,saving,Sum.elim_inl,add_zero]
        using hC (σ (Sum.inl j)) j
    | inr j =>
      have he :I j=σ (Sum.inr j) := by
        by_contra h
        apply hz
        apply zue (zTc (Sum.inr j))
        simp [A,Tr,h]
      simp [A,Tr,← he,weight,hI,saving]
  have hsum:=zQk (fun j (_:j∈zdB)=>hpoint j)
  have hsave : (∑ j,saving j)=if b=i then s else 0:= by
    by_cases h:b=i <;> simp [saving,Fintype.sum_sum_type,h]
  rw [Finset.sum_add_distrib,hsave,z5O σ weight,htotal] at hsum
  apply (degreeOf_mul_le _ _ _).trans
  rw [hsign,zero_add]
  apply (degreeOf_prod_le _ _ _).trans
  by_cases h:b=i
  · simp only [ite_eq_left h] at hsum ⊢
    omega
  · simpa only [ite_eq_right h,Nat.add_zero] using hsum
theorem proof :aiG.c2 := by
 intro F _ L w s M W _ _ hrank hWM hdegree hprim b i rows
 classical
 by_cases hzero :Mc.acq W (fun j=>(b,rows j))=0
 · simp [hzero]
 let φ:=algebraMap (aZ F) (CS F)
 let r :=(M.map φ).rank
 obtain ⟨pivot,cols,hpivot⟩:=b2j (M.map φ)
 let e : (Fin r ⊕ Fin s) ≃ Fin 2×Fin L :=
   Fintype.equivOfCardEq (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
     using hrank)
 let C:=M.submatrix e cols
 let V:=W.submatrix e id
 let p:Fin r→Fin r ⊕ Fin s :=e.symm ∘ pivot
 let I:Fin s→Fin r ⊕ Fin s := fun j=>e.symm (b,rows j)
 have hpmap : (C.submatrix p id).map φ=(M.map φ).submatrix pivot cols := by
   ext u j
   simp only [C,p,zAg,z6T,z3s,
     zIV,id_eq]
 have hp: (C.submatrix p id).det≠0:= by
   intro h
   apply hpivot
   rw [← hpmap,← zcW,← φ.map_det,h,map_zero]
 have hVC:V.transpose*C=0:= by
   apply Matrix.ext
   intro u j
   change (∑ t:Fin r ⊕ Fin s,W (e t) u*M (e t) (cols j))=0
   rw [z5O e (fun t=>W t u*M t (cols j))]
   exact congrFun (congrFun hWM u) (cols j)
 let P (J:Fin s→Fin r ⊕ Fin s) :=(V.submatrix J id).det
 let A (J:Fin s→Fin r ⊕ Fin s) :=(zE7 C (Tr J)).det
 let t:=(Matrix.fromRows (Tr p:z30 _ _ (aZ F)).transpose V.transpose).det
 have hminor (J:Fin s→Fin 2×Fin L) :
     P (e.symm ∘ J)=Mc.acq W J:= by
   change Mc.acq W (e ∘ (e.symm ∘ J))= _
   congr 1
   funext j
   exact e.apply_symm_apply (J j)
 have hP:P I≠0:= by
   change P (e.symm ∘ (fun j=>(b,rows j)))≠0
   rwa [hminor]
 have hdet (J:Fin s→Fin r ⊕ Fin s) :t*A J=(C.submatrix p id).det*P J :=
   duZ C V hVC p J
 have ht:t≠0:= by
   intro hz
   have he :=hdet I
   rw [hz,zero_mul] at he
   exact mul_ne_zero hp hP he.symm
 have hprimP:aG8 P:= by
   intro q hq
   apply hprim q
   intro J
   rw [← hminor J]
   exact hq _
 let:=UniqueFactorizationMonoid.strongNormalizationMonoid (α:=aZ F)
 let:=UniqueFactorizationMonoid.toNormalizedGCDMonoid (aZ F)
 obtain ⟨q,hq⟩:=d5X P A t _ ht hprimP hdet
 have hq0:q≠0:= by
   intro hz
   have he :=hdet I
   rw [hq I,hz,zero_mul,mul_zero] at he
   exact mul_ne_zero hp hP he.symm
 let block (u:Fin r ⊕ Fin s) :=(e u).1
 have hblock (j:Fin s) :block (I j)=b:= by
   simp only [block,I,zIV]
 have htotal: (∑ u,if block u=i then 1 else 0)=L:= by
   dsimp only [block]
   rw [z5O e (fun u:Fin 2×Fin L=>if u.1=i then (1 :ℕ) else 0)]
   rw [Fintype.sum_prod_type,Fin.sum_univ_two]
   fin_cases i <;> simp
 have hbound:=du0 C block b i I hblock (fun u j=>hdegree (e u) (cols j) i)
   L htotal
 change (A I).degreeOf i≤_ at hbound
 rw [hq I,degreeOf_mul_eq hq0 hP] at hbound
 rw [← hminor (fun j=>(b,rows j))]
 exact (Nat.le_add_left (degreeOf i (P I)) (degreeOf i q)).trans hbound
end cxK
end
section
set_option backward.isDefEq.respectTransparency false
namespace cxJ
noncomputable section
open Polynomial Matrix gR Mc aiG
private theorem bdA {A R:Type} [za6 A] [za6 R] [ztn R]
   (P:Fin 2→ A[X]) (h s :ℕ) (hdegree : ∀ b,(P b).natDegree≤h)
   (f :A→R) (hf :f 0=0) (b:Fin 2) (j:Fin (h+1))
   (hj:f ((P b).coeff j.val)≠0) :
   ∃ rows :Fin s→Fin (h+s),
     (((Sm P (h+s) s).submatrix (fun k=>(b,rows k)) id).map f).det≠0:= by
 classical
 let S:=(z4x (h+1)).filter (fun d=>f ((P b).coeff d)≠0)
 have hS:S.Nonempty :=⟨j.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt,hj⟩⟩
 let d:=S.max' hS
 have hd:d∈S:=S.max'_mem hS
 have hdle :d≤h:=zeh (Finset.mem_range.mp (Finset.mem_filter.mp hd).1)
 have hdne :f ((P b).coeff d)≠0:=(Finset.mem_filter.mp hd).2
 have hlarge (k :ℕ) (hk :d<k) :f ((P b).coeff k)=0:= by
   by_cases hkh:k<h+1
   · by_contra hne
     exact (not_le_of_gt hk) (S.le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkh,hne⟩))
   · have hk' : (P b).natDegree<k :=(hdegree b).trans_lt (by omega)
     rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk',hf]
 let rows (k :Fin s) :Fin (h+s) :=⟨d+k.val,by omega⟩
 let M:=((Sm P (h+s) s).submatrix (fun k=>(b,rows k)) id).map f
 have htri:M.IsUpperTriangular := by
   intro k l hkl
   change l.val<k.val at hkl
   change f ((P b*z7y ^l.val).coeff (d+k.val))=0
   rw [zBK,ite_eq_left (by omega)]
   exact hlarge _ (by omega)
 have hdiag (k :Fin s) :M k k=f ((P b).coeff d) := by
   change f ((P b*z7y ^k.val).coeff (d+k.val))= _
   rw [Polynomial.coeff_mul_X_pow]
 refine ⟨rows,?_⟩
 change M.det≠0
 rw [Matrix.det_of_isUpperTriangular htri]
 simp only [hdiag,Fin.prod_const]
 exact pow_ne_zero _ hdne
private theorem bKx {F:Type} [zrb F] {h:ℕ}
  (Q:Fin 2×Fin (h+1)→aZ F) (b:Fin 2) : (Gz Q b).natDegree≤h :=
 Principal.aCg _
private theorem bKw {F:Type} [zrb F] {h:ℕ}
  (Q:Fin 2×Fin (h+1)→aZ F) (b:Fin 2) (j:Fin (h+1)) :
  (Gz Q b).coeff j.val= Q (b,j) :=
 Principal.ahe _ _
private theorem ccG {F:Type} [zrb F] (h s :ℕ)
   (Q:Fin 2×Fin (h+1)→aZ F) (hQ:Q≠0) (hprim:aG8 Q) :
   aG8 (acq (Sm (Gz Q) (h+s) s)) := by
 classical
 intro q hq
 have hqne :q≠0:= by
   intro hz
   obtain ⟨⟨b,j⟩,hj⟩:=Function.ne_iff.mp hQ
   have hj' : id ((Gz Q b).coeff j.val)≠0:= by
     simpa only [id_eq,bKw,Pi.zero_apply] using hj
   obtain ⟨rows,hr⟩:=bdA (Gz Q) h s (bKx Q)
     id rfl b j hj'
   have he :=hq (fun k=>(b,rows k))
   rw [hz,zero_dvd_iff] at he
   apply hr
   change (((Sm (Gz Q) (h+s) s).submatrix (fun k=>(b,rows k)) id).map id).det=0
   rw [Matrix.map_id]
   exact he
 by_contra hqnu
 obtain ⟨p,hp,hpq⟩:=WfDvdMonoid.exists_irreducible_factor hqnu hqne
 let I:znc (aZ F) :=zye {p}
 let:I.IsPrime :=
   (Ideal.span_singleton_prime hp.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp)
 let φ:=zVv I
 have hsurvives : ∃ k,φ (Q k)≠0:= by
   by_contra! hall
   exact hp.not_isUnit (hprim p (fun k =>
     Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hall k))))
 obtain ⟨⟨b,j⟩,hj⟩:=hsurvives
 obtain ⟨rows,hr⟩:=bdA (Gz Q) h s (bKx Q)
   φ (map_zero φ) b j (by rwa [bKw])
 let M:=(Sm (Gz Q) (h+s) s).submatrix (fun k=>(b,rows k)) id
 have hz :φ M.det=0:=Ideal.Quotient.eq_zero_iff_mem.mpr
   (Ideal.mem_span_singleton.mpr (hpq.trans (hq (fun k=>(b,rows k)))))
 rw [φ.map_det,zcW] at hz
 exact hr hz
private theorem bXH {R:Type} [za6 R] {s :ℕ}
   (M:z30 (Fin s) (Fin s) R[X]) (H :ℕ) (hdegree : ∀ k l,(M k l).natDegree≤H) :
   M.det.coeff (s*H)=(M.map (fun q=>q.coeff H)).det:= by
 classical
 rw [zwK,zwK,Polynomial.finsetSum_coeff]
 apply zUo rfl
 intro σ _
 rw [Polynomial.coeff_smul]
 congr 1
 simpa only [Finset.card_univ,zgY,zAg] using
   Polynomial.coeff_prod_of_natDegree_le (zdB :zJe (Fin s))
     (fun k=>M (σ k) k) H (fun k _=>hdegree (σ k) k)
private theorem eEp {R:Type} [za6 R] {s :ℕ}
   (M:z30 (Fin s) (Fin s) R[X]) (H :ℕ) (hdegree : ∀ k l,(M k l).natDegree≤H) :
   M.det.natDegree≤ s*H := by
 classical
 rw [zwK]
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro σ _
 have hprod: (∏ k,M (σ k) k).natDegree≤ s*H := by
   calc
     _ ≤ ∑ k,(M (σ k) k).natDegree :=Polynomial.natDegree_prod_le _ _
     _ ≤ ∑ _:Fin s,H :=zQk (fun k _=>hdegree (σ k) k)
     _ = _:= by simp
 rcases znm (zjl σ) with hsign | hsign
 · simpa only [hsign,one_smul] using hprod
 · simpa only [hsign,Units.neg_smul,one_smul,Polynomial.natDegree_neg] using hprod
set_option maxHeartbeats 600000 in
private theorem gqi {F:Type} [zrb F] (h s :ℕ)
    (Q:Fin 2×Fin (h+1)→aZ F) (b i:Fin 2) (hpos :0<Kn Q b i) :
    ∃ rows :Fin s→Fin (h+s),
      (acq (Sm (Gz Q) (h+s) s) (fun k=>(b,rows k))).degreeOf i =
        s*Kn Q b i:= by
  classical
  let R:=z3y {j:Fin 2 // j≠i} F
  let φ:aZ F →+* R[X] :=
    ((MvPolynomial.renameEquiv F (Equiv.optionSubtypeNe i).symm).trans
      (MvPolynomial.optionEquivLeft F {j:Fin 2 // j≠i})).toRingHom
  have hφ (q:aZ F) : (φ q).natDegree=q.degreeOf i :=
    (MvPolynomial.degreeOf_eq_natDegree i q).symm
  let H :=Kn Q b i
  obtain ⟨j,_,hj⟩:=Finset.exists_mem_eq_sup (zdB :zJe (Fin (h+1)))
    Finset.univ_nonempty (fun k=>(Q (b,k)).degreeOf i)
  have hj' : (φ (Q (b,j))).natDegree=H :=(hφ _).trans hj.symm
  have htop: (φ ((Gz Q b).coeff j.val)).coeff H≠0:= by
    rw [bKw,← hj',Polynomial.coeff_natDegree]
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro hz
    rw [hz,zbf] at hj'
    exact (Nat.ne_of_gt hpos) hj'.symm
  obtain ⟨rows,hr⟩:=bdA (Gz Q) h s (bKx Q)
    (fun q=>(φ q).coeff H) (by rw [map_zero,Polynomial.coeff_zero]) b j htop
  let A:=(Sm (Gz Q) (h+s) s).submatrix (fun k=>(b,rows k)) id
  let M:=A.map φ
  have hcoeff (k :ℕ) : (φ ((Gz Q b).coeff k)).natDegree≤H := by
    by_cases hk :k<h+1
    · let j' : Fin (h+1) :=⟨k,hk⟩
      change (φ ((Gz Q b).coeff j'.val)).natDegree≤H
      rw [bKw,hφ]
      exact bD0 Q b i j'
    · have hk' : (Gz Q b).natDegree<k :=(bKx Q b).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk',map_zero,Polynomial.natDegree_zero]
      exact Nat.zero_le H
  have hM (k l:Fin s) : (M k l).natDegree≤H := by
    simp only [M,A,zAg,z6T,Mc.Sm,id_eq]
    rw [zBK]
    split_ifs
    · exact hcoeff _
    · rw [map_zero,zbf]
      exact zD0 H
  have htopDet:M.det.coeff (s*H)≠0:= by
    rw [bXH M H hM]
    exact hr
  refine ⟨rows,?_⟩
  change A.det.degreeOf i=s*H
  have hdet:φ A.det=M.det:=φ.map_det A
  rw [← hφ,hdet]
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (eEp M H hM) htopDet
theorem proof :aiG.c1 := by
 intro F inst h L s Q hL _ hQ hprim
 subst L
 exact ⟨ccG h s Q hQ hprim,gqi h s Q⟩
end
end cxJ
end
section
namespace cyy
noncomputable section
open rW NS MvPolynomial Filter
variable {k σ:Type*} [zrb k]
private theorem b54 (I:znc (z3y σ k)) (i:σ)
   (N :ℕ) {p:z3y σ k} (hp:p.totalDegree≤N) :
   ∃ q:z3y σ k,q.IsHomogeneous N ∧
     zVv (KL I i) q=zVv (KL I i) p:= by
 classical
 let J:=KL I i
 have hi:zVv J (z9v i)=1 := by
   apply sub_eq_zero.mp
   rw [← (zVv J).map_one,← map_sub,Ideal.Quotient.eq_zero_iff_mem]
   exact (le_sup_right:zye {z9v i - 1} ≤ J)
     (zCn (Set.mem_singleton _))
 refine ⟨∑ d∈z4x (p.totalDegree+1),
   z9v i^(N - d)*homogeneousComponent d p,IsHomogeneous.sum _ _ _ ?_,?_⟩
 · intro d hd
   have hdN :d≤N :=(zeh (Finset.mem_range.mp hd)).trans hp
   have hform :=(isHomogeneous_X_pow (R:=k) i (N - d)).mul
     (homogeneousComponent_isHomogeneous d p)
   simpa only [zxt hdN] using hform
 · change zVv J _=zVv J p
   rw [map_sum]
   simp only [map_mul,map_pow,hi,one_pow,one_mul]
   rw [← map_sum,sum_homogeneousComponent]
private theorem dIB [Finite σ] (I:znc (z3y σ k)) (i:σ)
   (N :ℕ) (hN :0<N) :
   affineHilbertFunction (KL I i) N+affineHilbertFunction I (N - 1) ≤
     affineHilbertFunction I N := by
 let J:=KL I i
 let V:=restrictTotalDegree σ k N
 let proj:V →ₗ[k] quotientDegreeLE I N :=
   ((zvR k I).toLinearMap.domRestrict V).codRestrict _ fun p ↦
     mk_mem_quotientDegreeLE ((mem_restrictTotalDegree σ N p.val).mp p.property)
 have hproj:zpX proj:= by
   intro z
   obtain ⟨p,hp,hz⟩:=mem_quotientDegreeLE.mp z.property
   exact ⟨⟨p,(mem_restrictTotalDegree σ N p).mpr hp⟩,Subtype.ext hz⟩
 let top:V →ₗ[k] quotientDegreeLE J N :=
   (((zvR k J).toLinearMap.comp (homogeneousComponent N)).domRestrict V).codRestrict _
     fun p ↦ mk_mem_quotientDegreeLE (homogeneousComponent_isHomogeneous N p.val).totalDegree_le
 have hker :z83 proj≤z83 top:= by
   intro p hp
   rw [zeS] at hp ⊢
   have hpI:p.val∈I:=Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hp)
   apply Subtype.ext
   change zVv J (homogeneousComponent N p.val)=0
   apply Ideal.Quotient.eq_zero_iff_mem.mpr
   exact (le_sup_left:lW I≤J) (zCn
     ⟨p.val,N,hpI,(mem_restrictTotalDegree σ N p.val).mp p.property,rfl⟩)
 let cut:quotientDegreeLE I N →ₗ[k] quotientDegreeLE J N :=
   ((z83 proj).liftQ top hker).comp
     (proj.quotKerEquivOfSurjective hproj).symm.toLinearMap
 have hcut (p:V) :cut (proj p)=top p:= by
   change (z83 proj).liftQ top hker
     ((proj.quotKerEquivOfSurjective hproj).symm (proj p))= _
   rw [LinearMap.quotKerEquivOfSurjective_symm_apply,Submodule.liftQ_apply]
 have hsurj:zpX cut:= by
   intro z
   obtain ⟨p,hp,hz⟩:=mem_quotientDegreeLE.mp z.property
   obtain ⟨q,hform,hq⟩:=b54 I i N hp
   let v :V:=⟨q,(mem_restrictTotalDegree σ N q).mpr hform.totalDegree_le⟩
   refine ⟨proj v,?_⟩
   rw [hcut]
   apply Subtype.ext
   change zVv J (homogeneousComponent N q)=z.val
   rw [homogeneousComponent_eq_self hform]
   exact hq.trans hz
 let incl:=Submodule.inclusion (quotientDegreeLE_mono I (Nat.sub_le N 1))
 have hincl (z :quotientDegreeLE I (N - 1)) :incl z∈z83 cut:= by
   obtain ⟨p,hp,hz⟩:=mem_quotientDegreeLE.mp z.property
   have hlt:p.totalDegree<N :=lt_of_le_of_lt hp (by omega)
   let v :V:=⟨p,(mem_restrictTotalDegree σ N p).mpr hlt.le⟩
   have he :incl z=proj v :=Subtype.ext hz.symm
   rw [he,zeS,hcut]
   apply Subtype.ext
   change zVv J (homogeneousComponent N p)=0
   rw [homogeneousComponent_eq_zero N p hlt,map_zero]
 have hinj:zq4 (incl.codRestrict (z83 cut) hincl) := by
   intro x y hxy
   exact Subtype.ext (congrArg (fun z ↦ z.val.val) hxy)
 have hle :=LinearMap.finrank_le_finrank_of_injective hinj
 have hdim:=cut.finrank_range_add_finrank_ker
 rw [LinearMap.range_eq_top.mpr hsurj,finrank_top] at hdim
 change affineHilbertFunction J N+affineHilbertFunction I (N - 1)≤_
 unfold affineHilbertFunction
 omega
private theorem aTz [Finite σ] (I:znc (z3y σ k)) (i:σ)
    (hI:dimension I=1) :dimension (KL I i)=0:= by
  let J:=KL I i
  obtain ⟨M,hM⟩:=exists_eval_affineHilbertPolynomial I
  have hbound : ∀ᶠ N :ℕ in atTop,
      (affineHilbertPolynomial J).eval (N :ℚ) ≤
        (Polynomial.backwardDifference 1 (affineHilbertPolynomial I)).eval (N :ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial J,eventually_ge_atTop (M+1)]
      with N hJ hN
    have hpos :0<N := by omega
    have hprev :M≤N - 1 := by omega
    have hcast: ((N - 1 :ℕ) :ℚ)=(N :ℚ) - 1 := by
      rw [Nat.cast_sub (show 1≤N by omega),Nat.cast_one]
    rw [Polynomial.eval_backwardDifference,← hcast,hM N (by omega),hM (N - 1) hprev,hJ]
    apply le_sub_iff_add_le.mpr
    exact_mod_cast dIB I i N hpos
  have h:=(Polynomial.natDegree_le_and_coeff_le_of_eventually_eval_natCast_le_backwardDifference
    (eventually_eval_affineHilbertPolynomial_nonneg J) hbound).1
  change dimension J≤dimension I - 1 at h
  rw [hI] at h
  exact za7 h
theorem proof :NS.c2 := by
 intro A _ hA i
 exact aTz A i hA
end
end cyy
end
section
namespace bzu
noncomputable section
open yz axb
open scoped BigOperators
def ark {α:Type} (v :α→iz) (S:zJe α) :Set iz :=
 convexHull ℝ (v '' (S:Set α))
theorem cEx {α:Type} (v :α→iz) {S:zJe α}
   (hS:S.Nonempty) :JG v S∈ark v S:= by
 have hcard: (S.card:ℝ)≠0:= by exact_mod_cast hS.card_pos.ne'
 unfold JG ark
 rw [Finset.smul_sum]
 apply (convex_convexHull ℝ _).sum_mem (fun _ _=>inv_nonneg.mpr (Nat.cast_nonneg _))
 · simp [nsmul_eq_mul,hcard]
 · intro a ha
   exact subset_convexHull ℝ _ (zVS v ha)
private theorem cKP {α:Type} {v :α→iz} {S:zJe α}
  {g:iz →ₗ[ℝ] ℝ} {a :α} (ha :a∈S)
  (hc : ∀ b∈S,g (v b)=g (v a)) :
  vectorSpan ℝ (v '' (S:Set α))≤z83 g:= by
 rw [vectorSpan_eq_span_vsub_set_right ℝ (zVS v ha),Submodule.span_le]
 rintro _ ⟨_,⟨b,hb,rfl⟩,rfl⟩
 simp [vsub_eq_sub,map_sub,hc b hb]
private theorem cNQ {α:Type} {v :α→iz} {S:zJe α}
  {g:iz →ₗ[ℝ] ℝ} (hg:aRv v S g) {a b:α}
  (ha :a∈S) (hb:b∉S) :g (v b)<g (v a) := by
 refine lt_of_le_of_ne ((hg a).1 ha b) (fun he=>hb ((hg b).2 (fun c => ?_)))
 rw [he]
 exact (hg a).1 ha c
theorem d5J {α:Type} {v :α→iz} {S T:zJe α}
  (hT:agG v T) (hTS:T<S) :
  vectorSpan ℝ (v '' (T:Set α))<vectorSpan ℝ (v '' (S:Set α)) := by
 obtain ⟨⟨a,ha⟩,g,hg⟩:=hT
 obtain ⟨b,hb,hbT⟩:=Finset.not_subset.mp (not_le_of_gt hTS)
 have hker :=cKP ha (g:=g)
  (fun c hc=>le_antisymm ((hg a).1 ha c) ((hg c).1 hc a))
 have hle :=vectorSpan_mono ℝ (Set.image_mono (f :=v) (show (T:Set α)⊆S from hTS.le))
 refine lt_of_le_not_ge hle (fun h => ?_)
 have hmem:v b - v a∈vectorSpan ℝ (v '' (S:Set α)) :=
  vsub_mem_vectorSpan ℝ (zVS v hb) (zVS v (hTS.le ha))
 have heq :=LinearMap.mem_ker.mp (hker (h hmem))
 rw [map_sub] at heq
 exact (cNQ hg ha hbT).ne (sub_eq_zero.mp heq)
private theorem d32 {E :Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
   {H :Set E} (hH :IsCompact H) {c x :E} (hx :x∈H) (hne :x≠c) :
   ∃ y∈H,y∉interior H∧Wbtw ℝ c x y := by
 obtain ⟨R,hR⟩:=(hH.image (continuous_id.sub continuous_const:Continuous (fun z :E=>z - c))).isBounded.exists_norm_le
 have hn:0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
 let t:=max 1 (R / ‖x - c‖ + 1)
 have ht:1≤t:=le_max_left _ _
 let p:=t•(x - c)+c
 have hp:p∉H := by
   intro hpH
   have hnorm:=hR (p - c) (zVS (fun z=>z - c) hpH)
   have hlt:R / ‖x - c‖ < t :=
     lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) (le_max_right _ _)
   have hmul :=(div_lt_iff₀ hn).mp hlt
   exact (not_le_of_gt hmul) (by
     simpa [p,norm_smul,Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans ht)] using hnorm)
 have hcx :Wbtw ℝ c x p:= by
   simpa [p,vadd_eq_add] using
     (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le c (x - c) zero_le_one ht)
 obtain ⟨y,hy,hpyx,hv⟩:=hH.isClosed.exists_wbtw_isVisible hx p
 refine ⟨y,hy,fun hyi=>hp ((hv.eq_of_mem_interior hyi).symm ▸ hy),?_⟩
 exact hcx.trans_right_left hpyx.symm
private theorem fV5 {α:Type} {v :α→iz} {S:zJe α}
   (hS:S.Nonempty) {x :iz} (hx :x∈ark v S) (hne :x≠JG v S) :
   ∃ (y :iz) (g:iz →ₗ[ℝ] ℝ),
     y∈ark v S∧Wbtw ℝ (JG v S) x y ∧
     (∀ a∈S,g (v a)≤g y) ∧ ∃ a∈S,g (v a)<g y := by
 let H :=ark v S
 let A:=affineSpan ℝ H
 let xA:A:=⟨x,subset_affineSpan ℝ H hx⟩
 let:Nonempty A:=⟨xA⟩
 let e :A.direction ≃ᵃ[ℝ] A:=AffineEquiv.vaddConst ℝ xA
 let u:A.direction →ᵃ[ℝ] iz :=A.subtype.comp e.toAffineMap
 let C:=u ⁻¹' H
 have hu (z :A.direction) :u z=(z :iz) + x :=rfl
 have hcv :Convex ℝ C:=(convex_convexHull ℝ _).affine_preimage u
 have hspan:affineSpan ℝ C = ⊤ := by
   let:Nonempty H :=⟨⟨x,hx⟩⟩
   change affineSpan ℝ (e ⁻¹' (((↑) :A→iz) ⁻¹' H)) = ⊤
   rw [← AffineSubspace.comap_span,affineSpan_coe_preimage_eq_top,AffineSubspace.comap_top]
 have hcompactH :IsCompact H :=(S.finite_toSet.image v).isCompact_convexHull ℝ
 have hclosed:IsClosed C:=hcompactH.isClosed.preimage u.continuous_of_finiteDimensional
 have hbounded:Bornology.IsBounded C:= by
   obtain ⟨R,hR⟩:=(hcompactH.image
     (continuous_id.sub continuous_const:Continuous (fun z :iz=>z - x))).isBounded.exists_norm_le
   apply (isBounded_iff_forall_norm_le).2
   refine ⟨R,fun z hz => ?_⟩
   have hz' := hR (u z - x)
     (zVS (fun p=>p - x) (show u z∈H from hz))
   simpa only [hu,add_sub_cancel_right,Submodule.norm_coe] using hz'
 have hcompact :IsCompact C:=Metric.isCompact_of_isClosed_isBounded hclosed hbounded
 have hc:=cEx v hS
 let cA:A:=⟨JG v S,subset_affineSpan ℝ H hc⟩
 have hxc:e.symm xA∈C:= by change (e (e.symm xA) :iz)∈H; simpa using hx
 have hcc:e.symm cA∈C:= by change (e (e.symm cA) :iz)∈H; simpa using hc
 have hne' : e.symm xA≠e.symm cA:= by
   intro he
   exact hne (congrArg Subtype.val (e.symm.injective he))
 obtain ⟨z,hz,hzi,hbtw⟩:=d32 hcompact (c:=e.symm cA) hxc hne'
 obtain ⟨f,hf,hmax⟩:=geometric_hahn_banach_of_nonempty_interior_point hcv hzi
   (hcv.interior_nonempty_iff_affineSpan_eq_top.mpr hspan)
 obtain ⟨g,hg⟩:=f.toLinearMap.exists_extend
 have hg' (z' : A.direction) :g (u z')=f z' + g x := by
   rw [hu,map_add]
   exact congrArg (· + g x) (z5U hg z')
 have hmap (p:A) :u (e.symm p)=(p:iz) := by
   change (e (e.symm p) :iz)= _
   rw [e.apply_symm_apply]
 let y :=u z
 have haH (a :α) (ha :a∈S) :v a∈H :=
   subset_convexHull ℝ _ (zVS v ha)
 have hle (a :α) (ha :a∈S) :g (v a)≤g y := by
   let aA:A:=⟨v a,subset_affineSpan ℝ H (haH a ha)⟩
   have haC:e.symm aA∈C:= by
     change u (e.symm aA)∈H
     rw [hmap]
     exact haH a ha
   have he :=add_le_add (hmax _ haC) (le_refl (g x))
   rw [← hg' (e.symm aA),← hg' z,hmap] at he
   exact he
 refine ⟨y,g,hz,by simpa only [hmap] using hbtw.map u,hle,?_⟩
 by_contra! hn
 obtain ⟨a,ha⟩:=hS
 have hker :=cKP ha (g:=g) (fun b hb =>
   (le_antisymm (hle b hb) (hn b hb)).trans (le_antisymm (hle a ha) (hn a ha)).symm)
 apply hf
 ext q
 have hq: (q:iz)∈vectorSpan ℝ (v '' (S:Set α)) := by
   have hm: (q:iz)∈(affineSpan ℝ (convexHull ℝ (v '' (S:Set α)))).direction :=
     q.property
   simpa only [affineSpan_convexHull,direction_affineSpan] using hm
 have hqg:=LinearMap.mem_ker.mp (hker hq)
 simpa using (z5U hg q).symm.trans hqg
private theorem ez9 {α:Type} {v :α→iz} {S:zJe α}
   {y :iz} (hy :y∈ark v S) {g:iz →ₗ[ℝ] ℝ}
   (hle : ∀ a∈S,g (v a)≤g y) [DecidablePred (fun a=>g (v a)=g y)] :
   y∈ark v (S.filter (fun a=>g (v a)=g y)) := by
 classical
 obtain ⟨ι,_,w,p,hw,hsum,hp,hcomb⟩:=mem_convexHull_iff_exists_fintype.mp hy
 have hle' (i:ι) :g (p i)≤g y := by
   obtain ⟨a,ha,he⟩:=hp i
   rw [← he]
   exact hle a ha
 have he0 : ∑ i,w i*(g y - g (p i))=0:= by
   have he :=congrArg g hcomb
   simp only [map_sum,map_smul,smul_eq_mul] at he
   simp only [mul_sub,zQq,← zkq,he,hsum,one_mul,sub_self]
 let I:=Finset.univ.filter (fun i=>w i≠0)
 have hcomb' : (∑ i∈I,w i•p i)=y := by
   rw [← hcomb]
   apply Finset.sum_subset (ziq _)
   intro i _ hi
   have hwi:w i=0:= by simpa [I] using hi
   simp [hwi]
 refine (congrArg (fun q=>q∈ark v (S.filter (fun a=>g (v a)=g y))) hcomb').mp ?_
 refine (convex_convexHull ℝ _).sum_mem (fun i _=>hw i) ?_ ?_
 · dsimp only [I]
   rw [Finset.sum_filter_ne_zero]
   exact hsum
 · intro i hi
   have hwi:=(Finset.mem_filter.mp hi).2
   have his :=(Finset.sum_eq_zero_iff_of_nonneg
     (fun j _=>mul_nonneg (hw j) (sub_nonneg.mpr (hle' j)))).mp he0 i (zTc _)
   have heq :=(sub_eq_zero.mp ((mul_eq_zero.mp his).resolve_left hwi)).symm
   obtain ⟨a,ha,hea⟩:=hp i
   exact subset_convexHull ℝ _ ⟨a,Finset.mem_filter.mpr ⟨ha,by rwa [hea]⟩,hea⟩
private theorem ePt {α:Type} [z85 α]
   {v :α→iz} {S T:zJe α} (hS:agG v S) (hT:T.Nonempty)
   {g:iz →ₗ[ℝ] ℝ} {m:ℝ}
   (hTmem : ∀ b,b∈T↔b∈S∧g (v b)=m)
   (hle : ∀ b∈S,g (v b)≤ m) :agG v T:= by
 classical
 obtain ⟨a,ha⟩:=hT
 obtain ⟨haS,hag⟩:=(hTmem a).mp ha
 obtain ⟨f,hf⟩:=hS.2
 let r (b:α) :=(g (v b) - m)/(f (v a) - f (v b))
 obtain ⟨b₀,-,hmax⟩:=z6Q zdB r ⟨a,zTc _⟩
 let M:=r b₀+1
 let G:=M•f+g
 have hG (b:α) :G (v b)=M*f (v b)+g (v b) :=rfl
 have hinside (b:α) (hb:b∈S) :f (v b)=f (v a) :=
   le_antisymm ((hf a).1 haS b) ((hf b).1 hb a)
 have hout (b:α) (hb:b∉S) :G (v b)<G (v a) := by
   have hden:=sub_pos.mpr (cNQ hf haS hb)
   have hr :r b<M:=(hmax b (zTc _)).trans_lt (lt_add_of_pos_right _ zero_lt_one)
   have h:=(div_lt_iff₀ hden).mp hr
   rw [hG,hG,hag]
   rw [mul_sub] at h
   linarith
 have hmaxG (b:α) :G (v b)≤G (v a) := by
   by_cases hb:b∈S
   · simp only [hG,hinside b hb,hag,add_le_add_iff_left]
     exact hle b hb
   · exact (hout b hb).le
 refine ⟨⟨a,ha⟩,G,fun b => ?_⟩
 rw [hTmem]
 constructor
 · rintro ⟨hb,hbg⟩ c
   have he :G (v b)=G (v a) := by rw [hG,hG,hinside b hb,hbg,hag]
   exact (hmaxG c).trans_eq he.symm
 · intro hb
   have hbS:b∈S:= by
     by_contra hn
     exact (hout b hn).not_ge (hb a)
   refine ⟨hbS,le_antisymm (hle b hbS) ?_⟩
   have h:=hb a
   simpa only [hG,hinside b hbS,hag,add_le_add_iff_left] using h
theorem dOT {α:Type} [z85 α] {v :α→iz}
   {S:zJe α} (hS:agG v S) {x :iz} (hx :x∈ark v S)
   (hne :x≠JG v S) :
   ∃ (T:zJe α) (y :iz),T<S∧agG v T ∧
     y∈ark v T∧Wbtw ℝ (JG v S) x y := by
 classical
 obtain ⟨y,g,hy,hbtw,hle,a,ha,halt⟩:=fV5 hS.1 hx hne
 let T:=S.filter (fun b=>g (v b)=g y)
 have hyT:y∈ark v T:=ez9 hy hle
 obtain ⟨_,b,hb,_⟩:=convexHull_nonempty_iff.mp ⟨y,hyT⟩
 have hTmem (b:α) :b∈T↔b∈S∧g (v b)=g y :=zO0
 have hlt:T<S :=
   lt_of_le_not_ge (zT0 _ _) (fun h=>halt.ne ((hTmem a).mp (h ha)).2)
 exact ⟨T,y,hlt,ePt hS ⟨b,hb⟩ hTmem hle,hyT,hbtw⟩
end
end bzu
end
section
namespace bzu
noncomputable section
open yz axb
open MeasureTheory
private def bcl {α:Type} {n:ℕ} (v :α→iz)
  (F:Fin (n+1)→zJe α) :Set iz :=
 convexHull ℝ (zxp (fun j=>JG v (F j)))
private theorem dRb {α:Type} [z85 α] (v :α→iz)
    (k :ℕ) (S:zJe α) (x :iz) (hk :S.card=k)
    (hS:agG v S) (hx :x∈ark v S) :
    ∃ (n:ℕ) (F:Fin (n+1)→zJe α),
      n≤zsE ℝ (vectorSpan ℝ (v '' (S:Set α))) ∧
      StrictMono F∧(∀ j,agG v (F j))∧F (zym n)=S ∧
      x∈bcl v F:= by
  induction k using Nat.strong_induction_on generalizing S x with
  | h k ih =>
    by_cases he :x=JG v S
    · refine ⟨0,fun _=>S,zD0 _,?_,fun _=>hS,rfl,?_⟩
      · intro i j hij
        exfalso
        omega
      · exact subset_convexHull ℝ _ ⟨0,he.symm⟩
    obtain ⟨T,y,hTS,hT,hy,hbtw⟩:=dOT hS hx he
    have hc:T.card<k :=hk ▸ Finset.card_lt_card hTS
    obtain ⟨n,F,hn,hmono,hface,hlast,hyF⟩:=ih T.card hc T y rfl hT hy
    have hd:=Submodule.finrank_lt_finrank_of_lt (d5J hT hTS)
    let G:Fin (n+1+1)→zJe α:=Fin.snoc F S
    have hG (j:Fin (n+1)) :G j.castSucc=F j:= by simp [G]
    have hlastG:G (zym (n+1))=S:= by simp [G]
    refine ⟨n+1,G,Nat.succ_le_of_lt (hn.trans_lt hd),?_,?_,hlastG,?_⟩
    · refine Fin.strictMono_iff_lt_succ.mpr (fun i => ?_)
      refine zsB ?_ (fun j => ?_) i
      · rw [hG,Fin.succ_last,hlastG,hlast]
        exact hTS
      · rw [hG,← Fin.castSucc_succ,hG]
        exact hmono j.castSucc_lt_succ
    · intro j
      refine zsB ?_ (fun j' => ?_) j
      · rw [hlastG]
        exact hS
      · rw [hG]
        exact hface j'
    · have hcy :JG v S∈bcl v G :=
        subset_convexHull ℝ _ ⟨zym (n+1),congrArg (JG v) hlastG⟩
      have hsub:bcl v F⊆bcl v G:= by
        apply convexHull_mono
        rintro _ ⟨i,rfl⟩
        exact ⟨i.castSucc,congrArg (JG v) (hG i)⟩
      exact (convex_convexHull ℝ _).mem_of_wbtw hbtw hcy (hsub hyF)
private theorem ec3 {α:Type} [z85 α] (v :α→iz)
  {F:Fin 5→zJe α} (hF:F∈flags v) :
  aoa v F⊆convexHull ℝ (zxp v) := by
 apply convexHull_min _ (convex_convexHull ℝ _)
 rintro _ ⟨j,rfl⟩
 have hj:=cEx v (((bsB v F).mp hF).2 j).1
 apply convexHull_mono _ hj
 rintro _ ⟨a,_,rfl⟩
 exact Set.mem_range_self a
private theorem gqQ {α:Type} (v :α→iz) (n:Fin 4)
   (F:Fin (n.val+1)→zJe α) :volume (bcl v F)=0:= by
 let p (i:Fin (n.val+1)) :=JG v (F i)
 have hdim:=finrank_vectorSpan_range_le ℝ p (n:=n.val) (zgY _)
 have hproper :affineSpan ℝ (zxp p) ≠ ⊤ := by
   intro he
   rw [← direction_affineSpan,he,AffineSubspace.direction_top,finrank_top,
     z4H] at hdim
   exact (not_le_of_gt n.isLt) hdim
 exact measure_mono_null (convexHull_min (subset_affineSpan ℝ _) (affineSpan ℝ _).convex)
   (Measure.addHaar_affineSubspace volume _ hproper)
theorem proof :axb.c1 := by
 classical
 intro α _ v
 let H :=convexHull ℝ (zxp v)
 let U := ⋃ F∈flags v,aoa v F
 let N := ⋃ (n:Fin 4) (F:Fin (n.val+1)→zJe α),bcl v F
 have hN :volume N=0 :=
   measure_iUnion_null fun n=>measure_iUnion_null fun F=>gqQ v n F
 have hUH :U⊆H := by
   refine Set.iUnion₂_subset fun F hF => ?_
   exact ec3 v hF
 have hHU:H \ U⊆N := by
   rintro x ⟨hx,hxU⟩
   have hlabels :v '' ((zdB :zJe α) :Set α)=zxp v := by simp
   have hx' : x∈ark v Finset.univ := by simpa only [ark,hlabels] using hx
   have hne : (zdB :zJe α).Nonempty := by
     obtain ⟨_,a,ha,_⟩:=convexHull_nonempty_iff.mp ⟨x,hx'⟩
     exact ⟨a,ha⟩
   have hface :agG v Finset.univ :=⟨hne,0,by intro a; simp⟩
   obtain ⟨n,F,hn,hmono,hf,_,hxF⟩ :=
     dRb v _ zdB x rfl hface hx'
   have hd:n≤4 :=hn.trans (Submodule.finrank_le _ |>.trans_eq (z4H ℝ))
   by_cases hshort:n<4
   · exact Set.mem_iUnion.2 ⟨⟨n,hshort⟩,Set.mem_iUnion.2 ⟨F,hxF⟩⟩
   · have he :n=4 :=le_antisymm hd (Nat.le_of_not_lt hshort)
     subst n
     exact (hxU (Set.mem_iUnion₂.2 ⟨F,(bsB v F).2 ⟨hmono,hf⟩,hxF⟩)).elim
 have hle :H ≤ᵐ[volume] U:=ae_le_set.mpr (measure_mono_null hHU hN)
 have hge :U ≤ᵐ[volume] H :=Filter.Eventually.of_forall fun _ hx=>hUH hx
 exact hle.antisymm hge
end
end bzu
end
section
namespace cyR
noncomputable section
open zP aaq aA9 MvPolynomial
open as3 hiding ke
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {A:Fin 4→zJe Exponent}
private theorem dId (a :Chart A) (m:ℕ) :
  GW A a^m∈Kx A (fun _=>m) := by
 classical
 have hsum: (∑ j:Fin 4,(Pi.single j 1 :Degree))=(fun _=>1) := by
  funext j
  simp [Finset.sum_apply,Pi.single_apply]
 have hpow:m•(fun _:Fin 4=>(1 :ℕ))=(fun _=>m) := by
  funext j
  change m•(1 :ℕ)=m
  simp
 have hchart:=IsWeightedHomogeneous.prod (w:=jT A) zdB
  (fun j:Fin 4=>(z9v ⟨j,a j⟩:vJ A))
  (fun j=>Pi.single j 1)
  (fun j _=>isWeightedHomogeneous_X (fZ A) (jT A) (⟨j,a j⟩:Slot A))
 rw [hsum] at hchart
 rw [← hpow]
 exact hchart.pow m
private theorem dVK (a :Chart A) (m:ℕ) :
  ew A (GW A a^m)=a2m a m:= by
 classical
 rw [map_pow,GW,map_prod]
 simp only [ew,aeval_X]
 rw [← monomial_sum_one,monomial_pow,one_pow,a2m]
private theorem Zy {g:vJ A} {e :Degree}
   (hg:g∈Kx A e) (f :vJ A) (d:Degree) :
   weightedHomogeneousComponent (jT A) (d+e) (f * g) =
     weightedHomogeneousComponent (jT A) d f * g:= by
 classical
 induction f using zNP with
 | monomial a c =>
   have ha :=isWeightedHomogeneous_monomial (jT A) a c rfl
   have hg' : g.IsWeightedHomogeneous (jT A) e :=hg
   simp only [weightedHomogeneousComponent_of_mem (ha.mul hg'),
     weightedHomogeneousComponent_of_mem ha,add_right_cancel_iff]
   split <;> simp_all
 | add p q hp hq=>simp [add_mul,hp,hq]
private theorem dSs (i:Fin 4) :
    as3.ke A (i.val+1) ≤
      Se A i.val ⊔ zye {T2 A i} := by
  apply sup_le
  · have hprefix :mo A 0≤ mo A i.val := by simp [mo]
    have hrel :Se A 0≤Se A i.val := by
      apply Ideal.span_mono
      intro f hf
      exact ⟨hf.1,hprefix hf.2⟩
    exact hrel.trans le_sup_left
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    change j.val< i.val+1 at hj
    by_cases hji:j=i
    · subst j
      exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
    · have hlt:j.val< i.val := by
        have hn:j.val≠i.val := fun he=>hji (Fin.ext he)
        omega
      apply Submodule.mem_sup_left
      apply zCn
      exact ⟨⟨_,aN7 j⟩,by
        rw [aNd]
        exact zCn ⟨j,hlt,rfl⟩⟩
private theorem d5I (i:Fin 4) (d:Degree) (f :vJ A)
   (hf :f∈Kx A (shift d i 1))
   (hcut:f∈as3.ke A (i.val+1)) :
   ∃ r∈dO A d,ew A f - ve A i*r∈mo A i.val := by
 classical
 let J:=Se A i.val
 have hJ:f∈zye {T2 A i} ⊔ J:= by
   rw [sup_comm]
   exact dSs i hcut
 obtain ⟨u,v,hv,hsum⟩:=Ideal.mem_span_singleton_sup.mp hJ
 let r :=weightedHomogeneousComponent (jT A) d u
 let s :=weightedHomogeneousComponent (jT A) (shift d i 1) v
 have hhom:J.IsHomogeneous (Kx A) :=
   Ideal.homogeneous_span _ _ fun _ h=>h.1
 have hs :s∈J:=weightedHomogeneousComponent_mem_of_mem _ _ hhom hv _
 have hrel :r*T2 A i+s=f := by
   have he :=congrArg (weightedHomogeneousComponent (jT A) (shift d i 1)) hsum
   rw [map_add,weightedHomogeneousComponent_eq_self (show f.IsWeightedHomogeneous _ _ from hf)]
     at he
   change weightedHomogeneousComponent (jT A) (d+Pi.single i 1)
     (u*T2 A i)+s=f at he
   rwa [Zy (aN7 i)] at he
 have hle :J≤(mo A i.val).comap (ew A).toRingHom :=
   Ideal.span_le.mpr fun _ h=>h.2
 refine ⟨ew A r,?_,?_⟩
 · rw [← aOJ]
   exact ⟨r,weightedHomogeneousComponent_mem _ _ _,rfl⟩
 · have he :=congrArg (ew A) hrel
   rw [map_add,map_mul,aNd] at he
   rw [← he,mul_comm (ve A i),add_sub_cancel_left]
   exact hle hs
theorem proof :aA9.c1 := by
 intro A hz hv i d p hp hprefix a
 have hp' : p∈(Kx A (shift d i 1)).map (ew A).toLinearMap:= by
  rwa [aOJ]
 obtain ⟨f,hf,hfp⟩:=hp'
 change ew A f=p at hfp
 obtain ⟨n,hn⟩:=bRi.proof A hz hv i f ⟨⟨_,hf⟩,hfp ▸ hprefix⟩
 obtain ⟨m,hm⟩:=aY0.proof A hz i a f n hn
 have hshift:shift d i 1+(fun _=>m)=shift (d+fun _=>m) i 1 := by
  unfold shift
  ac_rfl
 have hdeg:GW A a^m*f∈Kx A (shift (d+fun _=>m) i 1) := by
  rw [← hshift,mul_comm]
  exact IsWeightedHomogeneous.mul hf (dId a m)
 obtain ⟨r,hr,hrel⟩:=d5I i (d+fun _=>m) _ hdeg hm
 rw [map_mul,dVK,hfp] at hrel
 exact ⟨m,r,hr,hrel⟩
end
end cyR
end
section
namespace aRT
noncomputable section
open aR dN vS B8
private theorem cXr {A B:Type*} [za6 A] [za6 B]
  (ψ:A →+* B) (hψ:zpX ψ) {I:znc A} {J:znc B}
  (hIJ:I≤J.comap ψ) :Module.length B (B ⧸ J)≤Module.length A (A ⧸ I) := by
 rw [zSA,zSA]
 apply WithBot.coe_le_coe.mp
 rw [Order.coheight_eq_krullDim_Ici,Order.coheight_eq_krullDim_Ici]
 let F:Set.Ici J→Set.Ici I:= fun K=>⟨K.1.comap ψ,hIJ.trans (zOS K.2)⟩
 apply Order.krullDim_le_of_strictMono F
 intro K L hKL
 change K.1.comap ψ<L.1.comap ψ
 exact lt_of_le_of_ne (zOS hKL.le)
  (fun h=>hKL.ne (Subtype.ext (zyU ψ hψ h)))
private theorem dW8 {R:Type*} [za6 R] [ztn R] {d:ℕ}
   (g:z3y (Fin d) GeoField →+* R) (hinj:zq4 g)
   (hfin:g.Finite) :ringKrullDim R=(d:zUi ℕ∞) := by
 let B:=z3y (Fin d) GeoField
 let algebra :=g.toAlgebra
 let:=algebra
 let faithful:FaithfulSMul B R:=(faithfulSMul_iff_algebraMap_injective B R).mpr hinj
 let finite :zAa B R:=hfin
 have hB:ringKrullDim B=(d:zUi ℕ∞) := by
   rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,ringKrullDim_eq_zero_of_field]
   simp
 rw [← hB]
 apply le_antisymm
 · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B R))
   intro x y hxy
   exact Ideal.IsIntegral.under_lt_under (show x.asIdeal<y.asIdeal from hxy)
 · obtain ⟨q,hq,hheight⟩:=Ideal.exists_isPrime_le_height (n:=d) hB.ge
   obtain ⟨z,hz⟩:=Algebra.IsIntegral.comap_surjective B R (⟨q,hq⟩:PrimeSpectrum B)
   have hunder :z.asIdeal.under B=q:=congrArg PrimeSpectrum.asIdeal hz
   have hle :=Ideal.height_under_le_height (R:=B) z.asIdeal
   rw [hunder] at hle
   calc
     ringKrullDim B=(d:zUi ℕ∞) :=hB
     _≤(z.asIdeal.height:zUi ℕ∞) :=WithBot.coe_le_coe.mpr (hheight.trans hle)
     _≤ ringKrullDim R:=Ideal.height_le_ringKrullDim_of_isPrime
private theorem cKI (P:znc g9) [P.IsPrime] :
   ringKrullDim (g9 ⧸ P) =
     ((zIU P).natDegree :zUi ℕ∞) := by
 obtain ⟨d,g,hinj,hfin⟩:=exists_finite_inj_algHom_of_fg GeoField (g9 ⧸ P)
 rw [MvPolynomial.natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hfin hinj,
   Nat.card_fin]
 exact dW8 g.toRingHom hinj hfin
private theorem bEj {P C:znc g9} {D:g9} {d:ℕ}
  (hP:P.IsPrime) (hd:TB P (d+1)) (hD:D∉P)
  (hC: (i9 P D).IsMinimalPrime C) :TB C d:= by
 let:=hP
 let:=hC.isPrime
 have hp: (zIU P).natDegree=d+1 := by
  exact ENat.natCast_inj.mp (WithBot.coe_injective ((cKI P).symm.trans hd))
 have hc:=MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hD hC
 rw [hp] at hc
 simpa [TB,z8U hc] using cKI C
end
end aRT
end
section
namespace bRw
noncomputable section
open E7 agN
open scoped Polynomial
variable {k L σ:Type} [zrb k] [zrb L] [zZE k L]
private def aoH :
  z3y (Fin 2) k →+* (k[X])[X] :=
 zOD (Polynomial.C.comp z1z)
  ![z7y,z1z z7y*z7y]
private theorem eLH (m:Fin 2 →₀ ℕ) (c:k) :
   aoH (MvPolynomial.monomial m c) =
     zdM (m 0+m 1) (zdM (m 1) c) := by
 rw [aoH,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_monomial,
   Finsupp.prod_pow,Fin.prod_univ_two]
 change z1z (z1z c)*(z7y ^m 0 *
   (z1z z7y*z7y)^m 1)= _
 rw [mul_pow,← map_pow,← zoT,
   ← zoT,pow_add,map_mul]
 rw [mul_left_comm (z7y ^m 0) (z1z ((z7y:k[X])^m 1)),
   mul_assoc]
private theorem c4c (p:z3y (Fin 2) k) (m:Fin 2 →₀ ℕ) :
    ((aoH p).coeff (m 0+m 1)).coeff (m 1)=p.coeff m:= by
  classical
  induction p using zNP with
  | add p q hp hq =>
    simp only [map_add,Polynomial.coeff_add,AddMonoidAlgebra.coeff_add,hp,hq]
    rfl
  | monomial n c =>
    rw [eLH,zQm,MvPolynomial.coeff_monomial]
    by_cases h:n=m
    · simp [h]
    · rw [ite_eq_right h]
      by_cases hd:n 0+n 1=m 0+m 1
      · rw [ite_eq_left hd,zQm]
        apply ite_eq_right
        intro h1
        apply h
        have h0:n 0=m 0:= by omega
        ext j
        fin_cases j
        · exact h0
        · exact h1
      · simp [hd]
private theorem eLF :
  zq4 (aoH (k :=k)) := by
 intro p q h
 ext m
 rw [← c4c p m,← c4c q m,h]
private theorem eLD {b z :L} (hb:b≠0) (hz :Transcendental k z) :
    zq4
      (zOD (Polynomial.C.comp (algebraMap k L))
        ![z1z b*z7y,(z1z b*z7y)*z1z z]) := by
  let f :=zhd (Polynomial.aeval (R:=k) z).toRingHom
  let g:=Polynomial.compRingHom (z1z b*z7y)
  have hg:zq4 g:= by
    let e :L[X] ≃ₐ[L] L[X] :=
      Polynomial.algEquivOfCompEqX (z1z b*z7y)
        (z1z b⁻¹*z7y)
        (by simp [← zPC,← mul_assoc,hb])
        (by simp [← zPC,← mul_assoc,hb])
    exact e.injective
  have hf :zq4 f :=
    Polynomial.map_injective _ (transcendental_iff_injective.mp hz)
  have heq :zOD (Polynomial.C.comp (algebraMap k L))
      ![z1z b*z7y,(z1z b*z7y)*z1z z] =
      g.comp (f.comp aoH) := by
    apply zXT
    · intro c
      simp [f,g,aoH,Polynomial.aeval_C]
    · intro j
      fin_cases j
      · simp [f,g,aoH]
      · simp [f,g,aoH,mul_assoc,Polynomial.X_mul_C,
          mul_left_comm (z1z b) (z1z z)]
  rw [heq]
  exact hg.comp (hf.comp eLF)
private theorem bYv (u:σ→L) (j:σ) :
  wL k u (z9v j)=z1z (u j)*Polynomial.X:= by
 simp [wL]
private theorem cHC (u:σ→L) (c:k) :
  wL k u (znf c)=z1z (algebraMap k L c) := by
 simp [wL]
private theorem ePl [z85 σ] (u:σ→L) (i:σ) (a :σ→k)
    (hi:u i≠0) :
    (wL k u).comp (ahO i a).toRingHom =
      zOD (Polynomial.C.comp (algebraMap k L))
        ![z1z (u i)*z7y,
          (z1z (u i)*z7y)*z1z (O7 a (F8 u i))] := by
  have hlinear : ∑ j,algebraMap k L (a j)*u j =
      u i*O7 a (F8 u i) := by
    rw [O7,Finset.mul_sum]
    apply zUo rfl
    intro j _
    rw [Algebra.smul_def,F8]
    field_simp
  apply zXT
  · intro c
    simp [ahO,cHC,zKm]
  · intro j
    rw [zQb,zrD]
    change wL k u ((ahO i a) (z9v j))= _
    rw [ahO,MvPolynomial.aeval_X]
    have hcases : ∀ l:Fin 2,l=0∨l=1 :=
      Fin.forall_fin_two.2 ⟨Or.inl rfl,Or.inr rfl⟩
    rcases hcases j with rfl | rfl
    · exact bYv (k :=k) u i
    · simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
      calc
        _=(∑ l,z1z (algebraMap k L (a l)*u l))*Polynomial.X:= by
          rw [map_sum,zkq]
          simp only [map_mul,cHC,bYv,← mul_assoc]
        _ = _:= by
          rw [← map_sum,hlinear,map_mul,mul_right_comm]
private theorem c0c {F:Type} [zrb F] (C:L →+* F) (V:ValuationSubring F)
   (hc : ∀ c:k,C (algebraMap k L c)∈V) {z r :L}
   (hz :C z∈V) (hr :IsIntegral (zum k {z}) r) :C r∈V:= by
 let S:=zum k ({z} : Set L)
 have hS (x :S) :C (x :L)∈V:= by
   refine Algebra.adjoin_induction (p:= fun y _=>C y∈V) ?_ hc ?_ ?_ x.property
   · intro y hy
     simpa [Set.mem_singleton_iff.mp hy] using hz
   · intro x y _ _ hx hy
     simpa only [map_add] using V.add_mem _ _ hx hy
   · intro x y _ _ hx hy
     simpa only [map_mul] using V.mul_mem _ _ hx hy
 let φ:S →+* V.toSubring :=(C.comp S.val.toRingHom).codRestrict V.toSubring hS
 have h:IsIntegral V.toSubring (C r) :=IsIntegral.map_of_comp_eq φ C rfl hr
 exact (Subring.isIntegrallyClosedIn_iff.mp
   (inferInstanceAs (IsIntegrallyClosedIn V F))) h
private theorem eoI {A F:Type} [za6 A] [zrb F]
   (f :A →+* F) (C:L →+* F) (hc : ∀ c:k,C (algebraMap k L c)∈f.range)
   {s :F} {r z :L} (hz :z≠0) (hs :s∈f.range) (ht:s*C z∈f.range)
   (hr :IsIntegral (zum k {z}) r)
   (hr' : IsIntegral (zum k {z⁻¹}) (r/z)) :
   f.IsIntegralElem (s*C r) := by
 let:zZE A F:=f.toAlgebra
 let B:=(integralClosure A F).toSubring
 by_contra h
 obtain ⟨V,hBV,hn⟩:=Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
   (R:=B) (show s*C r∉B from h)
 have hm {x :F} (hx :x∈f.range) :x∈V:= by
   obtain ⟨y,rfl⟩:=hx
   exact hBV (show f y∈B from f.isIntegralElem_map)
 apply hn
 rcases V.mem_or_inv_mem (C z) with hV | hV
 · exact V.mul_mem _ _ (hm hs) (c0c C V (fun c=>hm (hc c)) hV hr)
 · have hz' : C z⁻¹∈V:= by simpa only [map_inv₀] using hV
   have hp:=V.mul_mem _ _ (hm ht) (c0c C V (fun c=>hm (hc c)) hz' hr')
   rwa [mul_assoc,← map_mul,mul_div_cancel₀ _ hz] at hp
theorem proof :agN.c2 := by
  classical
  intro k L σ _ _ _ _ u i a hi
  dsimp only
  intro hz hchart
  let z :=O7 a (F8 u i)
  let P:=SQ k u
  let φ:=ahO i a
  let Q:=P.comap φ.toRingHom
  have hp:=ePl u i a hi
  constructor
  · change zdq ((wL k u).comp φ.toRingHom) = ⊥
    rw [show φ=ahO i a from rfl,hp,← RingHom.injective_iff_ker_eq_bot]
    exact eLD hi hz
  · let ι:=algebraMap L[X] (RatFunc L)
    let g:=ι.comp (wL k u)
    have hg:zdq g=P :=
      RingHom.ker_comp_of_injective _ (RatFunc.algebraMap_injective L)
    let e :=Ideal.Quotient.lift P g (fun _ hx=>RingHom.mem_ker.mp (hg.symm ▸ hx))
    have he :zq4 e :=RingHom.lift_injective_of_ker_le_ideal _ _ hg.le
    let β: (z3y (Fin 2) k ⧸ Q) →ₐ[k] (z3y σ k ⧸ P) :=
      aWb P φ
    let f :=e.comp β.toRingHom
    let s :=RatFunc.C (u i)*RatFunc.X
    have hf (p:z3y (Fin 2) k) :
        f (zVv Q p) =
          ι (zOD (Polynomial.C.comp (algebraMap k L))
            ![z1z (u i)*z7y,
              (z1z (u i)*z7y)*z1z z] p) := by
      change e (zVv P (φ p))= _
      rw [z0R]
      exact congrArg ι (zLs hp p)
    have hc (c:k) :RatFunc.C (algebraMap k L c)∈f.range := by
      refine ⟨zVv Q (znf c),?_⟩
      rw [hf,zTv]
      rfl
    have hs :s∈f.range := by
      refine ⟨zVv Q (z9v 0),?_⟩
      rw [hf,zrD]
      simp [ι,s]
    have ht:s*RatFunc.C z∈f.range := by
      refine ⟨zVv Q (z9v 1),?_⟩
      rw [hf,zrD]
      simp [ι,s]
    have hgen (j:σ) :β.toRingHom.IsIntegralElem (zVv P (z9v j)) := by
      apply RingHom.IsIntegralElem.of_map he
      have hvalue :e (zVv P (z9v j)) =
          s*RatFunc.C (F8 u i j) := by
        rw [z0R,show g (z9v j)=ι (wL k u (z9v j))
          from rfl,bYv]
        have hu:u i*F8 u i j=u j:=mul_div_cancel₀ _ hi
        simp only [s,ι,map_mul,RatFunc.algebraMap_C,RatFunc.algebraMap_X]
        rw [mul_right_comm,← map_mul,hu]
      rw [hvalue]
      exact eoI f RatFunc.C hc hz.ne_zero hs ht (hchart.1 j) (hchart.2 j)
    change β.toRingHom.Finite
    apply RingHom.IsIntegral.to_finite
    · intro x
      obtain ⟨p,rfl⟩:=zld x
      let:zZE (z3y (Fin 2) k ⧸ Q) (z3y σ k ⧸ P) :=β.toRingHom.toAlgebra
      change zVv P p∈integralClosure (z3y (Fin 2) k ⧸ Q) _
      induction p using z5i with
      | C c =>
        have h:β.toRingHom (zVv Q (znf c)) =
            zVv P (znf c) := by
          change zVv P (φ (znf c))= _
          simp [φ,ahO,zKm]
        rw [← h]
        exact β.toRingHom.isIntegralElem_map
      | add p q hp hq =>
        rw [map_add]
        exact (integralClosure _ _).add_mem hp hq
      | mul_X p j hp =>
        rw [map_mul]
        exact (integralClosure _ _).mul_mem hp (hgen j)
    · apply RingHom.FiniteType.of_comp_finiteType (f :=algebraMap k (z3y (Fin 2) k ⧸ Q))
      have hcomp:β.toRingHom.comp (algebraMap k (z3y (Fin 2) k ⧸ Q)) =
          algebraMap k (z3y σ k ⧸ P) :=
        RingHom.ext fun c=>β.commutes c
      rw [hcomp]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
end
end bRw
end
section
namespace bRf
noncomputable section
open jA aFP Polynomial
open scoped Polynomial BigOperators
private abbrev kO (w:Fin 3→ℕ) :mA→ℕ :=
 fun i=>i.elim 0 w
private theorem dlY (w:Fin 3→ℕ) (F:ko) (i:ℕ) :
  ((qN F).coeff i).weightedTotalDegree w≤F.weightedTotalDegree (kO w) := by
 apply zf9
 intro a ha
 have hs :a.optionElim i∈F.support := by
  rw [MvPolynomial.mem_support_iff] at ha ⊢
  simpa only [qN,MvPolynomial.optionEquivLeft_coeff_coeff] using ha
 have h:=z6P (kO w) hs
 rw [zDM,Finsupp.sum_option_index_smul] at h
 simpa only [kO,Option.elim_none,Option.elim_some,smul_zero,zero_add,
  Finsupp.some_optionElim,zDM] using h
private theorem dl5 (w:Fin 3→ℕ) (F G:ko) (m n:ℕ) :
    ((qN F).resultant (qN G) m n).weightedTotalDegree w ≤
      n*F.weightedTotalDegree (kO w)+m*G.weightedTotalDegree (kO w) := by
  classical
  let A:=(qN F).sylvester (qN G) m n
  let B:=F.weightedTotalDegree (kO w)
  let D:=G.weightedTotalDegree (kO w)
  have hleft (i:Fin (m+n)) (j:Fin m) : (A i (j.castAdd n)).weightedTotalDegree w≤D:= by
    simp only [A,sylvester,Matrix.of_apply,Fin.addCases_left]
    split
    · exact dlY w G _
    · simp [z4a]
  have hright (i:Fin (m+n)) (j:Fin n) : (A i (j.natAdd m)).weightedTotalDegree w≤B:= by
    simp only [A,sylvester,Matrix.of_apply,Fin.addCases_right]
    split
    · exact dlY w F _
    · simp [z4a]
  change A.det.weightedTotalDegree w≤n*B+m*D
  rw [zg2 (n*B),zwK]
  refine (AddMonoidAlgebra.supDegree_sum_le (D:=ztN w)).trans (zf9 ?_)
  intro π _
  have hprod: (∏ i,A (π i) i).weightedTotalDegree w≤ m*D + n*B:= by
    have hbound: (∏ i,A (π i) i).weightedTotalDegree w ≤
        ∑ i,(A (π i) i).weightedTotalDegree w :=
      AddMonoidAlgebra.supDegree_prod_le (D:=ztN w) (map_zero _) (map_add _)
    apply hbound.trans
    rw [Fin.sum_univ_add]
    have h₁: (∑ j:Fin m,(A (π (j.castAdd n)) (j.castAdd n)).weightedTotalDegree w) ≤
        ∑ _j:Fin m,D:=zQk fun j _=>hleft _ j
    have h₂: (∑ j:Fin n,(A (π (j.natAdd m)) (j.natAdd m)).weightedTotalDegree w) ≤
        ∑ _j:Fin n,B:=zQk fun j _=>hright _ j
    simpa only [Finset.sum_const,Finset.card_univ,zgY,Nat.nsmul_eq_mul]
      using Nat.add_le_add h₁ h₂
  change (zjl π•(∏ i,A (π i) i)).weightedTotalDegree w≤ m*D + n*B
  have hneg (p:Lower) : (-p).weightedTotalDegree w=p.weightedTotalDegree w :=
    AddMonoidAlgebra.supDegree_neg (D:=ztN w)
  rcases znm (zjl π) with hs | hs <;>
    simpa [hs,hneg] using hprod
theorem proof :aFP.c2 := by
 intro F G
 constructor
 · have h:=dl5 (fun _:Fin 3=>1) F G (gY F) (gY G)
   change (aGx F G).weightedTotalDegree (fun _=>1) ≤
    gY G*vC F+gY F*vC G at h
   have hw: (fun _:Fin 3=>(1 :ℕ))=1 := by
    funext i
    simp only [Pi.one_apply]
   rwa [hw,MvPolynomial.weightedTotalDegree_one] at h
 · simpa only [aGx,aOE,lP,kO]
    using dl5 Fin.val F G (gY F) (gY G)
end
end bRf
end
section
namespace bRz
noncomputable section
open agO
variable {A B C D:Type} [za6 A] [za6 B] [za6 C] [za6 D]
private theorem b89 (a :A →+* C) (ha :zpX a) :
  (zdq a).minimalPrimes=Ideal.comap a '' (⊥ : znc C).minimalPrimes := by
 rw [zPx,Ideal.comap_minimalPrimes_eq_of_surjective ha]
private theorem cwP (a :A →+* C) (ha :zpX a)
   (p:znc C) [p.IsPrime] :
   weight (zdq a) (p.comap a)=weight ⊥ p:= by
 let aₚ:=Localization.localRingHom (p.comap a) p a rfl
 have hsurj:zpX aₚ :=
   RingHom.surjective_localRingHom_of_surjective a ha p
 have hcompl: (p.comap a).primeCompl.map a=p.primeCompl :=
   Submonoid.map_comap_eq_of_surjective ha p.primeCompl
 have hker :zdq aₚ=(zdq a).map
     (algebraMap A (Localization.AtPrime (p.comap a))) :=
   IsLocalization.ker_map (Localization.AtPrime p) a hcompl
 have h:=Ideal.coheight_comap_of_surjective aₚ hsurj
   (⊥ : znc (Localization.AtPrime p))
 rw [← zPx,hker] at h
 unfold weight
 rw [dite_eq_left (show (p.comap a).IsPrime from inferInstance),
   dite_eq_left (show p.IsPrime from inferInstance),zSA,
   zSA,Ideal.map_bot]
 exact congrArg ENat.toNat h
private theorem cG4 (g:A →+* B) (m:C →+* D) (a :A →+* C) (b:B →+* D)
  (h:m.comp a=b.comp g) (p:znc D) :
  (p.comap b).comap g=(p.comap m).comap a := by
 rw [zg6,zg6,h]
private theorem edP [ztn B] (g:A →+* B)
   (hg:zq4 g) (x :A) :
   zJ1 hg (algebraMap A (FractionRing A) x) =
     algebraMap B (FractionRing B) (g x) := by
 change IsLocalization.map _ g _ _ = _
 rw [IsLocalization.map_eq]
private theorem edU [ztn A] [ztn B] [ztn C] [ztn D]
   (g:A →+* B) (m:C →+* D) (hg:zq4 g) (hm:zq4 m)
   (a :A ≃+* C) (b:B ≃+* D) (h:m.comp a.toRingHom=b.toRingHom.comp g) :
   letI:=(zJ1 hg:FractionRing A →+* FractionRing B).toAlgebra
   letI:=(zJ1 hm:FractionRing C →+* FractionRing D).toAlgebra
   zsE (FractionRing A) (FractionRing B) =
     zsE (FractionRing C) (FractionRing D) := by
 let G:FractionRing A →+* FractionRing B:=zJ1 hg
 let M:FractionRing C →+* FractionRing D:=zJ1 hm
 let aK:FractionRing A ≃+* FractionRing C:=zDt a
 let bK:FractionRing B ≃+* FractionRing D:=zDt b
 let _:=G.toAlgebra
 let _:=M.toAlgebra
 have hsquare :M.comp aK.toRingHom=bK.toRingHom.comp G:= by
   apply IsFractionRing.ringHom_ext (A:=A)
   intro x
   change M (aK (algebraMap A (FractionRing A) x)) =
     bK (G (algebraMap A (FractionRing A) x))
   simp only [aK,bK,G,M,IsFractionRing.ringEquivOfRingEquiv_algebraMap,
     edP]
   exact congrArg (algebraMap D (FractionRing D)) (zLs h x)
 exact congrArg Cardinal.toNat (Algebra.rank_eq_of_equiv_equiv aK bK hsquare)
private theorem dVp (g:A →+* B) (m:C →+* D) (a :A →+* C) (b:B →+* D)
   (ha :zpX a) (hb:zpX b)
   (h:m.comp a=b.comp g) (p:znc D) [p.IsPrime] :
   degree g (p.comap b)=degree m p:= by
 let e :=cG4 g m a b h p
 let aq: (A ⧸ (p.comap b).comap g) ≃+* (C ⧸ p.comap m) :=
   RingEquiv.ofBijective (z3G (p.comap m) a e.le)
     ⟨Ideal.quotientMap_injective' e.ge,zc0 ha⟩
 let bp: (B ⧸ p.comap b) ≃+* (D ⧸ p) :=
   RingEquiv.ofBijective (z3G p b le_rfl)
     ⟨zmq,zc0 hb⟩
 let gq:=z3G (p.comap b) g le_rfl
 let mq:=z3G p m le_rfl
 have hq:mq.comp aq.toRingHom=bp.toRingHom.comp gq :=
   (Ideal.comp_quotientMap_eq_of_comp_eq h p).symm
 unfold degree
 rw [dite_eq_left (show (p.comap b).IsPrime from inferInstance),
   dite_eq_left (show p.IsPrime from inferInstance)]
 exact edU gq mq zmq zmq aq bp hq
private theorem cRQ [IsNoetherianRing B] [IsNoetherianRing D]
   (g:A →+* B) (m:C →+* D) (a :A →+* C) (b:B →+* D)
   (ha :zpX a) (hb:zpX b)
   (h:m.comp a=b.comp g) (q:znc C) :
   aNP g (zdq b) (q.comap a)=aNP m ⊥ q:= by
 have hb_inj:=zyU b hb
 have ha_inj:=zyU a ha
 have hmem (p:znc D) :
     p.comap b∈auX g (zdq b) (q.comap a)↔p∈auX m ⊥ q:= by
   simp only [auX,zO0,Ideal.mem_minimalPrimesFinset,
     b89 b hb,cG4 g m a b h,ha_inj.eq_iff]
   constructor
   · rintro ⟨⟨p',hp',he⟩,hq⟩
     exact ⟨hb_inj he ▸ hp',hq⟩
   · rintro ⟨hp,hq⟩
     exact ⟨⟨p,hp,rfl⟩,hq⟩
 unfold aNP
 symm
 refine Finset.sum_nbij (Ideal.comap b) (fun p hp=>(hmem p).2 hp) hb_inj.injOn ?_ ?_
 · intro P hP
   have hmin:P∈(zdq b).minimalPrimes :=
     Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp hP).1
   rw [b89 b hb] at hmin
   obtain ⟨p,_,rfl⟩:=hmin
   exact ⟨p,(hmem p).1 hP,rfl⟩
 · intro p hp
   let _:=aUP (⟨p,hp⟩:auX m ⊥ q)
   rw [cwP b hb,dVp g m a b ha hb h]
theorem proof :agO.c2 := by
 intro U V R S _ _ _ _ _ _ g f J I w r s hc Q hQ
 obtain ⟨m,hg,hf⟩:=hc
 change Q∈J.minimalPrimes at hQ
 rw [Ideal.minimalPrimes_eq_comap] at hQ
 obtain ⟨p,hp,rfl⟩:=hQ
 let _:=hp.isPrime
 refine ⟨p.comap r.toQuotient,?_,?_,?_⟩
 · change p.comap r.toQuotient∈(zye {w}).minimalPrimes
   rw [← r.ker_eq,b89 r.toQuotient r.surjective]
   exact ⟨p,hp,rfl⟩
 · have hJ:=cwP (zVv J) zld p
   have hw:=cwP r.toQuotient r.surjective p
   rw [Ideal.mk_ker] at hJ
   rw [r.ker_eq] at hw
   exact hJ.trans hw.symm
 · have hI:=cRQ g m (zVv J) (zVv I)
     zld zld hg p
   have hw:=cRQ f m r.toQuotient s.toQuotient
     r.surjective s.surjective hf p
   rw [Ideal.mk_ker] at hI
   rw [s.ker_eq] at hw
   exact hI.trans hw.symm
end
end bRz
end
section
namespace aA0
noncomputable section
open aR jA Rk
open scoped Polynomial PowerSeries
private def abg {Γ s} (P:jF Γ s) (L:kH P) :
  jK →+* bbm :=
 zOD
  (MvPolynomial.C.comp (zhd (algebraMap ao kS)))
  (fun i=>i.elim (znf (z1z seed)) (ar9 P L))
private theorem c8C {Γ s} (P:jF Γ s) (L:kH P) (p:ao[X]) :
  abg P L (znf p)=znf (jH p) := by
 simp [abg,jH]
private def aCE (a :atU) :atU →+* zpm bbm :=
 (zS4 znf).comp ((zpc a).comp expand)
private def bic {Γ s} (P:jF Γ s) (L:kH P) :
   jK →+* zpm bbm :=
 (zpc (znf (jH P.H^3))).comp
   ((zS4 (abg P L)).comp (Polynomial.coeToPowerSeries.ringHom.comp aEP))
private theorem bCT (a :atU) (p:ao[X]) :
  aCE a (jH p)=zMG (znf (jH p)) := by
 simp [aCE,d49,z2H]
private theorem dMb (a :atU) (p:ao[X]) (j:ℕ) :
   aCE a (z75 j (jH p)) =
     zMG (znf (z75 j (jH p))) := by
 rw [show z75 j (jH p)=jH (z75 j p) from
   zvb (algebraMap ao kS) j p]
 exact bCT _ _
private def cHr {A:Type*} [za6 A] (a b c:A) (D:Fin 3→A)
  (j:Fin 3) :A :=
 if j=0 then -a^2*D 0
 else if j=1 then a*b*D 0-a^2*D 1
 else (a*c - b^2)*D 0+a*b*D 1-a^2*D 2
set_option maxHeartbeats 800000 in
private theorem eDY {Γ s} (P:jF Γ s) (L:kH P) :
    ∃ M:bbm →+* zpm bbm,
      M.comp (abg P L)=bic P L ∧
        M (znf (jH P.H))=zMG (znf (jH P.H)) := by
  classical
  let H :=jH P.H
  let R:=ahH L.numerator L.denominator
  choose d hd using fun j:Fin 3 =>
    d5a (H^3) (z75 j.val R)
  let D:Fin 3→zpm bbm:= fun j=>zS4 znf (d j)
  let A:= fun p:atU=>zMG (znf (σ:=Fin 3) p)
  let Δ:=cHr (A H) (A (z75 1 H))
    (A (z75 2 H)) D
  let M:=zOD (aCE (H^3))
    (fun j=>zMG (z9v j)+Δ j)
  have hres (j:Fin 3) :
      aCE (H^3) (z75 j.val R) =
        A (z75 j.val R)+(A H)^3*D j:= by
    have hj:=congrArg (zS4 (znf (σ:=Fin 3))) (hd j)
    simpa [aCE,A,D,z2H] using hj
  have hMC (p:atU) :M (znf p)=aCE (H^3) p:= by
    simp only [M,zTv]
  have hMX (j:Fin 3) :M (z9v j)=zMG (z9v j)+Δ j:= by
    simp only [M,zrD]
  have hH (j:ℕ) :aCE (H^3) (z75 j H) =
      A (z75 j H) :=dMb _ P.H j
  have hH₀:aCE (H^3) H=A H :=bCT _ P.H
  have hH₁:aCE (H^3) (zst H)=A (zst H) := by
    simpa only [Polynomial.hasseDeriv_one'] using hH 1
  refine ⟨M,?_,?_⟩
  · apply zXT
    · intro p
      simp only [zQb,bic,c8C,hMC,bCT,
        gox,zwl,zni,
        z2H,bLl]
    · intro j
      cases j with
      | none =>
        simp only [zQb,bic,abg,zrD,
          Option.elim,hMC,aCE,d5b,goy,map_add,map_mul,
          zwl,Polynomial.coe_X,zni,
          z2H,PowerSeries.map_X,bLl,c8o]
        exact add_comm _ _
      | some j =>
        have hjet:M (ar9 P L j)=zMG (ar9 P L j) := by
          simp only [ar9,← show R=ahH L.numerator L.denominator from rfl,
            ← show H=jH P.H from rfl,map_add,map_sum,apply_ite,map_zero,map_mul]
          simp only [hMC,hMX,hres,hH]
          fin_cases j <;>
            norm_num [Fin.sum_univ_three,Δ,cHr,A,hH₀,hH₁,
              Polynomial.hasseDeriv_zero'] <;> ring
        simpa only [zQb,bic,abg,zrD,
          Option.elim,goz,zwl,
          zni,z2H,bLl] using hjet
  · rw [hMC,bCT]
private theorem dMC {Γ s} (P:jF Γ s) (L:kH P)
  (i:ℕ) (F:jK) :
  z2o i (bic P L F)=restore P L (Yd P.H i F) := by
 simp only [bic,zQb,PowerSeries.coeff_rescale,PowerSeries.coeff_map,
  zwl,Polynomial.coeff_coe,cGk]
 change _=abg P L (Yd P.H i F)
 simp only [Yd,← aIY,map_mul,c8C,jH,map_pow,pow_mul]
theorem c4E {Γ s} (P:jF Γ s) (L:kH P)
  (r i:ℕ) (F:jK)
  (hF:znf (jH P.H)^r∣restore P L F) :
  znf (jH P.H)^r∣restore P L (Yd P.H i F) := by
 obtain ⟨M,hM,hH⟩:=eDY P L
 change znf (jH P.H)^r∣abg P L F at hF
 obtain ⟨Q,hQ⟩:=hF
 refine ⟨z2o i (M Q),?_⟩
 rw [← dMC,← zmU hM F]
 change z2o i (M (abg P L F))= _
 rw [hQ,map_mul,map_pow,hH,← map_pow,PowerSeries.coeff_C_mul]
end
end aA0
end
section
namespace ap8
noncomputable section
open Kd MvPolynomial
open scoped BigOperators
variable {ι:Type} [DecidableEq ι]
private def factor (used :List ι) (f :ι→ℕ→ℚ) (i:ι) (a :ℕ) :ℚ :=
 if i∈used then f i (a+1) - f i a else f i a
private theorem dV1 [z85 ι] (used :List ι) (hn:used.Nodup)
    (f :ι→ℕ→ℚ) (a :ι→ℕ) :
    uU used (fun b => ∏ i,f i (b i)) a = ∏ i,factor used f i (a i) := by
  induction used generalizing a with
  | nil=>simp [uU,factor]
  | cons i rest ih =>
    obtain ⟨hi,hr⟩:=List.nodup_cons.mp hn
    let R := ∏ j∈Finset.univ.erase i,factor rest f j (a j)
    have same (b:ι→ℕ) (hb : ∀ j≠i,b j=a j) :
        (∏ j,factor rest f j (b j))=R*f i (b i) := by
      rw [← zNr _ _ (zTc i)]
      have hR: (∏ j∈Finset.univ.erase i,factor rest f j (b j))=R :=
        zX3 rfl fun j hj=> by rw [hb j (zFe hj)]
      rw [hR]
      simp [factor,hi]
    have hR: (∏ j∈Finset.univ.erase i,factor (i :: rest) f j (a j))=R:= by
      apply zX3 rfl
      intro j hj
      simp [factor,List.mem_cons,zFe hj]
    simp only [uU,ih hr]
    rw [same (a+step i) (fun j hj=> by simp [step,hj]),
      same a (fun _ _=>rfl),← Finset.prod_erase_mul _ _ (Finset.mem_univ i),hR]
    simp only [Pi.add_apply,step,Pi.single_eq_same,factor,List.mem_cons,true_or,ite_true]
    ring
private theorem dVZ (used :List ι) (c:ℚ) (f : (ι→ℕ)→ℚ) (a :ι→ℕ) :
   uU used (fun b=>c*f b) a=c*uU used f a := by
 induction used generalizing a with
 | nil=>rfl
 | cons i rest ih=>simp only [uU,ih,mul_sub]
private def a3v :List ι→(ι→ℕ)→z3y ι ℚ →ₗ[ℚ] ℚ
 | [],a=>(MvPolynomial.aeval fun i=>(a i:ℚ)).toLinearMap
 | i :: rest,a=>a3v rest (a+step i)-a3v rest a
private theorem b0C (used :List ι) (a :ι→ℕ) (P:z3y ι ℚ) :
   a3v used a P=uU used (fun b=>zY9 (fun i=>(b i:ℚ)) P) a := by
 induction used generalizing a with
 | nil=>rfl
 | cons i rest ih=>simp only [a3v,LinearMap.sub_apply,uU,ih]
private theorem dWU [z85 ι] (used :List ι) (hn:used.Nodup)
    (e :ι →₀ ℕ) (c:ℚ) (hd:e.degree≤used.length) (a b:ι→ℕ) :
    a3v used a (monomial e c) =
      if e.degree=used.length then a3v used b (monomial e c) else 0:= by
  have heval (z :ι→ℕ) :
      zY9 (fun i=>(z i:ℚ)) (monomial e c)=c * ∏ i,(z i:ℚ)^e i:= by
    rw [eval_monomial,Finsupp.prod_fintype _ _ (fun _=>pow_zero _)]
  let f (i:ι) (x :ℕ) :ℚ:=(x :ℚ)^e i
  have hcalc (z :ι→ℕ) :
      a3v used z (monomial e c)=c * ∏ i,factor used f i (z i) := by
    rw [b0C]
    simp_rw [heval]
    change uU used (fun b=>c * ∏ i,f i (b i)) z= _
    rw [dVZ,dV1 used hn f]
  rw [hcalc a,hcalc b]
  by_cases hz : ∃ i∈used,e i=0
  · obtain ⟨i,hi,he⟩:=hz
    have hzero (z :ι→ℕ) : (∏ j,factor used f j (z j))=0 :=
      zue (zTc i) (by simp [factor,hi,f,he])
    simp [hzero]
  · let m (i:ι) :ℕ:=if i∈used then 1 else 0
    have hm : ∑ i,m i=used.length:= by
      rw [← List.toFinset_card_of_nodup hn,Finset.card_eq_sum_ite (ziq _)]
      simp [m]
    have hme (i:ι) :m i≤e i:= by
      by_cases hi:i∈used
      · simpa [m,hi] using Nat.one_le_iff_ne_zero.mpr (fun he=>hz ⟨i,hi,he⟩)
      · simp [m,hi]
    have heq (i:ι) :e i=m i:= by
      by_contra hne
      have hlt: (∑ j,m j) < ∑ j,e j :=
        Finset.sum_lt_sum (fun j _=>hme j) ⟨i,zTc _,lt_of_le_of_ne (hme i) (Ne.symm hne)⟩
      rw [hm,← zFi] at hlt
      exact (not_lt_of_ge hd) hlt
    have he :e.degree=used.length:= by
      simp only [zFi,heq,hm]
    rw [ite_eq_left he]
    congr 1
    apply zX3 rfl
    intro i _
    by_cases hi:i∈used <;> simp [factor,hi,f,heq i,m]
theorem bD4 [z85 ι] (used :List ι) (hn:used.Nodup) (P:z3y ι ℚ)
   (hd:P.totalDegree≤used.length) (a b:ι→ℕ) :
   uU used (fun z=>zY9 (fun i=>(z i:ℚ)) P) a =
   uU used (fun z=>zY9 (fun i=>(z i:ℚ))
     (homogeneousComponent used.length P)) b:= by
 classical
 rw [← b0C,← b0C,homogeneousComponent_apply,map_sum,
   Finset.sum_filter]
 conv_lhs=>rw [P.as_sum,map_sum]
 apply zUo rfl fun e he => ?_
 exact dWU used hn e _ ((MvPolynomial.le_totalDegree he).trans hd) a b
end
end ap8
end
section
namespace ap8
noncomputable section
open aR dN Dr Kd MvPolynomial Filter
variable {ι:Type} [DecidableEq ι]
private theorem bD3 (used :List ι) {F G: (ι→ℕ)→ℚ} {u:ι→ℕ}
   (h : ∀ a≥u,F a=G a) (a :ι→ℕ) (ha :u≤a) :
   uU used F a=uU used G a := by
 induction used generalizing a with
 | nil=>exact h a ha
 | cons i rest ih =>
   simp only [uU,ih a ha,ih (a+step i) (ha.trans fun j=>z8K _ _)]
private theorem dV0 [z85 ι] (fF:ι→Shape) (base :ι)
   (F: (ι→ℕ)→ℚ) (G:Shape→ℚ)
   (hFG : ∀ v,0<v base→F v=G (ku fF v))
   (used :List ι) (v :ι→ℕ) (hv :0<v base) :
   uU used F v=BE G (used.map fF) (ku fF v) := by
 induction used generalizing v with
 | nil=>exact hFG v hv
 | cons i rest ih =>
   have hv' : 0<(v+step i) base :=hv.trans_le (z8K _ _)
   simp only [uU,List.map_cons,BE,ih v hv,ih _ hv',aES,aQe]
theorem proof :Kd.c5:= by
 intro ι _ _ fF J base used hs _ hn hd hfil
 dsimp only
 intro P hP
 obtain ⟨u,hu⟩:=eventually_atTop.mp hP
 have hcompare (v :ι→ℕ) (hv :0<v base) :=
   fT8 fF J base hs hfil P u hu v hv used.length hd
 have hdegree :P.totalDegree≤used.length :=
   (bO7 P u (dimension J)
     (fun v hv=>(hcompare v (hv base)).1)).trans hd
 let F:= fun v :ι→ℕ=>zY9 (fun i=>(v i:ℚ))
   (homogeneousComponent used.length P)
 have hFG (v :ι→ℕ) (hv :0<v base) :F v=capCoeff J used.length (ku fF v) :=
   (buL P u v hdegree).symm.trans (hcompare v hv).2
 filter_upwards [eventually_ge_atTop u] with a ha
 calc
   _=uU used (fun v=>zY9 (fun i=>(v i:ℚ)) P) a :=
     (bD3 used hu a ha).symm
   _=uU used F (step base) :=bD4 used hn P hdegree a (step base)
   _=BE (capCoeff J used.length) (used.map fF) (fF base) := by
     rw [dV0 fF base F _ hFG used _ (by simp [step]),aQe]
end
end ap8
end
section
namespace cze
theorem proof :axk.c2 :=
 aZc.proof
end cze
end
section
namespace aY6
noncomputable section
open MvPolynomial rW MJ
open scoped BigOperators
variable {k σ τ:Type*} [zrb k]
private theorem c5x (φ:z3y τ k →ₐ[k] z3y σ k)
  (hφ:agH φ) {n:ℕ} {p:z3y τ k} (hp:p.IsHomogeneous n) :
  (φ p).IsHomogeneous n:= by
 rw [aeval_unique φ]
 simpa only [one_mul,z3s] using hp.aeval (φ ∘ z9v) hφ
private theorem ePa (φ:z3y τ k →ₐ[k] z3y σ k)
   (hφ:agH φ) (n:ℕ) (p:z3y τ k) :
   φ (homogeneousComponent n p)=homogeneousComponent n (φ p) := by
 induction p using zNP with
 | monomial d c =>
   have hd: (monomial d c).IsHomogeneous d.degree :=isHomogeneous_monomial c rfl
   rw [homogeneousComponent_of_mem hd,homogeneousComponent_of_mem (c5x φ hφ hd)]
   split_ifs <;> simp
 | add p q hp hq =>
   simp only [map_add,hp,hq]
private theorem ePg (φ:z3y τ k →ₐ[k] z3y σ k)
    (hφ:agH φ) (p:z3y τ k) : (φ p).totalDegree≤p.totalDegree := by
  calc
    (φ p).totalDegree =
        (∑ n∈z4x (p.totalDegree+1),φ (homogeneousComponent n p)).totalDegree := by
      rw [← map_sum,sum_homogeneousComponent]
    _≤p.totalDegree := by
      apply totalDegree_finsetSum_le
      intro n hn
      exact (c5x φ hφ (homogeneousComponent_isHomogeneous n p)).totalDegree_le.trans
        (zeh (Finset.mem_range.mp hn))
private theorem dzW (φ:z3y τ k →ₐ[k] z3y σ k)
  (hφ:agH φ) (I:znc (z3y σ k)) :
  lW (I.comap φ)≤(lW I).comap φ:= by
 apply Ideal.span_le.mpr
 rintro _ ⟨p,hp,rfl⟩
 change φ (homogeneousComponent p.totalDegree p)∈lW I
 rw [ePa φ hφ]
 exact bcK (show φ p∈I from hp) (ePg φ hφ p)
variable [Finite σ] [Finite τ]
private theorem dy7 (φ:z3y τ k →ₐ[k] z3y σ k)
    (A:znc (z3y σ k)) (hA:A.IsPrime) (hb:aRK φ A) :
    dimension (A.comap φ)=dimension A:= by
  classical
  let _:=zQs σ
  have :A.IsPrime :=hA
  let J:=A.comap φ
  let g: (z3y τ k ⧸ J) →ₐ[k] (z3y σ k ⧸ A) :=
    Ideal.quotientMapₐ A φ le_rfl
  have hg:zq4 g :=
    zmq (I:=A) (f :=φ.toRingHom)
  apply le_antisymm (natDegree_affineHilbertPolynomial_le_of_injective g hg)
  choose u v hv huv using fun i:σ ↦ hb (z9v i)
  let t := ∏ i,v i
  let a :=zVv J t
  let b:=zVv A (φ t)
  have hgb:g a=b:=rfl
  have hb0:b≠0:= by
    change zVv A (φ (∏ i,v i))≠0
    rw [map_prod,map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
      mt Ideal.Quotient.eq_zero_iff_mem.mp (hv i)
  have hx (i:σ) : ∃ q,g q=b* zVv A (z9v i) := by
    let w := ∏ j∈Finset.univ.erase i,v j
    have ht:w*v i=t:=zNr _ _ (zTc i)
    have hi:zVv A (φ (u i)) =
        zVv A (φ (v i))* zVv A (z9v i) := by
      have hz :=Ideal.Quotient.eq_zero_iff_mem.mpr (huv i)
      simp only [map_sub,map_mul,sub_eq_zero] at hz
      exact hz.symm.trans (mul_comm _ _)
    refine ⟨zVv J (w*u i),?_⟩
    change zVv A (φ (w*u i)) =
      zVv A (φ t)* zVv A (z9v i)
    rw [← ht,map_mul,map_mul,map_mul,map_mul,hi,mul_assoc]
  have hrec (p:z3y σ k) :
      ∃ q m,g q=b^m* zVv A p:= by
    induction p using z5i with
    | C c =>
      refine ⟨algebraMap k (z3y τ k ⧸ J) c,0,?_⟩
      rw [AlgHom.commutes,pow_zero,one_mul]
      rfl
    | add p r hp hr =>
      obtain ⟨q,m,hq⟩:=hp
      obtain ⟨s,n,hs⟩:=hr
      refine ⟨a^n*q+a^m*s,m+n,?_⟩
      simp only [map_add,map_mul,map_pow,hgb,hq,hs,pow_add]
      ring
    | mul_X p i hp =>
      obtain ⟨q,m,hq⟩:=hp
      obtain ⟨s,hs⟩:=hx i
      refine ⟨q*s,m+1,?_⟩
      simp only [map_mul,hq,hs,pow_succ]
      ring
  let U:=Localization.Away a
  let V:=Localization.Away b
  have :IsLocalization.Away (g a) V:= by rw [hgb]; infer_instance
  let ψ:U →ₐ[k] V:=IsLocalization.Away.mapₐ U V g a
  have hψ:zpX ψ:= by
    apply (IsLocalization.Away.map_surjective_iff U V g.toRingHom a).mpr
    intro x
    obtain ⟨p,rfl⟩:=zld x
    simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,hgb] using hrec p
  exact natDegree_affineHilbertPolynomial_le_of_surjective_away_away
    (s :=φ t) (t:=t) (IsRegular.of_ne_zero hb0).1 ψ hψ
private theorem eAr {I Q:znc (z3y τ k)}
  (hQ:Q.IsPrime) (hIQ:I≤Q) (hdim:dimension Q=2) (hI:dimension I≤2) :
  I.IsMinimalPrime Q:= by
 refine ⟨⟨hQ,hIQ⟩,?_⟩
 intro R hR hRQ
 by_contra hn
 obtain ⟨f,hfQ,hfR⟩:=SetLike.exists_of_lt (lt_of_le_not_ge hRQ hn)
 have hbound:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
  hR.1 hfR (b:=f.totalDegree) le_rfl).1
 have hQle :R ⊔ zye {f} ≤ Q :=
  sup_le hRQ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfQ))
 have hle :=natDegree_affineHilbertPolynomial_le_of_le hQle
 have hRI:dimension R≤dimension I:=natDegree_affineHilbertPolynomial_le_of_le hR.2
 have hRbound:dimension R≤2 :=hRI.trans hI
 change dimension (R ⊔ zye {f})≤dimension R - 1 at hbound
 change dimension Q≤dimension (R ⊔ zye {f}) at hle
 omega
theorem proof :MJ.c4 := by
 intro k σ τ _ _ _ φ hφ A hA hdim hbir
 have hdim' : dimension (A.comap φ)=2 :=(dy7 φ A hA hbir).trans hdim
 refine ⟨hdim',?_⟩
 intro P hP hPd
 have :P.IsPrime :=hP.isPrime
 exact eAr (Ideal.IsPrime.comap φ)
  ((dzW φ hφ A).trans (zOS hP.le)) hPd
  ((cDp (A.comap φ)).trans_eq hdim')
end
end aY6
end
section
namespace cyp
noncomputable section
open aRS
open scoped BigOperators
variable {k m:ℕ}
private def limit (bad:zJe (Fin m →₀ ℕ)) (j:Fin m) :ℕ :=
 ∑ b∈bad,b j
private theorem eu1 {bad:zJe (Fin m →₀ ℕ)} {b:Fin m →₀ ℕ}
  (hb:b∈bad) (j:Fin m) :b j≤limit bad j :=
 zfK (f := fun b=>b j) (fun _ _=>zD0 _) hb
private def threshold (bad:zJe (Fin m →₀ ℕ)) :ℕ :=
 (∑ j,limit bad j)+1
private abbrev Vars (slot:Fin m→Fin k) (i:Fin k) := {j:Fin m // slot j=i}
private theorem dgd (slot:Fin m→Fin k) (i:Fin k) (a :Fin m→ℕ) :
   (∑ j:Vars slot i,a j.val) = ∑ j∈Finset.univ.filter (fun j=>slot j=i),a j :=
 (Finset.sum_subtype _ (by simp) a).symm
private abbrev bTD (slot:Fin m→Fin k) (bad:zJe (Fin m →₀ ℕ))
   (w:Fin k→ℕ) :=
 {e :Fin m →₀ ℕ // (∀ b∈bad,¬ b≤e) ∧
   ∀ i,∑ j∈Finset.univ.filter (fun j=>slot j=i),e j=w i}
private abbrev Cell (slot:Fin m→Fin k) (bad:zJe (Fin m →₀ ℕ)) :=
 {c : ∀ j,Fin (limit bad j+1) //
   (∀ b∈bad,¬ ∀ j,b j≤(c j).val) ∧
   ∀ i,∃ j:Vars slot i,(c j.val).val=limit bad j.val}
private abbrev B6 (slot:Fin m→Fin k) (bad:zJe (Fin m →₀ ℕ))
   (c:Cell slot bad) (i:Fin k) (n:ℕ) :=
 {a :Vars slot i→ℕ //
   (∀ j,min (a j) (limit bad j.val)=(c.val j.val).val) ∧ ∑ j,a j=n}
private instance gPX (slot:Fin m→Fin k) (bad:zJe (Fin m →₀ ℕ))
    (c:Cell slot bad) (i:Fin k) (n:ℕ) :Finite (B6 slot bad c i n) := by
  classical
  let encode (a :B6 slot bad c i n) (j:Vars slot i) :Fin (n+1) :=
    ⟨a.val j,zB1 (by
      calc
        a.val j ≤ ∑ l,a.val l :=
          zfK (fun _ _=>zD0 _) (zTc j)
        _=n:=a.property.2)⟩
  apply Finite.of_injective encode
  intro a b hab
  apply Subtype.ext
  funext j
  exact congrArg (fun f :Vars slot i→Fin (n+1)=>(f j).val) hab
private theorem eak (slot:Fin m→Fin k) (bad:zJe (Fin m →₀ ℕ))
    (c:Cell slot bad) (i:Fin k) :
    Monotone (fun n=>Nat.card (B6 slot bad c i n)) := by
  classical
  intro p q hpq
  obtain ⟨j,hj⟩:=c.property.2 i
  let lift (a :B6 slot bad c i p) :B6 slot bad c i q :=
    ⟨zWr a.val j (a.val j+(q - p)),by
      constructor
      · intro l
        by_cases h:l=j
        · subst l
          rw [zuO,hj]
          have ha :=a.property.1 j
          rw [hj] at ha
          have hle :limit bad j.val≤a.val j:=ha.symm.trans_le (min_le_left _ _)
          exact min_eq_right (hle.trans (z8K _ _))
        · rw [zBg h]
          exact a.property.1 l
      · have hsum:=z6q (zTc j) a.val (a.val j)
        rw [Function.update_eq_self,a.property.2] at hsum
        rw [z6q (zTc j)]
        omega⟩
  apply Nat.card_le_card_of_injective lift
  intro a b hab
  apply Subtype.ext
  funext l
  have he :=congrArg (fun f :B6 slot bad c i q=>f.val l) hab
  change zWr a.val j (a.val j+(q - p)) l =
    zWr b.val j (b.val j+(q - p)) l at he
  by_cases hl:l=j
  · subst l
    simp only [zuO] at he
    exact z8U he
  · simpa only [zBg hl] using he
private def clip {slot:Fin m→Fin k} {bad:zJe (Fin m →₀ ℕ)} {w:Fin k→ℕ}
    (hw : ∀ i,threshold bad≤w i) (e :bTD slot bad w) :Cell slot bad:= by
  classical
  refine ⟨fun j=>⟨min (e.val j) (limit bad j),
    zB1 (min_le_right _ _)⟩,?_,?_⟩
  · intro b hb h
    exact e.property.1 b hb (Finsupp.le_def.mpr (fun j=>(h j).trans (min_le_left _ _)))
  · intro i
    by_contra h
    have hle (j:Fin m) (hj:j∈Finset.univ.filter (fun j=>slot j=i)) :
        e.val j≤limit bad j:= by
      by_contra hlt
      have hge :limit bad j≤e.val j:=(Nat.lt_of_not_ge hlt).le
      exact h ⟨⟨j,(Finset.mem_filter.mp hj).2⟩,min_eq_right hge⟩
    have hweight:w i ≤ ∑ j,limit bad j:= calc
      w i = ∑ j∈Finset.univ.filter (fun j=>slot j=i),e.val j:=(e.property.2 i).symm
      _ ≤ ∑ j∈Finset.univ.filter (fun j=>slot j=i),limit bad j:=zQk hle
      _ ≤ ∑ j,limit bad j:=Finset.sum_le_sum_of_subset (zT0 _ _)
    exact (Nat.not_succ_le_self _) ((hw i).trans hweight)
private def join {slot:Fin m→Fin k} {bad:zJe (Fin m →₀ ℕ)} (w:Fin k→ℕ)
   (x :Σ c:Cell slot bad,∀ i,B6 slot bad c i (w i)) :bTD slot bad w:= by
 let ex (j:Fin m) :ℕ:=(x.2 (slot j)).val ⟨j,rfl⟩
 refine ⟨Finsupp.equivFunOnFinite.symm ex,?_,?_⟩
 · intro b hb he
   apply x.1.property.1 b hb
   intro j
   rw [← (x.2 (slot j)).property.1 ⟨j,rfl⟩]
   exact le_min (Finsupp.le_def.mp he j) (eu1 hb j)
 · intro i
   change ∑ j∈Finset.univ.filter (fun j=>slot j=i),ex j=w i
   rw [← dgd slot i ex,← (x.2 i).property.2]
   apply zUo rfl
   intro j _
   obtain ⟨j,hj⟩:=j
   subst i
   rfl
private theorem eqi {slot:Fin m→Fin k} {bad:zJe (Fin m →₀ ℕ)}
    {w:Fin k→ℕ} (hw : ∀ i,threshold bad≤w i) :
    Function.Bijective (join (slot:=slot) (bad:=bad) w) := by
  constructor
  · rintro ⟨c,x⟩ ⟨d,y⟩ h
    have he (j:Fin m) : (x (slot j)).val ⟨j,rfl⟩=(y (slot j)).val ⟨j,rfl⟩ :=
      congrArg (fun e :bTD slot bad w=>e.val j) h
    have hc:c=d:= by
      apply Subtype.ext
      funext j
      apply Fin.ext
      exact ((x (slot j)).property.1 ⟨j,rfl⟩).symm.trans
        ((congrArg (fun a=>min a (limit bad j)) (he j)).trans
          ((y (slot j)).property.1 ⟨j,rfl⟩))
    subst d
    apply congrArg (Sigma.mk c)
    funext i
    apply Subtype.ext
    funext j
    obtain ⟨j,hj⟩:=j
    subst i
    exact he j
  · intro e
    let c:=clip hw e
    refine ⟨⟨c,fun i=>⟨fun j=>e.val j.val,?_,?_⟩⟩,?_⟩
    · intro j
      rfl
    · rw [dgd slot i (fun j=>e.val j)]
      exact e.property.2 i
    · apply Subtype.ext
      apply Finsupp.ext
      intro j
      rfl
theorem proof :aRS.c2 := by
 classical
 intro k m slot bad
 let:z85 (Cell slot bad) :=zQs _
 let e :=(Fintype.equivFin (Cell slot bad)).symm
 refine ⟨threshold bad,Fintype.card (Cell slot bad),
   fun a i n=>(Nat.card (B6 slot bad (e a) i n) :ℚ),?_,?_,?_⟩
 · intro a i p q hpq
   exact Nat.cast_le.mpr (eak slot bad (e a) i hpq)
 · intro a i n
   exact Nat.cast_nonneg _
 · intro w hw
   have h:=Nat.card_eq_of_bijective (join (slot:=slot) (bad:=bad) w) (eqi hw)
   change Nat.card (Σ c:Cell slot bad,∀ i,B6 slot bad c i (w i)) =
     aAp slot bad w at h
   rw [← h,Nat.card_sigma]
   simp only [Nat.card_pi,Nat.cast_sum,Nat.cast_prod]
   apply Fintype.sum_equiv e.symm
   intro c
   rw [e.apply_symm_apply]
end
end cyp
end
section
namespace cxW
open yz axb MeasureTheory
open scoped BigOperators
private theorem cN2 {α:Type} {v :α→iz} {S T:zJe α}
   {f :iz →ₗ[ℝ] ℝ} (hf :aRv v S f) {a :α} (ha :a∈S)
   (hT:T.Nonempty) :f (JG v T)≤f (v a) := by
 by_cases hsub:T⊆S
 · exact (bFN hf ha hT hsub).le
 · exact (bFO hf ha hsub).le
private theorem dfY {ι:Type} [z85 ι] {x y :ι→iz}
  {w u:ι→ℝ} (hmass : ∑ i,w i = ∑ i,u i)
  (hsum : ∑ i,w i•x i = ∑ i,u i•y i)
  (f :iz →ₗ[ℝ] ℝ) (m:ℝ) :
  ∑ i,w i*(m - f (x i)) = ∑ i,u i*(m - f (y i)) := by
 have hf :=congrArg f hsum
 simp only [map_sum,map_smul,smul_eq_mul] at hf
 simp only [mul_sub,zQq,← zkq,hmass,hf]
private theorem cEC {α ι:Type} [z85 ι] {v :α→iz}
   {F G:ι→zJe α} {S:zJe α} (hS:agG v S)
   (hF : ∀ i,(F i).Nonempty) (hsub : ∀ i,F i⊆S) (hG : ∀ i,(G i).Nonempty)
   {w u:ι→ℝ} (hu : ∀ i,0< u i)
   (hmass : ∑ i,w i = ∑ i,u i)
   (hsum : ∑ i,w i•JG v (F i) = ∑ i,u i•JG v (G i)) :
   ∀ i,G i⊆S:= by
 obtain ⟨a,ha⟩:=hS.1
 obtain ⟨f,hf⟩:=hS.2
 have he :=dfY hmass hsum f (f (v a))
 have hzero : ∑ i,w i*(f (v a) - f (JG v (F i)))=0 :=
   zYF fun i _=> by
     rw [bFN hf ha (hF i) (hsub i),sub_self,mul_zero]
 rw [hzero] at he
 have hg:=(Fintype.sum_eq_zero_iff_of_nonneg (fun i =>
   mul_nonneg (hu i).le (sub_nonneg.mpr (cN2 hf ha (hG i))))).mp he.symm
 intro i
 by_contra h
 exact (mul_pos (hu i) (sub_pos.mpr (bFO hf ha h))).ne' (congrFun hg i)
private theorem cWR {α:Type} {v :α→iz} {n:ℕ}
   {F G:Fin (n+1)→zJe α}
   (hF:Monotone F) (hG:Monotone G)
   (hfaceF : ∀ i,agG v (F i)) (hfaceG : ∀ i,agG v (G i))
   {w u:Fin (n+1)→ℝ} (hw : ∀ i,0<w i) (hu : ∀ i,0< u i)
   (hmass : ∑ i,w i = ∑ i,u i)
   (hsum : ∑ i,w i•JG v (F i) = ∑ i,u i•JG v (G i)) :
   F (zym n)=G (zym n) := by
 apply Finset.Subset.antisymm
 · exact cEC (hfaceG _) (fun i=>(hfaceG i).1)
     (fun i=>hG (zO9 i)) (fun i=>(hfaceF i).1) hw hmass.symm hsum.symm _
 · exact cEC (hfaceF _) (fun i=>(hfaceF i).1)
     (fun i=>hF (zO9 i)) (fun i=>(hfaceG i).1) hu hmass hsum _
private theorem cWS {α:Type} {v :α→iz} {n:ℕ}
   {F G:Fin (n+2)→zJe α}
   (hF:StrictMono F)
   (hfaceF : ∀ i,agG v (F i)) (hfaceG : ∀ i,agG v (G i))
   (htop:F (zym (n+1))=G (zym (n+1)))
   {w u:Fin (n+2)→ℝ} (hu : ∀ i,0< u i)
   (hmass : ∑ i,w i = ∑ i,u i)
   (hsum : ∑ i,w i•JG v (F i) = ∑ i,u i•JG v (G i)) :
   u (zym (n+1))≤w (zym (n+1)) := by
 let p:Fin (n+2) :=(zym n).castSucc
 obtain ⟨a,ha⟩:=(hfaceF p).1
 obtain ⟨f,hf⟩:=(hfaceF p).2
 let gap (T:zJe α) :ℝ:=f (v a) - f (JG v T)
 have he : (∑ i,w i*gap (F i)) = ∑ i,u i*gap (G i) :=
   dfY hmass hsum f (f (v a))
 have hzero : ∑ i:Fin (n+1),w i.castSucc*gap (F i.castSucc)=0:= by
   apply zYF
   intro i _
   have hi:i.castSucc≤p:=Fin.castSucc_le_castSucc_iff.mpr (zO9 i)
   simp only [gap,bFN hf ha (hfaceF _).1 (hF.monotone hi),sub_self,mul_zero]
 have hnonneg:0 ≤ ∑ i:Fin (n+1),u i.castSucc*gap (G i.castSucc) :=
   Finset.sum_nonneg fun i _ =>
     mul_nonneg (hu _).le (sub_nonneg.mpr (cN2 hf ha (hfaceG _).1))
 have hpos :0<gap (F (zym (n+1))) :=
   sub_pos.mpr (bFO hf ha
     (not_le_of_gt (hF (Fin.castSucc_lt_last (zym n)))))
 rw [zHE (n:=n+1),zHE (n:=n+1),
   hzero,zero_add,← htop] at he
 apply le_of_mul_le_mul_right _ hpos
 rw [he]
 exact le_add_of_nonneg_left hnonneg
private theorem dHQ {α:Type} {v :α→iz} {n:ℕ}
    {F G:Fin (n+1)→zJe α}
    (hF:StrictMono F) (hG:StrictMono G)
    (hfaceF : ∀ i,agG v (F i)) (hfaceG : ∀ i,agG v (G i))
    {w u:Fin (n+1)→ℝ} (hw : ∀ i,0<w i) (hu : ∀ i,0< u i)
    (hmass : ∑ i,w i = ∑ i,u i)
    (hsum : ∑ i,w i•JG v (F i) = ∑ i,u i•JG v (G i)) :F=G:= by
  induction n with
  | zero =>
    have htop:=cWR hF.monotone hG.monotone hfaceF hfaceG hw hu hmass hsum
    funext i
    exact zsB htop (fun j=>Fin.elim0 j) i
  | succ n ih =>
    have htop:=cWR hF.monotone hG.monotone hfaceF hfaceG hw hu hmass hsum
    have hlast :w (zym (n+1))=u (zym (n+1)) :=
      le_antisymm (cWS hG hfaceG hfaceF htop.symm hw hmass.symm hsum.symm)
        (cWS hF hfaceF hfaceG htop hu hmass hsum)
    have hpre :=ih
      (F:= fun i=>F i.castSucc) (G:= fun i=>G i.castSucc)
      (w:= fun i=>w i.castSucc) (u:= fun i=>u i.castSucc)
      (fun _ _ hij=>hF (Fin.castSucc_lt_castSucc_iff.mpr hij))
      (fun _ _ hij=>hG (Fin.castSucc_lt_castSucc_iff.mpr hij))
      (fun i=>hfaceF i.castSucc) (fun i=>hfaceG i.castSucc)
      (fun i=>hw i.castSucc) (fun i=>hu i.castSucc)
      (by
        rw [zHE (n:=n+1),zHE (n:=n+1),
          hlast] at hmass
        exact add_right_cancel hmass)
      (by
        rw [zHE (n:=n+1),zHE (n:=n+1),
          hlast,htop] at hsum
        exact add_right_cancel hsum)
    funext i
    exact zsB htop (congrFun hpre) i
private theorem cVt {α:Type} [z85 α] {v :α→iz}
   {F:Fin 5→zJe α} (hF:F∈flags v) {x :iz}
   (hx :x∈interior (aoa v F)) :
   ∃ w:Fin 5→ℝ,(∀ i,0<w i)∧(∑ i,w i)=1 ∧
     ∑ i,w i•JG v (F i)=x := by
 have hi:=cSC v F hF
 have htop:=hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
 let b:AffineBasis (Fin 5) ℝ iz :=
   ⟨fun i=>JG v (F i),hi,htop⟩
 change x∈interior (convexHull ℝ (zxp b)) at hx
 rw [b.interior_convexHull] at hx
 exact ⟨fun i=>b.coord i x,hx,b.sum_coord_apply_eq_one x,b.linear_combination_coord_eq_self x⟩
theorem proof :axb.c2 := by
 intro α _ v F hF G hG hne
 change F∈flags v at hF
 change G∈flags v at hG
 obtain ⟨hmonoF,hfaceF⟩:=(bsB v F).mp hF
 obtain ⟨hmonoG,hfaceG⟩:=(bsB v G).mp hG
 have hinterior {x :iz} (hx :x∈interior (aoa v F))
     (hy :x∈interior (aoa v G)) :False := by
   obtain ⟨w,hw,hmassF,hsumF⟩:=cVt hF hx
   obtain ⟨u,hu,hmassG,hsumG⟩:=cVt hG hy
   exact hne (dHQ hmonoF hmonoG hfaceF hfaceG hw hu
     (hmassF.trans hmassG.symm) (hsumF.trans hsumG.symm))
 unfold AEDisjoint
 refine measure_mono_null
   (t:=frontier (aoa v F)∪frontier (aoa v G)) ?_ ?_
 · intro x hx
   by_cases h:x∈interior (aoa v F)
   · exact Or.inr ((mem_frontier_iff_notMem_interior hx.2).mpr (hinterior h))
   · exact Or.inl ((mem_frontier_iff_notMem_interior hx.1).mpr h)
 · exact measure_union_null ((convex_convexHull ℝ _).addHaar_frontier volume)
     ((convex_convexHull ℝ _).addHaar_frontier volume)
end cxW
end
section
namespace bRv
noncomputable section
open E7 Polynomial
open scoped WithZero
private theorem cH0 {k L:Type*} [zrb k] [zrb L] [zZE k L]
  (V:ValuationSubring L) (hV : ∀ c:k,algebraMap k L c∈V)
  (c:k) (hc:c≠0) :V.valuation (algebraMap k L c)=1 := by
 have hle :=(V.valuation_le_one_iff _).2 (hV c)
 have hinv : (algebraMap k L c)⁻¹∈V:= by
  rw [← map_inv₀]
  exact hV c⁻¹
 have hge :=(V.valuation.one_le_val_iff ((_root_.map_ne_zero (algebraMap k L)).2 hc)).2
  ((V.valuation_le_one_iff _).2 hinv)
 exact le_antisymm hle hge
private theorem exe {k L Γ:Type*} [zrb k] [zrb L] [zZE k L]
    [LinearOrderedCommGroupWithZero Γ] (v :Valuation L Γ)
    (hc : ∀ c:k,c≠0→v (algebraMap k L c)=1)
    {t:L} (ht:Transcendental k t) :
    ∃ g:Γ,g≠0 ∧ ∀ a :k,∃ n:ℤ,v (t - algebraMap k L a)=g^n:= by
  have hline (a :k) :t - algebraMap k L a≠0:= by
    intro ha
    exact ht ⟨z7y - C a,X_sub_C_ne_zero a,by simpa using ha⟩
  have hconst (a :k) :v (algebraMap k L a)≤1 := by
    by_cases ha :a=0
    · simp [ha]
    · exact (hc a ha).le
  by_cases hhigh:1<v t
  · refine ⟨v t,v.ne_zero_iff.mpr ht.ne_zero,fun a=>⟨1,?_⟩⟩
    rw [zpow_one]
    exact v.map_sub_eq_of_lt_left ((hconst a).trans_lt hhigh)
  have hle (a :k) :v (t - algebraMap k L a)≤1 :=
    v.map_sub_le (le_of_not_gt hhigh) (hconst a)
  by_cases hlow : ∃ a :k,v (t - algebraMap k L a)<1
  · obtain ⟨a,ha⟩:=hlow
    refine ⟨v (t - algebraMap k L a),v.ne_zero_iff.mpr (hline a),fun b => ?_⟩
    by_cases hab:b=a
    · subst b
      exact ⟨1,by rw [zpow_one]⟩
    refine ⟨0,?_⟩
    rw [zpow_zero]
    apply le_antisymm (hle b)
    by_contra! hb
    have hdiff : (t - algebraMap k L a)-(t - algebraMap k L b) =
        algebraMap k L (b-a) := by rw [map_sub]; ring
    have hlt:=v.map_sub_lt ha hb
    rw [hdiff,hc _ (sub_ne_zero.mpr hab)] at hlt
    exact (lt_irrefl 1) hlt
  · refine ⟨1,one_ne_zero,fun a=>⟨0,?_⟩⟩
    rw [zpow_zero]
    exact le_antisymm (hle a) (le_of_not_gt fun ha=>hlow ⟨a,ha⟩)
private theorem dsj {k L Γ:Type*} [zrb k] [IsAlgClosed k]
    [zrb L] [zZE k L] [LinearOrderedCommGroupWithZero Γ]
    (v :Valuation L Γ) (hc : ∀ c:k,c≠0→v (algebraMap k L c)=1)
    {t:L} (ht:Transcendental k t) :
    ∃ g:Γ,g≠0 ∧ ∀ y :IntermediateField.adjoin k {t},y≠0 →
      ∃ n:ℤ,v (y :L)=g^n:= by
  obtain ⟨g,hg,hlin⟩:=exe v hc ht
  have hprod (m:Multiset k) :
      ∃ n:ℤ,v (aeval t (m.map (fun a=>z7y - C a)).prod)=g^n:= by
    induction m using Multiset.induction_on with
    | empty=>exact ⟨0,by simp⟩
    | cons a m ih =>
      obtain ⟨i,hi⟩:=hlin a
      obtain ⟨j,hj⟩:=ih
      refine ⟨i+j,?_⟩
      rw [Multiset.map_cons,Multiset.prod_cons,map_mul,map_mul,hj,
        map_sub,aeval_X,aeval_C,hi,zpow_add₀ hg]
  have hpoly (p:k[X]) (hp:p≠0) : ∃ n:ℤ,v (aeval t p)=g^n:= by
    obtain ⟨n,hn⟩:=hprod p.roots
    refine ⟨n,?_⟩
    conv_lhs=>rw [(IsAlgClosed.splits p).eq_prod_roots]
    rw [map_mul,aeval_C,map_mul,hc _ (leadingCoeff_ne_zero.mpr hp),one_mul,hn]
  refine ⟨g,hg,fun y hy => ?_⟩
  let e :=RatFunc.algEquivOfTranscendental t ht
  obtain ⟨r,rfl⟩:=e.surjective y
  have hr :r≠0:= fun h=>hy (h ▸ e.map_zero)
  obtain ⟨i,hi⟩:=hpoly r.num (RatFunc.num_ne_zero hr)
  obtain ⟨j,hj⟩:=hpoly r.denom r.denom_ne_zero
  exact ⟨i - j,by rw [RatFunc.algEquivOfTranscendental_apply,map_div₀,hi,hj,
    zpow_sub₀ hg]⟩
private theorem gEZ {L Γ:Type*} [zrb L] [LinearOrderedCommGroupWithZero Γ]
   (v :Valuation L Γ) (s :zJe ℕ) (f :ℕ→L)
   (hsum : ∑ i∈s,f i=0) (hpos : ∃ i∈s,v (f i)≠0) :
   ∃ i∈s,∃ j∈s,i<j∧v (f i)=v (f j)∧v (f j)≠0:= by
 obtain ⟨a,ha,ha0⟩:=hpos
 obtain ⟨i,hi,hmax⟩:=z6Q s (fun j=>v (f j)) ⟨a,ha⟩
 have ha' : 0<v (f a) :=v.pos_iff.mpr (v.ne_zero_iff.mp ha0)
 have hi0:v (f i)≠0:=(ha'.trans_le (hmax a ha)).ne'
 have hother : ∃ j∈s,j≠i∧v (f j)=v (f i) := by
   by_contra! h
   have heq :=v.map_sum_eq_of_lt hi (f :=f) (fun j hj=> by
     rw [Finset.mem_sdiff,Finset.mem_singleton] at hj
     exact lt_of_le_of_ne (hmax j hj.1) (h j hj.1 hj.2))
   rw [hsum,map_zero] at heq
   exact hi0 heq.symm
 obtain ⟨j,hj,hji,heq⟩:=hother
 rcases lt_or_gt_of_ne hji with hlt | hlt
 · exact ⟨j,hj,i,hi,hlt,heq,hi0⟩
 · exact ⟨i,hi,j,hj,hlt,heq.symm,heq.trans_ne hi0⟩
private theorem gK1 {F L Γ:Type*} [zrb F] [zrb L] [zZE F L]
  [zAa F L] [LinearOrderedCommGroupWithZero Γ]
  (v :Valuation L Γ) {x :L} (hx :x≠0) :
  ∃ y :F,y≠0∧v x^(zsE F L).factorial=v (algebraMap F L y) := by
 let p:=minpoly F x
 let f :ℕ→L:= fun i=>algebraMap F L (p.coeff i)*x^i
 have hp:p.Monic:=minpoly.monic (IsIntegral.of_finite F x)
 have hxv :=v.ne_zero_iff.mpr hx
 have hsum : ∑ i∈z4x (p.natDegree+1),f i=0:= by
  simpa only [aeval_eq_sum_range,Algebra.smul_def] using minpoly.aeval F x
 have htop : ∃ i∈z4x (p.natDegree+1),v (f i)≠0:= by
  refine ⟨p.natDegree,Finset.mem_range.mpr (Nat.lt_succ_self _),?_⟩
  simp [f,hp.coeff_natDegree,hxv]
 obtain ⟨i,_,j,hj,hij,heq,hj0⟩:=gEZ v _ f hsum htop
 simp only [f,map_mul,map_pow] at heq hj0
 have hjc:v (algebraMap F L (p.coeff j))≠0:= fun hz=>hj0 (by rw [hz,zero_mul])
 have hic:v (algebraMap F L (p.coeff i))≠0:= fun hz=>hj0 (by rw [← heq,hz,zero_mul])
 have hpow:v x^(j - i)=v (algebraMap F L (p.coeff i/p.coeff j)) := by
  rw [pow_sub₀ _ hxv hij.le,← div_eq_mul_inv,map_div₀,map_div₀]
  exact (div_eq_div_iff (pow_ne_zero _ hxv) hjc).2 (by simpa only [mul_comm] using heq.symm)
 have hdeg:j - i≤zsE F L :=
  (Nat.sub_le _ _).trans ((zeh (Finset.mem_range.mp hj)).trans (minpoly.natDegree_le x))
 obtain ⟨m,hm⟩:=Nat.dvd_factorial (Nat.sub_pos_of_lt hij) hdeg
 have hcoeff (a :F) (ha :v (algebraMap F L a)≠0) :a≠0 :=
  fun hz=>ha (by rw [hz,map_zero,map_zero])
 refine ⟨(p.coeff i/p.coeff j)^m,pow_ne_zero _ (div_ne_zero (hcoeff _ hic)
  (hcoeff _ hjc)),?_⟩
 rw [hm,pow_mul,hpow,map_pow,map_pow]
private theorem dTm {k L Γ:Type*} [zrb k] [IsAlgClosed k]
   [zrb L] [zZE k L] [LinearOrderedCommGroupWithZero Γ]
   (v :Valuation L Γ) (hv :zpX v)
   (hc : ∀ c:k,c≠0→v (algebraMap k L c)=1)
   {t:L} (ht:Transcendental k t)
   [zAa (IntermediateField.adjoin k {t}) L] :IsCyclic Γˣ:= by
 let F:=IntermediateField.adjoin k {t}
 let N :=(zsE F L).factorial
 obtain ⟨g,hg,hbase⟩:=dsj v hc ht
 let G:=Subgroup.zpowers (Units.mk0 g hg)
 have hmem (u:Γˣ) :u^N∈G:= by
   obtain ⟨x,hx⟩:=hv (u:Γ)
   have hx0:x≠0:=v.ne_zero_iff.mp (hx ▸ Units.ne_zero u)
   obtain ⟨y,hy,hyval⟩:=gK1 (F:=F) v hx0
   obtain ⟨n,hn⟩:=hbase y hy
   have hp: (u:Γ)^N=g^n:= by
     rw [← hx,show v x^N=v (algebraMap F L y) from hyval]
     exact hn
   refine ⟨n,Units.ext ?_⟩
   rw [Units.val_zpow_eq_zpow_val,Units.val_pow_eq_pow_val,Units.val_mk0,hp]
 exact isCyclic_of_injective ((powMonoidHom N).codRestrict G hmem)
   ((MonoidHom.injective_codRestrict _ _ _).2
     (pow_left_strictMono (Nat.factorial_ne_zero (zsE F L))).injective)
theorem proof :agN.c1 := by
 intro k L _ _ _ _ hL V hproper hconst
 obtain ⟨t,ht,hfin⟩:=hL
 let:=hfin
 let v :=V.valuation
 have hnontriv :v.IsNontrivial:= by
   by_contra h
   apply hproper
   simpa only [v,ValuationSubring.valuationSubring_valuation] using
     (Valuation.valuationSubring_eq_top_iff v).2 h
 let:IsCyclic V.ValueGroupˣ:=dTm v V.valuation_surjective
   (cH0 V hconst) ht
 let:v.IsRankOneDiscrete :=Valuation.IsRankOneDiscrete.mk' v
 let e :=Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v
 let w:=v.restrict.map (.ofClass e) e.toOrderIso.monotone
 have hw (x :L) :w x=e (v.restrict x) :=rfl
 have hsurj:zpX v.restrict :=
   MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass v)
 refine ⟨⟨w,e.surjective.comp hsurj,fun c hc => ?_⟩,?_⟩
 · rw [hw,v.restrict_eq_one_iff.mpr (cH0 V hconst c hc),map_one]
 · ext x
   rw [Valuation.mem_valuationSubring_iff,hw,← map_one e]
   change e.toOrderIso (v.restrict x)≤e.toOrderIso 1↔x∈V
   rw [e.toOrderIso.le_iff_le,v.restrict_le_one_iff]
   exact V.valuation_le_one_iff x
end
end bRv
end
section
namespace aKq
noncomputable section
open aR dN vS aA5 MvPolynomial
open scoped Polynomial
private theorem c56 (g:af 4) (n:ℕ) (a :Chart g) :
   S g*D g (S g^n*a)-(n:Chart g)*D g (S g)*(S g^n*a) =
     S g^(n+1)*D g a := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [pow_succ' (S g) n,pow_succ' (S g) (n+1),mul_assoc (S g) (S g^n) a,
     bQM,Nat.cast_succ]
   linear_combination S g*ih
private theorem eGr (g:af 4) (n:ℕ) :
    incl g (su g n)=S g^(2*n)*(D g)^[n] (incl g (z9v 0)) := by
  induction n with
  | zero=>simp [su]
  | succ n ih =>
    rw [su,aqZ,map_sub,map_mul,map_mul,map_mul,map_natCast,
      ← bQK,← bQK,ih,zLk,
      show 2*(n+1)=(2*n+1)+1 by omega]
    let a :=(D g)^[n] (incl g (z9v 0))
    change S g*(S g*D g (S g^(2*n)*a)) -
      (↑(2*n) :Chart g)*(S g*D g (S g))*(S g^(2*n)*a) =
        S g^((2*n+1)+1)*D g a
    calc
      _=S g*(S g*D g (S g^(2*n)*a) -
          (↑(2*n) :Chart g)*D g (S g)*(S g^(2*n)*a)) := by ring
      _ = _:= by rw [c56,pow_succ' (S g) (2*n+1),mul_assoc]
private theorem ews (g:af 4) (n:ℕ) :
   zp g (numerator g n)=S g^n*(D g)^[n] (24*W g) := by
 induction n with
 | zero =>
   rw [numerator,map_mul,aVb,bel,map_ofNat,pow_zero,one_mul,
    Function.iterate_zero_apply]
 | succ n ih =>
   rw [numerator,ewv,ih,zLk,c56]
private theorem epn (g:af 4) : (D g)^[4] (incl g (z9v 0))=24*W g:= by
 have h0:D g (incl g (z9v 0))=incl g (z9v 1) := by simpa using bja g 0
 have h1 :D g (incl g (z9v 1))=2*incl g (z9v 2) := by simpa using bja g 1
 have h2 :D g (incl g (z9v 2))=3*incl g (z9v 3) := by simpa using bja g 2
 have h3:D g (incl g (z9v 3))=4*W g:=cxq g
 have hnat (n:ℕ) (a :Chart g) :D g ((n:Chart g)*a)=(n:Chart g)*D g a := by
  rw [bQM,cxr,zero_mul,add_zero]
 have htwo (a :Chart g) :D g (2*a)=2*D g a := by
  simpa only [Nat.cast_ofNat] using hnat 2 a
 have hsix (a :Chart g) :D g (6*a)=6*D g a := by
  simpa only [Nat.cast_ofNat] using hnat 6 a
 change D g (D g (D g (D g (incl g (z9v 0)))))= _
 rw [h0,h1,htwo,h2,← mul_assoc]
 rw [show (2 :Chart g)*3=6 by norm_num,hsix,h3]
 ring
private theorem cHn (g:af 4) (k :ℕ) :
  zp g (numerator g k)*S g^(k+8)=incl g (su g (k+4)) := by
 rw [ews,eGr,Function.iterate_add_apply,epn,
  mul_right_comm,← pow_add,show k+(k+8)=2*(k+4) by omega]
variable {f Q:af 4} {l:ℕ}
private def aAy (b:Branch f Q l) :Chart b.g →+* b.Local :=
 IsLocalization.Away.lift (separant b.g)
  (g:=b.vN.comp (zDK j8))
  (IsLocalization.Away.algebraMap_isUnit b.sigma)
@[simp] private theorem a87 (b:Branch f Q l) (P:af 4) :
   aAy b (incl b.g P)=b.vN (bC P) :=
  IsLocalization.Away.lift_eq _ _ _
end
end aKq
end
section
namespace cya
open aR dN BO GJ YU MvPolynomial
private theorem gnD {σ:Type*} (p:Shape)
   (label :uL p→σ) (hinj:zq4 label) (x :Fin 4→GeoField) :
   eval (fun i=>algebraMap GeoField (FractionRing (z3y σ GeoField)) (x i))
     (Uq p label)≠0:= by
 classical
 let m₀:uL p:= fun _=>0
 have hm₀:m₀∈Bz p:= by
   simp [Bz,m₀]
 let P:z3y σ GeoField :=
   ∑ m∈Bz p,z9v (label m)*C (∏ i:Fin 4,x i^(m i).val)
 let F:=FractionRing (z3y σ GeoField)
 let ρ:=algebraMap (z3y σ GeoField) F
 have hmap :algebraMap GeoField F=ρ.comp (C (σ:=σ)) :=
   zYY GeoField (z3y σ GeoField) F
 have heval :eval (fun i=>algebraMap GeoField F (x i)) (Uq p label)=ρ P:= by
   simp only [Uq,P,ρ,F,map_sum,map_mul,map_prod,map_pow,
     eval_C,eval_X,hmap,zQb]
 let c:σ→GeoField:= fun j=>if j=label m₀ then 1 else 0
 have hspecialize :eval c P=1 := by
   simp only [P,map_sum,map_mul,eval_X,eval_C]
   rw [zpa m₀ hm₀]
   · simp [c,m₀]
   · intro m _ hm
     simp [c,hinj.ne hm]
 change eval (fun i=>algebraMap GeoField F (x i)) (Uq p label)≠0
 rw [heval]
 intro hz
 have hP:P=0:=(zxb (K:=F) _) (hz.trans (map_zero ρ).symm)
 rw [hP,map_zero] at hspecialize
 exact zero_ne_one hspecialize
private theorem dcu {σ:Type*} (aI:znc GeoJets)
   [aI.IsPrime] (p:Shape) (label :uL p→σ)
   (hinj:zq4 label) :
   Uq p label∉aI.map
     (zDK (algebraMap GeoField (FractionRing (z3y σ GeoField)))) := by
 have hex : (zeroLocus GeoField aI).Nonempty := by
   by_contra h
   apply (inferInstance :aI.IsPrime).ne_top
   rw [← IsPrime.vanishingIdeal_zeroLocus (K:=GeoField) aI,
     Set.not_nonempty_iff_eq_empty.mp h,vanishingIdeal_empty]
 obtain ⟨x,hx⟩:=hex
 let F:=FractionRing (z3y σ GeoField)
 let ι:=algebraMap GeoField F
 let e :z3y (Fin 4) F →+* F:=eval (ι ∘ x)
 have hle :aI.map (zDK ι)≤zdq e := by
   apply Ideal.map_le_iff_le_comap.mpr
   intro f hf
   change eval (ι ∘ x) (zDK ι f)=0
   have hz :eval x f=0:= by simpa only [aeval_eq_eval] using hx f hf
   rw [eval_map,← eval₂_comp,hz,map_zero]
 exact fun hm=>gnD p label hinj x (hle hm)
theorem proof :akN.c1 := by
 intro aI a h hs _ _ _
 let:aI.IsPrime :=hs
 let: (gN aI a h).IsPrime :=aA7.beK aI hs
 constructor
 · unfold leftMul leftSection
   apply mul_right_injective₀
   exact fun hz=>dcu aI (a.scale 6) Sum.inl Sum.inl_injective
     (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 · unfold rightMul rightSection
   apply mul_right_injective₀
   exact fun hz=>dcu aI (h.scale 6) Sum.inr Sum.inr_injective
     (Ideal.Quotient.eq_zero_iff_mem.mp hz)
end cya
end
section
namespace bRo
open aR dN BO as4 MvPolynomial
private theorem efF (a :Shape) (x :Fin 4→GeoField) :
   eval (fun i=>algebraMap GeoField (dV a) (x i)) (adK a)≠0:= by
 classical
 let m₀:uL a := fun _=>0
 have hm₀:m₀∈Bz a := by
   simp [Bz,m₀]
 let P:z3y (uL a) GeoField :=
   ∑ m∈Bz a,z9v m*C (∏ i:Fin 4,x i^(m i).val)
 let ρ:=algebraMap (z3y (uL a) GeoField) (dV a)
 have hmap : (algebraMap GeoField (dV a)) =
     ρ.comp (C (σ:=uL a) :GeoField →+* _) :=
   zYY GeoField (z3y (uL a) GeoField) (dV a)
 have heq :eval (fun i=>algebraMap GeoField (dV a) (x i)) (adK a) =
     ρ P:= by
   simp only [adK,P,ρ,map_sum,map_mul,map_prod,map_pow,
     z9X,zV6,hmap,zQb]
 let c:uL a→GeoField:= fun m=>if m=m₀ then 1 else 0
 have he :zY9 c P=1 := by
   simp only [P,map_sum,map_mul,zV6,z9X]
   rw [zpa m₀ hm₀]
   · simp [c,m₀]
   · intro m _ hm
     simp [c,hm]
 rw [heq]
 intro hz
 have hP:P=0:=(zxb (K:=dV a) _)
   (hz.trans (map_zero ρ).symm)
 rw [hP,map_zero] at he
 exact zero_ne_one he
private theorem efG (C₀:znc GeoJets) [hC₀:C₀.IsPrime] (a :Shape) :
   adK a∉C₀.map (zDK (algebraMap GeoField (dV a))) := by
 have hex : (zeroLocus GeoField C₀).Nonempty := by
   by_contra h
   apply hC₀.ne_top
   rw [← IsPrime.vanishingIdeal_zeroLocus (K:=GeoField) C₀,
     Set.not_nonempty_iff_eq_empty.mp h,vanishingIdeal_empty]
 obtain ⟨x,hx⟩:=hex
 let ι:=algebraMap GeoField (dV a)
 let e :adi a →+* dV a :=eval (ι ∘ x)
 have hle :C₀.map (zDK ι)≤zdq e := by
   apply Ideal.map_le_iff_le_comap.mpr
   intro p hp
   change eval (ι ∘ x) (zDK ι p)=0
   have hz :eval x p=0:= by simpa only [aeval_eq_eval] using hx p hp
   rw [eval_map,← eval₂_comp,hz,map_zero]
 exact fun h=>efF a x (hle h)
theorem proof :as4.c1 := by
 intro C₀ a hC₀ hdim
 let:C₀.IsPrime :=hC₀
 let I:=C₀.map (zDK (algebraMap GeoField (dV a)))
 have hI:I.IsPrime :=aA7.beK C₀ hC₀
 have hdeg: (affineHilbertPolynomial I).natDegree≤1 := by
  rw [show I= _ from rfl,Ey.ZI]
  exact axg.beu (d:=1) (P:=C₀) (by simpa using hdim.le)
 have hcut:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
  hI (efG C₀ a) le_rfl).1
 apply moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero
 exact za7 (hcut.trans (Nat.sub_eq_zero_of_le hdeg).le)
end bRo
end
section
namespace Qt
noncomputable section
open cu Finset
open scoped BigOperators
private theorem ddI (s :Shape) (g:ℕ→ℕ→ℕ) :
  (∑ j∈range (s.J+1),∑ q∈Ico j (s.B+1),g q j)=ku s g:= by
 have h (j:ℕ) : (range (s.B+1)).filter (j ≤ ·)=Ico j (s.B+1) := by
  ext q
  simp [and_comm]
 simp_rw [← h,sum_filter,ku]
 rw [sum_comm]
 apply sum_congr rfl
 intro q _
 rw [← sum_filter]
 congr 1
 ext j
 simp
 omega
private theorem deK (U:ℕ) :Antitone (slots U) := by
 intro a b hab
 by_cases hb:b≤U
 · have ha :=hab.trans hb
   rw [slots,ite_eq_left hb,slots,ite_eq_left ha]
   unfold triangle
   have h:=Nat.sub_le_sub_left hab U
   exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
 · simp [slots,hb]
private theorem df9 (A:ℕ→ℕ) (hm:Antitone A) (n L:ℕ) :
   (∑ r∈range n,if r<L then A r - A (r+1) else 0)+A (min n L)=A 0:= by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [sum_range_succ]
   by_cases h:n<L
   · rw [min_eq_left h.le] at ih
     rw [ite_eq_left h,min_eq_left (by omega :n+1≤L)]
     rw [add_assoc,zxt (hm (show n≤n+1 by omega))]
     exact ih
   · rw [min_eq_right (by omega :L≤n)] at ih
     rwa [ite_eq_right h,add_zero,min_eq_right (by omega :L≤n+1)]
private theorem crK (top j t d c:ℕ) (hj:j≤t) :
   (∑ W∈range top,if t≤W+j∧W+d<top then c else 0) =
     c*(top+j - t - d) := by
 have hI: (range top).filter (fun W=>t≤W+j∧W+d<top) =
     Ico (t - j) (top - d) := by
   ext W
   simp only [mem_filter,mem_range,mem_Ico]
   omega
 rw [← sum_filter,hI]
 have hwidth :top - d-(t - j)=top+j - t - d:= by omega
 simp [hwidth,z5A]
private theorem c49 (top step W j r :ℕ) (hW:W<top) (hs :0<step) :
  r<1+(top - 1-W)/step - j↔W+step*(j+r)<top:= by
 have h:r<1+(top - 1-W)/step - j↔j+r≤(top - 1-W)/step:= by omega
 rw [h,Nat.le_div_iff_mul_le hs,z5A (j+r)]
 omega
end
end Qt
end
section
namespace atb
noncomputable section
open Polynomial K1 aR dN wH lB Tx
open scoped BigOperators
private theorem cr1 {P:gQ} {H :Shape} (h:yy P H) :
   Supported H P:= by
 intro m hm
 refine ⟨?_,?_,?_⟩
 · exact (Finset.le_sup (f := fun a=>a.sum fun _ e=>e) hm).trans h.1
 · have hw:=(z6P Fin.val hm).trans h.2.1
   simpa only [zDM,smul_eq_mul,z5A] using hw
 · exact (MvPolynomial.le_degreeOf_of_mem_support _ hm).trans h.2.2
end
end atb
end
section
namespace bzJ
open aR dN BO lB
def c1 :Prop :=as4.c1
def c2 :Prop :=as4.c2
theorem of_children (h₁:c1) (h₂:c2) :aFW.c2 := by
  classical
  have count:aKp.c2 :=as4.of_children h₁ h₂
  intro a ha ht aI P C hC
  obtain ⟨hp,hdim⟩:=dOx hC
  have hunit :=dHS ha ht
  have bound (U:GeoJets) (points :zJe KE) (hU:yy U a) (hne :U∉C)
      (hpoints : ∀ y∈points,
        C≤zdq (zY9 y)∧zY9 y U=0) :
      6*points.card≤pN C (a.scale 6) :=
    count C a hp hdim hunit U hU hne points hpoints
  refine ⟨?_,bound⟩
  obtain ⟨y,U,hy,hU,hne,hzero⟩:=aKp.bDo hp hdim
  have hfit :yy U a :=
    ⟨hU.1.trans hunit.1,hU.2.1.trans hunit.2.1,hU.2.2.trans hunit.2.2⟩
  simpa only [Finset.card_singleton,Nat.mul_one] using
    bound U {y} hfit hne (by
      intro z hz
      rw [Finset.mem_singleton.mp hz]
      exact ⟨hy,hzero⟩)
end bzJ
end
