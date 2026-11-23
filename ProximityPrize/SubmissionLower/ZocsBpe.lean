import ProximityPrize.SubmissionLower.ZhkBS3a
import ProximityPrize.SubmissionLower.ZG9rwXd
import ProximityPrize.SubmissionLower.Zl7U3sa
set_option Elab.async false
open _root_ renaming Finsupp.add_apply → zSs, Finsupp.ext → zbm, Finsupp.le_degree → z1Q, Function.Injective → zq4, LinearMap.mulRight → zBm, Module.finrank → zsE, MvPolynomial.C → znf, MvPolynomial.uniqueAlgEquiv → zpe, Nat.add_le_add → z9f, Nat.card_eq_fintype_card → zey, Nat.le_of_lt_succ → zeh, Nat.lt_succ_of_le → zB1, Nat.mul_comm → z5A
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q89PToe
noncomputable section
open Polynomial Finset
open cu (L triangle)
open Y3 (Dg aLS bjn embed aka)
open qkgz7gb (Stock physicalStock)
open qt5AtZa (HeightLT)
open qbIP9ia
open private bg6 from ProximityPrize.SubmissionLower.BJ
private def flatAlg:Dg ≃ₐ[L] Flat :=AlgEquiv.ofRingEquiv (f :=flatten) fun c=> by
 apply flatten.symm.injective
 rw [RingEquiv.symm_apply_apply]
 change Polynomial.C (znf (Polynomial.C c)) =
  ((MvPolynomial.optionEquivLeft L (Fin 2 ⊕ Unit)) (znf c)).map bg6.toRingHom
 rw [MvPolynomial.optionEquivLeft_C,Polynomial.map_C]
 change _=C (MvPolynomial.map (zpe L Unit).toRingHom
  (MvPolynomial.sumRingEquiv L (Fin 2) Unit (znf c)))
 rw [MvPolynomial.sumRingEquiv_C,MvPolynomial.map_C]
 congr 2
 exact ((zpe L Unit).commutes c).symm
def SeedOK (s :Stock) (m:Fin 2 →₀ ℕ) :Prop :=
 match s with
 | .symmetric v=>m.degree≤v
 | .asymmetric z t=>m 0≤z∧m 1≤t
abbrev atZ (s :Stock) := {m:Fin 2 →₀ ℕ // SeedOK s m}
def rectIndex (z t:ℕ) :atZ (.asymmetric z t) ≃ Fin (z+1)×Fin (t+1) where
 toFun m:=(⟨m.val 0,zB1 m.property.1⟩,⟨m.val 1,zB1 m.property.2⟩)
 invFun i:=⟨seedMon i.1 i.2,⟨zeh i.1.isLt,zeh i.2.isLt⟩⟩
 left_inv m:=Subtype.ext (zbm fun i=> by fin_cases i <;> rfl)
 right_inv i:=Prod.ext (Fin.ext rfl) (Fin.ext rfl)
instance (s :Stock) :Finite (atZ s) := by
 cases s with
 | symmetric v=>exact (Finsupp.finite_of_degree_le v).to_subtype
 | asymmetric z t=>exact Finite.of_injective _ (rectIndex z t).injective
theorem goP (s :Stock) :Nat.card (atZ s)=s.size := by
 cases s with
 | symmetric v =>
   change {m:Fin 2 →₀ ℕ | m.degree≤v}.ncard=triangle v
   rw [Finsupp.ncard_setOf_degree_le]
   simp [triangle,Nat.choose_two_right,z5A (v+2)]
 | asymmetric z t =>
   rw [Nat.card_congr (rectIndex z t),Nat.card_prod,Nat.card_fin,Nat.card_fin]
   rfl
private theorem seed_add {s :Stock} {m n:Fin 2 →₀ ℕ} {u:ℕ}
   (hm:SeedOK s m) (hn:n.degree≤u) :SeedOK (s.cUr u) (m+n) := by
 cases s with
 | symmetric v =>
   change m.degree≤v at hm
   change (m+n).degree≤v+u
   rw [map_add]
   exact z9f hm hn
 | asymmetric z t =>
   change m 0≤z∧m 1≤t at hm
   exact ⟨z9f hm.1 ((z1Q 0 _).trans hn),
     z9f hm.2 ((z1Q 1 _).trans hn)⟩
private abbrev ax0 (n:ℕ) (w:ℕ→ℕ) (s :Stock) :=
 (Σ j:Fin n,Fin (w j))×atZ s
private def coord {n w s} (i:ax0 n w s) :Exps :=exps i.1.1 i.1.2 i.2.val
private theorem raw_exps (j k :ℕ) (m:Fin 2 →₀ ℕ) :ao8 (exps j k m)=m :=
 zbm fun i=> by rw [rawSeed_apply,exps_s]
private theorem coord_injective {n w s} : zq4 (@coord n w s) := by
 intro t u h
 have hy :=congrArg (fun m:Exps=>m none) h
 have hx :=congrArg (fun m:Exps=>m amm) h
 have hs :=congrArg (fun m:Exps=>ao8 m) h
 simp only [coord,exps_y,exps_x] at hy hx
 simp only [coord,raw_exps] at hs
 have he :t.1.1=u.1.1 :=Fin.ext hy
 exact Prod.ext (Sigma.ext he ((Fin.heq_ext_iff (congrArg (fun j:Fin n=>w j) he)).2 hx))
  (Subtype.ext hs)
private def input {n w s} : (ax0 n w s →₀ L) →ₗ[L] Flat :=
 (AddMonoidAlgebra.coeffLinearEquiv L).symm.toLinearMap.comp (Finsupp.lmapDomain L L coord)
private theorem input_injective {n w s} : zq4 (@input n w s) :=
 (AddMonoidAlgebra.coeffLinearEquiv L).symm.injective.comp
   (Finsupp.mapDomain_injective coord_injective)
private theorem input_caps {n M s} (H :ax0 n (fun _=>M) s →₀ L) {m:Exps}
  (hm:m∈(input H).support) :m none<n∧m amm<M∧SeedOK s (ao8 m) := by
 change m∈(Finsupp.mapDomain coord H).support at hm
 rw [Finsupp.mapDomain_support_of_injective coord_injective,Finset.mem_image] at hm
 obtain ⟨i,_,rfl⟩:=hm
 exact ⟨(exps_y ..) ▸ i.1.1.isLt,(exps_x ..) ▸ i.1.2.isLt,(raw_exps ..).symm ▸ i.2.property⟩
private theorem cp4 (n:ℕ) (w:ℕ→ℕ) (s :Stock) :
  Nat.card (ax0 n w s)=(∑ j:Fin n,w j)*s.size := by
 rw [Nat.card_prod,goP,zey,Fintype.card_sigma]
 simp only [Fintype.card_fin]
private theorem debit_sum (D E :ℕ) :
  (∑ j:Fin (E+1),j.val*D)=D*(E*(E+1)/2) := by
 rw [← Finset.sum_mul,Fin.sum_univ_eq_sum_range (fun j:ℕ=>j),Finset.sum_range_id,
  Nat.add_sub_cancel,z5A (E+1),z5A _ D]
private theorem seed_ne {F:Dg} {m:Exps} (hm:m∈(flatten F).support) :
  (F.coeff (m none)).coeff (ao8 m)≠0 :=
 fun hz=>MvPolynomial.mem_support_iff.mp hm (by rw [flat_coeff',hz,coeff_zero])
private theorem lead_mem {F:Dg} {j:ℕ} {m:Fin 2 →₀ ℕ} (hm: (F.coeff j).coeff m≠0) :
  exps j ((F.coeff j).coeff m).natDegree m∈(flatten F).support :=
 MvPolynomial.mem_support_iff.mpr (by rw [flat_coeff]; exact leadingCoeff_ne_zero.mpr hm)
private theorem output_fits {s :Stock} {G:Dg}
   (h : ∀ j m,(G.coeff j).coeff m≠0→SeedOK s m) :s.fits (embed G) := by
 have hs (j:ℕ) {m:Fin 2 →₀ ℕ} (hm:m∈((embed G).coeff j).support) :SeedOK s m:= by
   rw [embed,coe_mapRingHom,coeff_map] at hm
   exact h j m (MvPolynomial.mem_support_iff.mp (MvPolynomial.support_map_subset _ _ hm))
 cases s with
 | symmetric v=>exact fun j=>Finset.sup_le fun _ hm=>hs j hm
 | asymmetric z t =>
   exact fun j=>⟨MvPolynomial.degreeOf_le_iff.mpr (fun _ hm=>(hs j hm).1),
     MvPolynomial.degreeOf_le_iff.mpr (fun _ hm=>(hs j hm).2)⟩
private theorem prime_guard {Q:Dg} (hQ:bjn Q) :
  ¬ MvPolynomial.X amm∣flatten Q:= by
 obtain ⟨j,m,hm⟩:=hQ
 rw [MvPolynomial.X_dvd_iff_modMonomial_eq_zero]
 intro h
 have hv : ¬ Finsupp.single amm 1≤exps j 0 m:= by
  rw [Finsupp.single_le_iff,exps_x]
  omega
 have hz :=congrArg (fun A:Flat=>A.coeff (exps j 0 m)) h
 rw [MvPolynomial.coeff_modMonomial_of_not_le _ hv,flat_coeff] at hz
 exact hm hz
private theorem cut_injective {g M:ℕ} {s :Stock} {Q:Dg} (hQ:bjn Q) :
   zq4 ((rem M).comp ((zBm L (flatten Q)).comp
     (@input (g+1) (fun _=>M) s))) := by
 apply (injective_iff_map_eq_zero _).mpr
 intro H hz
 change rem M (input H*flatten Q)=0 at hz
 have hd:=rem_eq M (input H*flatten Q)
 rw [hz,zero_add] at hd
 have hh:=(MvPolynomial.X_prime (R:=L) (i:=amm)).pow_dvd_of_dvd_mul_right M
   (prime_guard hQ) ⟨_,hd⟩
 rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero] at hh
 apply input_injective
 rw [map_zero]
 apply MvPolynomial.ext
 intro m
 by_cases hm:m∈(input H).support
 · have hlt:=(input_caps H hm).2.1
   have he :=congrArg (fun A:Flat=>A.coeff m) hh
   simpa only [MvPolynomial.coeff_modMonomial_of_not_le _ (Finsupp.single_le_iff.not.mpr hlt.not_ge)]
     using he
 · exact MvPolynomial.notMem_support_iff.mp hm
private theorem cut_caps {g e u M:ℕ} {s :Stock} {Q:Dg}
  (hQe :Q.natDegree≤e) (hQu:aLS Q u)
  (H :ax0 (g+1) (fun _=>M) s →₀ L) {v :Exps}
  (hv :v∈(rem M (input H*flatten Q)).support) :
  v none<e+g+1∧v amm<M∧SeedOK (s.cUr u) (ao8 v) := by
 obtain ⟨hvprod,hlt⟩:=rem_support hv
 obtain ⟨a,ha,b,hb,heq⟩:=Finset.mem_add.mp (MvPolynomial.support_mul _ _ hvprod)
 obtain ⟨hi,_,hs⟩:=input_caps H ha
 have hbne :=seed_ne hb
 have hbe :b none≤e :=(le_natDegree_of_ne_zero fun hz=>hbne (by rw [hz]; rfl)).trans hQe
 have he :=congrArg (fun m:Exps=>m none) heq
 rw [zSs] at he
 have hq:=(MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hbne)).trans
  (hQu (b none))
 have ht:=seed_add hs hq
 have hraw:ao8 (a+b)=ao8 a+ao8 b :=
  zbm fun k=> by simp only [rawSeed_apply,zSs]
 rw [← hraw,heq] at ht
 exact ⟨by omega,hlt,ht⟩
theorem proof :qt5AtZa.c1 := by
  classical
  intro D e u w hw Q hQe hQu hQ0
  let E :=e+w.g
  let M:=w.modulus
  let s :=w.stock
  let I:=ax0 (w.g+1) (fun _=>M) s
  let J:=ax0 (E+1) (fun j=>j*D) (s.cUr u)
  let:Fintype I:=Fintype.ofFinite I
  let:Fintype J:=Fintype.ofFinite J
  let f :=flatten Q
  let cut: (I →₀ L) →ₗ[L] Flat :=(rem M).comp ((zBm L f).comp input)
  let pick (j:J) :Exps :=exps j.1.1 (M-1-j.1.2) j.2.val
  let test : (I →₀ L) →ₗ[L] (J→L) :=(LinearMap.pi fun j=>MvPolynomial.lcoeff L (pick j)).comp cut
  let out:=flatAlg.symm.toLinearMap.comp (cut.comp test.ker.subtype)
  have hc (H :test.ker) :flatten (out H)=cut H.val :=flatten.apply_symm_apply _
  have Ca (G:Dg) (hG:G∈out.range) :
      G.natDegree≤E∧(s.cUr u).fits (embed G)∧HeightLT D M G:= by
    obtain ⟨H,rfl⟩:=hG
    have caps {j:ℕ} {m:Fin 2 →₀ ℕ} (hm: ((out H).coeff j).coeff m≠0) :
        j<E+1∧(((out H).coeff j).coeff m).natDegree<M∧SeedOK (s.cUr u) m:= by
      have hv :exps j (((out H).coeff j).coeff m).natDegree m∈(cut H.val).support :=
        hc H ▸ lead_mem hm
      simpa only [exps_y,exps_x,raw_exps] using cut_caps hQe hQu H.val hv
    refine ⟨natDegree_le_iff_coeff_eq_zero.mpr ?_,output_fits fun _ _ hm=>(caps hm).2.2,?_⟩
    · intro j hj
      apply MvPolynomial.ext
      intro m
      show ((out H).coeff j).coeff m=0
      by_contra hm
      exact (Nat.not_lt_of_ge (Nat.succ_le_iff.mpr hj)) (caps hm).1
    · intro j m hm
      obtain ⟨hj,hk,ht⟩:=caps hm
      let k :=(((out H).coeff j).coeff m).natDegree
      have hv :exps j k m∈(cut H.val).support :=hc H ▸ lead_mem hm
      change k+j*D <M
      by_contra! hn
      let t:J:=⟨⟨⟨j,hj⟩,⟨M-1-k,by change M-1-k<j*D; omega⟩⟩,⟨m,ht⟩⟩
      have hz :=congrFun (LinearMap.mem_ker.mp H.property) t
      change (cut H.val).coeff (exps j (M-1-(M-1-k)) m)=0 at hz
      rw [show M-1-(M-1-k)=k by omega] at hz
      exact MvPolynomial.mem_support_iff.mp hv hz
  refine ⟨out.range,?_,fun G hG=>(Ca G hG).1,fun G hG=>(Ca G hG).2.1,
    fun G hG=>(Ca G hG).2.2,?_⟩
  · have hI:zsE L (I →₀ L)=(w.g+1)*M*s.size := by
      rw [Module.finrank_finsupp_self,← zey,cp4]
      simp
    have hJ:zsE L (J→L)=D*(E*(E+1)/2)*(s.cUr u).size := by
      rw [Module.finrank_fintype_fun_eq_card,← zey,cp4,debit_sum]
    have hr :=test.finrank_range_add_finrank_ker
    have hl:=test.range.finrank_le
    rw [hI] at hr
    rw [hJ] at hl
    have ho:zq4 out :=
      flatAlg.symm.injective.comp ((cut_injective hQ0).comp Subtype.val_injective)
    rw [LinearMap.finrank_range_of_inj ho]
    have hg: (D*(E*(E+1)/2)+physicalStock (M-w.weight-1) D)*(s.cUr u).size <
        (w.g+1)*M*s.size :=hw.2.2.2.2.1
    rw [Nat.add_mul] at hg
    change physicalStock (M-w.weight-1) D*(s.cUr u).size<zsE L test.ker
    omega
  · intro G hG
    obtain ⟨H,rfl⟩:=hG
    refine ⟨flatten.symm (input H.val),flatten.symm ((input H.val*f).divMonomial
      (Finsupp.single amm M)),?_⟩
    apply flatten.injective
    rw [map_mul,map_add,map_mul,flatten.apply_symm_apply,flatten.apply_symm_apply,hc,
      map_pow aka,map_pow flatten,flatten_X]
    exact rem_eq M _
end
end q89PToe
end
section
namespace qrezXJe
noncomputable section
open Polynomial Finset
open scoped WithZero
open qFD8jve (aFA sheetPole)
open E7 (Tq poleOrder)
open private cast_le_one from ProximityPrize.SubmissionLower.Z62SyBc
open private sum_le_all finite_tuple from ProximityPrize.SubmissionLower.ZG9rwXd
theorem resultant_val_le {A:Type} [CommRing A] (w:Valuation A ℤᵐ⁰)
   (F G:A[X]) (m n:ℕ) (b:ℤᵐ⁰)
   (hF : ∀ i,w (F.coeff i)≤b) (hG : ∀ i,w (G.coeff i)≤b) :
   w (F.resultant G m n)≤b^(m+n) := by
 classical
 let M:=F.sylvester G m n
 have hentry (i j:Fin (m+n)) :w (M i j)≤b:= by
   induction j using Fin.addCases with
   | left j =>
     simp only [M,sylvester,Matrix.of_apply,Fin.addCases_left]
     split
     · apply hG
     · simp
   | right j =>
     simp only [M,sylvester,Matrix.of_apply,Fin.addCases_right]
     split
     · apply hF
     · simp
 change w M.det≤_
 rw [Matrix.det_apply]
 apply w.map_sum_le
 intro σ _
 have hterm :w (∏ i,M (σ i) i)≤b^(m+n) := by
   rw [map_prod]
   calc
     _ ≤ ∏ _:Fin (m+n),b:=prod_le_prod fun i _=>hentry (σ i) i
     _ = _:= by simp
 rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
   simpa [hs,Valuation.map_neg] using hterm
theorem discriminant_bound {E :Type} [Field E] (w:Valuation E ℤᵐ⁰)
  (G:E[X]) (h:ℕ) (hG:polyBound w G h) :
  w (discriminantResultant G)≤WithZero.exp (( (2*G.natDegree-1)*h:ℕ) :ℤ) := by
 have hg (i:ℕ) :w (G.derivative.coeff i)≤WithZero.exp (h:ℤ) := by
  rw [coeff_derivative,map_mul]
  simpa only [mul_one,Nat.cast_succ] using
    mul_le_mul' (hG (i+1)) (cast_le_one (v :=w) (i+1))
 have hd:G.natDegree+(G.natDegree-1)=2*G.natDegree-1 := by omega
 unfold discriminantResultant
 exact (resultant_val_le w G G.derivative _ _ _ hG hg).trans_eq (by
  rw [hd,← WithZero.exp_nsmul]
  simp [mul_comm])
theorem sheet_bound {E :Type} [Field E] (w:Valuation E ℤᵐ⁰) (f :E[X][X]) :
   aFA w f (sheetPole w f) := by
 intro i j
 by_cases hn: ((f.coeff i).coeff j)=0
 · simp [hn]
 have hi:f.coeff i≠0:= fun h=>hn (by simp [h])
 have hid :i<f.natDegree+1 :=zB1 (le_natDegree_of_ne_zero hi)
 have hjd:j<(f.support.sup fun i=>(f.coeff i).natDegree)+1 := by
   exact zB1 ((le_natDegree_of_ne_zero hn).trans
    (Finset.le_sup (f := fun i=>(f.coeff i).natDegree) (mem_support_iff.mpr hi)))
 have hle :poleOrder w ((f.coeff i).coeff j)≤ sheetPole w f := by
   unfold sheetPole Tq
   exact Finset.le_sup_of_le (mem_univ (⟨i,hid⟩,⟨j,hjd⟩)) le_rfl
 apply (WithZero.log_le_iff_le_exp (w.zero_iff.not.mpr hn)).mp
 exact (Int.self_le_toNat _).trans (Int.ofNat_le.mpr hle)
theorem sum_zeroOrder {E ι:Type} [Field E] [Algebra cu.L E]
   (hdiv :E7.axV cu.L E)
   (T:Finset ι) (v :ι→E7.CurvePlace cu.L E)
   (hv :Set.InjOn v (T:Set ι)) (f :E[X][X]) (c:E) (k :ℕ)
   (hc:c≠0)
   (hb : ∀ w:E7.CurvePlace cu.L E,w.value c≤WithZero.exp ((k*sheetPole w.value f :ℕ) :ℤ)) :
   ∑ i∈T,E7.KB (v i).value c≤k*qb0hmCe.coeffHeight f := by
 classical
 obtain ⟨hp,hz,heq,_⟩:=hdiv c
 rw [← Finset.sum_image (f := fun w:E7.CurvePlace cu.L E =>
   E7.KB w.value c) hv]
 refine (sum_le_all _ hz _).trans ?_
 rw [← heq,finsum_eq_finsetSum_of_support_subset _ (s :=hp.toFinset)
   (fun w hw=>(Set.Finite.mem_toFinset _).mpr hw)]
 have hh (w:E7.CurvePlace cu.L E) :
     poleOrder w.value c≤k*sheetPole w.value f :=
   Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (w.value.zero_iff.not.mpr hc)).mpr (hb w))
 refine (sum_le_sum fun w _=>hh w).trans ?_
 rw [← Finset.mul_sum]
 apply Nat.mul_le_mul_left
 exact sum_le_all _ (finite_tuple hdiv _) _
end
end qrezXJe
end
