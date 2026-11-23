import ProximityPrize.SubmissionLower.ZoqNZ8b
set_option Elab.async false
open _root_ renaming AlgHom.comp_apply → zip, Fin.sum_univ_three → zCj, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.aevalTower_X → z57, MvPolynomial.monomial → ztt, Polynomial.X → z7y, Polynomial.aeval → zEU, Polynomial.toMvPolynomial → z3n, Submodule.sum_mem → zo3
set_option autoImplicit true
namespace qnRjM0a
noncomputable section
open Finset Polynomial
open scoped Polynomial BigOperators
open cu (L)
open jA (kS mA jH)
open NR (O8 Lq TT)
open P5_7_2 (TopRow)
open q7IA62d (capColumns)
open qje58fc (ModelIndex modelImage modelMatrix restoreMap testSpace mem_testSpace seedValue)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
private abbrev k :L →+* kS:=algebraMap _ _
private abbrev seedX:kS:=algebraMap L[X] kS z7y
private def δ (a c:L) (z :kS) :kS:=k a-k c*z
private theorem projective_identity {F:Type*} [Field F] {a d c x z :F}
  (ha :a≠0) (hd:d≠0) (h:z*(d+x*c)=a*x) :
  a-c*z≠0∧(a-c*z)*x=d*z := by
 have hp: (a-c*z)*(d+x*c)=a*d:= by linear_combination (-c)*h
 refine ⟨fun hn=>mul_ne_zero ha hd ?_,by linear_combination -h⟩
 rw [hn,zero_mul] at hp
 exact hp.symm
private theorem projective (a d c:L) (ha :a≠0) (hd:d≠0) :
  let z :=seedValue a d c
  δ a c z≠0∧δ a c z*seedX=k d*z := by
 dsimp only
 let z :=seedValue a d c
 let D:L[X] :=C d+Polynomial.X*C c
 have hD:D ≠0:= by
  intro h
  apply hd
  simpa [D] using congrArg (evalRingHom (0:L)) h
 have hD' := (map_ne_zero_iff _ (IsFractionRing.injective L[X] kS)).2 hD
 have hC (v :L) :algebraMap L[X] kS (C v)=k v :=
  (IsScalarTower.algebraMap_apply L L[X] kS v).symm
 have hden:algebraMap L[X] kS D =k d+seedX*k c:= by
  simp only [D,map_add,map_mul,hC]
 have hnum :algebraMap L[X] kS (C a*z7y)=k a*seedX:= by
  rw [map_mul,hC]
 have hz :z*(k d+seedX*k c)=k a*seedX:= by
  rw [← hden,← hnum]
  exact div_mul_cancel₀ _ hD'
 have hn (v :L) :k v≠0↔v≠0 :=
  map_ne_zero_iff k (FaithfulSMul.algebraMap_injective L kS)
 exact projective_identity ((hn a).mpr ha) ((hn d).mpr hd) hz
private def stock (a d c:L) (U l:ℕ) :L[X] :=
 (C d*z7y)^l*(C a-C c*z7y)^(U-l)
private theorem stock_bound (a d c:L) (U l:ℕ) (hl:l≤U) :
  (stock a d c U l).natDegree≤U:= by
 have hx (r :L) : (C r*z7y).natDegree≤1 := by
  simpa using natDegree_C_mul_X_pow_le r 1
 have hz : (C a-C c*z7y).natDegree≤1 :=
  (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_C]; omega) (hx c))
 exact (natDegree_mul_le_of_le (natDegree_pow_le_of_le _ (hx d))
  (natDegree_pow_le_of_le _ hz)).trans (by omega)
private theorem eval_stock (a d c:L) (U l:ℕ) (hl:l≤U) {z :kS}
  (hz :δ a c z*seedX=k d*z) :
  zEU z (stock a d c U l)=(δ a c z)^U*seedX^l:= by
 simp only [stock,map_mul,map_pow,map_sub,Polynomial.aeval_C,Polynomial.aeval_X]
 change (k d*z)^l*(δ a c z)^(U-l)= _
 rw [← hz,mul_pow,mul_right_comm,← pow_add,Nat.add_sub_of_le hl]
private def Ti:kS[X] →ₐ[L] Lq :=
 (Algebra.ofId kS[X] Lq).restrictScalars L
private def ao8:kS →ₐ[L] Lq :=
 Ti.comp ((Algebra.ofId kS kS[X]).restrictScalars L)
private theorem at_phys (α:L) (z :kS) (p:L[X]) :
   zIe (rawVar α z) ((p.taylor α).toMvPolynomial 0) =
     znf (p.map k) := by
 rw [MvPolynomial.aeval_toMvPolynomial]
 change zEU (Ti (O8 α)) (p.taylor α)=Ti (p.map k)
 rw [Polynomial.aeval_algHom,zip]
 congr 1
 rw [Polynomial.aeval_def,Polynomial.taylor_apply,Polynomial.eval₂_comp,
   Polynomial.eval₂_add,Polynomial.eval₂_X,Polynomial.eval₂_C,O8]
 change p.eval₂ _ (z7y-C (k α)+C (k α))= _
 rw [sub_add_cancel]
 rfl
private def bLu (α:L) (z :kS) :Fin 3→Lq :=
 fun j=>if j=0 then rawVar α z 1+rawVar α z 0*rawVar α z 2
  else if j=1 then rawVar α z 2+rawVar α z 0*rawVar α z 3
  else rawVar α z 3+rawVar α z 0*rawVar α z 4
private theorem restore_jet (α:L) (z :kS) (j:Fin 3) :
  restoreMap (z7y-C α) (C z) (z9v (some j))=bLu α z j:= by
 have hl:jH (z7y-C α)=O8 α:= by simp [jH,O8]
 have h₁:derivative (O8 α)=1 := by
  simp only [O8,derivative_sub,derivative_X,derivative_C,sub_zero]
 have h₂:hasseDeriv 2 (O8 α)=0:= by
  simp only [O8,map_sub,hasseDeriv_X 2 (by decide),
   hasseDeriv_C 2 _ (by decide),sub_zero]
 simp only [restoreMap,z57,Option.elim,hl,zCj]
 fin_cases j <;>
  norm_num [bLu,rawVar,seedConst,hasseDeriv_zero,hasseDeriv_C,h₁,h₂,add_assoc]
private theorem restore_mono (α:L) (z :kS) (m:mA →₀ ℕ) (p:L[X]) :
    restoreMap (z7y-C α) (C z) (ztt m p) =
      znf (p.map k)*seedConst seedX ^m none *
        bLu α z 0^m (some 0)*bLu α z 1^m (some 1) *
        bLu α z 2^m (some 2) := by
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype _ _ (fun _=>pow_zero _),
    Fintype.prod_option,Fin.prod_univ_three]
  have hc:restoreMap (z7y-C α) (C z) (znf p) =
      znf (p.map k) := by
    rw [restoreMap,MvPolynomial.aevalTower_C]
    rfl
  have hn:restoreMap (z7y-C α) (C z) (z9v none) =
      seedConst seedX:= by
    rw [restoreMap,z57]
    rfl
  simp only [map_mul,map_pow,hc,hn,restore_jet,mul_assoc]
private theorem cap_coordinates {t:TopRow} {m:mA →₀ ℕ} (hm:capColumns t m) :
  m (some 0)+m (some 1)+m (some 2)≤t.shape.B ∧
  m (some 1)+2*m (some 2)≤t.shape.J∧m (some 2)≤t.YM∧m none≤t.shape.U:= by
 simpa [capColumns,Finsupp.weight_eq_sum,Fintype.sum_option,zCj,
  smul_eq_mul,Nat.mul_comm] using hm
private abbrev x :Fin 5→Model:=z9v
private def Bo (m:mA →₀ ℕ) :Model :=
 (x 1+x 0*x 2)^m (some 0)*(x 2+x 0*x 3)^m (some 1)*(x 3+x 0*x 4)^m (some 2)
private theorem c48 {t:TopRow} (α:L) (z :kS)
   (m:mA →₀ ℕ) (hm:capColumns t m) (v j:ℕ) (hj:j<t.shape.U+1) :
   readModel α z _ (x 0^v*x 1^j*Bo m)∈modelRange t α z := by
 by_cases hv :v<t.shape.B+t.shape.J
 · obtain ⟨hB,hJ,hC,_⟩:=cap_coordinates hm
   let q:Fin (t.shape.B+1) :=⟨m (some 0)+m (some 1)+m (some 2),by omega⟩
   let c:Fin (min q.val (min t.YM (t.shape.J/2))+1) :=
     ⟨m (some 2),by simp only [q,Nat.lt_succ_iff,le_min_iff]; omega⟩
   let b:Fin (min (q.val-c.val) (t.shape.J-2*c.val)+1) :=
     ⟨m (some 1),by simp only [q,c,Nat.lt_succ_iff,le_min_iff]; omega⟩
   let i:ModelIndex t t.shape.U:=⟨q,⟨c,b⟩,⟨v,hv⟩,⟨j,hj⟩⟩
   have hy :q.val-c.val-b.val=m (some 0) := by dsimp [q,c,b]; omega
   simpa only [modelImage,i,hy,Bo,← mul_assoc] using read_column_mem α z i
 · have he :=read_power_high (α:= α) (z :=z) (Nat.le_of_not_gt hv)
   simp [he]
private theorem monomial_mem {t:TopRow} (α a d c:L) (z :kS)
   (hz :δ a c z*seedX=k d*z)
   (m:mA →₀ ℕ) (hm:capColumns t m) (p:L[X]) :
   poleMk α _ (seedConst ((δ a c z)^t.shape.U) *
     restoreMap (z7y-C α) (C z) (ztt m p))∈modelRange t α z := by
 classical
 let P:=p.taylor α
 let S:=stock a d c t.shape.U (m none)
 have hU:=(cap_coordinates hm).2.2.2
 have hS:zIe (rawVar α z) (S.toMvPolynomial 1) =
     seedConst ((δ a c z)^t.shape.U*seedX^m none) := by
   rw [MvPolynomial.aeval_toMvPolynomial]
   change zEU (ao8 z) S=ao8 _
   rw [Polynomial.aeval_algHom,zip,eval_stock _ _ _ _ _ hU hz]
 have hj:zIe (rawVar α z) (Bo m) =
     bLu α z 0^m (some 0)*bLu α z 1^m (some 1)*bLu α z 2^m (some 2) := by
   simp [Bo,bLu]
 have he :poleMk α (t.shape.B+t.shape.J) (seedConst ((δ a c z)^t.shape.U) *
     restoreMap (z7y-C α) (C z) (ztt m p)) =
     readModel α z _ (P.toMvPolynomial 0*S.toMvPolynomial 1*Bo m) := by
   change poleMk α _ _=poleMk α _ (zIe (rawVar α z) _)
   congr 1
   simp only [P,map_mul,map_pow,at_phys,hS,hj,restore_mono]
   ring
 rw [he]
 have hp:=P.as_sum_range_C_mul_X_pow
 have hs :=S.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le (stock_bound a d c _ _ hU))
 have hp' := congrArg (z3n (0:Fin 5) (R:=L)) hp
 have hs' := congrArg (z3n (1 :Fin 5) (R:=L)) hs
 simp only [map_sum,map_mul,map_pow,Polynomial.toMvPolynomial_C,Polynomial.toMvPolynomial_X] at hp' hs'
 simp only [hp',hs',Finset.sum_mul,Finset.mul_sum,map_sum]
 apply zo3
 intro j hj
 apply zo3
 intro v _
 have hmul : (znf (P.coeff v)*x 0^v) *
     (znf (S.coeff j)*x 1^j)*Bo m =
     (P.coeff v*S.coeff j)•(x 0^v*x 1^j*Bo m) := by
   rw [Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul]
   ring
 rw [hmul,map_smul]
 exact (modelRange t α z).smul_mem _ (c48 α z m hm v j (mem_range.mp hj))
theorem proof :qje58fc.c1 := by
 classical
 intro b e α a d c ha hd t V hV hcap
 let:Module.Finite L V:=hV
 let z :=seedValue a d c
 let n:=t.shape.B+t.shape.J
 let W:=testSpace (z7y-C α) (C z) (O8 α) n
 change TT V W≤(modelMatrix t).rank
 let f :V →ₗ[L] PoleQuot α n:=(poleMk α n).toLinearMap.comp
   ((LinearMap.mul L Lq (seedConst ((δ a c z)^t.shape.U))).comp
     ((restoreMap (z7y-C α) (C z)).toLinearMap.comp V.subtype))
 obtain ⟨hδ,hz⟩:=projective a d c ha hd
 have hker :f.ker=W.comap V.subtype := by
   ext F
   change poleMk α n (seedConst ((δ a c z)^t.shape.U) *
     restoreMap (z7y-C α) (C z) F.val)=0↔F.val∈W
   have hu:=((isUnit_iff_ne_zero.mpr (pow_ne_zero t.shape.U hδ)).map seedConst).map (poleMk α n)
   rw [map_mul,hu.mul_right_eq_zero,poleMk,Ideal.Quotient.mkₐ_eq_mk,
     Ideal.Quotient.eq_zero_iff_mem,poleIdeal,Ideal.mem_span_singleton,mem_testSpace]
 have hle :f.range≤ modelRange t α z := by
   rintro _ ⟨F,rfl⟩
   change poleMk α n (seedConst ((δ a c z)^t.shape.U) *
     restoreMap (z7y-C α) (C z) F.val)∈_
   rw [F.val.as_sum,map_sum,Finset.mul_sum,map_sum]
   exact zo3 _ fun m hm=>monomial_mem α a d c z hz m (hcap F.val F.property m hm) _
 have hf :=LinearMap.finrank_range_add_finrank_ker (K:=L) (V := ↥V) (V₂:=PoleQuot α n) f
 have hk :=Submodule.finrank_map_subtype_eq V f.ker
 rw [hker,Submodule.map_comap_subtype] at hk
 rw [hker] at hf
 have hr :TT V W=Module.finrank L f.range := by
   rw [TT,hk,← hf,Nat.add_sub_cancel]
 rw [hr]
 let:Module.Finite L (modelRange t α z) := by unfold modelRange; infer_instance
 exact (Submodule.finrank_mono hle).trans (modelRange_le t α z)
end
end qnRjM0a
