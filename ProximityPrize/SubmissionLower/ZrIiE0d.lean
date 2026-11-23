import ProximityPrize.SubmissionLower.ZeFfOZc
import ProximityPrize.SubmissionLower.Z1sUWDe
import ProximityPrize.SubmissionLower.A
set_option Elab.async false
open _root_ renaming Field → zrb, Fin.sum_univ_eq_sum_range → zdx, Finset.mem_univ → zTc, Finset.sum_apply → zpH, Finset.sum_congr → zUo, Fintype → z85, Function.Injective → zq4, Function.update → zWr, Function.update_of_ne → zBg, IsFractionRing.injective → zxb, IsScalarTower.algebraMap_apply → zG3, LinearIndependent → z14, Matrix → z30, Matrix.ext → zqQ, Matrix.map_mul → zwg, Matrix.mul_apply → zW3, Matrix.mul_assoc → zoE, MvPolynomial.X → z9v, MvPolynomial.degreeOf_mul_le → zbF, MvPolynomial.totalDegree_mul → zhM, Nat.lt_succ_of_le → zB1, Polynomial.X → z7y, Polynomial.toMvPolynomial_C → zMz, Polynomial.toMvPolynomial_X → zS0
section
set_option autoImplicit true
section
namespace aeL
noncomputable section
open cu (Shape ku)
open Ge (jJ bjM)
open agU (Bb arY ajD)
open scoped BigOperators
theorem beO (s :Shape) (t:Offset s) (q:jJ s) (i:ℕ)
   (hi:i<Bb s.B s.J t.val q.val) :
   Gv s t+i≤ min q.val s.J ∧
     t.val+(Gv s t+i) - s.J<s.B+s.J:= by
 change i< min q.val (min s.J (s.B+2*s.J - 1 - t.val))+1 -
   (s.J - t.val) at hi
 have hq:min q.val (min s.J (s.B+2*s.J - 1 - t.val))≤q.val :=min_le_left ..
 have hj:=(min_le_right q.val _).trans (min_le_left s.J (s.B+2*s.J - 1 - t.val))
 have ht:=(min_le_right q.val _).trans (min_le_right s.J (s.B+2*s.J - 1 - t.val))
 have htl:t.val<s.B+2*s.J:=t.isLt
 unfold Gv
 rw [le_min_iff]
 omega
private abbrev biV (s :Shape) :=Σ t:Offset s,Pivot s t
private abbrev byV (s :Shape) :=Σ q:jJ s,bjM s q.val
private def toLocal (s :Shape) (r :biV s) :byV s :=
 let t:=r.1
 let q:=r.2.1
 let i:=r.2.2.val
 let j:=Gv s t+i
 let x :=t.val+j - s.J
 have hi:i< min (Bb s.B s.J t.val q.val) (aIN s t q) :=r.2.2.isLt
 have hj:=(beO s t q i (hi.trans_le (min_le_left ..))).1
 have hrow:x<s.B+s.J - q.val := by
   have h:=hi.trans_le (min_le_right _ _)
   have hjJ:=hj.trans (min_le_right _ _)
   have hq:=q.isLt
   dsimp [x,j,Gv,aIN] at *
   omega
 ⟨q,⟨x,hrow⟩,⟨j,zB1 hj⟩⟩
private theorem gBR (s :Shape) :zq4 (toLocal s) := by
 rintro ⟨t,q,i⟩ ⟨t',q',i'⟩ h
 have hq:q=q' := congrArg Sigma.fst h
 have hx :=congrArg (fun y :byV s=>y.2.1.val) h
 have hj:=congrArg (fun y :byV s=>y.2.2.val) h
 change t.val+(Gv s t+i.val) - s.J =
  t'.val+(Gv s t' + i'.val) - s.J at hx
 change Gv s t+i.val=Gv s t' + i'.val at hj
 have ht:t=t' := by
  apply Fin.ext
  unfold Gv at hx hj
  omega
 subst t'
 subst q'
 have hi:i=i' := Fin.ext (by omega)
 subst i'
 rfl
private theorem gBS (s :Shape) :Function.Surjective (toLocal s) := by
 rintro ⟨q,x,j⟩
 have hq:=q.isLt
 have hx :=x.isLt
 have hj:j.val≤ min q.val s.J:=Nat.lt_succ_iff.mp j.isLt
 have hjq:=hj.trans (min_le_left _ _)
 have hjJ:=hj.trans (min_le_right _ _)
 let t:Offset s :=⟨x.val+s.J - j.val,by omega⟩
 have ht:t.val+j.val=x.val+s.J:= by dsimp [t]; omega
 have hfirst:Gv s t≤j.val := by unfold Gv; omega
 let i:=j.val-Gv s t
 have hji:Gv s t+i=j.val := by dsimp [i]; omega
 have hhigh:j.val≤ s.B+2*s.J - 1 - t.val := by omega
 have hcol:i<Bb s.B s.J t.val q.val := by
   unfold Bb
   change i< min q.val (min s.J (s.B+2*s.J - 1 - t.val))+1-Gv s t
   have hmin:=le_min hjq (le_min hjJ hhigh)
   omega
 have hrow:i<aIN s t q:= by
   unfold aIN
   unfold Gv at hji
   omega
 let r :biV s :=⟨t,q,⟨i,lt_min hcol hrow⟩⟩
 refine ⟨r,Sigma.ext rfl (heq_of_eq (Prod.ext (Fin.ext ?_) (Fin.ext ?_)))⟩
 · change t.val+(Gv s t+i) - s.J=x.val
   omega
 · exact hji
private theorem dsV (s :Shape) :
  Fintype.card (biV s)=arY s := by
 classical
 rw [Fintype.card_congr (Equiv.ofBijective _ ⟨gBR s,gBS s⟩)]
 simp only [byV,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,
  arY,ku]
 rw [zdx (fun q=>(s.B+s.J - q)*(min q s.J+1)) (s.B+1)]
 apply zUo rfl
 intro q _
 simp [Nat.mul_comm]
def aJo (s :Shape) :Fin (arY s) ≃ biV s :=
 (Fintype.equivFinOfCardEq (dsV s)).symm
theorem fY5 (s :Shape) (d : ∀ t:Offset s,Pivot s t→ℕ)
  (hd : ∀ t,(∑ r,d t r)≤agU.aDY s.B s.J t.val) :
  (∑ k,d (aJo s k).1 (aJo s k).2)≤ajD s.B s.J:= by
 calc
  _ = ∑ k :biV s,d k.1 k.2 :=
    Fintype.sum_equiv (aJo s) _ _ (fun _=>rfl)
  _ = ∑ t:Offset s,∑ r,d t r :=Fintype.sum_sigma _
  _ ≤ ∑ t:Offset s,agU.aDY s.B s.J t.val :=
    Finset.sum_le_sum fun t _=>hd t
  _ = _:=zdx _ _
end
end aeL
end
section
namespace aeL
noncomputable section
open Matrix
open scoped BigOperators Matrix
private def consecutive {R:Type} [Semiring R] (l m:ℕ) :z30 (Fin m) (Fin m) R :=
 fun i j=>((l+j.val).choose i.val :R)
private theorem cHK {R:Type} [CommRing R] (l m:ℕ) :
    (consecutive (R:=R) l m).det=1 := by
  let L:z30 (Fin m) (Fin m) R:= fun i k =>
    if k.val≤ i.val then (l.choose (i.val - k.val) :R) else 0
  let U:z30 (Fin m) (Fin m) R:= fun k j=>(j.val.choose k.val :R)
  have hLU:consecutive l m=L*U:= by
    ext i j
    rw [zW3]
    change ((l+j.val).choose i.val :R) =
      ∑ k :Fin m,
        (if k.val≤ i.val then (l.choose (i.val - k.val) :R) else 0) *
          (j.val.choose k.val :R)
    rw [Nat.add_comm l j.val,Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Nat.cast_sum,
      zdx (fun k =>
        (if k≤ i.val then (l.choose (i.val - k) :R) else 0)*(j.val.choose k :R)) m]
    calc
      _ = ∑ k∈Finset.range (i.val+1),
          (if k≤ i.val then (l.choose (i.val - k) :R) else 0)*(j.val.choose k :R) := by
        apply zUo rfl
        intro k hk
        simp [Nat.lt_succ_iff.mp (Finset.mem_range.mp hk),mul_comm]
      _ = _:= by
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt i.isLt))
        intro k _ hk
        have hki : ¬ k≤ i.val := fun h=>hk (Finset.mem_range.mpr (zB1 h))
        simp [hki]
  have hL:L.IsLowerTriangular := by
    intro i k hik
    change (if k.val≤ i.val then (l.choose (i.val - k.val) :R) else 0)=0
    exact ite_eq_right (not_le_of_gt (show i.val<k.val from hik))
  have hU:U.IsUpperTriangular := by
    intro i j hij
    change (j.val.choose i.val :R)=0
    rw [Nat.choose_eq_zero_of_lt (show j.val< i.val from hij),Nat.cast_zero]
  rw [hLU,Matrix.det_mul,Matrix.det_of_isLowerTriangular L hL,Matrix.det_of_isUpperTriangular hU]
  simp [L,U]
theorem eKK (F:Type) [zrb F] (l n h:ℕ) :dqg F l n h:= by
 let e :Fin (min n h) ↪ Fin n:=Fin.castLEEmb (min_le_left n h)
 refine ⟨e,?_⟩
 change (consecutive (R:=F) l (min n h)).det≠0
 rw [cHK]
 exact one_ne_zero
theorem eKM (F:Type) [zrb F] (l n h:ℕ) :bTl F l n h:= by
 classical
 intro i hi
 unfold btx
 by_cases hle :h≤n
 · rw [min_eq_right hle]
   let k :Fin h:=⟨i,hi⟩
   refine ⟨fun r=>if r=k then 1 else 0,fun j => ?_⟩
   rw [Finset.sum_eq_single_of_mem k (zTc k)]
   · simp [k]
   · intro r _ hne
     simp [hne]
 · rw [min_eq_left (le_of_not_ge hle)]
   let B:=consecutive (R:=F) l n
   have hB:B.det=1 :=cHK l n
   let:Invertible B:=B.invertibleOfIsUnitDet (hB.symm ▸ isUnit_one)
   let v :Fin n→F:= fun j=>((l+j.val).choose i:F)
   refine ⟨v ᵥ* ⅟B,fun j => ?_⟩
   change v j=((v ᵥ* ⅟B) ᵥ* B) j
   rw [Matrix.vecMul_vecMul,invOf_mul_self,Matrix.vecMul_one]
end
end aeL
end
section
set_option backward.isDefEq.respectTransparency false
namespace aSk
noncomputable section
open Polynomial Matrix
open scoped Polynomial BigOperators
variable {F ι κ:Type} [zrb F] [z85 ι] [DecidableEq ι] [z85 κ]
local notation "K" => aeL.Ru F
local notation "φ" => algebraMap F[X] K
private theorem afo (M:z30 ι κ K) (e :ι ↪ κ)
   (he : (M.submatrix id e).det≠0) :
   ∃ (A:z30 ι κ F[X]) (b:K),b≠0∧A.map φ=b•M ∧
     (A.submatrix id e).det≠0:= by
 classical
 obtain ⟨b,hb⟩:=IsLocalization.exist_integer_multiples_of_finite
   (nonZeroDivisors F[X]) (fun p:ι×κ=>M p.1 p.2)
 choose a ha using hb
 let A:z30 ι κ F[X] := fun i j=>a (i,j)
 have hmap :A.map φ=φ b•M:= by
   apply zqQ
   intro i j
   change φ (a (i,j))=φ b*M i j
   simpa only [Algebra.smul_def] using ha (i,j)
 have hb0:φ b≠0 :=
   fun h=>(nonZeroDivisors.ne_zero b.property)
     (zxb F[X] K (h.trans (map_zero φ).symm))
 refine ⟨A,φ b,hb0,hmap,?_⟩
 intro h
 have hdet:φ (A.submatrix id e).det=(φ b•M.submatrix id e).det:= by
   rw [RingHom.map_det]
   exact congrArg Matrix.det (congrArg (fun B:z30 ι κ K=>B.submatrix id e) hmap)
 rw [h,map_zero,Matrix.det_smul] at hdet
 exact (mul_ne_zero (pow_ne_zero _ hb0) he) hdet.symm
theorem d4U (M:z30 ι κ K)
   (hM : ∃ e :ι ↪ κ,(M.submatrix id e).det≠0) :
   ∃ (Q:z30 ι κ F[X]) (T:z30 κ ι F[X]) (L:z30 ι ι K),
     Q*T=1∧M=L*Q.map φ:= by
 classical
 obtain ⟨e,he⟩:=hM
 obtain ⟨A,b,hb,hA,hminor⟩:=afo M e he
 let N :=LinearMap.range A.vecMulLinear
 have hAi:zq4 A.vecMulLinear := by
   intro x y hxy
   apply Matrix.vecMul_injective_iff.mpr (Matrix.linearIndependent_rows_of_det_ne_zero hminor)
   exact funext fun j=>congrFun hxy (e j)
 have hN :Module.finrank F[X] N=Fintype.card ι:= by
   rw [LinearMap.finrank_range_of_inj hAi,Module.finrank_pi]
 obtain ⟨n,S⟩:=N.smithNormalForm (Pi.basisFun F[X] κ)
 let re :ι ≃ Fin n:=Fintype.equivOfCardEq (by
   rw [← Module.finrank_eq_card_basis S.bN,hN])
 let Q:z30 ι κ F[X] := fun i=>S.bM (S.f (re i))
 let T:z30 κ ι F[X] := fun j i=>S.bM.coord (S.f (re i)) (Pi.single j 1)
 have hQT:Q*T=1 := by
   apply zqQ
   intro i j
   have hsum: (∑ k :κ,Q i k•(Pi.single k 1 :κ→F[X]))= Q i:= by
     funext k
     simp [zpH,Pi.smul_apply,Pi.single_apply,mul_ite]
   have hcoord:=congrArg (S.bM.coord (S.f (re j))) hsum
   simp only [map_sum,map_smul,smul_eq_mul] at hcoord
   change (∑ k :κ,Q i k*S.bM.coord (S.f (re j)) (Pi.single k 1))= _
   rw [hcoord]
   change S.bM.coord (S.f (re j)) (S.bM (S.f (re i)))= _
   simp only [Module.Basis.coord_apply,Module.Basis.repr_self_apply,Matrix.one_apply,
     EmbeddingLike.apply_eq_iff_eq]
 have hrow (i:ι) :A i∈N := by
   refine ⟨Pi.single i 1,?_⟩
   exact Matrix.single_one_vecMul i A
 let W:z30 ι ι F[X] := fun i j=>S.bN.repr ⟨A i,hrow i⟩ (re j)*S.a (re j)
 have hW:W*Q=A:= by
   apply zqQ
   intro i j
   have hsum:=S.bN.sum_repr ⟨A i,hrow i⟩
   let l:N →ₗ[F[X]] F[X] :=(LinearMap.proj j).comp N.subtype
   have hc:=congrArg l hsum
   rw [zW3,← Equiv.sum_comp re.symm]
   simpa only [l,map_sum,map_smul,LinearMap.comp_apply,LinearMap.proj_apply,
     Submodule.subtype_apply,W,Q,S.snf,Equiv.apply_symm_apply,← mul_assoc,
     Pi.smul_apply,smul_eq_mul] using hc
 refine ⟨Q,T,b⁻¹•W.map φ,hQT,?_⟩
 have h:=congrArg (fun B:z30 ι κ F[X]=>B.map φ) hW
 rw [zwg,hA] at h
 rw [Matrix.smul_mul,h,smul_smul,inv_mul_cancel₀ hb,one_smul]
end
end aSk
end
end
section
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace aSk
noncomputable section
open Polynomial Matrix
open scoped Polynomial BigOperators
variable {F ι κ:Type} [zrb F] [z85 ι] [DecidableEq ι] [z85 κ]
local notation "K" => aeL.Ru F
local notation "φ" => algebraMap F[X] K
def a5a (Q:z30 ι κ F[X]) (d:ι→ℕ) :z30 ι κ F :=
 fun i j=>(Q i j).coeff (d i)
omit [z85 ι] in
private theorem eEV {Q:z30 ι κ F[X]} {T:z30 κ ι F[X]}
  (h:Q*T=1) (p:ι) :Q p≠0:= by
 intro hp
 have hpp:=congrFun (congrFun h p) p
 rw [zW3,hp] at hpp
 simp at hpp
private theorem fVe (Q:z30 ι κ F[X]) (T:z30 κ ι F[X]) (d:ι→ℕ)
    (hQT:Q*T=1) (hdeg : ∀ r u,(Q r u).natDegree≤d r)
    (hbad : ¬ z14 F (a5a Q d).row) :
    ∃ (E :z30 ι ι F[X]) (d' : ι→ℕ),IsUnit E.det ∧
      (∀ r u,((E*Q) r u).natDegree≤d' r)∧(∑ r,d' r) < ∑ r,d r := by
  classical
  rw [Fintype.linearIndependent_iff] at hbad
  push Not at hbad
  obtain ⟨a,ha,i,hi⟩:=hbad
  let s :=Finset.univ.filter (fun i=>a i≠0)
  have hs :s.Nonempty :=⟨i,Finset.mem_filter.mpr ⟨zTc _,hi⟩⟩
  obtain ⟨p,hp,hmax⟩:=s.exists_max_image d hs
  have hap:a p≠0:=(Finset.mem_filter.mp hp).2
  have hle (r :ι) (hr :a r≠0) :d r≤d p :=
    hmax r (Finset.mem_filter.mpr ⟨zTc _,hr⟩)
  let c (r :ι) :F[X] :=C (a r)*(z7y (R:=F))^(d p - d r)
  let E :=(1 :z30 ι ι F[X]).updateRow p c
  have hc:c p=C (a p) := by simp [c]
  have hE :IsUnit E.det:= by
    have hrow: (∑ k,c k•(1 :z30 ι ι F[X]) k)=c:= by
      rw [← Matrix.vecMul_eq_sum,Matrix.vecMul_one]
    change IsUnit ((1 :z30 ι ι F[X]).updateRow p c).det
    rw [← hrow,Matrix.det_updateRow_sum,Matrix.det_one,smul_eq_mul,mul_one,hc]
    exact (isUnit_iff_ne_zero.mpr hap).map C
  have hform :E*Q= Q.updateRow p (∑ r,c r•Q r) := by
    change (1 :z30 ι ι F[X]).updateRow p c*Q= _
    rw [Matrix.updateRow_mul,Matrix.one_mul,Matrix.vecMul_eq_sum]
  have hbound (u:κ) : ((E*Q) p u).natDegree≤d p:= by
    rw [hform,Matrix.updateRow_self,zpH]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r _
    by_cases hz :a r=0
    · simp [c,hz]
    · have hr :=hle r hz
      change ((C (a r)*(z7y (R:=F))^(d p - d r))*Q r u).natDegree≤_
      rw [mul_assoc]
      have hm: ((z7y (R:=F))^(d p - d r)*Q r u).natDegree ≤
          (d p - d r)+d r :=
        Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_X_pow_le _) (hdeg r u)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (hm.trans (by omega))
  have hcoeff (u:κ) : ((E*Q) p u).coeff (d p)=0:= by
    rw [hform,Matrix.updateRow_self,zpH,Polynomial.finsetSum_coeff]
    have hA:=congrFun ha u
    simp only [zpH,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hA
    rw [← hA]
    apply zUo rfl
    intro r _
    change ((C (a r)*(z7y (R:=F))^(d p - d r))*Q r u).coeff (d p) =
      a r*(Q r u).coeff (d r)
    rw [mul_assoc,Polynomial.coeff_C_mul]
    by_cases hz :a r=0
    · simp [hz]
    · congr 1
      have hr :=hle r hz
      have heq :d r+(d p - d r)=d p:= by omega
      exact (congrArg (((z7y (R:=F))^(d p - d r)*Q r u).coeff) heq.symm).trans
        (Polynomial.coeff_X_pow_mul _ _ _)
  have hpos :0<d p:= by
    by_contra! hp0
    have heq :d p=0:=Nat.eq_zero_of_le_zero hp0
    have hright: (E*Q)*(T*E⁻¹)=1 := by
      rw [zoE E,← zoE Q,hQT,Matrix.one_mul,
        Matrix.mul_nonsing_inv _ hE]
    apply eEV hright p
    funext u
    have hdeg0: ((E*Q) p u).natDegree≤0:=heq ▸ hbound u
    have hz : ((E*Q) p u).coeff 0=0:=heq ▸ hcoeff u
    change ((E*Q) p u)=0
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg0,hz,map_zero]
  let d' := zWr d p (d p - 1)
  refine ⟨E,d',hE,?_,?_⟩
  · intro r u
    by_cases hr :r=p
    · subst r
      change ((E*Q) p u).natDegree≤zWr d p (d p - 1) p
      rw [Function.update_self]
      exact Polynomial.natDegree_le_pred (hbound u) (hcoeff u)
    · rw [hform,Matrix.updateRow_ne hr]
      change (Q r u).natDegree≤zWr d p (d p - 1) r
      rw [zBg hr]
      exact hdeg r u
  · apply Finset.sum_lt_sum
    · intro r _
      by_cases hr :r=p
      · simp [d',hr]
      · simp [d',zBg hr]
    · exact ⟨p,zTc p,by simpa [d'] using Nat.sub_lt hpos (by decide :0<1)⟩
theorem d4I (M:z30 ι κ K)
    (hM : ∃ (Q:z30 ι κ F[X]) (T:z30 κ ι F[X]) (L:z30 ι ι K),
      Q*T=1∧M=L*Q.map φ) :
    ∃ (Q:z30 ι κ F[X]) (T:z30 κ ι F[X]) (L:z30 ι ι K) (d:ι→ℕ),
      Q*T=1∧M=L*Q.map φ ∧
      (∀ r u,(Q r u).natDegree≤d r)∧z14 F (a5a Q d).row:= by
  classical
  let P (n:ℕ) :=
    ∃ (Q:z30 ι κ F[X]) (T:z30 κ ι F[X]) (L:z30 ι ι K) (d:ι→ℕ),
      Q*T=1∧M=L*Q.map φ∧(∀ r u,(Q r u).natDegree≤d r)∧(∑ r,d r)=n
  have hP : ∃ n,P n:= by
    obtain ⟨Q,T,L,hQT,hL⟩:=hM
    let d (i:ι) :=Finset.univ.sup (fun u:κ=>(Q i u).natDegree)
    exact ⟨_,Q,T,L,d,hQT,hL,fun r u=>Finset.le_sup (f := fun v :κ=>(Q r v).natDegree) (zTc u),rfl⟩
  obtain ⟨Q,T,L,d,hQT,hL,hdeg,hn⟩:=Nat.find_spec hP
  refine ⟨Q,T,L,d,hQT,hL,hdeg,?_⟩
  by_contra hbad
  obtain ⟨E,d',hE,hdeg',hlt⟩:=fVe Q T d hQT hdeg hbad
  let V:=E⁻¹
  have hEV:E*V=1 :=Matrix.mul_nonsing_inv _ hE
  have hVE :V*E=1 :=Matrix.nonsing_inv_mul _ hE
  have hnew :P (∑ i,d' i) := by
    refine ⟨E*Q,T*V,L*V.map φ,d',?_,?_,hdeg',rfl⟩
    · rw [zoE E,← zoE Q,hQT,Matrix.one_mul,hEV]
    · rw [zwg,zoE L,← zoE (V.map φ),
        ← zwg,hVE,Matrix.map_one _ (map_zero φ) (map_one φ),
        Matrix.one_mul,hL]
  exact (not_lt_of_ge (Nat.find_min' hP hnew)) (hn ▸ hlt)
end
end aSk
end
section
set_option backward.isDefEq.respectTransparency false
namespace aeL
noncomputable section
open Polynomial Matrix
open cu (Shape)
open DP (CI)
open Ge anc
open scoped BigOperators Matrix Polynomial
open private dg1 dc3 dmc from ProximityPrize.SubmissionLower.Z
private def pO (F:Type) [zrb F] (side :Fin 2) :F[X] →+* kq F :=
 (algebraMap (i5 F) (kq F)).comp (Polynomial.toMvPolynomial side).toRingHom
private def bqm (F:Type) [zrb F] (side :Fin 2) :
  Ru F →+* kq F :=
 IsFractionRing.lift (g:=pO F side)
  ((zxb (i5 F) (kq F)).comp
    (Polynomial.toMvPolynomial_injective side))
private theorem b3T {F:Type} [zrb F] (side :Fin 2) (g:F[X]) :
   bqm F side (algebraMap F[X] (Ru F) g) =
     algebraMap (i5 F) (kq F) (g.toMvPolynomial side) := by
 rw [bqm,IsFractionRing.lift_algebraMap]
 rfl
private theorem edS {F:Type} [zrb F] (side :Fin 2) (a :F) :
   bqm F side (algebraMap F (Ru F) a) =
     algebraMap F (kq F) a := by
 rw [zG3 F F[X] (Ru F),b3T]
 change algebraMap (i5 F) (kq F) ((Polynomial.C a).toMvPolynomial side)= _
 rw [zMz]
 exact (zG3 F (i5 F) (kq F) a).symm
private theorem edR {F:Type} [zrb F] (side :Fin 2) (a b c:F) :
  bqm F side (a6h a b c)=residue side a b c:= by
 simp only [a6h,residue,map_div₀,map_add,map_mul,edS,
  b3T,zS0]
def btV {F:Type} [zrb F] {s :Shape} {t:Offset s}
    (α:F) (side :Fin 2) (v :Lh s t→F[X]) :Gm F →ₗ[F] i5 F :=
  ∑ u,(v u).toMvPolynomial side•input α u
private theorem c4M {F:Type} [zrb F] {s :Shape} {t:Offset s}
  (α:F) (side :Fin 2) (v :Lh s t→F[X]) (P:Gm F) :
  btV α side v P = ∑ u,(v u).toMvPolynomial side*input α u P:= by
 simp only [btV,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
private theorem gqX {F:Type} [zrb F] (side :Fin 2) (p:F[X]) :
   (p.toMvPolynomial side).degreeOf (CI side)≤0 ∧
   (p.toMvPolynomial side).totalDegree≤p.natDegree := by
 classical
 have hsum:p.toMvPolynomial side =
     ∑ k∈p.support,MvPolynomial.C (p.coeff k)*z9v side^k := by
   conv_lhs=>rw [p.as_sum_support_C_mul_X_pow]
   simp only [map_sum,map_mul,map_pow,zMz,
     zS0]
 have hne :CI side≠side := by fin_cases side <;> decide
 rw [hsum]
 constructor
 · refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
   refine (zbF _ _ _).trans ?_
   simpa [MvPolynomial.degreeOf_X_of_ne hne] using
     MvPolynomial.degreeOf_pow_le (CI side) (z9v (R:=F) side) k
 · apply MvPolynomial.totalDegree_finsetSum_le
   intro k hk
   refine (zhM _ _).trans ?_
   rw [MvPolynomial.totalDegree_C,zero_add]
   exact ((MvPolynomial.totalDegree_pow (z9v (R:=F) side) k).trans
     (by simp)).trans (Polynomial.le_natDegree_of_mem_supp k hk)
theorem eMZ {F:Type} [zrb F] {s :Shape} {t:Offset s}
   (α:F) (side :Fin 2) (v :Lh s t→F[X]) {d:ℕ}
   (hd : ∀ u,(v u).natDegree≤d) {P:Gm F} (hP:adk s P) :
   bbs s.U d side (btV α side v P) := by
 rw [c4M]
 apply dmc
 intro u
 let f :=(v u).toMvPolynomial side
 let g:=input α u P
 have hf :=gqX side (v u)
 have hg:g.totalDegree≤ s.U:=dg1 s α P hP _ _ _
 have hother : (f * g).degreeOf (CI side)≤ s.U:= by
   refine (zbF _ _ _).trans ?_
   exact (Nat.add_le_add hf.1 ((MvPolynomial.degreeOf_le_totalDegree g _).trans hg)).trans_eq
     (Nat.zero_add _)
 have htotal: (f * g).totalDegree≤ s.U + d :=
   (zhM _ _).trans
     ((Nat.add_le_add (hf.2.trans (hd u)) hg).trans_eq (Nat.add_comm _ _))
 intro e he
 have hMem:e∈(f * g).support :=MvPolynomial.mem_support_iff.mpr he
 refine ⟨(MvPolynomial.le_degreeOf_of_mem_support _ hMem).trans hother,?_⟩
 rw [← dc3 side e]
 exact (show DP.Tl e≤_ from MvPolynomial.le_totalDegree hMem).trans htotal
theorem eM0 {F:Type} [zrb F] {s :Shape} (t:Offset s)
   (α:F) (side :Fin 2) (a b c:F) (P:Gm F)
   (Q:z30 (Pivot s t) (Lh s t) F[X])
   (L:z30 (Pivot s t) (Pivot s t) (Ru F))
   (hL:Pa s t (a6h a b c)=L*Q.map (algebraMap F[X] (Ru F)))
   (hz : ∀ r,btV α side (Q r) P=0) :
   Pa s t (residue side a b c) *ᵥ
     (fun u=>algebraMap (i5 F) (kq F) (input α u P))=0:= by
 let f :=bqm F side
 let V:Lh s t→kq F:= fun u=>algebraMap (i5 F) (kq F) (input α u P)
 let Q' : z30 (Pivot s t) (Lh s t) (kq F) := Q.map (pO F side)
 have hM: (Pa s t (a6h a b c)).map f=Pa s t (residue side a b c) := by
   ext r u
   simp only [Matrix.map_apply,Pa,f,apply_ite,map_zero,map_mul,map_natCast,
     map_pow,edR]
   split_ifs <;> rfl
 have hQ: (Q.map (algebraMap F[X] (Ru F))).map f= Q' := by
   ext r u
   exact b3T side (Q r u)
 have hV:Q' *ᵥ V=0:= by
   funext r
   change (∑ u,algebraMap (i5 F) (kq F) ((Q r u).toMvPolynomial side) *
     algebraMap (i5 F) (kq F) (input α u P))=0
   have hh:=congrArg (algebraMap (i5 F) (kq F)) (hz r)
   simpa only [c4M,map_sum,map_mul,map_zero] using hh
 change Pa s t (residue side a b c) *ᵥ V=0
 rw [← hM,hL,zwg,hQ,← Matrix.mulVec_mulVec,hV,Matrix.mulVec_zero]
end
end aeL
end
end
