import ProximityPrize.SubmissionLower.ZBlkecd
import ProximityPrize.SubmissionLower.ZFAtzgb
import ProximityPrize.SubmissionLower.ZZNStjd
import ProximityPrize.SubmissionLower.ZF73i6b
import ProximityPrize.SubmissionLower.ZwO1rQb
import ProximityPrize.SubmissionLower.ZitKCce
import ProximityPrize.SubmissionLower.AU
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.ZQ2Yete
import ProximityPrize.SubmissionLower.ZS4VEna
import ProximityPrize.SubmissionLower.ZULJdud
import ProximityPrize.SubmissionLower.A8
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.C3
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.CH
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.ZBRA0Kc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZaQt7ib
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qp56ikd
noncomputable section

open P5_7_2 (fO)
open q7F2qKe (wX lineFee weakAgreement)
open qzVScmb (LineRow LineCaps)
open qckEfrc (Box)
open cu (Jet)
open akZ (yE)
open Finset MvPolynomial
open scoped Polynomial




open private le_ceil from ProximityPrize.SubmissionLower.Z77J3Nc
private abbrev e := _root_.finSuccEquiv 2
private theorem rename_caps {f :Jet} {g:LineRow} (h:LineCaps f g) :
   rename e g∈Box (yE f 0) (yE f 1) (yE f 2) := by
 classical
 rw [mem_restrictCappedBidegree]
 intro m hm
 rw [support_rename_of_injective e.injective] at hm
 obtain ⟨n,hn,rfl⟩:=mem_image.mp hm
 obtain ⟨hb,hj,hu⟩:=h n hn
 refine ⟨?_,?_,?_⟩
 · change n.mapDomain e (e 0)≤_
   rwa [Finsupp.mapDomain_apply_of_injective e.injective]
 · change (n.mapDomain e).some.degree≤_
   rw [Finsupp.degree_eq_sum,Fin.sum_univ_two]
   change n.mapDomain e (e 1)+n.mapDomain e (e 2)≤_
   simpa only [Finsupp.mapDomain_apply_of_injective e.injective] using hb
 · change n.mapDomain e (e 2)≤_
   rwa [Finsupp.mapDomain_apply_of_injective e.injective]
private theorem Bh {n m c k err g:ℕ} (hg:0<g)
  (h: (g:ℚ)*n≤2*err*m+g*k) :
  n≤(2*(err :ℚ)/g*(m+c:ℕ)).ceil.toNat+k := by
 let r :ℚ:=2*(err :ℚ)/g*(m+c:ℕ)
 have hmg:2*(err :ℚ)*m≤2*err*(m+c:ℕ) :=
  mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.le_add_right m c)) (by positivity)
 have hx : (n:ℚ)-k≤ r := by
  dsimp only [r]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (Nat.cast_pos.mpr hg)).2
  linarith only [h,hmg]
 have h' := (sub_le_iff_le_add.mp hx).trans (add_le_add (le_ceil r) le_rfl)
 change n≤ r.ceil.toNat+k
 exact Nat.cast_le.mp (by simpa only [Nat.cast_add] using h')
private theorem bw {b:fO} {n B J U:ℕ} (hd:wX b<weakAgreement)
   (h: (gap (wX b) :ℚ)*n≤2*errors*kK (wX b) B J U+
     gap (wX b)*(B+U:ℕ)) :
   n≤lineFee b ![B,J,U] := by
 let d:=wX b
 let a :=total d B
 let v :=top d B J
 let t:=seed d U
 let c:=U*(2*a+v)+t*(2*B+J)+B*v+J*a+U+B+J
 have hm:kK d B J U=U*(2*a*v-v*v)+2*t*(B*v+J*(a-v)) := by
   rw [kK,cappedBidegreeMixedVolume_eq (show v≤a from min_le_left _ _)]
   change U*v*(2*a-v)+2*t*(B*v+J*(a-v))= _
   rw [Nat.mul_assoc U v,Nat.mul_sub_left_distrib,mul_comm v (2*a)]
 have hi:=Bh (c:=c) (Nat.sub_pos_of_lt hd) h
 rw [hm] at hi
 let cost:=(2*(errors :ℚ)/gap d*(U*(2*a*v-v*v)+2*t*(B*v+J*(a-v))+c:ℕ)).ceil.toNat
 change n≤ cost+(B+U) at hi
 change n≤ cost+B+U+1
 exact (hi.trans_eq (Nat.add_assoc _ _ _).symm).trans (Nat.le_succ _)
end
end qp56ikd
end
section
namespace qeFnRJb
noncomputable section
open Polynomial
open qZu9hjc (atPair physicalDeriv jacobian)
open q8Z6NHc (jo Generic Slot form genericF genericG)
open qG7TGJa (aFB value)
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
private theorem atPair_natural {K E F:Type} [Field K] [Field E] [Field F]
  (j:E →+* F) (k :K →+* E) (x y :E) (f :K[X][X]) :
  j (atPair k x y f)=atPair (j.comp k) (j x) (j y) f := by
 rw [atPair,atPair,hom_eval₂]
 apply congrArg (fun h:K[X] →+* F=>f.eval₂ h (j y))
 apply RingHom.ext
 intro r
 exact hom_eval₂ r k j x
private theorem atPair_map {K E :Type} [Field K] [Field E]
  (j:K →+* E) (x y :E) (f :K[X][X]) :
  atPair (RingHom.id E) x y (f.map (mapRingHom j))=atPair j x y f := by
 rw [atPair,atPair,eval₂_map]
 apply congrArg (fun h:K[X] →+* E=>f.eval₂ h y)
 apply RingHom.ext
 intro r
 change (r.map j).eval₂ (RingHom.id E) x=r.eval₂ j x
 rw [eval₂_map,RingHom.id_comp]
private theorem physical_map {K E :Type} [Field K] [Field E]
   (j:K →+* E) (f :K[X][X]) :
   physicalDeriv (f.map (mapRingHom j))=(physicalDeriv f).map (mapRingHom j) := by
 have h {T:Type} [Field T] (r :T[X][X]) (n:ℕ) :
     (physicalDeriv r).coeff n=(r.coeff n).derivative := by
   rw [physicalDeriv,sum_coeff _ derivative_zero]
 ext n m
 simp only [h,coeff_map,coe_mapRingHom,derivative_map]
private theorem physical_add {K:Type} [Field K] (f g:K[X][X]) :
  physicalDeriv (f+g)=physicalDeriv f+physicalDeriv g:= by
 unfold physicalDeriv
 apply sum_add_index <;> simp [derivative_add]
private theorem chain {K E M:Type} [Field K] [Field E] [Algebra K E]
   [AddCommGroup M] [Module K M] [Module E M] [IsScalarTower K E M]
   (D:Derivation K E M) (x y :E) (f :K[X][X]) :
   D (atPair (algebraMap K E) x y f) =
     atPair (algebraMap K E) x y (physicalDeriv f)•D x +
     atPair (algebraMap K E) x y f.derivative•D y := by
 induction f using Polynomial.induction_on' with
 | add f g hf hg =>
   simp only [atPair,eval₂_add,map_add,physical_add,add_smul] at *
   rw [hf,hg]
   abel
 | monomial n r =>
   rw [physicalDeriv,sum_monomial_index _ _ (by simp),derivative_monomial]
   simp only [atPair,eval₂_monomial,coe_eval₂RingHom,eval₂_mul,eval₂_natCast,
     Derivation.leibniz,Derivation.leibniz_pow,← Nat.cast_smul_eq_nsmul E,smul_smul]
   rw [← aeval_def,D.map_aeval]
   simp only [aeval_def,smul_smul]
   simp only [smul_add,add_smul,smul_smul,mul_assoc,mul_left_comm,mul_comm]
   <;> abel
private theorem jacobian_kernel {E M:Type} [Field E] [AddCommGroup M] [Module E M]
    (A B C D:E) (u v :M) (hf :A•u+B•v=0) (hg:C•u+D•v=0)
    (h:A*D - B*C≠0) :u=0∧v=0:= by
  constructor <;> apply (smul_eq_zero_iff_right h).mp
  · calc
      _=D•(A•u+B•v) - B•(C•u+D•v) := by
        simp only [sub_smul,smul_add,smul_sub,add_smul,smul_smul,mul_comm]
        abel
      _=0:= by rw [hf,hg,smul_zero,smul_zero,sub_self]
  · calc
      _=A•(C•u+D•v) - C•(A•u+B•v) := by
        simp only [sub_smul,smul_add,smul_sub,add_smul,smul_smul,mul_comm]
        abel
      _=0:= by rw [hf,hg,smul_zero,smul_zero,sub_self]
private theorem adjoin_separable {K A:Type} [Field K] [Field A] [Algebra K A]
   [Algebra.IsAlgebraic K A] (x y :A) (f g:K[X][X])
   (hf :atPair (algebraMap K A) x y f=0) (hg:atPair (algebraMap K A) x y g=0)
   (hj:jacobian (algebraMap K A) x y f g≠0) :
   Algebra.IsSeparable K (IntermediateField.adjoin K ({x,y} : Set A)) := by
 classical
 let F:=IntermediateField.adjoin K ({x,y} : Set A)
 let u:F:=⟨x,IntermediateField.subset_adjoin K _ (by simp)⟩
 let v :F:=⟨y,IntermediateField.subset_adjoin K _ (by simp)⟩
 have hgen:Algebra.adjoin K ({u,v} : Set F) = ⊤ := by
   apply Subalgebra.map_injective (f :=F.val) F.val.injective
   rw [AlgHom.map_adjoin,Algebra.map_top,F.range_val]
   change Algebra.adjoin K (F.val '' {u,v}) =
     (IntermediateField.adjoin K ({x,y} : Set A)).toSubalgebra
   rw [IntermediateField.adjoin_toSubalgebra,Set.image_pair]
   rfl
 let:Algebra.FiniteType K F:=⟨⟨{u,v},by simpa using hgen⟩⟩
 have hm (r :K[X][X]) :
     algebraMap F A (atPair (algebraMap K F) u v r)=atPair (algebraMap K A) x y r := by
   rw [atPair_natural,← IsScalarTower.algebraMap_eq K F A]
   rfl
 let D:=KaehlerDifferential.D K F
 have hzero (r :K[X][X]) (hr :atPair (algebraMap K A) x y r=0) :
     atPair (algebraMap K F) u v (physicalDeriv r)•D u +
     atPair (algebraMap K F) u v r.derivative•D v=0:= by
   have hz :atPair (algebraMap K F) u v r=0:= by
     apply (algebraMap F A).injective
     rwa [hm,map_zero]
   rw [← chain D,hz,map_zero]
 have hj' : jacobian (algebraMap K F) u v f g≠0:= by
   intro h
   apply hj
   simpa only [jacobian,map_sub,map_mul,hm,map_zero] using
     congrArg (algebraMap F A) h
 obtain ⟨hu,hv⟩:=jacobian_kernel _ _ _ _ _ _ (hzero f hf) (hzero g hg) hj'
 have hD:D =0:= by
   apply Derivation.ext_of_adjoin_eq_top _ hgen
   intro z hz
   rcases Set.mem_insert_iff.mp hz with rfl | hz
   · exact hu
   · rwa [Set.mem_singleton_iff.mp hz]
 let:Algebra.FormallyUnramified K F:= by
   refine ⟨(subsingleton_iff_forall_eq 0).mpr ?_⟩
   suffices h: (⊤ : Submodule F (KaehlerDifferential K F)) ≤ ⊥ by
     exact fun z=>h (Submodule.mem_top (x :=z))
   rw [← KaehlerDifferential.span_range_derivation K F,Submodule.span_le]
   rintro _ ⟨z,rfl⟩
   change D z=0
   rw [hD,Derivation.zero_apply]
 exact Algebra.FormallyUnramified.isSeparable K F
private theorem map_form {K A:Type} [Field K] [Field A] {d s a :ℕ}
  (j:K →+* A) (u:Slot d s a→K) :
  (form u).map (mapRingHom j)=form (fun i=>j (u i)) := by
 simp only [form,Polynomial.map_sum,map_monomial,coe_mapRingHom]
theorem proof :qG7TGJa.c3:= by
 intro d s a _ _ _ b c _ q hj _
 let R:=jo d s a
 let K:=aFB d s a
 let A:=Generic d s a
 let x :A:=q.val.1
 let y :A:=q.val.2
 let j:=algebraMap K A
 let f :K[X][X] :=form fun i=>algebraMap R K (MvPolynomial.X (Sum.inl i))
 let g:K[X][X] :=form fun i=>algebraMap R K (MvPolynomial.X (Sum.inr i))
 have hf :f.map (mapRingHom j)=genericF d s a := by
   simp only [f,map_form,genericF,j,← IsScalarTower.algebraMap_apply R K A]
   rfl
 have hg:g.map (mapRingHom j)=genericG d s a := by
   simp only [g,map_form,genericG,j,← IsScalarTower.algebraMap_apply R K A]
   rfl
 have hj' : jacobian j x y f g≠0:= by
   simpa only [← hf,← hg,jacobian,physical_map,derivative_map,atPair_map] using hj
 let F:=IntermediateField.adjoin K ({x,y} : Set A)
 let:Algebra.IsSeparable K F:=adjoin_separable x y f g
   (by simpa only [← hf,atPair_map] using q.prop.1)
   (by simpa only [← hg,atPair_map] using q.prop.2) hj'
 let u:F:=⟨x,IntermediateField.subset_adjoin K _ (by simp)⟩
 let v :F:=⟨y,IntermediateField.subset_adjoin K _ (by simp)⟩
 let w:F:=atPair (algebraMap K F) u v f.derivative/qZu9hjc.gauge b c v^(d-2)
 have h:=(Algebra.IsSeparable.isSeparable K w).map F.val F.val.injective
 change IsSeparable K (algebraMap F A w) at h
 have hw:algebraMap F A w=value b c q.val := by
   unfold w value qZu9hjc.gauge
   rw [map_div₀,map_pow,map_add,map_mul,atPair_natural,
     ← IsScalarTower.algebraMap_eq K F A,← atPair_map,← derivative_map,hf]
   rfl
 exact hw ▸ h
end
end qeFnRJb
end
