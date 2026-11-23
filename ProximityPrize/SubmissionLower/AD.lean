import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BD
set_option Elab.async false
open _root_ renaming AddHom.coe_mk→Ar,Algebra.algebraMap→vG,Classical.decEq→t9,Classical.propDecidable→zi,CompPoly.Extension.Ext.ofBase→z9,CompPoly.Extension.Ext.ofBaseRingHom→EK,Decidable→xm,DecidableEq→lz,EuclideanDomain.mul_div_cancel'→uW,ExpChar→ oy,Field→lI,Fin.castSucc→zS,Fin.sum_univ_castSucc→GB,Fin.sum_univ_three→Gr,Fin.sum_univ_two→zh,Finset→lJ,Finset.card_image_of_injective→Ea,Finset.card_sdiff_of_subset→ Il,Finset.card_univ→uh,Finset.mem_univ→qU,Finset.mul_sum→wB,Finset.subset_univ→zg,Finset.sum_add_distrib→Ef,Finset.sum_coe_sort→Av,Finset.sum_congr→pG,Finset.sum_subset→G2,Finset.univ→ oY,Fintype→c9,Fintype.card→aU,Fintype.card_coe→vl,Fintype.card_fin→sS,Fintype.card_prod→HZ,Fintype.card_subtype_compl→Gn,Fintype.sum_option→JK,Fintype.sum_prod_type→ IU,Function.Injective→cy,Function.Surjective→vh,GCDMonoid.gcd→ oj,GCDMonoid.gcd_dvd_left→v9,GCDMonoid.gcd_dvd_right→yB,IsCoprime→pz,KoalaBear.Field→FQ,KoalaBear.card_ext6→ Iw,KoalaBear.ext6Params→Aa,Lagrange.degree_interpolate_lt→GY,Lagrange.eval_interpolate_at_node→G8,Lagrange.interpolate→GR,LinearMap.coe_mk→Eg
open _root_ renaming LinearMap.comp_apply→ In,LinearMap.finrank_range_add_finrank_ker→t8,LinearMap.finrank_range_of_inj→FV,LinearMap.ker→n5,LinearMap.range→p7,LinearMap.range_comp_of_range_eq_top→Gi,Matrix→ oD,Matrix.cons_val_one→Gj,Matrix.cons_val_two→ IT,Matrix.cons_val_zero→G9,Matrix.det_diagonal→xI,Matrix.diagonal→yU,Matrix.map_apply→xu,Matrix.mulVec→p9,Matrix.mulVecLin_apply→G6,Matrix.mul_diagonal→Cy,Matrix.of→pL,Matrix.of_apply→Au,Matrix.rank_eq_finrank_span_row→zk,Matrix.rank_le_card_width→G4,Matrix.rank_mul_eq_left_of_det_ne_zero→G1,Matrix.rank_transpose→G5,Matrix.transpose_apply→wA,Module.finrank→nI,Module.finrank_fintype_fun_eq_card→t3,Multiset.le_iff_subset→Hw,Nat.add_le_add_left→JM,Pi.smul_apply→xL,Pi.zero_apply→zc,Polynomial→p6,Polynomial.C→lV,Polynomial.X→nq,Polynomial.card_le_degree_of_subset_roots→Ee,Polynomial.coe_evalRingHom→qz,Polynomial.coeff_map→wR,Polynomial.degreeLT→ ox,Polynomial.degreeLTEquiv→z8,Polynomial.degree_add_le→vZ,Polynomial.degree_sub_le→yJ,Polynomial.eq_C_of_natDegree_eq_zero→ II,Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero→GF,Polynomial.eval→EP,Polynomial.evalRingHom→nX,Polynomial.eval_C→pC,Polynomial.eval_X→qy,Polynomial.eval_add→qm,Polynomial.eval_finsetSum→qx,Polynomial.eval_map_apply→Dz
open _root_ renaming Polynomial.eval_mul→ oq,Polynomial.eval_pow→t7,Polynomial.eval_smul→C9,Polynomial.eval_sub→ze,Polynomial.map_map→Fa,Polynomial.map_mul→Bf,Polynomial.mem_roots→t5,Polynomial.natDegree_lt_iff_degree_lt→qJ,Polynomial.natDegree_map_eq_of_injective→FK,Polynomial.natDegree_mul→uz,Polynomial.natDegree_smul_le→G3,Polynomial.smul_eq_C_mul→C5,ProximityPrize.Benchmark.IRSProfile.Field→zm,ProximityPrize.Benchmark.IRSProfile.Index→vw,ProximityPrize.Benchmark.IRSProfile.domain→uJ,ProximityPrize.Benchmark.IRSProfile.interleaving→Dw,ReedSolomon.code→yo,RingHom.id_apply→z7,Set.range→t4,Submodule→th,Submodule.coe_add→Gk,Submodule.coe_smul→G7,Submodule.map_comp→F9,Submodule.span→qM,Subtype.ext→u8,Subtype.val→zE,Subtype.val_injective→FR,add_comm→y5,add_zero→wY,congrArg→ oz,congrFun→ ov,dotProduct→p5,frobenius→qG,gR.M4.IsPrimitive→yQ,gR.Principal.P8→t6,gR.Principal.aAt→v8,gR.Principal.aCg→x7,gR.Principal.ahe→yl,gR.Principal.assemble→mD,gR.Principal.avE→zd,gR.Principal.bwQ→Et,gR.Principal.specialize→sH,gR.apT.vector→yL,gR.weight→ oK,gR.zQ.RowBasis→sI,gR.zQ.pivot→u5,gcd_ne_zero_of_right→Fz,isCoprime_div_gcd_div_gcd→G0
open _root_ renaming le_antisymm→Du,left_div_gcd_ne_zero→Df,map_add→vi,map_mul→pU,map_ne_zero→FU,map_zero→zf,max_lt→u9,mul_add→vH,mul_assoc→vk,mul_comm→xW,mul_inv_cancel₀→Dv,mul_ne_zero→pQ,one_mul→ oZ,one_ne_zero→C4,right_div_gcd_ne_zero→zR,smul_eq_mul→vj
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset CoreDefinitions Code LinearCode
open scoped BigOperators
local instance gPD (P:Prop) :xm P:=zi P
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
def akD (x :ι→F) (u v :ι→F) (k A:ℕ) (γ:F) :Prop :=
  ∃ S:lJ ι,A≤S.card ∧
    NM x (fun i=>u i+γ*v i) k S ∧
    ¬ (NM x u k S∧NM x v k S)
theorem aNc (a :F) {P:F[X]} {k :ℕ} (hP:P.degree<k) :
 (a•P).degree<k :=(Polynomial.degree_smul_le a P).trans_lt hP
theorem degree_sub_lt {P Q:F[X]} {k :ℕ}
   (hP:P.degree<k) (hQ:Q.degree<k) : (P-Q).degree<k :=
 (yJ P Q).trans_lt (u9 hP hQ)
theorem cCQ (x :ι→F) (u v :ι→F) (k A:ℕ)
  (a b γ:F)
  (hrel :NM x (fun i=>a*u i+b*v i) k oY)
  (hbad:akD x u v k A γ) :a*γ=b:= by
 classical
 by_contra hne
 obtain ⟨P,hP,hPv⟩:=hrel
 obtain ⟨S,hAS,⟨Q,hQ,hQv⟩,hnonjoint⟩:=hbad
 have hd:b-a*γ≠0:=sub_ne_zero.mpr (Ne.symm hne)
 let V:F[X] :=(b-a*γ)⁻¹•(P-a•Q)
 let U:F[X] := Q-γ•V
 have hV:V.degree<k :=aNc _ (degree_sub_lt hP (aNc a hQ))
 have hU:U.degree<k :=degree_sub_lt hQ (aNc γ hV)
 have hVv : ∀ i∈S,V.eval (x i)=v i:= by
  intro i hi
  dsimp [V]
  simp only [C9,ze,vj]
  rw [hPv i (qU i),hQv i hi]
  field_simp
  ring
 have hUv : ∀ i∈S,U.eval (x i)=u i:= by
  intro i hi
  dsimp [U]
  simp only [ze,C9,vj]
  rw [hQv i hi,hVv i hi]
  ring
 exact hnonjoint ⟨⟨U,hU,hUv⟩,⟨V,hV,hVv⟩⟩
theorem cCO (x :ι→F) (u v :ι→F) (k A:ℕ)
   (a b:F) (hab:a≠0∨b≠0)
   (hrel :NM x (fun i=>a*u i+b*v i) k oY)
   (Γ:lJ F) (hΓ : ∀ γ∈Γ,akD x u v k A γ) :Γ.card≤1 := by
 classical
 apply Finset.card_le_one.mpr
 intro γ hγ γ' hγ'
 have hg:=cCQ x u v k A a b γ hrel (hΓ γ hγ)
 have hg' := cCQ x u v k A a b γ' hrel (hΓ γ' hγ')
 rcases hab with ha | hb
 · exact mul_left_cancel₀ ha (hg.trans hg'.symm)
 · have ha :a≠0:= by intro hz; simp [hz] at hg; exact hb hg.symm
   exact mul_left_cancel₀ ha (hg.trans hg'.symm)
theorem cCP (x :ι→F) (hx :cy x)
  (u v :ι→F) (k A:ℕ) (hkA:k<A) (γ:F)
  (hbad:akD x u v k A γ) :
  ∃ T:lJ ι,T.card=A ∧
    NM x (fun i=>u i+γ*v i) k T ∧
    ¬ (NM x u k T∧NM x v k T) := by
 obtain ⟨S,hS,⟨P,hP,hPv⟩,hbad⟩:=hbad
 obtain ⟨T,_,hT,hP',hPv',hbad'⟩ :=
  d3E x hx u v γ k A hkA S hS P hP hPv hbad
 exact ⟨T,hT,⟨P,hP',hPv'⟩,hbad'⟩
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace gR.kL
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
theorem aC4 (σ:F →+* F) (P:F[X]) (a :F)
  (ha :σ a=a) : (P.map σ).eval a=σ (P.eval a) := by
 simpa only [ha] using (Dz σ a (p:=P))
theorem ahy (U P:F[X]) (h k :ℕ)
   (hU:U.natDegree≤h) (hP:P.degree<k) :
   (U*P).degree<k+h:= by
 by_cases hp:P=0
 · simp [hp]
 have hpn:P.natDegree<k :=(qJ hp).mpr hP
 have hb: (U*P).natDegree<k+h :=
   natDegree_mul_le.trans_lt (by omega)
 exact degree_le_natDegree.trans_lt (by exact_mod_cast hb)
structure a1f (σ:F →+* F) (x w:ι→F)
  (k h:ℕ) (U V R:F[X]) :Prop where
 degree_U:U.natDegree≤h
 degree_V:V.natDegree≤h
 degree_R:R.degree<k+h
 nodes : ∀ i,U.eval (x i)*w i+V.eval (x i)*σ (w i)=R.eval (x i)
theorem dU2 (σ:F →+* F)
    (x w:ι→F) (hx :cy x) (hfixed : ∀ i,σ (x i)=x i)
    (k h:ℕ) (U V R:F[X]) (rel :a1f σ x w k h U V R)
    (S:lJ ι) (hS:k+h≤S.card) (P:F[X]) (hP:P.degree<k)
    (hagree : ∀ i∈S,P.eval (x i)=w i) :
    U*P+V*(P.map σ)=R:= by
  classical
  let Q:=U*P+V*(P.map σ)-R
  have hmap : (P.map σ).degree<k :=(Polynomial.degree_map_le).trans_lt hP
  have hQ:Q.degree<(k+h:ℕ) := by
    apply (yJ _ _).trans_lt
    exact u9
      ((vZ _ _).trans_lt
        (u9 (ahy U P h k rel.degree_U hP)
          (ahy V (P.map σ) h k rel.degree_V hmap))) rel.degree_R
  have hz : ∀ i∈S,Q.eval (x i)=0:= by
    intro i hi
    dsimp [Q]
    rw [ze,qm,oq,oq,
      aC4 σ P (x i) (hfixed i),hagree i hi,
      rel.nodes i,sub_self]
  have hzero :Q=0:= by
    by_contra hne
    have hc: (S.image x).card≤Q.natDegree :=
      Ee (fun a ha =>
        (t5 hne).mpr (by
          obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
          exact hz i hi))
    rw [Ea S hx] at hc
    have hdeg:Q.natDegree<k+h:=(qJ hne).mpr hQ
    omega
  exact sub_eq_zero.mp hzero
theorem dU1 (σ:F →+* F)
   (x w:ι→F) (hx :cy x) (hfixed : ∀ i,σ (x i)=x i)
   (k h:ℕ) (U V R:F[X]) (rel :a1f σ x w k h U V R)
   (S:lJ ι) (hS:k+h≤S.card) (P:F[X]) (hP:P.degree<k)
   (hagree : ∀ i∈S,P.eval (x i)=w i) (i:ι) :
   U.eval (x i)*(w i-P.eval (x i)) +
     V.eval (x i)*σ (w i-P.eval (x i))=0:= by
 have hpoly :=dU2 σ x w hx hfixed k h U V R rel S hS P hP hagree
 have he :=oz (EP (x i)) hpoly
 rw [qm,oq,oq,aC4 σ P (x i) (hfixed i)] at he
 have hr :=rel.nodes i
 rw [map_sub]
 linear_combination hr - he
theorem eem (p:ℕ) [oy F p]
  (x w:ι→F) (hx :cy x) (hfixed : ∀ i,x i^p=x i)
  (k h:ℕ) (U V R:F[X])
  (rel :a1f (qG F p) x w k h U V R)
  (S:lJ ι) (hS:k+h≤S.card) (P:F[X]) (hP:P.degree<k)
  (hagree : ∀ i∈S,P.eval (x i)=w i) (i:ι) :
  U.eval (x i)*(w i-P.eval (x i)) +
    V.eval (x i)*(w i-P.eval (x i))^p=0 :=
 dU1 (qG F p) x w hx hfixed k h U V R rel S hS P hP hagree i
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F:Type} [lI F]
theorem cId (u v P:F[X]) (d L:ℕ)
    (hu:u.natDegree≤d) (hv :v≠0) (hvd:v.natDegree=d)
    (hcop:pz u v) (hdL:d≤L) (hP:P.degree<(L+d:ℕ)) :
    ∃ A B:F[X],A.degree<L∧B.degree<L∧P=u*A+v*B:= by
  obtain ⟨s,t,hst⟩:=hcop
  let A:=(s*P)%v
  let B:=t*P+u*((s*P)/v)
  have hA:A.degree<L:= by
    apply (Polynomial.degree_mod_lt (s*P) hv).trans_le
    exact Polynomial.degree_le_natDegree.trans (by exact_mod_cast (hvd.trans_le hdL))
  have heq :P=u*A+v*B:= by
    have hm:=EuclideanDomain.mod_add_div (s*P) v
    calc
      P=(s*u+t*v)*P:= by rw [hst,oZ]
      _=u*(A+v*((s*P)/v))+v*(t*P) := by rw [show A+v*((s*P)/v)=s*P from hm]; ring
      _=u*A+v*B:= by dsimp [B]; ring
  have hB:B.degree<L:= by
    by_cases hb:B=0
    · simp [hb]
    have hprod: (v*B).degree<(L+d:ℕ) := by
      rw [show v*B=P-u*A by rw [heq]; ring]
      exact (yJ _ _).trans_lt
        (u9 hP (ahy u A d L hu hA))
    have hbn:=(qJ (pQ hv hb)).mpr hprod
    rw [uz hv hb,hvd] at hbn
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (show B.natDegree<L by omega))
  exact ⟨A,B,hA,hB,heq⟩
theorem bnX (u v P:F[X]) (d L:ℕ)
   (hu:u≠0) (hv :v≠0) (hd:max u.natDegree v.natDegree=d)
   (hcop:pz u v) (hdL:d≤L) (hP:P.degree<(L+d:ℕ)) :
   ∃ A B:F[X],A.degree<L∧B.degree<L∧P=u*A+v*B:= by
 by_cases hvd:v.natDegree=d
 · exact cId u v P d L
     (by omega) hv hvd hcop hdL hP
 · have hud:u.natDegree=d:= by omega
   obtain ⟨B,A,hB,hA,heq⟩:=cId v u P d L
     (by omega) hu hud hcop.symm hdL hP
   exact ⟨A,B,hA,hB,by rw [heq,y5 ]⟩
theorem dP0 (u v P:F[X]) (d L:ℕ)
    (hu:u≠0) (hv :v≠0) (hd:max u.natDegree v.natDegree=d)
    (hcop:pz u v) (hdL:d≤L) :
    P.degree<(L+d:ℕ) ↔
      ∃ A B:F[X],A.degree<L∧B.degree<L∧P=u*A+v*B:= by
  constructor
  · exact bnX u v P d L hu hv hd hcop hdL
  · rintro ⟨A,B,hA,hB,rfl⟩
    exact (vZ _ _).trans_lt
      (max_lt (ahy u A d L (by omega) hA)
        (ahy v B d L (by omega) hB))
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F:Type} [lI F] [lz F]
theorem bed (u v :F[X]) (hu:u≠0) (hv :v≠0) :
   (oj u v).natDegree≤max u.natDegree v.natDegree ∧
   max (u/oj u v).natDegree (v/oj u v).natDegree =
     max u.natDegree v.natDegree-(oj u v).natDegree := by
 let J:=oj u v
 have hJ:J≠0:=Fz hv
 have ha :=Df hu (q:=v)
 have hb:=zR hv (p:=u)
 have hua :J*(u/J)=u:=uW hJ (v9 u v)
 have hvb:J*(v/J)=v :=uW hJ (yB u v)
 have hda :=uz hJ ha
 have hdb:=uz hJ hb
 rw [hua] at hda
 rw [hvb] at hdb
 change J.natDegree≤max u.natDegree v.natDegree ∧
   max (u/J).natDegree (v/J).natDegree=max u.natDegree v.natDegree-J.natDegree
 have huD:u.natDegree=J.natDegree+(u/J).natDegree :=hda
 have hvD:v.natDegree=J.natDegree+(v/J).natDegree :=hdb
 rw [huD,hvD,Nat.add_max_add_left]
 constructor <;> omega
theorem efl (u v P:F[X]) (L:ℕ) (hu:u≠0) (hv :v≠0)
    (hL:max u.natDegree v.natDegree-(oj u v).natDegree≤L) :
    (∃ A B:F[X],A.degree<L∧B.degree<L∧P=u*A+v*B) ↔
      ∃ W:F[X],W.degree<(L+(max u.natDegree v.natDegree-
        (oj u v).natDegree) :ℕ)∧P=oj u v*W:= by
  let J:=oj u v
  let d:=max u.natDegree v.natDegree
  have hJ:J≠0:=Fz hv
  have ha :=Df hu (q:=v)
  have hb:=zR hv (p:=u)
  have hua :J*(u/J)=u:=uW hJ (v9 u v)
  have hvb:J*(v/J)=v :=uW hJ (yB u v)
  obtain ⟨hj,hd⟩:=bed u v hu hv
  change J.natDegree≤d at hj
  change max (u/J).natDegree (v/J).natDegree=d-J.natDegree at hd
  constructor
  · rintro ⟨A,B,hA,hB,hP⟩
    have hdvd:J∣P:= by
      rw [hP]
      exact dvd_add ((v9 u v).mul_right A) ((yB u v).mul_right B)
    obtain ⟨W,hW⟩:=hdvd
    refine ⟨W,?_,hW⟩
    by_cases hw0:W=0
    · simp [hw0]
    have hp0:P≠0:= by rw [hW]; exact pQ hJ hw0
    have hpdeg:P.degree<(L+d:ℕ) := by
      rw [hP]
      exact (vZ _ _).trans_lt
        (max_lt (ahy u A d L (by dsimp [d]; omega) hA)
          (ahy v B d L (by dsimp [d]; omega) hB))
    have hn:=(qJ hp0).mpr hpdeg
    rw [hW,uz hJ hw0] at hn
    exact degree_le_natDegree.trans_lt (by exact_mod_cast
      (show W.natDegree<L+(d-J.natDegree) by omega))
  · rintro ⟨W,hW,rfl⟩
    obtain ⟨A,B,hA,hB,heq⟩:=bnX (u/J) (v/J) W
      (d-J.natDegree) L ha hb hd (G0 hv) hL hW
    refine ⟨A,B,hA,hB,?_⟩
    calc
      J*W=J*((u/J)*A+(v/J)*B) := by rw [heq]
      _=u*A+v*B:= by rw [vH,← vk,← vk,hua,hvb]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι]
def a1S (x :ι→F) (N :ℕ) :ox F N →ₗ[F] (ι→F) where
 toFun P i:=(P:F[X]).eval (x i)
 map_add' P Q:= by ext i; exact qm
 map_smul' c P:= by ext i; simp
theorem dz4 (x :ι→F) (hx :cy x) (N :ℕ)
  (hN :N≤aU ι) :cy (a1S x N) := by
 classical
 intro P Q hPQ
 apply u8
 apply sub_eq_zero.mp
 by_contra hne
 have hdeg: ((P:F[X])-(Q:F[X])).degree<N :=
  (yJ _ _).trans_lt
    (u9 (Polynomial.mem_degreeLT.mp P.property) (Polynomial.mem_degreeLT.mp Q.property))
 have hn: ((P:F[X])-(Q:F[X])).natDegree<N :=
  (qJ hne).mpr hdeg
 have hz : ∀ i,((P:F[X])-(Q:F[X])).eval (x i)=0:= by
  intro i
  rw [ze,sub_eq_zero]
  exact ov hPQ i
 exact hne (GF _ hx hz (by omega))
theorem cDq (x :ι→F) (hx :cy x) (N :ℕ)
   (hN :aU ι≤N) :vh (a1S x N) := by
 classical
 intro w
 let P:=GR (oY :lJ ι) x w
 have hP:P.degree<N := by
   exact (GY w hx.injOn).trans_le (by
     simpa only [uh] using (show (aU ι:WithBot ℕ)≤N by exact_mod_cast hN))
 refine ⟨⟨P,Polynomial.mem_degreeLT.mpr hP⟩,?_⟩
 funext i
 exact G8 w hx.injOn (qU i)
theorem bVP (x :ι→F) (hx :cy x) (N :ℕ) :
   nI F (p7 (a1S x N))=min (aU ι) N := by
 by_cases hN :N≤aU ι
 · rw [FV (dz4 x hx N hN)]
   have hd:=(z8 F N).finrank_eq
   simpa only [t3 ,sS ,min_eq_right hN] using hd
 · have hc:Fintype.card ι≤N := by omega
   rw [LinearMap.range_eq_top.mpr (cDq x hx N hc),finrank_top,
    t3 ,min_eq_left hc]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F:Type} [lI F] [lz F]
theorem dh9 (σ:F →+* F) (u v P:F[X]) (d L:ℕ)
    (hu:u≠0) (hv :v≠0) (hd:max u.natDegree v.natDegree=d)
    (hcop:pz u v) (hdL:d≤L) :
    (∃ A B C:F[X],A.degree<L∧B.degree<L∧C.degree<L ∧
      P=(v*v.map σ)*A+(u*v.map σ)*B+(u*u.map σ)*C) ↔
      ∃ W:F[X],W.degree<(L+2*d-(oj u (v.map σ)).natDegree :ℕ) ∧
        P=oj u (v.map σ)*W:= by
  have huσ:u.map σ≠0:= by simpa using hu
  have hvσ:v.map σ≠0:= by simpa using hv
  have hdu: (u.map σ).natDegree=u.natDegree :=FK σ.injective u
  have hdv : (v.map σ).natDegree=v.natDegree :=FK σ.injective v
  have hdσ:max (u.map σ).natDegree (v.map σ).natDegree=d:= by rw [hdu,hdv,hd]
  have hcopσ:pz (u.map σ) (v.map σ) :=hcop.map (Polynomial.mapRingHom σ)
  have hcross :max u.natDegree (v.map σ).natDegree=d:= by rw [hdv,hd]
  have hj:=(bed u (v.map σ) hu hvσ).1
  rw [hcross] at hj
  have hnum : (L+d)+(d-(oj u (v.map σ)).natDegree) =
      L+2*d-(oj u (v.map σ)).natDegree := by omega
  have hspan:=efl u (v.map σ) P (L+d) hu hvσ
    (by rw [hcross]; omega)
  rw [hcross,hnum] at hspan
  constructor
  · rintro ⟨A,B,C,hA,hB,hC,hP⟩
    apply hspan.mp
    refine ⟨v.map σ*B+u.map σ*C,v*A,?_,?_,?_⟩
    · exact (vZ _ _).trans_lt
        (max_lt (ahy (v.map σ) B d L (by omega) hB)
          (ahy (u.map σ) C d L (by omega) hC))
    · exact ahy v A d L (by omega) hA
    · rw [hP]; ring
  · intro hW
    obtain ⟨Q,R,hQ,hR,hP⟩:=hspan.mpr hW
    obtain ⟨C,B1,hC,hB1,hQeq⟩:=bnX (u.map σ) (v.map σ)
      Q d L huσ hvσ hdσ hcopσ hdL hQ
    obtain ⟨B2,A,hB2,hA,hReq⟩:=bnX u v R d L
      hu hv hd hcop hdL hR
    refine ⟨A,B1+B2,C,hA,(vZ _ _).trans_lt (u9 hB1 hB2),hC,?_⟩
    rw [hP,hQeq,hReq]
    ring
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β:Type} [lI F] [c9 ι] [c9 β]
def JC {L:ℕ} (a :Fin L→F) :F[X] :=
 ∑ j,Polynomial.monomial j.val (a j)
theorem bnu {L:ℕ} (a :Fin L→F) :
  (JC a).degree<L:= by
 apply Polynomial.mem_degreeLT.mp
 apply (ox F L).sum_mem
 intro j _
 exact Polynomial.mem_degreeLT.mpr
  ((Polynomial.degree_monomial_le _ _).trans_lt (by exact_mod_cast j.isLt))
theorem dMW {L:ℕ} (a :Fin L→F) (x :F) :
  (JC a).eval x=∑ j,a j*x^j.val := by
 simp only [JC,qx ,eval_monomial]
theorem d2d (L:ℕ) (P:ox F L) (x :F) :
   (P:F[X]).eval x=∑ j:Fin L,(P:F[X]).coeff j.val*x^j.val := by
 by_cases hp: (P:F[X])=0
 · simp [hp]
 rw [Fin.sum_univ_eq_sum_range (fun j=>(P:F[X]).coeff j*x^j) L]
 exact Polynomial.eval_eq_sum_range'
   ((qJ hp).mpr (Polynomial.mem_degreeLT.mp P.property)) x
def aPn (g:β→F[X]) (L:ℕ) :
    (β→ ox F L) →ₗ[F] F[X] where
  toFun Q := ∑ b,g b*(Q b:F[X])
  map_add' Q R:= by simp only [Pi.add_apply,Gk,vH,Ef]
  map_smul' c Q:= by simp only [xL,G7,mul_smul_comm,Finset.smul_sum,z7]
def aST (x :ι→F) :F[X] →ₗ[F] (ι→F) where
 toFun P i:=P.eval (x i)
 map_add' P Q:= by ext i; exact qm
 map_smul' c P:= by ext i; simp
def avH (x :ι→F) (g:β→F[X]) (L:ℕ) :
    oD (β×Fin L) ι F:= fun b i=>(g b.1).eval (x i)*x i^b.2.val
theorem eFF (x :ι→F) (g:β→F[X]) (L:ℕ) :
   p7 (avH x g L).transpose.mulVecLin =
     (p7 (aPn g L)).map (aST x) := by
 classical
 rw [← LinearMap.range_comp]
 apply Du
 · rintro _ ⟨a,rfl⟩
   let Q:β→ ox F L:= fun b =>
     ⟨JC (fun j=>a (b,j)),Polynomial.mem_degreeLT.mpr (bnu _)⟩
   refine ⟨Q,?_⟩
   funext i
   simp only [In,aST,Eg ,Ar,
     aPn,qx ,oq,Q,dMW,
     G6,p9,p5 ,avH,wA,
     IU,wB]
   apply pG rfl
   intro b _
   apply pG rfl
   intro j _
   ring
 · rintro _ ⟨Q,rfl⟩
   refine ⟨fun b=>(Q b.1 :F[X]).coeff b.2.val,?_⟩
   funext i
   simp only [In,aST,Eg ,Ar,
     aPn,qx ,oq,G6,
     p9,p5 ,avH,wA,IU]
   simp_rw [d2d L (Q _) (x i),wB]
   apply pG rfl
   intro b _
   apply pG rfl
   intro j _
   ring
theorem c1V (x :ι→F) (g:β→F[X]) (L:ℕ) :
   (avH x g L).rank=nI F
     ((p7 (aPn g L)).map (aST x)) := by
 rw [← eFF]
 exact (G5 _).symm
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [lz F] [c9 ι]
def a6K (J:F[X]) :F[X] →ₗ[F] F[X] where
 toFun P:=J*P
 map_add' P Q:=vH _ _ _
 map_smul' c P:=mul_smul_comm _ _ _
def dPM (c:ι→F) (hc : ∀ i,c i≠0) : (ι→F) ≃ₗ[F] (ι→F) where
 toFun v i:=c i*v i
 invFun v i:=(c i)⁻¹*v i
 left_inv v := by funext i; simp only [← vk,inv_mul_cancel₀ (hc i),oZ]
 right_inv v := by funext i; simp only [← vk,Dv (hc i),oZ]
 map_add' v w:= by funext i; exact vH _ _ _
 map_smul' a v := by funext i; simp only [xL,vj,z7]; ring
theorem eEi (x :ι→F) (hx :cy x)
   (J:F[X]) (hJ : ∀ i,J.eval (x i)≠0) (N :ℕ) :
   nI F (((ox F N).map (a6K J)).map (aST x)) =
     min (aU ι) N := by
 let e :=dPM (fun i=>J.eval (x i)) hJ
 have heval :p7 (a1S x N) =
     (ox F N).map (aST x) := by
   ext v
   constructor
   · rintro ⟨P,rfl⟩
     exact ⟨P,P.property,rfl⟩
   · rintro ⟨P,hP,rfl⟩
     exact ⟨⟨P,hP⟩,rfl⟩
 have heq : ((ox F N).map (a6K J)).map (aST x) =
     (p7 (a1S x N)).map e.toLinearMap:= by
   rw [heval,← F9,← F9]
   congr 1
   ext P i
   exact oq
 rw [heq,LinearEquiv.finrank_map_eq,bVP x hx N]
def aJU (σ:F →+* F) (u v :F[X]) :Fin 3→F[X] :=
 ![v*v.map σ,u*v.map σ,u*u.map σ]
theorem gEw (σ:F →+* F) (u v :F[X]) (d L:ℕ)
    (hu:u≠0) (hv :v≠0) (hd:max u.natDegree v.natDegree=d)
    (hcop:pz u v) (hdL:d≤L) :
    p7 (aPn (aJU σ u v) L)=
      (ox F (L+2*d-(oj u (v.map σ)).natDegree)).map
        (a6K (oj u (v.map σ))) := by
  apply Du
  · rintro _ ⟨Q,rfl⟩
    have he : ∃ A B C:F[X],A.degree<L∧B.degree<L∧C.degree<L ∧
        aPn (aJU σ u v) L Q=
          (v*v.map σ)*A+(u*v.map σ)*B+(u*u.map σ)*C:= by
      refine ⟨Q 0,Q 1,Q 2,Polynomial.mem_degreeLT.mp (Q 0).property,
        Polynomial.mem_degreeLT.mp (Q 1).property,Polynomial.mem_degreeLT.mp (Q 2).property,?_⟩
      simp only [aPn,Eg ,Ar,Gr,aJU,
        G9,Gj,IT,Matrix.head_cons,Matrix.tail_cons]
    obtain ⟨W,hW,hP⟩:=(dh9 σ u v _ d L hu hv hd hcop hdL).mp he
    exact ⟨W,Polynomial.mem_degreeLT.mpr hW,hP.symm⟩
  · rintro _ ⟨W,hW,rfl⟩
    obtain ⟨A,B,C,hA,hB,hC,hP⟩ :=
      (dh9 σ u v ((oj u (v.map σ))*W) d L hu hv hd hcop hdL).mpr
        ⟨W,Polynomial.mem_degreeLT.mp hW,rfl⟩
    let Q:Fin 3→ ox F L :=
      ![⟨A,Polynomial.mem_degreeLT.mpr hA⟩,⟨B,Polynomial.mem_degreeLT.mpr hB⟩,⟨C,Polynomial.mem_degreeLT.mpr hC⟩]
    refine ⟨Q,?_⟩
    change (∑ b:Fin 3,aJU σ u v b*(Q b:F[X]))=_
    simp only [Gr,aJU,Q,G9,Gj,IT,Matrix.head_cons,Matrix.tail_cons]
    exact hP.symm
theorem gEv (σ:F →+* F) (x :ι→F) (hx :cy x)
   (u v :F[X]) (d L:ℕ) (hu:u≠0) (hv :v≠0)
   (hd:max u.natDegree v.natDegree=d) (hcop:pz u v) (hdL:d≤L)
   (hJ : ∀ i,(oj u (v.map σ)).eval (x i)≠0) :
   (avH x (aJU σ u v) L).rank =
     min (aU ι) (L+2*d-(oj u (v.map σ)).natDegree) := by
 rw [c1V,gEw σ u v d L hu hv hd hcop hdL]
 exact eEi x hx _ hJ _
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι]
def aWj (u v :F[X]) :Fin 2→F[X] := ![v,u]
theorem eJH (u v :F[X]) (d L:ℕ)
    (hu:u≠0) (hv :v≠0) (hd:max u.natDegree v.natDegree=d)
    (hcop:pz u v) (hdL:d≤L) :
    p7 (aPn (aWj u v) L)=ox F (L+d) := by
  apply Du
  · rintro _ ⟨Q,rfl⟩
    apply Polynomial.mem_degreeLT.mpr
    have hQ:=(dP0 u v
      (v*(Q 0:F[X])+u*(Q 1 :F[X])) d L hu hv hd hcop hdL).mpr
      ⟨Q 1,Q 0,Polynomial.mem_degreeLT.mp (Q 1).property,
        Polynomial.mem_degreeLT.mp (Q 0).property,y5 _ _⟩
    simpa [aPn,aWj,zh] using hQ
  · intro P hP
    obtain ⟨A,B,hA,hB,hP⟩:=bnX u v P d L hu hv hd hcop hdL
      (Polynomial.mem_degreeLT.mp hP)
    let Q:Fin 2→ ox F L :=
      ![⟨B,Polynomial.mem_degreeLT.mpr hB⟩,⟨A,Polynomial.mem_degreeLT.mpr hA⟩]
    refine ⟨Q,?_⟩
    change (∑ b:Fin 2,aWj u v b*(Q b:F[X]))=P
    simpa [zh,aWj,Q,y5] using hP.symm
theorem dVe (x :ι→F) (N :ℕ) :
   (ox F N).map (aST x)=p7 (a1S x N) := by
 ext v
 constructor
 · rintro ⟨P,hP,rfl⟩
   exact ⟨⟨P,hP⟩,rfl⟩
 · rintro ⟨P,rfl⟩
   exact ⟨P,P.property,rfl⟩
theorem eJF (x :ι→F) (hx :cy x)
  (u v :F[X]) (d L:ℕ) (hu:u≠0) (hv :v≠0)
  (hd:max u.natDegree v.natDegree=d) (hcop:pz u v) (hdL:d≤L) :
  (avH x (aWj u v) L).rank=min (aU ι) (L+d) := by
 rw [c1V,eJH u v d L hu hv hd hcop hdL,dVe]
 exact bVP x hx (L+d)
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Matrix Polynomial Finset
open scoped BigOperators
variable {F row col:Type} [lI F] [c9 row] [c9 col]
theorem ceu (M:oD row col F) (a :row→F) (b:col→F)
   (ha : ∀ i,a i≠0) (hb : ∀ j,b j≠0) :
   (pL (fun i j=>a i*M i j*b j)).rank=M.rank := by
 classical
 have heq : (pL (fun i j=>a i*M i j*b j))=
     yU a*M*yU b:= by
   ext i j
   simp only [Au,Cy ,Matrix.diagonal_mul]
 rw [heq,G1 _ _
   (by rw [xI]; exact Finset.prod_ne_zero_iff.mpr (fun j _=>hb j)),
   Matrix.rank_mul_eq_right_of_det_ne_zero _ _
   (by rw [xI]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>ha i))]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [lz F] [c9 ι]
def afy (σ:F →+* F) (x e :ι→F) (L:ℕ) :
    oD (Fin 2×Fin L) ι F:= fun b i => ![e i,σ (e i)] b.1*x i^b.2.val
def ayK (σ:F →+* F) (x e :ι→F) (L:ℕ) :
    oD (Fin 3×Fin L) ι F:= fun b i => ![e i,σ (e i),σ (σ (e i))] b.1*x i^b.2.val
theorem cME (σ:F →+* F) (u v e :F) (hv :v≠0)
  (hrel :u*e+v*σ e=0) :
  σ e=-(u/v)*e∧σ (σ e)=(u*σ u/(v*σ v))*e := by
 have hs :σ e=-(u/v)*e := by
  calc
    σ e=(-u*e)/v :=(eq_div_iff hv).mpr (by linear_combination hrel)
    _ = _:= by ring
 refine ⟨hs,?_⟩
 calc
  σ (σ e)=σ (-(u/v)*e) :=oz σ hs
  _ = _:= by rw [pU,map_neg,map_div₀,hs]; field_simp
theorem d2A {A B:F[X]} (hAB:A∣B) (x :F) (hB:B.eval x≠0) :
  A.eval x≠0:= by
 obtain ⟨Q,hQ⟩:=hAB
 rw [hQ,oq] at hB
 exact (mul_ne_zero_iff.mp hB).1
theorem d1B (σ:F →+* F) (x e :ι→F)
   (hx :cy x) (u v :F[X]) (d L:ℕ)
   (hu:u≠0) (hv :v≠0) (hd:max u.natDegree v.natDegree=d)
   (hcop:pz u v) (hdL:d≤L) (he : ∀ i,e i≠0)
   (hvx : ∀ i,v.eval (x i)≠0)
   (hrel : ∀ i,u.eval (x i)*e i+v.eval (x i)*σ (e i)=0) :
   (afy σ x e L).rank=min (aU ι) (L+d) := by
 classical
 let N :=avH x (aWj u v) L
 let a :Fin 2×Fin L→F:= fun b=>if b.1=1 then -1 else 1
 let b:ι→F:= fun i=>e i/v.eval (x i)
 have hb : ∀ i,b i≠0:= fun i=>div_ne_zero (he i) (hvx i)
 have ha : ∀ j,a j≠0:= by intro j; dsimp [a]; split_ifs <;> simp
 have heq :afy σ x e L=pL (fun j i=>a j*N j i*b i) := by
   ext ⟨j,l⟩ i
   have hs :=(cME σ (u.eval (x i)) (v.eval (x i)) (e i) (hvx i) (hrel i)).1
   fin_cases j
   · simp [afy,a,b,N,avH,aWj]
     field_simp [hvx i]
   · simp [afy,a,b,N,avH,aWj,hs]
     field_simp [hvx i]
 rw [heq,ceu N a b ha hb]
 exact eJF x hx u v d L hu hv hd hcop hdL
theorem d1A (σ:F →+* F) (x e :ι→F)
    (hx :cy x) (hfixed : ∀ i,σ (x i)=x i)
    (u v :F[X]) (d L:ℕ)
    (hu:u≠0) (hv :v≠0) (hd:max u.natDegree v.natDegree=d)
    (hcop:pz u v) (hdL:d≤L) (he : ∀ i,e i≠0)
    (hux : ∀ i,u.eval (x i)≠0) (hvx : ∀ i,v.eval (x i)≠0)
    (hrel : ∀ i,u.eval (x i)*e i+v.eval (x i)*σ (e i)=0) :
    (ayK σ x e L).rank=
      min (aU ι) (L+2*d-(oj u (v.map σ)).natDegree) := by
  classical
  let N :=avH x (aJU σ u v) L
  let a :Fin 3×Fin L→F:= fun b=>if b.1=1 then -1 else 1
  let b:ι→F:= fun i=>e i/(v.eval (x i)*σ (v.eval (x i)))
  have hvσ : ∀ i,σ (v.eval (x i))≠0:= fun i=>(FU σ).mpr (hvx i)
  have hb : ∀ i,b i≠0:= fun i=>div_ne_zero (he i) (pQ (hvx i) (hvσ i))
  have ha : ∀ j,a j≠0:= by intro j; dsimp [a]; split_ifs <;> simp
  have heq :ayK σ x e L=pL (fun j i=>a j*N j i*b i) := by
    ext ⟨j,l⟩ i
    obtain ⟨hs,ht⟩:=cME σ (u.eval (x i)) (v.eval (x i)) (e i) (hvx i) (hrel i)
    fin_cases j
    · simp [ayK,a,b,N,avH,aJU,
        aC4 σ _ _ (hfixed i)]
      field_simp [hvx i,hvσ i]
    · simp [ayK,a,b,N,avH,aJU,hs,
        aC4 σ _ _ (hfixed i)]
      field_simp [hvx i,hvσ i]
      <;> ring
    · simp [ayK,a,b,N,avH,aJU,ht,
        aC4 σ _ _ (hfixed i)]
      field_simp [hvx i,hvσ i]
      <;> ring
  rw [heq,ceu N a b ha hb]
  apply gEv σ x hx u v d L hu hv hd hcop hdL
  intro i
  exact d2A (v9 u (v.map σ)) (x i) (hux i)
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F V W:Type} [lI F] [AddCommGroup V] [Module F V]
 [AddCommGroup W] [Module F W] [FiniteDimensional F V]
theorem cqJ (f :V →ₗ[F] W) (S:th F V) :
  nI F (S.map f)+Module.finrank F (S ⊓ n5 f :th F V)=nI F S:= by
 have h:=t8 (f.domRestrict S)
 rw [LinearMap.range_domRestrict,LinearMap.ker_domRestrict] at h
 have hk :=Submodule.finrank_map_subtype_eq S ((n5 f).comap S.subtype)
 rw [Submodule.map_comap_subtype] at hk
 rw [← hk] at h
 exact h
theorem gu3 (f :V →ₗ[F] W) (S:th F V) :
  nI F S≤nI F (S.map f)+Module.finrank F (n5 f) := by
 have h:=cqJ f S
 have hi:=Submodule.finrank_mono (show S ⊓ n5 f≤n5 f from inf_le_right)
 omega
theorem ePn (f :V →ₗ[F] W) (S:th F V)
  (hsat :nI F S=nI F (S.map f)+Module.finrank F (n5 f)) :
  n5 f≤S:= by
 have h:=cqJ f S
 have heq :S ⊓ n5 f=n5 f :=
  Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
 rw [← heq]
 exact inf_le_left
theorem glH (f :V →ₗ[F] W) (S T:th F V) (hST:S≤T)
  (hsat :nI F S=nI F (S.map f)+Module.finrank F (n5 f)) :
  nI F T=nI F (T.map f)+Module.finrank F (n5 f) := by
 have hker :n5 f≤T:=(ePn f S hsat).trans hST
 have h:=cqJ f T
 rw [inf_eq_right.mpr hker] at h
 exact h.symm
section Coordinates
variable {ι:Type} [c9 ι] [lz ι]
def aUY (C:lJ ι) : (ι→F) →ₗ[F] ({i // i∉C} → F) where
 toFun v i:=v i.val
 map_add' v w:=rfl
 map_smul' c v :=rfl
theorem edu (C:lJ ι) :vh (aUY (F:=F) C) := by
 intro w
 refine ⟨fun i=>if h:i∉C then w ⟨i,h⟩ else 0,?_⟩
 funext i
 simp [aUY,i.property]
theorem edt (C:lJ ι) :
  nI F (n5 (aUY (F:=F) C))=C.card:= by
 have h:=t8 (aUY (F:=F) C)
 rw [LinearMap.range_eq_top.mpr (edu C),finrank_top,
  t3 ,t3 ,
  Gn,vl] at h
 have hc:=Finset.card_le_univ C
 omega
theorem dbV {row:Type} (M:oD row ι F) (C:lJ ι) :
   (qM F (t4 M.row)).map (aUY C)=
     qM F (t4 (M.submatrix id zE).row) := by
 rw [Submodule.map_span,← Set.range_comp]
 rfl
end Coordinates
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [lz F] [c9 ι] [lz ι]
theorem agd (x :ι→F) (hx :cy x) (P:F[X]) (hP:P≠0)
  (S:lJ ι) (hS : ∀ i∈S,P.eval (x i)=0) :S.card≤P.natDegree := by
 have h: (S.image x).card≤P.natDegree :=Ee
  (fun a ha=>(t5 hP).mpr (by
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
    exact hS i hi))
 simpa only [Ea S hx] using h
theorem db5 (σ:F →+* F) (x e :ι→F)
   (hx :cy x) (U V:F[X]) (h L:ℕ)
   (hU:U.natDegree≤h) (hV:V.natDegree≤h) (hpair :U≠0∨V≠0)
   (hsmall:h<L) (he : ∀ i,e i≠0)
   (hrel : ∀ i,U.eval (x i)*e i+V.eval (x i)*σ (e i)=0)
   (hrank : (afy σ x e L).rank=L+h) :U≠0∧V≠0:= by
 have hn:L+h≤aU ι:= by
   simpa only [hrank] using G4 (afy σ x e L)
 constructor
 · intro hzero
   have hv :=hpair.resolve_left (by simpa using hzero)
   have hz : ∀ i∈(oY :lJ ι),V.eval (x i)=0:= by
     intro i _
     have hh:=hrel i
     rw [hzero,eval_zero,zero_mul,zero_add] at hh
     exact (mul_eq_zero.mp hh).resolve_right ((FU σ).mpr (he i))
   have hc:=agd x hx V hv oY hz
   rw [uh] at hc
   omega
 · intro hzero
   have hu:=hpair.resolve_right (by simpa using hzero)
   have hz : ∀ i∈(oY :lJ ι),U.eval (x i)=0:= by
     intro i _
     have hh:=hrel i
     rw [hzero,eval_zero,zero_mul,wY] at hh
     exact (mul_eq_zero.mp hh).resolve_right (he i)
   have hc:=agd x hx U hu oY hz
   rw [uh] at hc
   omega
theorem dPZ (σ:F →+* F) (u v :F[X]) (a e :F)
   (hcop:pz u v) (he :e≠0)
   (hrel :u.eval a*e+v.eval a*σ e=0) :u.eval a≠0∧v.eval a≠0:= by
 have hne :=(hcop.map (nX a)).ne_zero_or_ne_zero
 constructor
 · intro hu
   have hv :=hne.resolve_left (by simpa using hu)
   rw [hu,zero_mul,zero_add] at hrel
   exact (pQ hv ((FU σ).mpr he)) hrel
 · intro hv
   have hu:=hne.resolve_right (by simpa using hv)
   rw [hv,zero_mul,wY] at hrel
   exact (pQ hu he) hrel
theorem d1z (σ:F →+* F) (x e :ι→F) (L:ℕ) :
  qM F (t4 (afy σ x e L).row)≤
   qM F (t4 (ayK σ x e L).row) := by
 apply Submodule.span_le.mpr
 rintro _ ⟨⟨b,j⟩,rfl⟩
 apply Submodule.subset_span
 refine ⟨(Fin.castLE (by decide :2≤3) b,j),?_⟩
 funext i
 fin_cases b <;> simp [afy,ayK,Matrix.row]
theorem eFc (σ:F →+* F) (x e :ι→F)
    (hx :cy x) (hfixed : ∀ i,σ (x i)=x i)
    (U V:F[X]) (h L:ℕ) (hU:U.natDegree≤h) (hV:V.natDegree≤h)
    (hpair :U≠0∨V≠0) (hsmall:h<L) (he : ∀ i,e i≠0)
    (hrel : ∀ i,U.eval (x i)*e i+V.eval (x i)*σ (e i)=0)
    (hrank : (afy σ x e L).rank=L+h) :
    let G:=oj U V
    let u:=U/G
    let v :=V/G
    let d:=max u.natDegree v.natDegree
    let j:=(oj u (v.map σ)).natDegree
    (Finset.univ.filter (fun i=>G.eval (x i)=0)).card=G.natDegree ∧
      d+G.natDegree=h ∧
      (ayK σ x e L).rank=min (aU ι) (L+h+(d-j)) := by
  obtain ⟨hU0,hV0⟩:=db5 σ x e hx U V h L hU hV hpair hsmall he hrel hrank
  let G:=oj U V
  let u:=U/G
  let v :=V/G
  let g:=G.natDegree
  let d:=max u.natDegree v.natDegree
  let j:=(oj u (v.map σ)).natDegree
  let C:lJ ι:=Finset.univ.filter (fun i=>G.eval (x i)=0)
  let D := {i // i∉C}
  have hG:G≠0:=Fz hV0
  have hu:u≠0:=Df hU0
  have hv :v≠0:=zR hV0
  have hcop:pz u v :=G0 hV0
  have hGu:G*u=U:=uW hG (v9 U V)
  have hGv :G*v=V:=uW hG (yB U V)
  have hdg:d+g≤h:= by
    have hd:=(bed U V hU0 hV0).2
    have hg:=(bed U V hU0 hV0).1
    change d=max U.natDegree V.natDegree-g at hd
    change g≤max U.natDegree V.natDegree at hg
    omega
  have hc:C.card≤g:=agd x hx G hG C (by intro i hi; exact (Finset.mem_filter.mp hi).2)
  have hDn:aU D=aU ι-C.card:= by
    simp only [D,Gn,vl]
  have hnormal:L+h≤aU ι:= by
    simpa only [hrank] using G4 (afy σ x e L)
  have hdL:d≤L:= by omega
  have hGD : ∀ i:D,G.eval (x i.val)≠0:= by
    intro i hz
    exact i.property (Finset.mem_filter.mpr ⟨qU _,hz⟩)
  have hrelD : ∀ i:D,u.eval (x i.val)*e i.val+v.eval (x i.val)*σ (e i.val)=0:= by
    intro i
    apply (mul_eq_zero.mp (show G.eval (x i.val)*
      (u.eval (x i.val)*e i.val+v.eval (x i.val)*σ (e i.val))=0 from ?_)).resolve_left (hGD i)
    have hh:=hrel i.val
    rw [← hGu,← hGv,oq,oq] at hh
    linear_combination hh
  have hunitD : ∀ i:D,u.eval (x i.val)≠0∧v.eval (x i.val)≠0 :=
    fun i=>dPZ σ u v (x i.val) (e i.val) hcop (he i.val) (hrelD i)
  have hdimD:L+d≤aU D:= by omega
  have hr2D: ((afy σ x e L).submatrix id (zE :D→ι)).rank=L+d:= by
    have hh:=d1B σ (fun i:D =>x i.val) (fun i:D =>e i.val)
      (hx.comp FR) u v d L hu hv rfl hcop hdL
      (fun i=>he i.val) (fun i=>(hunitD i).2) hrelD
    have heqD: (afy σ x e L).submatrix id (zE :D→ι) =
        afy σ (fun i:D =>x i.val) (fun i:D =>e i.val) L:= by
      ext b i
      rfl
    rw [heqD]
    exact hh.trans (min_eq_right hdimD)
  let S:=qM F (t4 (afy σ x e L).row)
  let T:=qM F (t4 (ayK σ x e L).row)
  let π:=aUY (F:=F) C
  have hS:nI F S=L+h:= by rw [← zk]; exact hrank
  have hSP:nI F (S.map π)=L+d:= by
    change nI F ((qM F (t4 (afy σ x e L).row)).map (aUY C))=_
    rw [dbV,← zk]
    exact hr2D
  have hπ:nI F (n5 π)=C.card:=edt C
  have hproj:=gu3 π S
  rw [hS,hSP,hπ] at hproj
  have hsat :d+C.card=h:= by omega
  have hcg:C.card=g:= by omega
  have hsum:d+g=h:= by omega
  have hT:=glH π S T (d1z σ x e L)
    (by rw [hS,hSP,hπ]; omega)
  have hj:j≤d:= by
    have hj' := (bed u (v.map σ) hu (by simpa using hv)).1
    have hm: (v.map σ).natDegree=v.natDegree :=FK σ.injective v
    simpa only [hm] using hj'
  have hr3D: ((ayK σ x e L).submatrix id (zE :D→ι)).rank=
      min (aU D) (L+2*d-j) :=
    d1A σ (fun i:D =>x i.val) (fun i:D =>e i.val)
      (hx.comp FR) (fun i=>hfixed i.val) u v d L hu hv rfl hcop hdL
      (fun i=>he i.val) (fun i=>(hunitD i).1) (fun i=>(hunitD i).2) hrelD
  have hTP:nI F (T.map π)=min (aU D) (L+2*d-j) := by
    change nI F ((qM F (t4 (ayK σ x e L).row)).map (aUY C))=_
    rw [dbV,← zk]
    exact hr3D
  rw [hTP,hπ,← zk] at hT
  change C.card=g∧d+g=h ∧
    (ayK σ x e L).rank=min (aU ι) (L+h+(d-j))
  refine ⟨hcg,hsum,?_⟩
  omega
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
theorem bhJ (x w:ι→F) (U:F[X]) (H j:ℕ)
   (hU:U.natDegree≤H) :
   oX x (fun i=>U.eval (x i)*w i) j =
     ∑ l:Fin (H+1),U.coeff l.val*oX x w (l.val+j) := by
 simp only [oX,wB]
 rw [Finset.sum_comm]
 apply pG rfl
 intro i _
 rw [← bw8 U H hU (x i)]
 simp only [Finset.sum_mul,wB,pow_add]
 apply pG rfl
 intro l _
 ring
theorem fVW (σ:F →+* F) (x w:ι→F)
    (hx :cy x) (k m H :ℕ) (hkm:k+m=aU ι)
    (hH :H≤m) (a :Fin 2×Fin (H+1)→F)
    (ha : (az2 (fun b j=>oX x
      (if b=0 then w else fun i=>σ (w i)) j) m H).mulVec a=0) :
    ∃ R:F[X],a1f σ x w k H
      (mD (fun i=>a (0,i)))
      (mD (fun i=>a (1,i))) R:= by
  let U:=mD (fun i=>a (0,i))
  let V:=mD (fun i=>a (1,i))
  let z := fun i=>U.eval (x i)*w i+V.eval (x i)*σ (w i)
  have hU:=x7 (fun i=>a (0,i))
  have hV:=x7 (fun i=>a (1,i))
  have hzero : ∀ j<aU ι-(k+H),oX x z j=0:= by
    intro j hj
    have hj' : j<m-H := by omega
    have he :=(c76 _ m H a).mp ha ⟨j,hj'⟩
    rw [zh] at he
    simp only [Fin.isValue,ite_true,ite_false,zero_ne_one,C4] at he
    have hs :oX x z j =
        (∑ l:Fin (H+1),a (0,l)*oX x w (l.val+j))+
        ∑ l:Fin (H+1),a (1,l)*oX x (fun i=>σ (w i)) (l.val+j) := by
      change oX x (fun i=>U.eval (x i)*w i+V.eval (x i)*σ (w i)) j= _
      have hlin:=v8 x
        (fun i=>U.eval (x i)*w i) (fun i=>V.eval (x i)*σ (w i)) 1 1 j
      simp only [oZ] at hlin
      rw [hlin,bhJ x w U H j hU,
        bhJ x (fun i=>σ (w i)) V H j hV]
      simp only [U,V,yl]
    exact hs.trans he
  obtain ⟨R,hR,hRv⟩:=Principal.b2G x hx z (k+H) (by omega) hzero
  refine ⟨R,hU,hV,hR,?_⟩
  intro i
  exact (hRv i (qU i)).symm
theorem cBn (H :ℕ) (a :Fin 2×Fin (H+1)→F) (ha :a≠0) :
   mD (fun i=>a (0,i))≠0 ∨
    mD (fun i=>a (1,i))≠0:= by
 by_contra h
 push Not at h
 have hcoeff (b:Fin 2) (hb:mD (fun i=>a (b,i))=0)
    (i:Fin (H+1)) :a (b,i)=0:= by
   have he :=oz (fun P:F[X]=>P.coeff i.val) hb
   simpa only [yl,coeff_zero] using he
 apply ha
 funext z
 rcases z with ⟨b,i⟩
 have hb:b=0∨b=1 := by omega
 rcases hb with rfl | rfl
 · exact hcoeff 0 h.1 i
 · exact hcoeff 1 h.2 i
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
def af7 (p:ℕ) (x u v :ι→F) (m H :ℕ) :
    oD (Fin (m-H)) (Fin 2×Fin (H+1)) F[X] :=
  fun j b=>t6 p x u v b.1 (b.2.val+j.val)
theorem c3y (φ:F[X] →+* Bx.lN F)
 (p:ℕ) (x u v :ι→F) (m H :ℕ) :
 (af7 p x u v m H).map φ =
   az2 (fun b j=>φ (t6 p x u v b j)) m H :=rfl
theorem eJZ (p:ℕ) [oy F p]
   (x u v :ι→F) (hfixed : ∀ i,x i^p=x i) (γ:F) (b:Fin 2) (j:ℕ) :
   (t6 p x u v b j).eval γ =
     oX x (if b=0 then fun i=>u i+γ*v i else fun i=>(u i+γ*v i)^p) j:= by
 have hs :oX x (fun i=>u i+γ*v i) j=oX x u j+γ*oX x v j:= by
   simpa only [oZ] using v8 x u v 1 γ j
 by_cases hb:b=0
 · simpa only [t6,hb,ite_true,qm,oq,pC,qy] using hs.symm
 · simp only [t6,hb,ite_false,
     qm,oq,pC,t7,qy]
   rw [bxn p x hfixed,hs]
   exact (vi (qG F p) _ _).trans (by rw [pU]; rfl) |>.symm
theorem eOn (p:ℕ) [oy F p] (hp:1≤p)
   (x u v :ι→F) (m H :ℕ)
   (hnull:Bx.ay6 (af7 p x u v m H)=1) :
   ∃ Q:Fin 2×Fin (H+1)→F[X],yQ Q ∧
     (af7 p x u v m H).mulVec Q=0 ∧
     (∀ b,(Q b).natDegree≤(2*H+1)*p) ∧
     ∀ γ:F,(fun b=>(Q b).eval γ)≠0:= by
 let N :=af7 p x u v m H
 have hr :Bx.adJ N=2*H+1 := by
   have h:=Bx.cep N
   rw [hnull,HZ,sS ,sS] at h
   omega
 obtain ⟨B⟩:=zQ.a3O
   (vG F[X] (Bx.lN F)) N (2*H+1) hr
 have hdeg : ∀ j b,(N j b).natDegree≤p:= by
   intro j b
   have hh:=a8L p x u v (m-H) H (b.1,j) b.2
   have hh' : (N j b).natDegree≤(if b.1=0 then 1 else p) := by
     simpa only [N,af7,t6,AI,QO,Nat.add_comm] using hh
   exact hh'.trans (by split_ifs <;> omega)
 obtain ⟨Q,hprim,hQ,hdegQ,_⟩:=asZ.d4D B
   (IsFractionRing.injective F[X] (Bx.lN F))
   (by simp only [HZ,sS]; omega) (fun _=>p) hdeg
 refine ⟨Q,hprim,hQ,?_,?_⟩
 · intro b
   simpa using hdegQ b
 · intro γ
   exact M4.bFs Q hprim γ
theorem gEM (p:ℕ) [oy F p] (hp:1≤p)
    (x u v :ι→F) (hx :cy x) (hfixed : ∀ i,x i^p=x i)
    (k m H :ℕ) (hkm:k+m=aU ι) (hH :H≤m)
    (hnull:Bx.ay6 (af7 p x u v m H)=1) :
    ∃ Q:Fin 2×Fin (H+1)→F[X],yQ Q ∧
      (af7 p x u v m H).mulVec Q=0 ∧
      (∀ b,(Q b).natDegree≤(2*H+1)*p) ∧
      ∀ γ:F,∃ R:F[X],
        (mD (fun i=>(Q (0,i)).eval γ)≠0 ∨
          mD (fun i=>(Q (1,i)).eval γ)≠0) ∧
        a1f (qG F p) x (fun i=>u i+γ*v i) k H
          (mD (fun i=>(Q (0,i)).eval γ))
          (mD (fun i=>(Q (1,i)).eval γ)) R:= by
  obtain ⟨Q,hprim,hQ,hdeg,hne⟩:=eOn p hp x u v m H hnull
  refine ⟨Q,hprim,hQ,hdeg,?_⟩
  intro γ
  let a := fun b=>(Q b).eval γ
  have hk : (az2 (fun b j=>oX x
      (if b=0 then fun i=>u i+γ*v i else fun i=>(u i+γ*v i)^p) j) m H).mulVec a=0:= by
    funext j
    have he :=oz (nX γ) (ov hQ j)
    simpa only [p9,p5 ,map_sum,pU,zf ,af7,
      qz ,eJZ p x u v hfixed γ,
      az2,aVg,wA,a,zc] using he
  obtain ⟨R,hR⟩:=fVW (qG F p) x (fun i=>u i+γ*v i)
    hx k m H hkm hH a hk
  exact ⟨R,cBn H a (hne γ),hR⟩
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β:Type} [lI F] [lz F] [c9 ι] [lz ι] [c9 β]
theorem cwQ (x :ι→F) (hx :cy x) (i:ι) :oK x i≠0:= by
 apply inv_ne_zero
 apply Finset.prod_ne_zero_iff.mpr
 intro j hj
 apply sub_ne_zero.mpr
 intro hij
 exact (Finset.mem_erase.mp hj).1 (hx hij).symm
theorem gMb (σ:F →+* F) (x :ι→F) (hfixed : ∀ i,σ (x i)=x i) (i:ι) :
  σ (oK x i)=oK x i:= by
 simp only [oK,map_inv₀,map_prod,map_sub,hfixed]
theorem cr7 (x :ι→F) (hx :cy x) (P:F[X])
   (k j:ℕ) (hP:P.degree<k) (hj:k+j<aU ι) :
   oX x (fun i=>P.eval (x i)) j=0:= by
 by_cases hp:P=0
 · simp [oX,hp]
 have hpn:=(qJ hp).mpr hP
 have hdeg: (P*(nq:F[X])^j).degree<(aU ι-1 :ℕ) := by
   apply degree_le_natDegree.trans_lt
   have hd:=natDegree_mul_le (p:=P) (q:=((nq:F[X])^j))
   simp only [natDegree_X_pow] at hd
   exact_mod_cast (show (P*(nq:F[X])^j).natDegree<aU ι-1 by omega)
 simpa only [oX,oq,t7,qy ,vk] using dl1 x hx (P*(nq:F[X])^j) hdeg
theorem dgw (x w:ι→F) (hx :cy x) (P:F[X])
  (k j:ℕ) (hP:P.degree<k) (hj:k+j<aU ι) :
  oX x w j=oX x (fun i=>w i-P.eval (x i)) j:= by
 have hz :=cr7 x hx P k j hP hj
 have hl:=v8 x w (fun i=>P.eval (x i)) 1 (-1) j
 simpa only [oZ,neg_one_mul,sub_eq_add_neg,hz,neg_zero,wY] using hl.symm
def bnN (σ:β→F →+* F) (x w:ι→F) (L t:ℕ) :
    oD (β×Fin L) (Fin (t+1)) F :=
  fun b j=>σ b.1 (oX x w (b.2.val+j.val))
def bcN (σ:β→F →+* F) (x e :ι→F) (L:ℕ) :oD (β×Fin L) ι F :=
 fun b i=>σ b.1 (e i)*x i^b.2.val
def b9Q (x :ι→F) (t:ℕ) :oD ι (Fin (t+1)) F:= fun i j=>x i^j.val
theorem c1A (x :ι→F) (hx :cy x)
   (t:ℕ) (hcard:aU ι≤t+1) :vh (b9Q x t).mulVecLin:= by
 intro w
 obtain ⟨P,hPw⟩:=cDq x hx (t+1) hcard w
 refine ⟨fun j=>(P:F[X]).coeff j.val,?_⟩
 funext i
 change (∑ j:Fin (t+1),x i^j.val*(P:F[X]).coeff j.val)=w i
 rw [show (∑ j:Fin (t+1),x i^j.val*(P:F[X]).coeff j.val)=
     ∑ j:Fin (t+1),(P:F[X]).coeff j.val*x i^j.val by apply pG rfl; intro j _; ring]
 rw [bw8 _ t (Principal.ayC P)]
 exact ov hPw i
theorem c6I {row mid col:Type} [c9 row] [c9 mid] [c9 col]
  (A:oD row mid F) (B:oD mid col F) (hB:vh B.mulVecLin) :
  (A*B).rank=A.rank := by
 rw [Matrix.rank,Matrix.rank,Matrix.mulVecLin_mul,
  Gi _ (LinearMap.range_eq_top.mpr hB)]
theorem dOX (σ:β→F →+* F)
    (x w:ι→F) (hx :cy x) (hfixed : ∀ b i,σ b (x i)=x i)
    (P:F[X]) (k L t:ℕ) (hP:P.degree<k) (hsize :k+L+t≤aU ι)
    (S:lJ ι) (hagree : ∀ i,i∉S→w i=P.eval (x i)) :
    bnN σ x w L t=
      pL (fun b (i:S)=>oK x i.val*σ b.1 (w i.val-P.eval (x i.val))*x i.val^b.2.val)*
        b9Q (fun i:S=>x i.val) t:= by
  ext b j
  change σ b.1 (oX x w (b.2.val+j.val))=∑ i:S,
    (oK x i.val*σ b.1 (w i.val-P.eval (x i.val))*x i.val^b.2.val)*x i.val^j.val
  rw [dgw x w hx P k _ hP (by have :=b.2.isLt; have :=j.isLt; omega)]
  simp only [oX,map_sum,pU,map_pow,gMb _ x (hfixed b.1),hfixed]
  rw [Av S (fun i =>
    oK x i*σ b.1 (w i-P.eval (x i))*x i^b.2.val*x i^j.val)]
  have hs : (∑ i:ι,oK x i*σ b.1 (w i-P.eval (x i))*x i^(b.2.val+j.val))=
      ∑ i∈S,oK x i*σ b.1 (w i-P.eval (x i))*x i^(b.2.val+j.val) := by
    symm
    apply G2 (zg S)
    intro i _ hi
    simp [hagree i hi]
  rw [hs]
  apply pG rfl
  intro i _
  rw [pow_add]
  ring
theorem cHH (σ:β→F →+* F)
   (x w:ι→F) (hx :cy x) (hfixed : ∀ b i,σ b (x i)=x i)
   (P:F[X]) (k L t:ℕ) (hP:P.degree<k) (hsize :k+L+t≤aU ι)
   (S:lJ ι) (hS:S.card≤t+1) (hagree : ∀ i,i∉S→w i=P.eval (x i)) :
   (bnN σ x w L t).rank=
     (bcN σ (fun i:S=>x i.val) (fun i:S=>w i.val-P.eval (x i.val)) L).rank := by
 rw [dOX σ x w hx hfixed P k L t hP hsize S hagree]
 have hB:vh (b9Q (fun i:S=>x i.val) t).mulVecLin :=
   c1A (fun i:S=>x i.val)
     (fun i j hij=>u8 (hx hij)) t (by simpa only [vl] using hS)
 rw [c6I _ _ hB]
 let N :=bcN σ (fun i:S=>x i.val) (fun i:S=>w i.val-P.eval (x i.val)) L
 have heq :pL (fun b (i:S)=>oK x i.val*σ b.1 (w i.val-P.eval (x i.val))*x i.val^b.2.val)=
     pL (fun b (i:S)=>(1:F)*N b i*oK x i.val) := by
   ext b i
   simp only [N,bcN,Au,oZ]
   ring
 rw [heq,ceu N (fun _=>1) (fun i=>weight x i.val) (by simp)
   (fun i=>cwQ x hx i.val)]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β:Type} [lI F] [lz F]
def a7D (s :β→ℕ→F) (m t:ℕ) :th F F[X] :=
  ox F (t+1) ⊓ ⨅ b,⨅ j:Fin (m-t),
    n5 (Principal.az1 (s b) j.val)
theorem b80 (s :β→ℕ→F) (m t:ℕ) (P:F[X]) :
  P∈a7D s m t↔P.degree<(t+1 :ℕ) ∧
    ∀ b j,j<m-t→Principal.az1 (s b) j P=0:= by
 simp only [a7D,Submodule.mem_inf,Polynomial.mem_degreeLT,Submodule.mem_iInf,
  LinearMap.mem_ker,Fin.forall_iff]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β:Type} [lI F] [lz F] [c9 β]
def aWQ (s :β→ℕ→F) (m t:ℕ) :
    oD (β×Fin (m-t)) (Fin (t+1)) F:= fun b j=>s b.1 (j.val+b.2.val)
theorem ceR (s :β→ℕ→F) (m t:ℕ) (P:F[X]) :
   P∈a7D s m t↔P.natDegree≤t ∧
     (aWQ s m t).mulVec (fun j=>P.coeff j.val)=0:= by
 rw [b80]
 constructor
 · rintro ⟨hP,hrec⟩
   have hn:P.natDegree≤t:=Principal.ayC ⟨P,Polynomial.mem_degreeLT.mpr hP⟩
   refine ⟨hn,?_⟩
   funext b
   have hh:=hrec b.1 b.2.val b.2.isLt
   rw [Principal.bLa _ _ t P hn] at hh
   simpa only [aWQ,p9,p5 ,zc,xW] using hh
 · rintro ⟨hn,hker⟩
   refine ⟨degree_le_natDegree.trans_lt (by exact_mod_cast (show P.natDegree<t+1 by omega)),?_⟩
   intro b j hj
   rw [Principal.bLa _ _ t P hn]
   have hh:=ov hker (b,⟨j,hj⟩)
   simpa only [aWQ,p9,p5 ,zc,xW] using hh
def etM (s :β→ℕ→F) (m t:ℕ) :
    (n5 (aWQ s m t).mulVecLin) ≃ₗ[F] a7D s m t where
  toFun a :=⟨mD a.val,(ceR s m t _).mpr
    ⟨x7 _,by
      have ha : (aWQ s m t).mulVec a.val=0:=a.property
      simpa only [yl] using ha⟩⟩
  invFun P:=⟨fun j=>(P.val).coeff j.val,((ceR s m t _).mp P.property).2⟩
  left_inv a := by apply u8; funext j; exact yl a.val j
  right_inv P:= by
    apply u8
    exact Principal.bUf t P.val ((ceR s m t _).mp P.property).1
  map_add' a b:= by
    apply u8
    simp only [mD,Gk,Pi.add_apply,vi ,
      Ef]
  map_smul' c a := by
    apply u8
    simp only [mD,G7,xL,← Polynomial.smul_monomial,
      Finset.smul_sum,z7]
theorem fU7 (s :β→ℕ→F) (m t:ℕ) :
   nI F (a7D s m t)=
    nI F (n5 (aWQ s m t).mulVecLin) :=
 (etM s m t).finrank_eq.symm
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [lz F] [c9 ι] [lz ι]
def a9j (σ:F →+* F) :Fin 2→F →+* F := ![RingHom.id F,σ]
theorem dOW (σ:F →+* F) (x e :ι→F) (L:ℕ) :
  bcN (a9j σ) x e L=afy σ x e L:= by
 ext ⟨b,j⟩ i
 fin_cases b <;> simp [bcN,a9j,afy]
def bG1 (p blocks :ℕ) (x u v :ι→F) (L t:ℕ) :
    oD (Fin blocks×Fin L) (Fin (t+1)) F[X] := fun b j =>
  C (oX x u (b.2.val+j.val)^(p^b.1.val))+
    (nq:F[X])^(p^b.1.val)*C (oX x v (b.2.val+j.val)^(p^b.1.val))
theorem dfp (p:ℕ) [oy F p] (x u v :ι→F) (L t:ℕ) :
  AI p x u v L t=bG1 p 2 x u v L t:= by
 ext ⟨b,i⟩ j
 fin_cases b <;> simp [AI,QO,bG1]
theorem cTe (p:ℕ) [oy F p] (blocks :ℕ)
    (x u v :ι→F) (L t:ℕ) (γ:F) :
    (bG1 p blocks x u v L t).map (nX γ)=
      bnN (fun b:Fin blocks=>iterateFrobenius F p b.val)
        x (fun i=>u i+γ*v i) L t:= by
  ext b j
  have hs :=v8 x u v 1 γ (b.2.val+j.val)
  simp only [oZ] at hs
  simp only [bG1,xu,qz ,qm,
    oq,pC,t7,qy]
  change (oX x u (b.2.val+j.val))^(p^b.1.val)+
    γ^(p^b.1.val)*(oX x v (b.2.val+j.val))^(p^b.1.val)=_
  rw [bnN,hs,vi ,pU]
  rfl
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β:Type} [lI F] [lz F] [c9 ι] [lz ι] [c9 β]
theorem ezQ {row col:Type} [c9 row] [c9 col]
  (M:oD row col F) (hr :M.rank=aU col) :cy M.mulVecLin:= by
 have hn:=t8 M.mulVecLin
 change M.rank+Module.finrank F (n5 M.mulVecLin)=_ at hn
 rw [t3 ,hr] at hn
 have hk :nI F (n5 M.mulVecLin)=0:= by omega
 exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
theorem bsf (x :ι→F) (hx :cy x)
   (S:lJ ι) (P:F[X]) (hz : ∀ i∈S,P.eval (x i)=0) :mL x S∣P:= by
 classical
 by_cases hP:P=0
 · simp [hP]
 have hroots : (mL x S).roots≤P.roots := by
   rw [Principal.bIF]
   apply (Hw (S.nodup.map hx)).mpr
   intro a ha
   obtain ⟨i,hi,rfl⟩:=Multiset.mem_map.mp ha
   exact (t5 hP).mpr (hz i hi)
 exact (Principal.bIG x S).dvd_of_roots_le_roots (S8 x S).ne_zero hroots
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
def aIb (x :ι→F) (w:ι→F[X]) :p6 (p6 F) :=
 ∑ i,lV (w i)*(Lagrange.basis oY x i).map (lV:F →+* F[X])
theorem eoU (x :ι→F) (w:ι→F[X]) (γ:F) :
  (aIb x w).map (nX γ)=
    GR oY x (fun i=>(w i).eval γ) := by
 have hcomp: (nX γ).comp (lV:F →+* F[X])=RingHom.id F:= by ext c; simp
 simp only [aIb,Polynomial.map_sum,Bf ,Polynomial.map_C,
  Fa ,hcomp,Polynomial.map_id,Lagrange.interpolate_apply,qz]
theorem eoV (x :ι→F) (hx :cy x)
   (w:ι→F[X]) (a :ι) :
   (aIb x w).eval (lV (x a))=w a := by
 classical
 simp only [aIb,qx ,oq,pC,Dz]
 rw [Finset.sum_eq_single a]
 · rw [Lagrange.eval_basis_self hx.injOn (qU a)]
   simp
 · intro b hb hba
   rw [Lagrange.eval_basis_of_ne hba (qU a)]
   simp
 · simp
theorem eoS (x :ι→F) (w:ι→F[X]) (B:ℕ)
  (hw : ∀ i,(w i).natDegree≤B) (j:ℕ) :
  ((aIb x w).coeff j).natDegree≤B:= by
 simp only [aIb,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,wR]
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro i _
 exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C,wY] using hw i)
theorem eoT [c9 F] (x :ι→F) (hx :cy x)
    (w:ι→F[X]) (D B:ℕ) (hD:D≤aU ι)
    (hw : ∀ i,(w i).natDegree≤B) (hB:B<aU F)
    (houtput : ∀ γ:F,∃ R:F[X],R.degree<D ∧ ∀ i,R.eval (x i)=(w i).eval γ) :
    (aIb x w).degree<D:= by
  classical
  apply (Polynomial.degree_lt_iff_coeff_zero _ D).mpr
  intro j hj
  have hzero : ∀ γ:F,((aIb x w).coeff j).eval γ=0:= by
    intro γ
    obtain ⟨R,hR,hRv⟩:=houtput γ
    have hRlt:R.degree<(aU ι:ℕ) :=hR.trans_le (by exact_mod_cast hD)
    have heq :R=(aIb x w).map (nX γ) := by
      rw [eoU]
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq oY hx.injOn
        (by simpa only [uh] using hRlt)
        (GY _ hx.injOn)
      intro i hi
      rw [G8 _ hx.injOn hi,hRv i]
    have hc:=oz (fun Q:F[X]=>Q.coeff j) heq
    rw [wR] at hc
    have hrzero :R.coeff j=0:=Polynomial.coeff_eq_zero_of_degree_lt
      (hR.trans_le (by exact_mod_cast hj))
    exact (hc.symm.trans hrzero)
  exact GF _ Function.injective_id hzero
    ((eoS x w B hw j).trans_lt hB)
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
theorem b4H (p:ℕ) (x u v :ι→F)
    (m a b c:ℕ) (hc:c≤m) (hsum:a+b+c=2*m+2)
    (ha :a≤b) (hb:b<c) (hc2 :1<c)
    (hHF:aKl
      (fun b j=>vG F[X] (Bx.lN F)
        (t6 p x u v b j)) m a b c) :
    Bx.ay6 (af7 p x u v m (m+1-c))=1 := by
  change nI (Bx.lN F) (n5
    ((af7 p x u v m (m+1-c)).map (vG F[X] (Bx.lN F))).mulVecLin)=1
  rw [c3y]
  exact eAu _ m a b c hc hsum ha hb hc2 hHF
theorem c75 (m L t r a b c:ℕ)
 (hm:m=L+t) (hc:c≤m) (hsum:a+b+c=2*m+2) (hr :r+a+b=2*t+2) :
 L+(m+1-c)+r=t+1 := by omega
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 F] [c9 ι] [lz ι]
theorem bA7 (H :ℕ) (q:Fin (H+1)→F[X]) (a :F) :
  (mD q).eval (lV a)=zd q a := by
 simp only [mD,qx ,eval_monomial,zd]
 apply pG rfl
 intro j _
 rw [← Polynomial.C_pow]
 ring
theorem eM9 (p:ℕ) [oy F p] (hp:1≤p)
    (x u v :ι→F) (hx :cy x) (k H δ:ℕ)
    (hsize :k+H≤aU ι) (hcard:δ+p<aU F)
    (Q:Fin 2×Fin (H+1)→F[X]) (hQdeg : ∀ b,(Q b).natDegree≤δ)
    (hsection : ∀ γ:F,∃ R:F[X],a1f (qG F p) x (fun i=>u i+γ*v i) k H
      (mD (fun j=>(Q (0,j)).eval γ))
      (mD (fun j=>(Q (1,j)).eval γ)) R) :
    ∃ R:p6 (p6 F),R.degree<(k+H :ℕ) ∧ ∀ i,
      (mD (fun j=>Q (0,j))).eval (lV (x i))*
        (lV (u i)+(nq:F[X])*lV (v i))+
      (mD (fun j=>Q (1,j))).eval (lV (x i))*
        (lV (u i^p)+(nq:F[X])^p*lV (v i^p))=
      R.eval (lV (x i)) := by
  let word:ι→F[X] := fun i =>
    zd (fun j=>Q (0,j)) (x i)*(C (u i)+(nq:F[X])*C (v i))+
    zd (fun j=>Q (1,j)) (x i)*(C (u i^p)+(nq:F[X])^p*C (v i^p))
  have hword : ∀ i,(word i).natDegree≤δ+p:= by
    intro i
    have h0: (C (u i)+(nq:F[X])*C (v i)).natDegree≤1 := by compute_degree
    have h1 : (C (u i^p)+(nq:F[X])^p*C (v i^p)).natDegree≤p:= by compute_degree
    have hU:=Principal.bsZ (fun j=>Q (0,j)) (fun j=>hQdeg (0,j)) (x i)
    have hV:=Principal.bsZ (fun j=>Q (1,j)) (fun j=>hQdeg (1,j)) (x i)
    exact (Polynomial.natDegree_add_le _ _).trans (max_le
      (Polynomial.natDegree_mul_le.trans (by omega)) (Polynomial.natDegree_mul_le.trans (by omega)))
  have houtput : ∀ γ:F,∃ R:F[X],R.degree<(k+H :ℕ) ∧ ∀ i,R.eval (x i)=(word i).eval γ:= by
    intro γ
    obtain ⟨R,hR⟩:=hsection γ
    refine ⟨R,hR.degree_R,?_⟩
    intro i
    have hU:=Principal.b9P (fun j=>Q (0,j)) (x i) γ
    have hV:=Principal.b9P (fun j=>Q (1,j)) (x i) γ
    rw [Et] at hU hV
    have hpower : (u i+γ*v i)^p=u i^p+γ^p*v i^p:= by
      have hh:=vi (qG F p) (u i) (γ*v i)
      rw [pU] at hh
      simpa only [frobenius_def] using hh
    dsimp only [word]
    simp only [qm,oq,pC,qy ,t7]
    rw [hU,hV,← hpower]
    exact (hR.nodes i).symm
  refine ⟨aIb x word,eoT x hx word (k+H) (δ+p)
    hsize hword hcard houtput,?_⟩
  intro i
  rw [bA7,bA7,eoV x hx word i]
theorem evs (p:ℕ) [oy F p] (hp:1≤p)
    (x u v :ι→F) (hx :cy x) (hfixed : ∀ i,x i^p=x i)
    (k m H :ℕ) (hkm:k+m=aU ι) (hH :H≤m)
    (hcard: (2*H+2)*p<aU F)
    (hnull:Bx.ay6 (af7 p x u v m H)=1) :
    ∃ (Q:Fin 2×Fin (H+1)→F[X]) (R:p6 (p6 F)),
      yQ Q∧(af7 p x u v m H).mulVec Q=0 ∧
      (∀ b,(Q b).natDegree≤(2*H+1)*p)∧R.degree<(k+H :ℕ) ∧
      ∀ i,
        (mD (fun j=>Q (0,j))).eval (lV (x i))*
          (lV (u i)+(nq:F[X])*lV (v i))+
        (mD (fun j=>Q (1,j))).eval (lV (x i))*
          (lV (u i^p)+(nq:F[X])^p*lV (v i^p))=
        R.eval (lV (x i)) := by
  obtain ⟨Q,hprim,hQ,hdeg,hsection⟩:=gEM p hp x u v hx hfixed k m H hkm hH hnull
  have hcard' : (2*H+1)*p+p<aU F:= by nlinarith [hcard]
  obtain ⟨R,hR,hRv⟩:=eM9 p hp x u v hx k H ((2*H+1)*p)
    (by omega) hcard' Q hdeg (by intro γ; obtain ⟨R,_,hR⟩:=hsection γ; exact ⟨R,hR⟩)
  exact ⟨Q,R,hprim,hQ,hdeg,hR,hRv⟩
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
local instance gPJ (P:Prop) :xm P:=zi P
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
structure bRV (p:ℕ) (x u v :ι→F) (L t:ℕ)
  (Δ:F[X]) where
 fixedRoots :lJ ι
 movingDegree :ℕ
 quotientDegree :ℕ
 moving_pos :0< movingDegree
 boS:fixedRoots.card+movingDegree+quotientDegree=t
 coefficients :Fin (movingDegree+1)→F[X]
 bnv : ∀ j,(coefficients j).natDegree≤p*movingDegree
 primitive_specialization : ∀ γ,sH coefficients γ≠0
 no_additional_fixed_root : ∀ i,i∉fixedRoots→avE coefficients (x i)≠0
 normal_nullity : ∀ γ,Δ.eval γ≠0 →
  nI F (n5
    ((AI p x u v L t).map (nX γ)).mulVecLin)=quotientDegree+1
 multiples_annihilate : ∀ γ (Q:ox F (quotientDegree+1)),
  ((AI p x u v L t).map (nX γ)).mulVec
    (aOU (mL x fixedRoots*sH coefficients γ)
      quotientDegree t Q)=0
theorem eOs (p:ℕ) [oy F p]
    (x :ι→F) (hx :cy x) (hfixed : ∀ i,x i^p=x i)
    (u v :ι→F) (k A L t δ:ℕ) (hkA:k<A)
    (hL:k+L=A) (ht:A+t=aU ι)
    (Δ:F[X]) (hΔ:Δ≠0) (hΔdeg:Δ.natDegree≤δ)
    (cert:bRV p x u v L t Δ)
    (Γ:lJ F) (hΓ : ∀ γ∈Γ,akD x u v k A γ) :
    Γ.card≤δ+p*(aU ι-cert.fixedRoots.card) := by
  classical
  let H :=cert.fixedRoots
  let d:=cert.movingDegree
  let q:=cert.quotientDegree
  let vcoeff :=cert.coefficients
  let V:=sH vcoeff
  have hroots (γ:F) (hγΓ:γ∈Γ) (hγΔ:Δ.eval γ≠0) :
      d≤(Finset.univ.filter
        (fun i : {i // i∉H} => (V γ).eval (x i.val)=0)).card:= by
    obtain ⟨T,hT,⟨P,hP,hPv⟩,hnonjoint⟩ :=
      cCP x hx u v k A hkA γ (hΓ γ hγΓ)
    let S:=oY \ T
    have hScard:S.card=t:= by
      dsimp [S]
      rw [Il (zg T),uh,hT]
      omega
    have hagree : ∀ i,i∉S→u i+γ*v i=P.eval (x i) := by
      intro i hi
      have TA:i∈T:= by simpa only [S,Finset.mem_sdiff,Finset.mem_univ,
        true_and,not_not] using hi
      exact (hPv i TA).symm
    have hker :=b8c p x hx hfixed u v γ k L t (by omega)
      P hP S (by omega) hagree
    let g:=mL x H*V γ
    have hg:g≠0:=pQ (S8 x H).ne_zero
      (cert.primitive_specialization γ)
    have hga :g.natDegree≤H.card+d:= by
      exact Polynomial.natDegree_mul_le.trans
        (by rw [ZQ]; exact JM (de9 _ _) _)
    have hsize :H.card+d+q=t:=cert.boS
    obtain ⟨Q,hQ,hfactor⟩:=c1F (H.card+d) q t
      ((AI p x u v L t).map (nX γ)) g hg hga
      (by omega) (cert.normal_nullity γ hγΔ) (cert.multiples_annihilate γ)
      (mL x S) (by rw [ZQ,hScard]) hker
    have hVdegree : (V γ).natDegree=d:= by
      apply eey (mL x H) (V γ) Q H.card d q
        (ZQ x H) (de9 _ _) hQ
      rw [← hfactor,ZQ,hScard,hsize]
    obtain ⟨hdiv,havoid⟩:=fWg x hx H S (V γ) Q hfactor
    rw [fX7 x H (V γ) havoid,
      ← cK0 x hx (S \ H) (V γ) hdiv,hVdegree]
  have hcount:=eOx
    (fun i : {i // i∉H} => x i.val) V
    (fun i : {i // i∉H} => avE vcoeff (x i.val)) p d δ
    cert.moving_pos
    (fun i=>cert.no_additional_fixed_root i.val i.property)
    (fun i=>bsZ vcoeff cert.bnv (x i.val))
    (fun i γ=>b9P vcoeff (x i.val) γ)
    Δ hΔ hΔdeg Γ hroots
  have hcard:aU {i // i∉H} = aU ι-H.card:= by simp
  simpa only [hcard] using hcount
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
local instance gPE (P:Prop) :xm P:=zi P
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
theorem dPc (p:ℕ) (x u v :ι→F) (L t:ℕ)
   (c:Fin (t+1)→F)
   (hc: (AI p x u v L t).mulVec (fun j=>C (c j))=0) :
   (∀ i:Fin L,∑ j:Fin (t+1),oX x u (i.val+j.val)*c j=0) ∧
   (∀ i:Fin L,∑ j:Fin (t+1),oX x v (i.val+j.val)*c j=0) := by
 have hrow (i:Fin L) :
     ∑ j:Fin (t+1),(QO x u v L t i j)*C (c j)=0:= by
   have hi:=ov hc (0,i)
   simpa [AI,p9,p5] using hi
 have hu (i:Fin L) : ∑ j:Fin (t+1),
     oX x u (i.val+j.val)*c j=0:= by
   have h:=oz (EP (0:F)) (hrow i)
   simpa [QO,qx] using h
 refine ⟨hu,fun i => ?_⟩
 have h:=oz (EP (1:F)) (hrow i)
 simp only [QO,qx ,oq,qm,
   pC,qy ,oZ,eval_zero] at h
 simp_rw [add_mul] at h
 rw [Ef ,hu i,zero_add] at h
 exact h
structure by1 (p:ℕ) (x u v :ι→F) (L t:ℕ)
  (Δ:F[X]) where
 space :th F (Fin (t+1)→F)
 generic_annihilates : ∀ c∈space,
  (AI p x u v L t).mulVec (fun j=>C (c j))=0
 normal_inclusion : ∀ γ,Δ.eval γ≠0 → ∀ c,
  ((AI p x u v L t).map (nX γ)).mulVec c=0→c∈space
theorem dO9 (p:ℕ) [oy F p]
   (x :ι→F) (hx :cy x) (hfixed : ∀ i,x i^p=x i)
   (u v :ι→F) (k A L t:ℕ) (hkA:k<A)
   (hL:k+L=A) (ht:A+t=aU ι)
   (Δ:F[X]) (hcert:by1 p x u v L t Δ)
   (γ:F) (hγ:Δ.eval γ≠0) : ¬ akD x u v k A γ:= by
 intro hbad
 obtain ⟨T,hT,⟨P,hP,hPv⟩,hnonjoint⟩:=cCP x hx u v k A hkA γ hbad
 let S:=oY \ T
 have hScard:S.card=t:= by
   dsimp [S]
   rw [Il (zg T),uh,hT]
   omega
 have hagree : ∀ i,i∉S→u i+γ*v i=P.eval (x i) := by
   intro i hi
   have TA:i∈T:= by simpa only [S,Finset.mem_sdiff,Finset.mem_univ,
     true_and,not_not] using hi
   exact (hPv i TA).symm
 have hker :=b8c p x hx hfixed u v γ k L t (by omega)
   P hP S (by omega) hagree
 have hmem:=hcert.normal_inclusion γ hγ
   (fun j:Fin (t+1)=>(mL x S).coeff j.val) hker
 obtain ⟨hu,hv⟩:=dPc p x u v L t _
   (hcert.generic_annihilates _ hmem)
 have hEu:=cUy x u (mL x S) L t
   (by rw [ZQ,hScard]) hu
 have hEv :=cUy x v (mL x S) L t
   (by rw [ZQ,hScard]) hv
 have hU:=b2F x hx u k L S (by omega) hEu
 have hV:=b2F x hx v k L S (by omega) hEv
 have hcomp:oY \ S=T:= by simp [S]
 rw [hcomp] at hU hV
 exact hnonjoint ⟨hU,hV⟩
theorem cHT (p:ℕ) [oy F p]
   (x :ι→F) (hx :cy x) (hfixed : ∀ i,x i^p=x i)
   (u v :ι→F) (k A L t δ:ℕ) (hkA:k<A)
   (hL:k+L=A) (ht:A+t=aU ι)
   (Δ:F[X]) (hΔ:Δ≠0) (hΔdeg:Δ.natDegree≤δ)
   (hcert:by1 p x u v L t Δ)
   (Γ:lJ F) (hΓ : ∀ γ∈Γ,akD x u v k A γ) :Γ.card≤δ:= by
 apply le_trans (b:=Δ.natDegree)
 · apply Ee
   intro γ hγ
   apply (t5 hΔ).mpr
   by_contra hn
   exact dO9 p x hx hfixed u v k A L t hkA hL ht
     Δ hcert γ hn (hΓ γ hγ)
 · exact hΔdeg
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F J:Type*} [lI F]
theorem gE3 (a b:J→F) (p:ℕ) (hp:1<p)
   (hminor : ∀ i j,
     ((C (a i)+(nq:F[X])*C (b i)) :F[X])*(C (a j^p)+(nq:F[X])^p*C (b j^p)) =
     (C (a j)+(nq:F[X])*C (b j))*(C (a i^p)+(nq:F[X])^p*C (b i^p))) :
   a=0 ∨ ∃ c:F,∀ i,b i=c*a i:= by
 classical
 by_cases ha :a=0
 · exact Or.inl ha
 right
 have han : ∃ j,a j≠0:= by
   by_contra h
   apply ha
   funext j
   simpa using not_exists.mp h j
 obtain ⟨j,hj⟩:=han
 have hjp:a j^p≠0:=pow_ne_zero _ hj
 refine ⟨b j/a j,fun i => ?_⟩
 have h0:=oz (fun q:F[X]=>q.coeff 0) (hminor i j)
 have h1 :=oz (fun q:F[X]=>q.coeff 1) (hminor i j)
 have hpoly (i j:J) :
     ((C (a i)+(nq:F[X])*C (b i)) :F[X])*(C (a j^p)+(nq:F[X])^p*C (b j^p)) =
     C (a i*a j^p)+C (b i*a j^p)*(nq:F[X]) +
     C (a i*b j^p)*(nq:F[X])^p+C (b i*b j^p)*(nq:F[X])^(p+1) := by
   simp only [pU]
   ring
 rw [hpoly,hpoly] at h0 h1
 simp only [coeff_add,coeff_C,coeff_C_mul_X,coeff_C_mul_X_pow] at h0 h1
 simp [show 0≠p by omega] at h0
 simp [show 1≠p by omega,show p≠0 by omega] at h1
 rw [div_mul_eq_mul_div]
 apply (eq_div_iff hj).mpr
 apply (mul_right_inj' hjp).mp
 linear_combination (a j)*h1-(b j)*h0
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
def bTJ (x u v :ι→F) (k p:ℕ) :Prop :=
  ∀ i j:Fin (aU ι-k),
    ((C (oX x u i.val)+(nq:F[X])*C (oX x v i.val)) *
      (C (oX x u j.val^p)+(nq:F[X])^p*C (oX x v j.val^p))) =
    ((C (oX x u j.val)+(nq:F[X])*C (oX x v j.val)) *
      (C (oX x u i.val^p)+(nq:F[X])^p*C (oX x v i.val^p)))
theorem gE1 (x :ι→F) (hx :cy x)
    (u v :ι→F) (k A p:ℕ) (hk :k≤aU ι) (hp:1<p)
    (hminor : ∀ i j:Fin (aU ι-k),
      ((C (oX x u i.val)+(nq:F[X])*C (oX x v i.val)) *
        (C (oX x u j.val^p)+(nq:F[X])^p*C (oX x v j.val^p))) =
      ((C (oX x u j.val)+(nq:F[X])*C (oX x v j.val)) *
        (C (oX x u i.val^p)+(nq:F[X])^p*C (oX x v i.val^p))))
    (Γ:lJ F) (hΓ : ∀ γ∈Γ,akD x u v k A γ) :Γ.card≤1 := by
  have hprop:=gE3
    (fun i:Fin (aU ι-k)=>oX x u i.val)
    (fun i:Fin (aU ι-k)=>oX x v i.val) p hp hminor
  rcases hprop with ha | ⟨c,hc⟩
  · have hu:NM x u k Finset.univ := by
      apply b2G x hx u k hk
      intro j hj
      exact ov ha ⟨j,hj⟩
    apply cCO x u v k A 1 0 (Or.inl C4) _ Γ hΓ
    simpa using hu
  · have hrel :NM x (fun i=>(-c)*u i+v i) k Finset.univ := by
      apply b2G x hx _ k hk
      intro j hj
      have h:=hc ⟨j,hj⟩
      have hl:=aAt x u v (-c) 1 j
      simp only [oZ] at hl
      rw [hl,h]
      ring
    apply cCO x u v k A (-c) 1 (Or.inr C4) _ Γ hΓ
    simpa only [oZ] using hrel
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset CoreDefinitions Code LinearCode
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 F] [c9 ι] [lz ι]
theorem ccW (x :ι ↪ F) (w:ι→F)
   (k :ℕ) [NeZero k] (T:lJ ι) :
   projectedWord w T∈projectedCodeSubmod (yo x k) T ↔
     NM x w k T:= by
 classical
 rw [LinearCode.mem_projectedCodeSubmod_iff]
 constructor
 · rintro ⟨c,hc,hproj⟩
   obtain ⟨P,hP,heval⟩:=ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hc
   refine ⟨P,Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hP),?_⟩
   intro i hi
   have h:=ov hproj ⟨i,hi⟩
   change w i=c i at h
   exact (heval i).trans h.symm
 · rintro ⟨P,hP,hPv⟩
   have hPn:P.natDegree<k := by
     by_cases h0:P=0
     · simpa [h0] using NeZero.pos k
     · exact (qJ h0).mpr hP
   refine ⟨fun i=>P.eval (x i),?_,?_⟩
   · exact ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨P,hPn,fun _=>rfl⟩
   · funext i
     exact (hPv i.val i.property).symm
theorem cVE (x :ι ↪ F) (U:Fin 2→ι→F)
   (k A:ℕ) [NeZero k] (δ:ℝ)
   (hthreshold : ∀ T:lJ ι,
     (aU ι:ℝ)*(1-δ)≤T.card→A≤T.card)
   (γ:F) (hmca :IsMCA (AffineLineGenerator F) (yo x k) γ U δ) :
   akD x (U 0) (U 1) k A γ:= by
 classical
 obtain ⟨T,hT,hcomb,j,hj⟩:=hmca
 refine ⟨T,hthreshold T hT,?_,?_⟩
 · apply (ccW x _ k T).mp
   simpa [AffineLineGenerator,zh,vj,xW] using hcomb
 · intro h
   fin_cases j
   · exact hj ((ccW x _ k T).mpr h.1)
   · exact hj ((ccW x _ k T).mpr h.2)
end
end gR.Principal
end
section
namespace gR.kL
noncomputable section
open Polynomial Matrix
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
structure axT (p:ℕ) (x u v :ι→F) (k H :ℕ) where
 coefficients :Fin 2×Fin (H+1)→F[X]
 output :p6 (p6 F)
 primitive :yQ coefficients
 coefficient_height : ∀ b,(coefficients b).natDegree≤(2*H+1)*p
 x_degree : ∀ b:Fin 2,(mD (fun j=>coefficients (b,j))).natDegree≤H
 output_degree :output.degree<(k+H :ℕ)
 nodes : ∀ i,
  (mD (fun j=>coefficients (0,j))).eval (lV (x i))*
    (lV (u i)+(nq:F[X])*lV (v i))+
  (mD (fun j=>coefficients (1,j))).eval (lV (x i))*
    (lV (u i^p)+(nq:F[X])^p*lV (v i^p))=
  output.eval (lV (x i))
def c4L [c9 F]
    (p:ℕ) [oy F p] (hp:1≤p) (x u v :ι→F)
    (hx :cy x) (hfixed : ∀ i,x i^p=x i)
    (k m H :ℕ) (hkm:k+m=aU ι) (hH :H≤m)
    (hcard: (2*H+2)*p<aU F)
    (hnull:Bx.ay6 (af7 p x u v m H)=1) :
    axT p x u v k H := by
  apply Classical.choice
  obtain ⟨Q,R,hprim,hQ,hdeg,hR,hRv⟩:=evs p hp x u v hx hfixed k m H hkm hH hcard hnull
  exact ⟨⟨Q,R,hprim,hdeg,fun b=>x7 _,hR,hRv⟩⟩
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace bz4
noncomputable section
open Polynomial Matrix Finset gR
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
def powers (x :ι→F) (b:ℕ) :oD ι (Fin b) F :=
 fun i j=>x i^j.val
omit [lz ι] in
theorem eNx (x :ι→F) (hx :cy x) (b:ℕ) :
  (powers x b).rank=min (aU ι) b:= by
 let e :=z8 F b
 have he : (powers x b).mulVecLin.comp e.toLinearMap=kL.a1S x b:= by
  ext P i
  change (∑ j:Fin b,x i^j.val*e P j)=(P:F[X]).eval (x i)
  rw [Polynomial.eval_eq_sum_degreeLTEquiv P.property]
  exact pG rfl (fun _ _=>xW _ _)
 rw [← kL.bVP x hx b,← he,
  Gi _ (LinearMap.range_eq_top.mpr e.surjective)]
 rfl
theorem cMD (x w:ι→F) (hx :cy x) (P:F[X])
  (k j:ℕ) (hP:P.degree<k) (hj:k+j<aU ι)
  (E :lJ ι) (hout : ∀ i,i∉E→w i=P.eval (x i)) :
  oX x w j = ∑ i∈E,(oK x i*(w i-P.eval (x i)))*x i^j:= by
 classical
 rw [kL.dgw x w hx P k j hP hj]
 symm
 apply G2 (zg E)
 intro i _ hi
 simp [hout i hi]
theorem eDQ (x w:ι→F) (hx :cy x) (P:F[X])
   (k l b:ℕ) (hP:P.degree<k) (hsize :k+l+b≤aU ι+1)
   (E :lJ ι) (hout : ∀ i,i∉E→w i=P.eval (x i)) :
   (pL (fun (i:Fin l) (j:Fin b)=>oX x w (i.val+j.val))) =
     (powers (fun i:E=>x i.val) l).transpose *
     yU (fun i:E=>oK x i.val*(w i.val-P.eval (x i.val))) *
     powers (fun i:E=>x i.val) b:= by
 ext i j
 rw [Matrix.of_apply,cMD x w hx P k _ hP (by have :=i.isLt; have :=j.isLt; omega)
   E hout,Matrix.mul_apply]
 simp only [Cy ,wA,powers]
 rw [Av E (fun a =>
   x a^i.val*(oK x a*(w a-P.eval (x a)))*x a^j.val)]
 apply pG rfl
 intro a ha
 rw [pow_add]
 ring
theorem cNh (x u v :ι→F) (γ:F) (l t:ℕ) :
    (QO x u v l t).map (nX γ) =
      pL (fun (i:Fin l) (j:Fin (t+1)) =>
        oX x (fun a=>u a+γ*v a) (i.val+j.val)) := by
  ext i j
  simpa only [Au,xu,qz ,QO,
    qm,oq,pC,qy ,oZ] using
      (v8 x u v 1 γ (i.val+j.val)).symm
theorem d3p (x u v :ι→F) (hx :cy x) (γ:F)
  (P:F[X]) (k l t:ℕ) (hP:P.degree<k) (hsize :k+l+t≤aU ι)
  (E :lJ ι) (hE :E.card≤t+1)
  (hout : ∀ i,i∉E→u i+γ*v i=P.eval (x i))
  (hin : ∀ i∈E,u i+γ*v i≠P.eval (x i)) :
  ((QO x u v l t).map (nX γ)).rank=min E.card l:= by
 classical
 let z :E→F:= fun i=>x i.val
 have hz :cy z :=hx.comp FR
 have hs :vh (powers z (t+1)).mulVecLin :=
  kL.c1A z hz t (by simpa only [vl] using hE)
 rw [cNh,eDQ x _ hx P k l (t+1) hP (by omega) E hout,
  kL.c6I _ _ hs]
 rw [G1 _ _ ?_,G5 ,
  eNx z hz,vl]
 rw [xI]
 exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
  pQ (kL.cwQ x hx _) (sub_ne_zero.mpr (hin i.val i.property)))
theorem eDP (x w:ι→F) (hx :cy x) (P:F[X])
   (k d:ℕ) (hP:P.degree<k) (hsize :k+d+d≤aU ι+1)
   (E :lJ ι) (hE :E.card=d)
   (hout : ∀ i,i∉E→w i=P.eval (x i))
   (hin : ∀ i∈E,w i≠P.eval (x i)) :
   (pL (fun (i j:Fin d)=>oX x w (i.val+j.val))).det≠0:= by
 classical
 let e :Fin d ≃ E :=(Fintype.equivFinOfCardEq (by simpa only [vl] using hE)).symm
 let z := fun i:Fin d=>x (e i).val
 let a := fun i:Fin d=>oK x (e i).val*(w (e i).val-P.eval (z i))
 let V:=Matrix.vandermonde z
 have hfactor : (pL (fun (i j:Fin d)=>oX x w (i.val+j.val))) =
     V.transpose*yU a*V:= by
   ext i j
   rw [Matrix.of_apply,cMD x w hx P k _ hP (by have :=i.isLt; have :=j.isLt; omega)
     E hout,Matrix.mul_apply]
   simp only [Cy ,wA,Matrix.vandermonde_apply,V]
   rw [← Av]
   symm
   apply Fintype.sum_equiv e
   intro b
   simp only [z,a,pow_add]
   ring
 have hV:V.det≠0:=Matrix.det_vandermonde_ne_zero_iff.mpr
   (hx.comp (Subtype.val_injective.comp e.injective))
 rw [hfactor,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,xI]
 exact pQ (pQ hV (Finset.prod_ne_zero_iff.mpr fun i _ =>
   pQ (kL.cwQ x hx _) (sub_ne_zero.mpr (hin _ (e i).property)))) hV
theorem dNc (x u v :ι→F) (hx :cy x) (γ:F)
   (P:F[X]) (k d:ℕ) (hP:P.degree<k) (hsize :k+d+d≤aU ι)
   (E :lJ ι) (hE :E.card=d)
   (hout : ∀ i,i∉E→u i+γ*v i=P.eval (x i))
   (hin : ∀ i∈E,u i+γ*v i≠P.eval (x i)) :
   let M:= QO x u v d d
   let A:=M.submatrix id zS
   let b:= fun i=>M i (Fin.last d)
   let c:=yL A b
   let q:= fun i => ∑ j:Option (Fin d),C (x i^(j.elim d Fin.val))*c j
   ∀ i,(q i).eval γ=A.det.eval γ*(mL x E).eval (x i)∧A.det.eval γ≠0:= by
 classical
 dsimp only
 let M:= QO x u v d d
 let A:=M.submatrix id zS
 let b:= fun i=>M i (Fin.last d)
 let D:=mL x E
 let f := fun (j:Option (Fin d))=>D.coeff (j.elim d Fin.val)
 let Aγ:=A.map (nX γ)
 let bγ:=nX γ ∘ b
 have hAγ:Aγ=pL (fun (i j:Fin d) =>
     oX x (fun a=>u a+γ*v a) (i.val+j.val)) := by
   ext i j
   exact ov (ov (cNh x u v γ d d) i) (zS j)
 have hdet:Aγ.det≠0:= by
   rw [hAγ]
   exact eDP x _ hx P k d hP (by omega) E hE hout hin
 have hpoint (i:ι) :D.eval (x i)*(u i+γ*v i)=D.eval (x i)*P.eval (x i) := by
   by_cases hi:i∈E
   · simp [D,arK x E i hi]
   · rw [hout i hi]
 have hd:D.natDegree=d:=(ZQ x E).trans hE
 have hker :=cUx x hx u v γ k d d hsize P D hP hd.le hpoint
 have hf :f none=1 := by
   change D.coeff d = 1
   rw [← hd]
   exact (S8 x E).coeff_natDegree
 have hborder : (apT.aTh Aγ bγ).mulVec f=0:= by
   funext i
   have hh:=ov hker i
   rw [p9,p5 ,GB] at hh
   simpa only [p9,p5 ,JK,apT.aTh,f,
     Option.elim_none,Option.elim_some,Aγ,A,bγ,b,xu,Matrix.submatrix_apply,
     Function.comp_apply,id_eq,qz ,Fin.val_castSucc,Fin.val_last,y5] using hh
 have hline :=apT.etS Aγ bγ hdet f hborder
 have hmapdet:Aγ.det=A.det.eval γ:=((nX γ).map_det A).symm
 have hcoeff (j:Option (Fin d)) :
     (yL A b j).eval γ=A.det.eval γ*f j:= by
   rw [← hmapdet]
   have he :=ov hline j
   rw [hf] at he
   change f j=(1/Aγ.det)*yL Aγ bγ j at he
   rw [apT.ezl] at he
   rw [he,← vk,one_div,Dv hdet,oZ]
   rfl
 intro i
 change (∑ j:Option (Fin d),C (x i^j.elim d Fin.val)*yL A b j).eval γ =
   A.det.eval γ*D.eval (x i)∧A.det.eval γ≠0
 refine ⟨?_,hmapdet ▸ hdet⟩
 simp only [qx ,oq,pC,hcoeff]
 rw [← bw8 D d hd.le,GB,JK,vH,
   wB,y5]
 congr 1
 · apply pG rfl
   intro j _
   simp only [f,Option.elim_some,Fin.val_castSucc]
   ring
 · simp only [f,Option.elim_none,Fin.val_last]
   ring
end
end bz4
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι K:Type} [lI F] [lI K] [c9 ι] [lz ι]
theorem eOz (φ:F[X] →+* K) (hφ:cy φ)
   (p:ℕ) (x u v :ι→F) (L t a q:ℕ) (haq:a+q=t)
   (B:sI φ (AI p x u v L t) a)
   (γ:F) (hγ: (u5 B).det.eval γ≠0) :
   nI F (n5
     ((AI p x u v L t).map (nX γ)).mulVecLin)=q+1 := by
 have hrank :=zQ.buH φ hφ (AI p x u v L t) a B γ hγ
 have hn:=t8
   ((AI p x u v L t).map (nX γ)).mulVecLin
 change ((AI p x u v L t).map (nX γ)).rank+_ = _ at hn
 rw [hrank,t3 ,sS] at hn
 omega
def cHM (φ:F[X] →+* K) (hφ:cy φ)
    (p:ℕ) (x u v :ι→F) (L t r :ℕ)
    (B:sI φ (AI p x u v L t) r)
    (W:th F (Fin (t+1)→F))
    (hWdim:nI F W=t+1-r)
    (hW : ∀ c∈W,(AI p x u v L t).mulVec (fun j=>C (c j))=0) :
    by1 p x u v L t (u5 B).det where
  space :=W
  generic_annihilates :=hW
  normal_inclusion := by
    intro γ hγ c hc
    have heval (β:F) (c' : Fin (t+1)→F) (hv :c' ∈ W) :
        ((AI p x u v L t).map (nX β)).mulVec c' = 0:= by
      have h:=oz (fun w=> fun i=>(w i).eval β) (hW c' hv)
      funext i
      have hi:=ov h i
      simpa [p9,p5 ,qx] using hi
    have heq :=zQ.dO8 φ hφ
      (AI p x u v L t) r B W (by simpa using hWdim) heval γ hγ
    rw [← heq]
    exact hc
def eD1 (φ:F[X] →+* K) (hφ:cy φ)
    (p:ℕ) (x u v :ι→F) (L t:ℕ) (H :lJ ι) (d q:ℕ)
    (hd:0<d) (hsize :H.card+d+q=t)
    (B:sI φ (AI p x u v L t) (H.card+d))
    (coeffs :Fin (d+1)→F[X])
    (hdeg : ∀ j,(coeffs j).natDegree≤p*d)
    (hprimitive : ∀ γ,sH coeffs γ≠0)
    (hfixed : ∀ i,i∉H→avE coeffs (x i)≠0)
    (hshift : ∀ γ (Q:ox F (q+1)),
      ((AI p x u v L t).map (nX γ)).mulVec
        (aOU (mL x H*sH coeffs γ) q t Q)=0) :
    bRV p x u v L t (u5 B).det where
  fixedRoots :=H
  movingDegree :=d
  quotientDegree :=q
  moving_pos :=hd
  boS:=hsize
  coefficients :=coeffs
  bnv :=hdeg
  primitive_specialization :=hprimitive
  no_additional_fixed_root :=hfixed
  normal_nullity :=eOz φ hφ p x u v L t (H.card+d) q hsize B
  multiples_annihilate :=hshift
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι:Type} [lI F] [lI K] [c9 ι] [lz ι]
theorem d5H (φ:F[X] →+* K) (hφ:cy φ)
    (p:ℕ) [oy F p] (hp:1≤p) (x u v :ι→F)
    (m d q:ℕ) (H :lJ ι) (hd:0<d) (hL:H.card+d+q< m)
    (P:atR (fun b j=>φ (P8 p x u v b j)) m (H.card+d) q)
    (f :K[X]) (hfd:f.natDegree≤d)
    (hfactor :P.generator=(mL x H).map (φ.comp (lV:F →+* F[X]))*f)
    (hnode : ∀ i,i∉H→f.eval (φ (C (x i)))≠0)
    (B:sI φ (AI p x u v (m-(H.card+d+q)) (H.card+d+q)) (H.card+d)) :
    Nonempty (bRV p x u v (m-(H.card+d+q)) (H.card+d+q)
      (u5 B).det) := by
  classical
  let a :=H.card+d
  let M:=AI p x u v (m-(a+q)) (a+q)
  let N :=AI p x u v (m-a) a
  let Hp:=(mL x H).map (lV:F →+* F[X])
  let Hk :=Hp.map φ
  let R:=az6 a d N Hp
  have hHp:Hp.natDegree≤H.card:=Polynomial.natDegree_map_le.trans (by rw [ZQ])
  have hHk :Hk.natDegree≤H.card:=Polynomial.natDegree_map_le.trans hHp
  have hHk0:Hk≠0:=((S8 x H).map (lV:F →+* F[X])).map φ |>.ne_zero
  have hfac:P.generator=Hk*f := by simpa only [Hk,Hp,Fa] using hfactor
  have hf0:f≠0:= by intro hf; apply P.nonzero; rw [hfac,hf,mul_zero]
  have hsmallLine :=P.gs0 hL
  rw [buO] at hsmallLine
  rw [hfac] at hsmallLine
  have hRmap :R.map φ=az6 a d (N.map φ) Hk :=
    fXe a d φ N Hp
  have hRline :n5 (R.map φ).mulVecLin =
      K ∙ (fun j:Fin (d+1)=>f.coeff j.val) := by
    rw [hRmap]
    exact fXf a H.card d rfl (N.map φ) Hk f hHk0 hHk hfd hsmallLine
  have hfv : (fun j:Fin (d+1)=>f.coeff j.val)≠0:= by
    intro hz
    apply hf0
    apply bcF d f 0 hfd (by simp)
    intro j
    simpa using ov hz j
  have hRnull:nI K (n5 (R.map φ).mulVecLin)=1 := by
    rw [hRline,finrank_span_singleton hfv]
  have hRrank : (R.map φ).rank=d:= by
    have hn:=t8 (R.map φ).mulVecLin
    change (R.map φ).rank+_= _ at hn
    rw [hRnull,t3 ,sS] at hn
    omega
  obtain ⟨Bsmall⟩:=zQ.a3O φ R d hRrank
  have hFE : (R.map φ).mulVec (fun j:Fin (d+1)=>f.coeff j.val)=0:= by
    change (fun j:Fin (d+1)=>f.coeff j.val)∈n5 (R.map φ).mulVecLin
    rw [hRline]
    exact Submodule.mem_span_singleton_self _
  have hRdeg : ∀ i j,(R i j).natDegree≤p:= by
    intro i j
    apply fXg a d N (mL x H) (fun _=>p) _ i j
    intro l k
    exact (a8L p x u v (m-a) a l k).trans (by split_ifs <;> omega)
  obtain ⟨coeffs,hprimitive,hRcoeff,hdegree,heval⟩:=d4C
    φ hφ R d Bsmall (fun _=>p) hRdeg _ hfv hFE
  have hdegree' : ∀ j,(coeffs j).natDegree≤p*d:= by
    intro j
    simpa [Nat.mul_comm] using hdegree j
  have hspec : ∀ γ,sH coeffs γ≠0:= by
    intro γ
    rw [bwQ]
    apply dtp
    intro hz
    obtain ⟨j,hj⟩:=heval γ
    exact hj (ov hz j)
  have hgeneric: (R.map φ).mulVec (fun j=>φ (coeffs j))=0:= by
    funext i
    have hi:=oz φ (ov hRcoeff i)
    simpa only [p9,p5 ,map_sum,pU,zf ,xu,zc] using hi
  have hmem: (fun j=>φ (coeffs j))∈n5 (R.map φ).mulVecLin:=hgeneric
  rw [hRline] at hmem
  obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp hmem
  have hgpoly :mD (fun j=>φ (coeffs j))=c•f := by
    apply bcF d
    · exact aCg _
    · exact (G3 _ _).trans hfd
    · intro j
      have hj:=ov hc j
      simpa only [ahe,Polynomial.coeff_smul,xL,vj] using hj.symm
  have hc0:c≠0:= by
    intro hz
    have hzero :mD (fun j=>φ (coeffs j))=0:= by simpa [hz] using hgpoly
    obtain ⟨j,hj⟩:=heval 0
    have hj0:=oz (fun Q:K[X]=>Q.coeff j.val) hzero
    have hcz :coeffs j=0:=hφ (by simpa only [ahe,coeff_zero,zf] using hj0)
    simp [hcz] at hj
  have hnofixed : ∀ i,i∉H→avE coeffs (x i)≠0:= by
    intro i hi hz
    have he :=eEZ φ coeffs (x i)
    rw [hz,zf ,hgpoly,C9,vj] at he
    exact (pQ hc0 (hnode i hi)) he.symm
  let G:=Hp*mD coeffs
  have hGdegree :G.natDegree≤a :=
    Polynomial.natDegree_mul_le.trans (by have :=aCg coeffs; omega)
  have hGker :N.mulVec (fun j:Fin (a+1)=>G.coeff j.val)=0:= by
    rw [← cfn a d N Hp coeffs]
    exact hRcoeff
  have hGmap (γ:F) :G.map (nX γ)=mL x H*sH coeffs γ:= by
    rw [Bf ,bUg]
    have hHpEval :Hp.map (nX γ)=mL x H := by
      ext j
      simp only [Hp,wR,qz ,pC]
    rw [hHpEval]
  have hshift : ∀ γ (Q:ox F (q+1)),
      (M.map (nX γ)).mulVec
        (aOU (mL x H*sH coeffs γ) q (a+q) Q)=0:= by
    intro γ Q
    have hh:=d6k p x u v m a q (by omega) G hGdegree hGker γ Q
    rw [hGmap] at hh
    exact hh
  refine ⟨?_⟩
  exact eD1 φ hφ p x u v (m-(a+q)) (a+q)
    H d q hd rfl B coeffs hdegree' hspec hnofixed hshift
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι:Type} [lI F] [lI K] [c9 ι] [lz ι]
theorem eOC (φ:F[X] →+* K) (p:ℕ) (x u v :ι→F)
  (m a q:ℕ)
  (P:atR (fun b j=>φ (P8 p x u v b j)) m a q) :
  Nonempty (sI φ (AI p x u v (m-(a+q)) (a+q)) a) := by
 let M:=AI p x u v (m-(a+q)) (a+q)
 have hnull:=P.dyW
 rw [buO] at hnull
 have hrank : (M.map φ).rank=a := by
  have hn:=t8 (M.map φ).mulVecLin
  change (M.map φ).rank+_= _ at hn
  rw [t3 ,sS] at hn
  change nI K (n5 (M.map φ).mulVecLin)=q+1 at hnull
  omega
 exact zQ.a3O φ M a hrank
theorem d5G (φ:F[X] →+* K) (hφ:cy φ)
    (p:ℕ) (x u v :ι→F) (m a q:ℕ) (H :lJ ι) (hHa :H.card=a)
    (P:atR (fun b j=>φ (P8 p x u v b j)) m a q)
    (c:K) (hc:c≠0)
    (hgen:P.generator=c•((mL x H).map (φ.comp (lV:F →+* F[X]))))
    (B:sI φ (AI p x u v (m-(a+q)) (a+q)) a) :
    Nonempty (by1 p x u v (m-(a+q)) (a+q)
      (u5 B).det) := by
  classical
  let M:=AI p x u v (m-(a+q)) (a+q)
  let ρ:=φ.comp (lV:F →+* F[X])
  let HK:=(mL x H).map ρ
  let W:=p7 (aOU (mL x H) q (a+q))
  have hHdeg: (mL x H).natDegree≤a := by rw [ZQ,hHa]
  have hinj:=b9A (mL x H) a q (a+q)
    (S8 x H).ne_zero hHdeg (by omega)
  have hWdim:nI F W=a+q+1-a := by
    have hh:=FV hinj
    change nI F W=nI F (ox F (q+1)) at hh
    rw [hh,(z8 F (q+1)).finrank_eq,t3 ,
      sS]
    omega
  have hW : ∀ w∈W,M.mulVec (fun j=>C (w j))=0:= by
    rintro _ ⟨Q,rfl⟩
    let QK:=(Q:F[X]).map ρ
    have hQK:QK.natDegree≤q:=Polynomial.natDegree_map_le.trans (ayC Q)
    have hproduct :P.generator*(c⁻¹•QK)=HK*QK:= by
      rw [hgen]
      change (c•HK)*(c⁻¹•QK)=HK*QK
      calc
        _=(c*c⁻¹)•(HK*QK) := by simp only [C5 ,pU]; ring
        _ = _:= by rw [Dv hc,one_smul]
    have hrec:akK
        (fun b j=>φ (P8 p x u v b j)) m (a+q) (HK*QK) := by
      apply (P.aOk _).mpr
      exact ⟨c⁻¹•QK,(G3 _ _).trans hQK,hproduct.symm⟩
    have hgeneric:=((aPN _ m (a+q) _).mp hrec).2
    rw [buO] at hgeneric
    let E :=(mL x H*(Q:F[X])).map (lV:F →+* F[X])
    have hEmap :E.map φ=HK*QK:= by simp only [E,HK,QK,Fa ,Bf ,ρ]
    have hgenericE : (M.map φ).mulVec
        (fun j:Fin (a+q+1)=>(E.map φ).coeff j.val)=0:= by rw [hEmap]; exact hgeneric
    have hpoly :=d6j φ hφ M E (fun j:Fin (a+q+1)=>j.val) hgenericE
    change M.mulVec (fun j:Fin (a+q+1)=>C ((mL x H*(Q:F[X])).coeff j.val))=0
    simpa only [E,wR] using hpoly
  exact ⟨cHM φ hφ p x u v (m-(a+q)) (a+q) a B W hWdim hW⟩
end
end gR.Principal
end
section
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι:Type} [lI F] [lI K] [c9 ι] [lz ι]
theorem efP (ρ:F →+* K) (x :ι→F)
   (hx :cy x) (g:K[X]) (hg:g≠0) (a :ℕ)
   (hga :g.natDegree≤a) :
   ∃ (H :lJ ι) (d:ℕ) (f :K[X]),H.card+d=a∧f.natDegree≤d ∧
     g=(mL x H).map ρ*f∧(∀ i,i∉H→f.eval (ρ (x i))≠0) := by
 classical
 let xK:= fun i=>ρ (x i)
 have hxK:cy xK:=ρ.injective.comp hx
 let H :=Finset.univ.filter (fun i=>g.eval (xK i)=0)
 have hle : (mL xK H).roots≤g.roots := by
   rw [bIF]
   apply (Hw (H.nodup.map hxK)).mpr
   intro z hz
   obtain ⟨i,hi,rfl⟩:=Multiset.mem_map.mp hz
   exact (t5 hg).mpr ((Finset.mem_filter.mp hi).2)
 have hdiv :mL xK H∣g:=(bIG xK H).dvd_of_roots_le_roots
   (S8 xK H).ne_zero hle
 obtain ⟨f,hf⟩:=hdiv
 have hf0:f≠0:= by intro hz; apply hg; rw [hf,hz,mul_zero]
 have hdegree :H.card+f.natDegree=g.natDegree := by
   rw [hf,uz (S8 xK H).ne_zero hf0,ZQ]
 have hHa :H.card≤a := by omega
 refine ⟨H,a-H.card,f,by omega,by omega,?_,?_⟩
 · rw [b8d]
   exact hf
 · intro i hi hzero
   have hgi:g.eval (xK i)≠0:= by
     simpa only [H,Finset.mem_filter,qU,true_and] using hi
   apply hgi
   rw [hf,oq]
   change (mL xK H).eval (xK i)*f.eval (ρ (x i))=0
   rw [hzero,mul_zero]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι:Type} [lI F] [lI K] [c9 ι] [lz ι]
theorem ef0 (φ:F[X] →+* K) (hφ:cy φ)
    (p:ℕ) [oy F p] (hp:1≤p) (x :ι→F) (hx :cy x)
    (hfixed : ∀ i,x i^p=x i) (u v :ι→F) (k m a q:ℕ)
    (hkm:k+m=aU ι) (hL:a+q< m)
    (P:atR (fun b j=>φ (P8 p x u v b j)) m a q)
    (B:sI φ (AI p x u v (m-(a+q)) (a+q)) a)
    (Γ:lJ F) (hΓ : ∀ γ∈Γ,akD x u v k (k+(m-(a+q))) γ) :
    Γ.card≤(∑ i,if (B.rows i).1=0 then 1 else p)+p*aU ι:= by
  classical
  obtain ⟨H,d,f,ha,hfd,hfactor,hnode⟩:=efP
    (φ.comp (lV:F →+* F[X])) x hx P.generator P.nonzero a P.aNb
  subst a
  by_cases hd:d=0
  · subst d
    simp only [Nat.add_zero] at *
    have hfC:f=C (f.coeff 0) :=II (by omega)
    have hc:f.coeff 0≠0:= by
      intro hz
      apply P.nonzero
      rw [hfactor,hfC,hz,C_0,mul_zero]
    have hgen:P.generator=f.coeff 0 •
        ((mL x H).map (φ.comp (lV:F →+* F[X]))) := by
      rw [hfactor,hfC,C5]
      simp only [coeff_C_zero]
      ring
    obtain ⟨cert⟩:=d5G φ hφ p x u v m H.card q H rfl P _ hc hgen B
    have hh:=cHT p x hx hfixed u v k (k+(m-(H.card+q)))
      (m-(H.card+q)) (H.card+q) _ (by omega) rfl (by omega)
      (u5 B).det B.minor_ne
      (zQ.aVV φ _ _ B _ (a8L p x u v _ _)) cert Γ hΓ
    exact hh.trans (Nat.le_add_right _ _)
  · have hdpos :0<d:= by omega
    obtain ⟨cert⟩:=d5H φ hφ p hp x u v m d q H hdpos hL
      P f hfd hfactor hnode B
    have hh:=eOs p x hx hfixed u v k (k+(m-(H.card+d+q)))
      (m-(H.card+d+q)) (H.card+d+q) _ (by omega) rfl (by omega)
      (u5  B).det B.minor_ne
      (zQ.aVV φ _ _ B _ (a8L p x u v _ _)) cert Γ hΓ
    exact hh.trans (JM  (Nat.mul_le_mul_left p (Nat.sub_le _ _)) _)
theorem efY (φ:F[X] →+* K) (hφ:cy φ)
  (p:ℕ) [oy F p] (hp:1≤p) (x :ι→F) (hx :cy x)
  (hfixed : ∀ i,x i^p=x i) (u v :ι→F) (k m a q:ℕ)
  (hkm:k+m=aU ι) (hL:a+q< m)
  (P:atR (fun b j=>φ (P8 p x u v b j)) m a q)
  (Γ:lJ F) (hΓ : ∀ γ∈Γ,akD x u v k (k+(m-(a+q))) γ) :
  ∃ B:sI φ (AI p x u v (m-(a+q)) (a+q)) a,
    Γ.card≤(∑ i,if (B.rows i).1=0 then 1 else p)+p*aU ι:= by
 obtain ⟨B⟩:=eOC φ p x u v m a q P
 exact ⟨B,ef0 φ hφ p hp x hx hfixed u v k m a q hkm hL P B Γ hΓ⟩
theorem efZ (φ:F[X] →+* K) (hφ:cy φ)
  (p:ℕ) [oy F p] (hp:1≤p) (x :ι→F) (hx :cy x)
  (hfixed : ∀ i,x i^p=x i) (u v :ι→F) (k m a q:ℕ)
  (hkm:k+m=aU ι) (hL:a+q< m)
  (P:atR (fun b j=>φ (P8 p x u v b j)) m a q)
  (Γ:lJ F) (hΓ : ∀ γ∈Γ,akD x u v k (k+(m-(a+q))) γ) :
  Γ.card≤p*(aU ι+a) := by
 obtain ⟨B,hcount⟩:=efY φ hφ p hp x hx hfixed u v k m a q hkm hL P Γ hΓ
 have hdegree : (∑ i,if (B.rows i).1=0 then 1 else p)≤p*a := by
  calc
    _ ≤ ∑ _i:Fin a,p:=Finset.sum_le_sum (fun i _=> by split_ifs <;> omega)
    _ = _:= by simp [Nat.mul_comm]
 calc
  _≤p*a+p*aU ι:=hcount.trans (Nat.add_le_add_right hdegree _)
  _ = _:= by ring
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
theorem cEP (p:ℕ) [oy F p] (x u v :ι→F) (k H :ℕ)
    (Crt:axT p x u v k H) (γ:F) :
    let U:=(mD (fun j=>Crt.coefficients (0,j))).map (nX γ)
    let V:=(mD (fun j=>Crt.coefficients (1,j))).map (nX γ)
    let R:=Crt.output.map (nX γ)
    (U≠0∨V≠0)∧a1f (qG F p) x (fun i=>u i+γ*v i) k H U V R:= by
  let φ:=nX γ
  have hne :=cBn H (fun b=>(Crt.coefficients b).eval γ)
    (M4.bFs _ Crt.primitive γ)
  have hu (b:Fin 2) : (mD (fun j=>Crt.coefficients (b,j))).map φ=
      mD (fun j=>(Crt.coefficients (b,j)).eval γ) := by
    rw [Principal.bUg,Et]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [Principal.bUg,Et] using hne
  · exact Polynomial.natDegree_map_le.trans (Crt.x_degree 0)
  · exact Polynomial.natDegree_map_le.trans (Crt.x_degree 1)
  · exact Polynomial.degree_map_le.trans_lt Crt.output_degree
  · intro i
    have hA (P:p6 (p6 F)) : (P.map φ).eval (x i)=φ (P.eval (lV (x i))) := by
      simpa only [φ,qz ,pC] using
        (Dz (nX γ) (lV (x i)) (p:=P))
    have hh:=oz φ (Crt.nodes i)
    simp only [vi ,pU,qz ,pC,qy ,t7] at hh
    rw [← hA,← hA,← hA] at hh
    have hp: (u i+γ*v i)^p=u i^p+γ^p*v i^p:= by
      have hp:=vi (qG F p) (u i) (γ*v i)
      rw [pU] at hp
      exact hp
    simpa only [φ,qz ,pC,qy ,t7,frobenius_def,← hp] using hh
theorem dHv (p:ℕ) [oy F p]
  (x u v :ι→F) (hx :cy x) (hfixed : ∀ i,x i^p=x i)
  (k H :ℕ) (Crt:axT p x u v k H) (γ:F)
  (S:lJ ι) (hS:k+H≤S.card) (P:F[X]) (hP:P.degree<k)
  (hagree : ∀ i∈S,P.eval (x i)=u i+γ*v i) (i:ι) :
  ((mD (fun j=>Crt.coefficients (0,j))).map (nX γ)).eval (x i)*
    (u i+γ*v i-P.eval (x i))+
  ((mD (fun j=>Crt.coefficients (1,j))).map (nX γ)).eval (x i)*
    (u i+γ*v i-P.eval (x i))^p=0:= by
 have hrel :=(cEP p x u v k H Crt γ).2
 exact eem p x _ hx hfixed k H _ _ _ hrel S hS P hP hagree i
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
theorem guf (x :ι→F) (hx :cy x)
   (E :lJ ι) (g:F[X]) (hg:g≠0) (hdiv :g∣mL x E) :
   ∃ B:lJ ι,B⊆E∧B.card=g.natDegree ∧ ∃ c:F,c≠0∧g=c•mL x B:= by
 classical
 let B:=Finset.univ.filter (fun i=>g.eval (x i)=0)
 have hE0:=(S8 x E).ne_zero
 have hsplits :=(Principal.bIG x E).of_dvd hE0 hdiv
 have hle :=Polynomial.roots.le_of_dvd hE0 hdiv
 rw [Principal.bIF] at hle
 have hnodup:g.roots.Nodup:=Multiset.nodup_of_le hle (E.nodup.map hx)
 have hBE :B⊆E := by
   intro i hi
   have hgx :g.eval (x i)=0:=(Finset.mem_filter.mp hi).2
   obtain ⟨Q,hQ⟩:=hdiv
   apply (Principal.aVH x hx E i).mp
   rw [hQ,oq,hgx,zero_mul]
 have himage :B.image x=g.roots.toFinset := by
   ext a
   simp only [Finset.mem_image,Multiset.mem_toFinset]
   constructor
   · rintro ⟨i,hi,rfl⟩
     exact (t5 hg).mpr (Finset.mem_filter.mp hi).2
   · intro ha
     have hEa :=Multiset.mem_of_le hle ha
     obtain ⟨i,hiE,hia⟩:=Multiset.mem_map.mp hEa
     refine ⟨i,Finset.mem_filter.mpr ⟨qU _,?_⟩,hia⟩
     rw [hia]
     exact (t5 hg).mp ha
 have hBcard:B.card=g.natDegree := by
   calc
     B.card=(B.image x).card:=(Ea B hx).symm
     _=g.roots.toFinset.card:=oz Finset.card himage
     _=g.roots.card:=Multiset.toFinset_card_of_nodup hnodup
     _=g.natDegree :=hsplits.natDegree_eq_card_roots.symm
 have hBg:mL x B∣g:=bsf x hx B g (fun i hi=>(Finset.mem_filter.mp hi).2)
 obtain ⟨Q,hQ⟩:=hBg
 have hQ0:Q≠0:= by intro hz; exact hg (by rw [hQ,hz,mul_zero])
 have hQd:Q.natDegree=0:= by
   have hh:=uz (S8 x B).ne_zero hQ0
   rw [← hQ,ZQ,hBcard] at hh
   omega
 have hQC:=II hQd
 have hc:Q.coeff 0≠0:= by intro hz; exact hQ0 (hQC.trans (by rw [hz,Polynomial.C_0]))
 refine ⟨B,hBE,hBcard,Q.coeff 0,hc,?_⟩
 calc
   g=mL x B*Q:=hQ
   _=mL x B*C (Q.coeff 0) :=oz (fun R:F[X]=>mL x B*R) hQC
   _= Q.coeff 0•mL x B:= by rw [C5]; ring
end
end gR.kL
end
section
namespace yP.FM
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
abbrev K:=zm
abbrev I:=vw
abbrev bAd:=Fin 2→ I→Fin Dw→K
local instance :lz K:=t9 K
theorem a5W:aU K=(2130706433:ℕ)^6:= by
 rw [Iw]
 rfl
theorem c1k :IRSProfile.code =
  ((yo uJ 131072)^⋈(Fin Dw)) := by
 unfold IRSProfile.code ReedSolomon.Interleaved.irsCode
 rfl
end
end yP.FM
end
section
namespace yP.C42
noncomputable section
open ProximityPrize.Benchmark
open scoped NNReal
theorem cFE (s :ℕ) :
  (claimedError s)^100=1/(2 :ℝ≥0)^s := by
 unfold claimedError
 rw [← NNReal.rpow_mul_natCast]
 have hex : -((s :ℝ)/ 100)*((100:ℕ) :ℝ) = -(s :ℝ) := by norm_num
 rw [hex,NNReal.rpow_neg,NNReal.rpow_natCast]
 simp only [one_div]
end
end yP.C42
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
namespace gR.Native
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark
open scoped BigOperators
abbrev K:=zm
abbrev I:=vw
abbrev p:ℕ:=2130706433
local instance gPH (P:Prop) :xm P:=zi P
instance gRe :CharP K p :=
 charP_of_injective_algebraMap
  (R:=FQ) (A:=K) (vG FQ K).injective p
theorem ahU (i:I) :uJ i^p=uJ i:= by
 change (EK Aa
  (IRSProfile.baseNttDomain.node i))^p =
  EK Aa (IRSProfile.baseNttDomain.node i)
 rw [← map_pow]
 exact oz (EK Aa)
  (ZMod.pow_card (IRSProfile.baseNttDomain.node i))
end
end gR.Native
end
section
namespace amZ
universe u
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open yP.C42
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
theorem ef8 {R E κ:Type*} [CommSemiring R] [CommSemiring E] [c9 κ]
  {d:ℕ} (psi:R →+* E) (cols :κ→SourceColumn d) (v :κ→R)
  (u:JetVariable d →₀ ℕ)
  (hu:u∈(MvPolynomial.map psi (SourceColumn.interpolant cols v)).support) :
  ∃ j:κ,u=(cols j).exponent:= by
 classical
 have hs :=MvPolynomial.support_map_subset psi (SourceColumn.interpolant cols v) hu
 obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
 exact ⟨j,by simpa [SourceColumn.interpolant] using MvPolynomial.support_monomial_subset hj⟩
end
end amZ
end
section
namespace yP.aLT.Native
set_option maxRecDepth 10000
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
abbrev tu:=FQ
abbrev K:=zm
abbrev Index :=vw
local instance :lz tu:=t9 tu
local instance :lz K:=t9 K
def phi:tu →+* K:=vG tu K
def nodes :Index ↪ tu where
  toFun i:=IRSProfile.baseNttDomain.node i
  inj' := by
    intro i j h
    apply IRSProfile.domain.injective
    change z9 (IRSProfile.baseNttDomain.node i) =
     z9 (IRSProfile.baseNttDomain.node j)
    exact oz z9 h
def D:lJ tu:=aul nodes
def radius :ℝ:=338557/ 1048576
def cap:ℕ:=7*262144^3
theorem dXs :D.card = 262144 := by
 rw [D,dyE]
 norm_num [Index,vw]
theorem cRV:aU K=2130706433^6:= by
 change aU KoalaBear.Ext6=2130706433^6
 rw [Iw]
 rfl
theorem threshold : (aU Index :ℝ)*(1 - radius)≤(177505:ℝ) := by
 norm_num [Index,vw ,radius]
theorem cfw:D.card+131072*(cap+1)^2<aU K:= by
 rw [dXs,cRV]
 exact eEr
def bpS (w:Index→tu) :tu→tu :=
 Function.extend nodes w (fun _ ↦ 0)
@[simp] theorem gPU (w:Index→tu) (i:Index) :
   bpS w (nodes i)=w i:=nodes.injective.extend_apply _ _ _
end
end yP.aLT.Native
end
section
namespace yP.baR
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
open yP.aLT yP.a92
abbrev K:=zm
abbrev I:=vw
abbrev aP2 :ModuleCode I K K:=yo uJ 131072
local instance :lz K:=t9 K
def d5w (w:I→K) :K→K :=
 Function.extend uJ w (fun _ ↦ 0)
@[simp] theorem gPT (w:I→K) (i:I) :
   d5w w (uJ i)=w i :=
  IRSProfile.domain.injective.extend_apply _ _ _
end
end yP.baR
end
section
namespace yP.baR
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
open yP.a92
abbrev YP:=Fin 2→Fin Dw→K
abbrev R16:=Fin 2×Fin 8
def awE :ModuleCode I K YP:=IRSProfile.code ^⋈ (Fin 2)
local instance :lz K:=t9 K
local instance :lz YP:=t9 YP
def flatten (f :I→YP) :I→R16→K:= fun i r ↦ f i r.1 r.2
theorem b3y :cy flatten:= by
 intro f g h
 funext i j r
 exact ov (ov h i) (j,r)
theorem b3x (f w:I→YP) :
  aaC f w≤aaC (flatten f) (flatten w) := by
 apply cA4 f w (flatten f) (flatten w)
 intro i he
 funext r
 exact ov (ov he r.1) r.2
theorem b3D (f :I→YP) (hf :f∈awE) :
  ∀ r :R16,(fun i ↦ flatten f i r)∈aP2 := by
 change ∀ j:Fin 2,∀ r :Fin 8,(fun i ↦ f i j r)∈aP2 at hf
 intro r
 exact hf r.1 r.2
end
end yP.baR
end
