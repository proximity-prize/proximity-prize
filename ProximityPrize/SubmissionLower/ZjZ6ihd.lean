import ProximityPrize.SubmissionLower.Z0SRqJa
import ProximityPrize.SubmissionLower.ZGa2w7a
import ProximityPrize.SubmissionLower.EA
import ProximityPrize.SubmissionLower.ZjNfeqc
import ProximityPrize.SubmissionLower.ZXiQNLd
import ProximityPrize.SubmissionLower.ZJ86yqc
import ProximityPrize.SubmissionLower.C3
import ProximityPrize.SubmissionLower.ZQmiAIb
set_option Elab.async false
open _root_ renaming IsFractionRing.injective → zxb, LinearMap.congr_fun → z5U, LinearMap.range → zWl, Matrix.diagonal_mul → zKY, Matrix.map_apply → zAg, Matrix.map_mul → zwg, Matrix.toLin'_mul → z4J, Matrix.toLin'_toMatrix' → zJt, MvPolynomial.C → znf, MvPolynomial.map_C → zpw, Nat.pos_of_ne_zero → zOl, Polynomial.C_injective → zmy, Polynomial.X → z7y
section
section
set_option backward.isDefEq.respectTransparency false
namespace qcsMxUc
noncomputable section
open Polynomial Matrix
open cu (Shape)
open aeL (Offset a2N Pa)
private theorem rank_eval_le {F I J:Type} [Field F] [Fintype I] [Fintype J]
    (M:Matrix I J F[X]) (a :F) : (M.map (evalRingHom a)).rank≤M.rank := by
  classical
  let B:=M.map (evalRingHom a)
  let f :=B.mulVecLin
  let e :zWl f ≃ₗ[F] (Fin B.rank→F) :=
    (Module.finBasis F (zWl f)).equivFun
  obtain ⟨right,hr⟩:=f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨left,hl⟩:=(zWl f).subtype.exists_leftInverse_of_injective
    (zWl f).ker_subtype
  let U:=(e.toLinearMap.comp left).toMatrix'
  let V:=(right.comp e.symm.toLinearMap).toMatrix'
  have hB:U*B*V=1 := by
    apply (Matrix.toLin' (R:=F)).injective
    rw [Matrix.toLin'_one,z4J,z4J]
    simp only [U,V,zJt]
    apply LinearMap.ext
    intro v
    change e (left (f (right (e.symm v))))=v
    have hright:=z5U hr (e.symm v)
    have hleft:=z5U hl (e.symm v)
    change f.rangeRestrict (right (e.symm v))=e.symm v at hright
    change left (f.range.subtype (e.symm v))=e.symm v at hleft
    change e (left (f.range.subtype (f.rangeRestrict (right (e.symm v)))))=v
    rw [hright,hleft,e.apply_symm_apply]
  let S:=U.map (C (R:=F))*M*V.map (C (R:=F))
  have hS:S.map (evalRingHom a)=1 := by
    rw [zwg,zwg]
    have hC {R C' : Type} (W:Matrix R C' F) :
        (W.map (C (R:=F))).map (evalRingHom a)=W:= by
      ext i j
      exact eval_C
    rw [hC,hC]
    exact hB
  have hd:S.det≠0:= by
    intro hz
    have he :=(evalRingHom a).map_det S
    change evalRingHom a S.det=(S.map (evalRingHom a)).det at he
    rw [hS,hz,map_zero,Matrix.det_one] at he
    exact zero_ne_one he
  calc
    B.rank=S.rank := by rw [rank_of_det_ne_zero hd,Fintype.card_fin]
    _≤M.rank :=(rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
private theorem rank_constants_le {F I J:Type} [Field F] [Fintype J]
  (M:Matrix I J F) : (M.map (C (R:=F))).rank≤M.rank := by
 classical
 let f :=M.mulVecLin
 let e :zWl f ≃ₗ[F] (Fin M.rank→F) :=
  (Module.finBasis F (zWl f)).equivFun
 let L:=(f.range.subtype.comp e.symm.toLinearMap).toMatrix'
 let R:=(e.toLinearMap.comp f.rangeRestrict).toMatrix'
 have hM:M=L*R:= by
  apply (Matrix.toLin' (R:=F)).injective
  rw [z4J]
  simp only [L,R,zJt]
  apply LinearMap.ext
  intro v
  change f v=f.range.subtype (e.symm (e (f.rangeRestrict v)))
  rw [e.symm_apply_apply]
  rfl
 have h:M.map (C (R:=F))=L.map (C (R:=F))*R.map (C (R:=F)) := by
  rw [← zwg,← hM]
 rw [h]
 exact (rank_mul_le_left _ _).trans (by simpa using rank_le_card_width (L.map (C (R:=F))))
theorem scale_le {F:Type} [Field F] (s :Shape) (t:Offset s) (u:ℕ) (a :F) :
    (plainMatrix s t u a).rank≤(plainMatrix s t u (1 :F)).rank := by
  classical
  let M:=plainMatrix s t u (z7y (R:=F))
  let N :=(plainMatrix s t u (1 :F)).map (C (R:=F))
  let D:=diagonal (fun r :qQCEOid.VP s t u=>z7y (R:=F)^r.1.1.val)
  let E :=diagonal (fun v :qQCEOid.SeedCol s t u=>z7y (R:=F)^v.1.1.val)
  have hm:plainMatrix s t u a=M.map (evalRingHom a) := by
    ext r v
    have hx :evalRingHom a (z7y (R:=F))=a :=eval_X
    simp only [M,zAg,plainMatrix,Pa,apply_ite,map_zero,
      map_mul,map_natCast,map_pow,hx]
    split_ifs <;> rfl
  have hd:D.det≠0:= by
    simp [D,det_diagonal,Finset.prod_ne_zero_iff,X_ne_zero]
  have h:D *M=N*E := by
    ext r v
    simp only [D,E,zKY,Matrix.mul_diagonal]
    by_cases hgrade :r.1.1.val+r.2.val=v.1.1.val+v.2.val
    · by_cases hp:r.1.1.val≤v.1.1.val∧a2N v.1≤ r.1.1.val
      · simp only [M,N,zAg,plainMatrix,Pa,ite_eq_left hgrade,
          ite_eq_left hp,one_pow,mul_one,map_mul,map_natCast]
        rw [← mul_assoc,mul_comm ((z7y (R:=F))^r.1.1.val),mul_assoc,← pow_add,
          Nat.add_sub_of_le hp.1]
      · simp only [M,N,plainMatrix,Pa,ite_eq_left hgrade,ite_eq_right hp,
          zAg,map_zero,mul_zero,zero_mul]
    · simp [M,N,plainMatrix,hgrade]
  rw [hm]
  calc
    (M.map (evalRingHom a)).rank≤M.rank :=rank_eval_le M a
    _=(D *M).rank :=(rank_mul_eq_right_of_det_ne_zero D M hd).symm
    _≤N.rank := by rw [h]; exact rank_mul_le_left _ _
    _≤_:=rank_constants_le _
end
end qcsMxUc
end
section
set_option backward.isDefEq.respectTransparency false
namespace qcsMxUc
noncomputable section
open Matrix
open cu (Shape)
open aeL (Offset Pivot Pa)
open qQCEOid (SeedCol VP WindowCol windowMatrix)
private theorem cwY {F:Type} [Field F] (s :Shape) (t:Offset s) (u:ℕ) :
    (plainMatrix s t u (1 :F)).rank ≤ ∑ k∈Finset.range (s.B+u+1),
      (windowMatrix F s t u k).rank := by
  classical
  let I:=Fin (s.B+u+1)
  let blocks (k :I) :=windowMatrix F s t u k.val
  let W:=blockDiagonal' blocks
  let rg (r :VP s t u) :=r.1.1.val+r.2.val
  let cg (v :SeedCol s t u) :=v.1.1.val+v.2.val
  have hc (v :SeedCol s t u) :cg v<s.B+u+1 := by
    have h₁:=v.1.1.isLt
    have h₂:=v.2.isLt
    dsimp [cg]
    omega
  let rows (r :VP s t u) :Σ _:I,Pivot s t :=
    ⟨if h:rg r<s.B+u+1 then ⟨rg r,h⟩ else 0,r.1⟩
  let cols (v :SeedCol s t u) :Σ k :I,WindowCol s t u k.val :=
    ⟨⟨cg v,hc v⟩,⟨v.1,by
      have h:=v.2.isLt
      dsimp [cg]
      omega⟩⟩
  let mask (r :VP s t u) :F:=if rg r<s.B+u+1 then 1 else 0
  have hW (l k :I) (r :Pivot s t) (v :WindowCol s t u k.val) :
      W ⟨l,r⟩ ⟨k, v⟩=if l=k then Pa s t (1 :F) r v.val else 0:= by
    by_cases h:l=k
    · subst l
      exact (blockDiagonal'_apply_eq blocks k r v).trans
        (ite_eq_left (show k=k from rfl)).symm
    · simpa only [ite_eq_right h] using blockDiagonal'_apply_ne blocks r v h
  have he :plainMatrix s t u (1 :F)=diagonal mask*W.submatrix rows cols := by
    ext r v
    rw [zKY]
    by_cases hr :rg r<s.B+u+1
    · have hh: (rows r).1=(cols v).1↔rg r=cg v := by
        refine Fin.ext_iff.trans ?_
        have hv : (rows r).1.val=rg r := by
          dsimp only [rows]
          rw [dite_eq_left hr]
        rw [hv] <;> rfl
      change (if rg r=cg v then Pa s t (1 :F) r.1 v.1 else 0) =
        mask r*W ⟨(rows r).1,r.1⟩ ⟨(cols v).1,(cols v).2⟩
      rw [hW]
      simp only [hh,mask,ite_eq_left hr,one_mul] <;> rfl
    · have hn:rg r≠cg v := by have :=hc v; omega
      change (if rg r=cg v then _ else 0)=mask r*_
      simp only [ite_eq_right hn,mask,ite_eq_right hr,zero_mul]
  rw [he]
  refine (rank_mul_le_right _ _).trans ((rank_submatrix_le W rows cols).trans ?_)
  rw [← Fin.sum_univ_eq_sum_range (fun k=>(windowMatrix F s t u k).rank)]
  exact a9M.fS3 blocks
theorem proof :qQCEOid.c1 := by
 intro F _ s t u a b c hb
 exact (projective s t u a b c hb).trans ((scale_le s t u a).trans (cwY s t u))
end
end qcsMxUc
end
end
section
section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace qh06gse
noncomputable section
open Polynomial
open P5 (K p)
open cu (L FX aZ qD)
open qaySLPd (pe)
open ak0 (aTH)
open private alV baseChange from ProximityPrize.SubmissionLower.G
open private coeffDx_mul from ProximityPrize.SubmissionLower.ZjNfeqc
open private bXz bXA aYE from ProximityPrize.SubmissionLower.DB
open private cXQ from ProximityPrize.SubmissionLower.EA
open private b0u from ProximityPrize.SubmissionLower.A3
private theorem lift_injective :Function.Injective lift :=
 (MvPolynomial.map_injective _ (zxb L[X] FX)).comp alV.injective
theorem b7D (A:pe[X]) :
   aTH (lift A)=lift A.derivative := by
 induction A using Polynomial.induction_on with
 | C q=>simp [bIr,bXA]
 | add a b ha hb=>simp only [map_add,ha,hb]
 | monomial n q ih =>
   rw [pow_succ,← mul_assoc]
   generalize C q*(z7y:pe[X])^n=R at ih ⊢
   simp only [map_mul,coeffDx_mul,derivative_mul,map_add,ih,cXC,
     bXz,aYE,derivative_X,map_one,mul_one]
   ac_rfl
attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem clearPair (a b:aZ) :
   ∃ A B:pe[X],∃ u:FX,u≠0 ∧
     a*znf u=lift A∧b*znf u=lift B:= by
 let M:Submonoid (MvPolynomial (Fin 2) L[X]) :=
   (nonZeroDivisors L[X]).map znf
 obtain ⟨A,B,⟨_,s,hs,rfl⟩,ha,hb⟩:=IsLocalization.surj₂ M aZ a b
 refine ⟨alV.symm A,alV.symm B,algebraMap L[X] FX s,?_,?_,?_⟩
 · exact (map_ne_zero_iff _ (zxb L[X] FX)).mpr
     (mem_nonZeroDivisors_iff_ne_zero.mp hs)
 · change a*baseChange (znf s)=baseChange A at ha
   change a*_=baseChange (alV (alV.symm A))
   rw [RingEquiv.apply_symm_apply]
   simpa only [baseChange,zpw] using ha
 · change b*baseChange (znf s)=baseChange B at hb
   change b*_=baseChange (alV (alV.symm B))
   rw [RingEquiv.apply_symm_apply]
   simpa only [baseChange,zpw] using hb
private theorem pullDerivative {z :K} {A:pe[X]} {b:aZ}
   (hb:qD z b≠0) (hd:lift A∣b*aTH (lift A)) :
   ∃ B:pe[X],qD z (lift B)≠0∧A∣B*A.derivative := by
 obtain ⟨c,hc⟩:=hd
 obtain ⟨B,C',u,hu,hB,hC⟩:=clearPair b c
 refine ⟨B,?_,C',lift_injective ?_⟩
 · rw [← hB,map_mul,show qD z (znf u)=u from MvPolynomial.eval_C _]
   exact mul_ne_zero hb hu
 · rw [map_mul,map_mul,← b7D,← hB,← hC]
   rw [mul_right_comm,hc,mul_assoc]
private theorem markedFactor {A:pe[X]} (hA:A≠0)
  (ev :pe[X] →+* FX) (h:ev A=0) :
  ∃ Q:pe[X],Prime Q∧Q∣A∧ev Q=0:= by
 obtain ⟨fs,hfs,u,hu⟩:=UniqueFactorizationMonoid.exists_prime_factors A hA
 have hz : (fs.map ev).prod=0:= by
  have ht:=congrArg ev hu
  rw [map_mul,map_multiset_prod,h] at ht
  exact (mul_eq_zero.mp ht).resolve_right (u.isUnit.map ev).ne_zero
 obtain ⟨Q,hQ,hzQ⟩:=Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
 refine ⟨Q,hfs Q hQ,?_,hzQ⟩
 rw [← hu]
 exact dvd_mul_of_dvd_left (Multiset.dvd_prod hQ) _
private theorem constFactor {A B Q:pe[X]} (hA:A≠0)
   (hdeg:A.natDegree<p) (hQ:Prime Q) (hq:Q∣A) (hb : ¬ Q∣B)
   (hd:A∣B*A.derivative) :Q.natDegree=0:= by
 by_contra hn
 let:CharP pe p :=
   charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 2) L) p
 let:CharP pe[X] p :=
   charP_of_injective_ringHom (f :=Polynomial.C) zmy p
 have hfin:=FiniteMultiplicity.of_prime_left hQ hA
 let n:=multiplicity Q A
 have hnpos :0<n:=multiplicity_pos_of_dvd hq hfin
 have hnlt:n<p:= by
   have h:=natDegree_le_of_dvd (pow_multiplicity_dvd Q A) hA
   rw [natDegree_pow,Nat.mul_comm] at h
   exact (Nat.le_mul_of_pos_left _ (zOl hn)).trans_lt (h.trans_lt hdeg)
 obtain ⟨R,hR,hr⟩:=hfin.exists_eq_pow_mul_and_not_dvd
 change A= Q^n*R at hR
 have hpow:Q^n∣B*A.derivative :=(pow_multiplicity_dvd Q A).trans hd
 obtain ⟨m,hm⟩:=Nat.exists_eq_succ_of_ne_zero hnpos.ne'
 rw [hm] at hR hpow hnlt
 have hc : ¬ Q∣(↑(m+1) :pe[X]) := by
   intro hc
   have hne : (↑(m+1) :pe[X])≠0:= by
     rw [Ne,CharP.cast_eq_zero_iff]
     exact fun h=>(not_le_of_gt hnlt) (Nat.le_of_dvd (Nat.succ_pos m) h)
   have hn0: (↑(m+1) :pe[X]).natDegree=0:= by
     rw [← map_natCast (C:pe →+* pe[X]),natDegree_C]
   exact hn (Nat.eq_zero_of_le_zero ((natDegree_le_of_dvd hc hne).trans hn0.le))
 have heta :Q^(m+1)∣Q^m *
     (B*(Q*R.derivative+(↑(m+1) :pe[X])*(Q.derivative*R))) := by
   convert hpow using 1
   rw [hR,derivative_mul,derivative_pow_succ,pow_succ Q m]
   simp only [Nat.cast_add,Nat.cast_one,map_add,map_natCast,map_one]
   ring
 rw [pow_succ,mul_dvd_mul_iff_left (pow_ne_zero _ hQ.ne_zero)] at heta
 have hs :Q∣B*((↑(m+1) :pe[X])*(Q.derivative*R)) := by
   rw [mul_add] at heta
   exact (dvd_add_right (dvd_mul_of_dvd_right (dvd_mul_right Q _) B)).mp heta
 have hder :=(hQ.dvd_mul.mp ((hQ.dvd_mul.mp
   ((hQ.dvd_mul.mp hs).resolve_left hb)).resolve_left hc)).resolve_right hr
 exact b0u Q (zOl hn)
   ((natDegree_le_of_dvd hq hA).trans_lt hdeg) hder
theorem descend {E :aZ} {A:pe[X]} {u:FX} {z :K}
   (hE :E≠0) (hu:u≠0) (hA:lift A=znf u*E)
   (hdeg:A.natDegree<p) (hz :qD z E=0)
   {b:aZ} (hb:qD z b≠0) (hd:E∣b*aTH E) :
   ∃ q:pe,Irreducible q∧uk.wZ q∣E ∧
     uk.zU z q=0:= by
 let ev :=(qD z).comp lift
 have hA0:A≠0:= fun h=>mul_ne_zero (MvPolynomial.C_ne_zero.mpr hu) hE
   (by rw [← hA,h,map_zero])
 have hs :IsUnit (znf u:aZ) :=
   (isUnit_iff_ne_zero.mpr hu).map znf
 have he :lift A∣b*aTH (lift A) := by
   rw [hA,hs.mul_left_dvd,coeffDx_mul,mul_add]
   exact dvd_add (by simpa only [mul_left_comm b] using dvd_mul_of_dvd_right hd (MvPolynomial.C u))
     (dvd_mul_of_dvd_right (dvd_mul_right E (aTH (MvPolynomial.C u))) b)
 obtain ⟨B,hB,hder⟩:=pullDerivative hb he
 obtain ⟨Q,hQ,hq,hzQ⟩:=markedFactor hA0 ev (by
   change qD z (lift A)=0
   rw [hA,map_mul,hz,mul_zero])
 have hn:Q.natDegree=0:=constFactor hA0 hdeg hQ hq (by
   intro h
   exact hB (zero_dvd_iff.mp (hzQ ▸ map_dvd ev h))) hder
 rw [eq_C_of_natDegree_eq_zero hn] at hQ hq hzQ
 refine ⟨Q.coeff 0,?_,?_,?_⟩
 · exact Irreducible.of_map (f :=(Polynomial.C:pe →+* pe[X])) hQ.irreducible
 · have h:=map_dvd lift hq
   rwa [bIr,hA,hs.dvd_mul_left] at h
 · change qD z (lift (C (Q.coeff 0)))=0 at hzQ
   rw [bIr,show qD z (uk.wZ (Q.coeff 0)) =
     uk.gA (uk.zU z (Q.coeff 0)) from
     RingHom.congr_fun (cXQ z) _] at hzQ
   exact ((zxb L[X] FX).comp zmy)
     (hzQ.trans (map_zero uk.gA).symm)
end
end qh06gse
end
section
set_option autoImplicit true
namespace qckEfrc
noncomputable section
open P5 (K)
open P5_7_1 (degree)
open cu (L FX kr)
open MvPolynomial Finset

open aZa (D6)


open scoped Polynomial
abbrev Var :=Option (Fin 2)
abbrev af :=MvPolynomial Var FX
abbrev Box (b j u:ℕ) :=restrictCappedBidegree (Fin 2) FX 1 u b j
abbrev power :=2*degree-3
abbrev seed (u:ℕ) :=power*u
def point (z :L) (S:K[X]) :Var→FX
 | none=>algebraMap L FX z
 | some i => ![kr S,kr S.derivative] i
abbrev Regular (g:af) (z :L) (S:K[X]) :Prop :=
 eval (point z S) g=0∧eval (point z S) (pderiv (some 1) g)≠0
local notation "ord" => (some (0:Fin 2))
local notation "vel" => (some (1 :Fin 2))
local notation "sep" => MvPolynomial.pderiv (R:=FX) vel
def drift (f :af) :af :=D6 f+MvPolynomial.X vel*pderiv ord f
def zD (f q:af) :af :=sep f*drift q - drift f*sep q
def BA (f :af) :ℕ→af
 | 0 => -drift f
 | i+1=>sep f*zD f (BA f i) -
     C ((2*i+1 :ℕ) :FX)*zD f (sep f)*BA f i
end
end qckEfrc
end
section
namespace qckEfrc
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P5 (K I node)
open P5_7 (midAgreement)
open P5_7_1 (degree)


structure OF (w:I→K) (T:Finset K) (s :K→K[X]) :Prop where
 distinct :Set.InjOn s (T:Set K)
 degree : ∀ γ∈T,(s γ).natDegree≤degree
 lg : ∀ γ∈T,∃ B:Finset I,midAgreement≤B.card ∧ ∀ i∈B,(s γ).eval (node i)=w i
theorem OF.mono {w T s} (h:OF w T s) {U:Finset K} (hU:U⊆T) :
   OF w U s :=
 ⟨h.distinct.mono hU,fun _ hγ=>h.degree _ (hU hγ),fun _ hγ=>h.lg _ (hU hγ)⟩
end
end qckEfrc
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace qs0zuzc
open P5_7_2 (Aux fO Ls introduction jX stages)

open jQ (cUo eE)
set_option quotPrecheck false in
local notation "blocks!" =>
 (by
   repeat' apply And.intro
   all_goals first | exact True.intro | decide +kernel)
local notation "m!" tail:arg vs:arg =>
 ai7.bsJ (last :=tail) vs blocks! rfl rfl
private theorem r1 :eE 101 22=3108650 :=
 m! 123 [3108650]
private theorem r2 :eE 107 23=3859829 :=
 m! 130 [3859829]
private theorem r3:eE 115 25=5166252 :=
 m! 140 [5166252]
private theorem r4 :eE 143 31=12155092 :=
 m! 174 [12155092]
private theorem r5:eE 143 32=12449254 :=
 m! 175 [12449254]
private theorem r6:eE 159 35=18685854 :=
 m! 194 [18685854]
private theorem r7:eE 190 41=37214873 :=
 m! 231 [37214873]
private theorem r8:eE 210 46=55941530 :=
 m! 256 [55941530]
private theorem r9:eE 218 48=65128192 :=
 m! 10 [65101450,26742]
private theorem dz :eE 277 61=0xa0a0024 :=
 m! 82 [0x959b20d,11554327]
private theorem dD:eE 287 63=0xb876020 :=
 m! 94 [0xa7bdb7f,17532065]
private theorem dK:eE 316 69=0x10d4900b :=
 m! 129 [0xe11e1e5,46312998]
private theorem e8:eE 354 81=0x1b65ef9f :=
 m! 179 [0x13ded71c,0x7871883]
private theorem gD:eE 675 140=0x14bfd4f36 :=
 m! 47 [0x4a9e49af,0xb97de180,0x47826457,6209456]
private theorem gx :eE 704 146=0x18896ec96 :=
 m! 82 [0x502b4afc,0xd3af9b80,0x62cef39d,32313981]
private theorem iu:eE 871 181=0x3972addf6 :=
 m! 28 [0x6ff71241,0x17edc8280,0x153daee65,0x546062da,1832950]
private theorem kD:eE 895 186=0x400867e35 :=
 m! 57 [0x746e7a4d,0x199dd4300,0x1802eabe5,0x712efd03,14489600]
private theorem lH :eE 1392 289=0x1751e30276 :=
 m! 145 [0xca79f040,0x417466258,0x65b705d80,0x65c015d80,0x4347cce0c,0x16f84543c,0x14afd296]
private theorem kR:eE 1701 354=0x3409882399 :=
 m! 7 [0xfe94d740,0x5b8929a7d,0xa4b8bb000,0xc25cdb000,0xb3a0fb000,0x7b0d0462b,0x36515557d,0x9110ba80,84916]
private theorem jV:eE 2159 449=0x86d5e284e8 :=
 m! 48 [0x14bcfc540,0x7fd9d9f50,0x10cede8580,0x16a09d8580,0x18ee5c8580,0x17b81b8580,0x13019fb1e4,0xbf4592364,0x562dc53bc,0x11c6283c0,21585300]
private theorem lp:eE 2788 580=0x176b3c10caf :=
 m! 40 [0x1b5e06c40,0xae344ac40,0x19eab0ba73,0x278f405400,0x30b0de5400,0x35487c5400,0x35561a5400,0x30d9b85400,0x27db1444f5,0x1bf0116bc0,0x10597a2f5b,0x6f84d3d80,0x15994fd80,16480940]
private def StageGood (lo hi:ℕ) (ss :List Ls) :Prop :=
 ∀ s∈ss,Good lo hi ⟨s.dI,s.free⟩ false∧Good lo hi ⟨s.dI,s.moving⟩ true
private def AuxGood (lo hi:ℕ) (ss :List Aux) :Prop :=
 ∀ a∈ss,Good lo hi a false
private theorem stage_cons {lo hi:ℕ} {s :Ls} {ss :List Ls}
  (hf :Good lo hi ⟨s.dI,s.free⟩ false)
  (hm:Good lo hi ⟨s.dI,s.moving⟩ true)
  (ht:StageGood lo hi ss) :StageGood lo hi (s :: ss) :=
 List.forall_mem_cons.mpr ⟨⟨hf,hm⟩,ht⟩
private theorem aux_cons {lo hi:ℕ} {a :Aux} {ss :List Aux}
  (ha :Good lo hi a false) (ht:AuxGood lo hi ss) :AuxGood lo hi (a :: ss) :=
 List.forall_mem_cons.mpr ⟨ha,ht⟩
private theorem stage_nil (lo hi:ℕ) :StageGood lo hi [] := by simp [StageGood]
private theorem aux_nil (lo hi:ℕ) :AuxGood lo hi [] := by simp [AuxGood]
local notation "g!" m:arg=>checked (le_trans (cUo _ _) (le_of_eq m)) rfl
local notation "s!" mf:arg mm:arg rest=>stage_cons (g! mf) (g! mm) rest
local notation "a!" m:arg rest=>aux_cons (g! m) rest
private abbrev b12 :fO:=⟨12,by decide⟩
private abbrev b13:fO:=⟨13,by decide⟩
private theorem s12 :StageGood (jX b12).lo (jX b12).hi (stages b12) :=
 s! r3 gD
 s! r3 gx
 s! r2 kD
 s! r5 iu
 s! r4 lH
 s! r7 kR
 s! dz jV
 s! dK lp
 stage_nil _ _
private theorem Zn:AuxGood (jX b12).lo (jX b12).hi (introduction b12) :=
 a! r3
 a! r6
 a! r5
 a! r4
 a! r7
 a! r8
 a! dz
 a! r9
 a! dz
 a! dD
 a! e8
 a! dK
 aux_nil _ _
private theorem s13:StageGood (jX b13).lo (jX b13).hi (stages b13) :=
 s! r1 gD
 s! r3 gx
 s! r2 kD
 s! r5 iu
 s! r4 lH
 s! r7 kR
 s! dz jV
 s! dK lp
 stage_nil _ _
private theorem Th:AuxGood (jX b13).lo (jX b13).hi (introduction b13) :=
 a! r3
 a! r5
 a! r6
 a! r4
 a! r8
 a! r7
 a! r9
 a! dz
 a! dz
 a! dD
 a! e8
 a! dK
 aux_nil _ _
theorem proof :qMNIwTb.c3:= by
 intro b h hl hu hb move a ha
 have htop:b.val<14 :=b.isLt
 have hx :b=b12∨b=b13:= by
   rcases (show b.val=12∨b.val=13 by omega) with e | e
   · exact Or.inl (Fin.ext e)
   · exact Or.inr (Fin.ext e)
 obtain ⟨hs,hi⟩:StageGood (jX b).lo (jX b).hi (stages b) ∧
     AuxGood (jX b).lo (jX b).hi (introduction b) := by
   rcases hx with e | e <;> subst b
   · exact ⟨s12,Zn⟩
   · exact ⟨s13,Th⟩
 rcases ha with ⟨rfl,ha⟩ | ⟨s,hm,rfl⟩
 · exact hi a ha h hl hu
 · cases move
   · exact (hs s hm).1 h hl hu
   · exact (hs s hm).2 h hl hu
end qs0zuzc
end
end
