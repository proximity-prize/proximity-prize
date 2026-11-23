import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.B1
import ProximityPrize.SubmissionLower.B2
import ProximityPrize.SubmissionLower.AC
set_option Elab.async false
open _root_ renaming AddMonoidAlgebra→GY,AddMonoidAlgebra.coeff_mul_single_add→VO,AddMonoidAlgebra.coeff_single→zE,AddMonoidAlgebra.coeff_zero→Qx,AddMonoidAlgebra.single→qx,AddMonoidAlgebra.singleAddHom_apply→Kv,AddMonoidAlgebra.single_mul_single→Gj,AlgEquiv.ofBijective→PD,AlgHom.comp_apply→Kp,Algebra.algebraMap→mD,CommRing→ oY,CommSemiring→xm,DFunLike.congr_fun→RP,Decidable→z7,Field→ oq,Fin.forall_fin_two→UZ,Fin.sum_univ_four→zg,Finset→qm,Finset.card_le_card→Np,Finset.mem_univ→ In,Finset.range→pz,Finset.range_mono→LO,Finset.single_le_sum→Dw,Finset.sum_add_distrib→JQ,Finset.sum_congr→yL,Finset.sum_insert→Nq,Finset.sum_le_sum→Df,Finset.sum_mul→Kz,Finset.sum_range_succ'→Mk,Finset.sum_subset→P7,Finset.sup_le→u5,Finsupp.add_apply→PA,Finsupp.degree_eq_sum→G1,Finsupp.single_apply→Ef,Finsupp.single_eq_same→Oc,Function.Injective→pQ,Function.Surjective→zh,Function.comp_apply→FV,Ideal→aU,Ideal.Quotient.eq_zero_iff_mem→MS,Ideal.Quotient.factor_surjective→Te,Ideal.Quotient.factorₐ→Gk,Ideal.Quotient.mk→ ox,Ideal.Quotient.mk_surjective→Lf,Ideal.Quotient.mkₐ→t6,Ideal.comap_comap→J4,Ideal.comap_map_of_bijective→N0,Ideal.comap_map_of_surjective→Ar
open _root_ renaming Ideal.exists_minimalPrimes_le→ Iw,Ideal.height_le_ringKrullDim_of_isPrime→S1,Ideal.map_comap_of_equiv→Pv,Ideal.map_map→vj,Ideal.map_span→KH,Ideal.mem_map_of_mem→Gr,Ideal.mul_mono_left→SL,Ideal.quotientMap_injective'→Ob,Ideal.quotientMap_surjective→QL,Ideal.quotientMapₐ→Fz,Ideal.ringKrullDim_quotient_succ_le_of_lt→Rm,Ideal.span→nX,Ideal.span_singleton_le_iff_mem→Fa,Ideal.span_singleton_prime→TI,Ideal.subset_span→vw,Ideal.sup_mul→GF,Int.ofNat_sub→G5,Irreducible→ oZ,IsDomain→zm,IsFractionRing.injective→vi,IsLocalization.isPrime_of_isPrime_disjoint→R9,IsLocalization.map_algebraMap_ne_top_iff_disjoint→NI,IsLocalization.under_map_of_isPrime_disjoint→SW,IsNoetherianRing→Au,IsUnit→wB,LinearMap.ker→vl,LinearMap.mulLeft→Vl,Matrix.cons_val_zero→Vz,Module.Finite→pC,Module.Finite.of_surjective→G4,Module.finrank→lV,Multiset→x7,Multiset.prod_cons→Un,MvPolynomial→c9,MvPolynomial.C→nq,MvPolynomial.X→lI,MvPolynomial.aeval→t3,MvPolynomial.aeval_C→VH,MvPolynomial.aeval_X→PM,MvPolynomial.affineHilbertPolynomial→Ok,MvPolynomial.algHom_ext→wR,MvPolynomial.algebraMap_def→Ml,MvPolynomial.algebraMap_eq→vZ,MvPolynomial.commAlgEquiv→Aa,MvPolynomial.degreeOf_X→yB,MvPolynomial.degreeOf_le_totalDegree→C4,MvPolynomial.degreeOf_mul_le→JM,MvPolynomial.degreeOf_sub_le→SU
open _root_ renaming MvPolynomial.eval→zc,MvPolynomial.eval₂Hom→qz,MvPolynomial.eval₂Hom_X'→zk,MvPolynomial.exists_mem_quotientDegreeLE→KI,MvPolynomial.finSuccEquiv→z9,MvPolynomial.le_totalDegree→sS,MvPolynomial.map→ oz,MvPolynomial.mem_restrictTotalDegree→Sv,MvPolynomial.mem_support_iff→S2,MvPolynomial.monomial→qG,MvPolynomial.monomialMap→uW,MvPolynomial.optionEquivLeft→EK,MvPolynomial.rename→yo,MvPolynomial.renameEquiv→vH,MvPolynomial.renameEquiv_apply→Mz,MvPolynomial.restrictSupport→C5,MvPolynomial.restrictSupport_eq_span→ Il,MvPolynomial.restrictTotalDegree→FQ,MvPolynomial.ringHom_ext→t4,MvPolynomial.sumAlgEquiv→FU,MvPolynomial.support_map_subset→NW,MvPolynomial.totalDegree→SC,MvPolynomial.totalDegree_mul→Kh,MvPolynomial.totalDegree_mul_of_isDomain→UY,MvPolynomial.totalDegree_zero→RC,MvPolynomial.uniqueAlgEquiv→Et,MvPolynomial.uniqueFactorizationMonoid→Kc,MvPolynomial.weightedTotalDegree_one→xW,MvPolynomial.weightedTotalDegree_piSingle→xL,Nat.add_assoc→uJ,Nat.add_comm→JW,Nat.add_le_add→GB,Nat.add_le_add_left→zS,Nat.add_mul→yJ,Nat.add_sub_of_le→LP,Nat.cast_add→qy,Nat.cast_mul→zR,Nat.cast_ofNat→yU,Nat.cast_one→vk,Nat.cast_zero→uz,Nat.descFactorial_succ→G2,Nat.div_lt_iff_lt_mul→Nr,Nat.eq_zero_of_le_zero→Qw,Nat.eq_zero_of_not_pos→NZ,Nat.factorial_dvd_descFactorial→Hw,Nat.factorial_succ→TZ,Nat.le_add_right→t9,Nat.le_div_iff_mul_le→FR
open _root_ renaming Nat.le_mul_of_pos_right→Ea,Nat.le_succ→t5,Nat.lt_succ_of_le→NX,Nat.mul_add→Mw,Nat.mul_comm→xI,Nat.mul_div_cancel'→F9,Nat.mul_le_mul_left→p6,Nat.mul_le_mul_right→sH,Nat.zero_le→vG,Order.height→HZ,Polynomial.C→qJ,Polynomial.C_dvd_iff_dvd_coeff→G3,Polynomial.X→pU,Polynomial.coe_eval₂RingHom→Gi,Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le→G7,Polynomial.coeff_natDegree→u8,Polynomial.commRing→SM,Polynomial.eq_C_of_natDegree_eq_zero→EP,Polynomial.eval_C→G0,Polynomial.eval_X→NY,Polynomial.eval_add→TH,Polynomial.eval_comp→Pc,Polynomial.eval_mul→Qy,Polynomial.ext→Dv,Polynomial.le_natDegree_of_ne_zero→ II,Polynomial.mapRingHom→Kl,Polynomial.map_mul→Pj,Polynomial.map_zero→Re,Polynomial.natDegree_C_mul_X_pow_le→OJ,Polynomial.natDegree_X_add_C→VC,Polynomial.natDegree_add_le→JK,Polynomial.natDegree_le_of_dvd→Ee,Polynomial.natDegree_mul→Bf,Polynomial.ringHom_ext→z8,PrimeSpectrum→xu,RingHom.comp_apply→C9,RingHom.congr_fun→v8,RingHom.ext→MK,RingHom.id→MO,RingHom.injective_iff_ker_eq_bot→RJ,RingHom.ker→p7,RingHom.ker_eq_comap_bot→Pr,RingHom.ker_isPrime→Dz,RingHom.mem_ker→Mj,Set.image_singleton→UP,Set.mem_insert_iff→Pk,Set.mem_singleton_iff→LR,Set.range→FK
open _root_ renaming Submodule→Eg,Submodule.equivMapOfInjective→yQ,Submodule.finrank_mono→Vs,Submodule.map_comp→Nj,Submodule.map_mono→Vq,Submodule.mem_map_of_mem→RD,Submodule.sum_mem→Sd,Subtype.ext→KA,Subtype.val_injective→Up,Sum.elim→yl,Sum.inl→wA,Sum.inr→qU,UniqueFactorizationMonoid→u9,aR.Shape→cy,aR.Shape.plus→ oK,aR.Shape.scale→pG,aR.symbols→Av,add_le_add→ IT,congrArg→ oD,congrFun→Du,cu.Equation→nI,cu.Shape→p5,dN.GeoField→ ov,dN.GeoJets→lz,gT.Ambient→lJ,inferInstance→y5,isUnit_of_dvd_unit→Pf,le_antisymm→qM,le_max_left→uh,le_max_right→sI,le_rfl→p9,le_sup_left→Cy,left_ne_zero_of_mul→Gn,map_add→wY,map_dvd_iff→G8,map_mul→pL,map_ne_zero_iff→t7,map_pow→zf,map_sub→LQ,map_sum→zd,map_zero→th,max_le→t8,min_le_right→G9,mul_assoc→vh,mul_comm→ oj,mul_ne_zero→GR,mul_one→zi,nonZeroDivisors→ze
open _root_ renaming one_add_one_eq_two→Ts,qQ.Slice→n5,right_ne_zero_of_mul→G6,ringKrullDim→ oy,ringKrullDim_eq_zero_of_field→ IU,wellFounded_dvdNotUnit→SD,zero_add→v9
set_option autoImplicit true
section
namespace FI
open aR
open scoped BigOperators
def oL:Shape :=⟨0,0,0⟩
def gG:ℕ:=26124168665121
def Valid (a :cy) :Prop :=1≤a.t∧3*a.t≤a.j∧a.j≤3*a.b
def bTv (a :cy) :Prop :=
 a.b≤19∧a.j≤6 ∧
 (4≤a.j→a.b≤17)∧(5≤a.j→a.b≤13)∧(6≤a.j→a.b≤6)
instance (a :cy) :z7 (Valid a) := by unfold Valid; infer_instance
instance (a :cy) :z7 (bTv a) := by unfold bTv; infer_instance
instance (a :cy) :z7 (acX a) := by unfold acX; infer_instance
def coefficients (r s :ℕ) :ℕ×ℕ×ℕ×ℕ×ℕ :=
 match r,s with
 | 0,0=>(1,22,57,36,0)
 | 0,1=>(2,29,63,36,0)
 | 0,2=>(4,37,69,36,0)
 | 0,3=>(7,46,75,36,0)
 | 0,4=>(11,56,81,36,0)
 | 0,_=>(16,67,87,36,0)
 | 1,0=>(1,63,314,468,216)
 | 1,1=>(3,92,377,504,216)
 | 1,2=>(7,129,446,540,216)
 | 1,3=>(14,175,521,576,216)
 | 1,4=>(25,231,602,612,216)
 | 1,_=>(41,298,689,648,216)
 | 2,0=>(1,38,172,243,108)
 | 2,1=>(2,54,205,261,108)
 | 2,2=>(5,75,241,279,108)
 | 2,3=>(9,100,280,297,108)
 | 2,4=>(16,131,322,315,108)
 | 2,_=>(25,167,367,333,108)
 | _,0=>(1,30,125,168,72)
 | _,1=>(2,42,148,180,72)
 | _,2=>(4,57,173,192,72)
 | _,3=>(8,76,200,204,72)
 | _,4=>(13,98,229,216,72)
 | _,_=>(20,124,260,228,72)
def Lw (r j:ℕ) :ℕ :=
 let q:=j/6
 let (a,b,c,d,e) :=coefficients r (j % 6)
 let p₂:=q*(q - 1)
 let p₃:=p₂*(q - 2)
 a+b*q+c*(p₂/2)+d*(p₃/6)+e*(p₃*(q-3)/24)
def ic (r j v :ℕ) :ℕ:=if v≤j then Lw r (j - v) else 0
def aL5 (b r j v :ℕ) :ℕ :=
 ic r j v - ic r j (v+r*(b+1))
def a3U (b j:ℕ) :ℕ :=
  (b+1)*Lw 0 j+aL5 b 2 j 3+aL5 b 2 j 4+aL5 b 2 j 5 -
    (aL5 b 1 j 1+aL5 b 1 j 2+aL5 b 1 j 3+aL5 b 3 j 6)
end FI
end
section
namespace FI
open aR
open scoped BigOperators
theorem gw6 {k m:ℕ} {f g:ℕ→ℕ} (hkm:k≤ m)
   (hfg : ∀ i<k,f i≤g i) :
   (∑ i∈pz k,f i) ≤ ∑ i∈pz m,g i :=
 (Df fun i hi=>hfg i (Finset.mem_range.mp hi)).trans
   (Finset.sum_le_sum_of_subset (LO hkm))
theorem gw7 {f :ℕ→ℕ} {k m:ℕ}
  (hz : ∀ i,m≤ i→f i=0) (h:m≤k) :
  (∑ i∈pz k,f i) = ∑ i∈pz m,f i:= by
 symm
 apply P7 (LO h)
 intro i _ hi
 exact hz i (by simpa using hi)
theorem aQD {f :ℕ→ℕ} (k m:ℕ)
   (hz : ∀ i,m≤ i→f i=0) :
   (∑ i∈pz k,f i) = ∑ i∈pz (min k m),f i:= by
 by_cases h:m≤k
 · rw [min_eq_right h]
   exact gw7 hz h
 · rw [min_eq_left (by omega :k≤ m)]
section
set_option maxRecDepth 8192
set_option maxHeartbeats 0
end
theorem aqT (a :ℕ) {l u:ℕ} (hl:0<l) (h:l≤u) :
  ceilDiv a u≤ ceilDiv a l:= by
 have hu:0< u:=hl.trans_le h
 have hceil (d q:ℕ) (hd:0<d) :ceilDiv a d≤q↔a≤q*d:= by
  rw [ceilDiv,← Nat.lt_succ_iff,Nr hd,Nat.succ_mul]
  omega
 exact (hceil u _ hu).mpr <|
  ((hceil l _ hl).mp p9).trans (p6 _ h)
end FI
end
section
namespace yi
open aR
def bF (p:cy) :Prop :=p.j≤p.b∧3*p.t≤p.j
private def Q9 (p q r s :cy) :ℤ :=
 gI (gI (gI (gI Dn p) q) r) s ⟨0,0,0⟩
private theorem bwo (p a q r s :cy) :
  Q9 (p.plus a) q r s= Q9 p q r s+Q9 a q r s := by
 simp only [Q9,gI,Dn,oK,qy ,uz]
 ring
private theorem a8w (p q r s :cy) :
  Q9 p q r s= Q9 q r s p:= by
 simp only [Q9,gI,Dn,oK,qy ,uz]
 ring
private theorem a2j (p:cy) (h:bF p) :
  (p.b:ℤ)=(↑(p.b - p.j) :ℤ) + ↑(p.j-3*p.t)+3*p.t ∧
  (p.j:ℤ)=(↑(p.j-3*p.t) :ℤ)+3*p.t:= by
 obtain ⟨hb,hj⟩:=h
 constructor <;> exact_mod_cast (by omega :_)
private theorem bwp (d q r s :cy) (hq:bF q) (hr :bF r)
  (hs :bF s) :0≤Q9 d q r s := by
 obtain ⟨hqb,hqj⟩:=a2j q hq
 obtain ⟨hrb,hrj⟩:=a2j r hr
 obtain ⟨hsb,hsj⟩:=a2j s hs
 simp only [Q9,gI,Dn,oK,qy ,uz]
 rw [hqb,hqj,hrb,hrj,hsb,hsj]
 ring_nf
 positivity
private theorem bJj {p p' : cy} (h:aO p p') {q r s :cy}
  (hq:bF q) (hr :bF r) (hs :bF s) :
  iH p q r s≤ iH p' q r s := by
 let d:Shape :=⟨p'.b - p.b,p'.j - p.j,p'.t - p.t⟩
 have hp:p.plus d=p' := by
  obtain ⟨pb,pj,pt⟩:=p
  obtain ⟨qb,qj,qt⟩:=p'
  obtain ⟨hb,hj,ht⟩:=h
  simp [oK,d,LP hb,LP hj,LP ht]
 change (Q9 p q r s).toNat≤(Q9 p' q r s).toNat
 apply Int.toNat_le_toNat
 rw [← hp,bwo]
 exact le_add_of_nonneg_right (bwp d q r s hq hr hs)
private theorem bJk (p q r s :cy) :
 iH p q r s=iH q r s p:=oD Int.toNat (a8w p q r s)
theorem tD {p q r s p' q' r' s' : cy}
  (hp:aO p p') (hq:aO q q') (hr :aO r r') (hs :aO s s')
  (hp' : bF p') (hq' : bF q') (hr' : bF r')
  (hqs :bF q) (hrs :bF r) (hss :bF s) :
  iH p q r s≤ iH p' q' r' s' := by
 calc
  iH p q r s≤ iH p' q r s :=bJj hp hqs hrs hss
  _=iH q r s p' := bJk _ _ _ _
  _≤ iH q' r s p' := bJj hq hrs hss hp'
  _=iH r s p' q' := bJk _ _ _ _
  _≤ iH r' s p' q' := bJj hr hss hp' hq'
  _=iH s p' q' r' := bJk _ _ _ _
  _≤ iH s' p' q' r' := bJj hs hp' hq' hr'
  _=iH p' q' r' s' := bJk _ _ _ _
end yi
end
section
namespace aY8
open FI
def row (r :ℕ) (j:ℤ) :ℤ :=
 if 0≤j then Lw r j.toNat else 0
theorem bgV (r :ℕ) {j:ℤ} (h:j<0) :row r j=0:= by
 simp [row,not_le.mpr h]
theorem fZt (r :ℕ) (j:ℤ) :0≤ row r j:= by
 unfold row
 split <;> omega
theorem bLJ (r j:ℕ) :row r j=Lw r j:= by simp [row]
def gI (w:ℤ) (f :ℤ→ℤ) (j:ℤ) :ℤ:=f j - f (j - w)
def step (j:ℤ) :ℤ:=if 0≤j then 1 else 0
private def polynomial (r s :ℕ) (q:ℤ) :ℤ :=
 let (a,b,c,d,e) :=coefficients r s
 24*a+24*b*q+12*c*q*(q - 1) +
  4*d*q*(q - 1)*(q - 2)+e*q*(q - 1)*(q - 2)*(q-3)
private theorem gmn (r q s :ℕ) (hq:3≤q) (hs :s<6) :
   24*(Lw r (6*q+s) :ℤ)=polynomial r s q:= by
 have hdiv : (6*q+s)/6=q:= by omega
 have hmod: (6*q+s) % 6=s := by omega
 unfold Lw polynomial
 rw [hdiv,hmod]
 generalize coefficients r s=t
 rcases t with ⟨a,b,c,d,e⟩
 have hd₂:2∣q*(q - 1) := by
   simpa [G2 ,oj] using Hw q 2
 have hd₃:6∣q*(q - 1)*(q - 2) := by
   simpa [G2 ,TZ,oj,mul_left_comm,vh] using
     Hw q 3
 have hd₄:24∣q*(q - 1)*(q - 2)*(q-3) := by
   simpa [G2 ,TZ,oj,mul_left_comm,vh] using
     Hw q 4
 have h₂:=oD (fun n:ℕ=>(n:ℤ)) (F9 hd₂)
 have h₃:=oD (fun n:ℕ=>(n:ℤ)) (F9 hd₃)
 have h₄:=oD (fun n:ℕ=>(n:ℤ)) (F9 hd₄)
 simp only [Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,Int.ofNat_sub (show 1≤q by omega),
   G5  (show 2≤q by omega),G5  hq] at h₂ h₃ h₄
 simp only [qy ,zR]
 linear_combination 12*(c:ℤ)*h₂+4*(d:ℤ)*h₃+(e :ℤ)*h₄
private theorem aAe (r q i v :ℕ) (hq:3≤q) (hv :v≤ i) :
   24*row r (6*(q:ℤ)+i - v)=polynomial r ((i - v) % 6)
     ((q:ℤ)+((i - v)/6:ℕ)) := by
 have h:6*(q:ℤ)+i - v =
     ((6*(q+(i - v)/6)+(i - v) % 6:ℕ) :ℤ) := by omega
 rw [h,bLJ,gmn r _ _ (by omega) (by omega),qy]
theorem cIg (j:ℤ) :
   gI 1 (gI 2 (gI 3 (row 0))) j=step j:= by
 by_cases hn:j<0
 · simp [gI,step,not_le.mpr hn,bgV _ hn,bgV,show j-3<0 by omega,
     show j - 2<0 by omega,show j - 2 - 3<0 by omega,
     show j - 1<0 by omega,show j - 1 - 3<0 by omega,
     show j - 1 - 2<0 by omega,show j - 1 - 2 - 3<0 by omega]
 by_cases hs :j<24
 · interval_cases j <;> decide
 let q:=j.toNat/6 - 1
 let s :=j.toNat % 6
 have hq:3≤q:= by dsimp [q]; omega
 have hsr :s<6:= by dsimp [s]; omega
 have hj:j=6*(q:ℤ)+((6+s :ℕ) :ℤ) := by dsimp [q,s]; omega
 have hstep:step j=1 := by simp [step,show 0≤j by omega]
 have h:=aAe 0 q (6+s) 0 hq (by omega)
 have h₁:=aAe 0 q (6+s) 1 hq (by omega)
 have h₂:=aAe 0 q (6+s) 2 hq (by omega)
 have h₄:=aAe 0 q (6+s) 4 hq (by omega)
 have h₅:=aAe 0 q (6+s) 5 hq (by omega)
 have h₆:=aAe 0 q (6+s) 6 hq (by omega)
 have hp:polynomial 0 ((6+s - 0) % 6) ((q:ℤ)+((6+s - 0)/6:ℕ)) -
     polynomial 0 ((6+s - 1) % 6) ((q:ℤ)+((6+s - 1)/6:ℕ)) -
     polynomial 0 ((6+s - 2) % 6) ((q:ℤ)+((6+s - 2)/6:ℕ)) +
     polynomial 0 ((6+s-4) % 6) ((q:ℤ)+((6+s-4)/6:ℕ)) +
     polynomial 0 ((6+s - 5) % 6) ((q:ℤ)+((6+s - 5)/6:ℕ)) -
     polynomial 0 ((6+s-6) % 6) ((q:ℤ)+((6+s-6)/6:ℕ))=24 := by
   clear_value q s
   interval_cases s <;> norm_num [polynomial,coefficients] <;> ring
 rw [← h,← h₁,← h₂,← h₄,← h₅,← h₆] at hp
 simp only [uz ,vk,yU,sub_zero,← hj] at hp
 simp only [gI,hstep]
 rw [show j - 2 - 3=j - 5 by omega,show j - 1 - 3=j-4 by omega,
   show j - 1 - 2=j-3 by omega,show j-3-3=j-6 by omega]
 omega
theorem cNZ (r :ℕ) (hr :1≤ r) (hr' : r≤3) (j:ℤ) :
   gI r (row r) j=row 0 j:= by
 by_cases hn:j<0
 · simp [gI,bgV _ hn,bgV _ (show j - r<0 by omega)]
 by_cases hs :j<24
 · interval_cases r <;> interval_cases j <;> decide
 let q:=j.toNat/6 - 1
 let s :=j.toNat % 6
 have hq:3≤q:= by dsimp [q]; omega
 have hsr :s<6:= by dsimp [s]; omega
 have hj:j=6*(q:ℤ)+((6+s :ℕ) :ℤ) := by dsimp [q,s]; omega
 have h₁:=aAe r q (6+s) 0 hq (by omega)
 have h₂:=aAe r q (6+s) r hq (by omega)
 have h₃:=aAe 0 q (6+s) 0 hq (by omega)
 have hp:polynomial r ((6+s - 0) % 6) ((q:ℤ)+((6+s - 0)/6:ℕ)) -
     polynomial r ((6+s - r) % 6) ((q:ℤ)+((6+s - r)/6:ℕ)) =
     polynomial 0 ((6+s - 0) % 6) ((q:ℤ)+((6+s - 0)/6:ℕ)) := by
   clear_value q s
   interval_cases r <;> interval_cases s <;> norm_num [polynomial,coefficients] <;> ring
 rw [← h₁,← h₂,← h₃] at hp
 simp only [uz ,sub_zero,← hj] at hp
 unfold gI
 omega
end aY8
end
section
namespace aY8
open scoped BigOperators
private def count (base :ℕ→ℤ→ℤ) :ℕ→ℕ→ℤ→ℤ
 | 0,b,j=>base b j
 | k+1,b,j =>
     ∑ i∈pz (b+1),count base k (b - i) (j-((k :ℤ)+1)*i)
private def bdv (_:ℕ) (j:ℤ) :ℤ:=step j
private def aGP (b:ℕ) (j:ℤ) :ℤ:=((b:ℤ)+1)*step j
private theorem bY1 (base :ℕ→ℤ→ℤ) (k :ℕ) (j:ℤ) :
   count base k 0 j=base 0 j:= by
 induction k with
 | zero=>rfl
 | succ k ih=>simpa [count] using ih
private theorem bY0 (base :ℕ→ℤ→ℤ) (k b:ℕ) (j:ℤ) :
   count base (k+1) (b+1) j =
     count base k (b+1) j+count base (k+1) b (j-((k :ℤ)+1)) := by
 simp only [count]
 rw [Mk,add_comm]
 simp only [Nat.sub_zero,uz ,mul_zero,sub_zero]
 congr 1
 apply yL rfl
 intro i _
 rw [show b+1-(i+1)=b - i by omega]
 congr 1
 push_cast
 ring
private theorem dQy (base :ℕ→ℤ→ℤ)
   (hn : ∀ b j,j<0→base b j=0) (k b:ℕ) (j:ℤ) (hj:j<0) :
   count base k b j=0:= by
 induction k generalizing b j with
 | zero=>exact hn b j hj
 | succ k ih =>
     apply Finset.sum_eq_zero
     intro i _
     apply ih
     have h:0≤((k :ℤ)+1)*(i:ℤ) := by positivity
     omega
private theorem bYV (base :ℕ→ℤ→ℤ)
    (hn : ∀ b j,j<0→base b j=0) (k b j:ℕ) :
    count base (k+1) b j =
      ∑ i∈pz (min b (j/(k+1))+1),
        count base k (b - i) (j-(k+1)*i:ℕ) := by
  let w:=k+1
  let f := fun i:ℕ=>count base k (b - i) ((j:ℤ)-(w:ℤ)*i)
  change (∑ i∈pz (b+1),f i)= _
  have hw:0<w:= by dsimp [w]; omega
  calc
    _ = ∑ i∈pz (min b (j/w)+1),f i:= by
      symm
      apply P7 (LO (Nat.succ_le_succ (min_le_left _ _)))
      intro i hi hout
      have hib:=Finset.mem_range.mp hi
      have hij:j/w< i:= by
        have h:=mt Finset.mem_range.mpr hout
        omega
      have hs :=(Nr hw).mp hij
      unfold f
      apply dQy base hn
      rw [← zR,oj w i]
      exact sub_neg.mpr (by exact_mod_cast hs)
    _ = _:= by
      apply yL rfl
      intro i hi
      have hm:=Finset.mem_range.mp hi
      have hij:i≤j/w:= by omega
      have hs :=(FR hw).mp hij
      rw [oj] at hs
      unfold f
      rw [← zR,G5 hs]
private theorem bVW (b:ℕ) (j:ℤ) (h:j<0) :aGP b j=0:= by
 simp [aGP,step,not_le.mpr h]
private theorem gxU (b j:ℕ) :
  (Av b j:ℤ)=count aGP 3 b j:= by
 rw [bYV aGP bVW 2]
 simp_rw [bYV aGP bVW 1,bYV aGP bVW 0]
 simp [Av,count,aGP,step,Nat.cast_sum,qy]
private theorem dAj (k b:ℕ) (j:ℤ) :
   count aGP k b j = ∑ d∈pz (b+1),count bdv k d j:= by
 induction k generalizing b j with
 | zero=>simp [count,aGP,bdv,Nat.cast_add]
 | succ k ihk =>
     induction b generalizing j with
     | zero=>simp [bY1,aGP,bdv]
     | succ b ihb =>
         rw [bY0,ihk,ihb]
         conv_rhs=>rw [Mk]
         simp_rw [bY0 bdv,JQ]
         rw [Mk (fun d=>count bdv k d j) (b+1)]
         simp only [bY1]
         abel
private def shift (w:ℤ) (f :ℤ→ℤ) (j:ℤ) :ℤ:=f (j - w)
private def factors (a :ℤ) :ℕ→(ℤ→ℤ)→(ℤ→ℤ)
 | 0,f=>f
 | k+1,f=>factors a k (gI (a+k) f)
private theorem d56 (a :ℤ) (k :ℕ) (f :ℤ→ℤ) :
   factors a (k+1) f=factors (a+1) k (gI a f) := by
 induction k generalizing f with
 | zero=>simp [factors]
 | succ k ih =>
    rw [factors,ih,factors]
    have h:a+((k+1 :ℕ) :ℤ)=a+1+k := by omega
    rw [h]
    congr 1
    funext j
    simp only [gI]
    rw [show j-a-(a+1+k)=j-(a+1+k)-a by ring]
    ring
private theorem d58 (a :ℤ) (k :ℕ) (f g:ℤ→ℤ) :
    factors a k (fun j=>f j - g j)=fun j=>factors a k f j - factors a k g j:= by
  induction k generalizing f g with
  | zero=>rfl
  | succ k ih =>
      have h:gI (a+k) (fun j=>f j - g j) =
          fun j=>gI (a+k) f j - gI (a+k) g j:= by
        funext j
        simp only [gI]
        ring
      simpa only [factors,h] using ih (gI (a+k) f) (gI (a+k) g)
private theorem d57 (a w:ℤ) (k :ℕ) (f :ℤ→ℤ) :
    factors a k (shift w f)=shift w (factors a k f) := by
  induction k generalizing f with
  | zero=>rfl
  | succ k ih =>
      have h:gI (a+k) (shift w f)=shift w (gI (a+k) f) := by
        funext j
        simp only [gI,shift]
        rw [show j-(a+k) - w=j - w-(a+k) by ring]
      simpa only [factors,h] using ih (gI (a+k) f)
private def denominator :ℕ→ℤ→ℤ
 | 0=>gI 1 (gI 2 (gI 3 (row 0)))
 | 1=>gI 2 (gI 3 (row 0))
 | 2=>gI 3 (row 0)
 | _=>row 0
private theorem cKn (k :ℕ) (hk :k<3) :
  gI ((k :ℤ)+1) (denominator (k+1))=denominator k := by
 interval_cases k <;> rfl
def gaussian (k b:ℕ) :ℤ→ℤ:=factors ((b:ℤ)+1) k (denominator k)
private theorem efi (k :ℕ) (hk :k≤3) (j:ℤ) :gaussian k 0 j=step j:= by
  induction k with
  | zero=>exact cIg j
  | succ k ih =>
      have hd:=cKn k (by omega)
      simpa only [gaussian,factors,uz ,v9,add_comm (1 :ℤ) k,hd] using
        ih (by omega)
private theorem efh (k b:ℕ) (hk :k<3) (j:ℤ) :
   gaussian (k+1) (b+1) j =
     gaussian k (b+1) j+gaussian (k+1) b (j-((k :ℤ)+1)) := by
 let a :=(b:ℤ)+1
 let w:=(k :ℤ)+1
 let f :=denominator (k+1)
 have ha : ((b+1 :ℕ) :ℤ)+1=a+1 := by rfl
 simp only [gaussian,ha]
 change factors (a+1) (k+1) f j =
   factors (a+1) k (denominator k) j+factors a (k+1) f (j - w)
 rw [d56 a k]
 apply sub_eq_iff_eq_add.mp
 change factors (a+1) k (gI (a+1+k) f) j -
     shift w (factors (a+1) k (gI a f)) j= _
 rw [← d57,← Du (d58 _ _ _ _) j]
 have h: (fun j=>gI (a+1+k) f j - shift w (gI a f) j) =
     gI w f := by
   funext j
   simp only [gI,shift,w]
   rw [show j-(a+1+k)=j-((k :ℤ)+1)-a by ring]
   ring
 rw [h,cKn k hk]
private theorem d3I (k b:ℕ) (hk :k≤3) (j:ℤ) :
   count bdv k b j=gaussian k b j:= by
 induction k generalizing b j with
 | zero=>exact (cIg j).symm
 | succ k ihk =>
     induction b generalizing j with
     | zero=>exact (bY1 _ _ _).trans (efi _ hk _).symm
     | succ b ihb =>
         rw [bY0,efh k b (by omega),ihk _ (by omega),ihb]
theorem dgv (b j:ℕ) :
  (Av b j:ℤ) = ∑ d∈pz (b+1),gaussian 3 d j:= by
 rw [gxU,dAj]
 exact yL rfl fun d _=>d3I 3 d (by omega) j
theorem cTC (d:ℕ) (j:ℤ) :
    gaussian 3 d j =
      row 0 j-(row 0 (j-(1+d))+row 0 (j-(2+d))+row 0 (j-(3+d))) +
        (row 0 (j-(3+2*d))+row 0 (j-(4+2*d))+row 0 (j-(5+2*d))) -
        row 0 (j-(6+3*d)) := by
  simp only [gaussian,factors,denominator,gI]
  push_cast
  ring_nf
end aY8
end
section
namespace aY8
open FI
open scoped BigOperators
private theorem bOB (b r :ℕ) (hr :1≤ r) (hr' : r≤3) (j v :ℤ) :
    (∑ d∈pz (b+1),row 0 (j-(v+(r :ℤ)*d))) =
      row r (j - v) - row r (j-(v+(r :ℤ)*((b:ℤ)+1))) := by
  induction b with
  | zero =>
      simpa [gI,sub_sub] using (cNZ r hr hr' (j - v)).symm
  | succ b ih =>
      rw [Finset.sum_range_succ,ih]
      have h:=cNZ r hr hr' (j-(v+(r :ℤ)*((b:ℤ)+1)))
      simp only [gI] at h
      simp only [Nat.cast_succ]
      rw [show j-(v+(r :ℤ)*((b:ℤ)+1)) - r =
        j-(v+(r :ℤ)*((b:ℤ)+1+1)) by ring] at h
      omega
private theorem ddY (r j v :ℕ) :
   (ic r j v :ℤ)=row r ((j:ℤ) - v) := by
 unfold ic
 split
 · rw [← G5 ‹v≤j›,bLJ]
 · have h: (j:ℤ) - v<0:= by omega
   simp [bgV _ h]
private theorem bTR (b r j v :ℕ) (hr :1≤ r) (hr' : r≤3) :
   (aL5 b r j v :ℤ)=row r ((j:ℤ) - v) -
     row r ((j:ℤ)-(v+(r :ℤ)*((b:ℤ)+1))) := by
 have h₁:=ddY r j v
 have h₂:=ddY r j (v+r*(b+1))
 push_cast at h₂
 have hn:0≤ row r ((j:ℤ) - v) - row r ((j:ℤ)-(v+(r :ℤ)*((b:ℤ)+1))) := by
   rw [← bOB b r hr hr']
   exact Finset.sum_nonneg fun _ _=>fZt _ _
 unfold aL5
 rw [G5 (by omega),h₁,h₂]
private theorem dGk {count positive negative :ℕ}
 (h: (count:ℤ)=(positive :ℤ)-(negative :ℤ)) :
 count=positive - negative := by omega
theorem gxW (b j:ℕ) :Av b j=a3U b j:= by
  unfold a3U
  apply dGk
  rw [dgv]
  simp only [cTC,Finset.sum_sub_distrib,JQ,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul,qy ,zR,vk,
    bTR b 1 j _ (by decide) (by decide),
    bTR b 2 j _ (by decide) (by decide),
    bTR b 3 j _ (by decide) (by decide),← bLJ]
  have h (v :ℤ) :
      (∑ d∈pz (b+1),row 0 (j-(v+(d:ℤ)))) =
        row 1 (j - v) - row 1 (j-(v+((b:ℤ)+1))) := by
    simpa only [vk,one_mul] using bOB b 1 (by decide) (by decide) j v
  have h₂ (v :ℤ) :
      (∑ d∈pz (b+1),row 0 (j-(v+2*d))) =
        row 2 (j - v) - row 2 (j-(v+2*((b:ℤ)+1))) := by
    simpa only [yU] using bOB b 2 (by decide) (by decide) j v
  have h₃ :
      (∑ d∈pz (b+1),row 0 (j-(6+3*d))) =
        row 3 (j-6) - row 3 (j-(6+3*((b:ℤ)+1))) := by
    simpa only [yU] using bOB b 3 (by decide) (by decide) j 6
  rw [h 1,h 2,h 3,h₂ 3,h₂ 4,h₂ 5,h₃]
  norm_num
  ring
end aY8
end
section
namespace YX
noncomputable section
open K1 cu gT pI XY
open scoped BigOperators
def aL7 (s :p5) (x y :ℕ) :Shape :=
 ⟨s.m,s.B-y,min s.J (s.B-y),s.U-x⟩
structure bjf (I:aU lJ) :Prop where
 Kw:pC aQ (Y0 I)
 jU:pC dV (ani I)
 kK:pC dV (Ik I)
 Bo:pC aQ (Lj I)
def bQz (P Q:Jet) (S:qm (aU lJ)) :Prop :=
 ∀ I∈S,I.IsPrime∧oy (gk I)=2∧iJ P∈I∧iJ Q∈I
def aJh (s t:p5) :Fin 4→ℕ :=
  ![s.B*t.J+t.B*s.J - s.J*t.J,
    s.U*t.J+t.U*s.J,s.U*t.B+t.U*s.B,s.U*t.U]
def af1 (x y :ℕ) :Fin 4→ℕ := ![y,x,2*x*y,x*x]
end
end YX
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace YX
noncomputable section
open K1 cu gT pI XY Polynomial
open scoped BigOperators Classical
theorem eHM (D:qm nI) (x y :ℕ)
    (hx : ∑ f∈D,My f≤x) (hy : ∑ f∈D,f.natDegree≤y)
    (k :Fin 4) :
    (∑ f∈D,af1 (My f) f.natDegree k)≤af1 x y k := by
  fin_cases k
  · exact hy
  · exact hx
  · change (∑ f∈D,2*My f*f.natDegree)≤2*x*y
    calc
      _ ≤ ∑ f∈D,2*My f*y := by
        apply Df
        intro f hf
        exact p6 _ ((Dw (fun _ _=>vG _) hf).trans hy)
      _=(2 * ∑ f∈D,My f)*y := by rw [Finset.mul_sum,Kz]
      _≤_:=sH _ (p6 _ hx)
  · change (∑ f∈D,My f*My f)≤x*x
    calc
      _ ≤ ∑ f∈D,My f*x := by
        apply Df
        intro f hf
        exact p6 _ ((Dw (fun _ _=>vG _) hf).trans hx)
      _=(∑ f∈D,My f)*x :=(Kz _ _ _).symm
      _≤_:=sH _ hx
theorem evL {S:qm (aU lJ)} {I:aU lJ} (hI:I∈S)
  (k :Fin 4) :pN I k≤ mass S k :=
 Dw (f := fun J=>pN J k) (fun _ _=>vG _) hI
private theorem d2F (z :K) (R:K[X]) (f :FX[X]) :
  aci z R (F7 f)=f.eval (kr R) := by
 have hC: (aci z R).comp nq=MO FX :=
  MK fun c=> by simp [aci]
 have hY:aci z R (lI 2)=kr R:= by simp [aci]
 change aci z R (f.eval₂ nq (lI 2))=f.eval (kr R)
 rw [Polynomial.hom_eval₂,hC,hY,Polynomial.eval₂_id]
theorem eHX {I:aU lJ} (hI:I.IsPrime)
   (hn : ¬ pQ ((ox I).comp F7))
   {z z' : K} {R R' : K[X]} (h:IZ I z R) (h' : IZ I z' R') :kr R=kr R' := by
 let:I.IsPrime :=hI
 let φ:=(ox I).comp F7
 let J:=p7 φ
 have hJ:J.IsMaximal :=
   (Dz φ).isMaximal_of_ne_bot
     (fun eq=>hn ((RJ φ).mpr eq))
 have heval {w:K} {S:K[X]} (hS:IZ I w S) :
     J≤p7 (evalRingHom (kr S)) := by
   intro f hf
   have hm:F7 f∈I:=Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hf)
   exact RingHom.mem_ker.mpr ((d2F w S f).symm.trans (RingHom.mem_ker.mp (hS hm)))
 have heq :=hJ.eq_of_le (RingHom.ker_ne_top _) (heval h)
 have hlin: (pU (R:=FX)-Polynomial.C (kr R))∈J:= by
   rw [heq]
   apply RingHom.mem_ker.mpr
   simp
 have hv :=RingHom.mem_ker.mp (heval h' hlin)
 simpa [sub_eq_zero,eq_comm] using hv
end
end YX
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace YX
noncomputable section
open K1 cu gT pI XY Polynomial
open scoped BigOperators Classical
def c2 :Prop :=
  ∀ f :nI,oZ f→0<f.natDegree→f.natDegree<p →
    ∃ g a,qQ.aw5 f g a∧ag6 (C f) (qQ.caE g) ∧
      ∀ z S,yq f z S=0→ rD (qQ.caE g) z S=0
def c3:Prop :=
  ∀ P Q:Jet,ag6 P Q →
    ∃ S:qm (aU lJ),bQz P Q S ∧
      ∀ z R,rD P z R=0→ rD Q z R=0 → ∃ I∈S,IZ I z R
def c4 :Prop :=
  ∀ P Q:Jet,ag6 P Q → ∀ s t,
    s.J≤ s.B→t.J≤t.B→ oU P s→ oU Q t →
    ∀ S,bQz P Q S →
      (∀ I∈S,bjf I)∧dM S (aJh s t)
def c6:Prop :=
  ∀ I:aU lJ,I.IsPrime→ oy (gk I)=2 →
    bjf I→pN I 0=0 →
    ∃ C:qQ.VN,C.curve.totalDegree≤pN I 2 ∧
      C.points.card≤pN I 3 ∧ ∀ z R,IZ I z R→C.ow z
end
end YX
end
section
namespace atd
noncomputable section
open cu gT pI Polynomial

abbrev jY:n5→Type
 | .seed | .Bo=>aQ
 | .jU | .kK=>dV
instance (s :n5) :oq (jY s) := by
 cases s <;> infer_instance
abbrev lK (F:Type) [oq F] :=c9 (Fin 2) F
def Xn (kK:Bool) :PI →ₐ[dV] lK dV :=
  t3
    ![nq (kz 2)-MvPolynomial.C (kz 0)*lI 0,
      lI 0,
      nq (kz 3) -
       nq (if kK then kz 1 else 0)*lI 1,
      lI 1]
def grT: (s :n5)→lJ →+* lK (jY s)
 | .seed=>Dk
 | .jU=>(Xn false).toRingHom.comp AU
 | .kK=>(Xn true).toRingHom.comp AU
 | .Bo=>CG
abbrev cAq (s :n5) (I:aU lJ) :=
 gk (I.map (grT s))
end
end atd
end
section
namespace aeE
noncomputable section
open K1 cu gT pI

def jY:n5→Type
 | .seed | .Bo=>aQ
 | .jU | .kK=>dV
instance (s :n5) :oq (jY s) := by
 cases s <;> unfold jY <;> infer_instance
def coefficients (s :n5) :FX →+* jY s :=
 match s with
 | .seed | .Bo=>algebraMap FX aQ
 | .jU | .kK=>algebraMap FX dV
abbrev lK (F:Type) [oq F] :=c9 (Fin 2) F
def amL (s :n5) :Fin 2→lK (jY s) :=
  match s with
  | .seed=> fun i=>MvPolynomial.C (ek i)
  | .jU | .kK =>
    ![nq (kz 2)-MvPolynomial.C (kz 0)*lI 0,
      lI 0]
  | .Bo=>MvPolynomial.X
def aoA (s :n5) :lK (jY s) :=
 match s with
 | .seed=>MvPolynomial.X 0
 | .jU=>MvPolynomial.C (kz 3)
 | .kK=>MvPolynomial.C (kz 3)-MvPolynomial.C (kz 1)*MvPolynomial.X 1
 | .Bo=>MvPolynomial.C (ek 0)
def an4 (s :n5) :lK (jY s) :=
 match s with
 | .Bo=>MvPolynomial.C (ek 1)
 | .seed | .jU | .kK=>MvPolynomial.X 1
def aD (s :n5) :Fin 4→lK (jY s) :=
 ![amL s 0,amL s 1,aoA s,an4 s]
def Yx (s :n5) :lJ →+* lK (jY s) :=
 qz (MvPolynomial.C.comp (coefficients s)) (aD s)
def Bu (s :n5) :Jet →+* lK (jY s) :=(Yx s).comp iJ
def bbh (s :n5) :Prop :=
  ∀ I:aU lJ,I.IsPrime →
    I.map (Yx s) = ⊤ ∨
      (I.map (Yx s)).IsPrime∧(I.map (Yx s)).comap (Yx s)=I
structure bTo {F:Type} [oq F] (P Q:lK F) :Prop where
 left_ne :P≠0
 right_ne :Q≠0
 no_common : ∀ D:lK F,oZ D→D ∣P → ¬ D ∣Q
def dqj (s :n5) (d:p5) (P:lK (jY s)) :Prop :=
 match s with
 | .seed=>P.totalDegree≤d.B∧P.degreeOf 1≤d.J
 | .jU=>P.degreeOf 0≤d.U∧P.degreeOf 1≤d.J
 | .kK=>P.degreeOf 0≤d.U∧P.degreeOf 1≤d.B
 | .Bo=>P.totalDegree≤d.U
abbrev cAd {F:Type} [oq F] (P Q:lK F) :=
 lK F ⧸ nX ({P,Q} : Set (lK F))
def by0 {F:Type} [oq F] (P Q:lK F) (n:ℕ) :Prop :=
 pC F (cAd P Q)∧lV F (cAd P Q)≤n
end
end aeE
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace atd
noncomputable section
open cu gT pI YX Polynomial

open scoped BigOperators
private def azt (kK:Bool) :aU PI :=
 nX {JN,if kK then Z6 else
  lI 2 - nq (kz 3)}
private def aU1 :lK dV →ₐ[dV] PI :=
 yo ![1,3]
private theorem ewC (kK:Bool) :zh (Xn kK) := by
 have h: (Xn kK).comp aU1=AlgHom.id _ _:= by
  apply wR
  intro i
  fin_cases i <;> simp [ Xn,aU1]
 intro q
 exact ⟨aU1 q,RP h q⟩
private theorem ewB (kK:Bool) :
    p7 (Xn kK).toRingHom=azt kK:= by
  let π:=t6 dV (azt kK)
  have hconst (a :dV) :
      π (nq a)=mD dV (PI ⧸ azt kK) a :=
    π.commutes a
  have hseed :π JN=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (vw (by simp))
  have hjet:π (if kK then Z6 else
      lI 2 - nq (kz 3))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (vw (by simp))
  have h: (π.comp aU1).comp (Xn kK)=π:= by
    apply wR
    intro i
    fin_cases i
    · simp [ Xn,aU1]
      simp only [JN,LQ,wY ,pL,hconst] at hseed
      linear_combination -hseed
    · simp [ Xn,aU1]
    · cases kK <;> simp [ Xn,aU1]
      · simp only [Bool.false_eq_true,ite_false,LQ,hconst] at hjet
        linear_combination -hjet
      · simp only [ite_true,Z6,LQ,wY ,pL,hconst] at hjet
        linear_combination -hjet
    · simp [ Xn,aU1]
  apply qM
  · intro q hq
    have hq' : Xn kK q=0:=hq
    have he :=RP h q
    simp only [Kp,hq',th] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm
  · apply Ideal.span_le.mpr
    intro q hq
    simp only [Pk,LR] at hq
    rcases hq with rfl | rfl
    · change Xn kK JN=0
      simp [JN,Xn]
    · change Xn kK (if kK then Z6 else _)=0
      cases kK <;> simp [Z6,Xn]
private def bfg (kK:Bool) (I:aU lJ) :
   gk (I.map AU ⊔ azt kK) ≃ₐ[dV]
     gk (I.map ((Xn kK).toRingHom.comp AU)) := by
 let e :=Xn kK
 let J:=I.map AU
 let J' := J.map e.toRingHom
 have he :zh e.toRingHom:=ewC kK
 have hh:J'.comap e.toRingHom=J ⊔ azt kK:= by
   change (J.map e.toRingHom).comap e.toRingHom= _
   rw [Ar _ he,← Pr]
   exact oD (J ⊔ ·) (ewB kK)
 let g:=Fz J' e hh.ge
 have hg:Function.Bijective g:=⟨Ob (H :=hh.ge) hh.le,
   QL (H :=hh.ge) he⟩
 change gk (J ⊔ azt kK) ≃ₐ[dV]
   gk (I.map (e.toRingHom.comp AU))
 rw [← vj]
 exact PD g hg
def bJ0 (I:aU lJ) :
    ani I ≃ₐ[dV] cAq .jU I :=
  bfg false I
def bJf (I:aU lJ) :
    Ik I ≃ₐ[dV] cAq .kK I :=
  bfg true I
end
end atd
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1000000
namespace aeE
noncomputable section
open K1 cu gT XY Polynomial

theorem aJQ (A:aZ) :iJ (C (C A))=oi (pZ A) := by
 simp [iJ,A7]
theorem ctB:iJ (C (pU (R:=aZ)))=lI 2 := by
 simp [iJ,A7,oi]
theorem ctA:iJ (pU (R:=nI))=lI 3:= by
 simp [iJ]
private def au2 :lJ →+* Jet :=
 qz (C.comp (C.comp nq))
  ![C (C (lI 0)),C (C (lI 1)),C pU,pU]
private theorem een :
   au2.comp (oi.comp pZ) =
    (C:nI →+* Jet).comp (C:aZ →+* nI) := by
 apply t4
 · intro c
   simp [au2,oi,pZ]
 · intro i
   fin_cases i <;> simp [au2,oi,pZ]
private theorem evh:au2.comp iJ=MO Jet:= by
 apply z8
 · intro A
   change ((au2.comp iJ).comp (C:nI →+* Jet)) A=(C:nI →+* Jet) A
   suffices h: (au2.comp iJ).comp (C:nI →+* Jet)=C from
     v8 h A
   apply z8
   · intro B
     change au2 (iJ (C (C B)))=C (C B)
     rw [aJQ]
     exact v8 een B
   · simp [C9,ctB,au2]
 · simp [C9,ctA,au2]
private theorem fXB:iJ.comp au2=MO Ambient:= by
 apply t4
 · intro c
   simp [au2,aJQ,oi,pZ]
 · intro i
   fin_cases i <;> simp [au2,aJQ,ctB,ctA,
    oi,pZ]
private def S5:Jet ≃+* Ambient :=
 { iJ with
   invFun:=au2
   left_inv :=v8 evh
   right_inv :=v8 fXB }
private theorem gD0 {A T:Type} [oY A] [zm A]
   [oY T] [Nontrivial T] (g:A →+* T)
   (ht : ∀ I:aU A,I.IsPrime →
     I.map g = ⊤ ∨ (I.map g).IsPrime∧(I.map g).comap g=I) :
   Function.Injective g:= by
 have h:=ht ⊥ Ideal.isPrime_bot
 rw [Ideal.map_bot] at h
 exact (RJ g).mpr (h.resolve_left bot_ne_top).2
private theorem ey9 {R A T:Type}
    [oY R] [zm R] [u9 R]
    [oY A] [zm A] [u9 A]
    [oY T] [zm T] [u9 T]
    (e :R ≃+* A) (g:A →+* T)
    (ht : ∀ I:aU A,I.IsPrime →
      I.map g = ⊤ ∨ (I.map g).IsPrime∧(I.map g).comap g=I)
    (P Q:R) (hP:P≠0) (hQ:Q≠0)
    (hcop : ∀ a :R,oZ a→a∣P → ¬ a∣Q) :
    let f :=g.comp e.toRingHom
    f P≠0∧f Q≠0 ∧ ∀ D:T,oZ D→D ∣f P → ¬ D ∣f Q:= by
  let f :=g.comp e.toRingHom
  change f P≠0∧f Q≠0 ∧ ∀ D:T,oZ D→D ∣f P → ¬ D ∣f Q
  have hf :pQ f :=(gD0 g ht).comp e.injective
  refine ⟨(t7 f hf).mpr hP,(t7 f hf).mpr hQ,?_⟩
  intro D hD hdP hdQ
  have hprime :=hD.prime
  have hex : ∀ B:R,B≠0→D ∣f B → ∃ a :R,oZ a∧a∣B∧D ∣f a := by
    intro B
    induction B using WfDvdMonoid.induction_on_irreducible with
    | zero=>simp
    | unit B hB =>
      intro _ h
      exact (hD.not_isUnit (Pf h (hB.map f))).elim
    | mul B a hB ha ih =>
      intro _ h
      rw [pL] at h
      rcases hprime.dvd_mul.mp h with h | h
      · exact ⟨a,ha,dvd_mul_right a B,h⟩
      · obtain ⟨b,hb,hba,hbd⟩:=ih hB h
        exact ⟨b,hb,hba.trans ⟨a,oj a B⟩,hbd⟩
  obtain ⟨a,ha,haP,hDa⟩:=hex P hP hdP
  have ha' : oZ (e a) :=ha.map e.toMulEquiv
  let I:aU A:=nX {e a}
  have hI:I.IsPrime :=Ideal.isPrime_span_singleton_of_prime ha'.prime
  have hspan:I.map g=nX {f a} := by
    change (nX {e a}).map g= _
    rw [KH,UP]
    rfl
  have hnt:I.map g ≠ ⊤ := by
    rw [hspan]
    exact fun h=>hD.not_isUnit (Pf hDa (Ideal.span_singleton_eq_top.mp h))
  have htrans :=(ht I hI).resolve_left hnt
  have hJ: (nX {f a}).IsPrime :=hspan ▸ htrans.1
  have hfa :f a≠0:=(t7 f hf).mpr ha.ne_zero
  have haf :Prime (f a) :=(TI hfa).mp hJ
  have had:f a∣D:=(hD.associated_of_dvd haf.irreducible hDa).dvd'
  have hQmem:e Q∈I:= by
    rw [← htrans.2]
    change f Q∈I.map g
    rw [hspan,Ideal.mem_span_singleton]
    exact had.trans hdQ
  have hdiv :e a∣e Q:=Ideal.mem_span_singleton.mp hQmem
  exact hcop a ha haP ((G8 e).mp hdiv)
theorem bLE (s :n5) (ht:bbh s) (P Q:Jet)
  (hp:ag6 P Q) :bTo (Bu s P) (Bu s Q) := by
 let:oY Equation := @SM aZ y5
 let:oY Jet := @SM nI y5
 let:u9 FX:=PrincipalIdealRing.to_uniqueFactorizationMonoid
 let:u9 Ambient:=Kc (Fin 4)
 let:u9 aZ:=Kc (Fin 2)
 let:u9 (lK (jY s)) :=
  Kc (Fin 2)
 obtain ⟨hP,hQ,hcop⟩ :=
  ey9 S5 (Yx s) ht P Q hp.left_ne hp.right_ne hp.no_common
 exact ⟨hP,hQ,hcop⟩
end
end aeE
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace aeE
noncomputable section
open K1 cu gT pI Polynomial

open scoped BigOperators
private abbrev bVq (s :n5) :=
 (nq:jY s →+* lK (jY s)).comp (coefficients s)
private theorem d2O (s :n5) (A:aZ) :
   Bu s (C (C A))=qz (bVq s) (amL s) A:= by
 have h: (Yx s).comp (oi.comp pZ) =
     qz (bVq s) (amL s) := by
   apply t4
   · intro c
     simp [pZ,oi,Yx,MvPolynomial.eval₂Hom_C]
   · intro i
     fin_cases i <;> simp [pZ,oi,Yx,aD,zk]
 change Yx s (iJ (C (C A)))= _
 rw [aJQ]
 exact v8 h A
private theorem bdu (s :n5) :
  Bu s (C (pU (R:=aZ)))=aoA s := by
 simp [Bu,ctB,Yx,aD]
private theorem d3f (s :n5) :
  Bu s (pU (R:=nI))=an4 s := by
 simp [Bu,ctA,Yx,aD]
private theorem crD {F ι:Type} [oq F] (D:lK F→ℕ)
   (h0:D 0=0) (hadd : ∀ f g,D (f+g)≤ max (D f) (D g))
   (T:qm ι) (a :ι→lK F) (N :ℕ) (h : ∀ i∈T,D (a i)≤N) :
   D (∑ i∈T,a i)≤N := by
 classical
 induction T using Finset.induction_on with
 | empty=>simp [h0]
 | @insert i T hi ih =>
   rw [Nq hi]
   exact (hadd _ _).trans (t8 (h i (Finset.mem_insert_self _ _))
     (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj))))
private theorem aNb (s :n5) (P:Jet) (d:p5) (h:oU P d)
    (D:lK (jY s)→ℕ) (h0:D 0=0) (h1 :D 1=0)
    (hadd : ∀ f g,D (f+g)≤ max (D f) (D g))
    (hmul : ∀ f g,D (f * g)≤D f+D g)
    (hpow : ∀ f n,D (f^n)≤n*D f)
    (hconst : ∀ a :jY s,D (nq a)=0)
    (u e j N :ℕ)
    (hu : ∀ i,D (amL s i)≤u)
    (he :D (aoA s)≤e) (hj:D (an4 s)≤j)
    (hN : ∀ v y,y+v≤d.B→v≤d.J→d.U*u+y*e+v*j≤N) :
    D (Bu s P)≤N := by
  classical
  have hseed (A:aZ) :D (Bu s (C (C A)))≤A.totalDegree*u:= by
    rw [d2O]
    conv_lhs=>rw [A.as_sum]
    rw [zd]
    apply crD D h0 hadd
    intro m hm
    rw [MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_monomial]
    apply (hmul _ _).trans
    rw [show bVq s (A.coeff m) =
      nq (coefficients s (A.coeff m)) from rfl,hconst,v9]
    unfold Finsupp.prod
    refine (m.support.apply_prod_le_sum_apply D (by rw [h1]) hmul).trans ?_
    calc
      _ ≤ ∑ i∈m.support,m i*u :=
        Df fun i _=>(hpow _ _).trans (p6 _ (hu i))
      _=m.degree*u:= by rw [← Kz ,Finsupp.degree_apply]
      _≤_:=sH u (sS hm)
  conv_lhs=>rw [P.as_sum_support_C_mul_X_pow]
  rw [zd]
  apply crD D h0 hadd
  intro v hv
  rw [pL,zf ,d3f]
  refine (hmul _ _).trans ?_
  have hv' := (hpow (an4 s) v).trans (p6 v hj)
  have hc:D (Bu s (C (P.coeff v)))≤N - v*j:= by
    conv_lhs=>rw [(P.coeff v).as_sum_support_C_mul_X_pow]
    rw [zd ,zd]
    apply crD D h0 hadd
    intro y hy
    rw [pL,pL,zf ,zf ,bdu]
    have hrow:=h v y (mem_support_iff.mp hy)
    have hs :=(hseed ((P.coeff v).coeff y)).trans (sH u hrow.2.2)
    have ht:=(hpow (aoA s) y).trans (p6 y he)
    have hn:=hN v y hrow.1 hrow.2.1
    exact (hmul _ _).trans (by omega)
  obtain ⟨y,hy⟩:=support_nonempty.mpr (mem_support_iff.mp hv)
  have hrow:=h v y (mem_support_iff.mp hy)
  have hn:=hN v y hrow.1 hrow.2.1
  omega
private theorem dhH (s :n5) (P:Jet) (d:p5) (h:oU P d)
  (u e j N :ℕ)
  (hu : ∀ i,(amL s i).totalDegree≤u)
  (he : (aoA s).totalDegree≤e) (hj: (an4 s).totalDegree≤j)
  (hN : ∀ v y,y+v≤d.B→v≤d.J→d.U*u+y*e+v*j≤N) :
  (Bu s P).totalDegree≤N :=
 aNb s P d h SC RC
  MvPolynomial.totalDegree_one MvPolynomial.totalDegree_add Kh
  MvPolynomial.totalDegree_pow MvPolynomial.totalDegree_C u e j N hu he hj hN
private theorem boP (i:Fin 2) (s :n5) (P:Jet) (d:p5) (h:oU P d)
  (u e j N :ℕ)
  (hu : ∀ a,(amL s a).degreeOf i≤u)
  (he : (aoA s).degreeOf i≤e) (hj: (an4 s).degreeOf i≤j)
  (hN : ∀ v y,y+v≤d.B→v≤d.J→d.U*u+y*e+v*j≤N) :
  (Bu s P).degreeOf i≤N :=
 aNb s P d h (MvPolynomial.degreeOf i) (MvPolynomial.degreeOf_zero i)
  (MvPolynomial.degreeOf_one i) (MvPolynomial.degreeOf_add_le i) (JM i)
  (MvPolynomial.degreeOf_pow_le i) (fun a=>MvPolynomial.degreeOf_C a i) u e j N hu he hj hN
private theorem go0 :
   (nq (kz 2) -
     nq (kz 0)*lI (0:Fin 2)).totalDegree≤1 :=
 (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp)
   ((Kh  _ _).trans (by simp)))
private theorem eHZ :
   (nq (kz 3) -
     nq (kz 1)*lI (1 :Fin 2)).totalDegree≤1 :=
 (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp)
   ((Kh  _ _).trans (by simp)))
theorem fZc (s :n5) (P:Jet) (d:p5) (h:oU P d) :
    dqj s d (Bu s P) := by
  classical
  have seed_deg0 : ∀ i,(amL .jU i).degreeOf 0≤1 := by
    rw [UZ]
    constructor
    · apply (C4 _ _).trans
      simpa only [amL,Vz] using go0
    · simp [amL]
  have seed_deg1 : ∀ i,(amL .jU i).degreeOf 1≤0:= by
    rw [UZ]
    constructor
    · change (nq (kz 2) -
          nq (kz 0)*lI (0:Fin 2)).degreeOf 1≤0
      apply (SU _ _ _).trans
      apply t8
      · simp
      · exact (JM _ _ _).trans (by simp [yB])
    · simp [amL,yB]
  have ordinate_deg0: (aoA .kK).degreeOf 0≤0:= by
    change (nq (kz 3) -
      nq (kz 1)*lI (1 :Fin 2)).degreeOf 0≤0
    apply (SU _ _ _).trans
    apply t8
    · simp
    · exact (JM _ _ _).trans (by simp [yB])
  cases s
  · refine ⟨dhH .seed P d h 0 1 1 d.B ?_ (by simp [aoA])
        (by simp [an4]) (by intro v y hB hJ; omega),
      boP 1 .seed P d h 0 0 1 d.J ?_
        (by simp [aoA,yB ])
        (by simp [an4]) (by intro v y hB hJ; omega)⟩
    all_goals intro i; fin_cases i <;> simp [amL]
  · exact ⟨boP 0 .jU P d h 1 0 0 d.U seed_deg0
        (by simp [aoA]) (by simp [an4,yB])
        (by intro v y hB hJ; omega),
      boP 1 .jU P d h 0 0 1 d.J seed_deg1
        (by simp [aoA]) (by simp [an4]) (by intro v y hB hJ; omega)⟩
  · exact ⟨boP 0 .kK P d h 1 0 0 d.U seed_deg0 ordinate_deg0
        (by simp [an4,yB]) (by intro v y hB hJ; omega),
      boP 1 .kK P d h 0 1 1 d.B seed_deg1
        ((C4 _ _).trans
          (by simpa only [aoA] using eHZ))
        (by simp [an4]) (by intro v y hB hJ; omega)⟩
  · exact dhH .Bo P d h 1 0 0 d.U (by simp [amL])
      (by simp [aoA]) (by simp [an4]) (by intro v y hB hJ; omega)
end
end aeE
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace aeE
noncomputable section
open K1 cu gT pI
section LinearCuts
variable {k :Type} [oY k]
private abbrev Four (F:Type) [xm F] :=c9 (Fin 4) F
private def ayv (a b u v :k) :Fin 4→c9 (Fin 2) k :=
 ![nq u-MvPolynomial.C a*lI 0,lI 0,
   nq v-MvPolynomial.C b*lI 1,lI 1]
private def Va (a b u v :k) :Four k →ₐ[k] c9 (Fin 2) k :=
 t3 (ayv a b u v)
private def BI (a u:k) :Four k :=
 lI (0:Fin 4)+MvPolynomial.C a*lI 1-MvPolynomial.C u
private def aOf (b v :k) :Four k :=
 lI (2 :Fin 4)+MvPolynomial.C b*lI 3-MvPolynomial.C v
private def a5t (a b u v :k) :aU (Four k) :=
 nX {BI a u,aOf b v}
private theorem cJa (a b u v :k) :zh (Va a b u v) := by
 let restore :c9 (Fin 2) k →ₐ[k] Four k :=t3 ![lI 1,lI 3]
 have h: (Va a b u v).comp restore=AlgHom.id k _:= by
  apply wR
  intro i
  fin_cases i <;> simp [Va,ayv,restore]
 intro f
 exact ⟨restore f,AlgHom.congr_fun h f⟩
private theorem dST (a b u v :k) :
    p7 (Va a b u v).toRingHom=a5t a b u v := by
  let q:=t6 k (a5t a b u v)
  let restore :c9 (Fin 2) k →ₐ[k] (Four k ⧸ a5t a b u v) :=
    t3 ![q (lI 1),q (lI 3)]
  have hs :q (BI a u)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (vw (Set.mem_insert _ _))
  have hj:q (aOf b v)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (vw (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have h:restore.comp (Va a b u v)=q:= by
    apply wR
    intro i
    rw [Kp,Va,PM]
    fin_cases i
    · rw [show ayv a b u v (⟨0,by decide⟩:Fin 4) =
        nq  u-MvPolynomial.C a*lI  0 from rfl]
      simp only [LQ ,pL ,restore,VH ,PM ,
        Vz ]
      apply sub_eq_iff_eq_add.mpr
      symm
      apply sub_eq_zero.mp
      change q (lI  (0:Fin 4))+_-_=0
      simpa only [BI,LQ ,wY ,pL ,← vZ ,
        AlgHom.commutes] using hs
    · rw [show ayv a b u v (⟨1,by decide⟩:Fin 4)=MvPolynomial.X 0 from rfl]
      simp [restore]
    · rw [show ayv a b u v (⟨2,by decide⟩:Fin 4) =
        nq  v-MvPolynomial.C b*lI  1 from rfl]
      simp only [LQ ,pL ,restore,VH ,PM ,
        Matrix.cons_val_one,Vz ]
      apply sub_eq_iff_eq_add.mpr
      symm
      apply sub_eq_zero.mp
      change q (lI  (2 :Fin 4))+_-_=0
      simpa only [aOf,LQ ,wY ,pL ,← vZ ,
        AlgHom.commutes] using hj
    · rw [show ayv a b u v (⟨3,by decide⟩:Fin 4)=MvPolynomial.X 1 from rfl]
      simp [restore]
  apply qM
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hx' := AlgHom.congr_fun h x
    have hx0:Va a b u v x=0:=RingHom.mem_ker.mp hx
    rw [Kp,hx0,th] at hx'
    exact hx'.symm
  · apply Ideal.span_le.mpr
    intro x hx
    apply RingHom.mem_ker.mpr
    rcases (Set.mem_insert_iff.mp hx) with rfl | hx
    · simp [Va,ayv,BI,← vZ]
    · obtain rfl :=Set.mem_singleton_iff.mp hx
      simp [Va,ayv,aOf,← vZ]
private def bDI {F:Type} [oY F] (g:F →+* k)
   (I:aU (c9 (Fin 4) F)) (a b u v :k) :
   (Four k ⧸ (I.map (oz g) ⊔ a5t a b u v)) ≃ₐ[k]
     (c9 (Fin 2) k ⧸ I.map ((Va a b u v).toRingHom.comp (oz g))) := by
 let cut:=Va a b u v
 let J:=I.map (cut.toRingHom.comp (oz g))
 have h:I.map (oz g) ⊔ a5t a b u v=J.comap cut.toRingHom:= by
   unfold J
   rw [← vj,Ar cut.toRingHom (cJa a b u v)]
   exact oD (I.map (oz g) ⊔ ·) (dST a b u v).symm
 let f :=Fz J cut h.le
 exact PD f
   ⟨Ob (H :=h.le) h.ge,
     QL (H :=h.le) (cJa a b u v)⟩
private theorem cI8 {F:Type} [oY F] (g:F →+* k) (a b u v :k) :
   (Va a b u v).toRingHom.comp (oz g) =
     qz (MvPolynomial.C.comp g) (ayv a b u v) := by
 apply MK
 intro p
 change t3 (ayv a b u v) (oz g p)= _
 rw [MvPolynomial.aeval_eq_eval₂Hom,MvPolynomial.eval₂Hom_map_hom,vZ]
end LinearCuts
def bJ0 (I:aU lJ) :
    ani I ≃ₐ[dV] (lK dV ⧸ I.map (Yx .jU)) := by
  have hcoords :ayv (kz 0) (0:dV)
      (kz 2) (kz 3)=aD .jU:= by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change nq (kz 3) -
        nq (0:dV)*lI (1 :Fin 2) =
          nq (kz 3)
      simp
    · rfl
  have hmap : (Va (kz 0) 0 (kz 2) (kz 3)).toRingHom.comp
      (oz (mD FX dV))=Yx .jU:= by
    rw [cI8,hcoords]
    rfl
  rw [← hmap]
  have hline :aOf (0:dV) (kz 3) =
      lI (2 :Fin 4)-MvPolynomial.C (kz 3) := by
    simp [aOf,MvPolynomial.C_0]
  have hsrc :I.map AU ⊔ nX
      {JN,lI 2 - nq (kz 3)} =
      I.map (oz (mD FX dV)) ⊔
        a5t (kz 0) 0 (kz 2) (kz 3) := by
    unfold a5t
    rw [hline]
    rfl
  exact (Ideal.quotientEquivAlgOfEq dV hsrc).trans
    (bDI (mD FX dV) I (kz 0) 0 (kz 2)
      (kz 3))
def bJf (I:aU lJ) :
    Ik I ≃ₐ[dV] (lK dV ⧸ I.map (Yx .kK)) := by
  have hcoords :ayv (kz 0) (kz 1)
      (kz 2) (kz 3)=aD .kK:= by
    funext i
    fin_cases i <;> rfl
  have hmap : (Va (kz 0) (kz 1) (kz 2)
      (kz 3)).toRingHom.comp (oz (mD FX dV)) =
      Yx .kK:= by
    rw [cI8,hcoords]
    rfl
  rw [← hmap]
  exact bDI (mD FX dV) I (kz 0) (kz 1)
    (kz 2) (kz 3)
end
end aeE
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace aeE
noncomputable section
open cu gT YX

open scoped BigOperators
private theorem gw4 {k R ι:Type} [oq k] [oY R] [Algebra k R]
   (L:aU R) (J:ι→ aU R) (qs :qm ι) [pC k (R ⧸ L)]
   (hcont : ∀ q∈qs,L≤J q)
   (hprime : ∀ q∈qs,J q = ⊤ ∨ (J q).IsPrime)
   (hdisjoint : ∀ q∈qs,∀ r∈qs,J q ≠ ⊤ → J r ≠ ⊤ → J q=J r→q=r) :
   (∑ q∈qs,lV k (R ⧸ J q))≤lV k (R ⧸ L) := by
 classical
 let T:=qs.filter fun q=>J q ≠ ⊤
 let J' : T→ aU R:= fun q=>J q
 have hT (q:T) : (q:ι)∈qs :=(Finset.mem_filter.mp q.property).1
 have hne (q:T) :J q ≠ ⊤ := (Finset.mem_filter.mp q.property).2
 have hle (q:T) :L≤J q:=hcont q (hT q)
 let (q:T) :pC k (R ⧸ J' q) :=
   G4 (Gk k (hle q)).toLinearMap
     (Te (hle q))
 have hJM (q:T) : (J q).IsMaximal:= by
   let: (J' q).IsPrime :=(hprime q (hT q)).resolve_left (hne q)
   let:IsArtinianRing (R ⧸ J' q) :=IsArtinianRing.of_finite k _
   exact Ideal.Quotient.maximal_of_isField (J' q) (IsArtinianRing.isField_of_isDomain _)
 have hcop:Pairwise fun q r=>IsCoprime (J' q) (J' r) := by
   intro q r hqr
   apply Ideal.isCoprime_iff_sup_eq.mpr
   apply (hJM q).coprime_of_ne
   · exact hJM r
   · exact fun h=>hqr (KA (hdisjoint q (hT q) r (hT r) (hne q) (hne r) h))
 let f :R ⧸ L →ₗ[k] ∀ q:T,R ⧸ J' q :=
   LinearMap.pi fun q=>(Gk k (hle q)).toLinearMap
 have hsurj:zh f := by
   intro x
   obtain ⟨y,hy⟩:=Ideal.quotientInfToPiQuotient_surj hcop x
   obtain ⟨a,rfl⟩:=Lf y
   refine ⟨ox L a,?_⟩
   funext q
   exact Du hy q
 have hd:=LinearMap.finrank_le_finrank_of_surjective hsurj
 rw [Module.finrank_pi_fintype] at hd
 change (∑ q:T,lV k (R ⧸ J q))≤_ at hd
 rw [Finset.sum_coe_sort T (fun q=>lV k (R ⧸ J q))] at hd
 change (∑ q∈qs.filter (fun q=>J q ≠ ⊤),lV k (R ⧸ J q))≤_ at hd
 rw [Finset.sum_filter] at hd
 convert hd using 1
 symm
 apply yL rfl
 intro q _
 by_cases h:J q = ⊤
 · let:Subsingleton (R ⧸ J q) :=Ideal.Quotient.subsingleton_iff.mpr h
   have hzero :lV k (R ⧸ J q)=0:=Module.finrank_eq_zero_of_subsingleton k _
   simp only [hzero,ite_self]
 · simp [h]
abbrev cxl (s :n5) (I:aU lJ) :=
 lK (jY s) ⧸ I.map (Yx s)
abbrev bQy (s :n5) (I:aU lJ) :=
 pC (jY s) (cxl s I)
def Lx (s :n5) (I:aU lJ) :ℕ :=
 lV (jY s) (cxl s I)
theorem bKy (s :n5) (P Q:Jet) (S:qm (aU lJ))
   (hS:bQz P Q S) (ht:bbh s) (n:ℕ)
   (hB:by0 (Bu s P) (Bu s Q) n) :
   (∀ I∈S,bQy s I)∧(∑ I∈S,Lx s I)≤n:= by
 let L:=nX ({Bu s P,Bu s Q} : Set (lK (jY s)))
 let J (I:aU lJ) :=I.map (Yx s)
 let:pC (jY s) (lK (jY s) ⧸ L) :=hB.1
 have hcont (I:aU lJ) (hi:I∈S) :L≤J I:= by
   change nX ({Bu s P,Bu s Q} : Set (lK (jY s)))≤J I
   rw [Ideal.span_insert,sup_le_iff]
   exact ⟨(Fa _).mpr (Gr _ (hS I hi).2.2.1),
     (Fa _).mpr (Gr _ (hS I hi).2.2.2)⟩
 refine ⟨fun I hi=>G4
   (Gk (jY s) (hcont I hi)).toLinearMap
   (Te (hcont I hi)),?_⟩
 refine (gw4 L J S hcont (fun I hi=>(ht I (hS I hi).1).imp_right And.left) ?_)
   |>.trans hB.2
 intro I hi I' hi' hn hn' heq
 rw [← ((ht I (hS I hi).1).resolve_left hn).2,
   ← ((ht I' (hS I' hi').1).resolve_left hn').2,show I.map (Yx s)=I'.map (Yx s) from heq]
end
end aeE
end
section
set_option backward.isDefEq.respectTransparency false
namespace aeE
noncomputable section
open K1 cu gT
theorem go7:Yx .seed=Dk :=rfl
theorem eqg:Yx .Bo=CG:=rfl
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Sw:=c9 (Fin 2) aZ
private def bY (e :Fin 4 ≃ Fin 2 ⊕ Fin 2) :lJ ≃+* Sw :=
 ((vH FX e).trans
   (FU FX (Fin 2) (Fin 2))).toRingEquiv
private theorem cFo (e :Fin 4 ≃ Fin 2 ⊕ Fin 2) :
    (mD Sw vR).comp (bY e).toRingHom =
      qz (MvPolynomial.C.comp (mD FX aQ))
        (yl lI (fun i=>nq (ek i)) ∘ e) := by
  apply t4
  · intro c
    simp [bY]
    rfl
  · intro i
    rw [C9,zk,FV]
    change mD Sw vR
      (FU FX (Fin 2) (Fin 2)
        (vH FX e (lI i)))= _
    rw [Mz ,MvPolynomial.rename_X,Ml]
    cases e i <;> simp [ek]
private theorem cYG (e :Fin 4 ≃ Fin 2 ⊕ Fin 2)
   (I:aU lJ) (hI:I.IsPrime) :
   let f :=(mD Sw vR).comp (bY e).toRingHom
   I.map f = ⊤ ∨ (I.map f).IsPrime∧(I.map f).comap f=I:= by
 dsimp only
 let S:Submonoid Sw:=(ze aZ).map nq
 let J:=I.map (bY e).toRingHom
 rw [← vj]
 by_cases ht:J.map (mD Sw vR) = ⊤
 · exact Or.inl ht
 have hJ:J.IsPrime := by
   change (I.map (bY e :lJ →+* Sw)).IsPrime
   rw [Pv (bY e)]
   exact hI.comap _
 have hd:=(NI S vR J).mp ht
 refine Or.inr ⟨R9 S vR J hJ hd,?_⟩
 rw [← J4]
 have hcontract : (J.map (mD Sw vR)).comap (mD Sw vR)=J :=
   SW S vR hJ hd
 change ((J.map (mD Sw vR)).comap (mD Sw vR)).comap
   (bY e).toRingHom=I
 rw [hcontract]
 exact N0 _ (bY e).bijective
theorem ddq:bbh .seed := by
 intro I hI
 rw [go7]
 let e :Fin 4 ≃ Fin 2 ⊕ Fin 2 :=(finSumFinEquiv (m:=2) (n:=2)).symm.trans (Equiv.sumComm (Fin 2) (Fin 2))
 have h: (mD Sw vR).comp (bY e).toRingHom=Dk := by
   rw [cFo]
   apply t4
   · intro c
     simp [Dk]
   · intro i
     simp only [Dk,zk,FV]
     fin_cases i <;> rfl
 exact h ▸ cYG e I hI
theorem cWl:bbh .Bo:= by
 intro I hI
 rw [eqg]
 let e :Fin 4 ≃ Fin 2 ⊕ Fin 2 :=(finSumFinEquiv (m:=2) (n:=2)).symm
 have h: (mD Sw vR).comp (bY e).toRingHom=CG:= by
   rw [cFo]
   apply t4
   · intro c
     simp [CG]
   · intro i
     simp only [CG,zk,FV]
     fin_cases i <;> rfl
 exact h ▸ cYG e I hI
end
end aeE
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace aeE
noncomputable section
open cu gT pI YX

open scoped BigOperators
def c1 :Prop :=bbh .jU∧bbh .kK
def c2 :Prop :=
  ∀ (F:Type) [oq F] (P Q:lK F) (b j c k :ℕ),
    j≤b→k≤ c→bTo P Q →
    P.totalDegree≤b→P.degreeOf 1≤j→Q.totalDegree≤ c→Q.degreeOf 1≤k →
    by0 P Q (b*k+c*j - j*k)
def c3:Prop :=
  ∀ (F:Type) [oq F] (P Q:lK F) (u j v k :ℕ),
    bTo P Q →
    P.degreeOf 0≤u→P.degreeOf 1≤j→Q.degreeOf 0≤v→Q.degreeOf 1≤k →
    by0 P Q (u*k+v*j)
private theorem bKZ {F:Type} [oY F]
   (I:aU (c9 (Fin 4) F)) (J:aU (c9 (Fin 2) F))
   (e : (c9 (Fin 4) F ⧸ I) ≃ₐ[F] (c9 (Fin 2) F ⧸ J)) :
   (pC F (c9 (Fin 2) F ⧸ J) →
     pC F (c9 (Fin 4) F ⧸ I)) ∧
   lV F (c9 (Fin 4) F ⧸ I) =
     lV F (c9 (Fin 2) F ⧸ J) := by
 refine ⟨?_,e.toLinearEquiv.finrank_eq⟩
 intro h
 let:pC F (c9 (Fin 2) F ⧸ J) :=h
 exact G4 e.symm.toLinearEquiv.toLinearMap e.symm.surjective
private theorem gpb (I:aU lJ) :
 lV aQ (Y0 I)=Lx .seed I:=rfl
private theorem eH1 (I:aU lJ) :
  lV dV (ani I)=Lx .jU I:= by
 have h:=(bKZ (F:=dV) _ _ (bJ0 I)).2
 exact h
private theorem eAX (I:aU lJ) :
  lV dV (Ik I)=Lx .kK I:= by
 have h:=(bKZ (F:=dV) _ _ (bJf I)).2
 exact h
private theorem eqh (I:aU lJ) :
 lV aQ (Lj I)=Lx .Bo I:=rfl
private theorem a6j (I:aU lJ) (h:bQy .jU I) :
  pC dV (ani I) := by
 have hf :=(bKZ (F:=dV) _ _ (bJ0 I)).1
 exact hf h
private theorem bfE (I:aU lJ) (h:bQy .kK I) :
  pC dV (Ik I) := by
 have hf :=(bKZ (F:=dV) _ _ (bJf I)).1
 exact hf h
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :YX.c4 := by
 intro P Q hp s t hs ht hP hQ S hS
 have hcap (k :n5) (R:Jet) (d:p5) (hR:oU R d) :=fZc k R d hR
 have hseed :=bKy .seed P Q S hS ddq _
   (h2 (jY .seed) _ _ s.B s.J t.B t.J hs ht (bLE .seed ddq P Q hp)
     (hcap .seed P s hP).1 (hcap .seed P s hP).2
     (hcap .seed Q t hQ).1 (hcap .seed Q t hQ).2)
 have hord:=bKy .jU P Q S hS h1.1 _
   (h3 (jY .jU) _ _ s.U s.J t.U t.J (bLE .jU h1.1 P Q hp)
     (hcap .jU P s hP).1 (hcap .jU P s hP).2
     (hcap .jU Q t hQ).1 (hcap .jU Q t hQ).2)
 have hmix :=bKy .kK P Q S hS h1.2 _
   (h3 (jY .kK) _ _ s.U s.B t.U t.B (bLE .kK h1.2 P Q hp)
     (hcap .kK P s hP).1 (hcap .kK P s hP).2
     (hcap .kK Q t hQ).1 (hcap .kK Q t hQ).2)
 have hjcap (R:Jet) (d:p5) (hR:oU R d) :
     (Bu .Bo R).totalDegree≤d.U:=hcap .Bo R d hR
 have hj:by0 (Bu .Bo P) (Bu .Bo Q) (s.U*t.U) := by
   have h:=h2 (jY .Bo) _ _ s.U s.U t.U t.U p9 p9 (bLE .Bo cWl P Q hp)
     (hjcap P s hP) ((C4 _ _).trans (hjcap P s hP))
     (hjcap Q t hQ) ((C4 _ _).trans (hjcap Q t hQ))
   rw [xI t.U s.U,Nat.add_sub_cancel] at h
   exact h
 have hjets :=bKy .Bo P Q S hS cWl _ hj
 constructor
 · intro I hI
   exact ⟨hseed.1 I hI,a6j I (hord.1 I hI),bfE I (hmix.1 I hI),
     hjets.1 I hI⟩
 intro i
 fin_cases i
 · change (∑ I∈S,lV aQ (Y0 I))≤ s.B*t.J+t.B*s.J - s.J*t.J
   simpa only [gpb] using hseed.2
 · change (∑ I∈S,lV dV (ani I))≤ s.U*t.J+t.U*s.J
   simpa only [eH1] using hord.2
 · change (∑ I∈S,lV dV (Ik I))≤ s.U*t.B+t.U*s.B
   simpa only [eAX] using hmix.2
 · change (∑ I∈S,lV aQ (Lj I))≤ s.U*t.U
   simpa only [eqh] using hjets.2
end
end aeE
end
section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace cyW
noncomputable section
open cu gT pI aeE MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev bzm:=Fin 2 ⊕ Fin 4
private abbrev GD:=c9 (Fin 4) FX
private abbrev asV:=c9 (Fin 2) lJ
private abbrev Flat :=c9 bzm FX
private abbrev Target :=lK dV
private abbrev nest:Flat ≃ₐ[FX] asV:=FU FX (Fin 2) (Fin 4)
private def ic (op:Flat→Flat→Flat) (a b:FX) :Fin 4→Flat :=
 ![op (lI (.inr 0)) (C a*lI (.inl 0)*lI (.inr 1)),
   lI (.inr 1),
   op (lI (.inr 2)) (C b*lI (.inl 1)*lI (.inr 3)),
   lI (.inr 3)]
private def aJs (op:Flat→Flat→Flat) (a b:FX) :Flat →ₐ[FX] Flat :=
 t3 (yl (fun i=>lI (.inl i)) (ic op a b))
private def J6 (a b:FX) :Flat ≃ₐ[FX] Flat := by
 refine AlgEquiv.ofAlgHom (aJs (· - ·) a b) (aJs (· + ·) a b) ?_ ?_
 · apply wR
   rintro (i | i)
   · simp [aJs]
   · fin_cases i <;> simp [aJs,ic,vZ]
 · apply wR
   rintro (i | i)
   · simp [aJs]
   · fin_cases i <;> simp [aJs,ic,vZ]
private def indices :bzm ≃ bzm where
 toFun:=yl ![qU 0,qU 1] ![qU 2,wA 0,qU 3,wA 1]
 invFun:=yl ![qU 1,qU 3] ![wA 0,wA 1,qU 0,qU 2]
 left_inv := by rintro (i | i) <;> fin_cases i <;> rfl
 right_inv := by rintro (i | i) <;> fin_cases i <;> rfl
private def Wn:Flat ≃ₐ[FX] asV :=
 (vH FX indices).trans nest
private def bY (b:FX) :asV ≃+* asV :=
 ((nest.symm.trans (J6 1 b)).trans Wn).toRingEquiv
private def finish:Flat →+* Target :=
 (mD asV Target).comp Wn.toRingEquiv.toRingHom
private theorem eaE (i:bzm) :
  finish (lI i)=yl lI (fun j=>C (kz j)) (indices i) := by
 change mD asV Target (nest (vH FX indices (lI i)))= _
 rw [Mz ,rename_X,Ml]
 cases indices i <;> simp [kz]
private theorem cRZ (c:FX) :finish (C c)=C (mD FX dV c) := by
 change mD asV Target (nest (vH FX indices (C c)))= _
 rw [Mz ,rename_C,sumAlgEquiv_C_inl,Ml,map_C]
 rfl
private def lineMap (b:FX) :lJ →+* Target :=
 ((mD asV Target).comp (bY b).toRingHom).comp C
private theorem cX4 (b:FX) :
    lineMap b=qz (C.comp (mD FX dV))
      (![C (kz 2) - C (kz 0)*lI 0,lI 0,
         C (kz 3) - C (mD FX dV b)*C (kz 1)*lI 1,
         lI 1] :Fin 4→Target) := by
  apply t4
  · intro c
    change finish (J6 1 b (nest.symm (C (C c))))= _
    rw [sumAlgEquiv_symm_C_C]
    change finish (aJs (· - ·) 1 b (C c))= _
    rw [show aJs (· - ·) 1 b (C c)=C c by simp [vZ]]
    rw [cRZ,eval₂Hom_C,C9]
  · intro i
    change finish (J6 1 b (nest.symm (C (lI i))))= _
    rw [sumAlgEquiv_symm_C_X]
    change finish (aJs (· - ·) 1 b (lI (.inr i)))= _
    rw [aJs,PM,Sum.elim_inr,zk]
    fin_cases i <;> simp [ic,eaE,cRZ,indices]
private theorem eHY:lineMap 0=Yx .jU:= by
 change lineMap 0=qz (C.comp (mD FX dV))
  (aD .jU:Fin 4→Target)
 rw [cX4]
 apply oD (qz (C.comp (mD FX dV)))
 funext i
 fin_cases i <;> simp [aD,amL,aoA,an4] <;> rfl
private theorem eAV:lineMap 1=Yx .kK:= by
 change lineMap 1=qz (C.comp (mD FX dV))
  (aD .kK:Fin 4→Target)
 rw [cX4]
 apply oD (qz (C.comp (mD FX dV)))
 funext i
 fin_cases i <;> simp [aD,amL,aoA,an4]
private theorem aWu {R σ:Type} [oY R] (I:aU R) (hI:I.IsPrime) :
  (I.map (C:R →+* c9 σ R)).IsPrime := by
 let:I.IsPrime :=hI
 let q:c9 σ R →+* c9 σ (R ⧸ I) :=
  oz (ox I)
 have hq:p7 q=I.map C:= by
  dsimp only [q]
  rw [MvPolynomial.ker_map,Ideal.mk_ker]
 rw [← hq]
 exact Dz q
private theorem cYe (b:FX) (I:aU lJ) (hI:I.IsPrime) :
   I.map (lineMap b) = ⊤ ∨
     (I.map (lineMap b)).IsPrime∧(I.map (lineMap b)).comap (lineMap b)=I:= by
 let C₀:lJ →+* asV:=C
 let e :=bY b
 let L:=mD asV Target
 let E :=I.map C₀
 let J:=E.map e.toRingHom
 let S:Submonoid asV:=(ze GD).map C
 have hE :E.IsPrime :=aWu I hI
 have hEback :E.comap C₀=I:= by
   ext p
   constructor
   · intro hp
     change C p∈I.map C₀ at hp
     simpa using (MvPolynomial.mem_map_C_iff.mp hp 0)
   · exact Gr C₀
 have hJ:J.IsPrime := by
   change (E.map (e :asV →+* asV)).IsPrime
   rw [Pv e]
   exact hE.comap _
 have hmap :I.map (lineMap b)=J.map L:= by
   change I.map ((L.comp e.toRingHom).comp C₀)= _
   rw [← vj,← vj]
 rw [hmap]
 by_cases ht:J.map L = ⊤
 · exact Or.inl ht
 have hd:=(NI S Target J).mp ht
 refine Or.inr ⟨R9 S Target J hJ hd,?_⟩
 have hback : (J.map L).comap L=J :=
   SW S Target hJ hd
 change (J.map L).comap ((L.comp e.toRingHom).comp C₀)=I
 rw [← J4 ,← J4 ,hback]
 have heback :J.comap e.toRingHom=E :=N0 _ e.bijective
 rw [heback,hEback]
theorem proof :aeE.c1 := by
 constructor
 · intro I hI
   rw [← eHY]
   exact cYe 0 I hI
 · intro I hI
   rw [← eAV]
   exact cYe 1 I hI
end
end cyW
end
section
set_option backward.isDefEq.respectTransparency false
namespace aRY
noncomputable section
open cu gT XY
open scoped BigOperators
private def afQ (F:Type*) [oY F] (n:ℕ) :
   Polynomial (c9 (Fin n) F) ≃+* c9 (Fin (n+1)) F :=
 (EK F (Fin n)).symm.toRingEquiv.trans
   (vH F (finSuccEquivLast (n:=n)).symm).toRingEquiv
private theorem brx (F:Type*) [oY F] (n:ℕ) :
  afQ F n pU=lI (Fin.last n) := by
 change yo _ ((EK F (Fin n)).symm pU)= _
 simp
private theorem brw (F:Type*) [oY F] (n:ℕ)
   (a :c9 (Fin n) F) :
   afQ F n (qJ a)=yo Fin.castSucc a := by
 have h: (EK F (Fin n)).symm (qJ a) =
     MvPolynomial.rename some a := by
   change (Polynomial.aevalTower (yo some) (lI none))
     (qJ a)= _
   simp
 change yo _
   ((EK F (Fin n)).symm (qJ a))= _
 have he : (finSuccEquivLast (n:=n)).symm ∘ some=Fin.castSucc:= by
   funext i
   simp
 rw [h,MvPolynomial.rename_rename,he]
private theorem castLE_succ (n:ℕ) :
  (Fin.castLE (t5 n) :Fin n→Fin (n+1))=Fin.castSucc:= by
 funext i
 apply Fin.ext
 rfl
private def S5:Jet ≃+* Ambient :=
 (Polynomial.mapEquiv (afQ FX 2)).trans (afQ FX 3)
private theorem beL (P:Jet) :S5 P=iJ P:= by
  have hroot : (afQ FX 2).toRingHom=A7:= by
    apply z8
    · intro a
      simpa [A7,pZ,castLE_succ] using brw FX 2 a
    · simpa [A7,Gi] using brx FX 2
  have hjet:S5.toRingHom=iJ:= by
    apply z8
    · intro a
      change afQ FX 3 ((qJ a).map (afQ FX 2).toRingHom) =
        iJ (qJ a)
      rw [Polynomial.map_C,brw,hroot]
      simp [iJ,oi,castLE_succ]
    · change afQ FX 3 (Polynomial.X.map (afQ FX 2).toRingHom) =
        iJ pU
      rw [Polynomial.map_X,brx]
      simp [iJ]
  exact v8 hjet P
private theorem ezT (F:Type*) [oq F] (n:ℕ)
    (m:aU (c9 (Fin n) F)) [m.IsMaximal] :m.height=n:= by
  induction n with
  | zero =>
    have hd:oy (c9 (Fin 0) F)=0:= by
      rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.isEmptyRingEquiv F (Fin 0)),
        IU]
    have h:=S1 (I:=m)
    rw [hd] at h
    exact qM (by exact_mod_cast h) (by simp)
  | succ n ih =>
    let e :=(z9 F n).toRingEquiv
    let M:=m.map e
    have :M.IsMaximal:=Ideal.map_isMaximal_of_equiv e
    let p:=M.comap (qJ:c9 (Fin n) F →+* _)
    have :p.IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing M
    have :M.LiesOver p:=⟨rfl⟩
    rw [← e.height_map m,Polynomial.height_eq_height_add_one p M,ih p]
    simp
private theorem epk {R:Type*} [oY R] [Au R]
   [IsJacobsonRing R] {J I:aU R} (hI:I∈J.minimalPrimes) :
   ∃ m:aU R,m.IsMaximal∧I≤ m ∧
     ∀ q∈J.minimalPrimes,q≤ m→q=I:= by
 classical
 let fmin:=J.finite_minimalPrimes_of_isNoetherianRing
 let s :=fmin.toFinset.erase I
 have hs (q:s) : ∃ x :R,x∈q.val∧x∉I:= by
   obtain ⟨hne,hq⟩:=Finset.mem_erase.mp q.property
   have hmin:q.val∈J.minimalPrimes :=fmin.mem_toFinset.mp hq
   by_contra! h
   exact hne (qM h (hI.2 hmin.1 h))
 choose f hf hfi using hs
 let x :R := ∏ q:s,f q
 have :I.IsPrime :=hI.isPrime
 have hxI:x∉I:= by
   intro hx
   obtain ⟨q,_,hq⟩:=Ideal.IsPrime.prod_mem_iff.mp hx
   exact hfi q hq
 have hrad:I.jacobson=I:=(isJacobsonRing_iff_prime_eq.mp y5) _ hI.isPrime
 have hm : ∃ m:aU R,m.IsMaximal∧I≤ m∧x∉m:= by
   by_contra! h
   apply hxI
   rw [← hrad,Ideal.jacobson,Ideal.mem_sInf]
   intro m hm
   exact h m hm.2 hm.1
 obtain ⟨m,hm,hIm,hxm⟩:=hm
 refine ⟨m,hm,hIm,fun q hq hqm => ?_⟩
 by_contra hne
 let i:s :=⟨q,Finset.mem_erase.mpr ⟨hne,fmin.mem_toFinset.mpr hq⟩⟩
 exact hxm (hqm (q.mem_of_dvd (Finset.dvd_prod_of_mem f (In i)) (hf i)))
private theorem eQy {a b:lJ} {I:aU lJ}
    (hI:I∈(nX {a,b}).minimalPrimes) :
    2≤ oy (gk I) := by
  classical
  let J:aU Ambient:=nX {a,b}
  obtain ⟨m,hm,hIm,honly⟩:=epk hI
  have :m.IsPrime :=hm.isPrime
  have hJm:J≤ m:=hI.le.trans hIm
  let M:aU (lJ ⧸ J) :=m.map (ox J)
  let m' : xu (lJ ⧸ J) :=
    ⟨M,Ideal.isPrime_map_quotientMk_of_isPrime hJm⟩
  have henc: ({a,b} : Set lJ).encard≤2 := by
    simpa [Ts] using Set.encard_insert_le ({b} : Set lJ) a
  have hmheight:m.height=(4 :ℕ∞) := by
    simpa only [yU] using ezT FX 4 m
  have hquot: (4 :ℕ∞)≤Ideal.height (R:=lJ ⧸ J) M+2 := by
    rw [← hmheight]
    exact (Ideal.height_le_height_add_encard_of_subset {a,b}
      (show ({a,b} : Set lJ)⊆m from Ideal.span_le.mp hJm)).trans
        (IT p9 henc)
  have htall:1<HZ m' := by
    rw [← PrimeSpectrum.height_eq_orderHeight (R:=lJ ⧸ J) m']
    by_contra! h
    have hbad: (4 :ℕ∞)≤1+2 :=hquot.trans (IT h p9)
    exact (by decide : ¬ (4 :ℕ∞)≤1+2) hbad
  obtain ⟨q,p,hpq,hqm⟩:=Order.one_lt_height_iff.mp htall
  let e :=J.primeSpectrumQuotientOrderIsoZeroLocus
  have hm' : (e m').val.asIdeal=m:= by
    change (m.map (ox J)).comap (ox J)=m
    rw [Ar _ Lf ,
      ← Pr,J.mk_ker,
      sup_eq_left.mpr hJm]
  have habove (r :xu (lJ ⧸ J)) (hr :r≤ m') :
      I≤(e r).val.asIdeal:= by
    have hrm: (e r).val.asIdeal≤ m:=hm' ▸ e.monotone hr
    have : (e r).val.asIdeal.IsPrime :=(e r).val.isPrime
    obtain ⟨u,hu,hule⟩:=Iw
      (show J≤(e r).val.asIdeal from (e r).property)
    exact honly u hu (hule.trans hrm) ▸ hule
  let liftPrime (r :xu (lJ ⧸ J)) (hr :r≤ m') :
      xu (gk I) :=
    I.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨(e r).val,habove r hr⟩
  have hmono {r t:xu (lJ ⧸ J)} {hr :r≤ m'} {ht:t≤ m'}
      (hlt:r<t) :liftPrime r hr<liftPrime t ht :=
    I.primeSpectrumQuotientOrderIsoZeroLocus.symm.strictMono (e.strictMono hlt)
  let p₀:=liftPrime p (hpq.trans hqm).le
  let p₁:=liftPrime q hqm.le
  let p₂:=liftPrime m' p9
  have h₀₁:p₀<p₁:=hmono (hr :=(hpq.trans hqm).le) (ht:=hqm.le) hpq
  have h₁₂:p₁<p₂:=hmono (hr :=hqm.le) (ht:=p9) hqm
  have htall' : 1<HZ p₂ :=
    Order.one_lt_height_iff.mpr ⟨p₁,p₀,h₀₁,h₁₂⟩
  have htwo: (2 :ℕ∞)≤HZ p₂:= by
    simpa only [Ts] using (ENat.add_one_le_iff ENat.one_ne_top).mpr htall'
  exact (WithBot.coe_le_coe.mpr htwo).trans (Order.height_le_krullDim p₂)
private theorem eQz {a b:lJ} (ha :a≠0)
    (hcop : ∀ D:lJ,oZ D→D ∣a → ¬ D ∣b)
    {I:aU lJ} [I.IsPrime] (haI:a∈I) (hbI:b∈I) :
    oy (gk I)≤2 := by
  have hI₀:I ≠ ⊥ := fun h=>ha (by simpa [h] using haI)
  obtain ⟨D,hD,hprime⟩:=Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹I.IsPrime› hI₀
  let T:aU Ambient:=nX {D}
  have :T.IsPrime :=(TI hprime.ne_zero).mpr hprime
  have hT₀: (⊥ : aU lJ)<T :=
    bot_lt_iff_ne_bot.mpr (fun h=>hprime.ne_zero (Ideal.span_singleton_eq_bot.mp h))
  have hTI:T<I:= by
    refine lt_of_le_of_ne ((Fa I).mpr hD) ?_
    intro he
    exact hcop D hprime.irreducible
      (Ideal.mem_span_singleton.mp (he ▸ haI:a∈T))
      (Ideal.mem_span_singleton.mp (he ▸ hbI:b∈T))
  have hd:oy lJ=4 := by simp [lJ,IU]
  have hbound:oy (gk I)+2≤4 := by
    calc
      _=(oy (gk I)+1)+1 := by rw [add_assoc]; norm_num
      _≤ oy (gk T)+1 :=
        IT (Rm hTI) p9
      _≤ oy (lJ ⧸ (⊥ : aU lJ)) :=
        Rm hT₀
      _=4 :=(RingEquiv.quotientBot lJ).ringKrullDim.trans hd
  exact (ENat.WithBot.add_le_add_natCast_right_iff (c:=2)).mp
    (by simpa only [yU,show (2 :WithBot ℕ∞)+2=4 by decide] using hbound)
theorem proof :YX.c3:= by
 classical
 intro P Q h
 let a :=iJ P
 let b:=iJ Q
 have ha :a≠0:= by
   rw [show a=S5 P from (beL P).symm]
   exact t7 S5 S5.injective |>.mpr h.left_ne
 have hcop (D:lJ) (hD:oZ D) (hDa :D ∣a) : ¬ D ∣b:= by
   obtain ⟨d,rfl⟩:=S5.surjective D
   rw [show a=S5 P from (beL P).symm,G8] at hDa
   rw [show b=S5 Q from (beL Q).symm,G8]
   exact h.no_common d ((MulEquiv.irreducible_iff S5).mp hD) hDa
 let J:aU Ambient:=nX {a,b}
 let fmin:=J.finite_minimalPrimes_of_isNoetherianRing
 let S:=fmin.toFinset
 refine ⟨S,?_,?_⟩
 · intro I hI
   have hmin:I∈J.minimalPrimes :=fmin.mem_toFinset.mp hI
   have :I.IsPrime :=hmin.isPrime
   have haI:a∈I:=hmin.le (vw (by simp))
   have hbI:b∈I:=hmin.le (vw (by simp))
   exact ⟨hmin.isPrime,qM (eQz ha hcop haI hbI)
     (eQy hmin),haI,hbI⟩
 · intro z R hP hQ
   let e :=aci z R
   have : (p7 e).IsPrime :=Dz e
   have hJ:J≤p7 e := by
     refine Ideal.span_le.mpr ?_
     intro g hg
     simp only [Pk,LR] at hg
     rcases hg with rfl | rfl
     · exact (aNB z R P).trans hP
     · exact (aNB z R Q).trans hQ
   obtain ⟨I,hI,hIe⟩:=Iw hJ
   exact ⟨I,fmin.mem_toFinset.mpr hI,hIe⟩
end
end aRY
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace atc
noncomputable section
open cu pI XY Polynomial
private def aOh:Jet →+* c9 (Fin 2) aZ :=
 (z9 aZ 1).symm.toRingHom.comp
   (Kl (Et aZ (Fin 1)).symm.toRingHom)
private theorem bXN (P:Jet) (d:Fin 2 →₀ ℕ) :
  (aOh P).coeff d=(P.coeff (d 0)).coeff (d 1) := by
 let Q:=P.map (Et aZ (Fin 1)).symm.toRingHom
 change ((z9 aZ 1).symm Q).coeff d= _
 rw [← Finsupp.cons_tail d,← MvPolynomial.finSuccEquiv_coeff_coeff,
  AlgEquiv.apply_symm_apply]
 simp only [Q,Polynomial.coeff_map]
 change ((Et aZ (Fin 1)).symm (P.coeff (d 0))).coeff d.tail= _
 rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
 rfl
private theorem b6M:pQ aOh :=
 (z9 aZ 1).symm.injective.comp
   (Polynomial.map_injective _ (Et aZ (Fin 1)).symm.injective)
private def aki:Jet →+* c9 (Fin 2) (c9 (Fin 2) FX) :=
 (Aa FX (Fin 2) (Fin 2)).toRingHom.comp aOh
private theorem cGl (P:Jet) (e d:Fin 2 →₀ ℕ) :
  ((aki P).coeff e).coeff d=((P.coeff (d 0)).coeff (d 1)).coeff e := by
 rw [← bXN]
 change ((Aa FX (Fin 2) (Fin 2) (aOh P)).coeff e).coeff d =
  ((aOh P).coeff d).coeff e
 simp [Aa ,AddMonoidAlgebra.commAlgEquiv,
  AddMonoidAlgebra.curryAlgEquiv,AddMonoidAlgebra.curryRingEquiv,
  AddMonoidAlgebra.curryAddEquiv,AddMonoidAlgebra.coeff_domCongr]
private theorem dc1 :pQ aki :=
 (Aa FX (Fin 2) (Fin 2)).injective.comp b6M
def jetDegree (P:Jet) :ℕ:=(aOh P).totalDegree
def gY (P:Jet) :ℕ:=(aki P).totalDegree
theorem bHW {P Q:Jet} (hP:P≠0) (hQ:Q≠0) :
  jetDegree (P*Q)=jetDegree P+jetDegree Q:= by
 unfold jetDegree
 rw [pL,UY
  ((t7 _ b6M).mpr hP)
  ((t7 _ b6M).mpr hQ)]
theorem acG {P Q:Jet} (hP:P≠0) (hQ:Q≠0) :
  gY (P*Q)=gY P+gY Q:= by
 unfold gY
 rw [pL,UY
  ((t7 _ dc1).mpr hP)
  ((t7 _ dc1).mpr hQ)]
private theorem aXY (d:Fin 2 →₀ ℕ) : (d.sum fun _ e=>e)=d 1+d 0:= by
 rw [Finsupp.sum_fintype _ _ (fun _=>rfl),Fin.sum_univ_two,JW]
theorem jetDegree_le (P:Jet) (b:ℕ) :
   jetDegree P≤b ↔ ∀ j i,(P.coeff j).coeff i≠0→i+j≤b:= by
 constructor
 · intro h j i hji
   let d:Fin 2 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![j,i]
   have hd:d∈(aOh P).support := by
    rw [S2 ,bXN]
    exact hji
   have hsum:=(sS hd).trans h
   rw [aXY] at hsum
   exact hsum
 · intro h
   apply u5
   intro d hd
   rw [aXY]
   rw [S2 ,bXN] at hd
   exact h _ _ hd
theorem bv9 (P:Jet) (u:ℕ) :
   gY P≤u ↔ ∀ j i,((P.coeff j).coeff i).totalDegree≤u:= by
 constructor
 · intro h j i
   apply u5
   intro e he
   apply (sS (p:=aki P) ?_).trans h
   apply MvPolynomial.mem_support_iff.mpr
   intro hz
   let d:Fin 2 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![j,i]
   have hzero :=oD (fun a :c9 (Fin 2) FX=>a.coeff d) hz
   rw [cGl,Qx ,Finsupp.zero_apply] at hzero
   exact (MvPolynomial.mem_support_iff.mp he) hzero
 · intro h
   apply u5
   intro e he
   obtain ⟨d,hd⟩ : ∃ d,((aki P).coeff e).coeff d≠0:= by
    by_contra! hz
    apply MvPolynomial.mem_support_iff.mp he
    ext d
    rw [hz,Qx]
    rfl
   rw [cGl] at hd
   exact (sS (MvPolynomial.mem_support_iff.mpr hd)).trans (h _ _)
theorem aW4 (P:Jet) (s :p5) :
   oU P s↔jetDegree P≤ s.B∧P.natDegree≤ s.J∧gY P≤ s.U:= by
 rw [jetDegree_le,bv9]
 constructor
 · intro h
   refine ⟨fun j i hji=>(h j i hji).1,natDegree_le_iff_coeff_eq_zero.mpr ?_,?_⟩
   · intro j hj
     apply Dv
     intro i
     rw [coeff_zero]
     by_contra hi
     exact (Nat.not_le_of_lt hj) (h j i hi).2.1
   · intro j i
     by_cases hz : (P.coeff j).coeff i=0
     · simp [hz]
     · exact (h j i hz).2.2
 · rintro ⟨hB,hJ,hU⟩ j i hi
   have hj:P.coeff j≠0:= by intro hz; simp [hz] at hi
   exact ⟨hB j i hi,(II hj).trans hJ,hU j i⟩
theorem bri (f :nI) :jetDegree (C f)=f.natDegree := by
  apply qM
  · apply (jetDegree_le _ _).mpr
    intro j i hi
    cases j with
    | zero=>simpa using le_natDegree_of_ne_zero (by simpa using hi:f.coeff i≠0)
    | succ j=>simp at hi
  · by_cases hf :f=0
    · simp [hf]
    · have hc: ((C f :Jet).coeff 0).coeff f.natDegree≠0:= by
        simpa [u8] using leadingCoeff_ne_zero.mpr hf
      simpa using (jetDegree_le _ _).mp p9 0 f.natDegree hc
theorem bg3 (f :nI) :gY (C f)=My f := by
 apply qM
 · apply (bv9 _ _).mpr
   intro j i
   cases j with
   | zero =>
     simp only [coeff_C_zero]
     by_cases hi:f.coeff i=0
     · simp [hi]
     · exact Finset.le_sup (f := fun y=>(f.coeff y).totalDegree) (mem_support_iff.mpr hi)
   | succ j=>simp
 · apply u5
   intro i _
   simpa using (bv9 (C f) _).mp p9 0 i
theorem bNz (a :aZ) :gY (C (C a))=a.totalDegree := by
 rw [bg3]
 by_cases ha :a=0
 · simp [ha,My]
 · simp [My,support_C ha]
end
end atc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace atc
noncomputable section
open cu gT pI XY Polynomial
theorem cN1 (P:Jet) (hP:P≠0) :
   ∃ (a :aZ) (R:Jet),P=C (C a)*R ∧
     ∀ b:aZ,C (C b)∣R→ wB b:= by
 classical
 revert hP
 refine (SD (α:=Jet)).induction
   (C:= fun P=>P≠0 → ∃ (a :aZ) (R:Jet),P=C (C a)*R ∧
     ∀ b:aZ,C (C b)∣R→ wB b) P ?_
 intro P ih hP
 by_cases h : ∃ b:aZ,¬ wB b∧C (C b)∣P
 · obtain ⟨b,hb,Q,hQ⟩:=h
   have hQ0:Q≠0:= fun hz=>hP (by simpa [hz] using hQ)
   have hlt:DvdNotUnit Q P :=
     ⟨hQ0,C (C b),fun hu=>hb (isUnit_C.mp (isUnit_C.mp hu)),hQ.trans (oj _ _)⟩
   obtain ⟨a,R,hR,hstrip⟩:=ih Q hlt hQ0
   exact ⟨b*a,R,by rw [C_mul,C_mul,vh,← hR,← hQ],hstrip⟩
 · exact ⟨1,P,by simp,fun b hb=> by by_contra hu; exact h ⟨b,hu,hb⟩⟩
private theorem cNA (D:Jet) (h : ¬ alm D) : ∃ G:tK,D =Gw G:= by
 let e :aZ →+* FX:=zc (fun _=>0)
 refine ⟨D.map (Kl e),?_⟩
 apply Dv
 intro j
 apply Dv
 intro i
 simp only [Gw,qQ.Ng,Polynomial.coe_mapRingHom,coeff_map]
 have hzero : ((D.coeff j).coeff i).totalDegree=0 :=
  NZ (fun hp=>h ⟨j,i,hp⟩)
 obtain hc:=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
 rw [hc]
 simp [e]
theorem cN0 (P Q:Jet) (hP:P≠0) (hQ:Q≠0)
    (hseed : ∀ b:aZ,C (C b)∣P→ wB b)
    (hord : ∀ D:Jet,oZ D→D ∣P→D ∣Q→D.natDegree=0) :
    ∃ (M:x7 nI) (L T:Jet),P=C M.prod*L∧Q=C M.prod*T ∧
      ag6 L T ∧ ∀ f∈M,oZ f∧0<f.natDegree := by
  classical
  revert Q
  revert hP hseed
  refine (SD (α:=Jet)).induction
    (C:= fun P=>P≠0→(∀ b:aZ,C (C b)∣P→ wB b) →
      ∀ Q:Jet,Q≠0 →
      (∀ D:Jet,oZ D→D ∣P→D ∣Q→D.natDegree=0) →
      ∃ (M:x7 nI) (L T:Jet),P=C M.prod*L∧Q=C M.prod*T ∧
        ag6 L T ∧ ∀ f∈M,oZ f∧0<f.natDegree) P ?_
  intro P ih hP hseed Q hQ hord
  by_cases h : ∃ D:Jet,oZ D ∧D ∣P∧D ∣Q
  · obtain ⟨D,hD,hDP,hDQ⟩:=h
    let f :=D.coeff 0
    have hd:D =C f :=EP (hord D hD hDP hDQ)
    have hf :oZ f := by
      rw [hd] at hD
      refine ⟨fun hu=>hD.not_isUnit (isUnit_C.mpr hu),?_⟩
      intro a b hab
      have he : (C f :Jet)=C a*C b:= by rw [← C_mul,← hab]
      exact (hD.isUnit_or_isUnit he).imp isUnit_C.mp isUnit_C.mp
    have hfpos :0<f.natDegree := by
      by_contra! hzero
      have hc:=EP (Qw hzero)
      have hdiv :C f∣P:=hd ▸ hDP
      rw [hc] at hdiv
      apply hf.not_isUnit
      rw [hc]
      exact isUnit_C.mpr (hseed _ hdiv)
    obtain ⟨P',hP'⟩:=hDP
    obtain ⟨Q',hQ'⟩:=hDQ
    have hP'0:P' ≠ 0:= fun hz=>hP (by simpa [hz] using hP')
    have hQ'0:Q' ≠ 0:= fun hz=>hQ (by simpa [hz] using hQ')
    have hPdiv :P' ∣ P:=⟨D,hP'.trans (oj _ _)⟩
    have hQdiv :Q' ∣ Q:=⟨D,hQ'.trans (oj _ _)⟩
    have hlt:DvdNotUnit P' P:=⟨hP'0,D,hD.not_isUnit,hP'.trans (oj _ _)⟩
    obtain ⟨M,L,T,hL,hT,hproper,hM⟩ :=
      ih P' hlt hP'0 (fun b hb=>hseed b (hb.trans hPdiv)) Q' hQ'0
        (fun D hD hdP hdQ=>hord D hD (hdP.trans hPdiv) (hdQ.trans hQdiv))
    refine ⟨f ::ₘ M,L,T,?_,?_,hproper,?_⟩
    · rw [hP',hd,Un,C_mul,vh,← hL]
    · rw [hQ',hd,Un,C_mul,vh,← hT]
    · intro g hg
      rcases Multiset.mem_cons.mp hg with rfl | hg
      · exact ⟨hf,hfpos⟩
      · exact hM g hg
  · exact ⟨0,P,Q,by simp,by simp,⟨hP,hQ,fun D hD hdP hdQ=>h ⟨D,hD,hdP,hdQ⟩⟩,by simp⟩
end
end atc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace atc
noncomputable section
open K1 cu gT pI YX XY Polynomial
open scoped BigOperators
private theorem b05 {P R:Jet} {s :p5} (hP:P≠0)
  (h:oU P s) (hd:R∣P) :oU R s := by
 obtain ⟨V,hV⟩:=hd
 have hmul :R*V≠0:=hV ▸ hP
 obtain ⟨hb,hj,hu⟩:=(aW4 P s).mp h
 rw [hV,bHW (Gn hmul) (G6 hmul)] at hb
 rw [hV,Bf (Gn hmul) (G6 hmul)] at hj
 rw [hV,acG (Gn hmul) (G6 hmul)] at hu
 exact (aW4 R s).mpr ⟨by omega,by omega,by omega⟩
private theorem dcF {P:Jet} {a :aZ} {s :p5}
  (hP:P≠0) (h:oU P s) (hd:C (C a)∣P) :a.totalDegree≤ s.U:= by
 have hu:=((aW4 _ _).mp (b05 hP h hd)).2.2
 rwa [bNz] at hu
private theorem b4x {F:nI} {R:Jet} {s :p5}
   (hF:F≠0) (hR:R≠0) (h:oU (C F*R) s) :
   My F≤ s.U∧F.natDegree≤ s.B ∧
     oU R (aL7 s (My F) F.natDegree) := by
 have hC: (C F:Jet)≠0:=C_ne_zero.mpr hF
 obtain ⟨hB,hJ,hU⟩:=(aW4 _ _).mp h
 rw [bHW hC hR,bri] at hB
 rw [Bf hC hR,natDegree_C,v9] at hJ
 rw [acG hC hR,bg3] at hU
 have hJR:R.natDegree≤jetDegree R:= by
   have hv :=leadingCoeff_ne_zero.mpr hR
   have hc: (R.coeff R.natDegree).coeff R.leadingCoeff.natDegree≠0:= by
     rw [u8 ,u8]
     exact leadingCoeff_ne_zero.mpr hv
   have htop:=(jetDegree_le _ _).mp p9 _ _ hc
   omega
 refine ⟨by omega,by omega,(aW4 _ _).mpr ?_⟩
 change jetDegree R≤ s.B-F.natDegree ∧
   R.natDegree≤ min s.J (s.B-F.natDegree)∧gY R≤ s.U-My F
 exact ⟨by omega,le_min hJ (by omega),by omega⟩
private theorem b9B (M:x7 nI) (hM : ∀ f∈M,f≠0) :
  M.prod≠0 :=
 Multiset.prod_ne_zero (fun he=>hM 0 he rfl)
private theorem b01 [DecidableEq nI] (d:nI→ℕ) (h1 :d 1=0)
   (hmul : ∀ {f g},f≠0→ g≠0→d (f * g)=d f+d g)
   (M:x7 nI) (hM : ∀ f∈M,f≠0) :
   (∑ f∈M.toFinset,d f)≤d M.prod:= by
 induction M using Multiset.induction_on with
 | empty=>simp [h1]
 | cons f M ih =>
   have hrest : ∀ g∈M,g≠0:= fun g hg=>hM g (Multiset.mem_cons_of_mem hg)
   rw [Multiset.prod_cons,hmul (hM f (by simp)) (b9B M hrest),
     Multiset.toFinset_cons]
   by_cases hf :f∈M.toFinset
   · rw [Finset.insert_eq_of_mem hf]
     exact (ih hrest).trans (Nat.le_add_left _ _)
   · rw [Nq hf]
     exact zS (ih hrest) _
private theorem dde {f g:nI} (hf :f≠0) (hg:g≠0) :
  My (f * g)=My f+My g:= by
 simpa only [← bg3,C_mul] using
  acG (C_ne_zero.mpr hf) (C_ne_zero.mpr hg)
private theorem cBv {M:x7 nI} {z :K} {S:K[X]}
  (h:yq M.prod z S=0) : ∃ f∈M,yq f z S=0:= by
 let e :=eval₂RingHom (qD z) (kr S)
 change e M.prod=0 at h
 rw [map_multiset_prod] at h
 exact Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h)
private theorem b6D (z :K) (S:K[X]) (P Q:Jet) :
   rD (P*Q) z S=rD P z S*rD Q z S :=
 (vf z S).map_mul P Q
private theorem b6E (z :K) (S:K[X]) (f :nI) :
  rD (C f) z S=yq f z S:= by
 simp [rD,yq]
end
end atc
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Mc
open K1 Polynomial
open gR ProximityPrize.Benchmark
private theorem cXI {G:kB[X]} {U V:nC} (hG:G≠0)
    (hU:G∣sZ U) (hV:G∣sZ V) :
    ∃ D:nC,D ≠0∧G.natDegree≤D.natDegree∧D ∣U∧D ∣V:= by
  let φ:K[X] →+* kB:=mD K[X] kB
  have hφ:pQ φ:=vi K[X] kB
  let Q:nC:=IsLocalization.integerNormalization (ze K[X]) G
  let D:= Q.primPart
  obtain ⟨a,ha,hQ⟩:=IsLocalization.integerNormalization_spec (ze K[X]) G
  have ha0:a≠0:=nonZeroDivisors.ne_zero ha
  have hscale :C (φ Q.content)*D.map φ=C (φ a)*G:= by
    calc
      C (φ Q.content)*D.map φ= Q.map φ:= by
        rw [← Polynomial.map_C,← Pj,← Q.eq_C_content_mul_primPart]
      _=C (φ a)*G:= by
        simpa only [Algebra.smul_def,Polynomial.algebraMap_apply] using hQ
  have hscale0:C (φ a)*G≠0 :=
    GR (C_ne_zero.mpr (fun hz=>ha0 (hφ (hz.trans (th φ).symm)))) hG
  have hDmap :D.map φ≠0:= by
    intro hz
    exact hscale0 (by rw [← hscale,hz,mul_zero])
  have hcontent:φ Q.content≠0:= by
    intro hz
    exact hscale0 (by rw [← hscale,hz,th,zero_mul])
  have hD:D ≠0:= fun hz=>hDmap (by rw [hz,Re])
  have hGtoD:G∣D.map φ:= by
    apply (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcontent)).dvd_mul_left.mp
    rw [hscale]
    exact dvd_mul_left _ _
  have hDtoG:D.map φ∣G:= by
    have ha' : φ a≠0:= fun hz=>ha0 (hφ (hz.trans (th φ).symm))
    apply (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha')).dvd_mul_left.mp
    rw [← hscale]
    exact dvd_mul_left _ _
  have hdeg:=Ee hGtoD hDmap
  rw [natDegree_map_eq_of_injective hφ] at hdeg
  exact ⟨D,hD,hdeg,
    Q.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hDtoG.trans hU),
    Q.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hDtoG.trans hV)⟩
private theorem cqo {D P A:nC} {γ:K} (hD:D ≠0)
   (hP:P=D *A) (hγ:vn P γ≠0) :
   vn P γ=vn D γ*vn A γ ∧
     (vn P γ).natDegree+D.natDegree≤P.natDegree+(vn D γ).natDegree := by
 have heq :vn P γ=vn D γ*vn A γ:= by rw [hP,vn,Pj]; rfl
 have hDγ:vn D γ≠0:= by
   intro hz
   exact hγ (by rw [heq,hz,zero_mul])
 have hAγ:vn A γ≠0:= by
   intro hz
   exact hγ (by rw [heq,hz,mul_zero])
 have hA:A≠0:= fun hz=>hAγ (by rw [hz,vn,Re])
 refine ⟨heq,?_⟩
 have hdeg: (vn A γ).natDegree≤A.natDegree :=natDegree_map_le
 rw [heq,Bf hDγ hAγ,hP,Bf hD hA]
 omega
private theorem a3F (P:nC) (γ x :K) :
  (vn P γ).eval x=(P.eval (C x)).eval γ:= by
 simpa only [vn,coe_evalRingHom,G0] using
  (Polynomial.eval_map_apply (evalRingHom γ) (C x) (p:=P))
private theorem c8U {F ι:Type} [oq F] [Fintype ι]
  [DecidableEq ι] (x :ι→F) (hx :pQ x) (errors fixed:qm ι) (D:F[X])
  (hD:D ∣mL x errors) (hdeg:fixed.card<D.natDegree) :
  ∃ i∉fixed,D.eval (x i)=0:= by
 classical
 let S:=Finset.univ.filter (fun i:ι=>D.eval (x i)=0)
 have hcard:D.natDegree=S.card:=Principal.cK0 x hx errors D hD
 have hNot : ¬ S⊆fixed:= fun h=> by
  have :=Np h
  omega
 obtain ⟨i,hiS,hiFixed⟩:=Finset.not_subset.mp hNot
 exact ⟨i,hiFixed,(Finset.mem_filter.mp hiS).2⟩
private theorem cHb {F ι:Type} [oq F] [Fintype ι]
   (U V:ι→F[X]) (H :ℕ) (Γ:qm F)
   (hU : ∀ i,(U i).natDegree≤H) (hV : ∀ i,(V i).natDegree≤H)
   (hNew : ∀ γ∈Γ,∃ i,¬ (U i=0∧V i=0)∧(U i).eval γ=0∧(V i).eval γ=0) :
   Γ.card≤Fintype.card ι*H := by
 classical
 let Q (i:ι) :=if U i=0 then V i else U i
 have hCover :Γ⊆(Finset.univ :qm ι).biUnion (fun i=>(Q i).roots.toFinset) := by
   intro γ hγ
   obtain ⟨i,hNZ,hu,hv⟩:=hNew γ hγ
   refine Finset.mem_biUnion.mpr ⟨i,In _,?_⟩
   rw [Multiset.mem_toFinset]
   by_cases h:U i=0
   · rw [show Q i=V i by simp [Q,h]]
     exact (mem_roots (fun hz=>hNZ ⟨h,hz⟩)).mpr hv
   · rw [show Q i=U i by simp [Q,h]]
     exact (mem_roots h).mpr hu
 refine (Np hCover).trans
   ((Finset.card_biUnion_le_card_mul _ _ H ?_).trans_eq (by rw [Finset.card_univ]))
 intro i _
 refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
 change (if U i=0 then V i else U i).natDegree≤H
 split_ifs
 · exact hV i
 · exact hU i
end Mc
end
section
namespace lB
noncomputable section
open Polynomial MvPolynomial aR Ex dN
theorem aJY {R S:Type*} [xm R] [xm S]
  (w:Fin 4→ℕ) {P:c9 (Fin 4) R} {Q:c9 (Fin 4) S}
  (h:P.support⊆Q.support) :
  P.weightedTotalDegree w≤Q.weightedTotalDegree w :=
 Finset.sup_mono h
theorem Po {R:Type*} [xm R] (w:Fin 4→ℕ)
  (a :R) (P:c9 (Fin 4) R) :
  (nq a*P).weightedTotalDegree w≤P.weightedTotalDegree w:= by
 simpa only [weightedTotalDegree_C,v9] using
  weightedTotalDegree_mul_le w (nq a) P
theorem abx {R:Type*} [xm R] (w:Fin 4→ℕ) (i:Fin 4) :
  (lI i:c9 (Fin 4) R).weightedTotalDegree w≤w i :=
 mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp (X_mem_restrictWeightedDegree _ _ _ p9)
theorem TaylorChart.aWC (C:TaylorChart) {h:cy} (hC:C.dM h) (a :agy) :
    yy (C.pullback a) h:= by
  classical
  have hw (w:Fin 4→ℕ) (d:ℕ) (hD:C.denom.weightedTotalDegree w≤d)
      (hN : ∀ i,(C.numerator i).weightedTotalDegree w≤d) :
      (C.pullback a).weightedTotalDegree w≤d:= by
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.add_mem
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((Po _ _ _).trans hD)
    · apply Sd
      intro i _
      exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((Po _ _ _).trans (hN i))
  refine ⟨?_,hw Fin.val h.j hC.1.2.1 (fun i=>(hC.2 i).2.1),?_⟩
  · simpa only [xW] using hw 1 h.b
      (by simpa only [xW] using hC.1.1)
      (fun i=> by simpa only [xW] using (hC.2 i).1)
  · simpa only [xL] using hw (Pi.single (3:Fin 4) 1) h.t
      (by simpa only [xL] using hC.1.2.2)
      (fun i=> by simpa only [xL] using (hC.2 i).2.2)
theorem abr {P:af 4} {p:cy} (hP:aO (shape P) p) :
   yy (bC P) p:= by
 classical
 have hw (w:Fin 4→ℕ) :=
   aJY w (NW j8 P)
 refine ⟨?_,?_,?_⟩
 · exact (by simpa only [bC,weightedTotalDegree_one] using hw 1 :
    (bC P).totalDegree≤P.totalDegree).trans hP.1
 · exact (hw Fin.val).trans (by simpa only [shape,C6] using hP.2.1)
 · exact (by simpa only [bC,weightedTotalDegree_piSingle] using hw (Pi.single (3:Fin 4) 1) :
    (bC P).degreeOf 3≤P.degreeOf 3).trans hP.2.2
theorem a9d {R:Type*} [xm R] (P:c9 (Fin 4) R) :
  3*P.degreeOf 3≤P.weightedTotalDegree Fin.val := by
 classical
 rw [MvPolynomial.degreeOf_eq_sup,xI 3,← FR (by decide :0<3)]
 apply u5
 intro m hm
 rw [FR (by decide :0<3)]
 have h:=Finsupp.apply_smul_le_weight (fun i:Fin 4=>i.val) m (3:Fin 4)
 have hm' := le_weightedTotalDegree (fun i:Fin 4=>i.val) hm
 have hthree : (3:Fin 4).val=3:=rfl
 simpa only [smul_eq_mul,hthree,xI] using h.trans hm'
theorem Tn (P:af 4) :bF (shape P).iU:= by
 refine ⟨sI _ _,?_⟩
 change 3*P.degreeOf 3≤qE P
 rw [C6]
 exact a9d P
theorem A9 (L:ℕ) (p:cy) :bF (bY L p) := by
 let i:=2*L*(p.j-3)+L+3
 refine ⟨sI _ _,?_⟩
 change 3*min _ (i/3)≤ i
 have h:=G9 (2*L*(p.t - 1)+L+1) (i/3)
 omega
end
end lB
end
section
namespace YV
noncomputable section
open aR dN lB MvPolynomial
private def translate (a :KE) :lz →ₐ[ov] GeoJets :=
 bind₁ (fun i=>lI i - C (a i))
private theorem dhU (a :KE) (f :lz) :
   translate (-a) (translate a f)=f := by
 unfold translate
 rw [bind₁_bind₁]
 have hi (i:Fin 4) :
     bind₁ (fun j=>lI j - C ((-a) j)) (lI i - C (a i))=lI i:= by
   simp
 simp only [hi,bind₁_X_left,AlgHom.id_apply]
private theorem d3d (a y :KE) (f :lz) :
  eval (y+a) (translate a f)=eval y f := by
 change t3 (y+a) (bind₁ (fun i=>lI i - C (a i)) f)=t3 y f
 rw [aeval_bind₁]
 simp
private theorem bPc (a :KE) {f :lz} {p:cy}
    (hf :yy f p) :yy (translate a f) p:= by
  have hw (w:Fin 4→ℕ) :
      (translate a f).weightedTotalDegree w≤f.weightedTotalDegree w:= by
    apply weightedTotalDegree_bind₁_le_of_le w w
    intro i
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    exact Submodule.sub_mem _
      (X_mem_restrictWeightedDegree _ _ _ p9)
      (C_mem_restrictWeightedDegree _ _ _)
  refine ⟨?_,(hw Fin.val).trans hf.2.1,?_⟩
  · simpa only [xW] using (hw 1).trans
      (show f.weightedTotalDegree 1≤p.b by simpa only [xW] using hf.1)
  · simpa only [xL] using (hw (Pi.single (3:Fin 4) 1)).trans
      (show f.weightedTotalDegree (Pi.single (3:Fin 4) 1)≤p.t by
        simpa only [xL] using hf.2.2)
private theorem epj (a y :KE) {f g u v :lz}
  (hy :aKn f g u v y) :
  aKn (translate a f) (translate a g) (translate a u) (translate a v) (y+a) := by
 let T:lz →+* GeoJets :=(translate a).toRingHom
 let J:aU GeoJets :=nX ({f,g,u,v} : Set lz)
 have hsurj:zh T:= by
  intro z
  refine ⟨translate (-a) z,?_⟩
  change translate a (translate (-a) z)=z
  simpa only [neg_neg] using (dhU (-a) z)
 have hinj:pQ T :=
  (show Function.LeftInverse (translate (-a)) T from dhU a).injective
 have hcomap : (J.map T).comap T=J:= by
  rw [Ar T hsurj]
  rw [Ideal.comap_bot_of_injective T hinj,sup_bot_eq]
 have hk : (p7 (eval (y+a))).comap T=p7 (eval y) := by
  ext z
  simp only [Ideal.mem_comap,Mj]
  change eval (y+a) (translate a z)=0↔eval y z=0
  rw [d3d]
 have h' : p7 (eval y)∈(Ideal.comap T (J.map T)).minimalPrimes := by
  rw [hcomap]
  exact hy
 rw [← hk,Ideal.comap_minimalPrimes_eq_of_surjective hsurj] at h'
 obtain ⟨P,hP,heq⟩:=h'
 have heq' : P=p7 (eval (y+a)) :=
  Ideal.comap_injective_of_surjective T hsurj heq
 change p7 (eval (y+a)) ∈
  (nX ({T f,T g,T u,T v} : Set lz)).minimalPrimes
 rw [← heq']
 simpa only [J,KH,Set.image_insert_eq,UP] using hP
theorem eD0 {p h:cy} {f g u v :lz}
    (hf :yy f p) (hg:yy g p) (hu:yy u h) (hv :yy v h)
    (points :qm KE) (hpts : ∀ y∈points,aKn f g u v y) :
    ∃ f' g' u' v',yy f' p∧yy g' p∧yy u' h∧yy v' h ∧
      ∃ points' : qm KE,points'.card=points.card ∧
        ∀ y∈points',aKn f' g' u' v' y ∧ ∀ i,y i≠0:= by
  classical
  have ha (i:Fin 4) : ∃ a :ov,a∉points.image (fun y => -y i) :=
    Infinite.exists_notMem_finset _
  choose a ha using ha
  let e :KE ↪ KE :=
    ⟨fun y=>y+a,fun _ _ h=>add_right_cancel h⟩
  refine ⟨translate a f,translate a g,translate a u,translate a v,
    bPc a hf,bPc a hg,bPc a hu,bPc a hv,
    points.map e,Finset.card_map e,?_⟩
  intro y hy
  obtain ⟨z,hz,rfl⟩:=Finset.mem_map.mp hy
  refine ⟨epj a z (hpts z hz),?_⟩
  intro i hi
  apply ha i
  exact Finset.mem_image.mpr ⟨z,hz,(eq_neg_of_add_eq_zero_right hi).symm⟩
end
end YV
end
section
namespace YZ
noncomputable section
open K1 cu qQ Polynomial
def alD (g:aix) :Jet :=
  C (adV (a2x g)) +
    pU (R:=nI)*C (adV g.derivative)
def compatible (P Q:Jet) (q:zI) :Prop :=
  ∀ f :nI,oZ f→0<f.natDegree→C f∣P→C f∣Q →
    C f∈q.asIdeal → ∀ g a,aw5 f g a →
      alD g∈q.asIdeal
end
end YZ
end
section
set_option maxSynthPendingDepth 8
namespace YZ
noncomputable section
open K1 cu qQ Polynomial

open private byO byP bxk bxl from ProximityPrize.SubmissionLower.CN
private def Certificate (s :p5) (r mode :ℕ) :Prop :=
 0<byO s+3555*byP s r ∧
 0<byO s+32680*byP s r ∧
 0<bxk s+3555*bxl s r mode ∧
 0<bxk s+32680*bxl s r mode
private def cqy (i:Fin 4) :Prop :=
 Certificate (ayj i) (dI i) 0 ∧
 Certificate (aIq i) (dI i) 1
private instance (i:Fin 4) :z7 (cqy i) := by
 unfold cqy Certificate
 infer_instance
private theorem cSB (G:Jet) (hn : ¬ gT.alm G) :
    G∈FK Ng:= by
  let ev :=zc (fun _:Fin 2=>(0:FX))
  refine ⟨G.map (Kl ev),?_⟩
  ext j y e
  have hd: ((G.coeff j).coeff y).totalDegree=0 :=
    NZ fun hp=>hn ⟨j,y,hp⟩
  have he :=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  have hid :nq (ev ((G.coeff j).coeff y))=(G.coeff j).coeff y := by
    conv_lhs=>rw [he]
    simpa [ev] using he.symm
  exact oD (fun a :aZ=>a.coeff e)
    (by simpa only [Ng,Polynomial.coe_mapRingHom,coeff_map] using hid :
      (((Ng (G.map (Polynomial.mapRingHom ev))).coeff j).coeff y) =
        (G.coeff j).coeff y)
end
end YZ
end
section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace YZ
noncomputable section
open K1 cu qQ Polynomial
open scoped BigOperators
private def abn (z :K) :Fin 2→L :=
 ![mD K L z,(mD K L z)^p]
private def aE4 (z :K) :aKb →+* L[X] :=
 zc (fun i=>C (abn z i))
private theorem gtZ (z :K) (e :Fin 2 →₀ ℕ) (a :L[X]) :
  aE4 z (qG e a) =
   a*C (e.prod fun i n=>abn z i^n) := by
 simp [aE4,MvPolynomial.eval_monomial,Finsupp.prod,map_prod,zf]
private theorem gtT (z :K) (c:aKb) :
  aE4 z (∑ e∈c.support,qG e (c.coeff e).derivative) =
   (aE4 z c).derivative := by
 conv_rhs=>rw [c.as_sum]
 simp only [zd ,gtZ,derivative_mul,derivative_C,
  mul_zero,add_zero]
private theorem gtS (g:aix) (z :K) (T:L[X]) :
    (g.eval₂ (aE4 z) T).derivative =
      (a2x g).eval₂ (aE4 z) T +
        T.derivative*g.derivative.eval₂ (aE4 z) T:= by
  conv_lhs=>rw [eval₂_eq_sum]
  rw [a2x,derivative_apply g]
  simp only [eval₂_sum,eval₂_monomial,eval₂_mul,eval₂_C,eval₂_X_pow,
    pL,map_natCast,gtT]
  simp only [Polynomial.sum,derivative_sum,
    derivative_mul,derivative_pow,JQ,Finset.mul_sum]
  apply oD (_ + ·)
  apply yL rfl
  intro j hj
  simp only [eval₂_natCast,map_natCast]
  ring
private theorem cqr (g:aix) (z :K) (S:K[X]) :
   yq (adV g) z S =
     mD L[X] FX (g.eval₂ (aE4 z) (j9 S)) := by
 unfold yq adV kr
 rw [coe_mapRingHom,eval₂_map,hom_eval₂]
 congr 1
 apply t4
 · intro c
   simp [aE4,qD]
 · intro i
   fin_cases i <;> simp [aE4,qD,abn,jz]
theorem bWP {f :nI} {g:aix} {a :L[X]}
   (ha :aw5 f g a) {z :K} {S:K[X]} (hzero :yq f z S=0) :
   rD (alD g) z S=0:= by
 have hg:yq (adV g) z S=0:= by
   rw [ha.2]
   simpa [yq,eval₂_mul] using
     mul_eq_zero_of_right ((qD z) (nq (mD L[X] FX a))) hzero
 rw [cqr] at hg
 have ht:g.eval₂ (aE4 z) (j9 S)=0 :=
   (vi L[X] FX) (by simpa only [th] using hg)
 have hd:=gtS g z (j9 S)
 rw [ht,derivative_zero] at hd
 have hn:=oD (mD L[X] FX) hd.symm
 rw [wY ,pL,th,← cqr,← cqr] at hn
 simpa only [alD,rD,eval₂_add,eval₂_mul,eval₂_C,eval₂_X,
   Gi ,yq,kr,j9,derivative_map] using hn
end
end YZ
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace YZ
noncomputable section
open K1 cu qQ Polynomial
open scoped BigOperators
private def qN :nI →+* c9 (Fin 2) (Polynomial FX) :=
 eval₂RingHom (oz C) (nq (pU (R:=FX)))
private theorem bUe (f :nI) (e :Fin 2 →₀ ℕ) (y :ℕ) :
   ((qN f).coeff e).coeff y=(f.coeff y).coeff e := by
 induction f using Polynomial.induction_on' with
 | add f g hf hg=>simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,coeff_add,hf,hg]
 | monomial n c =>
   simp only [qN,Gi ,eval₂_monomial,← zf]
   rw [oj,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_map,oj,
     C_mul_X_pow_eq_monomial,coeff_monomial,coeff_monomial]
   split <;> simp
private theorem gCw (f :nI) (U:ℕ)
  (hs : ∀ y,(f.coeff y).totalDegree≤U) : (qN f).totalDegree≤U:= by
 apply u5
 intro e he
 obtain ⟨y,hy⟩ : ∃ y,((qN f).coeff e).coeff y≠0:= by
  by_contra! hz
  exact (MvPolynomial.mem_support_iff.mp he) (Dv (by simpa using hz))
 rw [bUe] at hy
 exact (sS (MvPolynomial.mem_support_iff.mpr hy)).trans (hs y)
private theorem goO {f A:nI} (hdiv :f∣A) (hn:A≠0)
  {U:ℕ} (hA : ∀ y,(A.coeff y).totalDegree≤U) (y :ℕ) :
  (f.coeff y).totalDegree≤U:= by
 have hn' : qN A≠0:= by
  intro hz
  apply hn
  ext n e
  simp [← bUe A e n,hz]
 have h:=(MvPolynomial.totalDegree_le_of_dvd_of_isDomain (map_dvd qN hdiv) hn').trans
  (gCw A U hA)
 apply u5
 intro e he
 apply (sS (p:=qN f) ?_).trans h
 apply MvPolynomial.mem_support_iff.mpr
 intro hz
 exact (MvPolynomial.mem_support_iff.mp he) (by rw [← bUe,hz,coeff_zero])
private def amd:aKb →+* aZ:=oz (mD L[X] FX)
private theorem ev5:pQ amd :=
 MvPolynomial.map_injective _ (vi L[X] FX)
private theorem cXA (b:aKb) :
  (amd b).totalDegree=b.totalDegree := by
 unfold amd SC
 rw [MvPolynomial.support_map_of_injective _ (vi L[X] FX)]
private theorem cXH (g:aix) (y :ℕ) :
 (adV g).coeff y=amd (g.coeff y) :=coeff_map _ _
private theorem cFI {f :nI} {g:aix} {a :L[X]}
  (ha :aw5 f g a) (y :ℕ) :
  amd (g.coeff y)=nq (mD L[X] FX a)*f.coeff y := by
 rw [← cXH,ha.2,coeff_C_mul]
private def bEo (b:aKb) :aKb :=
 ∑ e∈b.support,qG e (b.coeff e).derivative
private theorem dYF (b:aKb) : (bEo b).totalDegree≤b.totalDegree :=
 MvPolynomial.totalDegree_finsetSum_le fun _ he =>
  (MvPolynomial.totalDegree_monomial_le _ _).trans (sS he)
private theorem dYI (g:aix) (y :ℕ) :
   (a2x g).coeff y=bEo (g.coeff y) := by
 classical
 unfold a2x
 rw [coeff_sum,Polynomial.sum_def,Finset.sum_eq_single y]
 · simp [bEo]
 · intro j _ hj
   exact coeff_monomial_of_ne _ (Ne.symm hj)
 · intro hy
   have hzero :g.coeff y=0:= by simpa [Polynomial.mem_support_iff] using hy
   simp [hzero]
private theorem b7D {f :nI} {g:aix} {a :L[X]}
  (ha :aw5 f g a) :
  adV g.derivative=C (nq (mD L[X] FX a))*f.derivative := by
 have hmap :adV g.derivative=(adV g).derivative :=
  (derivative_map g amd).symm
 rw [hmap,ha.2,derivative_mul,derivative_C,zero_mul,v9]
private theorem b0a (x :FX) (b:aZ) :
  (nq x*b).totalDegree≤b.totalDegree := by
 simpa using Kh (nq x) b
theorem bWO {s :p5} {Q:Jet} (hQ:Q≠0)
    (hc:oU Q s) (hj:1≤ s.J) {f :nI} (hf :C f∣Q)
    {g:aix} {a :L[X]} (ha :aw5 f g a) :
    oU (alD g) s := by
  have hn:=leadingCoeff_ne_zero.mpr hQ
  have hfQ:f∣Q.leadingCoeff :=(G3 _ _).mp hf Q.natDegree
  have ht: (Q.coeff Q.natDegree).coeff Q.leadingCoeff.natDegree≠0:= by
    rw [u8 ,u8]
    exact leadingCoeff_ne_zero.mpr hn
  have hy :f.natDegree≤ s.B:=(Ee hfQ hn).trans
    ((t9 _ _).trans (hc _ _ ht).1)
  have hu (y :ℕ) : (f.coeff y).totalDegree≤ s.U:= by
    apply goO hfQ hn _ y
    intro j
    by_cases hz : (Q.coeff Q.natDegree).coeff j=0
    · simpa only [← u8 ,hz,RC] using vG s.U
    · exact (hc _ _ hz).2.2
  intro v y hv
  cases v with
  | zero =>
    simp only [alD,coeff_add,coeff_C_zero,coeff_X_mul_zero,add_zero,
      cXH,dYI] at hv ⊢
    have hfy :f.coeff y≠0:= by
      intro hz
      have hg:g.coeff y=0:=ev5 (by simp [cFI ha y,hz])
      exact hv (by simp [hg,bEo])
    refine ⟨(II hfy).trans hy,vG _,?_⟩
    rw [cXA]
    refine (dYF _).trans ?_
    rw [← cXA,cFI ha y]
    exact (b0a _ _).trans (hu y)
  | succ v =>
    simp only [alD,coeff_add,coeff_C_succ,coeff_X_mul,v9] at hv ⊢
    cases v with
    | zero =>
      rw [coeff_C_zero,b7D ha,coeff_C_mul] at hv ⊢
      have hdy :f.derivative.coeff y≠0:= fun hz=>hv (by simp [hz])
      have hdegree :=II hdy
      have hpos :f.natDegree≠0:= by
        intro hz
        exact hdy (by rw [EP hz,derivative_C,coeff_zero])
      have hlt:=natDegree_derivative_lt hpos
      refine ⟨by omega,hj,(b0a _ _).trans ?_⟩
      rw [coeff_derivative]
      have hcast: (↑y+1 :aZ)=nq (↑y+1 :FX) := by simp
      rw [hcast,oj]
      exact (b0a _ _).trans (hu (y+1))
    | succ v=>simp [coeff_C_succ] at hv
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
 Polynomial.isLocalization in
private theorem d35 (f :nI) : ∃ g a,aw5 f g a := by
 let D:=(ze (L[X])).map (nq:L[X] →+* aKb)
 obtain ⟨⟨g,⟨_,d,hd,rfl⟩⟩,he⟩:=IsLocalization.surj (D.map C) f
 obtain ⟨a,ha,rfl⟩:=hd
 refine ⟨g,a,mem_nonZeroDivisors_iff_ne_zero.mp ha,?_⟩
 change f*adV (C (nq a))=adV g at he
 simpa [adV,oj] using he.symm
private theorem dWv {f :nI} (hd:0<f.natDegree)
  (hp:f.natDegree<p) (hf :f≠0) :f.derivative≠0:= by
 let _:CharP FX p:=charP_of_injective_algebraMap (vi L[X] FX) p
 let _:CharP aZ p:=charP_of_injective_ringHom (f :=(nq:FX →+* aZ))
  (MvPolynomial.C_injective (Fin 2) FX) p
 have hc: (f.natDegree :aZ)≠0:= by
  rw [Ne,CharP.cast_eq_zero_iff aZ p]
  exact fun h=>(not_le_of_gt hp) (Nat.le_of_dvd hd h)
 intro hzero
 have h:=oD (fun A:nI=>A.coeff (f.natDegree - 1)) hzero
 have hs :f.natDegree - 1+1=f.natDegree := by omega
 rw [coeff_zero,coeff_derivative,← Nat.cast_succ,Nat.succ_eq_add_one,hs,u8] at h
 exact GR (leadingCoeff_ne_zero.mpr hf) hc h
theorem dHP {f :nI} (hi:oZ f) (hd:0<f.natDegree)
   (hp:f.natDegree<p) {g:aix} {a :L[X]} (ha :aw5 f g a) :
   XY.ag6 (C f) (alD g) := by
 have hC: (C f :Jet)≠0:=C_ne_zero.mpr hi.ne_zero
 have ha' : mD L[X] FX a≠0:= by
   intro hz
   exact ha.1 ((vi L[X] FX) (by simpa only [th] using hz))
 have hu:wB (C (nq (mD L[X] FX a)) :nI) :=
   ((isUnit_iff_ne_zero.mpr ha').map (nq:FX →+* aZ)).map
     (C:aZ →+* nI)
 have hder :=dWv hd hp hi.ne_zero
 have hCutter : (alD g).coeff 1=adV g.derivative := by
   simp [alD]
 have hder' : adV g.derivative≠0:= by
   rw [b7D ha]
   exact GR hu.ne_zero hder
 have hOrd:IsRelPrime f (adV g.derivative) := by
   apply hi.isRelPrime_iff_not_dvd.mpr
   rw [b7D ha,hu.dvd_mul_left]
   exact fun hf=>(not_le_of_gt (natDegree_derivative_lt hd.ne')) (Ee hf hder)
 refine ⟨hC,fun h=>hder' (hCutter.symm.trans (by simp [h])),?_⟩
 intro D hD hleft hright
 have hdeg:D.natDegree≤0:= by simpa using Ee hleft hC
 have heq :=EP (Qw hdeg)
 rw [heq] at hleft hright
 have h0:D.coeff 0∣f := by simpa using (G3 _ _).mp hleft 0
 have h1 :=(G3 _ _).mp hright 1
 rw [hCutter] at h1
 apply hD.not_isUnit
 rw [heq]
 exact (hOrd h0 h1).map (C:nI →+* Jet)
theorem c2P (f :nI) (hi:oZ f) (hd:0<f.natDegree)
  (hp:f.natDegree<p) :
  ∃ g a,aw5 f g a∧XY.ag6 (C f) (alD g) ∧
    ∀ z S,yq f z S=0→ rD (alD g) z S=0:= by
 obtain ⟨g,a,ha⟩:=d35 f
 exact ⟨g,a,ha,dHP hi hd hp ha,fun _ _=>bWP ha⟩
end
end YZ
end
section
namespace aFX
noncomputable section
open K1 cu gT pI Polynomial
def aTw (P Q:Jet) (I:aU lJ) :Prop :=
  ∀ f :nI,oZ f→0<f.natDegree→C f∣P→C f∣Q →
    iJ (C f)∈I → ∀ g a,qQ.aw5 f g a →
      iJ (YZ.alD g)∈I
end
end aFX
end
section
namespace BO
noncomputable section
open Polynomial K1 aR dN
open scoped BigOperators
theorem Ue {P:af 4} {S:ao[X]} :
   bC P∈Ch S↔cK P S=0:= by
 unfold Ch
 rw [Mj]
 change zc _ (oz j8 P)=0↔_
 rw [MvPolynomial.eval_map]
 change MvPolynomial.eval₂ j8 (⇑j8 ∘ jet S) P=0↔_
 rw [← MvPolynomial.eval₂_comp]
 have injective :pQ j8 :=
   (mD lN ov).injective.comp
     (vi ao[X] lN)
 exact map_eq_zero_iff _ injective
private theorem duz (P:af 4) (S:ao[X]) :
  cK P S=(Z8 P S).coeff 0:= by
 let f :=nq (σ:=Fin 4) (R:=ao[X])
 let g:Fin 4→af 4 := fun i=>lI i+MvPolynomial.C (jet S i)
 change (zc (jet S)) P =
  (MvPolynomial.constantCoeff.comp (qz f g)) P
 congr 1
 ext <;> simp [f,g]
theorem bfW {P:af 4} {S:ao[X]} {l:ℕ}
  (hl:0<l) (h:wU P S l) :cK P S=0:= by
 rw [duz]
 by_contra he
 have h0:=h 0 (MvPolynomial.mem_support_iff.mpr he)
 simp at h0
 omega
theorem bsq {aI:aU lz} {P:af 4} {S:ao[X]}
  (hZ:aI≤Ch S) (hP:cK P S=0) :
  ∃ C,(AX aI P).IsMinimalPrime C∧C≤Ch S:= by
 have h:AX aI P≤Ch S :=
  sup_le hZ ((Fa _).2 (Ue.mpr hP))
 have : (Ch S).IsPrime :=Dz (An S)
 exact Iw h
theorem bhO (g P:af 4) (S:ao[X]) (a :ℕ)
   (hg:cK g S=0) (hP:cK P S=0) :cK (Uy g P a) S=0:= by
 induction a with
 | zero=>exact hP
 | succ a ih =>
   rw [Uy,Function.iterate_succ_apply']
   rw [aNw _ _ _ hg]
   change cK (separant g) S*derivative (cK (Uy g P a) S)=0
   rw [ih,th,mul_zero]
end
end BO
end
section
namespace GJ
noncomputable section
open aR dN BO lB
open scoped BigOperators
def c1 :Prop :=
  ∀ (aI:aU lz) (P:lz) (a h:cy),
    aI.IsPrime→ oy (lz ⧸ aI)=2 →
    vE a→vE h→P∉aI→yy P a →
    6*(∑ C∈(aI ⊔ nX {P}).minimalPrimesFinset,
      pN C (h.scale 6))≤Ux aI (a.scale 6) (h.scale 6)
def c2 :Prop :=
  ∀ (aI:aU lz) (a b h:cy) (m n:ℕ),
    aI.IsPrime→ oy (lz ⧸ aI)=2 →
    vE a→vE b→vE h→0< m →
    Ux aI (((a.scale m).plus (b.scale n)).scale 6) (h.scale 6) ≤
      m*Ux aI (a.scale 6) (h.scale 6) +
      n*Ux aI (b.scale 6) (h.scale 6)
def c3:Prop :=
  ∀ (F G:lz) (p q a h:cy),
    F≠0→G≠0→ IsRelPrime F G →
    vE p→vE q→vE a→vE h →
    yy F p→yy G q →
    ∀ (uG:qm (aU lz)) (v :aU lz→ℕ),
      (∀ aI∈uG,∃ hs : (Ib F G).IsMinimalPrime aI,
        oA (Ib F G) aI hs.isPrime=(v aI:ℕ∞)) →
      32*(∑ aI∈uG,v aI *
        Ux aI (a.scale 6) (h.scale 6))≤36*iH p q a h
end
end GJ
end
section
namespace E6
noncomputable section
open aR dN
def rU (p:cy) :Set (Fin 4→ℕ) :=
  {e | e 0+e 1+e 2+e 3≤p.b ∧
    e 1+2*e 2 + 3*e 3≤p.j∧e 3≤p.t}
def nE (p:cy) :Set (Fin 4 →₀ ℕ) :=
 {e | (fun i=>e i)∈rU (p.scale 6)}
instance (p:cy) :Finite (nE p) := by
 refine ((Finsupp.finite_of_degree_le (6*p.b)).subset ?_).to_subtype
 intro e he
 change e.degree≤6*p.b
 rw [G1 ,zg]
 have he' : e 0+e 1+e 2+e 3≤6*p.b:=he.1
 simpa only [uJ] using he'
def aFi (aI:aU lz) (p:cy) :ℚ :=
  (Ok
    (aI.comap (uW ov (nE p)).toRingHom)).coeff 2
end
end E6
end
section
namespace E6
open aR dN BO lB GJ
open scoped BigOperators Pointwise
theorem bI6 (p:cy) (m:uL p) :
  (fun i=>(m i).val)∈rU p↔m∈Bz p:= by
 norm_num [rU,Bz,zg]
theorem cNO (p:cy) :
   rU p=(fun m:uL p=> fun i=>(m i).val) ''
     (Bz p:Set (uL p)) := by
 ext e
 constructor
 · intro he
   have hsum: (∑ i,e i)≤p.b:= by
     have hb:e 0+e 1+e 2+e 3≤p.b:=he.1
     simpa [zg ,uJ] using hb
   let m:uL p:= fun i=>⟨e i,NX
     ((Dw (f :=e) (fun _ _=>vG _) (In i)).trans hsum)⟩
   exact ⟨m,(bI6 p m).mp he,rfl⟩
 · rintro ⟨m,hm,rfl⟩
   exact (bI6 p m).mpr hm
theorem bFF:rU ⟨0,0,0⟩=({0} : Set (Fin 4→ℕ)) := by
 ext e
 constructor
 · intro he
   have hb:e 0+e 1+e 2+e 3≤0:=he.1
   apply Set.mem_singleton_iff.mpr
   funext i
   fin_cases i
   · change e 0=0
     omega
   · change e 1=0
     omega
   · change e 2=0
     omega
   · change e 3=0
     omega
 · rintro rfl
   simp [rU]
private theorem aXT {x a b:ℕ} (h:x≤a+b) :
   ∃ u v :ℕ,u≤a∧v≤b∧u+v=x := by
 refine ⟨min x a,x - min x a,G9 _ _,?_,?_⟩
 · omega
 · omega
theorem cNP (p q:cy) (hp:bF p) (hq:bF q)
    (hpj:p.j % 2=0) (hqj:q.j % 2=0)
    (hpt:p.t % 2=0) :
    rU (p.plus q)=rU p+rU q:= by
  ext e
  change _ ↔ ∃ u∈rU p,∃ v∈rU q,u+v=e
  constructor
  · intro he
    obtain ⟨htotal,hindex,htop⟩:e 0+e 1+e 2+e 3≤p.b+q.b ∧
        e 1+2*e 2 + 3*e 3≤p.j+q.j∧e 3≤p.t+q.t:=he
    obtain ⟨hpb,hpc⟩:=hp
    obtain ⟨hqb,hqc⟩:=hq
    let u3:=min (e 3) p.t
    let v3:=e 3 - u3
    have hu3:u3≤p.t:=G9 _ _
    have hv3:v3≤q.t:= by dsimp [u3,v3]; omega
    have huv3:u3+v3=e 3:= by dsimp [u3,v3]; omega
    let jp:=p.j-3 * u3
    let jq:=q.j-3*v3
    have hjp:jp+3 * u3=p.j:= by dsimp [jp]; omega
    have hjq:jq+3*v3=q.j:= by dsimp [jq]; omega
    have hweight:e 1+2*e 2≤jp+jq:= by omega
    have hparity :jp % 2=0∨jq % 2=0:= by
      by_cases h:e 3≤p.t
      · have hz :v3=0:= by simp [v3,u3,min_eq_left h]
        right
        omega
      · have ht:u3=p.t:=min_eq_right (by omega)
        left
        omega
    have hcapacity :e 2≤jp/2+jq/2 := by
      rcases hparity with h | h <;> omega
    obtain ⟨u2,v2,hu2,hv2,huv2⟩:=aXT hcapacity
    have hindex1 :e 1≤(jp - 2*u2)+(jq - 2*v2) := by omega
    obtain ⟨u1,v1,hu1,hv1,huv1⟩:=aXT hindex1
    have hspentP:u1+2*u2 + 3 * u3≤p.j:= by omega
    have hspentQ:v1+2*v2 + 3*v3≤q.j:= by omega
    have htotal0:e 0≤(p.b-(u1+u2+u3))+(q.b-(v1+v2+v3)) := by omega
    obtain ⟨u0,v0,hu0,hv0,huv0⟩:=aXT htotal0
    refine ⟨![u0,u1,u2,u3],?_,![v0,v1,v2,v3],?_,?_⟩
    · change u0+u1+u2+u3≤p.b∧u1+2*u2 + 3 * u3≤p.j∧u3≤p.t
      exact ⟨by omega,hspentP,hu3⟩
    · change v0+v1+v2+v3≤q.b∧v1+2*v2 + 3*v3≤q.j∧v3≤q.t
      exact ⟨by omega,hspentQ,hv3⟩
    · funext i
      fin_cases i
      · exact huv0
      · exact huv1
      · exact huv2
      · exact huv3
  · rintro ⟨u,hu,v,hv,rfl⟩
    obtain ⟨hub,huj,hut⟩:u 0+u 1+u 2+u 3≤p.b ∧
        u 1+2*u 2 + 3 * u 3≤p.j∧u 3≤p.t:=hu
    obtain ⟨hvb,hvj,hvt⟩:v 0+v 1+v 2+v 3≤q.b ∧
        v 1+2*v 2 + 3*v 3≤q.j∧v 3≤q.t:=hv
    change (u 0+v 0)+(u 1+v 1)+(u 2+v 2)+(u 3+v 3)≤p.b+q.b ∧
      (u 1+v 1)+2*(u 2+v 2)+3*(u 3+v 3)≤p.j+q.j ∧
      u 3+v 3≤p.t+q.t
    exact ⟨by omega,by omega,by omega⟩
theorem BP {p:cy} (hp:bF p) (k :ℕ) :
  bF (p.scale k) := by
 refine ⟨p6 k hp.1,?_⟩
 change 3*(k*p.t)≤k*p.j
 rw [Nat.mul_left_comm 3 k]
 exact p6 k hp.2
theorem Nc {p q:cy} (hp:bF p) (hq:bF q) :
  bF (p.plus q) := by
 obtain ⟨hpb,hpt⟩:=hp
 obtain ⟨hqb,hqt⟩:=hq
 change p.j+q.j≤p.b+q.b∧3*(p.t+q.t)≤p.j+q.j
 omega
theorem d5r {p q:cy} (hp:bF p) (hq:bF q) :
  rU ((p.plus q).scale 6)=rU (p.scale 6)+rU (q.scale 6) := by
 rw [show (p.plus q).scale 6=(p.scale 6).plus (q.scale 6) from by
  cases p
  cases q
  simp [oK,pG,Mw]]
 apply cNP _ _ (BP hp 6) (BP hq 6) <;>
  change 6*_ % 2=0 <;> omega
theorem brA (p:cy) : (0:Fin 4 →₀ ℕ)∈nE p:= by
 simp [nE,rU]
theorem euG {p:cy} (hp:vE p) (i:Fin 4) :
  Finsupp.single i 1∈nE p:= by
 obtain ⟨⟨hpb,hpj⟩,hpt⟩:=hp
 fin_cases i <;> norm_num [nE,rU,pG,Ef] <;> omega
theorem a44 {p q:cy} (hp:bF p) (hq:bF q) :
   nE (p.plus q)=nE p+nE q:= by
 ext e
 change (fun i=>e i)∈rU ((p.plus q).scale 6) ↔
   ∃ u∈nE p,∃ v∈nE q,u+v=e
 rw [d5r hp hq]
 constructor
 · rintro ⟨u,hu,v,hv,he⟩
   refine ⟨Finsupp.equivFunOnFinite.symm u,hu,Finsupp.equivFunOnFinite.symm v,hv,?_⟩
   ext i
   exact Du he i
 · rintro ⟨u,hu,v,hv,rfl⟩
   exact ⟨fun i=>u i,hu,fun i=>v i,hv,rfl⟩
theorem brz {p:cy} (hp:bF p) (n:ℕ) :
   nE (p.scale n)=n•nE p:= by
 induction n with
 | zero =>
   rw [show p.scale 0=⟨0,0,0⟩ from by simp [pG]]
   ext e
   change (fun i=>e i)∈rU ⟨0,0,0⟩↔e∈(0:ℕ)•nE p
   rw [bFF,zero_smul,Set.mem_zero,LR]
   constructor
   · intro he
     ext i
     exact Du he i
   · rintro rfl
     rfl
 | succ n ih =>
   rw [show p.scale (n+1)=(p.scale n).plus p from by
     cases p
     simp [pG,oK,yJ]]
   rw [a44 (BP hp n) hp,ih,succ_nsmul]
private theorem aDS {S:Set (Fin 4 →₀ ℕ)} {n:ℕ}
    {e :Fin 4 →₀ ℕ} (he :e∈n•S) :
    ∃ P:c9 S ov,P.totalDegree≤n ∧
      uW ov S P=qG e 1 := by
  induction n generalizing e with
  | zero =>
    rw [zero_smul,Set.mem_zero] at he
    subst e
    exact ⟨1,by simp,by simp⟩
  | succ n ih =>
    rw [succ_nsmul] at he
    obtain ⟨u,hu,v,hv,rfl⟩:=he
    obtain ⟨P,hP,hmap⟩:=ih hu
    refine ⟨P*lI ⟨v,hv⟩,?_,?_⟩
    · exact (Kh _ _).trans (by
        rw [MvPolynomial.totalDegree_X]
        omega)
    · rw [pL,hmap,MvPolynomial.monomialMap_X,MvPolynomial.monomial_mul_monomial,zi]
theorem c0M {p:cy} (hp:bF p) (n:ℕ) :
   (FQ (nE p) ov n).map
     (uW ov (nE p)).toLinearMap =
     C5 ov (nE (p.scale n)) := by
 rw [brz hp n]
 apply qM
 · rintro _ ⟨P,hP,rfl⟩
   exact MvPolynomial.monomialMap_mem_restrictSupport_nsmul (brA p)
     ((Sv _ _ _).mp hP)
 · rw [Il]
   refine Submodule.span_le.mpr ?_
   rintro _ ⟨e,he,rfl⟩
   obtain ⟨P,hP,hmap⟩:=aDS he
   exact ⟨P,(Sv _ _ _).mpr hP,hmap⟩
end E6
end
section
namespace E6
noncomputable section
open aR dN GJ
def c1 :Prop :=
  ∀ (aI:aU lz) (a h:cy),
    aI.IsPrime→ oy (lz ⧸ aI)=2 →
    vE a→vE h →
    (Ux aI (a.scale 6) (h.scale 6) :ℚ) =
      aFi aI (a.plus h)-aFi aI a-aFi aI h
def c2 :Prop :=
  ∀ (aI:aU lz) (a b h:cy),
    aI.IsPrime→ oy (lz ⧸ aI)=2 →
    vE a→vE b→vE h →
    ∃ (aa bb hh ab ah bh:ℚ),∀ i j k :ℕ,0< i+j+k →
      aFi aI (((a.scale i).plus (b.scale j)).plus (h.scale k)) =
        aa*(i:ℚ)^2+bb*(j:ℚ)^2+hh*(k :ℚ)^2 +
        ab*(i:ℚ)*(j:ℚ)+ah*(i:ℚ)*(k :ℚ)+bh*(j:ℚ)*(k :ℚ)
theorem of_children (h1 :c1) (h2 :c2) :GJ.c2 := by
  intro aI a b h m n hs hdim ha hb hh hm
  let p:=(a.scale m).plus (b.scale n)
  have hp:vE p:= by
    refine ⟨Nc (BP ha.1 m) (BP hb.1 n),?_⟩
    change 0< m*a.t+n*b.t
    have hpos :=Nat.mul_pos hm ha.2
    omega
  obtain ⟨qa,qb,qh,qab,qah,qbh,hquad⟩:=h2 aI a b h hs hdim ha hb hh
  have htest :aFi aI h=qh:= by
    simpa [pG,oK] using hquad 0 0 1 (by decide)
  have kK (i j:ℕ) (hij:0< i+j) :
      aFi aI (((a.scale i).plus (b.scale j)).plus h) -
        aFi aI ((a.scale i).plus (b.scale j))-aFi aI h =
        (i:ℚ)*qah+(j:ℚ)*qbh:= by
    have hbase :=hquad i j 0 (by omega)
    have hsum:=hquad i j 1 (by omega)
    simp [pG,oK] at hbase hsum ⊢
    rw [hbase,hsum,htest]
    ring
  have hA: (Ux aI (a.scale 6) (h.scale 6) :ℚ)=qah:= by
    refine (h1 aI a h hs hdim ha hh).trans ?_
    simpa [pG,oK] using kK 1 0 (by decide)
  have hB: (Ux aI (b.scale 6) (h.scale 6) :ℚ)=qbh:= by
    refine (h1 aI b h hs hdim hb hh).trans ?_
    simpa [pG,oK] using kK 0 1 (by decide)
  have htotal :
      (Ux aI (p.scale 6) (h.scale 6) :ℚ) =
        (m:ℚ)*(Ux aI (a.scale 6) (h.scale 6) :ℚ) +
        (n:ℚ)*(Ux aI (b.scale 6) (h.scale 6) :ℚ) := by
    rw [hA,hB,h1 aI p h hs hdim hp hh]
    exact kK m n (by omega)
  exact le_of_eq (by exact_mod_cast htotal)
end
end E6
end
section
namespace YU
noncomputable section
open aR dN BO lB GJ E6
def dO {k :Type*} [oq k] (I:aU (c9 (Fin 4) k)) (p:cy) :
    Eg k (c9 (Fin 4) k ⧸ I) :=
  (C5 k (nE p)).map (t6 k I).toLinearMap
abbrev Coeff (a h:cy) :=VM (a.scale 6) (h.scale 6)
def gN (aI:aU lz) (a h:cy) :
    aU (c9 (Fin 4) (Coeff a h)) :=
  aI.map (oz (mD ov (Coeff a h)))
abbrev Oa (aI:aU lz) (a h:cy) :=
 c9 (Fin 4) (Coeff a h) ⧸ gN aI a h
def leftSection (a h:cy) :c9 (Fin 4) (Coeff a h) :=
 Uq (a.scale 6) (wA:uL (a.scale 6)→aav (a.scale 6) (h.scale 6))
def rightSection (a h:cy) :c9 (Fin 4) (Coeff a h) :=
 Uq (h.scale 6) (qU :uL (h.scale 6)→aav (a.scale 6) (h.scale 6))
def ke (aI:aU lz) (a h:cy) :
    aU (c9 (Fin 4) (Coeff a h)) :=
  gN aI a h ⊔ nX {leftSection a h,rightSection a h}
abbrev aiB (aI:aU lz) (a h:cy) :=
 c9 (Fin 4) (Coeff a h) ⧸ ke aI a h
def Va (aI:aU lz) (a h:cy) :
    Oa aI a h →ₐ[Coeff a h] aiB aI a h :=
  Fz _ (AlgHom.id _ _) (by
    change gN aI a h≤ke aI a h
    exact Cy)
def AL (aI:aU lz) (a h:cy) (i j:ℕ) :
    Eg (Coeff a h) (Oa aI a h) :=
  dO (gN aI a h) ((a.scale i).plus (h.scale j))
def leftMul (aI:aU lz) (a h:cy) :
    Oa aI a h →ₗ[Coeff a h] Oa aI a h :=
  Vl _ (ox (gN aI a h) (leftSection a h))
def rightMul (aI:aU lz) (a h:cy) :
    Oa aI a h →ₗ[Coeff a h] Oa aI a h :=
  Vl _ (ox (gN aI a h) (rightSection a h))
end
end YU
end
section
namespace YU
noncomputable section
open aR dN GJ E6 MvPolynomial
instance {k :Type*} [oq k] (I:aU (c9 (Fin 4) k)) (p:cy) :
  pC k (dO I p) := by
 let:=Module.Finite.of_basis (basisRestrictSupport k (nE p))
 unfold dO
 infer_instance
instance (aI:aU lz) (a h:cy) (i j:ℕ) :
  pC (Coeff a h) (AL aI a h i j) := by
 unfold AL
 infer_instance
theorem eQu (aI:aU lz) (a h:cy)
  (ha :vE a) {N i j:ℕ} (hi:N≤ i) :
  quotientDegreeLE (ke aI a h) N ≤
    (AL aI a h i j).map (Va aI a h).toLinearMap:= by
 intro x hx
 obtain ⟨P,hP,rfl⟩:=mem_quotientDegreeLE.mp hx
 have hat :=ha.2
 have haj:=ha.1.2
 have hab:=ha.1.1
 have haT:i≤ i*a.t:=Ea i hat
 have haJ:3*i≤ i*a.j:= by
  rw [xI 3 i]
  exact p6 _ (by omega)
 have haB:i≤ i*a.b:= by
  exact Ea _ (by omega)
 have hmem:P∈C5 (Coeff a h) (nE ((a.scale i).plus (h.scale j))) := by
  intro e he
  have hdeg:=(sS he).trans hP
  change e.degree≤N at hdeg
  rw [G1 ,zg] at hdeg
  change e 0+e 1+e 2+e 3≤6*(i*a.b+j*h.b) ∧
    e 1+2*e 2 + 3*e 3≤6*(i*a.j+j*h.j) ∧
    e 3≤6*(i*a.t+j*h.t)
  exact ⟨by omega,by omega,by omega⟩
 refine ⟨ox (gN aI a h) P,⟨P,hmem,rfl⟩,?_⟩
 rfl
theorem eAQ (aI:aU lz) (a h:cy) (i j:ℕ)
    (hl:pQ (leftMul aI a h))
    (hr :pQ (rightMul aI a h))
    (hinter : (AL aI a h i (j+1)).map (leftMul aI a h) ⊓
        (AL aI a h (i+1) j).map (rightMul aI a h) =
      (AL aI a h i j).map ((leftMul aI a h).comp (rightMul aI a h)))
    (hker :AL aI a h (i+1) (j+1) ⊓ vl (Va aI a h).toLinearMap =
        (AL aI a h i (j+1)).map (leftMul aI a h) ⊔
          (AL aI a h (i+1) j).map (rightMul aI a h)) :
    (lV (Coeff a h) (AL aI a h (i+1) (j+1)) :ℚ) -
      (lV (Coeff a h) (AL aI a h i (j+1)) :ℚ) -
      (lV (Coeff a h) (AL aI a h (i+1) j) :ℚ) +
      (lV (Coeff a h) (AL aI a h i j) :ℚ) =
      (lV (Coeff a h)
        ((AL aI a h (i+1) (j+1)).map (Va aI a h).toLinearMap) :ℚ) := by
  let W:=AL aI a h (i+1) (j+1)
  let q:=(Va aI a h).toLinearMap
  let f :=q.comp W.subtype
  let U:=(AL aI a h i (j+1)).map (leftMul aI a h)
  let V:=(AL aI a h (i+1) j).map (rightMul aI a h)
  have hmap : (vl f).map W.subtype=U ⊔ V:= by
    rw [← hker]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.property,hz⟩
    · rintro ⟨hx,hqx⟩
      exact ⟨⟨x,hx⟩,hqx,rfl⟩
  have hrange :LinearMap.range f=W.map q:= by
    dsimp only [f]
    rw [LinearMap.range_comp,Submodule.range_subtype]
  have hK:lV (Coeff a h) (vl f)=lV (Coeff a h) ↑(U ⊔ V) := by
    rw [← hmap]
    exact (yQ _ Up _).finrank_eq
  have hsum:=LinearMap.finrank_range_add_finrank_ker f
  rw [hrange,hK] at hsum
  have huv :=Submodule.finrank_sup_add_finrank_inf_eq U V
  change lV (Coeff a h) ↑(U ⊔ V)+Module.finrank (Coeff a h)
    ↑((AL aI a h i (j+1)).map (leftMul aI a h) ⊓
      (AL aI a h (i+1) j).map (rightMul aI a h)) =
    lV (Coeff a h) U + lV (Coeff a h) V at huv
  have hcomp:pQ ((leftMul aI a h).comp (rightMul aI a h)) :=
    fun _ _ hxy=>hr (hl hxy)
  rw [hinter,← (yQ _ hcomp (AL aI a h i j)).finrank_eq] at huv
  have hu:=(yQ _ hl (AL aI a h i (j+1))).finrank_eq
  have hv :=(yQ _ hr (AL aI a h (i+1) j)).finrank_eq
  change lV (Coeff a h) (AL aI a h i (j+1))= _ at hu
  change lV (Coeff a h) (AL aI a h (i+1) j)= _ at hv
  rw [show lV (Coeff a h) U= _ from hu.symm,
    show lV (Coeff a h) V= _ from hv.symm] at huv
  have hnat :lV (Coeff a h) W+Module.finrank (Coeff a h) (AL aI a h i j) =
      lV (Coeff a h) (W.map q) +
        lV (Coeff a h) (AL aI a h i (j+1)) +
        lV (Coeff a h) (AL aI a h (i+1) j) := by omega
  have hrat :=oD (fun x :ℕ=>(x :ℚ)) hnat
  push_cast at hrat
  change (lV (Coeff a h) W:ℚ)-_-_+_=(lV (Coeff a h) (W.map q) :ℚ)
  linarith
end
end YU
end
section
namespace YU
noncomputable section
open aR dN lB GJ E6 MvPolynomial
open scoped TensorProduct Polynomial
section ScalarExtension
variable {k L:Type*} [oq k] [oq L] [Algebra k L]
private abbrev a5G (I:aU (c9 (Fin 4) k)) :aU (c9 (Fin 4) L) :=
 I.map (oz (mD k L))
private def anK (I:aU (c9 (Fin 4) k)) :
   L ⊗[k] (c9 (Fin 4) k ⧸ I) ≃ₐ[L] c9 (Fin 4) L ⧸ a5G I:= by
 let e :=algebraTensorAlgEquiv (σ:=Fin 4) k L
 refine (Algebra.TensorProduct.tensorQuotientEquiv L (c9 (Fin 4) k) L I).trans
   (Ideal.quotientEquivAlg _ _ e ?_)
 change I.map (oz (mD k L)) =
   (I.map (Algebra.TensorProduct.includeRight (A:=L)).toRingHom).map
     e.toRingEquiv.toRingHom
 rw [vj]
 congr 1
 apply MK
 intro P
 change oz (mD k L) P=e (1 ⊗ₜ[k] P)
 simp [e]
private theorem bb2 (I:aU (c9 (Fin 4) k)) (c:L)
  (P:c9 (Fin 4) k) :
  anK I (c ⊗ₜ[k] ox I P) =
    c•ox (a5G I) (oz (mD k L) P) := by
 unfold anK
 simp only [AlgEquiv.trans_apply,Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
  Ideal.quotientEquivAlg_mk,MvPolynomial.algebraTensorAlgEquiv_tmul]
 exact map_smul (t6 L (a5G I)) c _
private theorem ebg (I:aU (c9 (Fin 4) k)) (p:cy) :
    lV L (dO (a5G (L:=L) I) p)=lV k (dO I p) := by
  classical
  let W:=dO I p
  let V:=dO (a5G (L:=L) I) p
  let f :L ⊗[k] W →ₗ[L] c9 (Fin 4) L ⧸ a5G I :=
    (anK I).toLinearEquiv.toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor L L W.subtype)
  have hcalc (c:L) (z :W) :f (c ⊗ₜ[k] z)=anK I (c ⊗ₜ[k] z.val) :=rfl
  have hinj:pQ f :=(anK I).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap W.subtype Up)
  have hrange :LinearMap.range f=V:= by
    apply qM
    · rintro _ ⟨z,rfl⟩
      induction z using TensorProduct.inductionOn with
      | tmul c z =>
        obtain ⟨P,hP,he⟩:=z.property
        have hval :ox I P=z.val :=he
        rw [hcalc,← hval,bb2]
        apply V.smul_mem
        refine ⟨_,?_,rfl⟩
        intro e he
        exact hP (NW (mD k L) P he)
      | add x y hx hy=>simpa only [map_add] using V.add_mem hx hy
    · change dO (a5G (L:=L) I) p≤_
      unfold dO
      rw [Il,Submodule.map_span,Submodule.span_le]
      rintro _ ⟨_,⟨e,he,rfl⟩,rfl⟩
      let z :W:=⟨ox I (qG e 1),
        ⟨qG e 1,by
          rw [Il]
          exact Submodule.subset_span ⟨e,he,rfl⟩,rfl⟩⟩
      refine ⟨(1 :L) ⊗ₜ[k] z,?_⟩
      rw [hcalc,show z.val=ox I (qG e 1) from rfl,bb2]
      simp [MvPolynomial.map_monomial]
  let e :=(LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hrange)
  exact e.finrank_eq.symm.trans Module.finrank_baseChange
end ScalarExtension
private abbrev bHI (aI:aU lz) (p:cy) :=
 aI.comap (uW ov (nE p)).toRingHom
private abbrev hilbertPoly (aI:aU lz) (p:cy) :=
 Ok (bHI aI p)
private theorem emX (aI:aU lz) {p:cy}
    (hp:bF p) (n:ℕ) :
    affineHilbertFunction (bHI aI p) n =
      lV ov (dO aI (p.scale n)) := by
  let φ:=(t6 ov aI).comp (uW ov (nE p))
  have hker :p7 φ.toRingHom=bHI aI p:= by
    ext x
    simp [φ,Mj,Ideal.mem_comap,MS]
  let j:=Ideal.kerLiftAlg φ
  let V:=quotientDegreeLE (p7 φ.toRingHom) n
  have hmap :V.map j.toLinearMap=dO aI (p.scale n) := by
    change ((FQ (nE p) ov n).map
      (t6 _ _).toLinearMap).map _ = _
    rw [← Nj,show j.toLinearMap.comp (t6 _ _).toLinearMap =
      φ.toLinearMap from rfl]
    change (FQ (nE p) ov n).map
      ((t6 ov aI).toLinearMap.comp
        (uW ov (nE p)).toLinearMap)= _
    rw [Nj,c0M hp]
    rfl
  rw [← hker]
  exact (yQ _ (Ideal.kerLiftAlg_injective φ) V).finrank_eq.trans
    (oD (fun S:Eg ov (lz ⧸ aI)=>lV ov S) hmap)
private theorem fXG {k A:Type*}
  [oq k] [oY A] [zm A] {d:ℕ}
  (f :c9 (Fin d) k →+* A) (hf :pQ f) (hfin:f.Finite) :
  (d:WithBot ℕ∞)≤ oy A:= by
 let B:=c9 (Fin d) k
 let algebra :=f.toAlgebra
 let:=algebra
 let faithful:FaithfulSMul B A:=(faithfulSMul_iff_algebraMap_injective _ _).mpr hf
 let finite :pC B A:=hfin
 have hB:oy B=(d:WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,IU]
  simp
 obtain ⟨b,hb,hbheight⟩:=Ideal.exists_isPrime_le_height (n:=d) hB.ge
 obtain ⟨z,hz⟩:=Algebra.IsIntegral.comap_surjective B A (⟨b,hb⟩:xu B)
 have hzb:z.asIdeal.under B=b:=oD PrimeSpectrum.asIdeal hz
 have hzheight:=Ideal.height_under_le_height (R:=B) z.asIdeal
 rw [hzb] at hzheight
 calc
  _≤(z.asIdeal.height:WithBot ℕ∞) :=WithBot.coe_le_coe.mpr (hbheight.trans hzheight)
  _≤ oy A:=S1
private theorem bHJ (aI:aU lz) (hs :aI.IsPrime)
  (hdim:oy (lz ⧸ aI)=2) (p:cy) :
  (hilbertPoly aI p).natDegree≤2 := by
 let:=hs
 obtain ⟨d,f,hf,hfin⟩ :=
  exists_finite_inj_algHom_of_fg ov (lz ⧸ aI)
 have hdeg:=natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective f hfin hf
 rw [Nat.card_fin] at hdeg
 have hd₀:=fXG f.toRingHom hf hfin
 rw [hdim] at hd₀
 have hd:d≤2 := by exact_mod_cast hd₀
 let f₀:=uW ov (nE p)
 have hmono:pQ (Fz aI f₀ p9) :=
  Ideal.quotientMap_injective (I:=aI) (f :=f₀.toRingHom)
 exact (natDegree_affineHilbertPolynomial_le_of_injective _ hmono).trans (hdeg.trans_le hd)
private theorem cbF {k :Type*} [oq k] (I:aU (c9 (Fin 4) k)) {p q:cy}
  (hb:p.b≤q.b) (hj:p.j≤q.j) (ht:p.t≤q.t) :
  dO I p≤dO I q:= by
 apply Vq
 apply restrictSupport_mono
 intro e he
 exact ⟨he.1.trans (p6 6 hb),he.2.1.trans (p6 6 hj),
  he.2.2.trans (p6 6 ht)⟩
private theorem cCC {k :Type*} [oq k] (I:aU (c9 (Fin 4) k))
   {p:cy} (hp:vE p) (q:cy) (N :ℕ) :
   ∃ s :ℕ,∀ n:ℕ,
     dO I (p.scale n)≤dO I ((p.scale n).plus (q.scale N)) ∧
     dO I ((p.scale n).plus (q.scale N))≤dO I (p.scale (n+s)) := by
 let s :=N*(q.b+q.j+q.t)
 have hpb:=hp.1.1
 have hpj:=hp.1.2
 have hpt:=hp.2
 have hb:N*q.b≤ s*p.b :=
   (Nat.mul_le_mul_left N (by omega :q.b≤q.b+q.j+q.t)).trans
     (Ea  s (by omega))
 have hj:N*q.j≤ s*p.j :=
   (Nat.mul_le_mul_left N (by omega :q.j≤q.b+q.j+q.t)).trans
     (Ea  s (by omega))
 have ht:N*q.t≤ s*p.t :=
   (Nat.mul_le_mul_left N (by omega :q.t≤q.b+q.j+q.t)).trans
     (Ea  s hp.2)
 refine ⟨s,fun n=>⟨cbF I (t9 ..) (t9 ..)
   (t9 ..),cbF I ?_ ?_ ?_⟩⟩
 · simpa [pG,oK,yJ] using zS hb (n*p.b)
 · simpa [pG,oK,yJ] using zS hj (n*p.j)
 · simpa [pG,oK,yJ] using zS ht (n*p.t)
private theorem fU5 (H :ℕ→ℕ→ℚ) (d:ℚ) (N :ℕ)
   (hd : ∀ i j:ℕ,N≤ i→N≤j →
     H (i+1) (j+1) - H i (j+1) - H (i+1) j+H i j=d) :
   ∀ i j:ℕ,
     H (N+i) (N+j)+H N N=H (N+i) N+H N (N+j)+d*(i:ℚ)*(j:ℚ) := by
 intro i
 induction i with
 | zero=>intro j; simp [add_comm]
 | succ i ih =>
   intro j
   induction j with
   | zero=>simp
   | succ j ihj =>
     have hstep:=hd (N+i) (N+j) (by omega) (by omega)
     have h₁:=ih (j+1)
     have h₂:=ih j
     simp only [← uJ,qy ,vk] at h₁ ihj ⊢
     linear_combination hstep+h₁+ihj - h₂
private def shift (P:ℚ[X]) (n:ℕ) :ℚ[X] :=
 P.comp (pU +Polynomial.C (n:ℚ))
private theorem asl (P:ℚ[X]) (n:ℕ) :
  (shift P n).natDegree≤P.natDegree := by
 have hh:=Polynomial.natDegree_comp_le (p:=P) (q:=pU +Polynomial.C (n:ℚ))
 rw [VC,zi] at hh
 exact hh
private theorem aXJ (P:ℚ[X]) (n:ℕ) (h:P.natDegree≤2) :
   (shift P n).coeff 2=P.coeff 2 := by
 by_cases he :P.natDegree=2
 · have hl:P.leadingCoeff=P.coeff 2 := by rw [← Polynomial.coeff_natDegree,he]
   have hh:=Polynomial.coeff_comp_degree_mul_degree (p:=P)
     (q:=pU +Polynomial.C (n:ℚ)) (by rw [VC ]; decide)
   rw [he,VC ,Polynomial.leadingCoeff_X_add_C,zi ,
     one_pow,zi ,hl] at hh
   exact hh
 · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((asl P n).trans_lt (by omega)),
     Polynomial.coeff_eq_zero_of_natDegree_lt (by omega :P.natDegree<2)]
private theorem a5e (a h:cy) (n:ℕ) :
  (a.scale n).plus (h.scale 0)=a.scale n:= by
 cases a
 cases h
 simp [pG,oK]
private theorem a7U (a h:cy) (n:ℕ) :
  (a.scale 0).plus (h.scale n)=h.scale n:= by
 cases a
 cases h
 simp [pG,oK]
private theorem cbX (a h:cy) :a.plus h=h.plus a := by
 cases a
 cases h
 simp [oK,JW]
private theorem bNh (a h:cy) (n:ℕ) :
  (a.plus h).scale n=(a.scale n).plus (h.scale n) := by
 cases a
 cases h
 simp [pG,oK,Mw]
private def bgb {k :Type*} [oq k] (I:aU (c9 (Fin 4) k))
  (p:cy) :ℕ :=
 lV k (dO I p)
private theorem bFz (aI:aU lz) (a h:cy)
  {p:cy} (hp:bF p) :
  ∃ M:ℕ,∀ n≥M,(hilbertPoly aI p).eval (n:ℚ) =
    (bgb (gN aI a h) (p.scale n) :ℚ) := by
 obtain ⟨M,hM⟩:=exists_eval_affineHilbertPolynomial (bHI aI p)
 exact ⟨M,fun n hn=> by
  rw [hM n hn,emX aI hp n]
  unfold bgb
  exact_mod_cast (ebg (L:=Coeff a h) aI (p.scale n)).symm⟩
theorem BE (aI:aU lz) (a h:cy) (hs :aI.IsPrime)
    (hdim:oy (lz ⧸ aI)=2) (ha :vE a) (hh:vE h)
    (hmix : ∃ N :ℕ,∀ i j:ℕ,N≤ i→N≤j →
      (lV (Coeff a h) (AL aI a h (i+1) (j+1)) :ℚ) -
        (lV (Coeff a h) (AL aI a h i (j+1)) :ℚ) -
        (lV (Coeff a h) (AL aI a h (i+1) j) :ℚ) +
        (lV (Coeff a h) (AL aI a h i j) :ℚ) =
        (Ux aI (a.scale 6) (h.scale 6) :ℚ)) :
    (Ux aI (a.scale 6) (h.scale 6) :ℚ) =
      aFi aI (a.plus h)-aFi aI a-aFi aI h:= by
  let I:=gN aI a h
  let H (i j:ℕ) :ℚ :=
    bgb (gN aI a h) ((a.scale i).plus (h.scale j))
  let d:ℚ:=Ux aI (a.scale 6) (h.scale 6)
  obtain ⟨N,hN⟩:=hmix
  have hrect :=fU5 H d N hN
  obtain ⟨r,hr⟩:=cCC I ha h N
  obtain ⟨s,ht⟩:=cCC I hh a N
  have hre (n:ℕ) :H n 0≤H n N∧H n N≤H (n+r) 0:= by
    simp only [H,a5e]
    unfold bgb
    exact ⟨by exact_mod_cast Submodule.finrank_mono (hr n).1,
      by exact_mod_cast Vs  (hr n).2⟩
  have hse (n:ℕ) :H 0 n≤H N n∧H N n≤H 0 (n+s) := by
    simp only [H,a7U]
    rw [cbX (a.scale N) (h.scale n)]
    unfold bgb
    exact ⟨by exact_mod_cast Submodule.finrank_mono (ht n).1,
      by exact_mod_cast Vs  (ht n).2⟩
  let P:=hilbertPoly aI a
  let Q:=hilbertPoly aI h
  let R:=hilbertPoly aI (a.plus h)
  obtain ⟨MP,hMP⟩:=bFz aI a h ha.1
  obtain ⟨MQ,hMQ⟩:=bFz aI a h hh.1
  obtain ⟨MR,hMR⟩:=bFz aI a h (Nc ha.1 hh.1)
  have hPe (n:ℕ) (hn:MP≤n) :P.eval (n:ℚ)=H n 0:= by
    simpa only [P,H,a5e] using hMP n hn
  have hQe (n:ℕ) (hn:MQ≤n) :Q.eval (n:ℚ)=H 0 n:= by
    simpa only [Q,H,a7U] using hMQ n hn
  have hRe (n:ℕ) (hn:MR≤n) :R.eval (n:ℚ)=H n n:= by
    simpa only [R,H,bNh] using hMR n hn
  have hshift (A:ℚ[X]) (b n:ℕ) :
      (shift A b).eval (n:ℚ)=A.eval ((n+b:ℕ) :ℚ) := by
    simp [shift,Pc,qy]
  let C0:=qJ (H N N)
  let S:=qJ d*pU ^2
  let lower :=shift P N+shift Q N+S - C0
  let upper :=shift P (N+r)+shift Q (N+s)+S - C0
  let diag:=shift R N
  have hbounds : ∀ᶠ n:ℕ in Filter.atTop,
      lower.eval (n:ℚ)≤diag.eval (n:ℚ)∧diag.eval (n:ℚ)≤upper.eval (n:ℚ) := by
    refine Filter.eventually_atTop.mpr ⟨max MP (max MQ MR),fun n hn => ?_⟩
    have hL:=hre (N+n)
    have hU:=hse (N+n)
    have hrec:=hrect n n
    have hnP:MP≤n+N := by omega
    have hnQ:MQ≤n+N := by omega
    have hnR:MR≤n+N := by omega
    have hnPr :MP≤n+(N+r) := by omega
    have hnQs :MQ≤n+(N+s) := by omega
    simp only [lower,upper,diag,C0,S,Polynomial.eval_sub,TH,
      Qy ,NY ,G0 ,hshift,
      hPe _ hnP,hQe _ hnQ,hRe _ hnR,hPe _ hnPr,hQe _ hnQs,pow_two]
    rw [show n+N=N+n by omega,show n+(N+r)=N+n+r by omega,
      show n+(N+s)=N+n+s by omega]
    exact ⟨by nlinarith only [hL.1,hU.1,hrec],by nlinarith only [hL.2,hU.2,hrec]⟩
  have hp:=bHJ aI hs hdim a
  have hq:=bHJ aI hs hdim h
  have hd:=bHJ aI hs hdim (a.plus h)
  have hdeg (i j:ℕ) : (shift P i+shift Q j+S - C0).natDegree≤2 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply t8
    · apply (JK _ _).trans
      apply t8
      · exact (JK _ _).trans
          (t8 ((asl P i).trans hp) ((asl Q j).trans hq))
      · exact OJ _ _
    · simp [C0]
  have hlo:=G7
    (hdeg N N) ((asl R N).trans hd) (hbounds.mono fun _ h=>h.1)
  have hhi:=G7
    ((asl R N).trans hd) (hdeg (N+r) (N+s)) (hbounds.mono fun _ h=>h.2)
  have hc (i j:ℕ) : (shift P i+shift Q j+S - C0).coeff 2=P.coeff 2+Q.coeff 2+d:= by
    simp [S,C0,aXJ P i hp,aXJ Q j hq]
  change (shift P N+shift Q N+S - C0).coeff 2≤(shift R N).coeff 2 at hlo
  change (shift R N).coeff 2≤(shift P (N+r)+shift Q (N+s)+S - C0).coeff 2 at hhi
  rw [hc,aXJ R N hd] at hlo
  rw [hc,aXJ R N hd] at hhi
  change d=R.coeff 2 - P.coeff 2 - Q.coeff 2
  linarith
private abbrev a3f (aI:aU lz) (a h:cy) (i j:ℕ) :=
 (AL aI a h i j).map (Va aI a h).toLinearMap
private theorem bZn (aI:aU lz) (a h:cy)
  {i j i' j' : ℕ} (hi:i≤ i') (hj:j≤j') :
  a3f aI a h i j≤a3f aI a h i' j' := by
 apply Vq
 exact cbF _ (GB (sH _ hi) (sH _ hj))
  (GB (sH _ hi) (sH _ hj))
  (GB (sH _ hi) (sH _ hj))
private theorem fU6 (H :ℕ→ℕ→ℚ) (d:ℚ) (N :ℕ)
    (hle : ∀ i j:ℕ,N≤ i→N≤j →
      d≤H (i+1) (j+1) - H i (j+1) - H (i+1) j+H i j) :
    ∀ i j:ℕ,H (N+i) N+H N (N+j)+d*(j:ℚ)*(i:ℚ) ≤
      H (N+i) (N+j)+H N N := by
  have vertical (i j:ℕ) :
      d*(j:ℚ)≤H (N+i+1) (N+j) - H (N+i) (N+j) -
        H (N+i+1) N+H (N+i) N := by
    induction j with
    | zero=>simp
    | succ j hj =>
      have hstep:=hle (N+i) (N+j) (by omega) (by omega)
      simp only [← uJ,qy ,vk,mul_add,zi]
      linarith only [hj,hstep]
  intro i j
  induction i with
  | zero=>simp [add_comm]
  | succ i hi =>
    have hstep:=vertical i j
    simp only [← uJ,qy ,vk,mul_add,zi]
    linarith only [hi,hstep]
theorem d4V (aI:aU lz) (a h:cy)
    (hprime :aI.IsPrime) (hdim:oy (lz ⧸ aI)=2)
    (ha :vE a) (hh:vE h) (N :ℕ)
    (hdiff : ∀ i j:ℕ,N≤ i→N≤j →
      (lV (Coeff a h) (AL aI a h (i+1) (j+1)) :ℚ) -
        (lV (Coeff a h) (AL aI a h i (j+1)) :ℚ) -
        (lV (Coeff a h) (AL aI a h (i+1) j) :ℚ) +
        (lV (Coeff a h) (AL aI a h i j) :ℚ) =
        (lV (Coeff a h)
          ((AL aI a h (i+1) (j+1)).map (Va aI a h).toLinearMap) :ℚ)) :
    ∃ M:ℕ,∀ i j:ℕ,M≤ i→M≤j →
      (AL aI a h i j).map (Va aI a h).toLinearMap = ⊤ := by
  classical
  let H (i j:ℕ) :ℚ :=
    bgb (gN aI a h) ((a.scale i).plus (h.scale j))
  let E (n:ℕ) :=lV (Coeff a h) (a3f aI a h n n)
  let R:=hilbertPoly aI (a.plus h)
  obtain ⟨MR,hMR⟩:=bFz aI a h (Nc ha.1 hh.1)
  have hRe (n:ℕ) (hn:MR≤n) :R.eval (n:ℚ)=H n n:= by
    simpa only [R,H,bNh] using hMR n hn
  have hr :=bHJ aI hprime hdim (a.plus h)
  have hbound (k :ℕ) : (E k :ℚ)≤R.coeff 2 := by
    let T:=max N k
    have hTk :k≤T:=sI _ _
    have hTN :N≤T:=uh _ _
    have hl (i j:ℕ) (hi:T≤ i) (hj:T≤j) :
        (E k :ℚ)≤H (i+1) (j+1) - H i (j+1) - H (i+1) j+H i j:= by
      have heq :H (i+1) (j+1) - H i (j+1) - H (i+1) j+H i j =
          (lV (Coeff a h) (a3f aI a h (i+1) (j+1)) :ℚ) :=
        hdiff i j (hTN.trans hi) (hTN.trans hj)
      rw [heq]
      exact_mod_cast Vs
        (bZn aI a h (hTk.trans (hi.trans (t5 _)))
          (hTk.trans (hj.trans (t5 _))))
    have hev : ∀ᶠ n:ℕ in Filter.atTop,
        (qJ (E k :ℚ)*pU ^2).eval (n:ℚ) ≤
          (shift R T+Polynomial.C (H T T)).eval (n:ℚ) := by
      refine Filter.eventually_atTop.mpr ⟨MR,fun n hn => ?_⟩
      have hrec:=fU6 H (E k :ℚ) T hl n n
      have hnonneg (i j:ℕ) :0≤H i j:=Nat.cast_nonneg _
      have hRn:=hRe (T+n) (by omega)
      simp only [shift,Pc,TH,G0 ,
        Qy ,Polynomial.eval_pow,NY ,← qy]
      rw [JW n T,hRn,pow_two]
      nlinarith only [hrec,hnonneg (T+n) T,hnonneg T (T+n)]
    have hdeg: (shift R T+Polynomial.C (H T T)).natDegree≤2 :=
      (JK _ _).trans <| t8 ((asl R T).trans hr) (by simp)
    have hcompare :=G7
      (OJ (E k :ℚ) 2) hdeg hev
    simpa [Polynomial.coeff_C_mul_X_pow,aXJ R T hr] using hcompare
  obtain ⟨B,hB⟩:=exists_nat_gt (R.coeff 2)
  have hB' (n:ℕ) :E n≤B:= by exact_mod_cast (hbound n).trans hB.le
  let S:=(pz (B+1)).filter fun k => ∃ n,E n=k
  have hmem (n:ℕ) :E n∈S :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (NX (hB' n)),⟨n,rfl⟩⟩
  have hS:S.Nonempty :=⟨E 0,hmem 0⟩
  obtain ⟨M,hM⟩:=(Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hmax (n:ℕ) :E n≤E M:= by
    rw [hM]
    exact Finset.le_max' S (E n) (hmem n)
  have htop:a3f aI a h M M = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n,hx⟩:=KI (ke aI a h) x
    let m:=max n M
    have hm:a3f aI a h M M=a3f aI a h m m :=
      Submodule.eq_of_le_of_finrank_le
        (bZn aI a h (sI _ _) (sI _ _)) (hmax m)
    rw [hm]
    exact eQu aI a h ha (uh _ M) hx
  exact ⟨M,fun i j hi hj=>top_unique (htop ▸ bZn aI a h hi hj)⟩
end
end YU
end
section
namespace YU
noncomputable section
open aR dN GJ E6
def c1 :Prop :=
  ∀ (aI:aU lz) (a h:cy),
    aI.IsPrime→ oy (lz ⧸ aI)=2 →
    vE a→vE h →
    pQ (leftMul aI a h)∧pQ (rightMul aI a h) ∧
    ∃ N :ℕ,∀ i j:ℕ,N≤ i→N≤j →
      (AL aI a h i (j+1)).map (leftMul aI a h) ⊓
        (AL aI a h (i+1) j).map (rightMul aI a h) =
      (AL aI a h i j).map ((leftMul aI a h).comp (rightMul aI a h))
def c2 :Prop :=
  ∀ (aI:aU lz) (a h:cy),
    aI.IsPrime→ oy (lz ⧸ aI)=2 →
    vE a→vE h →
    ∃ N :ℕ,∀ i j:ℕ,N≤ i→N≤j →
      AL aI a h (i+1) (j+1) ⊓ vl (Va aI a h).toLinearMap =
      (AL aI a h i (j+1)).map (leftMul aI a h) ⊔
        (AL aI a h (i+1) j).map (rightMul aI a h)
theorem of_children (h1 :c1) (h2 :c2) :E6.c1 := by
 intro aI a h hprime hdim ha hh
 obtain ⟨hl,hr,N₁,hN₁⟩:=h1 aI a h hprime hdim ha hh
 obtain ⟨N₂,hN₂⟩:=h2 aI a h hprime hdim ha hh
 let N :=max N₁ N₂
 have gI (i j:ℕ) (hi:N≤ i) (hj:N≤j) :=
   eAQ aI a h i j hl hr
     (hN₁ i j ((uh _ _).trans hi) ((uh _ _).trans hj))
     (hN₂ i j ((sI _ _).trans hi) ((sI _ _).trans hj))
 obtain ⟨M,hM⟩:=d4V aI a h hprime hdim ha hh N gI
 apply BE aI a h hprime hdim ha hh
 refine ⟨max N M,fun i j hi hj => ?_⟩
 have hcut:=gI i j ((uh _ _).trans hi) ((uh _ _).trans hj)
 rw [hM (i+1) (j+1) ((sI _ _).trans (hi.trans (t5 _)))
   ((sI _ _).trans (hj.trans (t5 _))),finrank_top] at hcut
 exact hcut
end
end YU
end
section
set_option maxHeartbeats 500000
namespace ap6
noncomputable section
open aR dN BO lB GJ
 E6 YU MvPolynomial
open scoped Pointwise
variable {k :Type*} [oq k]
abbrev Affine (I:aU (c9 (Fin 4) k)) :=
 c9 (Fin 4) k ⧸ I
abbrev box (I:aU (c9 (Fin 4) k)) (a h:cy) (d:ℕ×ℕ) :=
 dO I ((a.scale d.1).plus (h.scale d.2))
theorem bJw {I:aU (c9 (Fin 4) k)} {a h:cy}
   {d:ℕ×ℕ} {e :Fin 4 →₀ ℕ} (he :e∈nE ((a.scale d.1).plus (h.scale d.2)))
   (c:k) :ox I (qG e c)∈box I a h d :=
 ⟨_,(monomial_mem_restrictSupport k).mpr (Or.inl he),rfl⟩
private theorem dcb (I:aU (c9 (Fin 4) k)) (a h:cy)
  (d:ℕ×ℕ) (c:k) :mD k (Affine I) c∈box I a h d:= by
 change ox I (nq c)∈box I a h d
 simpa only [monomial_zero'] using
  (bJw (I:=I) (d:=d) (brA ((a.scale d.1).plus (h.scale d.2))) c)
theorem c2s (I:aU (c9 (Fin 4) k)) (a h:cy)
  (d:ℕ×ℕ) : (1 :Affine I)∈box I a h d:= by
 simpa only [map_one] using dcb I a h d 1
theorem bmu {I:aU (c9 (Fin 4) k)} {a h:cy}
  {d e :ℕ×ℕ} {x y :Affine I} (hx :x∈box I a h d) (hy :y∈box I a h e) :
  x*y∈box I a h (d+e) := by
 obtain ⟨p,hp,rfl⟩:=hx
 obtain ⟨q,hq,rfl⟩:=hy
 refine ⟨p*q,?_,pL (ox I) _ _⟩
 have hm:=Submodule.mul_mem_mul hp hq
 rw [← restrictSupport_add k] at hm
 refine restrictSupport_mono k ?_ hm
 rintro _ ⟨u,hu,v,hv,rfl⟩
 obtain ⟨hub,huj,hut⟩:=hu
 obtain ⟨hvb,hvj,hvt⟩:=hv
 simp only [nE,Set.mem_ofPred_eq,rU,PA,
  pG,oK,Prod.fst_add,Prod.snd_add,yJ,Mw] at *
 exact ⟨by omega,by omega,by omega⟩
def yH (I:aU (c9 (Fin 4) k)) (a h:cy) :
    Subalgebra k (GY (Affine I) (ℕ×ℕ)) where
  carrier := {p | ∀ d,p.coeff d∈box I a h d}
  zero_mem' d:=(box I a h d).zero_mem
  add_mem' hx hy d:=(box I a h d).add_mem (hx d) (hy d)
  one_mem' := by
    classical
    intro d
    change (qx 0 1 :GY (Affine I) (ℕ×ℕ)).coeff d∈_
    rw [zE,Ef]
    split
    · exact c2s I a h d
    · exact (box I a h d).zero_mem
  mul_mem' {p q} hp hq:= by
    classical
    intro d
    change (p*q).coeff d∈box I a h d
    simp only [AddMonoidAlgebra.coeff_mul,Finsupp.sum]
    refine (box I a h d).sum_mem fun i _=>(box I a h d).sum_mem fun j _ => ?_
    split
    · rename_i he
      rw [← he]
      exact bmu (hp i) (hq j)
    · exact (box I a h d).zero_mem
  algebraMap_mem' c:= by
    classical
    intro d
    change (qx 0 (mD k (Affine I) c)).coeff d∈_
    rw [zE,Ef]
    split
    · exact dcb I a h d c
    · exact (box I a h d).zero_mem
def homogeneous {I:aU (c9 (Fin 4) k)} {a h:cy} (d:ℕ×ℕ)
    (x :Affine I) (hx :x∈box I a h d) :yH I a h :=
  ⟨qx d x,by
    classical
    intro e
    change (qx d x).coeff e∈box I a h e
    rw [zE,Ef]
    split
    · rename_i he
      subst e
      exact hx
    · exact (box I a h e).zero_mem⟩
@[simp] theorem aJW {I:aU (c9 (Fin 4) k)} {a h:cy}
   {d:ℕ×ℕ} {x :Affine I} (hx :x∈box I a h d) :
   (yH I a h).val (homogeneous d x hx)=qx d x :=rfl
theorem a5e (a h:cy) : (a.scale 1).plus (h.scale 0)=a := by
 cases a
 cases h
 simp [pG,oK]
theorem a7U (a h:cy) : (a.scale 0).plus (h.scale 1)=h:= by
 cases a
 cases h
 simp [pG,oK]
def aaX (I:aU (c9 (Fin 4) k)) (a h:cy) (e :nE a) :
    yH I a h :=
  homogeneous (1,0) (ox I (qG e.val 1))
    (bJw (by simpa only [a5e] using e.property) 1)
def abh (I:aU (c9 (Fin 4) k)) (a h:cy) (e :nE h) :
    yH I a h :=
  homogeneous (0,1) (ox I (qG e.val 1))
    (bJw (by simpa only [a7U] using e.property) 1)
def Wi (I:aU (c9 (Fin 4) k)) (a h:cy)
    (e :nE a×nE h) :yH I a h :=
  aaX I a h e.1*abh I a h e.2
def irrelevant (I:aU (c9 (Fin 4) k)) (a h:cy) :aU (yH I a h) :=
 nX (FK (Wi I a h))
def shift (I:aU (c9 (Fin 4) k)) (a h:cy) :yH I a h :=
 homogeneous (1,1) 1 (c2s I a h _)
theorem dcy {σ:Type*} (p:cy) (f :uL (p.scale 6)→σ) :
   Uq (p.scale 6) f∈C5 _ (nE p) := by
 classical
 unfold Uq
 apply Sd
 intro m hm
 let e :Fin 4 →₀ ℕ:=Finsupp.equivFunOnFinite.symm fun i=>(m i).val
 have he :e∈nE p:=(bI6 (p.scale 6) m).mpr hm
 have hprod: (∏ i:Fin 4,lI i^(m i).val :c9 (Fin 4)
     (FractionRing (c9 σ ov)))=qG e 1 := by
   rw [monic_monomial_eq,Finsupp.prod_fintype _ _ (by simp)]
   rfl
 rw [hprod,C_mul_monomial]
 exact (monomial_mem_restrictSupport _).mpr (Or.inl he)
abbrev rT (aI:aU lz) (a h:cy) :=gN aI a h
abbrev Rees (aI:aU lz) (a h:cy) :=yH (rT aI a h) a h
abbrev aDD (aI:aU lz) (a h:cy) :=
 ox (rT aI a h) (leftSection a h)
abbrev aEC (aI:aU lz) (a h:cy) :=
 ox (rT aI a h) (rightSection a h)
theorem cXa (aI:aU lz) (a h:cy) :
  aDD aI a h∈box (rT aI a h) a h (1,0) := by
 rw [show box (rT aI a h) a h (1,0)=dO (rT aI a h) a
  from oD (dO (rT aI a h)) (a5e a h)]
 exact ⟨_,dcy a wA,rfl⟩
theorem c8K (aI:aU lz) (a h:cy) :
  aEC aI a h∈box (rT aI a h) a h (0,1) := by
 rw [show box (rT aI a h) a h (0,1)=dO (rT aI a h) h
  from oD (dO (rT aI a h)) (a7U a h)]
 exact ⟨_,dcy h qU,rfl⟩
def aOt (aI:aU lz) (a h:cy) :Rees aI a h :=
 homogeneous (1,0) (aDD aI a h) (cXa aI a h)
def aPV (aI:aU lz) (a h:cy) :Rees aI a h :=
 homogeneous (0,1) (aEC aI a h) (c8K aI a h)
def aVk (aI:aU lz) (a h:cy) :aU (Rees aI a h) :=
 nX {aOt aI a h,aPV aI a h}
def b51 (aI:aU lz) (a h:cy) :aU (Rees aI a h) :=
 aVk aI a h ⊔ nX ({shift (rT aI a h) a h} : Set (Rees aI a h))
end
end ap6
end
section
set_option maxHeartbeats 600000
namespace ap6
noncomputable section
open aR dN lB GJ
 E6 YU MvPolynomial
private theorem gxr {R:Type*} [oY R] (J P:aU R) (m:ℕ) :
   (J ⊔ P)^m≤J ⊔ P^m:= by
 induction m with
 | zero=>exact le_sup_right
 | succ m ih =>
   rw [pow_succ,pow_succ P]
   refine (SL ih).trans ?_
   rw [Ideal.mul_sup,GF,GF]
   exact sup_le (sup_le (Ideal.mul_le_left.trans Cy)
     (Ideal.mul_le_right.trans Cy))
     (sup_le (Ideal.mul_le_left.trans Cy) le_sup_right)
theorem d4B {R T:Type*} [oY R] [Au R]
    (g:T→R) (J:aU R) (s :R)
    (hg : ∀ t,∃ m:ℕ,g t^m∈J ⊔ nX {s}) :
    ∃ N :ℕ,∀ x∈nX (FK g)^N,(∃ m:ℕ,s^m*x∈J)→x∈J:= by
  let B:=nX (FK g)
  have hb:B≤(J ⊔ nX {s}).radical:= by
    apply Ideal.span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact hg t
  let C:ℕ →o Eg R R :=
    ⟨fun m=>J.colon {s^m},by
      intro i j hij x hx
      simp only [Submodule.mem_colon_singleton,smul_eq_mul] at hx ⊢
      rw [show j=j - i+i by omega,pow_add]
      simpa only [oj x,vh] using J.mul_mem_left (s^(j - i)) (by
        simpa only [oj x] using hx)⟩
  obtain ⟨m,hm⟩:=monotone_stabilizes_iff_noetherian.mpr y5 C
  have hC (i:ℕ) :C i≤C m:= by
    rcases le_total i m with h | h
    · exact C.monotone h
    · exact (hm i h).ge
  obtain ⟨n,hn⟩:=Ideal.exists_pow_le_of_le_radical_of_fg hb B.fg_of_isNoetherianRing
  have hpow:B^(n*m)≤J ⊔ nX {s^m} := by
    rw [pow_mul,← Ideal.span_singleton_pow]
    exact (Ideal.pow_right_mono hn m).trans (gxr J _ m)
  have hmul :B^(n*m)*(C m:aU R)≤J:= by
    refine (SL hpow).trans ?_
    rw [GF]
    refine sup_le Ideal.mul_le_left (Ideal.mul_le.mpr ?_)
    intro p hp x hx
    obtain ⟨t,rfl⟩:=Ideal.mem_span_singleton'.mp hp
    have hx' : x*s^m∈J:=Submodule.mem_colon_singleton.mp hx
    simpa only [vh,oj (s^m) x] using J.mul_mem_left t hx'
  obtain ⟨k,hk⟩:=B.exists_pow_inf_eq_pow_smul (C m)
  refine ⟨k+n*m,fun x hx ⟨i,hi⟩ => ?_⟩
  have hxi:x∈C i:= by
    apply Submodule.mem_colon_singleton.mpr
    change x*s^i∈J
    rwa [oj]
  have h:=hk (k+n*m) (t9 _ _)
  simp only [Ideal.smul_eq_mul,Ideal.mul_top,Nat.add_sub_cancel_left] at h
  have hx' : x∈B^(k+n*m) ⊓ C m:=⟨hx,hC i hxi⟩
  rw [h] at hx'
  exact hmul (Ideal.mul_mono_right inf_le_right hx')
variable {aI:aU lz} {a h:cy}
theorem cI3 (x :Oa aI a h) :
   Va aI a h x=0↔x∈nX {aDD aI a h,aEC aI a h} := by
 obtain ⟨p,rfl⟩:=Lf x
 change ox (ke aI a h) p=0↔_
 have hspan: (nX {leftSection a h,rightSection a h}).map
     (ox (rT aI a h)) =
     nX {aDD aI a h,aEC aI a h} := by
   rw [KH]
   simp
 rw [← hspan,Ideal.mem_quotient_iff_mem_sup,MS ,ke,sup_comm]
private theorem evf (r :Rees aI a h) (i j:ℕ) :
   ((yH (rT aI a h) a h).val (r*aOt aI a h)).coeff (i+1,j+1) =
     leftMul aI a h (r.val.coeff (i,j+1)) := by
 simp only [pL,aOt,aJW]
 rw [show (i+1,j+1)=(i,j+1)+(1,0) by rfl,
   VO ]
 exact oj _ _
private theorem fXz (r :Rees aI a h) (i j:ℕ) :
   ((yH (rT aI a h) a h).val (r*aPV aI a h)).coeff (i+1,j+1) =
     rightMul aI a h (r.val.coeff (i+1,j)) := by
 simp only [pL,aPV,aJW]
 rw [show (i+1,j+1)=(i+1,j)+(0,1) by rfl,
   VO ]
 exact oj _ _
theorem cUP (i j:ℕ) (x :Oa aI a h)
    (hx :x∈box (rT aI a h) a h (i+1,j+1)) :
    homogeneous (I:=rT aI a h) (a :=a) (h:=h) (i+1,j+1) x hx ∈
        aVk aI a h ↔
      x∈(AL aI a h i (j+1)).map (leftMul aI a h) ⊔
        (AL aI a h (i+1) j).map (rightMul aI a h) := by
  constructor
  · intro hxJ
    obtain ⟨r,t,he⟩:=Ideal.mem_span_pair.mp hxJ
    have hc:=oD (fun z :Rees aI a h =>
      ((yH (rT aI a h) a h).val z).coeff (i+1,j+1)) he
    change ((yH (rT aI a h) a h).val
      (r*aOt aI a h+t*aPV aI a h)).coeff (i+1,j+1) =
      ((yH (rT aI a h) a h).val
        (homogeneous (i+1,j+1) x hx)).coeff (i+1,j+1) at hc
    rw [wY ,AddMonoidAlgebra.coeff_add,PA,evf,fXz,
      aJW,zE,Oc] at hc
    have hr :r.val.coeff (i,j+1)∈AL aI a h i (j+1) :=
      r.property (i,j+1)
    have ht:t.val.coeff (i+1,j)∈AL aI a h (i+1) j :=
      t.property (i+1,j)
    exact Submodule.mem_sup.mpr ⟨_,RD (f :=leftMul aI a h) hr,
      _,RD (f :=rightMul aI a h) ht,hc⟩
  · intro hm
    obtain ⟨_,⟨y,hy,rfl⟩,_,⟨z,hz,rfl⟩,he⟩:=Submodule.mem_sup.mp hm
    change y∈box (rT aI a h) a h (i,j+1) at hy
    change z∈box (rT aI a h) a h (i+1,j) at hz
    refine Ideal.mem_span_pair.mpr
      ⟨homogeneous (i,j+1) y hy,homogeneous (i+1,j) z hz,KA ?_⟩
    change (yH (rT aI a h) a h).val
      (homogeneous (i,j+1) y hy*aOt aI a h +
        homogeneous (i+1,j) z hz*aPV aI a h) =
      (yH (rT aI a h) a h).val (homogeneous (i+1,j+1) x hx)
    simp only [wY ,pL,aOt,aPV,aJW,
      Gj]
    change qx (i+1,j+1) (y*aDD aI a h) +
      qx (i+1,j+1) (z*aEC aI a h) =
      qx (i+1,j+1) x
    rw [← Kv,← Kv,
      ← wY ,Kv]
    rw [oj y,oj z]
    exact oD (qx (i+1,j+1)) he
private theorem cJM (ha :vE a) {N i j:ℕ} (hi:N≤ i) :
  quotientDegreeLE (rT aI a h) N≤AL aI a h i j:= by
 intro x hx
 obtain ⟨P,hP,rfl⟩:=mem_quotientDegreeLE.mp hx
 have haT:i≤ i*a.t:=Ea i ha.2
 have haJ:3*i≤ i*a.j:= by
  rw [xI 3 i]
  exact p6 _ (by have :=ha.1.2; have :=ha.2; omega)
 have haB:i≤ i*a.b:= by
  exact Ea _ (by have :=ha.1.1; have :=ha.1.2; have :=ha.2; omega)
 refine ⟨P,?_,rfl⟩
 intro e he
 have hd:=(sS he).trans hP
 change e.degree≤N at hd
 rw [G1 ,zg] at hd
 change e 0+e 1+e 2+e 3≤6*(i*a.b+j*h.b) ∧
  e 1+2*e 2 + 3*e 3≤6*(i*a.j+j*h.j) ∧
  e 3≤6*(i*a.t+j*h.t)
 exact ⟨by omega,by omega,by omega⟩
private theorem gKN (n:ℕ) :
   (yH (rT aI a h) a h).val (shift (rT aI a h) a h^n) =
     qx (n,n) 1 := by
 induction n with
 | zero=>simp only [pow_zero,map_one,AddMonoidAlgebra.one_def]; rfl
 | succ n ih =>
   rw [pow_succ,pL,ih]
   change (qx (n,n) 1 :GY
     (Oa aI a h) (ℕ×ℕ))*qx (1,1) 1= _
   rw [Gj,zi ,Prod.mk_add_mk]
theorem d4R (ha :vE a) (i j:ℕ)
   (x :Oa aI a h) (hx :x∈box (rT aI a h) a h (i+1,j+1))
   (hzero :Va aI a h x=0) :
   ∃ n:ℕ,shift (rT aI a h) a h^n *
     homogeneous (i+1,j+1) x hx∈aVk aI a h:= by
 obtain ⟨u,v,he⟩:=Ideal.mem_span_pair.mp ((cI3 x).mp hzero)
 obtain ⟨nu,hu⟩:=KI (rT aI a h) u
 obtain ⟨nv,hv⟩:=KI (rT aI a h) v
 let n:=max nu nv
 let f :Rees aI a h :=
   shift (rT aI a h) a h^n*homogeneous (i+1,j+1) x hx
 have hf : (yH (rT aI a h) a h).val f =
     qx (n+i+1,n+j+1) x := by
   dsimp only [f]
   rw [pL,gKN,aJW,Gj,
     one_mul,Prod.mk_add_mk,uJ,uJ]
 have hfx :x∈box (rT aI a h) a h (n+i+1,n+j+1) := by
   have hc:=f.property (n+i+1,n+j+1)
   change ((yH (rT aI a h) a h).val f).coeff (n+i+1,n+j+1) ∈
     box (rT aI a h) a h (n+i+1,n+j+1) at hc
   simpa only [hf,zE,Oc] using hc
 have hf' : f=homogeneous (n+i+1,n+j+1) x hfx :=KA hf
 refine ⟨n,?_⟩
 change f∈_
 rw [hf',cUP]
 have hui:nu≤n+i:=(uh _ _).trans (t9 _ _)
 have hvi:nv≤n+i+1 :=
   (sI nu nv).trans ((t9 n i).trans (t5 _))
 exact Submodule.mem_sup.mpr ⟨_,⟨u,cJM ha hui hu,rfl⟩,
   _,⟨v,cJM ha hvi hv,rfl⟩,by
     change aDD aI a h*u+aEC aI a h*v=x
     rwa [oj (aDD aI a h) u,oj (aEC aI a h) v]⟩
end
end ap6
end
section
namespace axe
noncomputable section
open aR dN BO
open MvPolynomial
def aeg (h:cy) :lz →+* adi h :=
 oz (mD ov (dV h))
def To (J:aU lz) (h:cy) :aU (adi h) :=
 J.map (aeg h) ⊔ nX {adK h}
def bQW {k :Type} [oq k] (Q:c9 (Fin 4) k) (a :cy) :Prop :=
 Q.totalDegree≤a.b∧Q.weightedTotalDegree Fin.val≤a.j∧Q.degreeOf 3≤a.t
abbrev Jo (k :Type) [oq k] (a :cy) :=
 FractionRing (c9 (uL a) k)
def a3g (k :Type) [oq k] (a :cy) :
    c9 (Fin 4) (Jo k a) :=
  ∑ m∈Bz a,
    nq (mD (c9 (uL a) k) (Jo k a) (lI m)) *
      ∏ i:Fin 4,lI i^(m i).val
def bHl {k :Type} [oq k] (I:aU (c9 (Fin 4) k))
    (a :cy) :ℕ :=
  lV (Jo k a) (c9 (Fin 4) (Jo k a) ⧸
    (I.map (oz (mD k (Jo k a))) ⊔
      nX {a3g k a}))
end
end axe
end
section
set_option maxHeartbeats 800000
namespace ap6
noncomputable section
open aR dN lB GJ
 E6 YU MvPolynomial
def c1 :Prop :=
  ∀ {k :Type} [oq k] (I:aU (c9 (Fin 4) k)) (a h:cy),
    bF a→bF h →
    Au (yH I a h) ∧
    ∀ (i j:ℕ) (x :Affine I) (hx :x∈box I a h (i,j)) (n:ℕ),
      n≤ i→n≤j→homogeneous (i,j) x hx∈irrelevant I a h^n
def c2 :Prop :=
  ∀ (aI:aU lz) (a h:cy),
    aI.IsPrime→ oy (lz ⧸ aI)=2 →
    vE a→vE h →
    ∀ e :nE a×nE h,
      ∃ m:ℕ,Wi (rT aI a h) a h e^m∈b51 aI a h
private theorem enM (aI:aU lz) (a h:cy) (i j:ℕ) :
   (AL aI a h i (j+1)).map (leftMul aI a h) ⊔
     (AL aI a h (i+1) j).map (rightMul aI a h) ≤
   AL aI a h (i+1) (j+1) ⊓ vl (Va aI a h).toLinearMap:= by
 intro x hx
 obtain ⟨_,⟨u,hu,rfl⟩,_,⟨v,hv,rfl⟩,rfl⟩:=Submodule.mem_sup.mp hx
 change u∈box (rT aI a h) a h (i,j+1) at hu
 change v∈box (rT aI a h) a h (i+1,j) at hv
 have hu' := bmu hu (cXa aI a h)
 have hv' := bmu hv (c8K aI a h)
 have hsum:aDD aI a h*u+aEC aI a h*v ∈
     AL aI a h (i+1) (j+1) := by
   rw [oj (aDD aI a h) u,oj (aEC aI a h) v]
   exact (AL aI a h (i+1) (j+1)).add_mem hu' hv'
 refine ⟨hsum,(cI3 _).mpr ?_⟩
 apply Ideal.mem_span_pair.mpr
 refine ⟨u,v,?_⟩
 change u*aDD aI a h+v*aEC aI a h =
   aDD aI a h*u+aEC aI a h*v
 rw [oj u,oj v]
private theorem dzP (aI:aU lz) (a h:cy)
   (hNoeth:Au (Rees aI a h))
   (hchart : ∀ e :nE a×nE h,
     ∃ m:ℕ,Wi (rT aI a h) a h e^m∈b51 aI a h) :
   ∃ N :ℕ,∀ f∈irrelevant (rT aI a h) a h^N,
     (∃ m:ℕ,shift (rT aI a h) a h^m*f∈aVk aI a h) →
     f∈aVk aI a h :=
 @d4B (Rees aI a h) (nE a×nE h)
   y5 hNoeth (Wi (rT aI a h) a h)
   (aVk aI a h) (shift (rT aI a h) a h) hchart
private theorem etJ (aI:aU lz) (a h:cy) (ha :vE a)
    (i j N :ℕ)
    (hpower : ∀ (x :Oa aI a h) (hx :x∈box (rT aI a h) a h (i+1,j+1)),
      homogeneous (i+1,j+1) x hx∈irrelevant (rT aI a h) a h^N)
    (hbound : ∀ f∈irrelevant (rT aI a h) a h^N,
      (∃ m:ℕ,shift (rT aI a h) a h^m*f∈aVk aI a h) →
      f∈aVk aI a h) :
    AL aI a h (i+1) (j+1) ⊓ vl (Va aI a h).toLinearMap ≤
      (AL aI a h i (j+1)).map (leftMul aI a h) ⊔
        (AL aI a h (i+1) j).map (rightMul aI a h) := by
  rintro x ⟨hx,hxzero⟩
  change x∈box (rT aI a h) a h (i+1,j+1) at hx
  apply (cUP i j x hx).mp
  exact hbound _ (hpower x hx) (d4R ha i j x hx hxzero)
theorem of_children (h1 :c1) (h2 :c2) :YU.c2 := by
 intro aI a h hs hdim ha hh
 obtain ⟨hNoeth,hpower⟩:=h1 (rT aI a h) a h ha.1 hh.1
 obtain ⟨N,hbound⟩:=dzP aI a h hNoeth (h2 aI a h hs hdim ha hh)
 refine ⟨N,fun i j hi hj=>qM ?_ (enM aI a h i j)⟩
 exact etJ aI a h ha i j N
  (fun x hx=>hpower (i+1) (j+1) x hx N
    (hi.trans (t5 i)) (hj.trans (t5 j))) hbound
end
end ap6
end
section
namespace aFW
open dN
structure aSw (aI:aU lz) (P:lz) (C:aU lz) :Prop where
 prime :aI.IsPrime
 height:aI.height=2
 proper :P∉aI
 component: (aI ⊔ nX {P}).IsMinimalPrime C
end aFW
end
