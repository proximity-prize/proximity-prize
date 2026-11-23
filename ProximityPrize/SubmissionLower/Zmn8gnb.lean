import Mathlib.RingTheory.PowerSeries.Derivative
import ProximityPrize.SubmissionLower.ZkEhKoc
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, Field → zrb, Finset.range → z4x, Function.Injective → zq4, IsFractionRing.injective → zxb, MvPolynomial.C → znf, MvPolynomial.eval₂ → zSZ, MvPolynomial.eval₂_comp_left → zqI, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.mapRingHom → zhd, Polynomial.mapRingHom_comp → zPl, Polynomial.map_injective → zTo, Polynomial.map_map → zoi, Polynomial.map_mul → zNl, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.constantCoeff → zbO, PowerSeries.constantCoeff_C → zr8, RingHom.ext → zz4
section
namespace qAjZDhd
noncomputable section
open Polynomial
abbrev Physical (k :Type) [zrb k] :=(zpm k)[X]
abbrev Equation (k :Type) [zrb k] :=(Physical k)[X]
abbrev Generic (k :Type) [zrb k] :=RatFunc (FractionRing (zpm k))
variable {k :Type} [zrb k]
def reduce :Physical k →+* k[X] :=zhd zbO
def ek :Physical k →+* Generic k :=
  (algebraMap (FractionRing (zpm k))[X] (Generic k)).comp
    (zhd (algebraMap (zpm k) (FractionRing (zpm k))))
def Lv {S R:Type} [za6 S] [za6 R] [zZE S R]
    (d:Derivation S R R) :Derivation S R[X] R[X] :=
  PolynomialModule.equivPolynomialSelf.compDer d.mapCoeffs
def seedDeriv :Derivation k (Physical k) (Physical k) :=
 Lv (PowerSeries.derivative (R:=k))
def seedPartial (f :Equation k) :Equation k :=Lv seedDeriv f
def physicalPartial (f :Equation k) :Equation k :=
 Lv (Polynomial.derivative' (R:=zpm k)) f
def reference (a :k) :Physical k :=C (zMG a)
def branchPoly (f :Equation k) (g:ℕ) (a :k) :Physical k :=
 f.resultant f.derivative g (g - 1)*f.eval (reference a)
structure LocalMark (k :Type) [zrb k] (p:ℕ) where
 f :Equation k
 g:ℕ
 a :k
 r :Physical k
 s :k[X]
 degree :f.natDegree=g
 two_le :2≤g
 tame :g<p
 branch_nonzero :reduce (branchPoly f g a)≠0
 monic:r.Monic
 physical_tame :r.natDegree<p
 support : ∃ n:ℕ,
   (branchPoly f g a).map (algebraMap (zpm k) (FractionRing (zpm k))) ∣
     (r.map (algebraMap (zpm k) (FractionRing (zpm k))))^n
 root : (f.map reduce).eval s=0
 simple : (f.derivative.map reduce).eval s≠0
 different:s≠C a
variable {p:ℕ}
def LocalMark.denominator (M:LocalMark k p) :Equation k :=
 M.f.derivative*(z7y-Polynomial.C (reference M.a))
def LocalMark.numerator (M:LocalMark k p) (zD:Bool) :Equation k :=
  if zD then
    -C M.r.derivative*seedPartial M.f+C (seedDeriv M.r)*physicalPartial M.f
  else
    -C M.r*seedPartial M.f
def bL9:Physical k →+* AlgebraicClosure (Generic k) :=
 (algebraMap (Generic k) (AlgebraicClosure (Generic k))).comp ek
def RootProduct (M:LocalMark k p) (N Q:Equation k) :Prop :=
  Q.map bL9 =
    ((M.f.map bL9).roots.map fun (y :AlgebraicClosure (Generic k)) =>
      (z7y: (AlgebraicClosure (Generic k))[X]) -
        z1z ((N.map bL9).eval y/(M.denominator.map bL9).eval y)).prod
def yq (s :k[X]) (F:Equation k) :k[X] :=(F.map reduce).eval s
def LocalMark.logValue (M:LocalMark k p) (N :Equation k) :RatFunc k :=
  algebraMap k[X] (RatFunc k) (yq M.s N) /
    algebraMap k[X] (RatFunc k) (yq M.s M.denominator)
def WeightBound (r :ℕ) (Q:Equation k) :Prop :=
 ∀ i<Q.natDegree,(Q.coeff i).natDegree≤ r*(Q.natDegree - i)
end
end qAjZDhd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qAjZDhd
noncomputable section
open Polynomial
open P5 (K p)
open qL2osVa
open cu (L j9)
open DQ (DT)
open Cu (sQ oO zT)
section Derivatives
variable {S R:Type} [za6 S] [za6 R] [zZE S R]
theorem coeffDeriv_eval (d:Derivation S R R) (x :R) (f :R[X]) :
  d (f.eval x)=(Lv d f).eval x+f.derivative.eval x*d x := by
 have h:=PolynomialModule.aeval_equivPolynomial (d.mapCoeffs f) x
 have he : (Lv d f).eval x=PolynomialModule.eval x (d.mapCoeffs f) := by
  simpa [Lv,aeval_def] using h
 rw [d.apply_eval_eq,he,smul_eq_mul]
end Derivatives
section ArcMap
variable {C₀:sQ} [Fact (Irreducible C₀)] {C:MarkedSheet C₀} {γ:K}
private abbrev φ:Series →+* SeriesField:=algebraMap Series SeriesField
private theorem φ_injective :zq4 φ:=zxb _ _
abbrev arcParam (A:Arc C γ) :DT C.sheet.n →+* Series :=
 MvPolynomial.eval₂Hom zMG A.parameter
def arcEquation (A:Arc C γ) :Equation L :=
 C.sheet.bY.equation.map (zhd (arcParam A))
private theorem arc_generic (A:Arc C γ) :φ.comp (arcParam A) =
  A.embedding.comp C.genericParam:= by
 apply zz4
 intro q
 change φ (zSZ zMG A.parameter q) =
  A.embedding (zSZ (zT C₀) C.sheet.bY.coordinate q)
 rw [zqI,zqI]
 exact MvPolynomial.eval₂Hom_congr
  (zz4 fun a=>(A.constant_eq a).symm) (funext fun i=>(A.parameter_eq i).symm) rfl
private theorem arc_specialize (A:Arc C γ) :
  PowerSeries.constantCoeff.comp (arcParam A)=MvPolynomial.eval (C.sheet.parameter γ) := by
 apply zz4
 intro q
 change zbO (zSZ zMG A.parameter q) =
  zSZ (RingHom.id L) (C.sheet.parameter γ) q
 rw [zqI]
 exact MvPolynomial.eval₂Hom_congr
  (zz4 zr8) (funext A.parameter_value) rfl
theorem arcEquation_specialize (A:Arc C γ) :
  (arcEquation A).map reduce=C.markedEquation γ:= by
 rw [arcEquation,reduce,zoi,zPl,arc_specialize]
 rfl
private theorem arcEquation_degree (A:Arc C γ) : (arcEquation A).natDegree=C.g:= by
 let i:=zhd φ
 let j:=zhd A.embedding
 have he : (arcEquation A).map i =
     (C.sheet.bY.equation.map (zhd C.genericParam)).map j:= by
   simp only [arcEquation,zoi,i,j,zPl,arc_generic]
 rw [← natDegree_map_eq_of_injective (f :=i) (zTo φ φ_injective),
   he,natDegree_map_eq_of_injective (f :=j)
     (zTo A.embedding A.embedding.injective)]
 change (C.sheet.bY.equation.map _).natDegree= _
 rw [show C.sheet.bY.equation.map (zhd C.genericParam)= _ from
   C.sheet.bY.generic_eq,
   natDegree_C_mul (Polynomial.C_ne_zero.mpr
     (show (C.sheet.bY.scale :oO C₀)≠0 from C.sheet.bY.scale.ne_zero)),
   C.sheet.root.degree]
private theorem map_branch (A:Arc C γ) (a :L) :
  branchPoly (arcEquation A) C.g a=(C.branchEquation a).map (arcParam A) := by
 let e :=zhd (arcParam A)
 let F:=C.sheet.bY.equation
 have he :e (z1z (znf a))=reference a := by
  change (z1z (znf a)).map (arcParam A)= _
  simp [arcParam,reference]
 change (F.map e).resultant (F.map e).derivative C.g (C.g-1)*(F.map e).eval (reference a) =
  e (F.resultant F.derivative C.g (C.g-1)*F.eval (z1z (znf a)))
 rw [derivative_map,resultant_map_map,← he,eval_map_apply,map_mul]
private theorem radical_data {F:Type} [zrb F] {f :F[X]} (h:f≠0) :
  (monicRadical f).natDegree≤f.natDegree ∧ ∃ n:ℕ,f∣(monicRadical f)^n:= by
 classical
 exact ⟨natDegree_radical_le,UniqueFactorizationMonoid.exists_dvd_radical_self_pow h⟩
def localMark (A:ArcFamily C) {m:ℕ} (B:Branch C A m) (hγ:γ∈B.keep)
    (hg:2≤C.g) (hgp:C.g<p) (hmp:m<p) :LocalMark L p:= by
  classical
  let arc :=A ⟨γ,B.subset hγ⟩
  let r :=B.lift γ
  have hT:γ∈C.T:=(Finset.mem_filter.mp (B.subset hγ)).1
  have hr :r.map φ=(C.radicalBranch B.reference).map arc.embedding:=B.lift_eq γ hγ
  have hbranch : (branchPoly (arcEquation arc) C.g B.reference).map φ =
      (C.genericBranch B.reference).map arc.embedding:= by
    rw [map_branch,zoi,arc_generic,← zoi]
    rfl
  have hd:r.natDegree=(C.radicalBranch B.reference).natDegree := by
    rw [← natDegree_map_eq_of_injective φ_injective,hr,
      natDegree_map_eq_of_injective arc.embedding.injective]
  have hrad:=radical_data B.proper
  refine ⟨arcEquation arc,C.g,B.reference,r,j9 (C.s γ),arcEquation_degree arc,
    hg,hgp,?_,monic_of_injective φ_injective (hr ▸ B.monic.map arc.embedding),
    ?_,?_,?_,?_,B.different γ hT⟩
  · change ((branchPoly (arcEquation arc) C.g B.reference).map zbO)≠0
    rw [map_branch,zoi,arc_specialize]
    exact B.nonzero_at_mark γ hγ
  · rw [hd]
    exact hrad.1.trans_lt (B.degree.trans_lt hmp)
  · obtain ⟨n,hn⟩:=hrad.2
    refine ⟨n,?_⟩
    rw [hbranch,hr,← Polynomial.map_pow]
    exact Polynomial.map_dvd arc.embedding hn
  · rw [arcEquation_specialize]
    exact C.sheet.identity γ hT
  · rw [← derivative_map,arcEquation_specialize]
    exact B.simple_at_mark γ hγ
private theorem firstCoeff_eq (f :Physical L) :firstCoeff f=reduce (seedDeriv f) := by
 classical
 apply Polynomial.ext
 intro j
 have he : (reduce (seedDeriv f)).coeff j=PowerSeries.coeff 1 (f.coeff j) := by
   change ((seedDeriv f).map zbO).coeff j= _
   rw [coeff_map]
   change zbO (PowerSeries.derivative (f.coeff j))= _
   simpa using (PowerSeries.coeff_derivative (f.coeff j) 0)
 rw [he,firstCoeff,Polynomial.finsetSum_coeff]
 simp only [coeff_monomial,Finset.sum_ite_eq']
 split_ifs with hj
 · rfl
 · rw [notMem_support_iff.mp hj,map_zero]
theorem gK6 (A:ArcFamily C) {m:ℕ} (B:Branch C A m) (hγ:γ∈B.keep)
    (hg:2≤C.g) (hgp:C.g<p) (hmp:m<p) :
    let M:=localMark A B hγ hg hgp hmp
    A.variation γ = -algebraMap L[X] (RatFunc L) (yq M.s (seedPartial M.f)) /
      algebraMap L[X] (RatFunc L) (yq M.s M.f.derivative) := by
  classical
  let arc :=A ⟨γ,B.subset hγ⟩
  let s :=j9 (C.s γ)
  let s' := s.map zMG
  have hz :seedDeriv s' = 0:= by
    apply Polynomial.ext
    intro i
    rw [coeff_zero]
    change PowerSeries.derivative ((s.map zMG).coeff i)=0
    rw [coeff_map,PowerSeries.derivative_C]
  rw [ArcFamily.variation,dite_eq_left (B.subset hγ)]
  change arc.variation= _
  unfold Arc.variation
  dsimp only
  change -algebraMap L[X] (RatFunc L) (firstCoeff ((arcEquation arc).eval s')) /
    algebraMap L[X] (RatFunc L) ((C.markedEquation γ).derivative.eval s) =
      -algebraMap L[X] (RatFunc L) (yq s (seedPartial (arcEquation arc))) /
        algebraMap L[X] (RatFunc L) (yq s (arcEquation arc).derivative)
  rw [firstCoeff_eq,coeffDeriv_eval seedDeriv s',hz,mul_zero,add_zero]
  have hs :reduce s' = s := by
    ext i
    simp [s',reduce,zr8]
  rw [yq,yq,← derivative_map,arcEquation_specialize,
    ← hs,eval_map_apply]
  rfl
end ArcMap
end
end qAjZDhd
end
section
namespace qAjZDhd
noncomputable section
open Polynomial
variable {k :Type} [zrb k] {p:ℕ}
private abbrev toRat :=algebraMap k[X] (RatFunc k)
abbrev variationAt (M:LocalMark k p) :RatFunc k :=
 -toRat (yq M.s (seedPartial M.f))/toRat (yq M.s M.f.derivative)
private theorem physical_atMark (M:LocalMark k p) :
   yq M.s (physicalPartial M.f) = -(yq M.s M.f.derivative*M.s.derivative) := by
 have hmap : (physicalPartial M.f).map reduce =
     Lv (Polynomial.derivative' (R:=k)) (M.f.map reduce) := by
   ext i:1
   rw [coeff_map]
   change reduce ((M.f.coeff i).derivative)=((M.f.map reduce).coeff i).derivative
   rw [coeff_map]
   exact (derivative_map (M.f.coeff i) zbO).symm
 have h:=coeffDeriv_eval (Polynomial.derivative' (R:=k))
   M.s (M.f.map reduce)
 change ((M.f.map reduce).eval M.s).derivative= _ at h
 rw [M.root,derivative_zero,← hmap,derivative_map] at h
 exact eq_neg_of_add_eq_zero_left h.symm
theorem den_atMark (M:LocalMark k p) :
  yq M.s M.denominator=yq M.s M.f.derivative*(M.s - C M.a) := by
 simp only [LocalMark.denominator,yq,zNl,Polynomial.map_sub,
  Polynomial.map_X,Polynomial.map_C,eval_mul,eval_sub,eval_X,eval_C]
 simp [reduce,reference]
private theorem log_first (M:LocalMark k p) :
   M.logValue (M.numerator false)*toRat (M.s - C M.a) =
     toRat (reduce M.r)*variationAt M:= by
 have hs :toRat (M.s - C M.a)≠0:=RatFunc.algebraMap_ne_zero (sub_ne_zero.mpr M.different)
 have hd:toRat (yq M.s M.f.derivative)≠0:=RatFunc.algebraMap_ne_zero M.simple
 have hn:yq M.s (M.numerator false) = -(reduce M.r)*yq M.s (seedPartial M.f) := by
   simp [LocalMark.numerator,yq]
 rw [LocalMark.logValue,den_atMark,hn]
 simp only [map_mul,map_neg,variationAt]
 field_simp [hs,hd]
private theorem log_second (M:LocalMark k p) :
    M.logValue (M.numerator true)*toRat (M.s - C M.a) =
      toRat (reduce M.r.derivative)*variationAt M -
        toRat (reduce (seedDeriv M.r)*M.s.derivative) := by
  have hs :toRat (M.s - C M.a)≠0:=RatFunc.algebraMap_ne_zero (sub_ne_zero.mpr M.different)
  have hd:toRat (yq M.s M.f.derivative)≠0:=RatFunc.algebraMap_ne_zero M.simple
  have hn:yq M.s (M.numerator true) =
      -(reduce M.r.derivative)*yq M.s (seedPartial M.f) +
        reduce (seedDeriv M.r)*yq M.s (physicalPartial M.f) := by
    simp [LocalMark.numerator,yq]
  rw [LocalMark.logValue,den_atMark,hn,physical_atMark]
  simp only [map_add,map_mul,map_neg,variationAt]
  field_simp [hs,hd]; ring
private theorem denom_dvd_of_mul {v :RatFunc k} {r u:k[X]}
   (h:toRat r*v=toRat u) :v.denom∣r := by
 by_cases hr :r=0
 · rw [hr]
   exact dvd_zero _
 have he :v=toRat u/toRat r :=
   (eq_div_iff (RatFunc.algebraMap_ne_zero hr)).2 ((mul_comm _ _).trans h)
 rw [he]
 exact RatFunc.denom_div_dvd _ _
private theorem intDegree_sum_le {ι:Type} (s :Finset ι) (f :ι→RatFunc k)
   {b:ℤ} (hb:0≤b) (h : ∀ i∈s,(f i).intDegree≤b) :
   (∑ i∈s,f i).intDegree≤b:= by
 classical
 induction s using Finset.induction_on with
 | empty=>simpa using hb
 | insert i s hi ih =>
   rw [Finset.sum_insert hi]
   have ha :=h i (Finset.mem_insert_self i s)
   have hs :=ih (fun j hj=>h j (Finset.mem_insert_of_mem hj))
   by_cases hz : (∑ j∈s,f j)=0
   · simpa [hz] using ha
   by_cases hsum:f i+(∑ j∈s,f j)=0
   · simp [hsum,hb]
   exact (RatFunc.intDegree_add_le hz hsum).trans (max_le ha hs)
private theorem degree_pow (v :RatFunc k) (hv :v≠0) (n:ℕ) :
   (v^n).intDegree=n*v.intDegree := by
 induction n with
 | zero=>simp
 | succ n hi =>
   rw [pow_succ,RatFunc.intDegree_mul (pow_ne_zero _ hv) hv,hi,Nat.cast_succ,add_mul,
     one_mul]
private theorem weighted_root {F:k[X][X]} {v :RatFunc k} {r :ℕ}
   (hm:F.Monic) (hb : ∀ i<F.natDegree,
     (F.coeff i).natDegree≤ r*(F.natDegree - i))
   (he :F.eval₂ toRat v=0) :v.intDegree≤ r := by
 by_contra! h
 have hv :v≠0:= by
   rintro rfl
   rw [RatFunc.intDegree_zero] at h
   omega
 let n:=F.natDegree
 rw [Polynomial.eval₂_eq_sum_range,Finset.sum_range_succ,hm.coeff_natDegree,map_one,one_mul] at he
 change (∑ i∈z4x n,toRat (F.coeff i)*v^i)+v^n=0 at he
 have hn:0<n:=Nat.pos_of_ne_zero fun hz=> by simp [hz] at he
 have hd:0<v.intDegree :=(Int.natCast_nonneg r).trans_lt h
 have hb0:0≤(n:ℤ)*v.intDegree - 1 := by
   have hd' : (1 :ℤ)≤v.intDegree := by omega
   have hn' : (1 :ℤ)≤n:= by exact_mod_cast hn
   nlinarith only [mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hd'),hd',hn']
 have hs :=intDegree_sum_le (z4x n) (fun i=>toRat (F.coeff i)*v^i) hb0 (by
   intro i hi
   have hin:i<n:=Finset.mem_range.mp hi
   by_cases hz :F.coeff i=0
   · simpa [hz] using hb0
   rw [RatFunc.intDegree_mul (RatFunc.algebraMap_ne_zero hz) (pow_ne_zero _ hv),
     RatFunc.intDegree_polynomial,degree_pow _ hv]
   have hi' : (i:ℤ)<n:= by exact_mod_cast hin
   have hcoeff : ((F.coeff i).natDegree :ℤ)≤((r*(n-i) :ℕ) :ℤ) := by
     exact_mod_cast hb i hin
   rw [Nat.cast_mul,Nat.cast_sub hin.le] at hcoeff
   have hprod:=mul_pos (sub_pos.mpr hi') (sub_pos.mpr h)
   nlinarith only [hcoeff,show 1≤((n:ℤ) - i)*(v.intDegree - r) by omega])
 have heq :v^n = -(∑ i∈z4x n,toRat (F.coeff i)*v^i) := by
   exact eq_neg_of_add_eq_zero_right he
 rw [← RatFunc.intDegree_neg,← heq,degree_pow _ hv] at hs
 omega
def excessAt (r :k[X]) :ℕ:= by
 classical exact (EuclideanDomain.gcd r r.derivative).natDegree
theorem pole_bounds (M:LocalMark k p) {D:ℕ} (hD:M.s.natDegree≤D)
   (Q₁ Q₂:Equation k) (hm₁:Q₁.Monic) (hm₂:Q₂.Monic) (hw:WeightBound M.r.natDegree Q₁)
   (he₁: (Q₁.map reduce).eval₂ toRat (M.logValue (M.numerator false))=0)
   (he₂: (Q₂.map reduce).eval₂ toRat (M.logValue (M.numerator true))=0) :
   (variationAt M).denom.natDegree≤excessAt (reduce M.r) ∧
   (variationAt M).num.natDegree≤D + (variationAt M).denom.natDegree := by
 classical
 have hm {Q:Equation k} (hQ:Q.Monic) {v :RatFunc k}
     (he : (Q.map reduce).eval₂ toRat v=0) : ∃ u:k[X],toRat u=v :=
   IsIntegrallyClosed.isIntegral_iff.mp ⟨Q.map reduce,hQ.map reduce,he⟩
 obtain ⟨u,hu⟩:=hm hm₁ he₁
 obtain ⟨v,hv⟩:=hm hm₂ he₂
 have h₁:=log_first M
 have h₂:=log_second M
 rw [← hu,← map_mul] at h₁
 have hr' : reduce M.r.derivative=(reduce M.r).derivative :=
   (derivative_map M.r zbO).symm
 rw [← hv,← map_mul,hr'] at h₂
 have hd₁:=denom_dvd_of_mul h₁.symm
 have h₂' : toRat (reduce M.r).derivative*variationAt M =
     toRat (v*(M.s - C M.a)+reduce (seedDeriv M.r)*M.s.derivative) := by
   rw [map_add,h₂,sub_add_cancel]
 have hd₂:=denom_dvd_of_mul h₂'
 have hR: (reduce M.r).Monic:=M.monic.map zbO
 have hgcd:EuclideanDomain.gcd (reduce M.r) (reduce M.r).derivative≠0:= by
   intro h
   have hdvd:=EuclideanDomain.gcd_dvd_left (reduce M.r) (reduce M.r).derivative
   rw [h,zero_dvd_iff] at hdvd
   exact hR.ne_zero hdvd
 refine ⟨natDegree_le_of_dvd (EuclideanDomain.dvd_gcd hd₁ hd₂) hgcd,?_⟩
 by_cases hz :variationAt M=0
 · rw [hz,RatFunc.num_zero,natDegree_zero]
   exact Nat.zero_le _
 have hdeg:=weighted_root (hm₁.map reduce) (by
   intro i hi
   rw [hm₁.natDegree_map] at hi ⊢
   rw [coeff_map]
   exact (Polynomial.natDegree_map_le).trans (hw i hi)) he₁
 have hs :=RatFunc.algebraMap_ne_zero (sub_ne_zero.mpr M.different)
 have hl:M.logValue (M.numerator false)≠0:= by
   intro h
   have he :=log_first M
   rw [h,zero_mul] at he
   exact mul_ne_zero (RatFunc.algebraMap_ne_zero hR.ne_zero) hz he.symm
 have he :=congrArg RatFunc.intDegree (log_first M)
 rw [RatFunc.intDegree_mul hl hs,
   RatFunc.intDegree_mul (RatFunc.algebraMap_ne_zero hR.ne_zero) hz,
   RatFunc.intDegree_polynomial,RatFunc.intDegree_polynomial,
   show (reduce M.r).natDegree=M.r.natDegree from M.monic.natDegree_map _] at he
 change (M.logValue (M.numerator false)).intDegree+(M.s - C M.a).natDegree =
   (M.r.natDegree :ℤ) +
     ((variationAt M).num.natDegree-((variationAt M).denom.natDegree :ℤ)) at he
 have hdegS: (M.s - C M.a).natDegree≤D :=
   (natDegree_sub_le _ _).trans (max_le hD (by simp))
 omega
end
end qAjZDhd
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace qAjZDhd
noncomputable section
open Polynomial
private def homogenized {R:Type} [za6 R] (N E Q:R[X]) :R[X] :=
 ∑ i∈z4x (Q.natDegree+1),C (Q.coeff i)*N^i*E^(Q.natDegree - i)
private theorem homogenized_eval {R F:Type} [za6 R] [zrb F]
   (j:R →+* F) (x :F) (N E Q:R[X]) (he :E.eval₂ j x≠0) :
   (homogenized N E Q).eval₂ j x=(E.eval₂ j x)^Q.natDegree *
     Q.eval₂ j (N.eval₂ j x/E.eval₂ j x) := by
 simp only [homogenized,eval₂_finsetSum,eval₂_mul,eval₂_C,eval₂_pow]
 rw [eval₂_eq_sum_range (p:= Q),Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro i hi
 have hle :i≤Q.natDegree :=Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
 rw [div_pow,← mul_div_assoc,← mul_div_assoc]
 apply (eq_div_iff (pow_ne_zero _ he)).2
 rw [mul_assoc,← pow_add,Nat.sub_add_cancel hle]
 ring
private theorem specialize_dvd {R F S:Type} [za6 R] [zrb F] [za6 S]
   [IsDomain S] (j:R →+* F) (hj:zq4 j) (e :R →+* S)
   {f h:R[X]} (hdeg:1≤f.natDegree) (hlead:e f.leadingCoeff≠0)
   {x :S} (hx :f.eval₂ e x=0)
   (hd:f.map j∣h.map j) :h.eval₂ e x=0:= by
 by_cases hh:h=0
 · simp [hh]
 have hf :f≠0:= by
   intro hf
   exact hlead (by simp [hf])
 have hdl:f.integralNormalization∣h.scaleRoots f.leadingCoeff := by
   apply (Polynomial.map_dvd_map j hj (monic_integralNormalization hf)).mp
   obtain ⟨z,hz⟩:=hd
   refine ⟨(C f.leadingCoeff).map j*z.scaleRoots (j f.leadingCoeff),?_⟩
   have hnn {b:R} (hb:b≠0) :j b≠0:= fun he=>hb (hj (he.trans (map_zero j).symm))
   rw [map_scaleRoots _ _ _ (hnn (leadingCoeff_ne_zero.mpr hh)),
     hz,mul_scaleRoots_of_noZeroDivisors,
     ← map_scaleRoots _ _ _ (hnn (leadingCoeff_ne_zero.mpr hf)),
     ← integralNormalization_mul_C_leadingCoeff,zNl,mul_assoc]
 have hscaled:=eval₂_dvd e (e f.leadingCoeff*x) hdl
 rw [integralNormalization_eval₂_leadingCoeff_mul hdeg,hx,mul_zero,zero_dvd_iff,
   scaleRoots_eval₂_mul] at hscaled
 exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero _ hlead)
private theorem splitMap_injective {k :Type} [zrb k] :
  zq4 (bL9 (k :=k)) := by
 let F:=FractionRing (zpm k)
 have h₁:=zxb (zpm k) F
 have h₂:=RatFunc.algebraMap_injective F
 have h₃:=(algebraMap (Generic k) (AlgebraicClosure (Generic k))).injective
 exact h₃.comp (h₂.comp (zTo _ h₁))
private theorem dvd_homogenized {R F:Type} [za6 R] [zrb F] [IsAlgClosed F]
   (j:R →+* F) (f N E Q:R[X]) (hf :f.map j≠0) (hsep: (f.map j).Separable)
   (hd : ∀ y,(f.map j).eval y=0→E.eval₂ j y≠0)
   (hQ:Q.map j=((f.map j).roots.map fun y =>
     z7y-Polynomial.C ((N.map j).eval y/(E.map j).eval y)).prod) :
   f.map j∣(homogenized N E Q).map j:= by
 classical
 by_cases hH : (homogenized N E Q).map j=0
 · rw [hH]; exact dvd_zero _
 refine (IsAlgClosed.splits _).dvd_of_roots_le_roots hf
   ((Multiset.le_iff_subset (Polynomial.nodup_roots hsep)).mpr ?_)
 intro y hy
 have hh:Q.eval₂ j (N.eval₂ j y/E.eval₂ j y)=0:= by
   rw [eval₂_eq_eval_map,hQ,eval_multiset_prod,Multiset.map_map]
   apply Multiset.prod_eq_zero
   exact Multiset.mem_map.mpr ⟨y,hy,by simp only [Function.comp_apply,eval_sub,
     eval_X,eval_C,eval_map,sub_self]⟩
 apply (mem_roots hH).mpr
 change ((homogenized N E Q).map j).eval y=0
 rw [eval_map,homogenized_eval j y N E Q (hd y ((mem_roots hf).mp hy)),hh,mul_zero]
theorem cqt {k :Type} [zrb k] {p:ℕ}
   (M:LocalMark k p) (N Q:Equation k) (hQ:RootProduct M N Q) :
   (Q.map reduce).eval₂ (algebraMap k[X] (RatFunc k)) (M.logValue N)=0:= by
 classical
 let j:=bL9 (k :=k)
 let F:=M.f.map j
 let E :=M.denominator
 let H :=homogenized N E Q
 have hg:0<M.g:= by have :=M.two_le; omega
 have hBn:=M.branch_nonzero
 unfold branchPoly at hBn
 rw [map_mul] at hBn
 have hres :=left_ne_zero_of_mul hBn
 have href :=right_ne_zero_of_mul hBn
 have hj:zq4 j:=splitMap_injective
 have hne {u:Physical k} (hu:reduce u≠0) :j u≠0:= by
   intro h
   rw [hj (h.trans (map_zero j).symm),map_zero] at hu
   exact hu rfl
 have hR:=hne hres
 have hA:=hne href
 have hF:F≠0:= by
   have hd:F.natDegree=M.g :=
     (natDegree_map_eq_of_injective splitMap_injective _).trans M.degree
   intro hz
   rw [hz,natDegree_zero] at hd
   exact hg.ne' hd.symm
 have hsep:F.Separable :=
   separable_map_of_resultant_derivative_padded_ne_zero j M.f M.degree.le hg hR
 have hden (y :AlgebraicClosure (Generic k)) (hyF: (M.f.map j).eval y=0) :
     E.eval₂ j y≠0:= by
   have hd:=eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero
     j M.f M.degree.le hg hR y hyF
   have ha :y - j (reference M.a)≠0:= by
     intro hz
     rw [sub_eq_zero.mp hz,eval_map_apply] at hyF
     exact hA hyF
   change (M.f.derivative*(z7y-Polynomial.C (reference M.a))).eval₂ j y≠0
   rw [eval₂_mul,eval₂_sub,eval₂_X,eval₂_C,← eval_map j (p:=M.f.derivative),← derivative_map]
   exact mul_ne_zero hd ha
 have hdiv :F∣H.map j:=dvd_homogenized j M.f N E Q hF hsep hden hQ
 have hdeg:=natDegree_map_eq_of_resultant_derivative_padded_ne_zero reduce M.f M.degree.le hg hres
 have hlead:reduce M.f.leadingCoeff≠0 :=
   (natDegree_map_eq_iff.mp (hdeg.trans M.degree.symm)).resolve_right
     (fun hz=>hg.ne' (M.degree.symm.trans hz))
 have hroot :M.f.eval₂ reduce M.s=0:= by rw [← eval_map]; exact M.root
 have hh:H.eval₂ reduce M.s=0 :=
   specialize_dvd j hj reduce (M.degree.symm ▸ hg) hlead hroot hdiv
 let a :=algebraMap k[X] (RatFunc k)
 let e :=a.comp (reduce (k :=k))
 have heval (P:Equation k) :P.eval₂ e (a M.s)=a (yq M.s P) := by
   rw [← hom_eval₂,yq,eval_map]
 have he :E.eval₂ e (a M.s)≠0:= by
   rw [heval,show E=M.denominator from rfl,den_atMark]
   exact RatFunc.algebraMap_ne_zero (mul_ne_zero M.simple (sub_ne_zero.mpr M.different))
 have h0:H.eval₂ e (a M.s)=0:= by rw [← hom_eval₂,hh,map_zero]
 rw [show H=homogenized N E Q from rfl,homogenized_eval e (a M.s) N E Q he] at h0
 have h:=(mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ he)
 rw [heval N,heval E] at h
 rw [eval₂_map]
 exact h
end
end qAjZDhd
end
section
namespace qAjZDhd
noncomputable section
open Polynomial
def c1 :Prop :=
  ∀ (k :Type) [zrb k] (p:ℕ) [CharP k p] (M:LocalMark k p) (zD:Bool),
    ∃ Q:Equation k,Q.Monic∧RootProduct M (M.numerator zD) Q
def c2 :Prop :=
  ∀ (k :Type) [zrb k] (p:ℕ) [CharP k p] (M:LocalMark k p) (Q:Equation k),
    RootProduct M (M.numerator false) Q→WeightBound M.r.natDegree Q
theorem of_children (h1 :c1) (h2 :c2) :qL2osVa.c3:= by
 classical
 intro C₀ inst C A m B hg hgp hmp γ hγ
 let M:=localMark A B hγ hg hgp hmp
 let:CharP cu.L P5.p :=
  charP_of_injective_ringHom (algebraMap P5.K cu.L).injective P5.p
 obtain ⟨Q₁,hQ₁,hP₁⟩:=h1 _ _ M false
 obtain ⟨Q₂,hQ₂,hP₂⟩:=h1 _ _ M true
 have hT:γ∈C.T:=(Finset.mem_filter.mp (B.subset hγ)).1
 have hs :M.s.natDegree≤C.D:= by
  change (cu.j9 (C.s γ)).natDegree≤C.D
  simpa only [cu.j9,natDegree_map] using C.degree γ hT
 have hb:=pole_bounds M hs Q₁ Q₂ hQ₁ hQ₂ (h2 _ _ M Q₁ hP₁)
  (cqt M _ Q₁ hP₁) (cqt M _ Q₂ hP₂)
 rw [gK6 A B hγ hg hgp hmp]
 exact hb
end
end qAjZDhd
end
section
namespace qaJ7jxd
noncomputable section
open Polynomial qAjZDhd
variable {k :Type} [zrb k] {p:ℕ}
abbrev kq (k :Type) [zrb k] :=FractionRing (zpm k)
abbrev toFrac:Physical k →+* (kq k)[X] :=
 zhd (algebraMap (zpm k) (kq k))
def denom (M:LocalMark k p) :Physical k :=
 M.f.resultant M.denominator M.g M.g
def sylvesterNumer {R:Type} [za6 R] (f E N :R[X]) (g:ℕ) :R[X] :=
 let j:R →+* R[X] :=z1z
 let w:R[X] :=z7y
 (f.map j).resultant (z1z w*E.map j-N.map j) g g
def Fr (M:LocalMark k p) (zD:Bool) :Equation k :=
 sylvesterNumer M.f M.denominator (M.numerator zD) M.g
def TameLog:Prop :=
  ∀ (R K L:Type) [za6 R] [IsDomain R] [IsDiscreteValuationRing R]
    [zrb K] [zrb L] [zZE R K] [IsFractionRing R K] [zZE K L]
    [zZE R L] [IsScalarTower R K L]
    (p:ℕ) [CharP K p] (d:Derivation ℤ K K) (π:R),
    Irreducible π →
    (∀ b:R,∃ c:R,d (algebraMap R K b)=algebraMap R K c) →
    (∃ b:R,d (algebraMap R K π)=algebraMap R K (π*b)) →
    ∀ (f :K[X]) (a :K) (y :L),f.Separable→f.natDegree<p →
      d a=0→f.eval₂ (algebraMap K L) y=0→y≠algebraMap K L a →
      IsIntegral R
        (- (Lv d f).eval₂ (algebraMap K L) y /
          (f.derivative.eval₂ (algebraMap K L) y*(y-algebraMap K L a)))
end
end qaJ7jxd
end
