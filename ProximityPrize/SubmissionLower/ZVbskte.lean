import ProximityPrize.SubmissionLower.ZofdZzd
import ProximityPrize.SubmissionLower.Z55PrLe
import ProximityPrize.SubmissionLower.ZT8CHOb
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qWcuPdb
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L)
open Cu
open qrsE1ie (NodeAllowance discriminant geomSquare)
open quN7Z4a (Sheet)
open qRoCwuc
open private node_counts wordCut map_discrim from ProximityPrize.SubmissionLower.ZofdZzd
private theorem descend_monic {F E :Type*} [Field F] [Field E] (e :F →+* E)
    (h₂: (2 :E)≠0) {q:E[X]} (hm:q.Monic)
    (hs :q^2∈(mapRingHom e).range) :q∈(mapRingHom e).range := by
  classical
  have hpow:=(mem_map_range e).mp hs
  let n:=q.natDegree
  have htop:q.coeff n = 1 :=hm
  have hcoeff (d:ℕ) : ∀ k,n-k=d→q.coeff k∈e.range := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro k hk
      rcases lt_trichotomy k n with hlt | heq | hgt
      · let A:=antidiagonal (n+k)
        let B:=(A.erase (n,k)).erase (k,n)
        let f (ij:ℕ×ℕ) :=q.coeff ij.1*q.coeff ij.2
        have h₁: (n,k)∈A:=mem_antidiagonal.mpr rfl
        have h₂' : (k,n)∈A.erase (n,k) :=
          mem_erase.mpr ⟨fun h=>hlt.ne (congrArg Prod.fst h),
            mem_antidiagonal.mpr (Nat.add_comm _ _)⟩
        have hsum: (∑ ij∈B,f ij)∈e.range := by
          apply e.range.sum_mem
          rintro ⟨i,j⟩ hij
          obtain ⟨hjn,hin,ha⟩:=mem_erase.mp hij |>.imp_right mem_erase.mp
          have hij' := mem_antidiagonal.mp ha
          by_cases hi:n< i
          · simp [f,coeff_eq_zero_of_natDegree_lt hi]
          by_cases hj:n<j
          · simp [f,coeff_eq_zero_of_natDegree_lt hj]
          have hki:k< i:= by
            by_contra! h
            exact hjn (Prod.ext (by omega) (by omega))
          have hkj:k<j:= by
            by_contra! h
            exact hin (Prod.ext (by omega) (by omega))
          exact e.range.mul_mem (ih (n-i) (by omega) i rfl)
            (ih (n-j) (by omega) j rfl)
        have hsplit : (q^2).coeff (n+k)=(∑ ij∈B,f ij)+2*q.coeff k := by
          rw [pow_two,coeff_mul]
          change (∑ ij∈A,f ij)= _
          rw [← sum_erase_add _ _ h₁,← sum_erase_add _ _ h₂']
          simp [B,f,htop,two_mul,add_assoc]
        have hprod: (2 :E)*q.coeff k∈e.range := by
          have h:=e.range.sub_mem (hpow (n+k)) hsum
          rwa [hsplit,add_sub_cancel_left] at h
        have hinv : (2 :E)⁻¹∈e.range :=⟨(2 :F)⁻¹,by rw [map_inv₀,map_ofNat]⟩
        have h:=e.range.mul_mem hinv hprod
        rwa [← mul_assoc,inv_mul_cancel₀ h₂,one_mul] at h
      · rw [heq,htop]
        exact e.range.one_mem
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        exact e.range.zero_mem
  exact (mem_map_range e).mpr fun k=>hcoeff (n-k) k rfl
private theorem constant_part {F E :Type*} [Field F] [Field E] (e :F →+* E)
   (h₂: (2 :E)≠0) {D:F[X]} {q:E[X]} (hq:q^2=D.map e) :
   ConstantOddPart D:= by
 by_cases hz :q=0
 · have hD:D =0:=(Polynomial.map_injective e e.injective)
     (by simpa [hz] using hq.symm)
   exact ⟨0,0,by simp [hD]⟩
 let u:=q.leadingCoeff
 let Q:=C u⁻¹*q
 have hu:u≠0:=leadingCoeff_ne_zero.mpr hz
 have hQ:Q.Monic:= by
   show (C u⁻¹*q).leadingCoeff=1
   rw [leadingCoeff_mul,leadingCoeff_C,inv_mul_cancel₀ hu]
 have he :e D.leadingCoeff=u^2 := by
   rw [← leadingCoeff_map_of_injective e.injective,← hq,leadingCoeff_pow]
 have hD:D.leadingCoeff≠0:= fun h=> by
   rw [h,map_zero] at he
   exact pow_ne_zero 2 hu he.symm
 have hmap : (C D.leadingCoeff⁻¹*D).map e= Q^2 := by
   change _=(C u⁻¹*q)^2
   rw [Polynomial.map_mul,Polynomial.map_C,map_inv₀,he,← hq,mul_pow,
     ← Polynomial.C_pow,inv_pow]
 obtain ⟨r,hr⟩:=descend_monic e h₂ hQ ⟨_,hmap⟩
 change r.map e= Q at hr
 have hr' : C D.leadingCoeff⁻¹*D =r^2 :=
   (Polynomial.map_injective e e.injective) (by rw [hmap,Polynomial.map_pow,hr])
 refine ⟨D.leadingCoeff,r,?_⟩
 rw [← hr',← mul_assoc,← C_mul,mul_inv_cancel₀ hD,C_1,one_mul]
private theorem chart_part {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
   (S:Sheet C₀ J 2 H T z s) (hs :geomSquare S.root.equation) :
   ConstantOddPart (genericDisc S) := by
 let e :oO C₀ →+* AlgebraicClosure (oO C₀) :=algebraMap _ _
 let:CharP (AlgebraicClosure (oO C₀)) p :=
   charP_of_injective_ringHom (e.comp ((zT C₀).comp (algebraMap K L))).injective p
 have h₂: (2 :AlgebraicClosure (oO C₀))≠0 :=
   fun h=>(by decide : ¬ p∣2) ((CharP.cast_eq_zero_iff _ p 2).mp h)
 obtain ⟨q,hq⟩:=hs
 obtain ⟨a,r,hr⟩:=constant_part e h₂ hq
 have hdisc:genericDisc S=C (S.bY.scale :oO C₀)^2 *
     discriminant S.root.equation := by
   change mapRingHom (coord S) (discrim (coeff S 2) (coeff S 1) (coeff S 0))= _
   rw [map_discrim]
   simp only [coe_mapRingHom,coeff_generic,discrim,discriminant,C_ofNat]
   ring
 exact ⟨a,C (S.bY.scale :oO C₀)*r,by rw [hdisc,hr,mul_pow]; ring⟩
theorem proof :qrsE1ie.c3:= by
 classical
 intro C₀ _ J T z s w H S hs hz
 have hconst:=chart_part S hs
 have hnodes :NodeAllowance T s w (2*2*H) := by
   intro i
   have hc:=node_counts S hz hconst i (w i)
   have hle :H≤2*2*H := by omega
   by_cases h:coord S (wordCut S i (w i))=0
   · right
     refine le_trans ?_ ((hc.2 h).trans hle)
     exact le_of_eq (congrArg card (filter_congr fun _ _=>Iff.rfl))
   · left
     refine le_trans ?_ ((hc.1 h).trans hle)
     exact le_of_eq (congrArg card (filter_congr fun _ _=>Iff.rfl))
 refine ⟨⟨T,∅,Subset.rfl,empty_subset _,?_,2,0,by decide,hnodes,?_⟩⟩
 · simp
 · intro i
   left
   simp
end
end qWcuPdb
end
section
set_option autoImplicit true
namespace qPTDwMb
theorem proof :qa5nZzb.c3:=qWcuPdb.proof
end qPTDwMb
end
section
namespace qxDtRld
noncomputable section
open Polynomial q82zwcd
open P5 (K I)
open cu (L)
open Cu (sQ)
open E7 (CurvePlace)
open qb0hmCe (SiteTarget)
open qFD8jve (aFA sheetPole seedPole polarResultant)
open qbnx7gb (targetA targetB)
variable {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
 {z :K→K} {q:sQ} {J:WordChart D w U s}
def Go (F:DualSheet J q z) (R:SiteTarget) (t:L) :F.curve.E[X][X] :=
  qwGrtCa.transform (C (algebraMap L F.curve.E t)) (C (targetA F.curve R))
    1 (C (targetB F.curve R)) F.d
    (F.f.map (taylorAlgHom (algebraMap L F.curve.E R.center)).toRingHom)
abbrev nY {E :Type} [Field E] (a :E) (G:E[X][X]) :E[X][X] :=
 C (C a)*G
def resA (R:SiteTarget) (z :K→K) (γ:K) :L :=
 R.a+R.b*DP.Z7 (z γ) R.coord
def resB (R:SiteTarget) (z :K→K) (γ:K) :L :=
 R.c+R.d*DP.Z7 (z γ) R.coord
def markP (J:WordChart D w U s) (R:SiteTarget) (z :K→K) (γ:K) :L[X] :=
 C (resB R z γ)*taylor R.center (J.P γ) - C (resA R z γ)*taylor R.center (J.Q γ)
def markQ (J:WordChart D w U s) (R:SiteTarget) (t:L) (γ:K) :L[X] :=
 C t*taylor R.center (J.Q γ) - taylor R.center (J.P γ)
def correction (F:DualSheet J q z) (R:SiteTarget) (t:L) (γ:K) :L[X] :=
  C (F.direction γ R.coord) *
    (C R.d*taylor R.center (J.P γ) - C R.b*taylor R.center (J.Q γ))*markQ J R t γ
structure Chart {F:DualSheet J q z} (V:Variation F) (R:SiteTarget) (t:L) :Prop where
 degree : (Go F R t).natDegree=F.d
 leading: (Go F R t).leadingCoeff.coeff 0≠0
 separant:polarResultant (Go F R t)≠0
 avoids : ∀ γ∈V.good,targetHit J z R γ→t*resB R z γ - resA R z γ≠0
 bound : ∀ v :CurvePlace L F.curve.E,
  aFA v.value (Go F R t) (sheetPole v.value F.f+F.d*seedPole F.curve R v.value)
 integral : ∀ γ∈V.good,targetHit J z R γ →
  aFA (F.place γ).value (nY (F.scale γ:F.curve.E) (Go F R t)) 0
end
end qxDtRld
end
section
set_option autoImplicit true
namespace qJOpoVa
open qNu3xvc (Equation)
noncomputable def relativeRate {E :Type} [Field E] (A:Equation E) :ℕ :=
 (6*A.d-4)*A.b+(3*A.d*A.d-2)*A.s+(2*A.d-2)
end qJOpoVa
end
section
set_option autoImplicit true
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace qJOpoVa
noncomputable section
open Polynomial Finset qNu3xvc
open P5 (p)
open cu (L)
open E7 (CurvePlace)

open qFD8jve (aFA sheetPole)
open P5_7_1_7_4_3_4 (Pencil relativePolar adG bix)
open q82zwcd (WordChart DualSheet Variation polar)




open scoped Classical WithZero
def c1 :Prop :=
  ∀ {D w U s z q} {J:WordChart D w U s} {F:DualSheet J q z}
    (V:Variation F) (b:ℕ),3≤F.d →
    F.Jm (b+F.d*(J.u₀+(J.u₁-J.u₀))) →
    ∃ (A:Equation F.curve.E) (S:Sections A),
      A.d=F.d∧A.s=J.u₁-J.u₀∧A.b=b∧A.h≤F.h ∧
      (∑ γ∈V.good,V.DG γ)≤finitePoles S
def c2 :Prop :=qNu3xvc.c2
def c3:Prop :=qNu3xvc.c3
def c4 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d→A.d<p →
    ∀ (ι:Type) [Fintype ι] (w:ι→CurvePlace L E) (x :ι→L) (r :ι→Bool)
      (v : ∀ i,GraphVal A (r i)),(∀ i,Over (v i) (w i) (x i)) →
      ∃ C:Pencil A,C.tilt≠0 ∧
        (∀ i,(v i).val (relativePolar C)=(v i).val (qNu3xvc.polar A (r i))) ∧
        ∀ i,∃ n:ℕ,0<n ∧ ∀ g:E[X],
          (v i).val (C.base (algebraMap E[X] (RatFunc E) g))=adG (w i).value g^n
def c5:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d → ∀ C:Pencil A,
    C.tilt≠0 → ∃ P:E[X][X],P.coeff 0≠0 ∧
      bix C.base (relativePolar C) C.finite ∣
        P.map (algebraMap E[X] (RatFunc E)) ∧
      ∀ w:CurvePlace L E,aFA w.value P (relativeRate A*sheetPole w.value A.f)
def c6:Prop :=P5_7_1_7_4_3_4.c3
end
end qJOpoVa
end
