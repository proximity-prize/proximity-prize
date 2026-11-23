import ProximityPrize.SubmissionLower.ZGcgEBb
import ProximityPrize.SubmissionLower.ZhNzRYc
import ProximityPrize.SubmissionLower.Zqop1Ec
import ProximityPrize.SubmissionLower.ZSZKDCa
import ProximityPrize.SubmissionLower.ZXTI5ee
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace qqV3gre
noncomputable section
open Polynomial
open P5 (K p)
open cu (L)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation)
open qb0hmCe (CurveModel)
open qxPDCsa (References RadicalOf Good finiteRef reduce contentAt gcdDegree)
open scoped nonZeroDivisors
def c1 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} {V:Variation F} {D W:ℕ}
    (A:References V D W) (t:Cq.E[X]),F.d<p →
    RadicalOf (F.f.discr*finiteRef F (A.a 0)*finiteRef F (A.a 1)) t →
    ∀ γ (hγ:γ∈V.marks),Good A γ →
      let a :=F.atPlace γ (V.Bp hγ)
      integralLogs physicalCoeff (arcEquation a F.f) (t.map a.toRingHom) (A.a 0) (A.a 1)
def c2 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} {V:Variation F} {D W:ℕ}
    (A:References V D W) (t:Cq.E[X]),F.d<p →
    RadicalOf (F.f.discr*finiteRef F (A.a 0)*finiteRef F (A.a 1)) t →
    ∀ γ (hγ:γ∈V.marks),Good A γ →
      let a :=F.atPlace γ (V.Bp hγ)
      integralLogs physicalCoeff (arcEquation a F.f) (t.map a.toRingHom) (A.a 0) (A.a 1) →
      integralLogs integralCoeff (arcEquation a F.f) (t.map a.toRingHom) (A.a 0) (A.a 1)
def c3:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} {V:Variation F} {D W:ℕ}
    (A:References V D W) (t:Cq.E[X]),
    RadicalOf (F.f.discr*finiteRef F (A.a 0)*finiteRef F (A.a 1)) t →
    ∀ γ (hγ:γ∈V.marks),Good A γ →
      let a :=F.atPlace γ (V.Bp hγ)
      integralLogs integralCoeff (arcEquation a F.f) (t.map a.toRingHom) (A.a 0) (A.a 1) →
      (V.den γ)∣reduce a t∧(V.den γ)∣(reduce a t).derivative
def c4 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} {V:Variation F} {D W:ℕ}
    (A:References V D W) (r t:Cq.E[X]),
    RadicalOf F.f.discr r →
    RadicalOf (F.f.discr*finiteRef F (A.a 0)*finiteRef F (A.a 1)) t →
    ∀ γ (hγ:γ∈V.marks),Good A γ →
      let a :=F.atPlace γ (V.Bp hγ)
      let R:=reduce a r
      let T:=reduce a t
      let U:=reduce a (finiteRef F (A.a 0))
      let B:=reduce a (finiteRef F (A.a 1))
      T≠0∧R*U*B≠0∧T∣R*U*B ∧
        T.natDegree≤t.natDegree∧reduce a r.derivative=R.derivative
private theorem cast_small [CharP L p] {n:ℕ} (hpos :0<n) (h:n<p) :
   (n:L)≠0:= fun hz =>
 (not_le_of_gt h) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff L p n).mp hz))
set_option maxHeartbeats 400000 in
private theorem pole_degree {den T R U B C:L[X]}
    (hT:T≠0) (hRUB:R*U*B≠0) (hdiv :T∣R*U*B)
    (htame :T.natDegree<p) (hden:den∣T) (hder :den∣T.derivative)
    (hcontent : ∀ x,den.eval x=0 →
      U.rootMultiplicity x=C.rootMultiplicity x∧B.rootMultiplicity x=C.rootMultiplicity x) :
    den.natDegree≤gcdDegree R R.derivative+2*C.natDegree := by
  classical
  let G:=GCDMonoid.gcd R R.derivative
  have hR:R≠0:=left_ne_zero_of_mul (left_ne_zero_of_mul hRUB)
  have hG:G≠0:=gcd_ne_zero_of_left hR
  have hn:den≠0:= by rintro rfl; exact hT (zero_dvd_iff.mp hden)
  let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  have hroots :den.roots≤G.roots+C.roots+C.roots := by
    rw [Multiset.le_iff_count]
    intro x
    simp only [Multiset.count_add,count_roots]
    by_cases hd:den.eval x=0
    swap
    · simp [rootMultiplicity_eq_zero hd]
    have hdpos :=(rootMultiplicity_pos hn).mpr hd
    have hdt:=rootMultiplicity_le_rootMultiplicity_of_dvd hT hden x
    have htpos :=hdpos.trans_le hdt
    have htdeg:T.rootMultiplicity x≤T.natDegree := by
      have h:=natDegree_le_of_dvd (T.pow_rootMultiplicity_dvd x) hT
      simpa only [natDegree_pow,natDegree_X_sub_C,mul_one] using h
    have hcast:=cast_small htpos (htdeg.trans_lt htame)
    have hTroot :=(rootMultiplicity_pos hT).mp htpos
    have he :=derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hTroot
      (mem_nonZeroDivisors_iff_ne_zero.mpr hcast)
    have hdegree :=htpos.trans_le htdeg
    have hTder :T.derivative≠0:= by
      intro h
      have hcoef :=congrArg (fun g:L[X]=>g.coeff (T.natDegree-1)) h
      exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hT) (cast_small hdegree htame))
        (by simpa only [coeff_derivative,coeff_zero,← Nat.cast_add_one,
          Nat.sub_add_cancel hdegree,coeff_natDegree] using hcoef)
    have hdd:=rootMultiplicity_le_rootMultiplicity_of_dvd hTder hder x
    rw [he] at hdd
    have hTbound:=rootMultiplicity_le_rootMultiplicity_of_dvd hRUB hdiv x
    rw [rootMultiplicity_mul hRUB,rootMultiplicity_mul (left_ne_zero_of_mul hRUB),
      (hcontent x hd).1,(hcontent x hd).2] at hTbound
    have hRbound:R.rootMultiplicity x - 1≤G.rootMultiplicity x :=
      (le_rootMultiplicity_iff hG).2
        (dvd_gcd
          ((pow_dvd_pow _ (Nat.sub_le _ _)).trans (R.pow_rootMultiplicity_dvd x))
          (pow_sub_one_dvd_derivative_of_pow_dvd (R.pow_rootMultiplicity_dvd x)))
    omega
  have hc:=Multiset.card_le_card hroots
  simp only [Multiset.card_add,IsAlgClosed.card_roots_eq_natDegree] at hc
  change _≤G.natDegree+2*C.natDegree
  omega
theorem of_children (Oj:c1) (vertical:c2) (specialize :c3) (radical:c4) :
  qxPDCsa.c4 := by
 intro q Cq z S F V D W A r t hF ht hr hrad γ hγ hg
 let a :=F.atPlace γ (V.Bp hγ)
 obtain ⟨hn,hprod,hdiv,hdeg,hdiff⟩:=radical A r t hr hrad γ hγ hg
 obtain ⟨hden,hd'⟩:=specialize A t hrad γ hγ hg
  (vertical A t hF hrad γ hγ hg (Oj A t hF hrad γ hγ hg))
 change (V.den γ).natDegree≤gcdDegree (reduce a r) (reduce a r.derivative) +
  2*(contentAt F (V.Bp hγ)).natDegree
 rw [hdiff]
 exact pole_degree hn hprod hdiv (hdeg.trans_lt ht) hden hd'
  (fun x hx=>⟨A.content_order γ hγ x hx 0,A.content_order γ hγ x hx 1⟩)
end
end qqV3gre
end
section
set_option autoImplicit true
namespace q5rLXAc
theorem proof :P5_7_3_5_2_1.c1 :=q9Dxm8d.proof
end q5rLXAc
end
section
namespace qNdtvka
theorem proof :P5_7_3_5_2_1.c2 := by
 intro q hq Cq s hs
 obtain ⟨hz,i,hi⟩:=hs
 obtain ⟨a,hc,ha,hfree⟩:=qz11UBb.formalLift q s i hz hi
 obtain ⟨j,hji⟩:=exists_ne i
 refine qqpP4De.proof hq Cq s ⟨a,hc,ha,j,?_⟩
 rw [hfree j hji]
 simp
end qNdtvka
end
