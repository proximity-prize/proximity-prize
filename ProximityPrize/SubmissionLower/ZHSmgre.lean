import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZK3v1Id
import ProximityPrize.SubmissionLower.Z3e8uLd
import ProximityPrize.SubmissionLower.ZoU8PJb
import ProximityPrize.SubmissionLower.ZloDYIb
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.ZRSUmIe
set_option Elab.async false
open _root_ renaming MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.ringHom_ext → zXT, Polynomial.map_map → zoi, RingHom.comp_apply → zQb
section
set_option autoImplicit true
namespace q7F2qKe
noncomputable section
open Finset
open scoped BigOperators Classical

open cu (Shape)
open pI (pN)
open TD (GM J2 FP)

private theorem swap_tail (n:ℕ) (x y :ℕ→ℚ) :
    (∑ j∈range n,(∑ i∈range (j+1),x i)*y j) =
      ∑ i∈range n,x i*∑ j∈(range n).filter (i ≤ ·),y j:= by
  calc
    _ = ∑ j∈range n,∑ i∈range n,if i≤j then x i*y j else 0:= by
      apply sum_congr rfl
      intro j hj
      have he : (range n).filter (· ≤ j)=range (j+1) := by
        ext i
        simp only [mem_filter,mem_range]
        have :=mem_range.mp hj
        omega
      rw [← he,sum_mul,sum_filter]
    _ = ∑ i∈range n,∑ j∈range n,if i≤j then x i*y j else 0:=sum_comm
    _ = _:= by simp only [sum_filter,mul_sum,mul_ite,mul_zero]
private theorem crE {α:Type*} (s :Finset α) (w:GM) (x :α→GM) :
  (∑ a∈s,FP w (x a))=FP w (fun k => ∑ a∈s,x a k) := by
 simp only [FP,mul_sum]
 exact sum_comm
theorem dot_mass (s :Finset (Ideal gT.Ambient)) (w:GM) :
  (∑ I∈s,FP w (fun k=>pN I k))=FP w (J2 s) := by
 rw [crE]
 apply congrArg (FP w)
 funext k
 simp only [J2,pI.mass,Nat.cast_sum]
private theorem dot_add (u v w x :GM) :
  FP (fun k=>u k+v k+w k) x=FP u x+FP v x+FP w x := by
 simp only [FP,add_mul,sum_add_distrib]
private theorem matrix_dot (w:GM) (s :Shape) (r :bTu) :
  FP w (fun k=>kK r s k)=dotResources (factorUnit w s) r := by
 simp only [FP,kK,dotResources,factorUnit,Nat.cast_sum,Nat.cast_mul,mul_sum,sum_mul]
 rw [sum_comm]
 apply sum_congr rfl
 intro k _
 apply sum_congr rfl
 intro j _
 ring
end
end q7F2qKe
end
section
set_option autoImplicit true
namespace qWdRihc
noncomputable section
open Polynomial
open P5 (K p)
open cu (FX L Equation vm yq j9 Vg)
open Y3 (Dg JS aLS normalize)
open private swap bOH gxQ dcB compress from ProximityPrize.SubmissionLower.BJ
open private azZ abn cZx gK4 from ProximityPrize.SubmissionLower.BJ
private def view:JS →+* nC :=
 (mapRingHom (Vg (F:=L) p).toRingHom).comp swap.toRingHom
private theorem graph_at (z :L) :
   (evalRingHom z).comp (Vg (F:=L) p).toRingHom =
     zY9 ![z,z^p] := by
 apply zXT
 · intro c
   simp [Vg]
 · intro i
   fin_cases i <;> simp [Vg]
private theorem swap_C (f :L[X]) :swap (znf f) =
    f.map (znf:L →+* MvPolynomial (Fin 2) L) := by
  induction f using Polynomial.induction_on' with
  | add a b ha hb=>simp only [map_add,Polynomial.map_add,ha,hb]
  | monomial n c =>
    have hc:swap (znf (C c))=C (znf c) := by
      unfold swap
      rw [AlgEquiv.trans_apply,← MvPolynomial.optionEquivRight_C,
        AlgEquiv.symm_apply_apply,MvPolynomial.optionEquivLeft_C]
    have hx :swap (znf (Polynomial.X:L[X]))=Polynomial.X:= by
      simpa only [pow_one] using gxQ 1
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul,map_pow,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,
      Polynomial.map_X,hx,hc]
private theorem swap_X (i:Fin 2) :swap (z9v i) =
  C (z9v i) := by
 unfold swap
 rw [AlgEquiv.trans_apply,← MvPolynomial.optionEquivRight_X_some (R:=L),
  AlgEquiv.symm_apply_apply,MvPolynomial.optionEquivLeft_X_some]
private theorem view_at (z :K) :
    (specialize (algebraMap K L z)).comp view =
      zY9 (C ∘ abn z p) := by
  apply zXT
  · intro c
    simp only [zQb,MvPolynomial.eval_C]
    change (swap (znf c) |>.map (Vg (F:=L) p).toRingHom).map
      (evalRingHom (algebraMap K L z))=c
    rw [swap_C,zoi,zoi,graph_at]
    have he : (zY9 ![algebraMap K L z,(algebraMap K L z)^p]).comp
        (znf:L →+* MvPolynomial (Fin 2) L)=RingHom.id L:= by
      ext a
      simp
    rw [he,Polynomial.map_id]
  · intro i
    change (swap (z9v i) |>.map (Vg (F:=L) p).toRingHom).map
      (evalRingHom (algebraMap K L z))= _
    rw [swap_X,zoi,graph_at,Polynomial.map_C]
    fin_cases i <;> simp [abn]
private theorem view_bounded {G:Dg} {v :ℕ} (hv :aLS G v) (j:ℕ) :
   Bounded (view (G.coeff j)) ((p+1)*v) := by
 intro i
 let q:=(swap (G.coeff j)).coeff i
 have hs :q.totalDegree≤v :=(dcB (G.coeff j) v).mp (hv j) i
 simp only [view,zQb,coe_mapRingHom,coeff_map]
 change ((Vg p) q).natDegree≤(p+1)*v
 simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm v] using
   cu.b33 p v v q
     ((q.degreeOf_le_totalDegree 0).trans hs) ((q.degreeOf_le_totalDegree 1).trans hs)
private theorem view_ne_zero {G:Dg} {v :ℕ} (hv :aLS G v)
  (hp:v<p) {j:ℕ} (hn:G.coeff j≠0) :view (G.coeff j)≠0:= by
 obtain ⟨i,hi⟩:=Polynomial.support_nonempty.mpr (fun h =>
  hn (swap.injective (h.trans (map_zero _).symm)))
 let q:=(swap (G.coeff j)).coeff i
 have hs :q.totalDegree≤v :=(dcB (G.coeff j) v).mp (hv j) i
 intro hz
 have he :=congrArg (fun f :nC=>f.coeff i) hz
 simp only [view,zQb,coe_mapRingHom,coeff_map] at he
 change (Vg p) q=(0:nC).coeff i at he
 rw [coeff_zero] at he
 exact cu.bG0 p (by decide) q (Polynomial.mem_support_iff.mp hi)
  ((q.degreeOf_le_totalDegree 0).trans_lt (hs.trans_lt hp)) he
private theorem gLc {G:Dg} {n:ℕ} (hn:0<n)
  (hw : ∀ j m,(G.coeff j).coeff m≠0→((G.coeff j).coeff m).natDegree+j*d<n)
  (j:ℕ) : (view (G.coeff j)).natDegree<n:= by
 apply (natDegree_map_le (f :=(Vg (F:=L) p).toRingHom)).trans_lt
 change (swap (G.coeff j)).natDegree<n
 suffices (swap (G.coeff j)).natDegree≤n-1 by omega
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro i hi
 by_contra h
 obtain ⟨m,hm⟩:=MvPolynomial.support_nonempty.mpr h
 have hz :=MvPolynomial.mem_support_iff.mp hm
 rw [bOH] at hz
 have hdeg:=le_natDegree_of_ne_zero hz
 have hb:=hw j m (fun he=>hz (by rw [he,coeff_zero]))
 omega
private theorem fTZ {G:Dg} {n:ℕ} (hn:0<n)
   (hw : ∀ j m,(G.coeff j).coeff m≠0→((G.coeff j).coeff m).natDegree+j*d<n)
   (t:Fin 2→L) {S:K[X]} (hS:S.natDegree≤d) : (azZ t S G).natDegree<n:= by
 classical
 apply Nat.lt_of_le_pred hn
 change (G.eval₂ (zY9 (C ∘ t)) (j9 S)).natDegree≤n-1
 rw [eval₂_eq_sum,Polynomial.sum_def]
 apply natDegree_sum_le_of_forall_le
 intro j _
 rw [MvPolynomial.eval_eq,Finset.sum_mul]
 apply natDegree_sum_le_of_forall_le
 intro m hm
 rw [show (∏ i∈m.support,(C ∘ t) i^m i)=C (∏ i∈m.support,t i^m i) by
   simp only [Function.comp_apply,map_prod,map_pow]]
 have hbound:=hw j m (MvPolynomial.mem_support_iff.mp hm)
 have hpow: ((j9 S)^j).natDegree≤j*d :=
   natDegree_pow_le.trans (Nat.mul_le_mul_left _
     ((natDegree_map_le (f :=algebraMap K L) (p:=S)).trans hS))
 exact (natDegree_mul_le_of_le (natDegree_mul_C_le ((G.coeff j).coeff m) _) hpow).trans
   (Nat.le_pred_of_lt hbound)
private theorem quadratic_eval {G:Dg} (hG:G.natDegree≤2)
    (z :K) (S:K[X]) :
    azZ (abn z p) S G =
      specialize (algebraMap K L z) (view (G.coeff 2))*(j9 S)^2 +
        specialize (algebraMap K L z) (view (G.coeff 1))*j9 S +
        specialize (algebraMap K L z) (view (G.coeff 0)) := by
  have h G' : specialize (algebraMap K L z) (view G') =
      zY9 (C ∘ abn z p) G' :=
    RingHom.congr_fun (view_at z) G'
  simp only [h]
  change G.eval₂ (zY9 (C ∘ abn z p)) (j9 S)= _
  conv_lhs=>rw [G.as_sum_range' 3 (by omega)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,eval₂_add,
    eval₂_monomial,pow_zero,pow_one,mul_one,zero_add]
  ac_rfl
theorem shorten (J:UJ) (z' : K→K) (hz : ∀ γ,J.z γ=algebraMap K L (z' γ))
   (f :Equation) (hn:f≠0) (he :f.natDegree≤2) (hv :vm f seedCap)
   (hr : ∀ γ∈J.CF,yq f (z' γ) (J.scalar γ)=0) :
   ∃ a b c:nC,(a≠0∨b≠0∨c≠0) ∧
     Bounded a height∧Bounded b height∧Bounded c height ∧
     a.natDegree< modulus∧b.natDegree< modulus∧c.natDegree< modulus ∧
     ∀ γ∈J.CF,Zk J a b c γ:= by
 obtain ⟨Q,α,_,hQ,hQe,hQv,hterm⟩:=normalize f 2 seedCap hn he hv
 obtain ⟨H,G,B,hcong,hG,hGe,hGv,hw⟩ :=
   compress 2 d seedCap extra modulus (by decide) (by decide) Q hQe hQv hterm
 have hn' : ∃ j≤2,G.coeff j≠0 :=
   ⟨G.natDegree,hGe,by simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hG⟩
 obtain ⟨j,hj,hne⟩:=hn'
 have hvn:=view_ne_zero hGv (by decide) hne
 have hcases :j=0∨j=1∨j=2 := by omega
 refine ⟨view (G.coeff 2),view (G.coeff 1),view (G.coeff 0),?_,
   view_bounded hGv 2,view_bounded hGv 1,view_bounded hGv 0,
   gLc (by decide) hw 2,gLc (by decide) hw 1,gLc (by decide) hw 0,?_⟩
 · rcases hcases with rfl | rfl | rfl
   · exact Or.inr (Or.inr hvn)
   · exact Or.inr (Or.inl hvn)
   · exact Or.inl hvn
 · intro γ hγ
   let z :=z' γ
   let S:=J.scalar γ
   have hzero :azZ (abn z p) S Q=0:= by
     apply IsFractionRing.injective (Polynomial L) FX
     rw [cZx,map_zero,hQ]
     change (Y3.constant α*f).eval₂ (cu.qD z) (cu.kr S)=0
     have hr' : f.eval₂ (cu.qD z) (cu.kr S)=0:=hr γ hγ
     rw [eval₂_mul,hr',mul_zero]
   have hvan:=gK4 (abn z p) S hzero hcong
     (fTZ (by decide) hw _ (J.degree γ hγ))
   simpa only [Zk,hz,← quadratic_eval hGe] using hvan
end
end qWdRihc
end
