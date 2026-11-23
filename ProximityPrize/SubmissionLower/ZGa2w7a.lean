import ProximityPrize.SubmissionLower.ZdBkMOd
import ProximityPrize.SubmissionLower.ZgEngac
import ProximityPrize.SubmissionLower.ZEQaUSb
import ProximityPrize.SubmissionLower.ZVQ2TVd
import ProximityPrize.SubmissionLower.ZTqYzLd
import ProximityPrize.SubmissionLower.ZrgYIVd
import ProximityPrize.SubmissionLower.ZkMhvdb
set_option Elab.async false
open _root_ renaming Finsupp.optionElim_some → zX5, Finsupp.weight_optionElim → zVB, LinearMap.ker → z83, LinearMap.mulLeft → zzN, LinearMap.range → zWl, Module.Finite → zAa, Module.finrank → zsE, Nat.add_le_add_left → z3b, Nat.lt_succ_of_le → zB1, Nat.mul_le_mul_left → zBI, Polynomial.X → z7y, Submodule → zpI, Submodule.finrank_mono → zFM
section
section
set_option autoImplicit true
namespace qqXHigb
open cu (Shape triangle)
open agU (arY)
open P5_7_2 (fO row poleRowsAt)
open P5_7_4 (poleRank)
open qZyoMPc (aP4 bound)
open private slice profile from ProximityPrize.SubmissionLower.ZgEngac
open private bcT auf from ProximityPrize.SubmissionLower.A2
private theorem slice_affine (B J u q d:ℤ) :
  slice B J u q d=slice B J 0 q d+u*(slice B J 1 q d - slice B J 0 q d) := by
 unfold slice bcT
 ring
private theorem antidifference_affine (f g h:ℤ→ℤ) (u n:ℤ)
  (he : ∀ i,f i=g i+u*(h i - g i)) :
  auf f n=auf g n+u*(auf h n-auf g n) := by
 simp only [auf,he]
 ring
private theorem piece_affine (B J u start offset slope n:ℤ) :
    auf (profile B J u start offset slope) n =
      auf (profile B J 0 start offset slope) n+u *
        (auf (profile B J 1 start offset slope) n -
         auf (profile B J 0 start offset slope) n) :=
  antidifference_affine _ _ _ _ _ fun i=>slice_affine B J u (start+i) (offset+slope*i)
private theorem sW (B J u:ℕ) :
  aP4 B J u=aP4 B J 0+(u:ℤ)*(aP4 B J 1-aP4 B J 0) := by
 simp only [aP4,Nat.cast_zero,Nat.cast_one]
 rw [piece_affine (B:ℤ) J u 0 0 1,piece_affine (B:ℤ) J u J J 0]
 ring
private theorem profile_bound (s :Shape) (m e :ℕ) (hj:s.J≤ s.B) (hu:s.B≤ s.U)
  (h0:aP4 s.B s.J 0=2880*((m:ℤ)-e))
  (h1 :aP4 s.B s.J 1=2880*(2*(m:ℤ)-e)) :
  poleRank s≤triangle s.U*arY s+(m*(s.U+1)-e) := by
 apply bound _ _ hj hu
 have he :aP4 s.B s.J s.U=2880*((m:ℤ)*((s.U:ℤ)+1)-e) := by
  rw [sW,h0,h1]
  ring
 have hs : ((m*(s.U+1) :ℕ) :ℤ)-e≤((m*(s.U+1)-e :ℕ) :ℤ) := by omega
 rw [he]
 push_cast at hs
 exact mul_le_mul_of_nonneg_left hs (by decide)
private theorem first_profile (b:fO) (hb:b.val<4) :
  (row b).shape.B=2927∧(row b).shape.J=619:= by
 fin_cases b <;> first | decide | contradiction
private theorem second_profile (b:fO) (hl : ¬ b.val<4) (hu:b.val<12) :
  (row b).shape.B=3624∧(row b).shape.J=767:= by
 fin_cases b <;> first | decide | contradiction
theorem proof :qjf96Pd.c2 := by
 intro b hb u hu
 let s := { (row b).shape with U:=u }
 change poleRank s≤triangle u*arY s+poleRowsAt b u
 have hj:s.J≤ s.B:=(qjf96Pd.bank_guards b).2.2.1
 rw [poleRowsAt,ite_eq_right (Nat.not_le_of_lt hb)]
 split
 · rename_i h
   have hB:s.B=2927:=(first_profile b h).1
   have hJ:s.J=619:=(first_profile b h).2
   refine profile_bound s 0x1cccacb1996 0x47c4a7d1ca8f0 hj hu ?_ ?_ <;> rw [hB,hJ] <;> rfl
 · rename_i h
   have hB:s.B=3624 :=(second_profile b h hb).1
   have hJ:s.J=767:=(second_profile b h hb).2
   refine profile_bound s 0x43ae6a1ea00 0xd0d1138a56500 hj hu ?_ ?_ <;> rw [hB,hJ] <;> rfl
end qqXHigb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qgB1P4c

open DP (pW)
open Ge anc qcT6PRb Polynomial Finset
noncomputable section
abbrev Target (F:Type) [Field F] :=EM (kq F)
abbrev x (F:Type) [Field F] :Target F:=pW (z7y (R:=kq F))
def seed {F:Type} [Field F] (i:Fin 2) :kq F :=
 algebraMap (i5 F) (kq F) (MvPolynomial.X i)
end
end qgB1P4c
end
section
set_option autoImplicit true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace qB9xHGe
theorem b0:BudgetRows ⟨0,by decide⟩:=budget! 12 13 13 27
theorem b1 :BudgetRows ⟨1,by decide⟩:=budget! 12 13 14 28
theorem b2 :BudgetRows ⟨2,by decide⟩:=budget! 12 13 14 28
theorem b3:BudgetRows ⟨3,by decide⟩:=budget! 12 13 14 28
end qB9xHGe
end
section
set_option autoImplicit true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace qB9xHGe
theorem b4 :BudgetRows ⟨4,by decide⟩:=budget! 12 13 14 28
theorem b5:BudgetRows ⟨5,by decide⟩:=budget! 12 13 14 28
theorem b6:BudgetRows ⟨6,by decide⟩:=budget! 12 13 14 28
theorem b7:BudgetRows ⟨7,by decide⟩:=budget! 11 12 13 29
theorem b8:BudgetRows ⟨8,by decide⟩:=budget! 12 13 13 28
end qB9xHGe
end
section
set_option autoImplicit true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace qB9xHGe
theorem b9:BudgetRows ⟨9,by decide⟩:=budget! 13 14 13 26
theorem b10 :BudgetRows ⟨10,by decide⟩:=budget! 13 14 13 26
theorem b11 :BudgetRows ⟨11,by decide⟩:=budget! 13 14 13 23
theorem b12 :BudgetRows ⟨12,by decide⟩:=budget! 13 14 13 23
theorem b13:BudgetRows ⟨13,by decide⟩:=budget! 13 14 13 23
end qB9xHGe
end
end
section
set_option autoImplicit true
namespace qPQ4nYa
noncomputable section
open aR (ao)
open Rj (Flat Exp BU indexWeight oH La)
open qlc9qed (Bank)
open MvPolynomial
private theorem high_vanishes (b : Bank) (e : Exp) (c : ao) (he : b.m ≤ e none) :
    origin b (monomial e c) = 0 := by
  change weightedTruncation oH b.m (bind₁ La (monomial e c)) = 0
  apply (weightedTruncation_eq_zero_iff _ _ _).mpr
  refine bind₁_mem_restrictWeightedOrder
    (w := fun v : Option (Fin 3) => v.elim 1 (fun _ => 0)) ?_ ?_
  · intro v
    cases v with
    | none =>
      simpa [La] using
        (X_mem_restrictWeightedOrder (R := ao) oH
          (none : Option (Fin 3)) (m := 1) (by rfl))
    | some j => simp
  · apply (monomial_mem_restrictWeightedOrder _ _ _ _).mpr
    exact Or.inl (by simpa only [Finsupp.weight_elim_one_zero] using he)
private def aTg (b : Bank) (i : ℕ × ℕ) : zpI ao Flat :=
  zWl (af3 b i.1 i.2)
private instance (b : Bank) (i : ℕ × ℕ) : zAa ao (aTg b i) :=
  Module.Finite.range (af3 b i.1 i.2)
private def pairs (b : Bank) : Finset (ℕ × ℕ) :=
  Finset.range (b.box.b + 1) ×ˢ Finset.range (b.m + b.box.j)
private theorem cen (b : Bank) : originRange b ≤ (pairs b).sup (aTg b) := by
  classical
  intro P hP
  obtain ⟨Q, rfl⟩ := LinearMap.mem_range.mp hP
  change origin b Q.val ∈ (pairs b).sup (aTg b)
  have expand := congrArg (origin b) Q.val.as_sum
  rw [map_sum] at expand
  rw [expand]
  refine Submodule.sum_mem _ fun e he => ?_
  by_cases hi : b.m ≤ e none
  · rw [high_vanishes b e (Q.val.coeff e) hi]
    exact Submodule.zero_mem _
  have hbox : FF b e := Q.property he
  let q := e.weight BU
  let k := e none + (b.box.j - e.weight indexWeight)
  have hmem : (q, k) ∈ pairs b := by
    simp only [pairs, Finset.mem_product, Finset.mem_range]
    have hq := hbox.1
    dsimp [q, k]
    omega
  apply (Finset.le_sup (f := aTg b) hmem)
  refine LinearMap.mem_range.mpr ⟨⟨monomial e (Q.val.coeff e), ?_⟩, rfl⟩
  intro u hu
  have hue : u = e := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hu) (by simp [coeff_monomial, Ne.symm hne])
  subst u
  refine ⟨hbox, rfl, ?_⟩
  have hj := hbox.2.1
  dsimp [offset, k]
  omega
private theorem finrank_sup_le (b : Bank) (S : Finset (ℕ × ℕ)) :
    zsE ao (S.sup (aTg b) : zpI ao Flat) ≤
      ∑ i ∈ S, zsE ao (aTg b i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank (aTg b i) (S.sup (aTg b))).trans
      (z3b ih _)
end
end qPQ4nYa
end
section
set_option autoImplicit true
namespace qs0zuzc
open Finset
open P5 (p)
open P5_7_2 (Aux)
open qMNIwTb (aL4 capSum fullCap O3)
open cu (Shape ku triangle)
open DP (bga)
open agU (ad1 ajD)
open czX (a8x dei)
open private cck from ProximityPrize.SubmissionLower.E7
open private cut origin b7r cpY biN amv gxx gMy from ProximityPrize.SubmissionLower.ZkMhvdb
private def score (s :Shape) (r lo mode M:ℕ) (h:ℤ) :ℤ :=
  (triangle s.U:ℤ) *
    (b7r s r lo mode+(h-lo)*cpY s r lo mode -
      2*(262144*a8x (s.m-2*s.J) s.J:ℕ)) -
    24*h*((s.U:ℤ)+1)*M
private def mode (move :Bool) :ℕ:=if move then 1 else 0
def check (lo hi:ℕ) (a :Aux) (move :Bool) (M:ℕ) :Bool :=
  let s :=a.shape
  let r :=a.dI
  decide (hi≤131071) && decide (s.B<p) &&
    decide (2*s.J≤ s.m) && decide (s.m+s.J≤ s.B+1) &&
    decide (s.J≤ cut s r lo (mode move)) &&
    decide (0<biN s r lo) && decide (0<biN s r hi) &&
    decide (0<score s r lo (mode move) M lo) &&
    decide (0<score s r lo (mode move) M hi)
def Good (lo hi:ℕ) (a :Aux) (move :Bool) :Prop :=
  ∀ h,lo≤h→h≤hi→a.shape.B<p∧aL4 h a ∧
    bga a.shape+2*h*((a.shape.U+1)*ajD a.shape.B a.shape.J) <
      O3 h a (fullCap a.shape) move
private theorem between {f :ℤ→ℤ} {lo hi h:ℕ}
    (hl:lo≤h) (hu:h≤hi)
    (ha : ∀ x,f x=f lo+(x-lo)*(f ((lo:ℤ)+1)-f lo))
    (h₀:0<f lo) (h₁:0<f hi) :0<f h:= by
  rw [ha (hi:ℤ)] at h₁
  rw [ha (h:ℤ)]
  exact cck (Int.ofNat_le.mpr hl) (Int.ofNat_le.mpr hu) h₀ h₁
theorem checked {lo hi:ℕ} {a :Aux} {move :Bool} {M:ℕ}
    (hmoment:ajD a.shape.B a.shape.J≤M)
    (hc:check lo hi a move M=true) :Good lo hi a move := by
  intro h hl hu
  let s :=a.shape
  let r :=a.dI
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk,hp⟩,hm⟩,hB⟩,hj⟩,hw₀⟩,hw₁⟩,hs₀⟩,hs₁⟩:=hc
  have hh:=hu.trans hk
  have hw:=between hl hu (f :=biN s r)
    (fun x=> by unfold biN origin; ring) hw₀ hw₁
  have hs :=between hl hu (f :=score s r lo (mode move) M)
    (fun x=> by unfold score; ring) hs₀ hs₁
  have ht:=mul_le_mul_of_nonneg_left (gxx s r lo h (mode move) hh hj)
    (Int.natCast_nonneg (triangle s.U))
  have hn:=congrArg (fun n:ℕ=>(n:ℤ)) (dei s hm hB)
  have hd:bga s=triangle s.U*ad1 s := by
    unfold bga ad1
    rw [Nat.mul_assoc]
  have hg:O3 h a (fullCap s) move =
      triangle s.U*ku s (fun q j=>amv h r s q j - mode move*(2*h*j)) := by
    cases move <;>
      simp only [O3,capSum,ku,fullCap,mode,Bool.false_eq_true,ite_false,
        ite_true,zero_mul,one_mul] <;> rfl
  refine ⟨hp,?_,?_⟩
  · exact gMy s r h hh hw
  · apply lt_of_le_of_lt (z3b
      (zBI (2*h) (zBI (s.U+1) hmoment)) _)
    change bga s+2*h*((s.U+1)*M)<_
    rw [hg,hd]
    apply Int.ofNat_lt.mp
    unfold score at hs
    rw [← hn] at hs
    push_cast at hs ⊢
    linarith only [hs,ht]
end qs0zuzc
end
section
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qSxbgdc
noncomputable section
open aR (ao)
open jA
open NR (TT)
open Rj (Flat Exp BU indexWeight topWeight J6 oH)
open P5_7_2 (TopRow)
open q7IA62d (Aw clearance coord ays mem_ambient bsz)
open ReedSolomon.HiddenDerivative MvPolynomial
open scoped Polynomial
open private AV Bg Ky aob ec6 normalize eE1 dPj from ProximityPrize.SubmissionLower.S
private theorem flat_capped {b:TopRow} {F:jK} (h1 :vC F≤b.shape.B)
   (h2 :lP F≤b.shape.J) (h3:F.degreeOf (some 2)≤b.YM) (n:ℕ) :
   aob n F∈apR b:= by
 intro e he
 change e∈(aob n F).support at he
 have hc:=MvPolynomial.mem_support_iff.mp he
 rw [ec6] at hc
 have hs :e.some.optionElim n∈F.support :=
   MvPolynomial.mem_support_iff.mpr (fun h=>hc (by rw [h,Polynomial.coeff_zero]))
 have hb:=(le_weightedTotalDegree BU hs).trans h1
 have hj:=(le_weightedTotalDegree indexWeight hs).trans h2
 have ht:=(degreeOf_le_iff.mp h3) _ hs
 have hg (i:ℕ) : (e.some.optionElim i).weight BU=e.some.weight (fun _=>1) := by
   unfold BU
   rw [zVB,zero_mul,zero_add]
 have hi (i:ℕ) : (e.some.optionElim i).weight indexWeight=e.some.weight Fin.val := by
   unfold indexWeight
   rw [zVB,zero_mul,zero_add]
 change e.weight BU≤b.shape.B∧e.weight indexWeight≤b.shape.J∧e (some 2)≤b.YM
 have heq :=zX5 e
 rw [hg] at hb
 rw [hi] at hj
 refine ⟨?_,?_,?_⟩
 · exact (congrArg (Finsupp.weight BU) heq).symm.le.trans ((hg (e none)).le.trans hb)
 · exact (congrArg (Finsupp.weight indexWeight) heq).symm.le.trans ((hi (e none)).le.trans hj)
 · simpa using ht
private theorem normalize_capped {b:TopRow} {Q:Flat} (h:Q∈apR b) (x v :ao) :
    normalize x v Q∈apR b:= by
  have preserve (w:Option (Fin 3)→ℕ) (a :ℕ)
      (hQ : ∀ e∈Q.support,e.weight w≤a) :
      ∀ e∈(normalize x v Q).support,e.weight w≤a :=
    mem_restrictWeightAtMost.mp
      (globalPointTranslation_mem_restrictWeightAtMost (Nat.zero_le _) (Nat.zero_le _)
        x v (mem_restrictWeightAtMost.mpr hQ))
  have htop (e :Exp) :e.weight topWeight=e (some 2) := by
    conv_lhs=>rw [← zX5 e]
    unfold topWeight
    rw [zVB,zero_mul,zero_add,Finsupp.weight_single_one_apply]
    simp
  intro e he
  exact ⟨preserve BU _ (fun t ht=>(h ht).1) e he,
    preserve indexWeight _ (fun t ht=>(h ht).2.1) e he,
    htop e ▸ preserve topWeight _ (fun t ht=>(htop t).symm ▸ (h ht).2.2) e he⟩
private theorem contact_of_origin_zero (b:TopRow) (x v :ao) (F:jK)
   (h : ∀ n:ℕ,origin b (normalize x v (aob n F))=0) :F∈ays b x v := by
 apply bsz.mpr
 intro e
 let E :=Polynomial.taylorEquiv x
 have hX:E (z7y-Polynomial.C x)=Polynomial.X:= by
   rw [map_sub]
   change Polynomial.taylor x z7y-Polynomial.taylor x (Polynomial.C x)= _
   simp
 rw [← map_dvd_iff E,map_pow,hX,Polynomial.X_pow_dvd_iff]
 intro i hi
 have hc:E ((aCk x v F).coeff e) =
     (Ky (J6 (normalize x v (aob (e none) F)))).coeff e.some := by
   rw [eE1,zX5]
   rfl
 rw [hc]
 change ((optionEquivRight ao (Fin 3) _).coeff e.some).coeff i=0
 rw [optionEquivRight_coeff_coeff]
 have hz :=congrArg (fun Q:Flat=>Q.coeff (e.some.optionElim i)) (h (e none))
 change (weightedTruncation oH b.shape.m
   (J6 (normalize x v (aob (e none) F)))).coeff (e.some.optionElim i)=0 at hz
 have hlt: (e.some.optionElim i).weight oH<b.shape.m:= by
   rw [dPj]
   change i+3*e (some 0)<b.shape.m
   omega
 rw [coeff_weightedTruncation] at hz
 simpa only [hlt,ite_true] using hz
theorem finite_ambient (h:ℕ) (b:TopRow) (W:ℕ) :
    zAa ao (Aw h b W) := by
  classical
  let V:=Aw h b W
  let T:=W+clearance h b
  let N :=max b.shape.B b.shape.U + 1
  let E :=mA→Fin N
  let f :V →ₗ[ao] ((E×Fin (T+1))→ao) :=LinearMap.pi fun p =>
    (coord (Finsupp.equivFunOnFinite.symm (fun i=>(p.1 i).val)) p.2).comp V.subtype
  have hzero (Q:V) (hz :f Q=0) :Q=0:= by
    have hF:=mem_ambient.mp Q.property
    apply Subtype.ext
    apply MvPolynomial.ext
    intro a
    change Q.val.coeff a=0
    by_contra hn
    have ha :=MvPolynomial.mem_support_iff.mpr hn
    have hd: (Q.val.coeff a).natDegree≤T:=(Nat.le_add_right ..).trans (hF.2.2.2.2 a ha)
    have hb:=MvPolynomial.le_weightedTotalDegree BU ha
    have he (i:mA) :a i<N := by
      cases i with
      | none =>
        exact zB1 ((MvPolynomial.monomial_le_degreeOf _ ha).trans
          (hF.2.2.2.1.trans (le_max_right _ _)))
      | some j =>
        exact zB1 ((Finsupp.le_weight BU (s :=some j) Nat.one_ne_zero a).trans
          (hb.trans (hF.1.trans (le_max_left _ _))))
    let e :E := fun i=>⟨a i,he i⟩
    have hv :=congrFun hz (e,⟨_,zB1 hd⟩)
    change (Q.val.coeff (Finsupp.equivFunOnFinite.symm (fun i=>(e i).val))).coeff
      (Q.val.coeff a).natDegree=0 at hv
    rw [show Finsupp.equivFunOnFinite.symm (fun i=>(e i).val)=a from
      Finsupp.equivFunOnFinite.symm_apply_apply a,Polynomial.coeff_natDegree] at hv
    exact (Polynomial.leadingCoeff_ne_zero.mpr hn) hv
  apply Module.Finite.of_injective f
  intro Q R he
  apply sub_eq_zero.mp
  apply hzero
  rw [f.map_sub Q R,he,sub_self]
theorem codim_le_origin_gen (b:TopRow) (x v :ao) (V:zpI ao jK)
    [zAa ao V]
    (hcap : ∀ F∈V,vC F≤b.shape.B∧lP F≤b.shape.J ∧
      F.degreeOf (some 2)≤b.YM∧gY F≤b.shape.U) :
    TT V (ays b x v)≤(b.shape.U + 1)*zsE ao (originRange b) := by
  let A:V →ₗ[ao] (Fin (b.shape.U + 1)→ originRange b) :=LinearMap.pi fun n =>
    ((origin b).domRestrict (apR b)).rangeRestrict ∘ₗ
      (((normalize x v).toLinearMap ∘ₗ aob n ∘ₗ V.subtype).codRestrict _
        (fun F=>normalize_capped (flat_capped (hcap F F.property).1 (hcap F F.property).2.1 (hcap F F.property).2.2.1 n) x v))
  have hz (F:A.ker) : (F.val :jK)∈ays b x v := by
    apply contact_of_origin_zero
    intro n
    by_cases hn:n<b.shape.U + 1
    · have h:=congrFun (LinearMap.mem_ker.mp F.property) ⟨n,hn⟩
      exact congrArg (fun z :originRange b=>z.val) h
    · have hd: (AV (F.val :jK)).natDegree≤b.shape.U:= by
        simpa only [AV,natDegree_optionEquivLeft,gY] using
          (hcap F.val F.val.property).2.2.2
      have h₀:Bg n F.val=0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))
      have h₁:aob n F.val=0:= by
        change Ky.symm (Bg n F.val)=0
        rw [h₀,map_zero]
      simp [h₁]
  have hle :A.ker.map V.subtype≤V ⊓ ays b x v := by
    rintro _ ⟨F,hF,rfl⟩
    exact Submodule.mem_inf.mpr ⟨F.property,hz ⟨F,hF⟩⟩
  have hk :=zFM hle
  rw [Submodule.finrank_map_subtype_eq] at hk
  change zsE ao A.ker≤zsE ao (V ⊓ ays b x v :zpI ao jK) at hk
  have hr :=Submodule.finrank_le A.range
  rw [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hr
  have hnull:=LinearMap.finrank_range_add_finrank_ker (K:=ao)
    (V := ↥V) (V₂:=Fin (b.shape.U + 1)→ originRange b) A
  have hc:TT V (ays b x v)≤zsE ao A.range := by
    unfold TT
    omega
  exact hc.trans (by simpa only [Nat.cast_id] using hr)
theorem codim_le_origin (b:TopRow) (x v :ao) (h W:ℕ) :
  TT (Aw h b W) (ays b x v) ≤
   (b.shape.U + 1)*zsE ao (originRange b) :=
 have :=finite_ambient h b W
 codim_le_origin_gen b x v _ fun F hF =>
  let a :=mem_ambient.mp hF; ⟨a.1,a.2.1,a.2.2.1,a.2.2.2.1⟩
end
end qSxbgdc
end
section
set_option autoImplicit true
namespace qm7o3Fa
noncomputable section
open aR (ao)
open Rj (Flat Exp lK adf acw J6 La oH)
open P5_7_2 (TopRow)
open qSxbgdc
open MvPolynomial
open scoped BigOperators
open private bhx bhy y NH dcj gmr gms blU a8I a6A aid cwS aQH bv2 cva caB eLE from ProximityPrize.SubmissionLower.S
variable (b:TopRow)
def cbQ (q:ℕ) (g:ℤ) :Set adf :=
  {e | e.weight (fun _=>1)=iO b q ∧
    -g≤(e.weight Fin.val :ℤ)∧e.weight Fin.val≤b.shape.J∧e 2≤b.YM}
def aqz (q:ℕ) (g:ℤ) :zpI ao lK :=
 restrictSupport ao (cbQ b q g)
def aPi (q:ℕ) (g:ℤ) :aqz b q g →ₗ[ao] lK :=
  ((weightedTruncation a6A (Ic b q g).toNat).comp
    (bind₁ acw).toLinearMap).domRestrict (aqz b q g)
instance gRv (q:ℕ) (g:ℤ) :zAa ao (aqz b q g) := by
 apply restrictSupport_finite
 refine (Finsupp.finite_of_nat_weight_le (fun _:Fin 3=>1)
  (by simp) (iO b q)).subset ?_
 intro e he
 exact (show e.weight (fun _=>1)=iO b q from he.1).le
private def jO (q:ℕ) :ℕ:=q - iO b q
private def Ra (q:ℕ) (e :Exp) :adf :=
 Finsupp.equivFunOnFinite.symm ![e (some 0) - jO b q,e (some 1),e (some 2)]
private theorem buZ {q k :ℕ} (e :TO b q k) :
  jO b q≤e.val (some 0) := by
 have hd:=e.property.2.1
 have hj:=e.property.1.2.1
 rw [bhx] at hd
 rw [bhy] at hj
 simp only [jO,iO]
 omega
private theorem cqD {q k :ℕ} (e :TO b q k) :
  Ra b q e∈cbQ b q (offset b k) := by
 have hd:=e.property.2.1
 have hj:=e.property.1.2.1
 have ht:=e.property.1.2.2
 have hg:=e.property.2.2
 have ha :=buZ b e
 rw [bhx] at hd
 rw [bhy] at hj hg
 simp [cbQ,Finsupp.weight_eq_sum,Fin.sum_univ_three,Ra,smul_eq_mul,Nat.mul_comm]
 simp only [jO,iO] at *
 omega
private def bpl (q k :ℕ) (e :TO b q k) :
   aqz b q (offset b k) :=
 ⟨monomial (Ra b q e) 1,
   (monomial_mem_restrictSupport ao).mpr (Or.inl (cqD b e))⟩
private def encode (q k :ℕ) :Block b q k →ₗ[ao] aqz b q (offset b k) :=
 (basisRestrictSupport ao (TO b q k)).constr ao (bpl b q k)
private theorem b1y (q k :ℕ) (e :TO b q k) :
  ((encode b q k (basisRestrictSupport ao (TO b q k) e)) :lK) =
    monomial (Ra b q e) 1 :=
 congrArg Subtype.val
  ((basisRestrictSupport ao (TO b q k)).constr_basis ao (bpl b q k) e)
local notation "T" => (MvPolynomial.X (none :Option (Fin 3)) :Flat)
private theorem cqE (q:ℕ) (e :Exp) :
    bind₁ NH (bind₁ acw (monomial (Ra b q e) 1)) =
      La (some 0)^(e (some 0) - jO b q) *
        (T*y 1)^e (some 1)*(T^2*y 2)^e (some 2) := by
  rw [bind₁_bind₁,blU,Fin.prod_univ_three]
  simp [dcj,gmr,gms,Ra,mul_assoc]
private theorem cpw (q k :ℕ) (e :TO b q k) :
    T^(-offset b k).toNat*J6 (monomial e.val 1) =
      T^(offset b k).toNat*La (some 0)^jO b q *
        bind₁ NH (bind₁ acw (monomial (Ra b q e) 1)) := by
  have hi:=e.property.2.2
  rw [bhy] at hi
  have ht: (-offset b k).toNat+e.val none =
      (offset b k).toNat+e.val (some 1)+2*e.val (some 2) := by omega
  have ha :jO b q+(e.val (some 0) - jO b q)=e.val (some 0) := by
    have :=buZ b e
    omega
  have hT:T^(-offset b k).toNat*T^e.val none =
      T^(offset b k).toNat*T^e.val (some 1)*T^(2*e.val (some 2)) := by
    simpa only [pow_add] using congrArg (T ^ ·) ht
  have hA:La (some 0)^e.val (some 0) =
      La (some 0)^jO b q*La (some 0)^(e.val (some 0) - jO b q) := by
    rw [← pow_add,ha]
  rw [a8I,cqE]
  simp only [mul_pow,← pow_mul]
  calc
    _=(T^(-offset b k).toNat*T^e.val none) *
        (La (some 0)^e.val (some 0)*y 1^e.val (some 1)*y 2^e.val (some 2)) := by
      ring
    _ = _:= by rw [hT,hA]; ring
private theorem gqH (q k :ℕ) (p:Block b q k) :
    T^(-offset b k).toNat*J6 (p:Flat) =
      T^(offset b k).toNat*La (some 0)^jO b q *
        bind₁ NH (bind₁ acw (encode b q k p:lK)) := by
  let l:=(zzN ao (T^(-offset b k).toNat)).comp
    (J6.toLinearMap.comp (Block b q k).subtype)
  let r :=(zzN ao (T^(offset b k).toNat*La (some 0)^jO b q)).comp
    ((bind₁ NH).toLinearMap.comp ((bind₁ acw).toLinearMap.comp
      ((aqz b q (offset b k)).subtype.comp (encode b q k))))
  have h:l=r := by
    apply (basisRestrictSupport ao (TO b q k)).ext
    intro e
    change T^(-offset b k).toNat *
      J6 (↑(basisRestrictSupport ao (TO b q k) e) :Flat) =
        T^(offset b k).toNat*La (some 0)^jO b q *
          bind₁ NH (bind₁ acw
            (↑(encode b q k (basisRestrictSupport ao (TO b q k) e)) :lK))
    rw [b1y,coe_basisRestrictSupport_apply]
    exact cpw b q k e
  exact LinearMap.congr_fun h p
private theorem brp (q k :ℕ) :
   z83 ((aPi b q (offset b k)).comp (encode b q k)) ≤
     z83 (af3 b q k) := by
 intro p hp
 let L:aqz b q (offset b k) :=encode b q k p
 let S:lK:=bind₁ acw (L:lK)
 let cut:=(Ic b q (offset b k)).toNat
 have hz :weightedTruncation a6A cut S=0:=LinearMap.mem_ker.mp hp
 have hcontact :=(weightedTruncation_eq_zero_iff _ _ _).mp hz
 have hgrade : (L:lK).IsWeightedHomogeneous (fun _:Fin 3=>1) (iO b q) :=
   fun e he=>(L.property (mem_support_iff.mpr he)).1
 have hS:S.IsWeightedHomogeneous (fun _:Fin 3=>1) (iO b q) :=
   hgrade.bind₁ eLE
 have hscaled:S∈restrictWeightedOrder aid (cut+iO b q) := by
   intro e he
   have hg:=hS (mem_support_iff.mp he)
   have hc:=mem_restrictWeightedOrder.mp hcontact e he
   change cut+iO b q≤e.weight aid
   rw [cwS,hg]
   exact Nat.add_le_add_right hc _
 have hprod:=mul_mem_restrictWeightedOrder
   (mul_mem_restrictWeightedOrder (aQH (offset b k).toNat)
     (by simpa using pow_mem_restrictWeightedOrder cva (jO b q)))
   (bind₁_mem_restrictWeightedOrder bv2 hscaled)
 have hbound:b.shape.m+(-offset b k).toNat ≤
     (offset b k).toNat+jO b q+(cut+iO b q) := by
   have hd:iO b q≤q:=min_le_left ..
   dsimp [cut,Ic,jO]
   omega
 have hshift:T^(-offset b k).toNat*J6 (p:Flat) ∈
     restrictWeightedOrder oH (b.shape.m+(-offset b k).toNat) := by
   rw [gqH]
   exact restrictWeightedOrder_anti _ hbound hprod
 apply LinearMap.mem_ker.mpr
 exact (weightedTruncation_eq_zero_iff _ _ _).mpr (caB hshift)
theorem fTp (q k :ℕ) :
   zsE ao (zWl (af3 b q k)) ≤
     zsE ao (zWl (aPi b q (offset b k))) := by
 let f :=(aPi b q (offset b k)).comp (encode b q k)
 have hker :=zFM (brp b q k)
 change zsE ao (z83 f) ≤
   zsE ao (z83 (af3 b q k)) at hker
 have h₁:=f.finrank_range_add_finrank_ker
 have h₂:=(af3 b q k).finrank_range_add_finrank_ker
 exact (show zsE ao (zWl (af3 b q k)) ≤
     zsE ao (zWl f) by omega).trans
   (zFM (LinearMap.range_comp_le_range _ _))
end
end qm7o3Fa
end
section
set_option autoImplicit true
namespace qPQ4nYa
noncomputable section
open aR (ao)
open jA
open NR (TT)
open qlc9qed (Bank ays bsz)
theorem codim_le_origin (b:Bank) (x v :ao) (V:zpI ao jK)
  [zAa ao V] (hcap : ∀ F∈V,Jn b.box F∧gY F≤b.U) :
  TT V (ays b.m x v)≤(b.U + 1)*zsE ao (originRange b) := by
 have h:ays b.m x v=q7IA62d.ays (top b) x v := by
  ext F
  rw [bsz,q7IA62d.bsz]
  exact Iff.rfl
 rw [h]
 exact qSxbgdc.codim_le_origin_gen (top b) x v V fun F hF =>
  let a :=hcap F hF; ⟨a.1.1,a.1.2.1,a.1.2.2.1,a.2⟩
end
end qPQ4nYa
end
end
