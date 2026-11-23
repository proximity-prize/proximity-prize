import ProximityPrize.SubmissionLower.Zmk5EEe
import ProximityPrize.SubmissionLower.ZFh47Da
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qK3TPae
noncomputable section
open Finset Polynomial
open P5 (K p)
open P5_7 (midAgreement)
open P5_7_1 (Input Poles degree hi)

open q7YMR4d (ke oF)

open Cu (sQ)
open E7 (CurvePlace poleOrder KB)



open private cut_upper cut_lower degree_pos from ProximityPrize.SubmissionLower.ZTV7u3a
open scoped Classical BigOperators
theorem marks {x :Input} (P:Poles x) {T:Finset K} (hT:T⊆x.Γ) :
    qkgz7gb.UJ degree x.M.word T x.M.label x.F.scalar := by
  refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,?_,?_,?_⟩
  · intro γ hγ
    rcases (x.F.mark γ (hT hγ)).aic with hz | hd
    · simp [hz]
    · have h:=x.kA.2
      change x.M.iF≤(2532 :ℤ) at h
      change ((x.F.scalar γ).natDegree :ℤ)≤131071 + x.M.iF at hd
      have hm: ((x.F.scalar γ).natDegree :ℤ)≤(degree :ℤ) :=
        hd.trans (add_le_add_right h (131071 :ℤ))
      exact_mod_cast hm
  · intro γ hγ
    let m:=x.F.mark γ (hT hγ)
    exact ⟨m.bad.support,(by decide :midAgreement≤P5.dw).trans m.bad.dw,
      m.scalar_hits⟩
  · refine ⟨x.h,?_,P.D,fun γ hγ=>P.marks γ (hT hγ)⟩
    have h:=x.kA.1
    change (2326:ℤ)≤x.M.iF at h
    change 0<x.M.iF.toNat
    omega
theorem high_count {T:Finset K} (C:AmplifiedCut T) :
   p^C.order*T.card≤C.ng.sum (fun _ n=>n) := by
 let zord (v :CurvePlace cu.L C.E) :=KB v.value C.Lw
 let pord (v :CurvePlace cu.L C.E) :=poleOrder v.value C.Lw
 have divs :=aFU.of_children bRt.proof
   bRu.proof _ _ C.curve C.Lw
 let U:Finset (CurvePlace cu.L C.E) :=univ.map C.Ia
 let A:=C.ng.support∪U
 let V:=A∪divs.1.toFinset∪divs.2.1.toFinset
 have hUV:U⊆V:=(subset_union_right:U⊆A).trans
   ((subset_union_left:A⊆A∪divs.1.toFinset).trans subset_union_left)
 have hAV:C.ng.support⊆V:=(subset_union_left:C.ng.support⊆A).trans
   ((subset_union_left:A⊆A∪divs.1.toFinset).trans subset_union_left)
 have hP:Function.support pord ⊆ ↑V:= fun v hv =>
   mem_union_left _ (mem_union_right _ (divs.1.mem_toFinset.mpr hv))
 have hZ:Function.support zord ⊆ ↑V:= fun v hv =>
   mem_union_right _ (divs.2.1.mem_toFinset.mpr hv)
 have heq : ∑ v∈V,pord v = ∑ v∈V,zord v := by
   rw [← finsum_eq_sum_of_support_subset pord hP,← finsum_eq_sum_of_support_subset zord hZ]
   exact divs.2.2.1
 have hall : ∑ v∈V,C.ng v=C.ng.sum (fun _ n=>n) := by
   exact (sum_subset hAV (fun _ _ hv=>Finsupp.notMem_support_iff.mp hv)).symm
 let w (v :CurvePlace cu.L C.E) :=C.ng v - pord v+zord v
 have hsum: (∑ v∈V,w v)+(∑ v∈V,pord v)=(∑ v∈V,C.ng v) + ∑ v∈V,zord v := by
   rw [← sum_add_distrib,← sum_add_distrib]
   apply sum_congr rfl
   intro v _
   have hp:=C.poles v
   dsimp only [w,pord,zord] at *
   omega
 have hcount:p^C.order*T.card ≤ ∑ v∈V,w v := calc
   _ = ∑ v∈U,p^C.order := by simp [U,Nat.mul_comm]
   _ ≤ ∑ v∈U,w v := by
     apply sum_le_sum
     intro v hv
     obtain ⟨t,_,rfl⟩:=mem_map.mp hv
     have h:=C.vanishing t
     dsimp only [w,pord,zord]
     omega
   _≤_:=sum_le_sum_of_subset hUV
 rw [heq,hall] at hsum
 omega
theorem polar_count (hlocal:q7YMR4d.c3) {Q:sQ} (hQ:Irreducible Q)
   {T:Finset K} {z :K→K} (hz :Set.InjOn z (T:Set K))
   (hseed : ∀ γ∈T,Q.eval (DP.Z7 (z γ))=0) :
   3*(T \ regular Q z T).card≤Q.totalDegree*(Q.totalDegree-1) := by
 obtain ⟨i,hi⟩:=q7YMR4d.polar_exists Q hQ
 let g:=MvPolynomial.pderiv i Q
 have hd:g.totalDegree≤Q.totalDegree-1 := by
   simpa only [MvPolynomial.weightedTotalDegree_one,Pi.one_apply] using
     MvPolynomial.weightedTotalDegree_pderiv_le_sub (1 :Fin 2→ℕ) i Q
 obtain ⟨hf,hu⟩:=cut_upper hQ hi (hd.trans_lt (by have :=degree_pos hQ; omega))
 let:=hf
 let a :=DP.Z7 ∘ z
 have ha :Set.InjOn a ((T \ regular Q z T:Finset K) :Set K) :=
   fun γ hγ δ hδ h=>hz (mem_sdiff.mp hγ).1 (mem_sdiff.mp hδ).1
     ((algebraMap K cu.L).injective (congrFun h 0))
 have hl : ∀ γ∈T \ regular Q z T,3≤Module.finrank cu.L
     (sQ ⧸ (ke Q g ⊔ oF (a γ)^3)) := by
   intro γ hγ
   obtain ⟨hm,hn⟩:=mem_sdiff.mp hγ
   have hn' : ¬ RegularPoint Q (a γ) := fun h=>hn (mem_filter.mpr ⟨hm,h⟩)
   exact hlocal Q _ i (hseed γ hm)
     (fun j=>not_not.mp fun hj=>hn' (Or.inl ⟨hseed γ hm,j,hj⟩))
     (fun h=>hn' (Or.inr h))
 exact (cut_lower ha hl).trans
   (hu.trans ((Nat.mul_le_mul_right _ hd).trans_eq (Nat.mul_comm _ _)))
end
end qK3TPae
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace quN7Z4a
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P5 (K I node p blockLength)
open P5_7 (midAgreement)
open P5_7_3 (fO)
open qAxtVye (HorizontalBand wX gap branchDegree horizontalUnit horizontalBase)
open gT (kM)
open Cu (sQ)
open scoped BigOperators Classical
def c1 :Prop :=
  ∀ (b:fO) (C₀:sQ) [Fact (Irreducible C₀)]
    (J:Ideal kM) (T:Finset K) (z :K→K) (s :K→K[X]) (w:I→K)
    (g d H :ℕ) (S:Sheet C₀ J g H T z s),
    HorizontalBand b→2≤g→ C₀.totalDegree=d→0<d→d*g<p →
    branchDegree b g<p →
    physicalWeight (wX b) S.root.equation<compressionWidth (wX b) g →
    Set.InjOn z (T:Set K)→OF T s w (wX b)→PoleStarts T z s →
    Nonempty (VariationBudget (T.filter fun γ=>Smooth C₀ (Z7 (z γ))) s w b g d H)
def c2 :Prop :=
  ∀ (b:fO) (C₀:sQ) [Fact (Irreducible C₀)]
    (J:Ideal kM) (T:Finset K) (z :K→K) (s :K→K[X]) (w:I→K)
    (g d H :ℕ) (S:Sheet C₀ J g H T z s),
    HorizontalBand b→2≤g→ C₀.totalDegree=d→0<d→d*g<p →
    compressionWidth (wX b) g≤physicalWeight (wX b) S.root.equation →
    Set.InjOn z (T:Set K)→OF T s w (wX b) →
    (T.card:ℚ)≤(2*(d:ℚ)/3+1)*(d*g:ℚ)+(3*(g:ℚ)+1)*H+g
def c3:Prop :=
  ∀ (b:fO) (C₀:sQ) [Fact (Irreducible C₀)]
    (J:Ideal kM) (T:Finset K) (z :K→K) (s :K→K[X]) (w:I→K)
    (d H :ℕ) (S:Sheet C₀ J 2 H T z s),
    HorizontalBand b→ C₀.totalDegree=d→0<d→d*2<p →
    branchDegree b 2<p →
    physicalWeight (wX b) S.root.equation<compressionWidth (wX b) 2 →
    Set.InjOn z (T:Set K)→OF T s w (wX b) →
    (T.card:ℚ)≤quadraticUnit b*H+2
private theorem variation_count {b U s w g d H} {T:Finset K}
    (W:OF T s w (wX b)) (hb:HorizontalBand b) (hU:U⊆T)
    (P:VariationBudget U s w b g d H) :
    (U.card:ℚ)≤ standardUnit b g*H+(4*g*g*d:ℕ) := by
  classical
  let miss (γ:K) :=univ.filter fun i=>(s γ).eval (node i)=w i∧i∉P.zeroNodes γ
  have hit_count (γ:K) (hγ:γ∈P.good) :
      gap b≤(miss γ).card+P.finitePoles γ:= by
    obtain ⟨B,hB,hw⟩:=W.lg γ (hU (P.subset hγ))
    have h:=card_le_card (s :=B) (t:=miss γ∪P.zeroNodes γ) (by
      intro i hi
      by_cases hz :i∈P.zeroNodes γ
      · exact mem_union_right _ hz
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hw i hi,hz⟩))
    have hsum:=card_union_le (miss γ) (P.zeroNodes γ)
    have hzero :=P.Ju γ hγ
    change midAgreement - wX b≤_
    omega
  have hsum:gap b*P.good.card≤(2*g*blockLength+2*g*(2*branchDegree b g-1))*H := by
    calc
      _ = ∑ γ∈P.good,gap b:= by rw [sum_const,smul_eq_mul,Nat.mul_comm]
      _ ≤ ∑ γ∈P.good,((miss γ).card+P.finitePoles γ) :=sum_le_sum hit_count
      _≤(blockLength*(2*g*H))+2*g*(2*branchDegree b g-1)*H := by
        rw [sum_add_distrib]
        apply Nat.add_le_add _ P.poles
        have hh : ∑ γ∈P.good,(miss γ).card =
            ∑ i:I,(P.good.filter (fun γ=>(s γ).eval (node i)=w i∧i∉P.zeroNodes γ)).card:= by
          simp only [miss,card_filter]
          rw [sum_comm]
        rw [hh]
        calc
          _ ≤ ∑ _i:I,2*g*H :=sum_le_sum (fun i _=>P.lg i)
          _ = _:= by rw [sum_const,smul_eq_mul,card_univ,IRSProfile.card_index]
      _ = _:= by ring
  have hq: (0:ℚ)<gap b:= by
    exact_mod_cast (Nat.sub_pos_of_lt (degree_lt hb) :0<gap b)
  let a :ℕ:=2*g*blockLength+2*g*(2*branchDegree b g-1)
  have hhN :P.good.card*gap b≤a*H := by
    rw [Nat.mul_comm P.good.card (gap b)]
    exact hsum
  have hh: (P.good.card:ℚ)*(gap b:ℚ)≤a*H := by exact_mod_cast hhN
  have hgood:=(le_div_iff₀ hq).mpr hh
  rw [mul_div_right_comm] at hgood
  have hc:U.card≤P.good.card+((8+6*g)*H+4*g*g*d) := by
    have h:=card_sdiff_add_card_eq_card P.subset
    have h' := P.exceptional
    omega
  have hc' : (U.card:ℚ)≤P.good.card+((8+6*(g:ℚ))*H+(4*g*g*d:ℚ)) := by
    exact_mod_cast hc
  have hr : ((a :ℚ)/gap b)*H+((8+6*(g:ℚ))*H+4*g*g*d) =
      standardUnit b g*H+4*g*g*d:= by dsimp [a,standardUnit]; ring
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat]
  exact (hc'.trans (add_le_add hgood le_rfl)).trans_eq hr
private theorem degree_payment {d g:ℕ} (hg:2≤g) :
  (4*g*g*d:ℚ)+(d:ℚ)*(d-1 :ℕ)≤horizontalBase d g*(d*g:ℚ) := by
 have hgQ: (2 :ℚ)≤g:= by exact_mod_cast hg
 have hd: (0:ℚ)≤d:=Nat.cast_nonneg _
 have hds : ((d-1 :ℕ) :ℚ)≤d:= by exact_mod_cast Nat.sub_le d 1
 have hs :=mul_le_mul_of_nonneg_left hds hd
 have hlarge :=mul_le_mul_of_nonneg_left hgQ (show (0:ℚ)≤d*d/3 by positivity)
 have hsmall: (0:ℚ)≤(d:ℚ)*g:= by positivity
 unfold horizontalBase
 nlinarith only [hs,hlarge,hsmall,mul_nonneg hd hd]
private theorem high_payment {d g H :ℕ} {kA:fO}
    {value :ℚ} (h:value≤(2*(d:ℚ)/3+1)*(d*g:ℚ)+(3*(g:ℚ)+1)*H+g) :
    value≤horizontalBase d g*(d*g:ℚ)+horizontalUnit kA g*H+g:= by
  have hgQ: (0:ℚ)≤g:=Nat.cast_nonneg _
  have hbase :2*(d:ℚ)/3+1≤horizontalBase d g:= by
    unfold horizontalBase
    linarith
  have hstd:3*(g:ℚ)+1≤ standardUnit kA g:= by
    unfold standardUnit
    have hnon : (0:ℚ) ≤
        ((2*g*blockLength+2*g*(2*branchDegree kA g-1) :ℕ) :ℚ)/gap kA:= by positivity
    linarith
  have hunit :3*(g:ℚ)+1≤horizontalUnit kA g:= by
    change 3*(g:ℚ)+1≤ if g=2 then min (standardUnit kA g) (quadraticUnit kA) else standardUnit kA g
    split_ifs with he
    · refine le_min hstd ?_
      subst g
      unfold quadraticUnit
      have hnon : (0:ℚ)≤8*(blockLength:ℚ)/gap kA:= by positivity
      linarith
    · exact hstd
  exact h.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbase (by positivity))
    (mul_le_mul_of_nonneg_right hunit (Nat.cast_nonneg H))) le_rfl)
end
end quN7Z4a
end
