import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.ZQGI7be
import ProximityPrize.SubmissionLower.ZwO1rQb
set_option Elab.async false
set_option autoImplicit true
namespace q6nKpZc
noncomputable section
open Polynomial Finset
open P6 (K jG)
open P5_7_2 (A Window row rankBlend)
open q7F2qKe (wX weakAgreement au1 Individual rankPrice freeCap globalCap)
open qVm3Zhc (Word equation_bound jetRate Ut lambda blendTerm)
open TD (FP bCb)
open baX (mix)
open gT (Ambient)
open pI (xN dual pN)
open aF0 (BJ YM)
open private OF.mk OF.distinct from ProximityPrize.SubmissionLower.ZogIzOe
open private bLI dmf errors ePE eK0 arV c3W aPh from ProximityPrize.SubmissionLower.ZdSQxye
open private cSy from ProximityPrize.SubmissionLower.Z6ykYva
open private c3F from ProximityPrize.SubmissionLower.U
open private blend_range from ProximityPrize.SubmissionLower.ZwO1rQb
open scoped BigOperators Classical
private theorem bd0 {b u del} {M:jG u del} {Γ}
    (F:P1.bje A M Γ) (hband:Window b M.iF) {T:Finset K} (hT:T⊆Γ) :
    Word M.word T F.scalar (wX b) := by
  refine OF.mk (F.distinct.mono hT) ?_ ?_
  · intro γ hγ
    have hw:=hband.2
    have hh:=(bLI b).1
    have hh' : M.iF.toNat≤(row b).declaredHi:= by omega
    exact (P6_7.aic F (hT hγ)).trans (Nat.add_le_add_left hh' _)
  · intro γ hγ
    let mark :=F.mark γ (hT hγ)
    exact ⟨mark.bad.support,mark.bad.dw,mark.scalar_hits⟩
theorem fixed_tariff {b u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    (hband:Window b M.iF) :FixedTariff F b:= by
  classical
  intro B J guard G hG T hT hroot
  let d:=wX b
  have hdl:131071≤d:=Nat.le_add_right _ _
  have hdu:d≤133774 :=Nat.add_le_add_left (bLI b).2 131071
  have hd:d<weakAgreement:=hdu.trans_lt (by decide)
  have hw:=bd0 F hband hT
  let q:=weakAgreement - d
  let a :=BJ d B
  let v :=YM d B J
  let β:ℚ:=(errors :ℚ)/q
  let m:=(B-J)*v+J*a
  have hv :v≤a :=min_le_left _ _
  have hβ:0≤β:= by dsimp only [β]; positivity
  have hq:0<q:=Nat.sub_pos_of_lt hd
  have hqR: (0:ℚ)<(q:ℚ) := by exact_mod_cast hq
  unfold au1
  apply le_min
  · have h:=cSy (OF.distinct hw) guard G hG hroot (β*a) (β*v) (by positivity)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hv) hβ) (fun U hU f hf hp hB hJ hreg=> by
        have hc:=ePE (dmf hw hU) (by omega) hd guard.jpos f hf hp hB hJ hreg
        refine hc.trans_eq ?_
        change β *mix f.totalDegree (f.degreeOf 1) a v+1= _
        unfold mix
        ring)
    have he :mix B J (β*a) (β*v)=β *m:= by unfold mix m; push_cast; ring
    rw [he] at h
    let num :=errors*m
    let gX:=(num+(q-1))/q
    have hr :=Nat.mod_add_div (num+(q-1)) q
    have hlt:=Nat.mod_lt (num+(q-1)) hq
    have hn:num≤q*gX:= by dsimp only [gX]; omega
    have hpay :β *m≤(gX:ℚ) := by
      dsimp only [β]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hqR).mpr
      rw [mul_comm (gX:ℚ)]
      exact_mod_cast hn
    change T.card≤gX+B^2
    have hfinal: (T.card:ℚ)≤(gX:ℚ)+(B^2 :ℕ) :=
      h.trans (add_le_add hpay le_rfl)
    exact_mod_cast hfinal
  · let ap:=arV d B
    let vp:=aPh d B J
    have ha :0≤ap:=c3W d B
    have hvp:0≤vp:=le_min ha (by positivity)
    have h:=cSy (OF.distinct hw) guard G hG hroot ap vp hvp (min_le_left _ _)
      (fun U hU=>eK0 (dmf hw hU) hdl hdu guard.jpos)
    let r :=mix B J ap vp
    have hceil:r≤(r.ceil.toNat :ℕ) := by
      have hz :r.ceil≤(r.ceil.toNat :ℤ) :=Int.self_le_toNat _
      have hcast: (r.ceil:ℚ)≤(r.ceil.toNat :ℚ) := by exact_mod_cast hz
      exact Rat.le_ceil.trans hcast
    change T.card≤ r.ceil.toNat+B^2
    have hfinal: (T.card:ℚ)≤(r.ceil.toNat :ℚ)+(B^2 :ℕ) :=
      h.trans (add_le_add hceil le_rfl)
    exact_mod_cast hfinal
theorem rank_tariff {b u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    (hband:Window b M.iF) {o:ℕ} (I:Ideal Ambient) (hI:xN I)
    (hn : ¬ dual I) (hind:Individual b o 0 fun k=>pN I k) :
    ((Γ.filter (I0 F I)).card:ℚ)≤FP (rankPrice b o) fun k=>pN I k := by
  classical
  obtain ⟨G,hG,hGI⟩:=c3F bzS.proof cy5.proof hI hn
  let T:=Γ.filter (I0 F I)
  have hw:=bd0 F hband (show T⊆Γ from filter_subset _ _)
  let r :=bCb (freeCap b o 0) (globalCap b 0)
  have hB: (pN I 2 :ℚ)≤ r 2 := by
    simpa only [r,bCb,min_comm (freeCap b o 0 2)] using (hind.2.1 2).2
  have hJ: (pN I 1 :ℚ)≤ r 1 := by
    simpa only [r,bCb,min_comm (freeCap b o 0 1)] using (hind.2.1 1).2
  have hc:=equation_bound hw (Nat.le_add_right _ _) (Nat.add_le_add_left (bLI b).2 _)
    G hG hI.mixed_lt (fun γ hγ=> by
      simpa only [pI.d2l] using RingHom.mem_ker.mp ((mem_filter.mp hγ).2 hGI))
    hB hJ (blend_range b)
  refine hc.trans ?_
  let L:=jetRate (wX b)
  let μ:=Ut (wX b)
  cases h:rankBlend b with
  | none =>
    simp [h,qVm3Zhc.coeff,rankPrice,FP,Fin.sum_univ_succ]
    change (2*L*r 2+μ)*pN I 1+(2*L*r 1+r 2)*pN I 2 ≤
      (2*lambda*wX b*r 2+μ)*pN I 1+(2*lambda*wX b*r 1+r 2)*pN I 2
    rw [mul_assoc (2 :ℚ) lambda]
  | some v =>
    simp only [h,qVm3Zhc.coeff,rankPrice,FP,Fin.sum_univ_succ,Fin.sum_univ_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,zero_mul,add_zero,zero_add]
    let a :=L*blendTerm (r 2) (r 1)*(1-v)+r 2
    change (4*L*r 2*v+μ)*pN I 1+a*pN I 2 ≤
      (4*lambda*wX b*r 2*v+μ)*pN I 1+(a+1)*pN I 2
    rw [mul_assoc (4 :ℚ) lambda]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (Nat.cast_nonneg _))
end
end q6nKpZc
