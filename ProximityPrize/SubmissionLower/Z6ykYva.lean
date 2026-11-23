import ProximityPrize.SubmissionLower.Z1G66Gc
import ProximityPrize.SubmissionLower.ZJ86yqc
set_option Elab.async false
set_option autoImplicit true
namespace qUJtx6c
noncomputable section
open Polynomial Finset
open P5 (K blockLength)
open P5_7 (farAgreement)
open P5_7_5 (wX)
open TD (aBh)
open baX (mix b9f)
open aR (af extend embed)
open oR (qg)
open gT (tK FW)
open pI (abM)
open bz3 (cFG bFR)
open aF0 (BJ YM)
open private degree_guards from ProximityPrize.SubmissionLower.ZEXP3Xa
open scoped BigOperators
private theorem cSy {T:Finset K} {s :K→K[X]} {B J:ℕ}
    (hdistinct :Set.InjOn s (T:Set K)) (guard :aBh B J)
    (G:tK) (hG:abM G B J) (hroot : ∀ γ∈T,FW G (s γ)=0)
    (a v :ℚ) (hv :0≤v) (hva :v≤a)
    (count : ∀ U⊆T,∀ f :af 2,Irreducible f→0<f.degreeOf 1 →
      f.totalDegree≤B→f.degreeOf 1≤J →
      (∀ γ∈U,qg 1 f (extend (s γ))) →
      (U.card:ℚ)≤ mix f.totalDegree (f.degreeOf 1) a v+1) :
    (T.card:ℚ)≤ mix B J a v+(B^2 :ℕ) := by
  classical
  obtain ⟨q,hq,hb,hj,hsolve⟩:=cFG G hG.1 hG.2.1 hG.2.2
  obtain ⟨A,R,hA,hAb,hAj,hR,hRd,hcover⟩ :=
    bFR q hq guard.bmin guard.small hb hj
  let iy :=T.filter fun γ=>R.eval (extend (s γ))=0
  let reg (g:af 2) :=T.filter fun γ=>qg 1 g (extend (s γ))
  have hord:iy.card≤B*(B - 1) := by
    let image (γ:K) :=extend (s γ)
    have hinj:Set.InjOn image (iy :Set K) := fun _ ha _ hb he =>
      hdistinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hcard: (iy.image image).card≤R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans hRd
  have htotal:T.card≤ iy.card + ∑ g∈A,(reg g).card:= by
    have hsub:T⊆iy∪A.biUnion reg:= by
      intro γ hγ
      rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨g,ha,hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ,hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g,ha,Finset.mem_filter.mpr ⟨hγ,hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hnum :A.card≤B:= by
    calc
      A.card = ∑ _∈A,1 := by simp
      _ ≤ ∑ g∈A,g.totalDegree :=Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _≤B:=hAb
  have hlocal (f :af 2) (hf :f∈A) :
      ((reg f).card:ℚ)≤ mix f.totalDegree (f.degreeOf 1) a v+1 :=
    count (reg f) (Finset.filter_subset _ _) f (hA f hf).1 (hA f hf).2
      ((Finset.single_le_sum (fun g _=>Nat.zero_le g.totalDegree) hf).trans hAb)
      ((Finset.single_le_sum (fun g _=>Nat.zero_le (g.degreeOf 1)) hf).trans hAj)
      (fun γ hγ=>(Finset.mem_filter.mp hγ).2)
  have hreg: (∑ g∈A,((reg g).card:ℚ))≤ mix B J a v+B:= by
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [b9f (MvPolynomial.degreeOf_le_totalDegree _ _),b9f guard.jb,
      Finset.sum_add_distrib,← Finset.sum_mul,Finset.sum_const,nsmul_eq_mul,mul_one]
    have hbt: (∑ g∈A,(g.totalDegree :ℚ))≤B:= by exact_mod_cast hAb
    have hjt: (∑ g∈A,(g.degreeOf 1 :ℚ))≤J:= by exact_mod_cast hAj
    have hnr : (A.card:ℚ)≤B:= by exact_mod_cast hnum
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbt hv)
      (mul_le_mul_of_nonneg_right hjt (sub_nonneg.mpr hva))) hnr
  have hbox :B*(B-1)+B=B^2 := by
    calc
      _=B*((B-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ = _:= by rw [Nat.sub_add_cancel ((by decide :1≤2).trans guard.bmin),pow_two]
  have hs : (T.card:ℚ)≤ iy.card + ∑ g∈A,((reg g).card:ℚ) := by exact_mod_cast htotal
  have ho: (iy.card:ℚ)≤(B*(B-1) :ℕ) := by exact_mod_cast hord
  have hboxQ: (↑(B*(B-1) :ℕ) :ℚ)+B=(B^2 :ℕ) := by exact_mod_cast hbox
  linarith only [hs,ho,hreg,hboxQ]
theorem proof :P5_7_5.c2 := by
  classical
  intro b u del M Γ F hband B J guard G hG T hT hroot
  let d:=wX b.row.hi
  have hd:d<farAgreement:=(degree_guards b).2.1
  have hd₀:2≤d:=(by decide :2≤131071).trans (Nat.le_add_right _ _)
  have hdeg (γ) (hγ:γ∈T) : (F.scalar γ).natDegree≤d:= by
    rcases (F.mark γ (hT hγ)).aic with hz | hh
    · simp [hz]
    · change ((F.scalar γ).natDegree :ℤ)≤131071+M.iF at hh
      change (F.scalar γ).natDegree≤131071+b.row.hi
      have hhi:=hband.2
      omega
  let q:=farAgreement - d
  let a :=BJ d B
  let v :=YM d B J
  let β:ℚ:=((blockLength - farAgreement:ℕ) :ℚ)/q
  let m:=(B-J)*v+J*a
  have hβ:0≤β:= by dsimp only [β]; positivity
  have hv :v≤a :=min_le_left _ _
  have h:=cSy (F.distinct.mono hT) guard G hG hroot (β*a) (β*v) (by positivity)
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hv) hβ) (fun U hU f hf hp hB hJ hreg=> by
      have hc:=ePE (F.distinct.mono (hU.trans hT))
        (fun γ hγ=>hdeg γ (hU hγ)) (fun γ hγ =>
          let mark :=F.mark γ (hT (hU hγ))
          ⟨mark.bad.support,mark.bad.dw,mark.scalar_hits⟩)
        hd₀ hd guard.jpos f hf hp hB hJ hreg
      refine hc.trans_eq ?_
      change β *mix f.totalDegree (f.degreeOf 1) a v+1= _
      unfold mix
      ring)
  have he :mix B J (β*a) (β*v)=β*m:= by unfold mix m; push_cast; ring
  rw [he] at h
  let num :=(blockLength - farAgreement)*m
  let gX:=(num+(q-1))/q
  have hq:0<q:=Nat.sub_pos_of_lt hd
  have hqR: (0:ℚ)<(q:ℚ) := by exact_mod_cast hq
  have hr :=Nat.mod_add_div (num+(q-1)) q
  have hlt:=Nat.mod_lt (num+(q-1)) hq
  have hn:num≤q*gX:= by dsimp only [gX]; omega
  have hpay :β*m≤(gX:ℚ) := by
    dsimp only [β]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hqR).mpr
    rw [mul_comm (gX:ℚ)]
    exact_mod_cast hn
  change T.card≤gX+B^2
  have : (T.card:ℚ)≤(gX:ℚ)+(B^2 :ℕ) :=h.trans (add_le_add hpay le_rfl)
  exact_mod_cast this
end
end qUJtx6c
