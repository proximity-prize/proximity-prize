import ProximityPrize.SubmissionLower.AW
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZzQsYjc
import ProximityPrize.SubmissionLower.Z3e8uLd
import ProximityPrize.SubmissionLower.Zo0SdJd
set_option Elab.async false
set_option autoImplicit true
namespace qUJtx6c
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P5 (K I node blockLength)
open P5_7 (farAgreement)
open cz7 (a8m)
open baX (mix aCz)
open aR (af extend)
open oR (qg)
open ana (aVQ)
open aF0 (BJ YM)
open private aDW from ProximityPrize.SubmissionLower.ZgdIx1d
open private azg from ProximityPrize.SubmissionLower.B4
private theorem Wq {w:I→K} {T:Finset K} {s :K→K[X]}
    {A d err :ℕ} (hn:262144=A+err) (he :0<err) (hd:d<A)
    (distinct :Set.InjOn s T)
    (degree : ∀ γ∈T,(s γ).natDegree≤d)
    (lg : ∀ γ∈T,∃ B:Finset I,A≤B.card ∧ ∀ i∈B,(s γ).eval (node i)=w i)
    (cap:ℕ)
    (bound : ∀ i,(∃ γ∈T,(s γ).eval (node i)≠w i)→(T.filter fun γ=>(s γ).eval (node i)=w i).card≤ cap) :
    (A-d)*T.card≤err*cap+(A-d) := by
  classical
  by_cases hs :T.card≤1
  · have h:=Nat.mul_le_mul_left (A-d) hs
    omega
  let H (γ:K) :=univ.filter fun i=>(s γ).eval (node i)=w i
  let common :=univ.filter fun i => ∀ γ∈T,(s γ).eval (node i)=w i
  let N :=univ \ common
  have sub (γ) (hγ:γ∈T) :common⊆H γ :=
    fun i hi=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2 γ hγ⟩
  have pair (a) (ha :a∈T) (b) (hb:b∈T) (hab:a≠b) :
      (H a∩H b).card≤d:= by
    let p:=s a - s b
    have hp:p≠0:=sub_ne_zero.mpr fun eq=>hab (distinct ha hb eq)
    refine (gR.kL.agd node IRSProfile.domain.injective p hp _ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (degree a ha) (degree b hb)))
    intro i hi
    change (s a - s b).eval (node i)=0
    rw [eval_sub,(mem_filter.mp (mem_inter.mp hi).1).2,(mem_filter.mp (mem_inter.mp hi).2).2,sub_self]
  obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp (by omega :1<T.card)
  have hc:=(card_le_card (subset_inter (sub a ha) (sub b hb))).trans (pair a ha b hb hab)
  let x :=A - common.card
  have hN :N.card=x+err := by
    rw [card_sdiff_of_subset (subset_univ common),card_univ,IRSProfile.card_index,hn]
    dsimp [x]
    omega
  have trim (γ:K) : ∃ B:Finset I,γ∈T→B⊆H γ \ common∧B.card=x := by
    by_cases hγ:γ∈T
    · obtain ⟨B,hB,hE⟩:=lg γ hγ
      have hBH :B⊆H γ:= fun i hi=>mem_filter.mpr ⟨mem_univ _,hE i hi⟩
      have hsize :x≤(H γ \ common).card:= by
        rw [card_sdiff_of_subset (sub γ hγ)]
        exact Nat.sub_le_sub_right (hB.trans (card_le_card hBH)) _
      obtain ⟨C,hC,hx⟩:=exists_subset_card_eq hsize
      exact ⟨C,fun _=>⟨hC,hx⟩⟩
    · exact ⟨∅,fun h=>(hγ h).elim⟩
  choose B hB using trim
  have into (γ) (hγ:γ∈T) :B γ⊆N :=
    fun i hi=>mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a) (ha :a∈T) (b) (hb:b∈T) (hab:a≠b) :
      (B a∩B b).card≤x-(A-d) := by
    have cover : (B a∩B b)∪common⊆H a∩H b:= by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨sub a ha hi,sub b hb hi⟩
    have disj:Disjoint (B a∩B b) common :=disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into a ha (mem_inter.mp hi).1)).2 hi'
    have hu:=(card_le_card cover).trans (pair a ha b hb hab)
    rw [card_union_of_disjoint disj] at hu
    dsimp [x]
    omega
  have occ (i) (hi:i∈N) : (T.filter fun γ=>i∈B γ).card≤ cap:= by
    have miss : ∃ γ∈T,(s γ).eval (node i)≠w i:= by
      by_contra! hall
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _,hall⟩)
    refine (card_le_card ?_).trans (bound i miss)
    intro γ hγ
    obtain ⟨hγ,hγi⟩:=mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ,(mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hγi)).1).2⟩
  obtain ⟨h₂,h₁⟩:=aDW T N B x (x-(A-d)) cap
    (fun γ hγ=>⟨into γ hγ,(hB γ hγ).2⟩) overlap occ
  rw [hN] at h₁ h₂
  exact azg err _ x (A-d) cap (by omega) (by omega) (by dsimp [x]; omega) he h₂ h₁
theorem ePE {w:I→K} {T:Finset K} {s :K→K[X]} {d B J:ℕ}
    (hdistinct :Set.InjOn s (T:Set K)) (hdeg : ∀ γ∈T,(s γ).natDegree≤d)
    (hhits : ∀ γ∈T,∃ E :Finset I,farAgreement≤E.card ∧
      ∀ i∈E,(s γ).eval (node i)=w i)
    (hd₀:2≤d) (hd:d<farAgreement) (hJ:0<J)
    (f :af 2) (hf :Irreducible f) (hfpos :0<f.degreeOf 1)
    (hb:f.totalDegree≤B) (hj:f.degreeOf 1≤J)
    (hreg : ∀ γ∈T,qg 1 f (extend (s γ))) :
    (T.card:ℚ)≤((blockLength - farAgreement:ℕ) :ℚ)/(farAgreement - d:ℕ) *
      mix f.totalDegree (f.degreeOf 1) (BJ d B) (YM d B J)+1 := by
  classical
  obtain ⟨C⟩:=czH.proof f d B J hd₀ (hd.trans (by decide)) hJ hb hj
  let cap:=MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1)
    (BJ d B) (YM d B J)
  have hcount:=Wq (err :=blockLength - farAgreement) rfl (by decide)
    hd hdistinct hdeg hhits cap (fun i hi =>
      a8m hdistinct f hf hfpos hreg (by simp [BJ])
        (lt_min (by simp [BJ]) (by omega)) i hi (C.cut (node i) (w i))
        (aVQ _ (C.ags _ _) (C.top_bound _ _))
        (fun γ hγ=>C.agrees _ (hdeg γ hγ) (hreg γ hγ) _ _))
  have hgap: (0:ℚ)<((farAgreement-d:ℕ) :ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt hd
  have hc:=(le_div_iff₀ hgap).mpr (by exact_mod_cast (mul_comm _ _).trans_le hcount :
    (T.card:ℚ)*((farAgreement-d:ℕ) :ℚ) ≤
      ((blockLength - farAgreement:ℕ) :ℚ)*cap+((farAgreement-d:ℕ) :ℚ))
  have hv :YM d B J≤BJ d B:=min_le_left _ _
  dsimp only [cap] at hc
  rw [aCz (f.degreeOf_le_totalDegree 1) hv] at hc
  refine hc.trans_eq ?_
  field_simp
end
end qUJtx6c
