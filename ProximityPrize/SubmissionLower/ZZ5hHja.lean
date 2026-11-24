import ProximityPrize.SubmissionLower.Zf6e2ca
import ProximityPrize.SubmissionLower.ZeFzsob
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qY7abfd
noncomputable section
open P6 (K I p dw blockLength)
open P5_7 (midAgreement farAgreement)
open P6_7_3 (Input degree hi)
open qUrGXob (persistentRate gap)
open DQ (Ag)
open axI (c7Q)
open P5_7_7 (UJ hit mem_sites linear_count)
open private OF OF.mk ceY qTOdRca.rho aaM gAN from ProximityPrize.SubmissionLower.Zf6e2ca
open private cK1 cK2 cK3 from ProximityPrize.SubmissionLower.CR
open private hitmiss_pair from ProximityPrize.SubmissionLower.Zz5zkKe
open Finset Polynomial
open scoped Classical
private theorem degree_le (x :Input) {γ:K} (hγ:γ∈x.Γ) :
    (x.F.scalar γ).natDegree≤degree := by
  have hh:x.M.iF≤(hi:ℤ) :=x.kA.2
  have hn:x.h≤hi:= by
    change x.M.iF.toNat≤hi
    omega
  exact (P6_7.aic x.F hγ).trans (Nat.add_le_add_left hn _)
theorem persistent {x T J Q e H} (he :0<e) (heP:e<p)
    (A:DescendedMarks x T J Q e H) : (T.card:ℚ)≤persistentRate e*H+e := by
  obtain ⟨U,hU,hexc,n,⟨bY⟩⟩:=c7Q T x.M.label x.F.scalar J e H he heP
    A.curve (fun _ _ _ _ h=>sub_left_inj.mp h) A.marks
  have hw:OF x.M.word U x.F.scalar degree := by
    refine OF.mk (x.F.distinct.mono (hU.trans A.subset))
      (fun γ hγ=>degree_le x (A.subset (hU hγ))) ?_
    intro γ hγ
    let m:=x.F.mark γ (A.subset (hU hγ))
    exact ⟨m.bad.support,(by decide :midAgreement≤dw).trans m.bad.dw,
      m.scalar_hits⟩
  have hu:=ceY bY hw he (by decide) (by decide)
  have heQ: (1 :ℚ)≤e := by exact_mod_cast he
  have hx : ((T \ U).card:ℚ)≤(Ag e :ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card:ℚ)=((T \ U).card:ℚ)+(U.card:ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _≤(Ag e :ℚ)*H+((2*aaM*degree*(Ag e :ℚ)+qTOdRca.rho degree)*H+1) :=
      add_le_add hx hu
    _≤(Ag e :ℚ)*H+((2*aaM*degree*(Ag e :ℚ)+qTOdRca.rho degree)*H+e) :=
      add_le_add le_rfl (add_le_add le_rfl heQ)
    _=persistentRate e*H+e := by
      rw [gAN he]
      unfold persistentRate qTOdRca.rho
      ring
private theorem count {w:I→K} {T:Finset K} {z :K→K} {s :K→K[X]} {H :ℕ}
    (M:UJ degree w T z s)
    (hsite : ∀ i,(T.filter fun γ=>hit w s γ i).card≤H ∨
      (T.filter fun γ => ¬ hit w s γ i).card≤H) :
    (T.card:ℚ)≤linearRate*H+1 := by
  by_cases hz :H=0
  · have hone :T.card≤1 := by
      by_contra! h
      obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp h
      have hc:=hitmiss_pair M ha hb hab
      obtain ⟨i,hi⟩:=card_pos.mp ((by decide :0<P5_7.gap degree).trans_le hc)
      obtain ⟨hi₁,hi₂⟩:=mem_sdiff.mp hi
      rcases hsite i with hw | hm
      · rw [hz] at hw
        exact (Nat.not_lt_zero _) ((card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,mem_sites.mp hi₁⟩⟩).trans_le hw)
      · rw [hz] at hm
        exact (Nat.not_lt_zero _) ((card_pos.mpr ⟨b,mem_filter.mpr ⟨hb,
          fun hh=>hi₂ (mem_sites.mpr hh)⟩⟩).trans_le hm)
    simpa only [hz,Nat.cast_zero,mul_zero,zero_add] using (show (T.card:ℚ)≤1 by exact_mod_cast hone)
  have h:=linear_count M (Nat.pos_of_ne_zero hz) (by decide) hsite
  have hmul :T.card*gap≤blockLength*H := by
    rw [Nat.mul_comm T.card]
    exact (Nat.mul_le_mul_right _ (by decide :gap≤P5_7.gap degree)).trans h
  have hgap: (0:ℚ)<gap:=Nat.cast_pos.mpr (by decide)
  have hT: (T.card:ℚ)≤(blockLength:ℚ)/gap*H := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hgap).mpr (by exact_mod_cast hmul)
  refine hT.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg H)
  rw [linearRate,mul_div_assoc]
  have hn:0≤(blockLength:ℚ)/gap:=div_nonneg (Nat.cast_nonneg _) hgap.le
  linarith only [hn]
theorem linear {x T J Q H} (A:DescendedMarks x T J Q 1 H) :
    (T.card:ℚ)≤linearRate*H+1 := by
  obtain ⟨hJ,C₀,hC₀,hseed,hsf,hs,hyf,hy⟩:=A.curve
  let:Fact (Irreducible C₀) :=⟨hC₀⟩
  obtain ⟨R⟩:=cK1 C₀ J 1 hJ hseed hsf hs Nat.one_pos
  obtain ⟨n,B,t,hbase,_,hroots⟩:=cK2 C₀ J 1 R T x.M.label x.F.scalar A.marks
  have hH :=cK3 C₀ J 1 H n R B Nat.one_pos hyf hy
  have M:UJ degree x.M.word T x.M.label x.F.scalar := by
    refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono A.subset,
      fun γ hγ=>degree_le x (A.subset hγ),?_⟩
    intro γ hγ
    let m:=x.F.mark γ (A.subset hγ)
    exact (by decide :farAgreement≤dw).trans
      (m.bad.dw.trans (card_le_card fun i hi=>mem_sites.mpr (m.scalar_hits i hi)))
  exact count M (qo38hre.sections B hH M.Kw hbase hroots x.M.word)
end
end qY7abfd
