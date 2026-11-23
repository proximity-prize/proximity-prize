import ProximityPrize.SubmissionLower.Zf6e2ca
import ProximityPrize.SubmissionLower.ZwuC0Sd
set_option Elab.async false
set_option autoImplicit true
namespace q6hAhQd
noncomputable section
open Finset Polynomial
open P6 (K dw)
open P6_7 (RectTail aic)
open P6_7_2 (Input Bs)
open P6_7_2_3 (degree oldAgreement persistentRate)
open P5_7 (midAgreement)
open cu (L)
open DQ (Ag)
open axI (c7Q)
open private OF OF.mk ceY qTOdRca.rho aaM gAN from ProximityPrize.SubmissionLower.Zf6e2ca
open private cK1 cK2 cK3 from ProximityPrize.SubmissionLower.CR
open scoped Classical
private theorem bD1 (b:RectTail) :
    b.kA.hi≤(Bs b).hi∧degree b≤qWdRihc.d:= by
  cases b <;> decide
private theorem input_degree {b:RectTail} (x :Input b) {γ:K} (hγ:γ∈x.Γ) :
    (x.F.scalar γ).natDegree≤degree b:= by
  have hh:x.M.iF≤(b.kA.hi:ℤ) :=x.kA.2
  have hn:x.h≤b.kA.hi:= by
    change x.M.iF.toNat≤b.kA.hi
    omega
  exact (aic x.F hγ).trans
    (Nat.add_le_add_left (hn.trans (bD1 b).1) 131071)
theorem persistent {b:RectTail} {x :Input b} {T J C g H}
    (hg:0<g) (hm:DescendedMarks x T J C g H) :
    (T.card:ℚ)≤persistentRate b g*H+g:= by
  have hp:=(Nat.le_mul_of_pos_left g hm.plane_pos).trans_lt hm.seed_lt
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩:=c7Q T x.M.label x.F.scalar J g H hg hp
    hm.curve (fun _ _ _ _ h=>sub_left_inj.mp h) hm.marks
  have hw:OF x.M.word U x.F.scalar (degree b) := by
    refine OF.mk (x.F.distinct.mono (hU.trans hm.subset))
      (fun γ hγ=>input_degree x (hm.subset (hU hγ))) ?_
    intro γ hγ
    let m:=x.F.mark γ (hm.subset (hU hγ))
    exact ⟨m.bad.support,(by decide :midAgreement≤dw).trans m.bad.dw,m.scalar_hits⟩
  have hreg:=ceY A hw hg (Nat.le_add_right _ _)
    ((bD1 b).2.trans (by decide :qWdRihc.d≤135070))
  have hone : (1 :ℚ)≤g:= by exact_mod_cast hg
  have hx : ((T \ U).card:ℚ)≤(Ag g:ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card:ℚ)=((T \ U).card:ℚ)+(U.card:ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _≤(Ag g:ℚ)*H +
        ((2*aaM*degree b*(Ag g:ℚ)+qTOdRca.rho (degree b))*H+1) :=
      add_le_add hx hreg
    _≤_:=(add_le_add le_rfl (add_le_add le_rfl hone)).trans_eq (by
      rw [gAN hg]
      unfold persistentRate qTOdRca.rho aaM
      ring)
theorem linear {b:RectTail} {x :Input b} {T J C H}
    (hm:DescendedMarks x T J C 1 H) :
    (T.card:ℚ)≤linearRate b*H+1 := by
  have hz :Set.InjOn x.M.label (T:Set K) := fun _ _ _ _ h=>sub_left_inj.mp h
  let W:qWdRihc.UJ :=
    ⟨T,algebraMap K L ∘ x.M.label,x.F.scalar,x.M.word,
      fun _ _ _ _ h=>sub_left_inj.mp ((algebraMap K L).injective h),
      x.F.distinct.mono hm.subset,
      fun γ hγ=>(input_degree x (hm.subset hγ)).trans (bD1 b).2,
      fun γ hγ =>
        let m:=x.F.mark γ (hm.subset hγ)
        ⟨m.bad.support,(by decide :P5_7_2.A≤dw).trans m.bad.dw,m.scalar_hits⟩⟩
  obtain ⟨hJ,C₀,hC₀,hseed,hsf,hs,hyf,hy⟩:=hm.curve
  let:Fact (Irreducible C₀) :=⟨hC₀⟩
  obtain ⟨R⟩:=cK1 C₀ J 1 hJ hseed hsf hs Nat.one_pos
  obtain ⟨n,B,t,hbase,_,hroots⟩:=cK2 C₀ J 1 R T x.M.label x.F.scalar hm.marks
  have hh:=cK3 C₀ J 1 H n R B Nat.one_pos hyf hy
  have hsite :qWdRihc.asT W T H := by
    intro i
    have he :T.filter (fun γ=>W.hit γ i) =
        T.filter (fun γ=>P5_7_7.hit x.M.word x.F.scalar γ i) :=
      filter_congr (fun _ _=>Iff.rfl)
    have hn:T.filter (fun γ => ¬ W.hit γ i) =
        T.filter (fun γ => ¬ P5_7_7.hit x.M.word x.F.scalar γ i) :=
      filter_congr (fun _ _=>Iff.rfl)
    rw [he,hn]
    exact qo38hre.sections B hh hz hbase hroots x.M.word i
  have hc: (T.card:ℚ)≤6*H+1 := by
    exact_mod_cast qWdRihc.exceptional_count W T (Subset.rfl :T⊆T) H hsite
  have hp: (0:ℚ)<(gap b:ℚ) :=Nat.cast_pos.mpr
    (Nat.sub_pos_of_lt ((bD1 b).2.trans_lt (by decide :qWdRihc.d<oldAgreement)))
  have hsmall:gap b≤48669 :=
    Nat.sub_le_sub_left (Nat.le_add_right 131071 (Bs b).hi) oldAgreement
  have hratio: (5:ℚ)≤3*262144/(gap b:ℚ) := by
    apply (le_div_iff₀ hp).mpr
    exact_mod_cast (show 5*gap b≤3*262144 by omega)
  have hrate : (6:ℚ)≤linearRate b:= by
    unfold linearRate
    linarith only [hratio]
  exact hc.trans (add_le_add (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg H)) le_rfl)
end
end q6hAhQd
