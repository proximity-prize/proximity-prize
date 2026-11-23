import ProximityPrize.SubmissionLower.ZJb37yc
set_option Elab.async false
set_option autoImplicit true
namespace qTOdRca
noncomputable section
open P5 (K I node p blockLength)
open P5_7 (midAgreement)
open qAxtVye (wX gap alO)
open DQ (Ag Wh)
open axI (azO aVj dcv c7Q c3X)
open Finset Polynomial ProximityPrize.Benchmark
private structure OF (w:I→K) (U:Finset K) (s :K→K[X]) (d:ℕ) :Prop where
  distinct :Set.InjOn s (U:Set K)
  degree : ∀ γ∈U,(s γ).natDegree≤d
  lg : ∀ γ∈U,∃ B:Finset I,midAgreement≤B.card ∧ ∀ i∈B,(s γ).eval (node i)=w i
private theorem bf9 {w U s d} (hw:OF w U s d) (hU:1<U.card) :
    (azO w U s).card≤d:= by
  obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp hU
  let P:=s a - s b
  have hp:P≠0:=sub_ne_zero.mpr fun eq=>hab (hw.distinct ha hb eq)
  refine (gR.kL.agd node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a)-(s b)).eval (node i)=0
  rw [Polynomial.eval_sub,aVj ha hi,aVj hb hi,sub_self]
private theorem bNu {w U s d} (hw:OF w U s d) (D:ℕ)
    (hsection : ∀ i:I,(∃ γ∈U,(s γ).eval (node i)≠w i) →
      (U.filter fun γ=>(s γ).eval (node i)=w i).card≤D) :
    (midAgreement - (azO w U s).card)*U.card ≤
      (blockLength-(azO w U s).card)*D:= by
  classical
  let sites :=azO w U s
  let nodes :Finset I:=univ \ sites
  let lg (γ:K) :=nodes.filter fun i=>(s γ).eval (node i)=w i
  let occ (i:I) :=U.filter fun γ=>(s γ).eval (node i)=w i
  have hhit (γ:K) (hγ:γ∈U) :midAgreement - sites.card≤(lg γ).card:= by
    obtain ⟨B,hB,hvals⟩:=hw.lg γ hγ
    let good:Finset I:=univ.filter fun i=>(s γ).eval (node i)=w i
    have hgood:midAgreement≤good.card :=
      hB.trans (card_le_card fun i hi=>mem_filter.mpr ⟨mem_univ _,hvals i hi⟩)
    have hZG:sites⊆good:= fun i hi=>mem_filter.mpr ⟨mem_univ _,aVj hγ hi⟩
    have heq :lg γ=good \ sites := by
      ext i
      simp only [lg,nodes,good,mem_filter,mem_sdiff,mem_univ,true_and]
      exact and_comm
    rw [heq,card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes :nodes.card=blockLength - sites.card:= by
    rw [card_sdiff_of_subset (subset_univ sites),card_univ,IRSProfile.card_index]
  calc
    _ = ∑ γ∈U,(midAgreement - sites.card) := by rw [sum_const,smul_eq_mul,Nat.mul_comm]
    _ ≤ ∑ γ∈U,(lg γ).card:=sum_le_sum hhit
    _ = ∑ i∈nodes,(occ i).card:= by simp only [lg,occ,card_filter]; rw [sum_comm]
    _ ≤ ∑ _i∈nodes,D:= by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _,h⟩)
    _ = _:= by rw [sum_const,smul_eq_mul,hnodes]
private def rho (s :ℕ) :ℚ :=
  ((blockLength - s :ℕ) :ℚ)/((midAgreement - s :ℕ) :ℚ)
private abbrev aaM:ℚ:=(blockLength:ℚ)/midAgreement
private theorem weights {s d:ℕ} (hs :s≤d) (hd:d< midAgreement)
    (haux :rho d≤aaM*d) :
    rho s≤ rho d∧rho s*(max 1 (d-s) :ℕ)≤aaM*d:= by
  have hAN :midAgreement≤blockLength:= by decide
  have hsA:=hs.trans_lt hd
  have hdN :=hd.le.trans hAN
  have hsN :=hs.trans hdN
  have hAs : (0:ℚ)<(midAgreement:ℚ) - s :=sub_pos.mpr (by exact_mod_cast hsA)
  have hAd: (0:ℚ)<(midAgreement:ℚ) - d:=sub_pos.mpr (by exact_mod_cast hd)
  have hmain:rho s≤ rho d:= by
    unfold rho
    rw [Nat.cast_sub hsN,Nat.cast_sub hsA.le,Nat.cast_sub hdN,Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h:=mul_nonneg (sub_nonneg.mpr (show (s :ℚ)≤d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (midAgreement:ℚ)≤blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain,?_⟩
  by_cases heq :s=d
  · subst s
    simpa using haux
  have hpos :1≤d - s := by omega
  rw [max_eq_right hpos]
  have hden: (0:ℚ)<(midAgreement:ℚ) := by exact_mod_cast (by decide :0< midAgreement)
  have hfrac: ((d-s :ℕ) :ℚ)/((midAgreement-s :ℕ) :ℚ)≤(d:ℚ)/midAgreement:= by
    rw [Nat.cast_sub hs,Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h:=mul_nonneg (Nat.cast_nonneg s : (0:ℚ)≤ s) hAd.le
    nlinarith only [h]
  calc
    _=((blockLength-s :ℕ) :ℚ)*(((d-s :ℕ) :ℚ)/((midAgreement-s :ℕ) :ℚ)) := by
      unfold rho
      ring
    _≤(blockLength:ℚ)*((d:ℚ)/midAgreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _=aaM*d:= by ring
private theorem bu7 {d:ℕ} (hl:131071≤d) (hh:d≤135070) :
    rho d≤aaM*d:= by
  have hdA:d< midAgreement:=hh.trans_lt (by decide)
  have hgap: (0:ℚ)<((midAgreement - d:ℕ) :ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt hdA
  have hdom:blockLength - d≤3*(midAgreement - d) := by
    change 262144 - d≤3*(179740 - d)
    omega
  have hrho:rho d≤3:=(div_le_iff₀ hgap).mpr (by exact_mod_cast hdom)
  have hDensity :1≤aaM:= by
    apply (le_div_iff₀ (show (0:ℚ)< midAgreement by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide :midAgreement≤blockLength)
  exact hrho.trans (calc
    (3:ℚ)≤(d:ℚ) := by exact_mod_cast (show 3≤d by omega)
    _=1*(d:ℚ) :=(one_mul _).symm
    _≤aaM*d:=mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem gAN {g:ℕ} (hg:0<g) :
    (Ag g:ℚ)=2*(g:ℚ) - 1 := by
  unfold Ag
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem ceY {n g H d:ℕ} {U:Finset K} {s :K→Polynomial K} {w}
    (A:DQ.bk0 U s g H n) (hw:OF w U s d)
    (hg:0<g) (hl:131071≤d) (hh:d≤135070) :
    (U.card:ℚ)≤(2*aaM*d*(Ag g:ℚ)+rho d)*H+1 := by
  have hbound:0≤(2*aaM*d*(Ag g:ℚ)+rho d)*(H :ℚ) := by
    unfold rho
    positivity
  by_cases hc:U.card≤1
  · have h: (U.card:ℚ)≤1 := by exact_mod_cast hc
    linarith only [h,hbound]
  let sites :=azO w U s
  let t:=max 1 (d-sites.card)
  have hd:d< midAgreement:=hh.trans_lt (by decide)
  have hs :sites.card≤d:=bf9 hw (by omega)
  have ht:0<t:=(by decide :0<1).trans_le (le_max_left _ _)
  have htp:t<p:=(max_le (by omega :1≤d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt:d≤ sites.card+t:= by
    have h:=le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C,hreconstruct⟩:=c3X sites w hdt htp hg A.equation A.equation_degree
  let D:=Ag t*(g*H)+Wh t g*H
  have hsection :=dcv (w:=w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi=>aVj hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc: ((midAgreement - sites.card:ℕ) :ℚ)*U.card≤((blockLength - sites.card:ℕ) :ℚ)*D:= by
    exact_mod_cast bNu hw D hsection
  have hden: (0:ℚ)<((midAgreement - sites.card:ℕ) :ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard: (U.card:ℚ)≤ rho sites.card*(D:ℚ) := by
    rw [rho,div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _=((midAgreement - sites.card:ℕ) :ℚ)*U.card:=mul_comm _ _
      _≤_:=hinc
  obtain ⟨hρ,hρt⟩:=weights hs hd (bu7 hl hh)
  have hρb:rho sites.card*(Ag t:ℚ)≤2*aaM*d:= by
    have hb: (Ag t:ℚ)≤2*(t:ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1 :Ag t≤2*t)
    have hρ0:0≤ rho sites.card:=div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h:=mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h,hρt]
  have hsum:g+(g - 1)=Ag g:= by unfold Ag; omega
  have hD:D =(Ag t*Ag g+1)*H := by
    rw [← hsum]
    dsimp [D,Wh]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _=(rho sites.card*(Ag t:ℚ)*(Ag g:ℚ)+rho sites.card)*H := by
      rw [hD]
      push_cast
      ring
    _≤_:=mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)
theorem proof :qAxtVye.c3:= by
  intro b u del M Γ F hband T hT J g H hg hgLimit hcurve _hseed hmarks
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩:=c7Q T M.label F.scalar J g H hg
    hgLimit hcurve (fun _ _ _ _ h=>sub_left_inj.mp h) hmarks
  let d:=wX b
  have hprice :b.jX.hi≤b.pricedHi:= by cases b <;> decide
  have hheight:M.iF≤(b.pricedHi:ℤ) :=hband.2.trans (by exact_mod_cast hprice)
  have hw:OF M.word U F.scalar d:= by
    refine ⟨F.distinct.mono (hU.trans hT),?_,?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT (hU hγ))).aic with hz | hm
      · simp [hz]
      · change ((F.scalar γ).natDegree :ℤ)≤131071+M.iF at hm
        change (F.scalar γ).natDegree≤131071+b.pricedHi
        omega
    · intro γ hγ
      let m:=F.mark γ (hT (hU hγ))
      exact ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩
  have hlo:131071≤d:=Nat.le_add_right _ _
  have hhi:d≤135070 :=
    Nat.add_le_add_left (show b.pricedHi≤3999 by cases b <;> decide) _
  have hregular :=ceY A hw hg hlo hhi
  have hgQ: (1 :ℚ)≤g:= by exact_mod_cast hg
  have hexcQ: ((T \ U).card:ℚ)≤(Ag g:ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card:ℚ)=((T \ U).card:ℚ)+(U.card:ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _≤(Ag g:ℚ)*H+((2*aaM*d*(Ag g:ℚ)+rho d)*H+1) :=
      add_le_add hexcQ hregular
    _≤(Ag g:ℚ)*H+((2*aaM*d*(Ag g:ℚ)+rho d)*H+g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _=alO b g*H+g:= by
      rw [gAN hg]
      unfold alO gap rho
      dsimp only [d]
      ring
end
end qTOdRca
