import ProximityPrize.SubmissionLower.ZogIzOe
import ProximityPrize.SubmissionLower.Z77J3Nc
import ProximityPrize.SubmissionLower.Z6ykYva
set_option Elab.async false
set_option autoImplicit true
namespace qrxbUDe
noncomputable section
open Finset Polynomial
open P5 (K node p blockLength)
open P5_7_2 (fO jX row)
open q7F2qKe (wX au1 weakAgreement)
open axI (azO aVj)
open baX (mix aCz cpz)
open cz7 (a8m)
open aR (af extend)
open oR (qg)
open ana (aVQ)
open aF0 (power BJ YM)
open private OF OF.mk OF.distinct OF.degree OF.lg bf9 bNu q9NbxKa.rho aaM weights from ProximityPrize.SubmissionLower.ZogIzOe
open private Wq from ProximityPrize.SubmissionLower.ZJ86yqc
open private cSy from ProximityPrize.SubmissionLower.Z6ykYva
private abbrev errors :ℕ:=blockLength - weakAgreement
private theorem bLI (b:fO) :
    (jX b).hi≤(row b).declaredHi∧(row b).declaredHi≤2703:= by
  fin_cases b <;> decide
private theorem dmf {w T s d} (h:OF w T s d) {U:Finset K}
    (hU:U⊆T) :OF w U s d :=
  OF.mk ((OF.distinct h).mono hU) (fun γ hγ=>OF.degree h γ (hU hγ))
    (fun γ hγ=>OF.lg h γ (hU hγ))
private theorem ePE {w T s d B J} (hw:OF w T s d)
    (hd₀:2≤d) (hd:d<weakAgreement) (hJ:0<J)
    (f :af 2) (hf :Irreducible f) (hfpos :0<f.degreeOf 1)
    (hb:f.totalDegree≤B) (hj:f.degreeOf 1≤J)
    (hreg : ∀ γ∈T,qg 1 f (extend (s γ))) :
    (T.card:ℚ) ≤
      ((errors :ℚ)/(weakAgreement - d:ℕ)) *
        mix f.totalDegree (f.degreeOf 1) (BJ d B) (YM d B J)+1 := by
  classical
  have hchart:=czH.proof
  obtain ⟨C⟩:=hchart f d B J hd₀ (hd.trans (by decide :weakAgreement<180265)) hJ hb hj
  have hcount:=Wq (err :=errors) rfl (by decide) hd
    (OF.distinct hw) (OF.degree hw) (OF.lg hw)
    (MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (BJ d B) (YM d B J))
    (fun i hi =>
      a8m (OF.distinct hw) f hf hfpos hreg (by simp [BJ])
        (lt_min (by simp [BJ]) (by omega)) i hi (C.cut (node i) (w i))
        (aVQ _ (C.ags _ _) (C.top_bound _ _))
        (fun γ hγ=>C.agrees _ (OF.degree hw γ hγ) (hreg γ hγ) _ _))
  have hgap: (0:ℚ)<((weakAgreement-d:ℕ) :ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt hd
  have hc:=(le_div_iff₀ hgap).mpr (by exact_mod_cast (mul_comm _ _).trans_le hcount :
    (T.card:ℚ)*(↑(weakAgreement-d:ℕ) :ℚ) ≤
      errors*MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1)
        (BJ d B) (YM d B J)+(↑(weakAgreement-d:ℕ) :ℚ))
  have hv :YM d B J≤BJ d B:=min_le_left _ _
  rw [aCz (f.degreeOf_le_totalDegree 1) hv] at hc
  refine hc.trans_eq ?_
  field_simp
private abbrev Ut:=q9NbxKa.rho
private theorem bu7 {d:ℕ} (hl:131071≤d) (hh:d≤133774) :
    Ut d≤aaM*d:= by
  have hdA:d<weakAgreement:=hh.trans_lt (by decide)
  have hdN :d≤blockLength:=hh.trans (by decide)
  have hrho:Ut d≤3:= by
    unfold Ut q9NbxKa.rho
    have hp: (0:ℚ)<((weakAgreement - d:ℕ) :ℚ) :=
      Nat.cast_pos.mpr (Nat.sub_pos_of_lt hdA)
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN,Nat.cast_sub hdA.le]
    change (262144 :ℚ) - d≤3*((179740:ℚ) - d)
    have hQ: (d:ℚ)≤133774 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity :1≤aaM:= by
    apply (le_div_iff₀ (show (0:ℚ)<(weakAgreement:ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide :weakAgreement≤blockLength)
  have h3: (3:ℚ)≤d:= by exact_mod_cast (show 3≤d from (by decide :3≤131071).trans hl)
  exact hrho.trans (h3.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg d)))
private def arV (d B:ℕ) :ℚ:=Ut d+2*aaM*d*(B-1 :ℕ)
private def aPh (d B J:ℕ) :ℚ :=
  min (arV d B) (aaM*d*(2*J-1 :ℕ))
private theorem c3W (d B:ℕ) :0≤arV d B:= by
  unfold arV Ut q9NbxKa.rho
  positivity
private theorem cEc {d m B J:ℕ} (hl:131071≤d) (hh:d≤133774)
    (hm:m≤d) (hJ:0<J) :
    let t:=max 1 (d-m)
    Ut m*BJ t B≤arV d B ∧
      Ut m*YM t B J≤aPh d B J:= by
  let t:=max 1 (d-m)
  have hd:d<weakAgreement:=hh.trans_lt (by decide)
  obtain ⟨hMu,hLambda⟩:=weights hm hd (bu7 hl hh)
  change Ut m*t≤aaM*d at hLambda
  have hRatio:0≤Ut m:= by unfold Ut q9NbxKa.rho; positivity
  have hp: (power t:ℚ)≤2*(t:ℚ) := by
    exact_mod_cast (Nat.sub_le (2*t) 3)
  have hpow:Ut m*power t≤2*(aaM*d) := by
    have h:=mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h,hLambda]
  have htot:Ut m*BJ t B≤arV d B:= by
    unfold BJ arV
    push_cast
    rw [mul_add,mul_one,← mul_assoc,show 2*aaM*(d:ℚ)=2*(aaM*d) from
      mul_assoc _ _ _]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot,?_⟩
  unfold aPh
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show YM t B J≤BJ t B from min_le_left _ _)) hRatio).trans htot
  · have hcap:YM t B J≤t*(2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1=2*(J-1)+1 by omega,Nat.mul_add,Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _≤Ut m*((t*(2*J-1) :ℕ) :ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _=(Ut m*t)*(2*J-1 :ℕ) := by push_cast; ring
      _≤_:=mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
private theorem eK0 {w T s d B J} (hw:OF w T s d)
    (hl:131071≤d) (hh:d≤133774) (hJ:0<J)
    (f :af 2) (hf :Irreducible f) (hfpos :0<f.degreeOf 1)
    (hb:f.totalDegree≤B) (hj:f.degreeOf 1≤J)
    (hreg : ∀ γ∈T,qg 1 f (extend (s γ))) :
    (T.card:ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (arV d B) (aPh d B J)+1 := by
  have hpos :0≤ mix f.totalDegree (f.degreeOf 1) (arV d B) (aPh d B J) := by
    have ha :0≤arV d B:=c3W d B
    have hv :0≤aPh d B J:=le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall:T.card≤1
  · exact (show (T.card:ℚ)≤1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites :=azO w T s
  let t:=max 1 (d-sites.card)
  have hs :sites.card≤d:=bf9 hw (by omega)
  have ht:t≤d:=max_le (by omega) (Nat.sub_le _ _)
  have htpos :0<t:=(Nat.le_max_left _ _)
  have hsum:d≤ sites.card+t:= by
    have h:=Nat.le_max_right 1 (d-sites.card)
    omega
  have hd:d<weakAgreement:=hh.trans_lt (by decide)
  have hdp:=hd.trans (by decide :weakAgreement<p)
  have ha :0<BJ t B:= by simp [BJ]
  have hv :0<YM t B J:=lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D:=MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (BJ t B) (YM t B J)
  have hcount:=bNu hw D (fun i hi=> by
    obtain ⟨cut,hc,he⟩:=cpz f hdp ht hJ hb hj sites hsum w i
    exact a8m (OF.distinct hw) f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ=>he _ (OF.degree hw γ hγ) (hreg γ hγ) (fun _ hj=>aVj hγ hj)))
  have hgap: (0:ℚ)<((weakAgreement-sites.card:ℕ) :ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio: (T.card:ℚ)≤Ut sites.card*D:= by
    unfold Ut q9NbxKa.rho
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card:ℚ)]
    exact_mod_cast hcount
  have hvle :YM t B J≤BJ t B:=min_le_left _ _
  dsimp only [D] at hratio
  rw [aCz (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA,hcapV⟩:=cEc (B:=B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _=(↑(f.totalDegree - f.degreeOf 1 :ℕ) :ℚ)*(Ut sites.card*YM t B J) +
        f.degreeOf 1*(Ut sites.card*BJ t B) := by ring
    _≤(↑(f.totalDegree - f.degreeOf 1 :ℕ) :ℚ)*aPh d B J +
        f.degreeOf 1*arV d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _≤_:=le_add_of_nonneg_right (by decide)
theorem proof :q7F2qKe.c2 := by
  classical
  intro b u del M Γ F hband B J guard G hG T hT hroot
  let d:=wX b
  have hdl:131071≤d:=Nat.le_add_right _ _
  have hdu:d≤133774 :=Nat.add_le_add_left (bLI b).2 131071
  have hd:d<weakAgreement:=hdu.trans_lt (by decide)
  have hw:OF M.word T F.scalar d:= by
    refine OF.mk (F.distinct.mono hT) ?_ ?_
    · intro γ hγ
      rcases (F.mark γ (hT hγ)).aic with hz | hdeg
      · simp [hz]
      · have hhi:=hband.2
        have hdecl:=(bLI b).1
        change ((F.scalar γ).natDegree :ℤ)≤131071+M.iF at hdeg
        change (F.scalar γ).natDegree≤131071+(row b).declaredHi
        omega
    · intro γ hγ
      let mark :=F.mark γ (hT hγ)
      exact ⟨mark.bad.support,mark.bad.dw,mark.scalar_hits⟩
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
end
end qrxbUDe
