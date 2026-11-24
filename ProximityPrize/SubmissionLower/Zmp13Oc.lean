import ProximityPrize.SubmissionLower.ZJb37yc
import ProximityPrize.SubmissionLower.ZdSQxye
set_option Elab.async false
set_option autoImplicit true
namespace qEgARld
noncomputable section
open Finset Polynomial
open P5 (p blockLength)
open P5_7 (midAgreement)
open P5_7_3 (fO)

open axI (azO aVj)
open baX (mix aCz cpz)
open cz7 (a8m)
open aR (af extend)
open oR (qg)
open aF0 (power BJ YM)
open private OF OF.distinct OF.degree bf9 bNu q9NbxKa.rho aaM weights from ProximityPrize.SubmissionLower.ZogIzOe


open private arV aPh c3W from ProximityPrize.SubmissionLower.ZdSQxye
private abbrev Ut:=q9NbxKa.rho
private theorem band_bounds (b:fO) :b.jX.hi≤b.pricedHi∧b.pricedHi≤3999:= by
  cases b <;> first | exact ⟨le_rfl,by decide⟩ | decide
private theorem bu7 {d:ℕ} (hl:131071≤d) (hh:d≤135070) :
    Ut d≤aaM*d:= by
  have hdA:d< midAgreement:=hh.trans_lt (by decide)
  have hdN :d≤blockLength:=hh.trans (by decide)
  have hrho:Ut d≤3:= by
    unfold Ut q9NbxKa.rho
    have hp: (0:ℚ)<((midAgreement - d:ℕ) :ℚ) :=
      Nat.cast_pos.mpr (Nat.sub_pos_of_lt hdA)
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN,Nat.cast_sub hdA.le]
    change (262144 :ℚ) - d≤3*((179740:ℚ) - d)
    have hQ: (d:ℚ)≤135070:= by exact_mod_cast hh
    linarith only [hQ]
  have hDensity :1≤aaM:= by
    apply (le_div_iff₀ (show (0:ℚ)<(midAgreement:ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide :midAgreement≤blockLength)
  have h3: (3:ℚ)≤d:= by exact_mod_cast (show 3≤d from (by decide :3≤131071).trans hl)
  exact hrho.trans (h3.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg d)))
private theorem cEc {d m B J:ℕ} (hl:131071≤d) (hh:d≤135070)
    (hm:m≤d) (hJ:0<J) :
    let t:=max 1 (d-m)
    Ut m*BJ t B≤arV d B ∧
      Ut m*YM t B J≤aPh d B J:= by
  let t:=max 1 (d-m)
  have hd:d< midAgreement:=hh.trans_lt (by decide)
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
    (hl:131071≤d) (hh:d≤135070) (hJ:0<J)
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
  have hd:d< midAgreement:=hh.trans_lt (by decide)
  have hdp:=hd.trans (by decide :midAgreement<p)
  have ha :0<BJ t B:= by simp [BJ]
  have hv :0<YM t B J:=lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D:=MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (BJ t B) (YM t B J)
  have hcount:=bNu hw D (fun i hi=> by
    obtain ⟨cut,hc,he⟩:=cpz f hdp ht hJ hb hj sites hsum w i
    exact a8m (OF.distinct hw) f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ=>he _ (OF.degree hw γ hγ) (hreg γ hγ) (fun _ hj=>aVj hγ hj)))
  have hgap: (0:ℚ)<((midAgreement-sites.card:ℕ) :ℚ) := by
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
end
end qEgARld
