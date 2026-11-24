import ProximityPrize.SubmissionLower.ZQfUTPd
set_option Elab.async false
namespace qrezXJe
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K p)
open qkgz7gb (branchDegree)

open qFD8jve (aFA)
open P5_7_3_5_2 (Variation)
open cu (L j9)
open E7 (CurveField CurvePlace axV KB)
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
def c1 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (f :E[X][X]) (D:ℕ) (r :L) (G:E[X])
    (w:CurvePlace L E) (a :E →ₐ[L] LaurentSeries L) (P:L[X]),
    CurveField L E→ Irreducible f→0<f.natDegree→f.natDegree<p →
    (∀ c,w.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c)) →
    aFA w.value f 0→polyBound w.value G 0 →
    branch f r≠0→G.leadingCoeff=(branch f r).leadingCoeff →
    G.Separable→G∣branch f r→(∃ n:ℕ,branch f r∣G^n)→G.natDegree<p →
    w.value G.leadingCoeff=1→P.natDegree≤D →
    rootEval (qb0hmCe.cLN a 0 f) P=0→Nonempty (LocalVariation a f P D G)
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (G:E[X])
    (w:CurvePlace L E) (a :E →ₐ[L] LaurentSeries L),
    (∀ c,w.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c)) →
    G.Separable→G.natDegree<p→polyBound w.value G 0→w.value G.leadingCoeff=1 →
    (EuclideanDomain.gcd (residuePoly a G) (residuePoly a G).derivative).natDegree ≤
      KB w.value (discriminantResultant G)
private theorem degree_mono {D d e W:ℕ} (hde :d≤e) (hW:e*D ≤W) :
  2*d*W-d*d*D ≤2*e*W-e*e*D:= by
 have h (n m:ℕ) (hn:n≤e) (hm:m≤e) : (n+m)*D ≤2*W:= by
  rw [Nat.add_mul,two_mul]
  exact Nat.add_le_add ((Nat.mul_le_mul_right _ hn).trans hW)
    ((Nat.mul_le_mul_right _ hm).trans hW)
 have hi (n:ℕ) (hn:n≤e) :n*n*D ≤2*n*W:= by
  calc
    _=n*(n*D) :=Nat.mul_assoc ..
    _≤n*((n+n)*D) :=Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
    _≤n*(2*W) :=Nat.mul_le_mul_left _ (h n n hn hn)
    _ = _:= by ring
 have hh:=h d e hde le_rfl
 zify [hi d hde,hi e le_rfl] at hde hh ⊢
 nlinarith [mul_nonneg (sub_nonneg.mpr hde) (sub_nonneg.mpr hh)]
private theorem bad_one {E :Type} [Field E] (w:Valuation E ℤᵐ⁰) {c:E}
  (hc:c≠0) (hle :w c≤1) (hne :w c≠1) :1≤KB w c:= by
 have hlog:WithZero.log (w c)<(0:ℤ) :=
  (WithZero.log_lt_iff_lt_exp (w.zero_iff.not.mpr hc)).2 (by
    simpa using lt_of_le_of_ne hle hne)
 unfold KB
 omega
private theorem residue_nonzero {E :Type} [Field E] [Algebra L E] (G:E[X])
  (w:CurvePlace L E) (a :E →ₐ[L] LaurentSeries L)
  (ha : ∀ c,w.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c))
  (hu:w.value G.leadingCoeff=1) :residuePoly a G≠0:= by
 have hcoeff (i:ℕ) : (residuePoly a G).coeff i=(a (G.coeff i)).coeff 0 :=
  sum_coeff (fun c=>(a c).coeff 0) (by simp) G i
 have hv :=(ha G.leadingCoeff).symm.trans hu
 obtain ⟨u,hEq⟩:=(LaurentSeries.val_le_one_iff_eq_coe L _).mp hv.le
 have h1 : (a G.leadingCoeff).coeff 0≠0:= by
  intro hzero
  have hz :=(q1kuFjb.power_residue _ _ hEq.symm).symm.trans hzero
  have hlt:=(q1kuFjb.small_valuation u).mpr hz
  rw [hEq,hv] at hlt
  have h:=WithZero.exp_le_exp.mp (show WithZero.exp (0:ℤ)≤WithZero.exp (-1 :ℤ) by
    rwa [WithZero.exp_zero])
  omega
 intro h0
 change (a (G.coeff G.natDegree)).coeff 0≠0 at h1
 exact h1 (by rw [← hcoeff,h0,coeff_zero])
theorem of_children (variation :c1) (rank :c2) :
    P5_7_3_5_2.c3:= by
  intro q CM z S F D e W v hok hd hwt hS
  obtain ⟨_,_,_,he,hW,hM⟩:=hok
  let m:=branchDegree D e W (.symmetric v)
  let d:=F.d
  have hp:d<p:=hd.trans_lt he
  obtain ⟨r,hn,hm,hB⟩:=branch_exists F.f D W F.irreducible F.positive hp hwt
  let B:=branch F.f r
  have hm' : B.natDegree≤ m:=hm.trans (degree_mono hd hW)
  obtain ⟨G,hlc,hs,hg,hpow,hG⟩:=scaled_radical B hn (hm'.trans_lt hM)
  have hdeg:G.natDegree≤ m:=(natDegree_le_of_dvd hg hn).trans hm'
  have hpG:=hdeg.trans_lt hM
  have hdiv :axV L CM.E :=
    aFU.of_children bRt.proof bRu.proof L CM.E CM.curve
  let T:=F.marks.filter fun γ=>(F.place γ).value B.leadingCoeff=1
  have hT:T⊆F.marks :=filter_subset _ _
  have hF0 (γ:K) (hγ:γ∈F.marks) :aFA (F.place γ).value F.f 0:= by
    simpa [aFA] using F.integral γ hγ
  have hI (γ:K) (hγ:γ∈F.marks) :polyBound (F.place γ).value G 0:= by
    simpa using hG (F.place γ) 0 (hB _ 0 (hF0 γ hγ))
  have hU (γ:K) (hγ:γ∈T) : (F.place γ).value G.leadingCoeff=1 :=
    hlc ▸ (mem_filter.mp hγ).2
  let Vloc (γ:K) (hγ:γ∈T) :=
    Classical.choice (variation F.f D r G (F.place γ) (F.atPlace γ (hT hγ)) (j9 (S γ))
      CM.curve F.irreducible F.positive hp (F.value γ (hT hγ)) (hF0 γ (hT hγ)) (hI γ (hT hγ))
      hn hlc hs hg hpow hpG (hU γ hγ) (natDegree_map_le.trans (hS γ (hT hγ))) (F.root γ (hT hγ)))
  let V:Variation F := {
    marks :=T
    Bp:=hT
    num := fun γ=>if hγ:γ∈T then (Vloc γ hγ).num else 0
    den:= fun γ=>if hγ:γ∈T then (Vloc γ hγ).den else 1
    den_ne := fun γ hγ=> by simpa only [dite_eq_left hγ] using (Vloc γ hγ).den_ne
    reduced:= fun γ hγ=> by simpa only [dite_eq_left hγ] using (Vloc γ hγ).reduced
    simple := fun γ hγ=>(Vloc γ hγ).simple
    formula := fun γ hγ=> by simpa only [dite_eq_left hγ,tangentValue,tangentDenom,rootEval,P5_7_3_5_2.atPolynomial] using
      (Vloc γ hγ).formula }
  refine ⟨V,?_,?_⟩
  · have hc:B.leadingCoeff≠0:=leadingCoeff_ne_zero.mpr hn
    have hcard: (F.marks \ T).card ≤ ∑ γ∈F.marks \ T,KB (F.place γ).value B.leadingCoeff := by
      rw [Finset.card_eq_sum_ones]
      apply sum_le_sum
      intro γ hγ
      obtain ⟨hγF,hγT⟩:=mem_sdiff.mp hγ
      refine bad_one (F.place γ).value hc ?_ (fun heq=>hγT (mem_filter.mpr ⟨hγF,heq⟩))
      exact (hB (F.place γ) 0 (hF0 γ hγF) B.natDegree).trans_eq (by simp only [Nat.mul_zero,Nat.cast_zero,WithZero.exp_zero])
    refine (hcard.trans (sum_zeroOrder hdiv _ F.place
      (F.distinct.mono fun _ hg=>(mem_sdiff.mp hg).1) F.f _ (2*d) hc (fun w => ?_))).trans ?_
    · exact hB w _ (sheet_bound w.value F.f) B.natDegree
    · exact Nat.mul_le_mul_right _ (by gcongr)
  · let g:=discriminantResultant G
    have hgn:g≠0:= by
      by_cases h0:G.natDegree=0
      · simp [g,discriminantResultant,h0,resultant]
      let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
      let _:CharP CM.E p:=charP_of_injective_ringHom (algebraMap L CM.E).injective p
      have hdd:=bD9 (Nat.pos_of_ne_zero h0) hpG
      unfold g discriminantResultant
      rw [← hdd]
      exact resultant_ne_zero _ _ hs
    have hlocal : ∑ γ∈V.marks,V.DG D γ ≤ ∑ γ∈T,KB (F.place γ).value g:= by
      apply sum_le_sum
      intro γ hγ
      let a :=F.atPlace γ (hT hγ)
      let Q:=Vloc γ hγ
      have hr :=residue_nonzero G (F.place γ) a (F.value γ (hT hγ)) (hU γ hγ)
      have hgcd:EuclideanDomain.gcd (residuePoly a G) (residuePoly a G).derivative≠0 :=
        fun he=>hr (EuclideanDomain.gcd_eq_zero_iff.mp he).1
      have hden:Q.den.natDegree≤(EuclideanDomain.gcd (residuePoly a G) (residuePoly a G).derivative).natDegree :=
        natDegree_le_of_dvd Q.divides hgcd
      have hnum := Q.infinity
      have hx :V.DG D γ≤Q.den.natDegree := by
        simp only [Variation.DG,V,dite_eq_left hγ,← show Q=Vloc γ hγ from rfl]
        exact max_le le_rfl (by omega)
      exact hx.trans (hden.trans (rank G (F.place γ) a (F.value γ (hT hγ)) hs hpG
        (hI γ (hT hγ)) (hU γ hγ)))
    have hsum:=sum_zeroOrder hdiv T F.place (F.distinct.mono hT) F.f g ((2*G.natDegree-1)*(2*d)) hgn
      (fun w=> by
        rw [Nat.mul_assoc]
        exact discriminant_bound w.value G _ (hG w _ (hB w _ (sheet_bound w.value F.f))))
    refine hlocal.trans (hsum.trans (Nat.mul_le_mul_right _ ?_))
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul (by gcongr) (Nat.sub_le_sub_right (by gcongr) _)
end
end qrezXJe
