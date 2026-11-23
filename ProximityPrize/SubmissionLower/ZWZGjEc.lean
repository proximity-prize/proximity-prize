import ProximityPrize.SubmissionLower.Z2dBXLe
import ProximityPrize.SubmissionLower.ZUJ1rYc
set_option Elab.async false
set_option autoImplicit true
namespace qSCPCwb
noncomputable section
open aR (af)

open we (cH Of)
open aiJ
open P6_6 (bf mW)
open P6_6_5 (Fb acg Zl aHT)
open MvPolynomial Finset
open scoped BigOperators Polynomial
open private cSG c7T from ProximityPrize.SubmissionLower.K
open private cIR from ProximityPrize.SubmissionLower.K
open private b07 dOq c5B from ProximityPrize.SubmissionLower.ZUJ1rYc
private def aWB (Q:Bk) :aYJ:=lA Q
private def a7Q (f :af 3) :aYJ :=
  aHZ f ⊔ Ideal.span {GZ (Dm f)}
theorem bZv (f :af 3) (S:cH[X])
    (hS:S.natDegree<bf) (hf :Of f S=0) :
    Of (Dm f) S=0:= by
  have hk :bf-3+3=bf :=rfl
  change Of (oR.AR f (bf-3)) S=0
  exact dOq f S _ (hk.le.trans (by change 133426≤133672; decide)) (hk.symm ▸ hS) hf
private theorem ePk {f :af 3} {Q:Bk}
    (h:acU f Q) :a7Q f≤aWB Q:= by
  have hrow:aHZ f≤aWB Q :=
    le_sup_left.trans (((b07 f).1 Q h.solution).on_divisor)
  refine sup_le hrow ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  change tO (GZ (Dm f))∈gN Q
  rw [(bRk.proof Q h.solution.prime).2]
  intro a ha
  rw [aA3.btJ,aA3.aHI,
    bZv f _ (Nat.lt_succ_of_le (h.short a ha)) (h.solution.solves a ha),map_zero]
private theorem retuned_comparison {f :af 3} {Q:Bk}
    (h:acU f Q) :
    (aWB Q).IsPrime∧(affineHilbertPolynomial (aWB Q)).natDegree=1 ∧
      affineDegree Q≤affineDegree (aWB Q) :=
  c5B ⟨h.solution,fun a ha=>(h.short a ha).trans (by decide)⟩
private theorem fXt {f :af 3} (hf :Irreducible f) (hw : ¬ Fb f) :
    IsLeftRegular (Ideal.Quotient.mk (aHZ f) (GZ (Dm f))) := by
  have hp: (Ideal.span {f} : Ideal (af 3)).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hc:Dm f∉(Ideal.span {f} : Ideal (af 3)) :=
    fun h=>hw (Ideal.mem_span_singleton.mp h)
  apply c7T a4j (cSG a4j cS5)
  · exact fun _ _ h=>mul_left_cancel₀ hf.ne_zero h
  · exact fun _ _ h=>mul_left_cancel₀ (mt Ideal.Quotient.eq_zero_iff_mem.mp hc) h
private theorem d5R (f :af 3) (hf :Irreducible f) (hw : ¬ Fb f)
    (T:Finset aYJ)
    (hT : ∀ Q∈T,Q.IsPrime∧a7Q f≤Q ∧
      (affineHilbertPolynomial Q).natDegree=1) :
    (∑ Q∈T,affineDegree Q)≤((f.totalDegree*(Dm f).totalDegree :ℕ) :ℚ) := by
  classical
  by_cases hEmpty :T = ∅
  · rw [hEmpty,sum_empty]
    positivity
  obtain ⟨Q,hQ⟩:=nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨hp,hle,hdim⟩:=hT Q hQ
  have hPproper :=ne_top_of_le_ne_top hp.ne_top (le_sup_left.trans hle)
  have hPdim: (affineHilbertPolynomial (aHZ f)).natDegree=2 := by
    have h:=natDegree_affineHilbertPolynomial_span_singleton_add_one
      (cTb hf.ne_zero) hPproper
    rw [Nat.card_fin] at h
    change (affineHilbertPolynomial (aHZ f)).natDegree+1=3 at h
    omega
  have hcut:=principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (fXt hf hw) (bqq (Dm f))
  rw [hPdim] at hcut
  have hJdim: (affineHilbertPolynomial (a7Q f)).natDegree=1 :=
    le_antisymm hcut.1 (hdim ▸ natDegree_affineHilbertPolynomial_le_of_le hle)
  have hsub:T⊆(a7Q f).minimalPrimesFinset.filter fun P =>
      (affineHilbertPolynomial P).natDegree=(affineHilbertPolynomial (a7Q f)).natDegree := by
    intro P hP
    obtain ⟨hp',hle',hdim'⟩:=hT P hP
    exact mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr (cIR hp' hle' hJdim.le hdim'),
      hdim'.trans hJdim.symm⟩
  have hdeg:affineDegree (aHZ f)≤(f.totalDegree :ℚ) := by
    rw [aHZ,affineDegree_span_singleton (cTb hf.ne_zero)]
    exact_mod_cast bqq f
  calc
    (∑ P∈T,affineDegree P)≤affineDegree (a7Q f) :=
      (sum_le_sum_of_subset_of_nonneg hsub fun P _ _=>affineDegree_nonneg P).trans
        (sum_affineDegree_minimalPrimes_filter_le _)
    _≤((Dm f).totalDegree :ℚ)*affineDegree (aHZ f) := by
      rw [affineDegree,hJdim,Nat.factorial_one,Nat.cast_one,one_mul,Polynomial.leadingCoeff,hJdim]
      simpa [a7Q,affineDegree,hPdim,mul_assoc] using hcut.2
    _≤((f.totalDegree*(Dm f).totalDegree :ℕ) :ℚ) := by
      rw [Nat.cast_mul,mul_comm (f.totalDegree :ℚ)]
      exact mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _)
private theorem dR0 (f :af 3) (hf :Irreducible f) (hw : ¬ Fb f)
    (C:Finset Bk) (hC : ∀ Q∈C,acU f Q) :
    (∑ Q∈C,affineDegree Q)≤((f.totalDegree*(Dm f).totalDegree :ℕ) :ℚ) := by
  classical
  have hinj:Set.InjOn aWB (C:Set Bk) := by
    intro Q hQ R hR he
    exact (b07 f).2 (hC Q hQ).solution (hC R hR).solution he
  calc
    (∑ Q∈C,affineDegree Q) ≤ ∑ Q∈C,affineDegree (aWB Q) :=
      sum_le_sum fun Q hQ=>(retuned_comparison (hC Q hQ)).2.2
    _ = ∑ P∈C.image aWB,affineDegree P:=(sum_image hinj).symm
    _≤((f.totalDegree*(Dm f).totalDegree :ℕ) :ℚ) := by
      apply d5R f hf hw
      intro P hP
      obtain ⟨Q,hQ,rfl⟩:=mem_image.mp hP
      have hc:=retuned_comparison (hC Q hQ)
      exact ⟨hc.1,ePk (hC Q hQ),hc.2.1⟩
private def bZy (b:ℕ) :ℕ :=
  1+aHT*(b - 1)
private theorem dTf :Monotone bZy := by
  intro a b hab
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hab _)) _
theorem ed8 {v n:ℕ} {f :Fin n→af 3} (hf :Zl v f)
    (C:Finset Bk)
    (hsource : ∀ Q∈C,∃ i,¬ Fb (f i)∧acU (f i) Q) :
    ∃ d:Bk→ℕ,
      (∀ Q∈C,0<d Q∧affineDegree Q≤(d Q:ℚ)) ∧
        (∑ Q∈C,d Q)≤acg v := by
  classical
  by_cases hEmpty :C = ∅
  · subst C
    exact ⟨fun _=>0,by simp,by simp⟩
  obtain ⟨Q₀,hQ₀⟩:=nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨i₀,_⟩:=hsource Q₀ hQ₀
  let pick (Q:Bk) :Fin n :=
    if hQ:Q∈C then Classical.choose (hsource Q hQ) else i₀
  have hpick (Q:Bk) (hQ:Q∈C) :
      ¬ Fb (f (pick Q))∧acU (f (pick Q)) Q:= by
    simpa only [pick,dite_eq_left hQ] using Classical.choose_spec (hsource Q hQ)
  let part (i:Fin n) :=C.filter fun Q=>pick Q=i
  have hlocal (i:Fin n) : (∑ Q∈part i,affineDegree Q) ≤
      ((f i).totalDegree*(Dm (f i)).totalDegree :ℕ) := by
    have hpart (Q:Bk) (hQ:Q∈part i) :
        ¬ Fb (f i)∧acU (f i) Q:= by
      obtain ⟨hm,hi⟩:=mem_filter.mp hQ
      simpa only [hi] using hpick Q hm
    by_cases hw:Fb (f i)
    · have he :part i = ∅ := eq_empty_iff_forall_notMem.mpr fun Q hQ=>(hpart Q hQ).1 hw
      rw [he,sum_empty]
      positivity
    exact dR0 _ (hf.irreducible i) hw _ fun Q hQ=>(hpart Q hQ).2
  have hnat : (∑ i:Fin n,(f i).totalDegree*(Dm (f i)).totalDegree)≤acg v := by
    calc
      _ ≤ ∑ i:Fin n,(f i).totalDegree*bZy (mW v).b:= by
        apply sum_le_sum
        intro i _
        have hi:=(single_le_sum (f := fun j=>(f j).totalDegree)
          (fun _ _=>Nat.zero_le _) (mem_univ i)).trans hf.total
        exact Nat.mul_le_mul_left _ ((btd (f i)).trans (dTf hi))
      _=(∑ i:Fin n,(f i).totalDegree)*bZy (mW v).b:= by rw [sum_mul]
      _≤acg v :=Nat.mul_le_mul_right _ hf.total
  have hsum: (∑ Q∈C,affineDegree Q)≤(acg v :ℚ) := by
    calc
      _ = ∑ i:Fin n,∑ Q∈part i,affineDegree Q :=
        (sum_fiberwise_of_maps_to (t:=(univ :Finset (Fin n)))
          (g:=pick) (fun _ _=>mem_univ _) affineDegree).symm
      _ ≤ ∑ i:Fin n,(((f i).totalDegree*(Dm (f i)).totalDegree :ℕ) :ℚ) :=
        sum_le_sum fun i _=>hlocal i
      _≤(acg v :ℚ) := by exact_mod_cast hnat
  have hex (Q:Bk) : ∃ d:ℕ,Q∈C→0<d∧affineDegree Q=(d:ℚ) := by
    by_cases hQ:Q∈C
    · have h:=(hpick Q hQ).2
      obtain ⟨d,hd,he⟩:=aM6 Q h.solution.prime h.solution.dimension
      exact ⟨d,fun _=>⟨hd,he⟩⟩
    · exact ⟨0,fun h=>False.elim (hQ h)⟩
  let d (Q:Bk) :=Classical.choose (hex Q)
  have hd (Q:Bk) (hQ:Q∈C) :0<d Q∧affineDegree Q=(d Q:ℚ) :=
    Classical.choose_spec (hex Q) hQ
  refine ⟨d,fun Q hQ=>⟨(hd Q hQ).1,(hd Q hQ).2.le⟩,?_⟩
  have hcast: (∑ Q∈C,(d Q:ℚ))≤(acg v :ℚ) :=
    (sum_congr rfl fun Q hQ=>(hd Q hQ).2.symm).trans_le hsum
  exact_mod_cast hcast
end
end qSCPCwb
