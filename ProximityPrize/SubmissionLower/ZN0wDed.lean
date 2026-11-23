import ProximityPrize.SubmissionLower.ZUHlXra
import ProximityPrize.SubmissionLower.Z2dBXLe
import ProximityPrize.SubmissionLower.ZaJ8RNa
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
namespace qkZfm9d
noncomputable section
open Polynomial K1 aR dN rW wH Rl ap9 MvPolynomial
open scoped BigOperators
open private aFG dfX from ProximityPrize.SubmissionLower.ZpTf9za
open private cMx from ProximityPrize.SubmissionLower.J
open private beg bhF from ProximityPrize.SubmissionLower.J
private theorem surface_degree :ap9.c3 :=
  MJ.of_children
    (aeD.of_children bRr.proof bRs.proof)
    aA7.proof
    (E7.of_children aKt.proof
      (aFU.of_children bRt.proof bRu.proof)
      (agN.of_children bRv.proof bRw.proof
        aY4.proof bRx.proof)
      bRy.proof cyA.proof aY5.proof)
    aY6.proof
    (agO.of_children aY7.proof bRz.proof
      bRA.proof bjB.proof)
private theorem threefold_degree :ap9.c4 :=
  aRU.of_children
    (ata.of_children bRD.proof cyN.proof)
    dnh.proof
private theorem proper_degree_sum {f :af 4} (hf :Irreducible f) (T:Li f) :
    ∑ P∈Ji f T.test,affineDegree P ≤
      ((shape f).iU.b:ℚ)*(rH (shape f)).b:= by
  classical
  let V:=(aFs f).filter (fun component=>bC T.test∉component)
  let b:=(rH (shape f)).b
  have hdeg: (bC T.test).totalDegree≤b:=(beg _).trans T.aX4.1
  calc
    _ ≤ ∑ component∈V,∑ P∈(AX component T.test).minimalPrimesFinset,affineDegree P :=
      bhF V _ affineDegree affineDegree_nonneg
    _ ≤ ∑ component∈V,(b:ℚ)*affineDegree component:= by
      refine Finset.sum_le_sum fun component hZ => ?_
      obtain ⟨hZ,ht⟩:=Finset.mem_filter.mp hZ
      let _:=(Ideal.mem_minimalPrimesFinset.mp hZ).isPrime
      exact principalCut_sum_affineDegree_minimalPrimes_le ht hdeg
    _=(b:ℚ) * ∑ component∈V,affineDegree component:=(Finset.mul_sum ..).symm
    _≤(b:ℚ)*(shape f).iU.b :=
      mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun P _ _=>affineDegree_nonneg P)).trans
        (bP0 hf)) (by positivity)
    _ = _:=mul_comm _ _
private theorem b2Q {f :af 4} (hf :P6_6.wm f)
    (T:Li f) {S:ao[X]} (hm:aYV f S) :
    ∃ A:kT,akB f A∧aFG f T A∧A≤aG7 S:= by
  classical
  obtain ⟨A,ha,hApoint⟩:=hm
  have hA:=K1_13_7_2_5_1.proof f T A ha
  let Q:=lA A
  let _:Q.IsPrime :=hA.extended_prime.comap mS
  have hspan:Ideal.span {bC f} ≤ Q:=Ideal.span_le.mpr (by simpa using hA.factor)
  obtain ⟨component,hZ,hZle⟩:=Ideal.exists_minimalPrimes_le hspan
  let _:=hZ.isPrime
  have hfZ:bC f∈component:=hZ.le (Ideal.subset_span (by simp))
  have hreg:bC (separant f)∉component:= fun h=>hA.regular (hZle h)
  have hdimZ:=bPZ hf.1 hZ
  by_cases ht:bC T.test∈component
  · have htest :=(T.test_iff component hZ.isPrime hfZ hreg).mp ht
    obtain ⟨B,hb,hBle⟩:=dPz f hf component hZ hreg htest
    have hB:=K1_13_7_2_5_1.proof f T B hb
    have hmin:Minimal (fun P:n8=>P.IsPrime∧Ideal.span {bC f} ≤ P)
        component:=hZ
    have heq :lA B=component:=Minimal.eq_of_le hmin
      ⟨hB.extended_prime.comap mS,Ideal.span_le.mpr (by simpa using hB.factor)⟩ hBle
    have hBA:B≤A:=b7l hB hA ha.prime (hBle.trans hZle)
    have hdimB:dimension B=3:= by rw [← hB.dimension_eq,heq,hdimZ]
    have hmem:lA B∈aFs f := by
      rw [heq]
      exact Ideal.mem_minimalPrimesFinset.mpr hZ
    exact ⟨B,hb,Or.inr ⟨hdimB,hmem⟩,hBA.trans hApoint⟩
  · have hcut:AX component T.test≤Q :=
      sup_le hZle (Ideal.span_le.mpr (by simpa using hA.test))
    obtain ⟨P,hP,hPle⟩:=Ideal.exists_minimalPrimes_le hcut
    have hdimP:=principalCut_natDegree_affineHilbertPolynomial_add_one ht hP
    change dimension P+1=dimension component at hdimP
    have hp:dimension P=2 := by omega
    have hdimQ:2≤dimension Q:= by
      change 2≤dimension (lA A)
      rw [hA.dimension_eq]
      exact ha.dimension
    have heq :P= Q:=cMx hP.isPrime hPle hp hdimQ
    have hdimA:dimension A=2 := by
      rw [← hA.dimension_eq]
      change dimension Q=2
      rwa [← heq]
    refine ⟨A,ha,Or.inl ⟨hdimA,?_⟩,hApoint⟩
    change Q∈Ji f T.test
    rw [← heq]
    exact Finset.mem_biUnion.mpr ⟨component,
      Finset.mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr hZ,ht⟩,
      Ideal.mem_minimalPrimesFinset.mpr hP⟩
theorem proof :qs56oUd.c2 := by
  classical
  intro Γ s f hf _helig T hdistinct hdegree _hon
  let fresh:=K1_13_7_2_5_1.proof f T
  let M:=Γ.filter (fun γ=>aYV f (extend (s γ)))
  have hw (γ:M) : ∃ A:kT,akB f A∧aFG f T A ∧
      γ.val∈JI Γ s A:= by
    obtain ⟨hγ,hmark⟩:=Finset.mem_filter.mp γ.property
    obtain ⟨A,ha,hc,hp⟩:=b2Q hf T hmark
    exact ⟨A,ha,hc,ez8 hγ hp⟩
  let A:M→kT:= fun γ=>Classical.choose (hw γ)
  have hA (γ:M) :akB f (A γ)∧aFG f T (A γ)∧γ.val∈JI Γ s (A γ) :=
    Classical.choose_spec (hw γ)
  let U:=M.attach.image A
  let U₂:=U.filter (fun B=>dimension B=2)
  let U₃:=U.filter (fun B=>dimension B=3)
  have hU (B:kT) (hB:B∈U) :
      akB f B∧aFG f T B∧(JI Γ s B).Nonempty := by
    obtain ⟨γ,_,rfl⟩:=Finset.mem_image.mp hB
    exact ⟨(hA γ).1,(hA γ).2.1,⟨γ.val,(hA γ).2.2⟩⟩
  have hV₂ (B:kT) (hB:B∈U₂) :lA B∈Ji f T.test := by
    obtain ⟨hBU,hd⟩:=Finset.mem_filter.mp hB
    rcases (hU B hBU).2.1 with h | h
    · exact h.2
    · have :=h.1
      omega
  have hV₃ (B:kT) (hB:B∈U₃) :lA B∈aFs f := by
    obtain ⟨hBU,hd⟩:=Finset.mem_filter.mp hB
    rcases (hU B hBU).2.1 with h | h
    · have :=h.1
      omega
    · exact h.2
  have hinj:Set.InjOn lA (U:Set kT) := by
    intro B hB D hD he
    have hBp:=(hU B hB).1
    have hDp:=(hU D hD).1
    have hBm:=fresh B hBp
    have hDm:=fresh D hDp
    exact le_antisymm (b7l hBm hDm hDp.prime he.le)
      (b7l hDm hBm hBp.prime he.ge)
  have hpart (B:kT) :JI Γ s B⊆Γ:= fun _ hγ=>(P6.mp hγ).1
  let C:=aa9 U₂ (JI Γ s) (fun B _=>hpart B)
  let F:=aa9 U₃ (JI Γ s) (fun B _=>hpart B)
  have hdegree' (γ:K) (hγ:γ∈Γ) : (s γ).natDegree≤133671 :=
    (hdegree γ hγ).trans (by decide :P6_6.gZ≤133671)
  have hd (γ:K) (hγ:γ∈Γ) : (s γ).natDegree<bf :=
    Nat.lt_succ_of_le (hdegree' γ hγ)
  have hpoints (B:kT) : ∀ γ∈JI Γ s B,rV s γ∈zeroLocus ao B :=
    fun _ hγ=>(P6.mp hγ).2
  have hpointInj:=bsp hdistinct hdegree'
  refine ⟨C,F,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    let B:=U₂.equivFin.symm i
    obtain ⟨hBU,hdim⟩:=Finset.mem_filter.mp B.property
    exact bxh (hU B hBU).1.prime hdim
      (fun γ hγ=>hd γ (hpart B hγ)) (hpointInj.mono (hpart B)) (hpoints B)
  · intro i
    let B:=U₃.equivFin.symm i
    obtain ⟨hBU,hdim⟩:=Finset.mem_filter.mp B.property
    exact ctj (hU B hBU).1.prime hdim
      (fun γ hγ=>hd γ (hpart B hγ)) (hpointInj.mono (hpart B)) (hpoints B)
  · intro i
    let B:=U₂.equivFin.symm i
    have h:=hU B (Finset.mem_filter.mp B.property).1
    exact aT4 h.1.prime h.2.2
  · intro i
    let B:=U₃.equivFin.symm i
    have h:=hU B (Finset.mem_filter.mp B.property).1
    exact aT4 h.1.prime h.2.2
  · intro γ hγ hm
    let γ' : M:=⟨γ,Finset.mem_filter.mpr ⟨hγ,hm⟩⟩
    have hmem:A γ' ∈ U:=Finset.mem_image_of_mem A (Finset.mem_attach _ _)
    rcases (hA γ').2.1 with h | h
    · exact Finset.mem_union_left _ (a5M.mpr
        ⟨_,Finset.mem_filter.mpr ⟨hmem,h.1⟩,(hA γ').2.2⟩)
    · exact Finset.mem_union_right _ (a5M.mpr
        ⟨_,Finset.mem_filter.mpr ⟨hmem,h.1⟩,(hA γ').2.2⟩)
  · have hsum:=dfX U₂ (Ji f T.test)
      (hinj.mono (Finset.filter_subset _ _)) hV₂
    have hb:2*(C.total:ℚ) ≤
        (133671 :ℚ)*(shape f).iU.b*(rH (shape f)).b:= calc
      _≤2 * ∑ B∈U₂,affineDegree B :=
        mul_le_mul_of_nonneg_left (a6x (T:=U₂) (part:=JI Γ s)) (by positivity)
      _ ≤ ∑ B∈U₂,133671*affineDegree (lA B) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun B hB => ?_
        obtain ⟨hBU,hdim⟩:=Finset.mem_filter.mp hB
        have h:=(hU B hBU).1
        have hb:=fresh B h
        exact surface_degree B h.prime hb.extended_prime hdim (bGZ hb)
      _=133671 * ∑ B∈U₂,affineDegree (lA B) :=(Finset.mul_sum ..).symm
      _≤_:= by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hsum.trans (proper_degree_sum hf.1 T)) (by positivity)
    exact_mod_cast hb
  · let b:=((rH (shape f)).b:ℚ)
    have hsum:=dfX U₃ (aFs f)
      (hinj.mono (Finset.filter_subset _ _)) hV₃
    have hb: (F.total:ℚ)≤((shape f).iU.b:ℚ)*b^2 := calc
      _ ≤ ∑ B∈U₃,affineDegree B:=a6x
      _ ≤ ∑ B∈U₃,affineDegree (lA B)*b^2 := by
        refine Finset.sum_le_sum fun B hB => ?_
        obtain ⟨hBU,hdim⟩:=Finset.mem_filter.mp hB
        have h:=(hU B hBU).1
        exact threefold_degree f T B h (fresh B h) hdim
      _=(∑ B∈U₃,affineDegree (lA B))*b^2 :=(Finset.sum_mul ..).symm
      _≤_:=mul_le_mul_of_nonneg_right (hsum.trans (bP0 hf.1)) (by positivity)
    dsimp only [b] at hb
    exact_mod_cast hb
end
end qkZfm9d
