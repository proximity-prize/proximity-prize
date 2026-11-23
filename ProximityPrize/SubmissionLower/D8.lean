import ProximityPrize.SubmissionLower.A
set_option Elab.async false
set_option autoImplicit true
section
namespace baY
open cu (slots)

def Bp (U v g r :ℕ) :ℕ :=
 if r≤g then slots U (r*v) else 0
end baY
end
section
namespace baY
noncomputable section
open Polynomial Finset MvPolynomial
open cu (FX Equation vm slots triangle)

open Qt (aH3 gY Qc acG)

open private flatten b3z from ProximityPrize.SubmissionLower.A0




private theorem cer (C:Submodule FX Equation) {g:Equation} (hg:g≠0)
    {a U yspent spent:ℕ} (hyspent:yspent≤g.natDegree) (hspent:spent≤gY g)
    (hC : ∀ c∈C,c≠0→c.natDegree<a∧vm c U∧g∣c) :
    Module.rank FX C≤(↑((a - yspent)*slots U spent) :Cardinal) := by
  have hquot : ∀ c∈C,c≠0 → ∃ q:Equation,
      c=g*q∧q.natDegree<a - yspent∧spent+gY q≤U:= by
    intro c hc hn
    obtain ⟨hY,hU,q,rfl⟩:=hC c hc hn
    have hq:q≠0:=right_ne_zero_of_mul hn
    refine ⟨q,rfl,?_,?_⟩
    · rw [Polynomial.natDegree_mul hg hq] at hY
      omega
    · have h:=(Qc _ _).mpr hU
      rw [acG hg hq] at h
      omega
  by_cases h:0<a - yspent∧spent≤U
  · let B:=restrictBidegree (Fin 2) FX (a - yspent - 1) (U - spent)
    let m:B →ₗ[FX] Equation :=
      (LinearMap.mulLeft FX g).comp (flatten.symm.toLinearMap.comp B.subtype)
    have hm:C≤LinearMap.range m:= by
      intro c hc
      by_cases hn:c=0
      · rw [hn]
        exact (LinearMap.range m).zero_mem
      · obtain ⟨q,rfl,hq,hqU⟩:=hquot c hc hn
        refine ⟨⟨flatten q,b3z (by omega) (by omega)⟩,?_⟩
        change g*flatten.symm (flatten q)=g*q
        rw [AlgEquiv.symm_apply_apply]
    have hB:Module.finrank FX B=(a-yspent)*slots U spent:= by
      rw [MvPolynomial.finrank_restrictBidegree,slots,ite_eq_left h.2]
      simp [Nat.choose_two_right,triangle,Nat.mul_comm (U-spent+2),
        show a-yspent-1+1=a-yspent by omega]
    calc
      _≤Module.rank FX (LinearMap.range m) :=Submodule.rank_mono hm
      _≤Module.rank FX B:=rank_range_le m
      _ = _:= by rw [← Module.finrank_eq_rank,hB]
  · have hc:C = ⊥ := by
      apply bot_unique
      intro c hmem
      rw [Submodule.mem_bot]
      by_contra hn
      obtain ⟨q,_,hq,hqU⟩:=hquot c hmem hn
      exact h ⟨by omega,by omega⟩
    rw [hc]
    simp
private theorem cTX (k B W j U r E v :ℕ) (hk :0<k) (he :0<E) :
   (aH3 k B W j - r*E)*slots U (r*v) =
     ∑ q∈Ico j (B+1),if q*k≤W+j then Bp U v ((q-j)/E) r else 0:= by
 have hq (q:ℕ) :q*k≤W+j↔q<(W+j)/k+1 := by
   rw [Nat.lt_succ_iff,Nat.le_div_iff_mul_le hk]
 have hr (q:ℕ) :r≤(q-j)/E↔r*E≤q-j:=Nat.le_div_iff_mul_le he
 have hI: (Ico j (B+1)).filter (fun q=>q*k≤W+j∧r≤(q-j)/E) =
     Ico (j+r*E) (min (B+1) ((W+j)/k+1)) := by
   ext q
   simp only [mem_filter,mem_Ico,hq,hr,lt_min_iff]
   omega
 simp_rw [Bp,← ite_and]
 rw [← sum_filter,hI,sum_const,Nat.nsmul_eq_mul,Nat.card_Ico,aH3,Nat.sub_sub]
end
end baY
end
section
namespace baY
open Finset
open cu (slots triangle)
open private deK df9 crK c49 from ProximityPrize.SubmissionLower.A1
private theorem bKE (top step t j U v g:ℕ) (hj:j≤t) (hs :0<step) :
    (∑ W∈range top,if t≤W+j then
      Bp U v g (1+(top-1-W)/step-j) else 0) +
    ((∑ a∈range g,(slots U (a*v) - slots U ((a+1)*v))*(top+j-t-step*(j+a))) +
      slots U (g*v)*(top+j-t-step*(j+g))) =
    triangle U*(top+j-t) := by
  let A:=Bp U v g
  let L W:=1+(top-1-W)/step-j
  have hmono:Antitone A:= by
    intro a b hab
    by_cases hb:b≤g
    · simpa only [A,Bp,ite_eq_left hb,ite_eq_left (hab.trans hb)] using
        deK U (Nat.mul_le_mul_right v hab)
    · simp [A,Bp,hb]
  have hmin (l:ℕ) :A (min (g+1) l)=A l:= by
    by_cases hl:l≤g+1
    · rw [min_eq_right hl]
    · rw [min_eq_left (by omega)]
      simp [A,Bp,show ¬ g+1≤g by omega,show ¬ l≤g by omega]
  have hsplit :
      (∑ a∈range (g+1),(A a - A (a+1))*(top+j-t-step*(j+a))) =
        (∑ a∈range g,(slots U (a*v) - slots U ((a+1)*v))*(top+j-t-step*(j+a))) +
        slots U (g*v)*(top+j-t-step*(j+g)) := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro a ha
      simp [A,Bp,(mem_range.mp ha).le,Nat.succ_le_of_lt (mem_range.mp ha)]
    · simp [A,Bp,show ¬ g+1≤g by omega]
  rw [← hsplit]
  change (∑ W∈range top,if t≤W+j then A (L W) else 0)+_ = _
  have hzero :A 0=triangle U:= by simp [A,Bp,slots]
  rw [← hzero]
  simp_rw [← crK top j t _ _ hj]
  rw [sum_comm (s :=range (g+1)),← sum_add_distrib]
  have hbase :=crK top j t 0 (A 0) hj
  rw [Nat.sub_zero] at hbase
  rw [← hbase]
  apply sum_congr rfl
  intro W hW
  have hWt:=mem_range.mp hW
  by_cases h:t≤W+j
  · simp only [h,true_and,Nat.add_zero,hWt,ite_true]
    have hsum:=df9 A hmono (g+1) (L W)
    rw [hmin,add_comm] at hsum
    rw [← hsum]
    congr 1
    apply sum_congr rfl
    intro a _
    simp only [show a<L W↔W+step*(j+a)<top from c49 _ _ _ _ _ hWt hs]
  · simp [h]
end baY
end
