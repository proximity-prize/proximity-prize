import ProximityPrize.SubmissionLower.ZbnhR9d
set_option Elab.async false
set_option autoImplicit true
namespace qiFSOoc
noncomputable section
open Finset Polynomial
open cu (FX Equation Jet ku)
open Qt (aH3)
open P6_7_1
open private ddI df9 crK c49 from ProximityPrize.SubmissionLower.A1
open private bGH Wb from ProximityPrize.SubmissionLower.A0
private abbrev forced (N h W:ℕ) :=1+(N-1-W)/(2*h)
private def caps (s :Rectangle) (a :Fin 2) :ℕ×ℕ :=
  if a=0 then (s.t,s.z) else (s.z,s.t)
private def Bp (U v g r :ℕ) :ℕ :=
  if r≤g then U+1-r*v else 0
def aT2 (N h:ℕ) (s :Rectangle) (a :Fin 2) (E v W:ℕ) :ℕ :=
  ((caps s a).1+1)*ku s.box fun q j =>
    if q*(131071-h)≤W+j then Bp (caps s a).2 v ((q-j)/E) (forced N h W-j)
    else 0
private def b4O (N h:ℕ) (s :Rectangle) (a :Fin 2) (E v W j:ℕ) :ℕ :=
  let r :=forced N h W-j
  ((caps s a).1+1)*((aH3 (131071-h) s.B W j-r*E)*((caps s a).2+1-r*v))
private theorem ay9 (k B W j U r E v :ℕ) (hk :0<k) (he :0<E) :
    (aH3 k B W j-r*E)*(U+1-r*v) =
      ∑ q∈Ico j (B+1),if q*k≤W+j then Bp U v ((q-j)/E) r else 0:= by
  have hq (q:ℕ) :q*k≤W+j↔q<(W+j)/k+1 := by
    rw [Nat.lt_succ_iff,Nat.le_div_iff_mul_le hk]
  have hi: (Ico j (B+1)).filter (fun q=>q*k≤W+j∧r≤(q-j)/E) =
      Ico (j+r*E) (min (B+1) ((W+j)/k+1)) := by
    ext q
    simp only [mem_filter,mem_Ico,hq,Nat.le_div_iff_mul_le he,lt_min_iff]
    omega
  simp_rw [Bp,← ite_and]
  rw [← sum_filter,hi,sum_const,Nat.nsmul_eq_mul,Nat.card_Ico,aH3,Nat.sub_sub]
private theorem capacity_eq (N h:ℕ) (s :Rectangle) (a :Fin 2) (E v W:ℕ)
    (hk :0<131071-h) (he :0<E) :
    (∑ j∈range (s.J+1),b4O N h s a E v W j)=aT2 N h s a E v W:= by
  rw [aT2,← ddI,mul_sum]
  apply sum_congr rfl
  intro j _
  exact congrArg (((caps s a).1+1)*·) (ay9 _ _ _ _ _ _ _ _ hk he)
private theorem grade_rank (C:Submodule FX Equation) (s :Rectangle) (a :Fin 2)
    {f :Equation} (hf :f≠0) {r E v A:ℕ}
    (hE :E≤f.natDegree) (hv :v≤axisDegree f a)
    (hC : ∀ c∈C,c≠0 →
      c.natDegree<A∧axisDegree c 0≤ s.z∧axisDegree c 1≤ s.t∧f^r∣c) :
    Module.rank FX C≤(↑(((caps s a).1+1)*((A-r*E)*((caps s a).2+1-r*v))) :Cardinal) := by
  have he :r*E≤(f^r).natDegree := by
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_le_mul_left _ hE
  have hs :r*v≤axisDegree (f^r) a := by
    rw [axis_pow hf]
    exact Nat.mul_le_mul_left _ hv
  by_cases ha :a=0
  · subst a
    have h:=rank_multiples C (pow_ne_zero r hf) he hs (Nat.zero_le _) hC
    simpa only [caps,ite_eq_left (rfl : (0:Fin 2)=0),ite_true,
      Nat.sub_zero,Nat.mul_comm (s.t+1)] using h
  · have ha' := Fin.eq_one_of_ne_zero a ha
    rw [ha'] at hs
    have h:=rank_multiples C (pow_ne_zero r hf) he (Nat.zero_le _) hs hC
    simpa only [caps,ite_eq_right ha,Nat.sub_zero,Nat.mul_left_comm (s.z+1),Nat.mul_assoc] using h
set_option backward.isDefEq.respectTransparency false in
theorem boi (N h:ℕ) (s :Rectangle) (a :Fin 2) (E v W:ℕ)
    (V:Submodule FX Jet) {f :Equation} (hf :f≠0)
    (hE :E≤f.natDegree) (hv :v≤axisDegree f a) (hk :0<131071-h) (he :0<E)
    (hcaps : ∀ g∈V,g≠0→ g.leadingCoeff.natDegree+g.natDegree≤ s.B∧g.natDegree≤ s.J)
    (hlead : ∀ g∈V,g≠0 →
      (g.leadingCoeff.natDegree+g.natDegree)*(131071-h)≤W+g.natDegree)
    (hseed : ∀ g∈V,∀ j,axisDegree (g.coeff j) 0≤ s.z∧axisDegree (g.coeff j) 1≤ s.t)
    (hdiv : ∀ g∈V,g≠0→f^(forced N h W-g.natDegree)∣g.leadingCoeff) :
    Module.finrank FX V≤aT2 N h s a E v W:= by
  rw [← capacity_eq N h s a E v W hk he]
  refine bGH (F:=FX) (A:=Equation) V (b4O N h s a E v W)
    (s.J+1) ?_ ?_
  · intro j
    apply grade_rank _ s a hf hE hv
    rintro c ⟨⟨g,hg⟩,rfl⟩ hc
    change g.coeff j≠0 at hc
    obtain ⟨hm,hd⟩:=Wb.mp hg
    have hn:g≠0:= by intro hz; exact hc (by simp [hz])
    have hj:g.natDegree=j :=
      le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hn).2 hd))
        (le_natDegree_of_ne_zero hc)
    have hb:=(hcaps g hm hn).1
    have hw:=hlead g hm hn
    have hp:=hdiv g hm hn
    rw [hj] at hb hw hp
    obtain ⟨hz,ht⟩:=hseed g hm j
    refine ⟨?_,hz,ht,?_⟩
    · change (g.coeff j).natDegree<aH3 (131071-h) s.B W j
      rw [← hj,coeff_natDegree,hj]
      have hd' := (Nat.le_div_iff_mul_le hk).2 hw
      unfold aH3
      omega
    · change f^(forced N h W-j)∣g.coeff j
      rwa [← hj,coeff_natDegree,hj]
  · intro g hg
    by_cases hn:g=0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hcaps g hg hn).2)
private theorem bKE (top step b j U v g:ℕ) (hj:j≤b) (hs :0<step) :
    (∑ W∈range top,if b≤W+j then Bp U v g (1+(top-1-W)/step-j) else 0) +
    ((∑ i∈range g,(U+1-i*v-(U+1-(i+1)*v))*(top+j-b-step*(j+i))) +
      (U+1-g*v)*(top+j-b-step*(j+g)))=(U+1)*(top+j-b) := by
  let A:=Bp U v g
  let L W:=1+(top-1-W)/step-j
  have hmono:Antitone A:= by
    intro a b hab
    by_cases hb:b≤g
    · simp only [A,Bp,ite_eq_left hb,ite_eq_left (hab.trans hb)]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_right v hab) _
    · simp [A,Bp,hb]
  have hmin (l:ℕ) :A (min (g+1) l)=A l:= by
    by_cases hl:l≤g+1
    · rw [min_eq_right hl]
    · rw [min_eq_left (by omega)]
      simp [A,Bp,show ¬ g+1≤g by omega,show ¬ l≤g by omega]
  have hsplit :
      (∑ i∈range (g+1),(A i-A (i+1))*(top+j-b-step*(j+i))) =
        (∑ i∈range g,(U+1-i*v-(U+1-(i+1)*v))*(top+j-b-step*(j+i))) +
        (U+1-g*v)*(top+j-b-step*(j+g)) := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro i hi
      simp [A,Bp,(mem_range.mp hi).le,Nat.succ_le_of_lt (mem_range.mp hi)]
    · simp [A,Bp]
  rw [← hsplit]
  change (∑ W∈range top,if b≤W+j then A (L W) else 0)+_ = _
  have hzero :A 0=U+1 := by simp [A,Bp]
  rw [← hzero]
  simp_rw [← crK top j b _ _ hj]
  rw [sum_comm (s :=range (g+1)),← sum_add_distrib]
  have hbase :=crK top j b 0 (A 0) hj
  rw [Nat.sub_zero] at hbase
  rw [← hbase]
  apply sum_congr rfl
  intro W hW
  have hWt:=mem_range.mp hW
  by_cases h:b≤W+j
  · simp only [h,true_and,Nat.add_zero,hWt,ite_true]
    have hsum:=df9 A hmono (g+1) (L W)
    rw [hmin,add_comm] at hsum
    rw [← hsum]
    congr 1
    apply sum_congr rfl
    intro i _
    simp only [show i<L W↔W+step*(j+i)<top from c49 _ _ _ _ _ hWt hs]
  · simp [h]
theorem bDM (h:ℕ) (s :Rectangle) (a :Fin 2) (E v :ℕ)
    (hh:0<2*h) (hk :1≤131071-h) :
    (∑ W∈range (s.m*P6.dw),aT2 (s.m*P6.dw) h s a E v W) +
      rectGain h s a E v=rectVolume h s := by
  let N :=s.m*P6.dw
  let u:=(caps s a).1
  let U:=(caps s a).2
  let F W q j:=if q*(131071-h)≤W+j then Bp U v ((q-j)/E) (forced N h W-j) else 0
  let G q j :=
    let g:=(q-j)/E
    let w:=amv h s q j
    (∑ i∈range g,(U+1-i*v-(U+1-(i+1)*v))*(w-2*h*(j+i))) +
      (U+1-g*v)*(w-2*h*(j+g))
  have hvol:rectVolume h s=(u+1)*((U+1)*ku s.box (amv h s)) := by
    by_cases ha :a=0 <;> simp [rectVolume,u,U,caps,ha,Nat.mul_assoc,Nat.mul_left_comm]
  have hgain:rectGain h s a E v=(u+1)*ku s.box G:= by
    by_cases ha :a=0 <;> simp only [rectGain,G,u,U,caps,ha,ite_true,ite_false]
  rw [hgain]
  change (∑ W∈range N,(u+1)*ku s.box (F W))+(u+1)*ku s.box G= _
  rw [hvol,← mul_sum,← mul_add]
  congr 1
  have hswap: (∑ W∈range N,ku s.box (F W)) =
      ku s.box (fun q j => ∑ W∈range N,F W q j) := by
    unfold ku
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  rw [hswap]
  simp only [ku,← sum_add_distrib,mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq:=(Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left q s.box.J)
  have hq:q≤q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact bKE N (2*h) (q*(131071-h)) j U v ((q-j)/E) (hjq.trans hq) hh
end
end qiFSOoc
