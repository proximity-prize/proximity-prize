import ProximityPrize.SubmissionLower.ZYcqQEc
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
namespace qMskYpa
noncomputable section
open Polynomial qNu3xvc
open P5_7_1_7_4_3_4 (PencilBound gauge)
open qTFhFCb (pencilOrd pencilJet)
open qFD8jve (aFA sheetPole)
open cu (L)
open E7 (CurvePlace)
open qrezXJe (sheet_bound)
open scoped WithZero
open private chart_root from ProximityPrize.SubmissionLower.Z5cOcra
open private other other_degree coeff_other from ProximityPrize.SubmissionLower.ZN2gA7a
open private coeff_phys eval_false from ProximityPrize.SubmissionLower.Z3IN5pc
open private cast_le_one from ProximityPrize.SubmissionLower.Z62SyBc
variable {E :Type} [Field E] [Algebra L E] {A:Equation E}
private def Bounded (A:Equation E) (k :ℕ) (g:E[X][X]) :Prop :=
  g.natDegree≤A.d ∧
    (∀ i≤A.d,(g.coeff i).natDegree+i*A.s≤A.b+A.d*A.s+k) ∧
    ∀ w:CurvePlace L E,aFA w.value g (sheetPole w.value A.f)
omit [Algebra L E] in
private theorem weight (A:Equation E) (i:ℕ) (hi:i≤A.d) :
    (A.f.coeff i).natDegree+i*A.s≤A.b+A.d*A.s := by
  rcases A.weight i with h | h
  · exact h
  · rw [h,natDegree_zero,zero_add]
    exact (Nat.mul_le_mul_right _ hi).trans (Nat.le_add_left _ _)
private theorem Bounded.qW {g:E[X][X]} (h:Bounded A (A.s+1) g) :PencilBound A g:= by
  refine ⟨h.1,fun i => ?_⟩
  by_cases hi:i≤A.d
  · exact Or.inl (by simpa only [Nat.add_assoc] using h.2.1 i hi)
  · exact Or.inr (coeff_eq_zero_of_natDegree_lt (h.1.trans_lt (Nat.lt_of_not_ge hi)))
private theorem Bounded.mono {g:E[X][X]} {j k :ℕ} (h:Bounded A j g) (hjk :j≤k) :
    Bounded A k g :=
  ⟨h.1,fun i hi=>(h.2.1 i hi).trans (Nat.add_le_add_left hjk _),h.2.2⟩
private theorem Bounded.add {g h:E[X][X]} {k :ℕ}
    (hg:Bounded A k g) (hh:Bounded A k h) :Bounded A k (g+h) := by
  refine ⟨natDegree_add_le_of_degree_le hg.1 hh.1,fun i hi => ?_,fun w i j => ?_⟩
  · rw [coeff_add]
    exact (Nat.add_le_add_right (natDegree_add_le _ _) _).trans (by
      rw [← max_add_add_right]
      exact max_le (hg.2.1 i hi) (hh.2.1 i hi))
  · rw [coeff_add,coeff_add]
    exact w.value.map_add_le (hg.2.2 w i j) (hh.2.2 w i j)
private def scalar (c:L) :E[X][X] :=C (C (algebraMap L E c))
private theorem Bounded.scale {g:E[X][X]} {k :ℕ} (h:Bounded A k g) (c:L) :
    Bounded A k (scalar c*g) := by
  refine ⟨(natDegree_C_mul_le _ _).trans h.1,fun i hi => ?_,fun w i j => ?_⟩
  · rw [scalar,coeff_C_mul]
    exact (Nat.add_le_add_right (natDegree_C_mul_le _ _) _).trans (h.2.1 i hi)
  · rw [scalar,coeff_C_mul,coeff_C_mul,map_mul]
    have hc:w.value (algebraMap L E c)≤1 := by
      obtain rfl | hc:=eq_or_ne c 0
      · simp
      · exact (w.on_constants c hc).le
    exact (mul_le_mul' hc (h.2.2 w i j)).trans_eq (one_mul _)
private theorem Bounded.phys {g:E[X][X]} {k :ℕ} (h:Bounded A k g) :
    Bounded A (k+1) (C (Polynomial.X:E[X])*g) := by
  refine ⟨(natDegree_C_mul_le _ _).trans h.1,fun i hi => ?_,fun w i j => ?_⟩
  · rw [coeff_C_mul]
    have hX: (Polynomial.X*g.coeff i).natDegree≤(g.coeff i).natDegree+1 := by
      simpa only [natDegree_X,add_comm 1] using
        (natDegree_mul_le (p:=(Polynomial.X:E[X])) (q:=g.coeff i))
    have hh:=h.2.1 i hi
    omega
  · rw [coeff_C_mul]
    cases j with
    | zero=>simp
    | succ j=>rw [coeff_X_mul]; exact h.2.2 w i j
private theorem Bounded.linear {g:E[X][X]} {k :ℕ} (hd:g.natDegree≤A.d)
    (h : ∀ i≤A.d,g.coeff i≠0 → ∃ j≤A.d,∃ c:E,
      (∀ w:CurvePlace L E,w.value c≤1) ∧
        g.coeff i=C c*A.f.coeff j∧i*A.s≤j*A.s+k) :Bounded A k g:= by
  have hzero (i:ℕ) (hi:i≤A.d) (hz :g.coeff i=0) :
      (g.coeff i).natDegree+i*A.s≤A.b+A.d*A.s+k := by
    rw [hz,natDegree_zero,zero_add]
    exact (Nat.mul_le_mul_right _ hi).trans (by omega)
  refine ⟨hd,fun i hi => ?_,fun w i j => ?_⟩
  · by_cases hz :g.coeff i=0
    · exact hzero i hi hz
    · obtain ⟨m,hm,c,-,he,hs⟩:=h i hi hz
      rw [he]
      have hw:=weight A m hm
      have hc:=natDegree_C_mul_le c (A.f.coeff m)
      omega
  · by_cases hz :g.coeff i=0
    · simp [hz]
    · have hi:=(le_natDegree_of_ne_zero hz).trans hd
      obtain ⟨m,-,c,hc,he,-⟩:=h i hi hz
      rw [he,coeff_C_mul,map_mul]
      exact (mul_le_mul' (hc w) (sheet_bound w.value A.f m j)).trans_eq (one_mul _)
theorem representatives :qTFhFCb.c2 := by
  intro E _ _ A hd a b l hg hp
  let B:=A.f.derivative
  let Q:=other A.d A.f
  let Y₀:E[X][X] :=Polynomial.X
  let M:=Y₀*B
  let T := -(Y₀*Q)
  let J:=physicalDerivative A.f
  have hB:Bounded A A.s B:= by
    apply Bounded.linear ((natDegree_derivative_le _).trans (Nat.sub_le _ _))
    intro i _ hi
    have hn:A.f.coeff (i+1)≠0:= by
      intro hz
      exact hi (by simp [coeff_derivative,hz])
    refine ⟨i+1,le_natDegree_of_ne_zero hn,(i+1 :ℕ),fun w=>cast_le_one (v :=w.value) _,?_,?_⟩
    · simp only [coeff_derivative,Nat.cast_succ,C_add,C_1,C_eq_natCast]
      ring
    · rw [Nat.add_mul,one_mul]; omega
  have hM:Bounded A A.s M:= by
    have hBdeg:B.natDegree≤A.d-1 :=natDegree_derivative_le A.f
    have hMdeg:M.natDegree≤A.d:= calc
      _≤1+B.natDegree := by simpa only [Y₀,natDegree_X] using natDegree_mul_le (p:=Y₀) (q:=B)
      _≤1+(A.d-1) :=Nat.add_le_add_left hBdeg _
      _=A.d:=(Nat.add_comm _ _).trans (Nat.sub_add_cancel A.positive)
    apply Bounded.linear hMdeg
    intro i hi hz
    cases i with
    | zero=>exact (hz (coeff_X_mul_zero B)).elim
    | succ i =>
      refine ⟨i+1,hi,(i+1 :ℕ),fun w=>cast_le_one (v :=w.value) _,?_,by omega⟩
      change (Polynomial.X*A.f.derivative).coeff (i+1)= _
      rw [coeff_X_mul,coeff_derivative]
      simp only [Nat.cast_succ,C_add,C_1,C_eq_natCast]
      ring
  have hT:Bounded A A.s T:= by
    have hq:Q.natDegree≤A.d-1 := by
      have he :A.d-1+1=A.d:=Nat.sub_add_cancel A.positive
      simpa only [he] using other_degree A.f (A.d-1) he.ge
    have hTdeg:T.natDegree≤A.d:= calc
      _=(Y₀*Q).natDegree :=natDegree_neg _
      _≤1+Q.natDegree := by simpa only [Y₀,natDegree_X] using natDegree_mul_le (p:=Y₀) (q:= Q)
      _≤1+(A.d-1) :=Nat.add_le_add_left hq _
      _=A.d:=(Nat.add_comm _ _).trans (Nat.sub_add_cancel A.positive)
    apply Bounded.linear hTdeg
    intro i hi hz
    cases i with
    | zero=>exact (hz (by simp [T,Y₀])).elim
    | succ i =>
      refine ⟨i,by omega,-((A.d:E)-(i:E)),fun w => ?_,?_,?_⟩
      · rw [w.value.map_neg,sub_eq_add_neg]
        exact w.value.map_add_le (cast_le_one _) (by rw [w.value.map_neg]; exact cast_le_one _)
      · simp only [T,Y₀,Q,coeff_neg,coeff_X_mul,coeff_other,← C_eq_natCast,← C_sub,C_neg,neg_mul]
      · simp only [Nat.add_mul,one_mul,le_refl]
  have hJ:Bounded A A.s (-J) := by
    have hc (i:ℕ) : (-J).coeff i = -(A.f.coeff i).derivative := by rw [coeff_neg,coeff_phys]
    refine ⟨natDegree_le_iff_coeff_eq_zero.mpr (fun i hi=> by
      rw [hc,coeff_eq_zero_of_natDegree_lt hi,derivative_zero,neg_zero]),fun i hi => ?_,fun w i j => ?_⟩
    · rw [hc,natDegree_neg]
      have h:=weight A i hi
      have hd:=natDegree_derivative_le (A.f.coeff i)
      omega
    · rw [hc,coeff_neg,coeff_derivative,w.value.map_neg,map_mul]
      have hj:w.value ((j:E)+1)≤1 := by
        simpa only [Nat.cast_succ] using cast_le_one (v :=w.value) (j+1)
      exact (mul_le_mul' (sheet_bound w.value A.f i (j+1)) hj).trans_eq (mul_one _)
  let D:=B+scalar (l+l)*M+scalar (l*l)*T
  let N :=scalar a*(C (Polynomial.X:E[X])*D) +
    scalar b*(M+scalar l*T) + -J
  have hD:Bounded A A.s D:=(hB.add (hM.scale _)).add (hT.scale _)
  have hN :Bounded A (A.s+1) N :=
    ((hD.phys.scale _).add (((hM.add (hT.scale _)).scale _).mono (Nat.le_succ _))).add
      (hJ.mono (Nat.le_succ _))
  let e :=KM A false
  let y :=jU A false
  let P:=polar A false
  let c:=(seed A).comp (algebraMap L E)
  have hsc (z :L) :e (scalar z)=c z := by rw [eval_false]; rfl
  have hx :e (C (Polynomial.X:E[X]))=amm A:= by rw [eval_false]; rfl
  have hy :e Y₀=y :=eval₂_X _ _
  have heM:e M=y*P:= by rw [show M=Y₀*B from rfl,map_mul,hy]; rfl
  have heT:e T=y^2*P:= by
    have hf :e A.f=0:=chart_root A hd false
    change e (-(Y₀*(C (A.d:E[X])*A.f-Y₀*B)))= _
    simp only [map_neg,map_mul,map_sub,hy,hf,mul_zero,zero_sub,mul_neg,neg_neg]
    change y*(y*P)= _
    ring
  have hDe :e D =gauge A l^2*P:= by
    change e (B+scalar (l+l)*M+scalar (l*l)*T)=(1+c l*y)^2*P
    simp only [map_add,map_mul,hsc,heM,heT,show e B=P from rfl]
    ring
  refine ⟨N,D,(hN.qW),(hD.mono (Nat.le_succ _)).qW,hN.2.2,hD.2.2,hDe,?_⟩
  change e (scalar a*(C (Polynomial.X:E[X])*D) +
    scalar b*(M+scalar l*T) + -J)/e D = _
  simp only [map_add,map_mul,map_neg,hsc,hx,hDe,heM,heT,pencilOrd,pencilJet]
  change (c a*(amm A*(gauge A l^2*P))+c b*(y*P+c l*(y^2*P)) + -e J) /
    (gauge A l^2*P)=c a*amm A+(c b*(y/gauge A l)+(-e J/P)/gauge A l^2)
  have hg' : 1+c l*y≠0:=hg
  simp only [show gauge A l=1+c l*y from rfl]
  field_simp [hg',show P≠0 from hp]
  ring
end
end qMskYpa
