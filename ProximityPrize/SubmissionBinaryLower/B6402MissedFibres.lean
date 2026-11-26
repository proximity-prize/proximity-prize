import ProximityPrize.SubmissionBinaryLower.B6401ResLineOrd

/-! The regular-fibre parity used by the 6402 extra interpolation conditions.
All derivatives are ordinary formal derivatives in characteristic two. -/

namespace ProximityPrize.SubmissionBinaryLower.B6402MissedFibres

open Polynomial B6401ContactKerD B6401ResLineOrd
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {K : Type*}
local notation "B" => BiPoly K

section Parity
variable [CommRing K] [IsDomain K]

noncomputable def flow (f₀ f₁ v : B) : B := f₁*dXBi v + f₀*v.derivative

private lemma flow_add (a b p q : B) :
    flow a b (p+q) = flow a b p + flow a b q := by
  simp only [flow, dXBi_add, derivative_add]; ring

private lemma flow_mul (a b p q : B) :
    flow a b (p*q) = flow a b p*q+p*flow a b q := by
  simp only [flow, dXBi_mul, derivative_mul]; ring

private lemma flow_one (a b : B) : flow a b 1 = 0 := by
  have h : dXBi (1:B) = 0 := by ext j; simp [coeff_dXBi,coeff_one]; split_ifs <;> simp
  simp [flow,h]

private lemma flow_eigen_pow (a b v h : B) (hv : flow a b v = h*v) (n : ℕ) :
    flow a b (v^n) = (n:B)*h*v^n := by
  induction n with
  | zero => simp [flow_one]
  | succ n ih => rw [pow_succ,flow_mul,ih,hv,Nat.cast_succ]; ring

private lemma flow_sum (a b : B) (v : ℕ → B) (n : ℕ) :
    flow a b (∑ j ∈ Finset.range n, v j) = ∑ j ∈ Finset.range n, flow a b (v j) := by
  induction n with
  | zero =>
    have h : dXBi (0:B) = 0 := by ext j; simp [coeff_dXBi]
    simp [flow,h]
  | succ n ih => rw [Finset.sum_range_succ,Finset.sum_range_succ,flow_add,ih]

private lemma shifted_sum (a b : ℕ → B) (n : ℕ) (h₀ : a 0=0) (hn : b n=0)
    (h : ∀ j<n, a (j+1) = -b j) :
    (∑ j ∈ Finset.range (n+1), (a j+b j)) = 0 := by
  rw [Finset.sum_add_distrib,Finset.sum_range_succ' a,Finset.sum_range_succ b,h₀,hn,add_zero,add_zero]
  rw [Finset.sum_congr rfl (fun j hj => h j (Finset.mem_range.mp hj)), Finset.sum_neg_distrib,neg_add_cancel]

variable [CharP K 2]

/-- The slope resultant is an eigenvector of the vector field defined by F,
including when the resultant is identically zero. -/
theorem resultant_flow (F G : ContactPoly K) (s : ℕ) (hF : F.natDegree≤1)
    (hG : G.natDegree≤s) (dF : contactDeriv F=0) (dG : contactDeriv G=0) :
    flow (F.coeff 0) (F.coeff 1) (resultant F G 1 s) =
      (s:B)*dXBi (F.coeff 1)*resultant F G 1 s := by
  classical
  let a := F.coeff 0
  let b := F.coeff 1
  let h := dXBi b
  have haX : dXBi a=0 := by
    simpa [a,coeff_contactDeriv] using congrArg (fun p : ContactPoly K => p.coeff 0) dF
  have haY : a.derivative=h := by
    have hx : h + a.derivative = 0 := by
      simpa [h,b,a,coeff_contactDeriv] using congrArg (fun p : ContactPoly K => p.coeff 1) dF
    have htwo : (2:B)=0 := CharP.cast_eq_zero _ 2
    linear_combination hx - h * htwo
  have bY : b.derivative=0 := by
    have hh := congrArg (fun p : ContactPoly K => p.coeff 2) dF
    have h2 := coeff_eq_zero_of_natDegree_lt (show F.natDegree<2 by omega)
    have hz : dXBi (0:B)=0 := by ext j; simp [coeff_dXBi]
    simpa [b,coeff_contactDeriv,h2,hz] using hh
  have ha : flow a b a=h*a := by simp [flow,haX,haY]; ring
  have hb : flow a b b=h*b := by simp [flow,bY,h]; ring
  let p (j : ℕ) := b*dXBi (G.coeff j)*a^j*b^(s-j)
  let t (j : ℕ) := a*(G.coeff j).derivative*a^j*b^(s-j)
  have gX₀ : dXBi (G.coeff 0)=0 := by
    simpa [coeff_contactDeriv] using congrArg (fun v : ContactPoly K => v.coeff 0) dG
  have gYs : (G.coeff s).derivative=0 := by
    have hh:=congrArg (fun v : ContactPoly K => v.coeff (s+1)) dG
    have hh' := coeff_eq_zero_of_natDegree_lt (show G.natDegree<s+1 by omega)
    have hz : dXBi (0:B)=0 := by ext j; simp [coeff_dXBi]
    simpa [coeff_contactDeriv,hh',hz] using hh
  have cancel : (∑ j ∈ Finset.range (s+1), (p j+t j))=0 := by
    apply shifted_sum _ _ _ (by simp [p,gX₀]) (by simp [t,gYs])
    intro j hj
    have hh : dXBi (G.coeff (j+1)) + (G.coeff j).derivative = 0 := by
      simpa [coeff_contactDeriv] using congrArg (fun v : ContactPoly K => v.coeff (j+1)) dG
    have hh' : dXBi (G.coeff (j+1)) = -(G.coeff j).derivative := eq_neg_of_add_eq_zero_left hh
    dsimp [p,t]
    rw [hh',show s-j=(s-(j+1))+1 by omega,pow_succ,pow_succ]; ring
  rw [resultant_deg1_char2]
  change flow a b (∑ j ∈ Finset.range (s+1), G.coeff j*a^j*b^(s-j)) =
    (s:B)*h*∑ j ∈ Finset.range (s+1), G.coeff j*a^j*b^(s-j)
  rw [flow_sum,Finset.mul_sum]
  have hEach (j : ℕ) (hj : j∈Finset.range (s+1)) :
      flow a b (G.coeff j*a^j*b^(s-j)) =
        (p j+t j) + (s:B)*h*(G.coeff j*a^j*b^(s-j)) := by
    have hj' : j≤s := by simpa using hj
    rw [flow_mul,flow_mul,flow_eigen_pow _ _ _ _ ha,flow_eigen_pow _ _ _ _ hb]
    have hadd : ((s-j : ℕ):B)+(j:B)=(s:B) := by
      simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n:B)) (Nat.sub_add_cancel hj')
    dsimp [p,t,flow]
    linear_combination h * G.coeff j * a^j * b^(s-j) * hadd
  rw [Finset.sum_congr rfl hEach,Finset.sum_add_distrib,cancel,zero_add]

/-- Once an odd number of spatial layers vanishes, the next layer is automatic
at any prime transverse to this vector field. -/
theorem next_layer {a b π φ eigen : B} (hπ : Prime π) (hregular : ¬ π ∣ flow a b π)
    (hφ : flow a b φ=eigen*φ) (j : ℕ) (hd : π^(2*j+1) ∣ φ) :
    π^(2*j+2) ∣ φ := by
  obtain ⟨u,hu⟩ := hd
  have htwo : (2:B)=0 := CharP.cast_eq_zero _ 2
  have hs : flow a b (π^(2*j))=0 := by
    rw [show 2*j=j+j by omega,pow_add,flow_mul]
    linear_combination flow a b (π^j) * π^j * htwo
  rw [hu,pow_succ,flow_mul,flow_mul,hs,zero_mul,zero_add] at hφ
  have cancel : flow a b π*u = π*(eigen*u - flow a b u) := by
    apply mul_left_cancel₀ (pow_ne_zero (2*j) hπ.ne_zero)
    linear_combination hφ
  have hd' : π ∣ flow a b π*u := ⟨_,cancel⟩
  obtain ⟨v,hv⟩ := (hπ.dvd_or_dvd hd').resolve_left hregular
  refine ⟨v,?_⟩
  rw [hu,hv,show 2*j+2=(2*j+1)+1 by omega,pow_succ]; ring

/-- The actual spatial fibre in the promoted polynomial representation. -/
theorem regular_fibre_next (F G : ContactPoly K) (x : K) (s j : ℕ)
    (hF : F.natDegree≤1) (hG : G.natDegree≤s)
    (dF : contactDeriv F=0) (dG : contactDeriv G=0)
    (hreg : ¬ C ((Polynomial.X : Polynomial K)-C x) ∣ F.coeff 1)
    (hd : C ((Polynomial.X : Polynomial K)-C x)^(2*j+1) ∣ resultant F G 1 s) :
    C ((Polynomial.X : Polynomial K)-C x)^(2*j+2) ∣ resultant F G 1 s := by
  have hp : Prime (C ((Polynomial.X : Polynomial K)-C x) : B) := Polynomial.prime_C_iff.mpr (Polynomial.prime_X_sub_C x)
  have hdx : dXBi (C ((Polynomial.X : Polynomial K)-C x) : B)=1 := by
    apply Polynomial.ext
    intro k
    by_cases hk : k=0
    · subst k; simp [coeff_dXBi]
    · simp [coeff_dXBi,coeff_C,coeff_one,hk]
  apply next_layer hp (a:=F.coeff 0) (b:=F.coeff 1) _ (resultant_flow F G s hF hG dF dG) j hd
  simpa only [flow,hdx,derivative_C,mul_one,mul_zero,add_zero] using hreg

end Parity

section WitnessRoots
variable [Field K]

/-- A polynomial with these fit and miss orders has too many roots for its
spatial cap. This applies unchanged to the originally chosen agreement set. -/
theorem zero_of_fit_and_miss {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι ↪ K)
    (fits marked : Finset ι) (P : Polynomial K) (m b : ℕ) (hb : b ≤ m)
    (hfit : ∀ i ∈ fits, (Polynomial.X-C (x i))^(2*(if i∈marked then m else m-b)) ∣ P)
    (hmiss : ∀ i ∈ marked, i∉fits → (Polynomial.X-C (x i))^(2*b) ∣ P)
    (hdeg : P.natDegree < 2*((m-b)*fits.card+b*marked.card)) : P=0 := by
  classical
  let n (i : ι) := (if i ∈ fits then 2*(m-b) else 0) + (if i ∈ marked then 2*b else 0)
  have hit (i : ι) : (Polynomial.X-C (x i))^(n i) ∣ P := by
    by_cases f : i ∈ fits
    · have hi := hfit i f
      by_cases z : i ∈ marked
      · simpa [n,f,z,show 2*(m-b)+2*b=2*m by omega] using hi
      · simpa [n,f,z] using hi
    · by_cases z : i ∈ marked
      · simpa [n,f,z] using hmiss i z f
      · simp [n,f,z]
  have hd : (∏ i : ι, (Polynomial.X-C (x i))^(n i)) ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      apply IsCoprime.pow
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr
        (sub_ne_zero.mpr (fun he => hij (x.injective he))))
    · exact fun i _ => hit i
  by_contra hP
  have hw := natDegree_le_of_dvd hd hP
  rw [natDegree_prod _ _ (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))] at hw
  simp only [natDegree_pow,natDegree_X_sub_C,mul_one] at hw
  have hsum : (∑ i : ι, n i)=fits.card*(2*(m-b))+marked.card*(2*b) := by
    simp [n,Finset.sum_add_distrib]
  rw [hsum] at hw
  nlinarith only [hw,hdeg]

end WitnessRoots

section RegularFibres
variable [CommRing K] [IsDomain K] [CharP K 2]

/-- An upper bound on the ordinate degree that does not use the number of
seed monomials or the spatial size of the coefficient field. -/
theorem resultant_ordinate_degree (F G : ContactPoly K) (s J : ℕ)
    (ha : (F.coeff 0).natDegree ≤ 5) (hb : (F.coeff 1).natDegree ≤ 4)
    (hg : ∀ j≤s, G.coeff j ≠ 0 → (G.coeff j).natDegree+j ≤ J) :
    (resultant F G 1 s).natDegree ≤ J+4*s := by
  rw [resultant_deg1_char2]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun j hj => ?_)
  dsimp only [Function.comp_apply]
  by_cases h0 : G.coeff j=0
  · simp [h0]
  · have hj' : j≤s := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
    have hg' := hg j hj' h0
    have hp : (F.coeff 0^j).natDegree ≤ j*5 := natDegree_pow_le.trans (Nat.mul_le_mul_left j ha)
    have hq : (F.coeff 1^(s-j)).natDegree ≤ (s-j)*4 := natDegree_pow_le.trans (Nat.mul_le_mul_left _ hb)
    have hm := natDegree_mul_le (p:=G.coeff j) (q:=F.coeff 0^j)
    exact natDegree_mul_le.trans (by omega)

/-- A single even slice of the resultant needs only the ordinate coefficient
interval left by its total order and ordinate degree. Work in translated
coordinates, with the spatial and ordinate centre both zero. -/
theorem regular_fibre_conditions (F G : ContactPoly K) (s m b J : ℕ)
    (hF : F.natDegree≤1) (hG : G.natDegree≤s)
    (dF : contactDeriv F=0) (dG : contactDeriv G=0)
    (hreg : ¬ C (Polynomial.X : Polynomial K) ∣ F.coeff 1)
    (hdegree : (resultant F G 1 s).natDegree ≤ J+4*s)
    (hord : ∀ i j, i+j<2*m+3*s → ((resultant F G 1 s).coeff j).coeff i = 0)
    (htest : ∀ i<b, ∀ j, 2*m+3*s ≤ 2*i+j → j≤J+4*s →
      ((resultant F G 1 s).coeff j).coeff (2*i) = 0) :
    C (Polynomial.X : Polynomial K)^(2*b) ∣ resultant F G 1 s := by
  let φ := resultant F G 1 s
  have step (i : ℕ) (hi : i<b) (ih : C (Polynomial.X : Polynomial K)^(2*i) ∣ φ) :
      C (Polynomial.X : Polynomial K)^(2*(i+1)) ∣ φ := by
    have ev (j : ℕ) : (φ.coeff j).coeff (2*i)=0 := by
      by_cases big : j>J+4*s
      · have hz := coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt big)
        simp [φ,hz]
      · by_cases low : 2*i+j<2*m+3*s
        · exact hord _ _ low
        · exact htest i hi j (by omega) (by omega)
    have middle : C (Polynomial.X : Polynomial K)^(2*i+1) ∣ φ := by
      rw [←map_pow, C_dvd_iff_dvd_coeff] at ih ⊢
      intro j
      rw [X_pow_dvd_iff]
      intro n hn
      rcases lt_or_eq_of_le (show n≤2*i by omega) with h|rfl
      · exact X_pow_dvd_iff.mp (ih j) n h
      · exact ev j
    have hz : ¬ C ((Polynomial.X : Polynomial K)-C (0:K)) ∣ F.coeff 1 := by simpa using hreg
    simpa only [map_zero,sub_zero, Nat.mul_add, Nat.mul_one] using
      regular_fibre_next F G 0 s i hF hG dF dG hz (by simpa [φ] using middle)
  have loop : ∀ j, j≤b → C (Polynomial.X : Polynomial K)^(2*j) ∣ φ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj; exact step j (by omega) (ih (by omega))
  exact loop b le_rfl

end RegularFibres

section WitnessEvaluation
variable [Field K] [CharP K 2]

omit [CharP K 2] in
private lemma evaluated_sum (G : ContactPoly K) (P : Polynomial K) (s : ℕ) (hs : G.natDegree≤s) :
    B6401QuotInterp.evalContact G P =
      ∑ j ∈ Finset.range (s+1), (G.coeff j).eval P * P.derivative^j := by
  unfold B6401QuotInterp.evalContact
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_eq_sum_range' (evalRingHom P) (Nat.lt_succ_of_le hs) P.derivative

/-- The resultant evaluated on the original witness equals the auxiliary
equation on its derivative graph, times the s-th power of the slope coefficient. -/
theorem resultant_on_witness (F G : ContactPoly K) (P : Polynomial K) (s : ℕ)
    (hF : F.natDegree≤1) (hG : G.natDegree≤s)
    (onF : B6401QuotInterp.evalContact F P=0) :
    (resultant F G 1 s).eval P =
      ((F.coeff 1).eval P)^s * B6401QuotInterp.evalContact G P := by
  rw [evaluated_sum F P 1 hF] at onF
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one] at onF
  have h0 : (F.coeff 0).eval P = (F.coeff 1).eval P*P.derivative := by
    have htwo : (2 : Polynomial K)=0 := CharP.cast_eq_zero _ 2
    linear_combination onF - ((F.coeff 1).eval P*P.derivative)*htwo
  rw [resultant_deg1_char2,evaluated_sum G P s hG,Finset.mul_sum]
  rw [←coe_evalRingHom, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [map_mul, map_pow, coe_evalRingHom, h0, mul_pow]
  have h : ((F.coeff 1).eval P)^j * ((F.coeff 1).eval P)^(s-j) = ((F.coeff 1).eval P)^s := by
    rw [←pow_add]; congr 1; have := Finset.mem_range.mp hj; omega
  linear_combination (G.coeff j).eval P * P.derivative^j * h

theorem missed_roots_of_resultant (F G : ContactPoly K) (P : Polynomial K) (x : K) (s b : ℕ)
    (hF : F.natDegree≤1) (hG : G.natDegree≤s) (onF : B6401QuotInterp.evalContact F P=0)
    (unit : IsCoprime ((Polynomial.X : Polynomial K)-C x) ((F.coeff 1).eval P))
    (hd : C ((Polynomial.X : Polynomial K)-C x)^(2*b) ∣ resultant F G 1 s) :
    ((Polynomial.X : Polynomial K)-C x)^(2*b) ∣ B6401QuotInterp.evalContact G P := by
  obtain ⟨Q,hQ⟩ := hd
  have h := congrArg (fun f : B => f.eval P) hQ
  simp only [eval_mul,eval_pow,eval_C,resultant_on_witness F G P s hF hG onF] at h
  have cop : IsCoprime (((Polynomial.X : Polynomial K)-C x)^(2*b)) (((F.coeff 1).eval P)^s) := unit.pow
  exact cop.dvd_of_dvd_mul_left ⟨_,h⟩

end WitnessEvaluation

#print axioms missed_roots_of_resultant
#print axioms regular_fibre_conditions
#print axioms zero_of_fit_and_miss
#print axioms regular_fibre_next
#print axioms resultant_flow
#print axioms next_layer
end ProximityPrize.SubmissionBinaryLower.B6402MissedFibres
