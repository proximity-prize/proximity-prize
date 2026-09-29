import ProximityPrize.SubmissionLower.CofactorOwnership6814

/-! Whole-space exclusion of the recorded simple quadratic's fixed cube.
This uses polynomial degree additivity and dimension, not independently
chosen factors for each source. Variables are X,S,Y,R,gamma.
-/
namespace ProximityPrize.SubmissionLower.WholeSpaceCube6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K]
abbrev Poly := MvPolynomial (Fin 5) K

def weightEmbed (w : Fin 5 → ℕ) : (Fin 5 →₀ ℕ) →+ (Fin 6 →₀ ℕ) where
  toFun d := Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
    Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)+Finsupp.single 4 (d 4)+
    Finsupp.single 5 (Finsupp.weight w d)
  map_zero' := by simp
  map_add' d e := by ext i; fin_cases i <;> simp [Finsupp.add_apply,map_add]

theorem weightEmbed_coord (w : Fin 5 → ℕ) (d : Fin 5 →₀ ℕ) (i : Fin 5) :
    weightEmbed w d i.castSucc = d i := by
  fin_cases i <;> simp [weightEmbed]

theorem weightEmbed_injective (w : Fin 5 → ℕ) : Function.Injective (weightEmbed w) := by
  intro d e h
  ext i
  simpa only [weightEmbed_coord] using congrArg (fun x : Fin 6 →₀ ℕ => x i.castSucc) h

def weightedLift (w : Fin 5 → ℕ) : Poly (K := K) →+* MvPolynomial (Fin 6) K :=
  AddMonoidAlgebra.mapDomainRingHom K (weightEmbed w)

theorem weightedLift_injective (w : Fin 5 → ℕ) : Function.Injective (weightedLift (K := K) w) :=
  AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective w)

theorem weightedLift_degree (w : Fin 5 → ℕ) (P : Poly (K := K)) :
    (weightedLift w P).degreeOf 5 = weightedTotalDegree w P := by
  have hs : (weightedLift w P).support = P.support.image (weightEmbed w) :=
    Finsupp.mapDomain_support_of_injective (weightEmbed_injective w) _
  rw [degreeOf_eq_sup,hs,Finset.sup_image]
  change P.support.sup (fun d => weightEmbed w d 5) = P.support.sup (Finsupp.weight w)
  congr 1
  funext d
  simp [weightEmbed]

theorem weight_mul (w : Fin 5 → ℕ) (P Q : Poly (K := K)) (hP : P≠0) (hQ : Q≠0) :
    weightedTotalDegree w (P*Q) = weightedTotalDegree w P+weightedTotalDegree w Q := by
  have hn (A : Poly (K := K)) (hA : A≠0) : weightedLift w A ≠ 0 := by
    intro hz
    apply hA
    exact weightedLift_injective w (by simpa only [map_zero] using hz)
  rw [←weightedLift_degree,map_mul,degreeOf_mul_eq (hn P hP) (hn Q hQ),
    weightedLift_degree,weightedLift_degree]

theorem weight_pow (w : Fin 5 → ℕ) (P : Poly (K := K)) (hP : P≠0) (n : ℕ) :
    weightedTotalDegree w (P^n) = n*weightedTotalDegree w P := by
  induction n with
  | zero => simp [weightedTotalDegree]
  | succ n ih =>
    rw [pow_succ,weight_mul w _ _ (pow_ne_zero _ hP) hP,ih]
    ring

def codeWeights : Fin 5 → ℕ := ![1,131069,131071,131070,0]
def middleWeights : Fin 5 → ℕ := ![0,1,1,1,0]
def totalWeights : Fin 5 → ℕ := ![0,1,1,1,1]

theorem weight_coords (w : Fin 5 → ℕ) (e : Fin 5 →₀ ℕ) :
    Finsupp.weight w e = e 0*w 0+e 1*w 1+e 2*w 2+e 3*w 3+e 4*w 4 := by
  have he : e = Finsupp.single 0 (e 0)+Finsupp.single 1 (e 1)+
      Finsupp.single 2 (e 2)+Finsupp.single 3 (e 3)+Finsupp.single 4 (e 4) := by
    ext i; fin_cases i <;> simp
  rw [he,map_add,map_add,map_add,map_add]
  simp [Finsupp.weight_single]

theorem factor_code_lower (J : Poly (K := K)) (hJ : J≠0)
    (hmid : weightedTotalDegree middleWeights J=30)
    (hB : ∀ e ∈ J.support, 2*e 1+e 3 ≤ 9) :
    3932121 ≤ weightedTotalDegree codeWeights J := by
  obtain ⟨e,he,hmax⟩ := Finset.exists_mem_eq_sup J.support (support_nonempty.mpr hJ)
    (Finsupp.weight middleWeights)
  have hm : Finsupp.weight middleWeights e=30 := hmax.symm.trans hmid
  have hc : Finsupp.weight codeWeights e ≤ weightedTotalDegree codeWeights J := Finset.le_sup he
  have hb := hB e he
  have hm' : e 1+e 2+e 3=30 := by simpa [weight_coords,middleWeights] using hm
  have hc' : e 0+131069*e 1+131071*e 2+131070*e 3 ≤ weightedTotalDegree codeWeights J := by
    simpa [weight_coords,codeWeights,Nat.mul_comm] using hc
  omega

theorem quotient_bounds (J Q : Poly (K := K)) (hJ : J≠0) (hQ : Q≠0)
    (hmid : weightedTotalDegree middleWeights J=30)
    (hB : ∀ e ∈ J.support, 2*e 1+e 3 ≤ 9)
    (ht : weightedTotalDegree totalWeights J=331)
    (hcode : weightedTotalDegree codeWeights (J^3*Q) < 13050360)
    (htotal : weightedTotalDegree totalWeights (J^3*Q) ≤ 995) :
    weightedTotalDegree codeWeights Q < 1253997 ∧
      weightedTotalDegree totalWeights Q ≤ 2 := by
  have hl := factor_code_lower J hJ hmid hB
  rw [weight_mul _ _ _ (pow_ne_zero _ hJ) hQ,weight_pow _ _ hJ] at hcode htotal
  rw [ht] at htotal
  omega

abbrev QuotientIndex := Fin 1253997 × (Fin 4 → Fin 3)

def quotientExponent (i : QuotientIndex) : Fin 5 →₀ ℕ :=
  Finsupp.cons i.1.val (Finsupp.equivFunOnFinite.symm (fun j => (i.2 j).val))

theorem quotientExponent_injective : Function.Injective quotientExponent := by
  rintro ⟨x,v⟩ ⟨y,u⟩ h
  have hxy : x=y := Fin.ext (by simpa [quotientExponent] using congrArg (fun e => e 0) h)
  have hvu : v=u := by
    funext i
    apply Fin.ext
    simpa [quotientExponent] using congrArg (fun e => e i.succ) h
  exact Prod.ext hxy hvu

theorem quotient_support (Q : Poly (K := K))
    (hcode : weightedTotalDegree codeWeights Q < 1253997)
    (htotal : weightedTotalDegree totalWeights Q ≤ 2) :
    ∀ e ∈ Q.support, e ∈ Set.range quotientExponent := by
  intro e he
  have hc := (Finset.le_sup (f := Finsupp.weight codeWeights) he).trans_lt hcode
  have ht := (Finset.le_sup (f := Finsupp.weight totalWeights) he).trans htotal
  simp [weight_coords,codeWeights,totalWeights] at hc ht
  have hx : e 0 < 1253997 := by omega
  have hrest : ∀ i : Fin 4, e i.succ < 3 := by
    intro i
    fin_cases i
    · change e 1 < 3; omega
    · change e 2 < 3; omega
    · change e 3 < 3; omega
    · change e 4 < 3; omega
  refine ⟨(⟨e 0,hx⟩,fun i => ⟨e i.succ,hrest i⟩),?_⟩
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [quotientExponent]

def cubeMultiply (J : Poly (K := K)) : Poly (K := K) →ₗ[K] Poly (K := K) where
  toFun Q := J^3*Q
  map_add' := mul_add _
  map_smul' a Q := by
    simp only [MvPolynomial.smul_eq_C_mul,RingHom.id_apply]
    ac_rfl

def cubeQuotient (V : Submodule K (Poly (K := K))) (J : Poly (K := K))
    (hdiv : ∀ v : V, J^3 ∣ v.val) (v : V) : Poly (K := K) :=
  Classical.choose (hdiv v)

theorem cubeQuotient_spec (V : Submodule K (Poly (K := K))) (J : Poly (K := K))
    (hdiv : ∀ v : V, J^3 ∣ v.val) (v : V) : v.val=J^3*cubeQuotient V J hdiv v :=
  Classical.choose_spec (hdiv v)

def cubeQuotientLinear (V : Submodule K (Poly (K := K))) (J : Poly (K := K))
    (hJ : J≠0) (hdiv : ∀ v : V, J^3 ∣ v.val) : V →ₗ[K] Poly (K := K) where
  toFun := cubeQuotient V J hdiv
  map_add' v u := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hJ)
    rw [mul_add,←cubeQuotient_spec,←cubeQuotient_spec,←cubeQuotient_spec]
    rfl
  map_smul' a v := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hJ)
    rw [←cubeQuotient_spec]
    change a • v.val=J^3*(a • cubeQuotient V J hdiv v)
    rw [cubeQuotient_spec V J hdiv v]
    simp only [MvPolynomial.smul_eq_C_mul]
    ac_rfl

theorem finrank_le_coefficients {W I : Type*} [AddCommGroup W] [Module K W]
    [Fintype I] (e : I → Fin 5 →₀ ℕ) (f : W →ₗ[K] Poly (K := K))
    (hf : Function.Injective f)
    (hs : ∀ v : W, ∀ d ∈ (f v).support, d ∈ Set.range e) :
    Module.finrank K W ≤ Fintype.card I := by
  let A : W →ₗ[K] (I → K) := LinearMap.pi (fun i => (MvPolynomial.lcoeff K (e i)).comp f)
  have hi : Function.Injective A := by
    intro v u h
    apply hf
    ext d
    have hh (i : I) : (f v).coeff (e i)=(f u).coeff (e i) := congrFun h i
    by_cases hv : d ∈ (f v).support
    · obtain ⟨i,rfl⟩ := hs v d hv
      exact hh i
    by_cases hu : d ∈ (f u).support
    · obtain ⟨i,rfl⟩ := hs u d hu
      exact hh i
    rw [MvPolynomial.notMem_support_iff.mp hv,MvPolynomial.notMem_support_iff.mp hu]
  simpa using LinearMap.finrank_le_finrank_of_injective hi

/-- The recorded quadratic cannot divide the ENTIRE small-source space
to the third power. Its support and the source dimension force a genuine
element outside that ideal, not just a new conditional counting adapter.
The dimension lower bound is the independently checked source-27 nullity;
the theorem is otherwise independent of how V was constructed. -/
theorem exists_not_dvd_cube
    (V : Submodule K (Poly (K := K))) [Module.Finite K V]
    (hdim : 101867694 ≤ Module.finrank K V)
    (hcode : ∀ P ∈ V, weightedTotalDegree codeWeights P < 13050360)
    (htotal : ∀ P ∈ V, weightedTotalDegree totalWeights P ≤ 995)
    (J : Poly (K := K)) (hJ : J≠0)
    (hmid : weightedTotalDegree middleWeights J=30)
    (hB : ∀ e ∈ J.support, 2*e 1+e 3 ≤ 9)
    (ht : weightedTotalDegree totalWeights J=331) :
    ∃ P ∈ V, ¬ J^3 ∣ P := by
  classical
  by_contra hno
  have hdiv : ∀ P ∈ V, J^3 ∣ P := by simpa only [not_exists,not_and,not_not] using hno
  let hd : ∀ v : V, J^3 ∣ v.val := fun v => hdiv v.val v.property
  let f := cubeQuotientLinear V J hJ hd
  have hf : Function.Injective f := by
    intro v u he
    apply Subtype.ext
    rw [cubeQuotient_spec V J hd v,cubeQuotient_spec V J hd u]
    exact congrArg (fun Q => J^3*Q) he
  have hs : ∀ v : V, ∀ e ∈ (f v).support, e ∈ Set.range quotientExponent := by
    intro v e he
    have hq : f v ≠ 0 := by intro hz; simpa [hz] using he
    have hv : v.val=J^3*f v := cubeQuotient_spec V J hd v
    have hb := quotient_bounds J (f v) hJ hq hmid hB ht
      (by rw [←hv]; exact hcode v.val v.property)
      (by rw [←hv]; exact htotal v.val v.property)
    exact quotient_support (f v) hb.1 hb.2 e he
  have hm := finrank_le_coefficients quotientExponent f hf hs
  have hi : Fintype.card QuotientIndex=101573757 := by simp [QuotientIndex]
  rw [hi] at hm
  omega

#print axioms weight_mul
#print axioms factor_code_lower
#print axioms quotient_bounds
#print axioms exists_not_dvd_cube
end
end ProximityPrize.SubmissionLower.WholeSpaceCube6814
