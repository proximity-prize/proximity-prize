import ProximityPrize.SubmissionLower.ColumnRank6921
import ProximityPrize.SubmissionLower.Fast003
import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast009
import ProximityPrize.SubmissionLower.Fast065
import ProximityPrize.SubmissionLower.Fast070
import ProximityPrize.SubmissionLower.Fast071
import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.Fast076
import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.Front6921
set_option Elab.async false

/- Profile transport of Dadon's PR 627. -/
section Port_K1_11CertificateArithmetic
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K21_11
open Finset

/-- Exact number of source monomials. D is an inclusive weighted bound. -/
def V (D w B s t : ℕ) : ℕ :=
  ∑ i ∈ range (B+1), ∑ j ∈ range (B+1-i),
    (D+1-w*(i+j))*(s+1-i)*(t+1-j)

/-- Truncated three-contact-variable monomial count with parameter weights. -/
def J (m s t : ℕ) : ℕ :=
  ∑ i ∈ range m, ∑ j ∈ range (m-i),
    (m-i-j)*(s+1-i)*(t+1-j)

end K21_11
end Port_K1_11CertificateArithmetic

section Port_K1_11Elimination
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K21_11
noncomputable section
open Polynomial Finset

/-- Homogeneous denominator clearing. It remains meaningful at b=0. -/
def clearedEval {R : Type*} [CommRing R] (B : ℕ) (Q : R[X]) (a b : R) : R :=
  ∑ j∈range (B+1),Q.coeff j*a^j*b^(B-j)

/-- Denominator clearing commutes with every actual root specialization,
including b=0. This is the identity needed for the SAME original decoder. -/
theorem clearedEval_at_root {R : Type*} [CommRing R]
    (B : ℕ) (Q : R[X]) (hQ : Q.natDegree≤B) (a b y : R) (hy : b*y=a) :
    clearedEval B Q a b=b^B*Q.eval y := by
  rw [eval_eq_sum_range' (show Q.natDegree<B+1 by omega),mul_sum]
  unfold clearedEval
  apply sum_congr rfl
  intro j hj
  have hjB : j≤B := by have := mem_range.mp hj; omega
  rw [← hy,mul_pow]
  have hb : b^j*b^(B-j)=b^B := by rw [← pow_add,Nat.add_sub_of_le hjB]
  calc
    Q.coeff j*(b^j*y^j)*b^(B-j) = Q.coeff j*y^j*(b^j*b^(B-j)) := by ring
    _ = b^B*(Q.coeff j*y^j) := by rw [hb]; ring

theorem clearedEval_zero_of_root {R : Type*} [CommRing R]
    (B : ℕ) (Q : R[X]) (hQ : Q.natDegree≤B) (a b y : R)
    (hy : b*y=a) (hroot : Q.eval y=0) : clearedEval B Q a b=0 := by
  rw [clearedEval_at_root B Q hQ a b y hy,hroot,mul_zero]

/-- Over a field, a nonmultiple survives linear elimination. -/
theorem clearedEval_ne_zero_field {K : Type*} [Field K]
    (B : ℕ) (Q : K[X]) (hQ : Q.natDegree≤B) (a b : K) (hb : b≠0)
    (hnot : ¬ (C b*Polynomial.X-C a) ∣ Q) : clearedEval B Q a b≠0 := by
  have heq : C b*Polynomial.X-C a=C b*(Polynomial.X-C (a/b)) := by
    rw [mul_sub,← C_mul]
    have hba : b*(a/b)=a := by field_simp
    rw [hba]
  have hroot : Q.eval (a/b)≠0 := by
    intro hz
    apply hnot
    rw [heq]
    have hd : (Polynomial.X-C (a/b))∣Q := (dvd_iff_isRoot).mpr hz
    have hu : C b ∣ (1 : K[X]) := (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb)).dvd
    simpa using mul_dvd_mul hu hd
  rw [clearedEval_at_root B Q hQ a b (a/b) (by field_simp)]
  exact mul_ne_zero (pow_ne_zero B hb) hroot

/-- The coefficient-ring map respects the cleared expression. -/
theorem map_clearedEval {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (B : ℕ) (Q : R[X]) (a b : R) :
    f (clearedEval B Q a b)=clearedEval B (Q.map f) (f a) (f b) := by
  simp [clearedEval]

/-- Primitive linear elimination over any GCD domain. Gauss transfers
nondivisibility to the fraction field. -/
theorem clearedEval_ne_zero {R K : Type*} [CommRing R] [IsDomain R]
    [IsGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : ℕ) (Q : R[X]) (hQ : Q.natDegree≤B) (a b : R) (hb : b≠0)
    (hprimitive : (C b*Polynomial.X-C a).IsPrimitive) (hnot : ¬ (C b*Polynomial.X-C a)∣Q) :
    clearedEval B Q a b≠0 := by
  have hmap : ¬ (C (algebraMap R K b)*Polynomial.X-C (algebraMap R K a))∣Q.map (algebraMap R K) := by
    simpa only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X] using
      (not_congr (hprimitive.dvd_iff_fraction_map_dvd_fraction_map K)).mp hnot
  have hdeg : (Q.map (algebraMap R K)).natDegree≤B := (natDegree_map_le).trans hQ
  have hb' : algebraMap R K b≠0 := by simpa using (IsFractionRing.injective R K).ne hb
  have hn := clearedEval_ne_zero_field B (Q.map (algebraMap R K)) hdeg
    (algebraMap R K a) (algebraMap R K b) hb' hmap
  rw [← map_clearedEval] at hn
  exact fun hz => hn (by rw [hz,map_zero])

end
end K21_11
end Port_K1_11Elimination

section Port_K1_11_3Multiplicity
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K21_11_3
noncomputable section
open Polynomial

/-- Multiple roots after SPECIALIZATION are assigned to one of at most B
ordinary Y derivatives. Generic squarefreeness is unnecessary. -/
theorem exists_simple_derivative_at_root {R : Type*} [CommRing R] [IsDomain R]
    (p B : ℕ) [CharP R p] (f : R[X]) (hf : f≠0) (hdegree : f.natDegree≤B)
    (hsmall : B<p) (y : R) (hroot : f.IsRoot y) :
    ∃ j<B,(derivative^[j] f).IsRoot y ∧ ¬(derivative (derivative^[j] f)).IsRoot y := by
  let μ := f.rootMultiplicity y
  have hμpos : 0<μ := (rootMultiplicity_pos hf).mpr hroot
  have hμle : μ≤B := by
    have hd := natDegree_le_of_dvd (f.pow_rootMultiplicity_dvd y) hf
    have hle : μ≤f.natDegree := by simpa [μ,natDegree_pow] using hd
    exact hle.trans hdegree
  have hnzd : ∀ m≤μ,m≠0 → (m : R)∈nonZeroDivisors R := by
    intro m hm hmn
    apply mem_nonZeroDivisors_of_ne_zero
    intro hz
    have hd : p∣m := (CharP.cast_eq_zero_iff R p m).mp hz
    have hp : p≤m := Nat.le_of_dvd (Nat.pos_of_ne_zero hmn) hd
    omega
  have hnext : ¬(derivative^[μ] f).IsRoot y := by
    intro hnext
    have hall : ∀ m≤μ,(derivative^[m] f).IsRoot y := by
      intro m hm
      rcases lt_or_eq_of_le hm with hh | rfl
      · exact isRoot_iterate_derivative_of_lt_rootMultiplicity hh
      · exact hnext
    have hc := lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' hf hall hnzd
    exact (Nat.lt_irrefl μ) hc
  refine ⟨μ-1,by omega,isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega),?_⟩
  have he : derivative (derivative^[μ-1] f)=derivative^[μ] f := by
    simpa only [Nat.succ_eq_add_one,Nat.sub_add_cancel hμpos] using (Function.iterate_succ_apply' derivative (μ-1) f).symm
  rwa [he]

end
end K21_11_3
end Port_K1_11_3Multiplicity

section Port_K1_11ContactOrder
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K21_11
noncomputable section
open MvPolynomial
variable {F σ : Type*} [Field F]

def contactExponent (v : σ → ℕ) : (σ →₀ ℕ) →+ (Option σ →₀ ℕ) where
  toFun e := e.optionElim (e.weight v)
  map_zero' := by ext i; cases i <;> simp
  map_add' e f := by ext i; cases i <;> simp

theorem contactExponent_injective (v : σ → ℕ) : Function.Injective (contactExponent v) := by
  intro e f h
  have := congrArg Finsupp.some h
  simpa [contactExponent] using this

/-- Insert a formal contact scale and retain every original monomial.
Unlike numeric specialization, this embedding cannot cancel leading jets. -/
def contactLift (v : σ → ℕ) : MvPolynomial σ F →+* Polynomial (MvPolynomial σ F) :=
  (optionEquivLeft F σ).toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom F (contactExponent v))

theorem contactLift_injective (v : σ → ℕ) : Function.Injective (contactLift (F:=F) v) :=
  (optionEquivLeft F σ).injective.comp
    (AddMonoidAlgebra.mapDomain_injective (contactExponent_injective v))

theorem contactLift_monomial (v : σ → ℕ) (e : σ →₀ ℕ) (a : F) :
    contactLift v (monomial e a)=Polynomial.monomial (e.weight v) (monomial e a) := by
  change (optionEquivLeft F σ) (AddMonoidAlgebra.mapDomain (contactExponent v) (monomial e a))=_
  change (optionEquivLeft F σ) (AddMonoidAlgebra.mapDomain (contactExponent v) (AddMonoidAlgebra.single e a))=_
  rw [AddMonoidAlgebra.mapDomain_single]
  change (optionEquivLeft F σ) (monomial ((contactExponent v) e) a)=_
  rw [optionEquivLeft_monomial]
  simp [contactExponent]

theorem contactLift_coeff (v : σ → ℕ) (P : MvPolynomial σ F) (n : ℕ) (e : σ →₀ ℕ) :
    ((contactLift v P).coeff n).coeff e=if e.weight v=n then P.coeff e else 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial f a =>
    rw [contactLift_monomial]
    by_cases hfe : f=e
    · subst f
      split_ifs <;> simp_all [Polynomial.coeff_monomial]
    · by_cases hw : f.weight v=n <;> by_cases he : e.weight v=n <;> simp [Polynomial.coeff_monomial,MvPolynomial.coeff_monomial,hfe,Ne.symm hfe,hw,he]
  | add P Q hP hQ =>
    simp only [map_add,Polynomial.coeff_add,MvPolynomial.coeff_add,hP,hQ]
    split_ifs <;> simp

/-- Actual order filtration is exactly divisibility by the scale variable. -/
theorem contactLift_X_pow_dvd_iff (v : σ → ℕ) (m : ℕ) (P : MvPolynomial σ F) :
    Polynomial.X^m ∣ contactLift v P ↔ P∈restrictWeightedOrder v m := by
  rw [Polynomial.X_pow_dvd_iff,mem_restrictWeightedOrder]
  constructor
  · intro h e he
    by_contra hh
    have hc := congrArg (fun Q : MvPolynomial σ F => Q.coeff e) (h (e.weight v) (by omega))
    rw [contactLift_coeff,if_pos rfl] at hc
    exact (mem_support_iff.mp he) hc
  · intro h n hn
    ext e
    rw [contactLift_coeff]
    by_cases he : e.weight v=n
    · rw [if_pos he]
      by_contra hc
      have := h e (mem_support_iff.mpr hc)
      omega
    · simp [he]

/-- Exact first order follows from vanishing contact constant and one
nonzero linear contact coefficient; parameter coefficients remain intact. -/
theorem contact_order_one_of_coefficient (v : σ → ℕ) (L : MvPolynomial σ F)
    (horder : L∈restrictWeightedOrder v 1) (e : σ →₀ ℕ)
    (he : e.weight v=1) (hc : L.coeff e≠0) :
    (contactLift v L).natTrailingDegree=1 := by
  have hLn : L≠0 := by intro hz; exact hc (by rw [hz]; rfl)
  have hLn' : contactLift v L≠0 := fun hz => hLn (contactLift_injective v (hz.trans (map_zero _).symm))
  have hlow := Polynomial.le_natTrailingDegree hLn'
    (Polynomial.X_pow_dvd_iff.mp ((contactLift_X_pow_dvd_iff v 1 L).mpr horder))
  have hc' : (contactLift v L).coeff 1≠0 := by
    intro hz
    have hh := congrArg (fun P : MvPolynomial σ F => P.coeff e) hz
    rw [contactLift_coeff,if_pos he] at hh
    exact hc hh
  have hup := Polynomial.natTrailingDegree_le_of_ne_zero hc'
  omega

/-- If L has exact contact order one, truncated multiplication by L
injects jets of contact degree below m-1 into jets below m. This theorem
keeps the full coefficient polynomial ring, so parameter zeros are harmless. -/
theorem contact_product_not_high_order (v : σ → ℕ) (m : ℕ)
    (L H : MvPolynomial σ F)
    (hL : (contactLift v L).natTrailingDegree=1) (hLn : L≠0)
    (hH : H≠0) (hHlow : ∀ e∈H.support,e.weight v<m-1) :
    L*H ∉ restrictWeightedOrder v m := by
  intro hh
  have hLn' : contactLift v L≠0 := fun hz => hLn (contactLift_injective v (hz.trans (map_zero _).symm))
  have hHn' : contactLift v H≠0 := fun hz => hH (contactLift_injective v (hz.trans (map_zero _).symm))
  have hmul : contactLift v (L*H)≠0 := by rw [map_mul]; exact mul_ne_zero hLn' hHn'
  have hhigh := Polynomial.le_natTrailingDegree hmul
    (Polynomial.X_pow_dvd_iff.mp ((contactLift_X_pow_dvd_iff v m (L*H)).mpr hh))
  rw [map_mul,Polynomial.natTrailingDegree_mul hLn' hHn',hL] at hhigh
  obtain ⟨e,he⟩ := support_nonempty.mpr hH
  have hc : (contactLift v H).coeff (e.weight v)≠0 := by
    intro hz
    have hz' := congrArg (fun Q : MvPolynomial σ F => Q.coeff e) hz
    rw [contactLift_coeff,if_pos rfl] at hz'
    exact (mem_support_iff.mp he) hz'
  have hmin := Polynomial.natTrailingDegree_le_of_ne_zero hc
  have := hHlow e he
  omega

end
end K21_11
end Port_K1_11ContactOrder

section Port_K1_11FilteredQuotient
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K21_11
noncomputable section
open MvPolynomial
variable {F σ ι : Type*} [Field F]

/-- Simultaneous polynomial filtrations; none of the weights must be positive. -/
def filtered (v : ι → σ → ℕ) (d : ι → ℕ) : Submodule F (MvPolynomial σ F) :=
  ⨅ i, restrictWeightedDegree (v i) (d i)

@[simp] theorem mem_filtered (v : ι → σ → ℕ) (d : ι → ℕ) (P : MvPolynomial σ F) :
    P ∈ filtered v d ↔ ∀ i, P.weightedTotalDegree (v i) ≤ d i := by
  simp only [filtered, Submodule.mem_iInf, mem_restrictWeightedDegree_iff_weightedTotalDegree_le]

/-- Exact subtraction for ALL multiples, with the zero multiplier included. -/
theorem mul_mem_filtered_iff (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L H : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i, L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i) :
    L*H ∈ filtered v d ↔ H ∈ filtered v (fun i => d i-e i) := by
  by_cases hH : H=0
  · simp [hH]
  · simp only [mem_filtered]
    constructor
    · intro h i
      have hi := h i
      rw [weightedTotalDegree_mul _ _ _ hL hH,hdeg i] at hi
      omega
    · intro h i
      have hi := h i
      rw [weightedTotalDegree_mul _ _ _ hL hH,hdeg i]
      have := hed i
      omega

/-- Multiplication into the bounded source space. -/
def filteredMul (v : ι → σ → ℕ) (d e : ι → ℕ) (L : MvPolynomial σ F)
    (hL : L≠0) (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i)
    (hed : ∀ i,e i≤d i) :
    filtered (F:=F) v (fun i => d i-e i) →ₗ[F] filtered (F:=F) v d where
  toFun H := ⟨L*H.val,(mul_mem_filtered_iff v d e L H.val hL hdeg hed).mpr H.property⟩
  map_add' H J := by apply Subtype.ext; exact mul_add L H.val J.val
  map_smul' a H := by apply Subtype.ext; exact mul_smul_comm a L H.val

theorem filteredMul_injective (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i) :
    Function.Injective (filteredMul v d e L hL hdeg hed) := by
  intro H J heq
  apply Subtype.ext
  exact mul_left_cancel₀ hL (congrArg Subtype.val heq)

/-- The range consists of exactly the source polynomials divisible by L. -/
theorem mem_filteredMul_range_iff (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i)
    (Q : filtered (F:=F) v d) :
    Q ∈ LinearMap.range (filteredMul v d e L hL hdeg hed) ↔ L ∣ Q.val := by
  constructor
  · rintro ⟨H,hH⟩
    exact ⟨H.val,congrArg Subtype.val hH.symm⟩
  · rintro ⟨H,hH⟩
    have hm : H ∈ filtered v (fun i => d i-e i) :=
      (mul_mem_filtered_iff v d e L H hL hdeg hed).mp (hH ▸ Q.property)
    exact ⟨⟨H,hm⟩,Subtype.ext hH.symm⟩

/-- Dimension of the quotient by ALL polynomial multiples of L. The two
finite source dimensions may be supplied by any monomial enumeration. -/
theorem filtered_quotient_finrank (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i)
    [Module.Finite F (filtered (F:=F) v d)] :
    Module.finrank F ((filtered (F:=F) v d) ⧸
      LinearMap.range (filteredMul v d e L hL hdeg hed)) =
    Module.finrank F (filtered (F:=F) v d) -
      Module.finrank F (filtered (F:=F) v (fun i => d i-e i)) := by
  have hr := LinearMap.finrank_range_of_inj (filteredMul_injective v d e L hL hdeg hed)
  have hq := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (filteredMul v d e L hL hdeg hed))
  omega

end
end K21_11
end Port_K1_11FilteredQuotient

section Port_K1_11SourceBox
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K21_11
noncomputable section
open Finset MvPolynomial

/-- Variable order X,Y0,Y1,S,T. -/
def sourceWeights (w : ℕ) : Fin 4 → Fin 5 → ℕ :=
  ![![1,w,w,0,0], ![0,1,1,0,0], ![0,1,0,1,0], ![0,0,1,0,1]]
def sourceBounds (D B s t : ℕ) : Fin 4 → ℕ := ![D,B,s,t]

def tuples (D w B s t : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ × ℕ × ℕ) :=
  (range (B+1)).sigma fun i => (range (B+1-i)).sigma fun j =>
    (range (D+1-w*(i+j))) ×ˢ ((range (s+1-i)) ×ˢ (range (t+1-j)))

def exponent5 (x i j a b : ℕ) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![x,i,j,a,b]

def tupleExponent (c : Σ _ : ℕ, Σ _ : ℕ, ℕ × ℕ × ℕ) : Fin 5 →₀ ℕ :=
  exponent5 c.2.2.1 c.1 c.2.1 c.2.2.2.1 c.2.2.2.2

@[simp] theorem exponent5_apply (x i j a b : ℕ) (q : Fin 5) :
    exponent5 x i j a b q = ![x,i,j,a,b] q := by
  simp [exponent5]

theorem tupleExponent_injective : Function.Injective tupleExponent := by
  intro c d h
  have h0 := congrArg (fun e : Fin 5 →₀ ℕ => e 0) h
  have h1 := congrArg (fun e : Fin 5 →₀ ℕ => e 1) h
  have h2 := congrArg (fun e : Fin 5 →₀ ℕ => e 2) h
  have h3 := congrArg (fun e : Fin 5 →₀ ℕ => e 3) h
  have h4 := congrArg (fun e : Fin 5 →₀ ℕ => e 4) h
  simp only [tupleExponent,exponent5_apply,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons] at h0 h1 h2 h3 h4
  rcases c with ⟨i,j,x,a,b⟩
  rcases d with ⟨i',j',x',a',b'⟩
  dsimp at h0 h1 h2 h3 h4
  subst i'; subst j'; subst x'; subst a'; subst b'
  rfl

@[simp] theorem tuples_card (D w B s t : ℕ) : (tuples D w B s t).card=V D w B s t := by
  simp [tuples,V,card_sigma,Nat.mul_assoc]

def sourceExponents (D w B s t : ℕ) : Finset (Fin 5 →₀ ℕ) :=
  (tuples D w B s t).image tupleExponent

theorem sourceExponents_card (D w B s t : ℕ) :
    (sourceExponents D w B s t).card=V D w B s t := by
  rw [sourceExponents,card_image_of_injective _ tupleExponent_injective,tuples_card]

theorem weight5 (e : Fin 5 →₀ ℕ) (a b c d f : ℕ) :
    e.weight ![a,b,c,d,f]=e 0*a+e 1*b+e 2*c+e 3*d+e 4*f := by
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  omega

/-- Exact membership of the finite exponent box, without any positivity
assumption on D-w*B or on s-B/t-B. -/
theorem mem_sourceExponents (D w B s t : ℕ) (e : Fin 5 →₀ ℕ) :
    e∈sourceExponents D w B s t ↔
    e 0+w*(e 1+e 2)≤D ∧ e 1+e 2≤B ∧ e 1+e 3≤s ∧ e 2+e 4≤t := by
  constructor
  · rintro he
    obtain ⟨⟨i,j,x,a,b⟩,hc,rfl⟩ := mem_image.mp he
    simp only [tuples,mem_sigma,mem_range,mem_product] at hc
    simp [tupleExponent]
    omega
  · rintro ⟨hX,hY,hS,hT⟩
    apply mem_image.mpr
    refine ⟨⟨e 1,e 2,e 0,e 3,e 4⟩,?_,?_⟩
    · simp only [tuples,mem_sigma,mem_range,mem_product]
      omega
    · ext q
      fin_cases q <;> simp [tupleExponent]

/-- The four simultaneous filtrations are literally this finite
monomial coefficient space. -/
theorem source_filtered_eq {F : Type*} [Field F] (D w B s t : ℕ) :
    filtered (F:=F) (sourceWeights w) (sourceBounds D B s t)=
      restrictSupport F (↑(sourceExponents D w B s t) : Set (Fin 5 →₀ ℕ)) := by
  ext P
  rw [mem_filtered]
  simp only [mem_restrictSupport_iff,Finset.mem_coe]
  constructor
  · intro h e he
    apply (mem_sourceExponents D w B s t e).mpr
    have hh q := (le_weightedTotalDegree (sourceWeights w q) he).trans (h q)
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    have h3 := hh 3
    simp [sourceWeights,sourceBounds,weight5] at h0 h1 h2 h3
    constructor
    · nlinarith
    · exact ⟨h1,h2,h3⟩
  · intro h q
    apply Finset.sup_le
    change ∀ e∈P.support, _
    intro e he
    have hh := (mem_sourceExponents D w B s t e).mp (h he)
    fin_cases q <;> simp [sourceWeights,sourceBounds,weight5] <;> nlinarith

instance source_filtered_finite {F : Type*} [Field F] (D w B s t : ℕ) :
    Module.Finite F (filtered (F:=F) (sourceWeights w) (sourceBounds D B s t)) := by
  rw [source_filtered_eq]
  exact restrictSupport_finite (Finset.finite_toSet _)

theorem source_filtered_finrank {F : Type*} [Field F] (D w B s t : ℕ) :
    Module.finrank F (filtered (F:=F) (sourceWeights w) (sourceBounds D B s t))=
      V D w B s t := by
  rw [source_filtered_eq,finrank_restrictSupport_finset,sourceExponents_card]

end
end K21_11
end Port_K1_11SourceBox

section Port_K1_11EliminationDegrees
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K21_11
noncomputable section
open Finset MvPolynomial
variable {F σ : Type*} [Field F]

/-- Weighted denominator-clearing bound. The coefficient condition is
additive, avoiding an invalid truncated subtraction when j*e>d. -/
theorem clearedEval_weight_bound (v : σ → ℕ) (B d e aa bb : ℕ)
    (Q : Polynomial (MvPolynomial σ F)) (a b : MvPolynomial σ F)
    (hcoeff : ∀ j≤B,Q.coeff j≠0 → (Q.coeff j).weightedTotalDegree v+j*e≤d)
    (ha : a.weightedTotalDegree v≤aa) (hb : b.weightedTotalDegree v≤bb)
    (hbalance : aa≤e+bb) :
    (clearedEval B Q a b).weightedTotalDegree v≤d+B*bb := by
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  unfold clearedEval
  apply Submodule.sum_mem
  intro j hj
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  by_cases hc : Q.coeff j=0
  · simp [hc,weightedTotalDegree]
  have hjB : j≤B := by have := mem_range.mp hj; omega
  have hco := hcoeff j hjB hc
  have hpa := (weightedTotalDegree_pow_le v a j).trans (Nat.mul_le_mul_left j ha)
  have hpb := (weightedTotalDegree_pow_le v b (B-j)).trans (Nat.mul_le_mul_left (B-j) hb)
  have hm := (weightedTotalDegree_mul_le v (Q.coeff j*a^j) (b^(B-j))).trans
    (Nat.add_le_add ((weightedTotalDegree_mul_le v _ _).trans (Nat.add_le_add_left hpa _)) hpb)
  have hjadd : j+(B-j)=B := Nat.add_sub_of_le hjB
  have hbal := Nat.mul_le_mul_left j hbalance
  nlinarith

end
end K21_11
end Port_K1_11EliminationDegrees

section Port_K1_11PolynomialView
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K21_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]

/-- Old X,Y0,Y1,S,T become Y1,X,Y0,S,T before peeling the first variable. -/
def decoderPermutation : Fin 5 ≃ Fin 5 :=
  Equiv.ofBijective ![1,2,0,3,4] (by decide)

def polynomialView : MvPolynomial (Fin 5) F ≃ₐ[F] Polynomial (MvPolynomial (Fin 4) F) :=
  (renameEquiv F decoderPermutation).trans (finSuccEquiv F 4)

def scalarWeightY : Fin 4 → ℕ := ![0,1,0,0]
def scalarWeightYS : Fin 4 → ℕ := ![0,1,1,0]
def scalarWeightT : Fin 4 → ℕ := ![0,0,0,1]

/-- A coefficient monomial of the peeled polynomial comes from an actual
source monomial, with ALL original coordinates identified. -/
theorem polynomialView_coeff_support (Q : MvPolynomial (Fin 5) F) (j : ℕ)
    (f : Fin 4 →₀ ℕ) (hf : f∈((polynomialView Q).coeff j).support) :
    ∃ e∈Q.support,e 0=f 0 ∧ e 1=f 1 ∧ e 2=j ∧ e 3=f 2 ∧ e 4=f 3 := by
  have hc := mem_support_iff.mp hf
  change ((finSuccEquiv F 4 (rename decoderPermutation Q)).coeff j).coeff f≠0 at hc
  rw [finSuccEquiv_coeff_coeff] at hc
  obtain ⟨e,he,hcoeff⟩ := coeff_rename_ne_zero decoderPermutation Q (f.cons j) hc
  refine ⟨e,mem_support_iff.mpr hcoeff,?_⟩
  have hh (i : Fin 5) := congrArg (fun z : Fin 5 →₀ ℕ => z (decoderPermutation i)) he
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have h4 := hh 4
  simp only [Finsupp.mapDomain_apply_of_injective decoderPermutation.injective] at h0 h1 h2 h3 h4
  simp [decoderPermutation] at h0 h1 h2 h3 h4
  exact ⟨h0,h1,h2,h3,h4⟩

/-- A nonzero polynomial with every weighted monomial plus a fixed charge
bounded has its maximum weighted degree plus that same charge bounded. -/
theorem weighted_degree_plus_le {σ : Type*} (v : σ → ℕ) (P : MvPolynomial σ F)
    (c d : ℕ) (hP : P≠0) (h : ∀ e∈P.support,e.weight v+c≤d) :
    P.weightedTotalDegree v+c≤d := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hP
  have hcd : c≤d := by have := h e he; omega
  have hdeg : P.weightedTotalDegree v≤d-c := by
    apply Finset.sup_le
    intro e he
    have := h e he
    omega
  omega

/-- The actual five-variable filtered source gives all three coefficient
bounds required by the scalar elimination theorem. -/
theorem polynomialView_source_coefficients (D w B s t : ℕ)
    (Q : MvPolynomial (Fin 5) F)
    (hQ : Q∈filtered (sourceWeights w) (sourceBounds D B s t)) :
    (∀ j≤B,(polynomialView Q).coeff j≠0 →
      ((polynomialView Q).coeff j).weightedTotalDegree scalarWeightY+j≤B) ∧
    (∀ j≤B,(polynomialView Q).coeff j≠0 →
      ((polynomialView Q).coeff j).weightedTotalDegree scalarWeightYS≤s) ∧
    (∀ j≤B,(polynomialView Q).coeff j≠0 →
      ((polynomialView Q).coeff j).weightedTotalDegree scalarWeightT+j≤t) := by
  have hmono (j : ℕ) (f : Fin 4 →₀ ℕ) (hf : f∈((polynomialView Q).coeff j).support) :
      f 1+j≤B ∧ f 1+f 2≤s ∧ j+f 3≤t := by
    obtain ⟨e,he,he0,he1,he2,he3,he4⟩ := polynomialView_coeff_support Q j f hf
    rw [source_filtered_eq,mem_restrictSupport_iff] at hQ
    have hh := (mem_sourceExponents D w B s t e).mp (hQ he)
    omega
  constructor
  · intro j hj hc
    apply weighted_degree_plus_le scalarWeightY _ j B hc
    intro f hf
    have hh := hmono j f hf
    simpa [scalarWeightY,Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul] using hh.1
  constructor
  · intro j hj hc
    apply Finset.sup_le
    intro f hf
    have hh := hmono j f hf
    simpa [scalarWeightYS,Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul] using hh.2.1
  · intro j hj hc
    apply weighted_degree_plus_le scalarWeightT _ j t hc
    intro f hf
    have hh := hmono j f hf
    simpa [scalarWeightT,Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul,Nat.add_comm] using hh.2.2

theorem polynomialView_natDegree (D w B s t : ℕ) (Q : MvPolynomial (Fin 5) F)
    (hQ : Q∈filtered (sourceWeights w) (sourceBounds D B s t)) :
    (polynomialView Q).natDegree≤B := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hc
  obtain ⟨f,hf⟩ := support_nonempty.mpr hc
  obtain ⟨e,he,he0,he1,he2,he3,he4⟩ := polynomialView_coeff_support Q j f hf
  rw [source_filtered_eq,mem_restrictSupport_iff] at hQ
  have hh := (mem_sourceExponents D w B s t e).mp (hQ he)
  omega

theorem polynomialView_X (i : Fin 5) :
    polynomialView (F:=F) (MvPolynomial.X i)=
      ![Polynomial.C (MvPolynomial.X 0),Polynomial.C (MvPolynomial.X 1),Polynomial.X,
        Polynomial.C (MvPolynomial.X 2),Polynomial.C (MvPolynomial.X 3)] i := by
  fin_cases i <;> simp [polynomialView,decoderPermutation,finSuccEquiv_apply,renameEquiv_apply] <;> rfl

def scalarImages (P : Polynomial F) (s t : F) : Fin 4 → Polynomial F :=
  ![Polynomial.X,P,Polynomial.C s,Polynomial.C t]

theorem polynomialView_eval (P Q : Polynomial F) (s t : F) (G : MvPolynomial (Fin 5) F) :
    Polynomial.eval₂ (aeval (scalarImages P s t)).toRingHom Q (polynomialView G)=
      aeval ![Polynomial.X,P,Q,Polynomial.C s,Polynomial.C t] G := by
  have heq : (Polynomial.eval₂RingHom (aeval (scalarImages P s t)).toRingHom Q).comp
      (polynomialView (F:=F)).toRingHom=(aeval ![Polynomial.X,P,Q,Polynomial.C s,Polynomial.C t]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [polynomialView,finSuccEquiv_apply]
    · intro i
      change Polynomial.eval₂ (aeval (scalarImages P s t)).toRingHom Q (polynomialView (MvPolynomial.X i))=_
      rw [polynomialView_X]
      fin_cases i <;> simp [scalarImages]
  exact RingHom.congr_fun heq G

end
end K21_11
end Port_K1_11PolynomialView

section Port_K1_11ContactJets
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K21_11
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]

def contactWeight : Fin 5 → ℕ := ![1,1,1,0,0]

abbrev JetSpace (F : Type*) [Field F] (d s t : ℕ) :=
  filtered (F:=F) (sourceWeights 1) (sourceBounds d d s t)

theorem J_eq_V (d s t : ℕ) : J (d+1) s t=V d 1 d s t := by
  unfold J V
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  simp only [one_mul,Nat.sub_sub]

theorem jetSpace_finrank (d s t : ℕ) :
    Module.finrank F (JetSpace F d s t)=J (d+1) s t := by
  rw [J_eq_V]
  exact source_filtered_finrank d 1 d s t

theorem jetSpace_support_bound (d s t : ℕ) (H : JetSpace F d s t) :
    ∀ e∈H.val.support,e.weight contactWeight<d+1 := by
  intro e he
  have hh := (le_weightedTotalDegree (sourceWeights 1 0) he).trans
    ((mem_filtered _ _ _).mp H.property 0)
  simpa [sourceWeights,sourceBounds,contactWeight] using Nat.lt_succ_of_le hh

/-- Truncation cannot increase either parameter filtration; its contact
support lies strictly below d+2. -/
theorem truncated_mul_mem_jet (d s t dS dT : ℕ) (L : MvPolynomial (Fin 5) F)
    (hS : L.weightedTotalDegree (sourceWeights 1 2)≤dS)
    (hT : L.weightedTotalDegree (sourceWeights 1 3)≤dT)
    (H : JetSpace F d s t) :
    weightedTruncation contactWeight (d+2) (L*H.val) ∈ JetSpace F (d+1) (s+dS) (t+dT) := by
  simp only [JetSpace]
  rw [source_filtered_eq,mem_restrictSupport_iff]
  intro e he
  have hc : e.weight contactWeight<d+2 := by
    have he' := mem_support_iff.mp he
    rw [coeff_weightedTruncation] at he'
    by_contra hh
    exact he' (if_neg hh)
  have heL : e∈(L*H.val).support := by
    apply mem_support_iff.mpr
    have := mem_support_iff.mp he
    simpa only [coeff_weightedTruncation,if_pos hc] using this
  have hHs := (mem_filtered _ _ _).mp H.property 2
  have hHt := (mem_filtered _ _ _).mp H.property 3
  have hs := (le_weightedTotalDegree (sourceWeights 1 2) heL).trans
    ((weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add hS hHs))
  have ht := (le_weightedTotalDegree (sourceWeights 1 3) heL).trans
    ((weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add hT hHt))
  apply (mem_sourceExponents (d+1) 1 (d+1) (s+dS) (t+dT) e).mpr
  simp [sourceWeights,sourceBounds,contactWeight,weight5] at hc hs ht ⊢
  omega

end
end K21_11
end Port_K1_11ContactJets

section Port_K1_11ContactShift
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K21_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]

def shiftImages (x a b c d : F) : Fin 5 → MvPolynomial (Fin 5) F :=
  ![MvPolynomial.X 0+C x,MvPolynomial.X 1+C a+MvPolynomial.X 3*C b,MvPolynomial.X 2+C c+MvPolynomial.X 4*C d,MvPolynomial.X 3,MvPolynomial.X 4]

def contactShift (x a b c d : F) : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval (shiftImages x a b c d)

theorem contactShift_mul (x a b c d : F) (P Q : MvPolynomial (Fin 5) F) :
    contactShift x a b c d (P*Q)=contactShift x a b c d P*contactShift x a b c d Q :=
  map_mul _ _ _

theorem shift_preserves_weight (v : Fin 5 → ℕ) (hv1 : v 1=v 3) (hv2 : v 2=v 4)
    (x a b c d : F) (P : MvPolynomial (Fin 5) F) :
    (contactShift x a b c d P).weightedTotalDegree v≤P.weightedTotalDegree v := by
  apply weightedTotalDegree_aeval_le_of_le v v
  intro i
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  fin_cases i
  · change MvPolynomial.X 0+C x∈restrictWeightedDegree v (v 0)
    exact Submodule.add_mem _ (X_mem_restrictWeightedDegree v _ _ le_rfl)
      (C_mem_restrictWeightedDegree v _ _)
  · change MvPolynomial.X 1+C a+MvPolynomial.X 3*C b∈restrictWeightedDegree v (v 1)
    apply Submodule.add_mem _
      (Submodule.add_mem _ (X_mem_restrictWeightedDegree v _ _ le_rfl)
        (C_mem_restrictWeightedDegree v _ _))
    have hm := mul_mem_restrictWeightedDegree
      (X_mem_restrictWeightedDegree (R:=F) v (v 3) 3 le_rfl)
      (C_mem_restrictWeightedDegree (R:=F) v 0 b)
    simpa [hv1] using hm
  · change MvPolynomial.X 2+C c+MvPolynomial.X 4*C d∈restrictWeightedDegree v (v 2)
    apply Submodule.add_mem _
      (Submodule.add_mem _ (X_mem_restrictWeightedDegree v _ _ le_rfl)
        (C_mem_restrictWeightedDegree v _ _))
    have hm := mul_mem_restrictWeightedDegree
      (X_mem_restrictWeightedDegree (R:=F) v (v 4) 4 le_rfl)
      (C_mem_restrictWeightedDegree (R:=F) v 0 d)
    simpa [hv2] using hm
  · change MvPolynomial.X 3∈restrictWeightedDegree v (v 3)
    exact X_mem_restrictWeightedDegree v _ _ le_rfl
  · change MvPolynomial.X 4∈restrictWeightedDegree v (v 4)
    exact X_mem_restrictWeightedDegree v _ _ le_rfl

/-- Both original parameter filtrations survive affine contact translation. -/
theorem contactShift_parameter_weights (x a b c d : F) (P : MvPolynomial (Fin 5) F) :
    (contactShift x a b c d P).weightedTotalDegree (sourceWeights 1 2)≤
      P.weightedTotalDegree (sourceWeights 1 2) ∧
    (contactShift x a b c d P).weightedTotalDegree (sourceWeights 1 3)≤
      P.weightedTotalDegree (sourceWeights 1 3) := by
  constructor <;> apply shift_preserves_weight <;> decide

/-- Truncate ANY polynomial with bounded parameter weights to the finite
contact jet space. No bound on its full contact degree is needed. -/
theorem trunc_mem_jet_of_parameters (d s t : ℕ) (P : MvPolynomial (Fin 5) F)
    (hS : P.weightedTotalDegree (sourceWeights 1 2)≤s)
    (hT : P.weightedTotalDegree (sourceWeights 1 3)≤t) :
    weightedTruncation contactWeight (d+1) P∈JetSpace F d s t := by
  simp only [JetSpace]
  rw [source_filtered_eq,mem_restrictSupport_iff]
  intro e he
  have hc : e.weight contactWeight<d+1 := by
    have hh := mem_support_iff.mp he
    rw [coeff_weightedTruncation] at hh
    by_contra hn
    exact hh (if_neg hn)
  have heP : e∈P.support := by
    apply mem_support_iff.mpr
    have := mem_support_iff.mp he
    simpa only [coeff_weightedTruncation,if_pos hc] using this
  have hs := (le_weightedTotalDegree (sourceWeights 1 2) heP).trans hS
  have ht := (le_weightedTotalDegree (sourceWeights 1 3) heP).trans hT
  apply (mem_sourceExponents d 1 d s t e).mpr
  simp [sourceWeights,contactWeight,weight5] at hc hs ht ⊢
  omega

def sourceToJet (D w B s t d : ℕ) (x a b c e : F) :
    filtered (F:=F) (sourceWeights w) (sourceBounds D B s t) →ₗ[F] JetSpace F d s t where
  toFun Q := ⟨weightedTruncation contactWeight (d+1) (contactShift x a b c e Q.val),by
    apply trunc_mem_jet_of_parameters
    · exact (contactShift_parameter_weights x a b c e Q.val).1.trans
        ((mem_filtered _ _ _).mp Q.property 2)
    · exact (contactShift_parameter_weights x a b c e Q.val).2.trans
        ((mem_filtered _ _ _).mp Q.property 3)⟩
  map_add' Q R := by apply Subtype.ext; simp
  map_smul' a Q := by apply Subtype.ext; simp

end
end K21_11
end Port_K1_11ContactShift

section Port_K1_11ContactMembership
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K21_11
noncomputable section
open MvPolynomial Polynomial
variable {F : Type*} [Field F]

/-- Contact modulo L pulls back to ordinary polynomial multiplicity whenever
L vanishes and the three contact coordinates vanish to first order. The
parameter coordinates have weight zero, so their values need not be units. -/
theorem contact_mod_relation_pullback {σ : Type*} (v : σ → ℕ) (m : ℕ)
    (P L H : MvPolynomial σ F) (g : σ → F[X]) (z : F[X])
    (hcontact : P-L*H∈restrictWeightedOrder v m)
    (hg : ∀ i,z^(v i) ∣ g i)
    (hL : eval₂Hom Polynomial.C g L=0) :
    z^m ∣ eval₂Hom Polynomial.C g P := by
  have hd := pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder Polynomial.C hcontact hg
  simpa only [map_sub,map_mul,hL,zero_mul,sub_zero] using hd

end
end K21_11
end Port_K1_11ContactMembership

section Port_K1_11DecoderPullback
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K21_11
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]

/-- The two decoder variables remain the ORIGINAL code polynomials. -/
def decoderImages (P Q : Polynomial F) (s t : F) : Fin 5 → Polynomial F :=
  ![Polynomial.X,P,Q,Polynomial.C s,Polynomial.C t]

def contactDecoderImages (x a b c d s t : F) (P Q : Polynomial F) : Fin 5 → Polynomial F :=
  ![Polynomial.X-Polynomial.C x,P-Polynomial.C (a+s*b),
    Q-Polynomial.C (c+t*d),Polynomial.C s,Polynomial.C t]

theorem decoder_contact_composition (x a b c d s t : F) (P Q : Polynomial F)
    (G : MvPolynomial (Fin 5) F) :
    aeval (contactDecoderImages x a b c d s t P Q) (contactShift x a b c d G)=
      aeval (decoderImages P Q s t) G := by
  rw [contactShift,aeval_eq_bind₁,aeval_bind₁]
  have hf : (fun i => aeval (contactDecoderImages x a b c d s t P Q) (shiftImages x a b c d i))=decoderImages P Q s t := by
    funext i
    fin_cases i <;> simp [shiftImages,contactDecoderImages,decoderImages] <;> ring
  rw [hf]

theorem contactDecoderImages_vanish (x a b c d s t : F) (P Q : Polynomial F)
    (hP : P.eval x=a+s*b) (hQ : Q.eval x=c+t*d) :
    ∀ i,(Polynomial.X-Polynomial.C x)^contactWeight i∣
      contactDecoderImages x a b c d s t P Q i := by
  have hp : (Polynomial.X-Polynomial.C x)∣P-Polynomial.C (a+s*b) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [hP]
  have hq : (Polynomial.X-Polynomial.C x)∣Q-Polynomial.C (c+t*d) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [hQ]
  simp only [Polynomial.C_add,Polynomial.C_mul] at hp hq
  intro i
  fin_cases i <;> simp [contactWeight,contactDecoderImages,hp,hq]

/-- Actual correct-node contact multiplicity after quotienting by L. -/
theorem decoder_contact_multiplicity (m : ℕ) (x a b c d s t : F)
    (P Q : Polynomial F) (G L H : MvPolynomial (Fin 5) F)
    (hP : P.eval x=a+s*b) (hQ : Q.eval x=c+t*d)
    (hL : aeval (decoderImages P Q s t) L=0)
    (hcontact : contactShift x a b c d G-contactShift x a b c d L*H∈
      restrictWeightedOrder contactWeight m) :
    (Polynomial.X-Polynomial.C x)^m∣aeval (decoderImages P Q s t) G := by
  have hh := contact_mod_relation_pullback contactWeight m
    (contactShift x a b c d G) (contactShift x a b c d L) H
    (contactDecoderImages x a b c d s t P Q) (Polynomial.X-Polynomial.C x)
    hcontact (contactDecoderImages_vanish x a b c d s t P Q hP hQ)
    (by
      change aeval (contactDecoderImages x a b c d s t P Q) (contactShift x a b c d L)=0
      rw [decoder_contact_composition]
      exact hL)
  change (Polynomial.X-Polynomial.C x)^m∣aeval (contactDecoderImages x a b c d s t P Q) (contactShift x a b c d G) at hh
  rwa [decoder_contact_composition] at hh

/-- The weighted source degree controls substitution by every actual
pair of degree<=w decoders, independently of the source's ordinary X-degree. -/
theorem decoder_eval_degree (w D : ℕ) (G : MvPolynomial (Fin 5) F)
    (hG : G.weightedTotalDegree (sourceWeights w 0)≤D)
    (P Q : Polynomial F) (hP : P.natDegree≤w) (hQ : Q.natDegree≤w) (s t : F) :
    (aeval (decoderImages P Q s t) G).natDegree≤D := by
  apply (natDegree_aeval_le_weightedTotalDegree_of_le (sourceWeights w 0)
    (decoderImages P Q s t) G ?_).trans hG
  intro i
  fin_cases i <;> simp [decoderImages,sourceWeights] <;> assumption

/-- A polynomial with m contacts at each distinct node is zero once its
weighted degree is strictly below m times the number of correct nodes. -/
theorem eq_zero_of_many_contacts {ι : Type*} (S : Finset ι) (x : ι → F)
    (hx : Function.Injective x) (m : ℕ) (Q : Polynomial F)
    (hcontact : ∀ i∈S,(Polynomial.X-Polynomial.C (x i))^m∣Q)
    (hdeg : Q.natDegree<m*S.card) : Q=0 := by
  classical
  by_contra hQ
  have hp : (∏ i∈S,(Polynomial.X-Polynomial.C (x i))^m)∣Q := by
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact (Polynomial.pairwise_coprime_X_sub_C hx hij).pow
    · exact hcontact
  have hd := Polynomial.natDegree_le_of_dvd hp hQ
  have hne : ∀ i∈S,(Polynomial.X-Polynomial.C (x i))^m≠0 := by
    intro i hi
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  rw [Polynomial.natDegree_prod _ _ hne] at hd
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,Nat.mul_one,
    Finset.sum_const,smul_eq_mul] at hd
  nlinarith

end
end K21_11
end Port_K1_11DecoderPullback

section Port_K1_11ScalarEliminant
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

namespace K21_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]

/-- Scalar annihilator in X,Y0,S,T after clearing the Y1 denominator. -/
def scalarEliminant (B : ℕ) (G : MvPolynomial (Fin 5) F)
    (a b : MvPolynomial (Fin 4) F) : MvPolynomial (Fin 4) F :=
  clearedEval B (polynomialView G) a b

theorem scalarEliminant_ne_zero (D w B s t : ℕ) (G L : MvPolynomial (Fin 5) F)
    (hG : G∈filtered (sourceWeights w) (sourceBounds D B s t))
    (hnot : ¬ L∣G) (a b : MvPolynomial (Fin 4) F) (hb : b≠0)
    (hlinear : polynomialView L=Polynomial.C b*Polynomial.X-Polynomial.C a)
    (hprimitive : (Polynomial.C b*Polynomial.X-Polynomial.C a).IsPrimitive) :
    scalarEliminant B G a b≠0 := by
  have hnd : ¬ (Polynomial.C b*Polynomial.X-Polynomial.C a)∣polynomialView G := by
    rintro ⟨H,hH⟩
    apply hnot
    refine ⟨polynomialView.symm H,?_⟩
    apply polynomialView.injective
    rw [map_mul,hlinear,AlgEquiv.apply_symm_apply]
    exact hH
  letI : GCDMonoid (MvPolynomial (Fin 4) F) := UniqueFactorizationMonoid.toGCDMonoid _
  exact clearedEval_ne_zero (K:=FractionRing (MvPolynomial (Fin 4) F)) B
    (polynomialView G) (polynomialView_natDegree D w B s t G hG) a b hb hprimitive hnd

/-- Specialized zero denominators are covered by a polynomial identity,
not division. The output still annihilates the ORIGINAL Y0 decoder. -/
theorem scalarEliminant_annihilates (D w B s t : ℕ) (G L : MvPolynomial (Fin 5) F)
    (hG : G∈filtered (sourceWeights w) (sourceBounds D B s t))
    (a b : MvPolynomial (Fin 4) F)
    (hlinear : polynomialView L=Polynomial.C b*Polynomial.X-Polynomial.C a)
    (P Q : Polynomial F) (s0 t0 : F)
    (hL : aeval (decoderImages P Q s0 t0) L=0)
    (hzero : aeval (decoderImages P Q s0 t0) G=0) :
    aeval (scalarImages P s0 t0) (scalarEliminant B G a b)=0 := by
  let φ : MvPolynomial (Fin 4) F →+* Polynomial F := (aeval (scalarImages P s0 t0)).toRingHom
  have hroot : Polynomial.eval Q ((polynomialView G).map φ)=0 := by
    rw [Polynomial.eval_map,polynomialView_eval]
    exact hzero
  have hrel : φ b*Q=φ a := by
    have hh := polynomialView_eval P Q s0 t0 L
    rw [hlinear] at hh
    have hz : Polynomial.eval₂ φ Q (Polynomial.C b*Polynomial.X-Polynomial.C a)=0 :=
      hh.trans hL
    apply sub_eq_zero.mp
    simpa only [Polynomial.eval₂_sub,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X] using hz
  have hd : ((polynomialView G).map φ).natDegree≤B :=
    Polynomial.natDegree_map_le.trans (polynomialView_natDegree D w B s t G hG)
  have hh := clearedEval_zero_of_root B ((polynomialView G).map φ) hd (φ a) (φ b) Q hrel hroot
  rw [← map_clearedEval] at hh
  exact hh

end
end K21_11
end Port_K1_11ScalarEliminant

section Port_K1_11Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K21_11
noncomputable section

open K21 MvPolynomial

/-- Independent parameter lift, using the order X,Y₀,Y₁,S,T. Graph
specialization may retain a nonzero content in the one-variable seed. -/
structure IndependentLift {u : Words} {T : TwoActive u} (R : Relation T) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  omitted : U.degreeOf 1 = 0 ∧ U.degreeOf 2 = 0 ∧
    V.degreeOf 1 = 0 ∧ V.degreeOf 2 = 0
  heights : U.degreeOf 0 ≤ T.height ∧ V.degreeOf 0 ≤ T.height
  boxes : U.degreeOf 3 ≤ 2 ∧ U.degreeOf 4 ≤ 3 ∧ V.degreeOf 3 ≤ 3 ∧ V.degreeOf 4 ≤ 2
  primitive : ∀ q : MvPolynomial (Fin 2) K,
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ U →
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ V → IsUnit q
  content : Polynomial K
  content_ne : content ≠ 0
  graphU : aeval ![Polynomial.X, 0, 0, seed, seed ^ p] U =
    Polynomial.C content * leftU R
  graphV : aeval ![Polynomial.X, 0, 0, seed, seed ^ p] V =
    Polynomial.C content * leftV R
  original_height : 24549 ≤ T.height

structure Puncture (deleted : Finset I) where
  N : ℕ
  index : Fin N ↪ I
  retained : ∀ i, i ∈ Set.range index ↔ i ∉ deleted
  size : N + deleted.card = 262144

def Puncture.nodes {deleted : Finset I} (P : Puncture deleted) (i : Fin P.N) : K :=
  node (P.index i)

structure Marks (u : Words) (deleted : Finset I) (Γ : Finset K) where
  mark : ∀ γ ∈ Γ, BadMark u γ
  survives : ∀ γ (hγ : γ ∈ Γ) i, i ∈ (mark γ hγ).support → i ∉ deleted

inductive Bank
  | lowS
  | lowT
  | symmetric
  | oneThree
  | threeOne
  | twoThree
  | threeTwo
  | threeThree

def Bank.dS : Bank → ℕ
  | .lowS => 1
  | .lowT => 2
  | .symmetric => 2
  | .oneThree => 1
  | .threeOne => 3
  | .twoThree => 2
  | .threeTwo => 3
  | .threeThree => 3

def Bank.dT : Bank → ℕ
  | .lowS => 2
  | .lowT => 1
  | .symmetric => 2
  | .oneThree => 3
  | .threeOne => 1
  | .twoThree => 3
  | .threeTwo => 2
  | .threeThree => 3

def Bank.s : Bank → ℕ
  | .lowS => 15
  | .lowT => 9
  | .symmetric => 11
  | .oneThree => 11
  | .threeOne => 6
  | .twoThree => 10
  | .threeTwo => 7
  | .threeThree => 8

def Bank.t : Bank → ℕ
  | .lowS => 8
  | .lowT => 14
  | .symmetric => 8
  | .oneThree => 5
  | .threeOne => 10
  | .twoThree => 5
  | .threeTwo => 8
  | .threeThree => 6

def Bank.a (b : Bank) : ℕ := b.s + 5 * b.dS
def Bank.b (b : Bank) : ℕ := b.t + 5 * (b.dT - 1)
def Bank.E (b : Bank) : ℕ := b.a + b.b
def Bank.M (b : Bank) : ℕ := (2 * 131071 - 1) * (b.E - 1) + 1
def Bank.zeroFee (b : Bank) : ℕ := b.a + p * b.b
def Bank.chartFee (b : Bank) : ℚ := b.E * ((131073 / 49098 : ℚ) * b.M) ^ 2

def Bank.relationBounds (b : Bank) (H : ℕ) : Fin 4 → ℕ := ![131071 + H, 1, b.dS, b.dT]

/-- Source data for the actual punctured words, including local order
over the independent parameters and the primitive equation in Y₁. -/
structure ContactInput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (b : Bank) (H : ℕ) where
  L : MvPolynomial (Fin 5) K
  L_ne : L ≠ 0
  degrees : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j
  order_one : ∀ i : Fin P.N,
    (contactLift contactWeight
      (contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) L)).natTrailingDegree = 1
  numerator : MvPolynomial (Fin 4) K
  denominator : MvPolynomial (Fin 4) K
  denominator_ne : denominator ≠ 0
  linear : polynomialView L =
    Polynomial.C denominator * Polynomial.X - Polynomial.C numerator
  primitive : (Polynomial.C denominator * Polynomial.X - Polynomial.C numerator).IsPrimitive
  numerator_Y : numerator.weightedTotalDegree scalarWeightY ≤ 1
  denominator_Y : denominator.weightedTotalDegree scalarWeightY ≤ 0
  numerator_S : numerator.weightedTotalDegree scalarWeightYS ≤ b.dS
  denominator_S : denominator.weightedTotalDegree scalarWeightYS ≤ b.dS
  numerator_T : numerator.weightedTotalDegree scalarWeightT ≤ b.dT
  denominator_T : denominator.weightedTotalDegree scalarWeightT ≤ b.dT - 1

def scalarWeightTotal : Fin 4 → ℕ := ![0, 1, 1, 1]

/-- The chosen actual decoder of each original slope is a root, including
at labels where the denominator used in the construction specializes to zero. -/
structure Annihilator {u : Words} {deleted : Finset I} {Γ : Finset K}
    (F : Marks u deleted Γ) (b : Bank) where
  Q : MvPolynomial (Fin 4) K
  nonzero : Q ≠ 0
  degreeY : Q.weightedTotalDegree scalarWeightY ≤ 5
  degreeS : Q.weightedTotalDegree scalarWeightYS ≤ b.a
  degreeT : Q.weightedTotalDegree scalarWeightT ≤ b.b
  degreeTotal : Q.weightedTotalDegree scalarWeightTotal ≤ b.E
  vanishes : ∀ γ (hγ : γ ∈ Γ),
    aeval (scalarImages (F.mark γ hγ).decoder γ (γ ^ p)) Q = 0

/-- The node equation of a Taylor polynomial with its denominator cleared.
Chart coordinates are Y at the transcendental center, S, and T. -/
def nodeCut (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (numerator : Polynomial (MvPolynomial (Fin 3) Frac)) (denominator : MvPolynomial (Fin 3) Frac)
    (i : Fin P.N) : MvPolynomial (Fin 3) Frac :=
  numerator.eval (C (algebraMap K Frac (P.nodes i))) -
    denominator * (C (algebraMap K Frac (u 0 (P.index i))) +
      MvPolynomial.X 1 * C (algebraMap K Frac (u 1 (P.index i))))

/-- One simple-root chart. The same cleared polynomial describes the
selected decoder at every marked point and determines all its node cuts. -/
structure TaylorChart (u : Words) {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank) (Λ : Finset K) where
  subset : Λ ⊆ Γ
  equation : MvPolynomial (Fin 3) Frac
  equation_ne : equation ≠ 0
  equation_degree : equation.totalDegree ≤ b.E
  numerator : Polynomial (MvPolynomial (Fin 3) Frac)
  numerator_degree : numerator.natDegree ≤ 131071
  denominator : MvPolynomial (Fin 3) Frac
  cut_degree : ∀ i, (nodeCut u P numerator denominator i).totalDegree ≤ b.M
  point : K → Fin 3 → Frac
  slope : ∀ γ ∈ Λ, point γ 1 = algebraMap K Frac γ
  on_equation : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) equation = 0
  regular : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) denominator ≠ 0
  reconstruction : ∀ γ (hγ : γ ∈ Λ),
    numerator.map (MvPolynomial.eval (point γ)) =
      Polynomial.C (MvPolynomial.eval (point γ) denominator) *
        (F.mark γ (subset hγ)).decoder.map (algebraMap K Frac)

end
end K21_11
end Port_K1_11Defs

section Port_K1_11BankArithmetic
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace K21_11
open K21

/-- Lower the X-height by e and remove those same e nodes. The finite
monomial sums are affine on this native interval, including the shortest block. -/
theorem bank_surplus (b : Bank) (h H e N : ℕ) (hh : 24549 ≤ h) (hmax : h ≤ 32872)
    (hH : H + e = h) (hN : N + e = 262144) :
    N * (J 4 b.s b.t - J 3 (b.s - b.dS) (b.t - b.dT)) +
      V (720675 - 131071 - H) 131071 4 (b.s - b.dS) (b.t - b.dT) <
      V 720675 131071 5 b.s b.t := by
  cases b <;> norm_num [Bank.s, Bank.t, Bank.dS, Bank.dT, V, J, Finset.sum_range_succ,
    Nat.sub_sub] <;> omega

theorem chartFee_nonneg (b : Bank) : 0 ≤ b.chartFee := by
  unfold Bank.chartFee
  positivity

theorem final_fee (b : Bank) :
    (b.zeroFee : ℚ) + 5 * b.chartFee ≤ 150000000000000000 := by
  cases b <;> norm_num [Bank.zeroFee, Bank.chartFee, Bank.M, Bank.E, Bank.a, Bank.b,
    Bank.s, Bank.t, Bank.dS, Bank.dT, FrobeniusLocator.Native.p]

end K21_11
end Port_K1_11BankArithmetic

section Port_K1_11QuotientSource
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace K21_11
noncomputable section

open MvPolynomial

private theorem exists_kernel_outside {F E G : Type*} [Field F]
    [AddCommGroup E] [Module F E] [Module.Finite F E]
    [AddCommGroup G] [Module F G] [Module.Finite F G]
    (f : E →ₗ[F] G) (R : Submodule F E)
    (hdim : Module.finrank F G + Module.finrank F R < Module.finrank F E) :
    ∃ q : E, f q = 0 ∧ q ∉ R := by
  by_contra hn
  have hle : LinearMap.ker f ≤ R := by
    intro q hq
    by_contra hnot
    exact hn ⟨q, LinearMap.mem_ker.mp hq, hnot⟩
  have hk := Submodule.finrank_mono hle
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hr := (LinearMap.range f).finrank_le
  omega

abbrev Source (F : Type*) [Field F] (b : Bank) :=
  filtered (F := F) (sourceWeights 131071) (sourceBounds 720675 5 b.s b.t)

abbrev Multipliers (F : Type*) [Field F] (b : Bank) := JetSpace F 2 (b.s - b.dS) (b.t - b.dT)

variable {F : Type*} [Field F]

structure ContactData (N : ℕ) (L : MvPolynomial (Fin 5) F) (b : Bank) where
  x : Fin N → F
  first : Fin N → F
  firstSlope : Fin N → F
  second : Fin N → F
  secondSlope : Fin N → F
  nonzero : L ≠ 0
  degreeS : L.weightedTotalDegree (sourceWeights 1 2) ≤ b.dS
  degreeT : L.weightedTotalDegree (sourceWeights 1 3) ≤ b.dT
  order_one : ∀ i, (contactLift contactWeight
    (contactShift (x i) (first i) (firstSlope i) (second i) (secondSlope i) L)).natTrailingDegree = 1

variable {N : ℕ} {L : MvPolynomial (Fin 5) F} {b : Bank} {H : ℕ} (D : ContactData N L b)

def ContactData.shifted (i : Fin N) (Q : MvPolynomial (Fin 5) F) :=
  contactShift (D.x i) (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i) Q

private theorem shifted_S (i : Fin N) :
    (D.shifted i L).weightedTotalDegree (sourceWeights 1 2) ≤ b.dS := by
  apply (contactShift_parameter_weights _ _ _ _ _ L).1.trans
  exact D.degreeS

private theorem shifted_T (i : Fin N) :
    (D.shifted i L).weightedTotalDegree (sourceWeights 1 3) ≤ b.dT := by
  apply (contactShift_parameter_weights _ _ _ _ _ L).2.trans
  exact D.degreeT

private theorem shifted_ne (i : Fin N) : D.shifted i L ≠ 0 := by
  intro hz
  have hh := D.order_one i
  change (contactLift contactWeight (D.shifted i L)).natTrailingDegree = 1 at hh
  simp [hz] at hh

private theorem bank_s (b : Bank) : b.s - b.dS + b.dS = b.s := by cases b <;> rfl
private theorem bank_t (b : Bank) : b.t - b.dT + b.dT = b.t := by cases b <;> rfl

private def localMultiply (i : Fin N) : Multipliers F b →ₗ[F] JetSpace F 3 b.s b.t where
  toFun Q := ⟨weightedTruncation contactWeight 4 (D.shifted i L * Q.val), by
    simpa only [bank_s, bank_t] using
      truncated_mul_mem_jet 2 (b.s-b.dS) (b.t-b.dT) b.dS b.dT (D.shifted i L)
        (shifted_S D i) (shifted_T D i) Q⟩
  map_add' Q R := by apply Subtype.ext; simp [mul_add]
  map_smul' a Q := by apply Subtype.ext; simp

private theorem localMultiply_injective (i : Fin N) :
    Function.Injective (localMultiply D i) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro Q hQ
  by_contra hn
  have hprod : weightedTruncation contactWeight 4 (D.shifted i L * Q.val) = 0 :=
    congrArg (fun x : JetSpace F 3 b.s b.t => x.val) hQ
  have hhigh := (weightedTruncation_eq_zero_iff _ _ _).mp hprod
  have hQn : Q.val ≠ 0 := fun hz => hn (Subtype.ext hz)
  exact contact_product_not_high_order contactWeight 4 (D.shifted i L) Q.val
    (D.order_one i) (shifted_ne D i) hQn (jetSpace_support_bound _ _ _ Q) hhigh

private abbrev LocalSpace (i : Fin N) :=
  (JetSpace F 3 b.s b.t) ⧸ LinearMap.range (localMultiply D i)

private theorem local_finrank (i : Fin N) :
    Module.finrank F (LocalSpace D i) = J 4 b.s b.t - J 3 (b.s-b.dS) (b.t-b.dT) := by
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (localMultiply D i))
  rw [LinearMap.finrank_range_of_inj (localMultiply_injective D i), jetSpace_finrank,
    jetSpace_finrank] at hq
  change Module.finrank F (LocalSpace D i) + J 3 (b.s-b.dS) (b.t-b.dT) = J 4 b.s b.t at hq
  omega

private def nodeMap (i : Fin N) : Source F b →ₗ[F] LocalSpace D i :=
  (LinearMap.range (localMultiply D i)).mkQ.comp
    (sourceToJet 720675 131071 5 b.s b.t 3 (D.x i) (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i))

private theorem localContact (Q : Source F b) (i : Fin N) (hi : nodeMap D i Q = 0) :
    ∃ R : Multipliers F b, D.shifted i Q.val - D.shifted i L * R.val ∈
      restrictWeightedOrder contactWeight 4 := by
  have hmem : sourceToJet 720675 131071 5 b.s b.t 3 (D.x i)
      (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i) Q ∈
      LinearMap.range (localMultiply D i) :=
    (Submodule.Quotient.mk_eq_zero _).mp hi
  obtain ⟨R, hR⟩ := hmem
  refine ⟨R, (weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm

theorem exists_quotient_source (h e : ℕ) (hmin : 24549 ≤ h) (hmax : h ≤ 32872)
    (hH : H + e = h) (hN : N + e = 262144)
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j) :
    ∃ Q : Source F b, ¬ L ∣ Q.val ∧ ∀ i, ∃ R : Multipliers F b,
      D.shifted i Q.val - D.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hfit : ∀ i, b.relationBounds H i ≤ sourceBounds 720675 5 b.s b.t i := by
    intro i
    cases b <;> fin_cases i <;>
      simp [Bank.relationBounds, Bank.s, Bank.t, Bank.dS, Bank.dT, sourceBounds] <;> omega
  have hshift : (fun i => sourceBounds 720675 5 b.s b.t i - b.relationBounds H i) =
      sourceBounds (720675 - 131071 - H) 4 (b.s-b.dS) (b.t-b.dT) := by
    funext i
    fin_cases i <;> simp [sourceBounds, Bank.relationBounds] <;> omega
  let mult := filteredMul (sourceWeights 131071) (sourceBounds 720675 5 b.s b.t)
    (b.relationBounds H) L D.nonzero hdeg hfit
  have hdimMult : Module.finrank F (LinearMap.range mult) =
      V (720675 - 131071 - H) 131071 4 (b.s-b.dS) (b.t-b.dT) := by
    rw [LinearMap.finrank_range_of_inj
      (filteredMul_injective _ _ _ L D.nonzero hdeg hfit), hshift, source_filtered_finrank]
  have hdimLocal : Module.finrank F (∀ i : Fin N, LocalSpace D i) =
      N * (J 4 b.s b.t - J 3 (b.s-b.dS) (b.t-b.dT)) := by
    letI (i : Fin N) : Module.Free F (LocalSpace D i) := Module.Free.of_divisionRing F _
    rw [Module.finrank_pi_fintype]
    simp only [local_finrank D, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim : Module.finrank F (∀ i : Fin N, LocalSpace D i) +
      Module.finrank F (LinearMap.range mult) < Module.finrank F (Source F b) := by
    rw [hdimLocal, hdimMult, source_filtered_finrank]
    exact bank_surplus b h H e N hmin hmax hH hN
  letI : Module F (∀ i : Fin N, LocalSpace D i) := Pi.module _ _ _
  obtain ⟨Q, hQ, hnot⟩ := exists_kernel_outside (G := ∀ i : Fin N, LocalSpace D i)
    (LinearMap.pi (nodeMap D)) (LinearMap.range mult) hdim
  exact ⟨Q, (mem_filteredMul_range_iff _ _ _ L D.nonzero hdeg hfit Q).not.mp hnot,
    fun i => localContact D Q i (congrFun hQ i)⟩

end
end K21_11
end Port_K1_11QuotientSource

section Port_K1_11_1Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K21_11_1

noncomputable section

open Polynomial Matrix FrobeniusLocator

abbrev Seeds (F : Type) [Field F] := MvPolynomial (Fin 2) F

abbrev PlaneField (F : Type) [Field F] := FractionRing (Seeds F)

def graph {F : Type} [Field F] (p : ℕ) : Seeds F →ₐ[F] F[X] :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.X ^ p]

def coefficientPrimitive {A ι : Type} [CommMonoid A] (v : ι → A) : Prop :=
  ∀ q : A, (∀ i, q ∣ v i) → IsUnit q

def planePair {F : Type} [Field F] {h : ℕ}
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2) : (Seeds F)[X] :=
  Principal.assemble (fun j => Q (b, j))

def blockDegree {F : Type} [Field F] {h : ℕ}
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b i : Fin 2) : ℕ :=
  Finset.univ.sup (fun j : Fin (h + 1) => (Q (b, j)).degreeOf i)

def planeSyndrome {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (b : Fin 2) (j : ℕ) : Seeds F :=
  if b = 0 then
    MvPolynomial.C (syndrome x u j) + MvPolynomial.X b * MvPolynomial.C (syndrome x v j)
  else
    MvPolynomial.C (syndrome x u j ^ p) + MvPolynomial.X b * MvPolynomial.C (syndrome x v j ^ p)

def planeSlice {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (m h : ℕ) :
    Matrix (Fin (m - h)) (Fin 2 × Fin (h + 1)) (Seeds F) :=
  fun j b => planeSyndrome p x u v b.1 (b.2.val + j.val)

def planeStack {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (L t : ℕ) : Matrix (Fin 2 × Fin L) (Fin (t + 1)) (Seeds F) :=
  fun b j => planeSyndrome p x u v b.1 (b.2.val + j.val)

def seedPositions : Fin 2 → Fin 5 := ![3, 4]

def intoFive {F : Type} [Field F] : (Seeds F)[X] →+* MvPolynomial (Fin 5) F :=
  Polynomial.eval₂RingHom (MvPolynomial.rename seedPositions).toRingHom (MvPolynomial.X 0)

end

end K21_11_1
end Port_K1_11_1Defs

section Port_K1_11_1Graph
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K21_11_1

noncomputable section

open MvPolynomial Finset Polynomial
open FrobeniusLocator

variable {F : Type} [Field F]

-- Bounded-degree coefficient injection, adapted from z13 FrobeniusCoefficient.
def graphExponent (p : ℕ) (e : Fin 2 →₀ ℕ) : ℕ := e 0+p*e 1

theorem graphExponent_injOn (p : ℕ) (hp : 0<p) :
    Set.InjOn (graphExponent p) {e : Fin 2 →₀ ℕ | e 0<p} := by
  intro e he f hf h
  have hm := congrArg (fun n : ℕ => n%p) h
  simp only [graphExponent,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf] at hm
  have hmul : p*e 1=p*f 1 := by unfold graphExponent at h; omega
  have h1 : e 1=f 1 := Nat.eq_of_mul_eq_mul_left hp hmul
  ext i
  fin_cases i <;> assumption

theorem graph_monomial (p : ℕ) (e : Fin 2 →₀ ℕ) (a : F) :
    graph p (monomial e a)=Polynomial.monomial (graphExponent p e) a := by
  rw [graph,MvPolynomial.aeval_monomial]
  simp [Finsupp.prod_fintype,Fin.prod_univ_succ,graphExponent,← pow_mul,← pow_add,Polynomial.C_mul_X_pow_eq_monomial]

theorem graph_coeff (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hdegree : Q.degreeOf 0 < p) (e : Fin 2 →₀ ℕ) (he : e∈Q.support) :
    (graph p Q).coeff (graphExponent p e)=Q.coeff e := by
  classical
  have hex : graph p Q=∑ f∈Q.support,Polynomial.monomial (graphExponent p f) (Q.coeff f) := by
    conv_lhs => rw [Q.as_sum]
    simp only [map_sum,graph_monomial]
  rw [hex,Polynomial.finsetSum_coeff]
  trans ((Polynomial.monomial (graphExponent p e) (Q.coeff e)).coeff (graphExponent p e))
  · apply Finset.sum_eq_single_of_mem e he
    intro f hf hfe
    rw [Polynomial.coeff_monomial,ite_eq_right]
    intro h
    apply hfe
    apply graphExponent_injOn p hp
    · exact (le_degreeOf_of_mem_support 0 hf).trans_lt hdegree
    · exact (le_degreeOf_of_mem_support 0 he).trans_lt hdegree
    · exact h
  · simp

theorem graph_ne_zero (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hQ : Q≠0) (hdegree : Q.degreeOf 0 < p) : graph p Q≠0 := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hQ
  intro hz
  have hh := graph_coeff p hp Q hdegree e he
  rw [hz,Polynomial.coeff_zero] at hh
  exact (mem_support_iff.mp he) hh.symm

section Rank

open Matrix

variable {r H J : ℕ}

private theorem exists_rank_minor {ι κ E : Type} [Fintype ι] [Fintype κ] [Field E]
    (A : Matrix ι κ E) :
    ∃ (rows : Fin A.rank → ι) (cols : Fin A.rank → κ), (A.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis
    (Polynomial.evalRingHom (0 : E)) (A.map Polynomial.C) A.rank (by
      have heq : (A.map Polynomial.C).map (Polynomial.evalRingHom (0 : E)) = A := by
        ext i j
        simp
      rw [heq])
  refine ⟨B.rows, B.cols, ?_⟩
  intro h
  apply B.minor_ne
  change ((A.submatrix B.rows B.cols).map Polynomial.C).det = 0
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]

private theorem minor_degree {υ : Type} [Fintype υ] [DecidableEq υ]
    (i : Fin 2) (A : Matrix υ υ (Seeds F)) (d : υ → ℕ)
    (hd : ∀ j k, (A j k).degreeOf i ≤ d k) :
    A.det.degreeOf i ≤ ∑ k, d k := by
  classical
  rw [Matrix.det_apply']
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  have hc : ((↑↑(Equiv.Perm.sign σ) : Seeds F)).degreeOf i = 0 := by
    rw [← map_intCast (MvPolynomial.C : F →+* Seeds F), degreeOf_C]
  apply (degreeOf_mul_le _ _ _).trans
  rw [hc, zero_add]
  exact (degreeOf_prod_le _ _ _).trans (Finset.sum_le_sum (fun k _ => hd (σ k) k))

private theorem graph_minor_ne_zero (p : ℕ) (hp : 0 < p) (hH : H < p)
    (A : Matrix (Fin J) (Fin 2 × Fin H) (Seeds F))
    (hd : ∀ j k, (A j k).degreeOf 0 ≤ if k.1 = 0 then 1 else 0)
    (rows : Fin r → Fin J) (cols : Fin r → Fin 2 × Fin H)
    (hminor : (A.submatrix rows cols).det ≠ 0) :
    graph p (A.submatrix rows cols).det ≠ 0 := by
  classical
  have hinj : Function.Injective cols := by
    intro j k hjk
    by_contra hne
    exact hminor (Matrix.det_zero_of_column_eq hne (by
      intro l
      change A (rows l) (cols j) = A (rows l) (cols k)
      rw [hjk]))
  apply graph_ne_zero p hp _ hminor
  apply (minor_degree 0 (A.submatrix rows cols) (fun k => if (cols k).1 = 0 then 1 else 0)
    (fun j k => hd (rows j) (cols k))).trans_lt
  apply lt_of_le_of_lt _ hH
  let S : Finset (Fin r) := Finset.univ.filter (fun k => (cols k).1 = 0)
  have hsum : (∑ k, if (cols k).1 = 0 then 1 else 0) = S.card := by
    simp [S, Finset.sum_boole]
  rw [hsum]
  have hle : S.card ≤ Fintype.card (Fin H) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_le_of_injective (fun k : S => (cols k.val).2) ?_
    intro j k hjk
    apply Subtype.ext
    apply hinj
    have hj : (cols j.val).1 = 0 := (Finset.mem_filter.mp j.property).2
    have hk : (cols k.val).1 = 0 := (Finset.mem_filter.mp k.property).2
    exact Prod.ext (hj.trans hk.symm) hjk
  simpa only [Fintype.card_fin] using hle

/-- All nonzero minors survive because their first-parameter degree is
bounded by the number of available ordinary columns. -/
theorem rank_graph (q : ℕ) (hq : 0 < q) (hH : H < q)
    (A : Matrix (Fin J) (Fin 2 × Fin H) (Seeds F))
    (hd : ∀ j k, (A j k).degreeOf 0 ≤ if k.1 = 0 then 1 else 0) :
    (A.map (algebraMap (Seeds F) (PlaneField F))).rank =
      (A.map ((algebraMap F[X] (FrobeniusLocator.GenericLayer.GenericField F)).comp
        (graph q).toRingHom)).rank := by
  let f := algebraMap (Seeds F) (PlaneField F)
  let g := (algebraMap F[X] (FrobeniusLocator.GenericLayer.GenericField F)).comp
    (graph (F := F) q).toRingHom
  have hdet {E : Type} [Field E] (φ : Seeds F →+* E) {s : ℕ} (rows : Fin s → Fin J) (cols : Fin s → Fin 2 × Fin H) :
      ((A.map φ).submatrix rows cols).det = φ (A.submatrix rows cols).det := by
    have he := φ.map_det (A.submatrix rows cols)
    rw [RingHom.mapMatrix_apply] at he
    exact he.symm
  change (A.map f).rank = (A.map g).rank
  apply le_antisymm
  · obtain ⟨rows, cols, hn⟩ := exists_rank_minor (A.map f)
    rw [hdet f] at hn
    have hn' : (A.submatrix rows cols).det ≠ 0 := fun h => hn (by rw [h, map_zero])
    have hg : ((A.map g).submatrix rows cols).det ≠ 0 := by
      rw [hdet g]
      change algebraMap F[X] (GenericLayer.GenericField F) (graph q _) ≠ 0
      rw [← map_zero (algebraMap F[X] (GenericLayer.GenericField F))]
      exact (IsFractionRing.injective F[X] _).ne
        (graph_minor_ne_zero q hq hH A hd rows cols hn')
    have h := Matrix.rank_submatrix_le (A.map g) rows cols
    rwa [Matrix.rank_of_det_ne_zero hg, Fintype.card_fin] at h
  · obtain ⟨rows, cols, hn⟩ := exists_rank_minor (A.map g)
    rw [hdet g] at hn
    have hn' : (A.submatrix rows cols).det ≠ 0 := fun h => hn (by rw [h, map_zero])
    have hf : ((A.map f).submatrix rows cols).det ≠ 0 := by
      rw [hdet f]
      rw [← map_zero f]
      exact (IsFractionRing.injective (Seeds F) _).ne hn'
    have h := Matrix.rank_submatrix_le (A.map f) rows cols
    rwa [Matrix.rank_of_det_ne_zero hf, Fintype.card_fin] at h

end Rank

end
end K21_11_1
end Port_K1_11_1Graph

section Port_K1_11DecoderSource
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace K21_11
noncomputable section

open K21 MvPolynomial

variable {u : Words} {deleted : Finset I} {P : Puncture deleted} {b : Bank} {H : ℕ}
    (D : ContactInput u P b H)

def ContactInput.shifted (_D : ContactInput u P b H) (i : Fin P.N) (Q : MvPolynomial (Fin 5) K) :=
  contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
    (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) Q

private def asContactData : ContactData P.N D.L b where
  x := P.nodes
  first := fun i => u 0 (P.index i)
  firstSlope := fun i => u 1 (P.index i)
  second := fun i => u 0 (P.index i) ^ p
  secondSlope := fun i => u 1 (P.index i) ^ p
  nonzero := D.L_ne
  degreeS := le_of_eq (D.degrees 2)
  degreeT := le_of_eq (D.degrees 3)
  order_one := D.order_one

private theorem contact_order_one_mem {σ : Type*} (v : σ → ℕ) (L : MvPolynomial σ K)
    (hL : (contactLift v L).natTrailingDegree = 1) : L ∈ restrictWeightedOrder v 1 := by
  apply (contactLift_X_pow_dvd_iff v 1 L).mp
  apply Polynomial.X_pow_dvd_iff.mpr
  intro d hd
  apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
  omega

def correctOn (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (Q Q' : Polynomial K) (s t : K) (S : Finset (Fin P.N)) : Prop :=
  ∀ i ∈ S, Q.eval (P.nodes i) = u 0 (P.index i) + s * u 1 (P.index i) ∧
    Q'.eval (P.nodes i) = u 0 (P.index i) ^ p + t * u 1 (P.index i) ^ p

theorem nodes_injective : Function.Injective P.nodes :=
  ProximityPrize.Benchmark.IRSProfile.domain.injective.comp P.index.injective

theorem relation_annihilates (hH : H ≤ 32872) (Q Q' : Polynomial K)
    (hQ : Q.natDegree ≤ 131071) (hQ' : Q'.natDegree ≤ 131071)
    (s t : K) (S : Finset (Fin P.N)) (hS : 180169 ≤ S.card) (hc : correctOn u P Q Q' s t S) :
    aeval (decoderImages Q Q' s t) D.L = 0 := by
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 1
  · intro i hi
    have ho := contact_order_one_mem contactWeight (D.shifted i D.L) (D.order_one i)
    have hd := pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder Polynomial.C ho
      (contactDecoderImages_vanish _ _ _ _ _ s t Q Q' (hc i hi).1 (hc i hi).2)
    change (Polynomial.X-Polynomial.C (P.nodes i))^1 ∣
      aeval (contactDecoderImages (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i)^p) (u 1 (P.index i)^p) s t Q Q') (D.shifted i D.L) at hd
    rwa [ContactInput.shifted, decoder_contact_composition] at hd
  · have hdeg : D.L.weightedTotalDegree (sourceWeights 131071 0) ≤ 131071+H :=
      le_of_eq (D.degrees 0)
    have hd := decoder_eval_degree 131071 (131071+H) D.L hdeg Q Q' hQ hQ' s t
    omega

theorem exists_two_decoder_source (h : ℕ) (hmin : 24549 ≤ h) (hmax : h ≤ 32872)
    (hH : H + deleted.card = h) :
    ∃ G : Source K b, ¬ D.L ∣ G.val ∧
      ∀ (Q Q' : Polynomial K), Q.natDegree ≤ 131071 → Q'.natDegree ≤ 131071 →
        ∀ (s t : K) (S : Finset (Fin P.N)), 180169 ≤ S.card → correctOn u P Q Q' s t S →
          aeval (decoderImages Q Q' s t) G.val = 0 := by
  obtain ⟨G, hnot, hnode⟩ := exists_quotient_source (asContactData D) h deleted.card hmin hmax hH P.size D.degrees
  refine ⟨G, hnot, ?_⟩
  intro Q Q' hQ hQ' s t S hS hc
  have hrel := relation_annihilates D (by omega) Q Q' hQ hQ' s t S hS hc
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 4
  · intro i hi
    obtain ⟨R, hR⟩ := hnode i
    exact decoder_contact_multiplicity 4 _ _ _ _ _ s t Q Q' G.val D.L R.val
      (hc i hi).1 (hc i hi).2 hrel hR
  · have hd := decoder_eval_degree 131071 720675 G.val
      ((mem_filtered _ _ _).mp G.property 0) Q Q' hQ hQ' s t
    omega

end
end K21_11
end Port_K1_11DecoderSource

section Port_K1_11_1Coefficients
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K21_11_1

noncomputable section

open Polynomial Matrix FrobeniusLocator
open scoped BigOperators nonZeroDivisors

theorem mulVec_map {A B ι κ : Type} [CommRing A] [CommRing B] [Fintype κ]
    (f : A →+* B) (M : Matrix ι κ A) (v : κ → A) :
    (M.map f).mulVec (fun j => f (v j)) = fun i => f (M.mulVec v i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

private theorem primitive_vector {A κ : Type} [CommRing A] [IsDomain A]
    [NormalizedGCDMonoid A] [Fintype κ] (v : κ → A) (hv : v ≠ 0) :
    ∃ (g : A) (Q : κ → A), g ≠ 0 ∧ v = g • Q ∧ coefficientPrimitive Q := by
  classical
  let g := Finset.univ.gcd v
  have hdiv (i : κ) : g ∣ v i := Finset.gcd_dvd (Finset.mem_univ i)
  have hg : g ≠ 0 := by
    intro he
    apply hv
    funext i
    simpa only [he, zero_dvd_iff, Pi.zero_apply] using hdiv i
  choose Q hQ using hdiv
  refine ⟨g, Q, hg, funext hQ, fun q hq => ?_⟩
  have hd : g * q ∣ g := Finset.dvd_gcd (fun i _ => by
    rw [hQ i, mul_dvd_mul_iff_left hg]
    exact hq i)
  apply isUnit_iff_dvd_one.mpr
  apply (mul_dvd_mul_iff_left hg).mp
  simpa only [mul_one] using hd

/-- Clear denominators in a nonzero kernel vector, then divide its
coefficients by their gcd in the independent seed ring. -/
theorem plane_generator {F ι κ : Type} [Field F] [Fintype κ]
    (M : Matrix ι κ (Seeds F))
    (hn : 0 < Module.finrank (PlaneField F)
      (LinearMap.ker (M.map (algebraMap (Seeds F) (PlaneField F))).mulVecLin)) :
    ∃ Q : κ → Seeds F, Q ≠ 0 ∧ M.mulVec Q = 0 ∧ coefficientPrimitive Q := by
  classical
  let N := M.map (algebraMap (Seeds F) (PlaneField F))
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hn
  let v : κ → PlaneField F := w.val
  have hv : v ≠ 0 := fun he => hw (Subtype.ext he)
  have hk : N.mulVec v = 0 := w.property
  let D := (Seeds F)⁰
  let g := IsLocalization.commonDenom D Finset.univ v
  let W (i : κ) : Seeds F := IsLocalization.integerMultiple D Finset.univ v ⟨i, Finset.mem_univ i⟩
  have hW (i : κ) : algebraMap (Seeds F) (PlaneField F) (W i) =
      algebraMap (Seeds F) (PlaneField F) (g : Seeds F) * v i := by
    have he := IsLocalization.map_integerMultiple D Finset.univ v ⟨i, Finset.mem_univ i⟩
    change _ = (g : Seeds F) • v i at he
    simpa only [Algebra.smul_def] using he
  have hg : algebraMap (Seeds F) (PlaneField F) (g : Seeds F) ≠ 0 :=
    fun hz => (mem_nonZeroDivisors_iff_ne_zero.mp g.property)
      (IsFractionRing.injective (Seeds F) (PlaneField F) (hz.trans (map_zero _).symm))
  have hWne : W ≠ 0 := by
    intro he
    apply hv
    funext i
    have hf := hW i
    rw [he, Pi.zero_apply, map_zero] at hf
    exact (mul_eq_zero.mp hf.symm).resolve_left hg
  have hWM : M.mulVec W = 0 := by
    have h := mulVec_map (algebraMap (Seeds F) (PlaneField F)) M W
    simp only [hW] at h
    change N.mulVec ((algebraMap (Seeds F) (PlaneField F) (g : Seeds F)) • v) = _ at h
    rw [Matrix.mulVec_smul, hk, smul_zero] at h
    funext i
    apply IsFractionRing.injective (Seeds F) (PlaneField F)
    rw [Pi.zero_apply, map_zero]
    exact (congrFun h i).symm
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := Seeds F)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Seeds F)
  obtain ⟨a, Q, ha, he, hp⟩ := primitive_vector W hWne
  refine ⟨Q, ?_, ?_, hp⟩
  · intro hz
    rw [hz, smul_zero] at he
    exact hWne he
  · rw [he, Matrix.mulVec_smul] at hWM
    funext i
    exact (mul_eq_zero.mp (congrFun hWM i)).resolve_left ha

/-- A vector in the degree-h slice supplies all of its shifts in
the full window. The cutoffs keep every shifted moment in the slice. -/
theorem shifts_annihilate {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (h L s t : ℕ) (hs : h + s = L)
    (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (hQ : (planeSlice p x u v (L + t) h).mulVec Q = 0) :
    (K1_6.shifts (planePair Q) L s).transpose * planeStack p x u v L t = 0 := by
  classical
  apply Matrix.ext
  intro d j
  let e : Fin 2 × Fin (h + 1) ↪ Fin 2 × Fin L :=
    ⟨fun z => (z.1, ⟨z.2.val + d.val, by have := z.2.isLt; have := d.isLt; omega⟩),
      fun a b hab => Prod.ext (congrArg (fun z : Fin 2 × Fin L => z.1) hab)
        (Fin.ext (by
          have he := congrArg (fun z : Fin 2 × Fin L => z.2.val) hab
          exact Nat.add_right_cancel he))⟩
  let jd : Fin (L + t - h) := ⟨j.val + d.val, by have := j.isLt; have := d.isLt; omega⟩
  have hshift (z : Fin 2 × Fin (h + 1)) :
      (K1_6.shifts (planePair Q) L s) (e z) d = Q z := by
    change (planePair Q z.1 * Polynomial.X ^ d.val).coeff (z.2.val + d.val) = Q z
    rw [coeff_mul_X_pow, planePair, Principal.assemble_coeff]
  have hzero (z : Fin 2 × Fin L) (hz : z ∉ Set.range e) :
      (K1_6.shifts (planePair Q) L s) z d = 0 := by
    change (planePair Q z.1 * Polynomial.X ^ d.val).coeff z.2.val = 0
    by_cases hlo : z.2.val < d.val
    · rw [coeff_mul_X_pow', ite_eq_right (not_le.mpr hlo)]
    · have hhi : h < z.2.val - d.val := by
        by_contra! hh
        apply hz
        refine ⟨(z.1, ⟨z.2.val - d.val, by omega⟩), Prod.ext rfl (Fin.ext ?_)⟩
        change z.2.val - d.val + d.val = z.2.val
        omega
      have he : z.2.val - d.val + d.val = z.2.val := Nat.sub_add_cancel (by omega)
      rw [← he, coeff_mul_X_pow]
      exact coeff_eq_zero_of_natDegree_lt ((Principal.assemble_natDegree_le _).trans_lt hhi)
  change (∑ z, K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j) = 0
  have hsum : (∑ z : Fin 2 × Fin L, K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j) =
      ∑ z : Fin 2 × Fin (h + 1), K1_6.shifts (planePair Q) L s (e z) d *
        planeStack p x u v L t (e z) j := by
    let f (z : Fin 2 × Fin L) := K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j
    calc
      _ = ∑ z ∈ Finset.univ.map e, f z := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro z _ hz
        change K1_6.shifts (planePair Q) L s z d * planeStack p x u v L t z j = 0
        rw [hzero z (fun hm => hz (by
          obtain ⟨w, rfl⟩ := hm
          exact Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩)), zero_mul]
      _ = _ := Finset.sum_map _ e f
  rw [hsum]
  have hk := congrFun hQ jd
  change (∑ z, planeSlice p x u v (L + t) h jd z * Q z) = 0 at hk
  rw [← hk]
  apply Finset.sum_congr rfl
  intro z _
  rw [hshift, mul_comm]
  congr 1
  change planeSyndrome p x u v z.1 (z.2.val + d.val + j.val) =
    planeSyndrome p x u v z.1 (z.2.val + (j.val + d.val))
  congr 1
  omega

end

end K21_11_1
end Port_K1_11_1Coefficients

section Port_K1_11_1Native
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000

namespace K21_11_1

noncomputable section

open Polynomial Matrix FrobeniusLocator K21 ProximityPrize.Benchmark
open scoped BigOperators

private theorem graph_syndrome {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (b : Fin 2) (j : ℕ) :
    graph q (planeSyndrome q x u v b j) = Principal.parameterSyndromes q x u v b j := by
  fin_cases b <;> simp [graph, planeSyndrome, Principal.parameterSyndromes]

private theorem syndrome_degree {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (b i : Fin 2) (j : ℕ) :
    (planeSyndrome q x u v b j).degreeOf i ≤ if b = i then 1 else 0 := by
  have h (a c : F) :
      (MvPolynomial.C a + MvPolynomial.X b * MvPolynomial.C c).degreeOf i ≤
        if b = i then 1 else 0 := by
    apply (MvPolynomial.degreeOf_add_le i _ _).trans
    apply max_le
    · simp
    · apply (MvPolynomial.degreeOf_mul_C_le _ _ _).trans
      rw [MvPolynomial.degreeOf_X]
      by_cases he : b = i
      · simp [he]
      · simp [he, Ne.symm he]
  unfold planeSyndrome
  by_cases hb : b = 0
  · simpa only [hb, ite_true] using h (syndrome x u j) (syndrome x v j)
  · simpa only [hb, ite_false] using h (syndrome x u j ^ q) (syndrome x v j ^ q)

private theorem graph_slice_map {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (m h : ℕ) :
    (planeSlice q x u v m h).map
        ((algebraMap F[X] (GenericLayer.GenericField F)).comp (graph q).toRingHom) =
      (Strata.parameterRelation q x u v m h).map (algebraMap F[X] (GenericLayer.GenericField F)) := by
  apply Matrix.ext
  intro j b
  change algebraMap F[X] (GenericLayer.GenericField F)
      (graph q (planeSyndrome q x u v b.1 (b.2.val + j.val))) =
    algebraMap F[X] (GenericLayer.GenericField F)
      (Principal.parameterSyndromes q x u v b.1 (b.2.val + j.val))
  rw [graph_syndrome]

private theorem graph_stack_map {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (x u v : ι → F) (L t : ℕ) :
    (planeStack q x u v L t).map
        ((algebraMap F[X] (GenericLayer.GenericField F)).comp (graph q).toRingHom) =
      (stacked q x u v L t).map (algebraMap F[X] (GenericLayer.GenericField F)) := by
  apply Matrix.ext
  intro b j
  change algebraMap F[X] (GenericLayer.GenericField F)
      (graph q (planeSyndrome q x u v b.1 (b.2.val + j.val))) =
    algebraMap F[X] (GenericLayer.GenericField F)
      (Principal.parameterSyndromes q x u v b.1 (b.2.val + j.val))
  rw [graph_syndrome]


theorem first_slice_nullity (u : Words) (T : TwoActive u) :
    GenericLayer.genericNullity
      (Strata.parameterRelation p node (u 0) (u 1) 131072 T.height) = 1 :=
  Strata.generic_relation_line_of_level p node (u 0) (u 1) 131072 T.a T.b T.c
    T.top (by exact T.degreeSum) T.ab (T.active.trans_lt T.inactive)
    (by have := T.inactive; omega) T.level

theorem plane_first_slice_nullity (u : Words) (T : TwoActive u) (hh : T.height ≤ 32872) :
    Module.finrank (PlaneField K) (LinearMap.ker
      ((planeSlice p node (u 0) (u 1) 131072 T.height).map
        (algebraMap (Seeds K) (PlaneField K))).mulVecLin) = 1 := by
  let A := planeSlice p node (u 0) (u 1) 131072 T.height
  have hdeg (j : Fin (131072 - T.height)) (b : Fin 2 × Fin (T.height + 1)) :
      (A j b).degreeOf 0 ≤ if b.1 = 0 then 1 else 0 :=
    syndrome_degree p node (u 0) (u 1) b.1 0 _
  have he := rank_graph p (by decide) (by have hp : p = 2130706433 := rfl; omega) A hdeg
  change (A.map (algebraMap (Seeds K) (PlaneField K))).rank =
    ((planeSlice p node (u 0) (u 1) 131072 T.height).map _).rank at he
  rw [graph_slice_map] at he
  have hn := GenericLayer.rank_add_nullity
    (Strata.parameterRelation p node (u 0) (u 1) 131072 T.height)
  rw [first_slice_nullity u T] at hn
  apply GenericRank.nullity_one_of_rank
  change (A.map (algebraMap (Seeds K) (PlaneField K))).rank + 1 = _
  rw [he]
  exact hn

theorem plane_stack_rank (u : Words) :
    ((planeStack p node (u 0) (u 1) 49097 81975).map
      (algebraMap (Seeds K) (PlaneField K))).rank = stackRank u := by
  let A := planeStack p node (u 0) (u 1) 49097 81975
  have hdeg (j : Fin 81976) (b : Fin 2 × Fin 49097) :
      (A.transpose j b).degreeOf 0 ≤ if b.1 = 0 then 1 else 0 :=
    syndrome_degree p node (u 0) (u 1) b.1 0 _
  have he := rank_graph p (by decide) (by decide) A.transpose hdeg
  rw [Matrix.transpose_map, Matrix.transpose_map, Matrix.rank_transpose, Matrix.rank_transpose] at he
  change ((planeStack p node (u 0) (u 1) 49097 81975).map _).rank =
    ((planeStack p node (u 0) (u 1) 49097 81975).map _).rank at he
  rw [graph_stack_map] at he
  exact he


theorem plane_stack_degree (u : Words) (b : Fin 2 × Fin 49097) (j : Fin 81976)
    (i : Fin 2) :
    (planeStack p node (u 0) (u 1) 49097 81975 b j).degreeOf i ≤
      if b.1 = i then 1 else 0 :=
  syndrome_degree p node (u 0) (u 1) b.1 i _

private theorem map_syndrome {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (f : F →+* E)
    (x w : ι → F) (j : ℕ) :
    f (syndrome x w j) = syndrome (fun i => f (x i)) (fun i => f (w i)) j := by
  simp only [syndrome, weight, map_sum, map_mul, map_pow, map_inv₀, map_prod, map_sub]

/-- The actual supplied relation is in the first slice, by its node identity
and the vanishing dual checks of its output. -/
private theorem certificate_kernel {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) [ExpChar F q] (x u v : ι → F) (hx : Function.Injective x)
    (hfix : ∀ i, x i ^ q = x i) (k m h : ℕ)
    (hkm : k + m = Fintype.card ι)
    (R : Strata.PolynomialRelationCertificate q x u v k h) :
    ((Strata.parameterRelation q x u v m h).map
      (algebraMap F[X] (GenericLayer.GenericField F))).mulVec
      (fun j => algebraMap F[X] (GenericLayer.GenericField F) (R.coefficients j)) = 0 := by
  classical
  let E := GenericLayer.GenericField F
  let φ := algebraMap F[X] E
  let f := φ.comp Polynomial.C
  let y := fun i => f (x i)
  let z := φ Polynomial.X
  let w : Fin 2 → ι → E := fun b i =>
    if b = 0 then f (u i) + z * f (v i)
    else f (u i ^ q) + z ^ q * f (v i ^ q)
  let P (b : Fin 2) : E[X] := (Principal.assemble (fun j => R.coefficients (b, j))).map φ
  have hmoment (b : Fin 2) (j : ℕ) :
      φ (Principal.parameterSyndromes q x u v b j) = syndrome y (w b) j := by
    by_cases hb : b = 0
    · simp only [Principal.parameterSyndromes, hb, ite_true, map_add, map_mul]
      change f (syndrome x u j) + z * f (syndrome x v j) = _
      rw [map_syndrome, map_syndrome]
      simpa only [w, hb, ite_true, one_mul] using
        (Principal.syndrome_linear y (fun i => f (u i)) (fun i => f (v i)) 1 z j).symm
    · simp only [Principal.parameterSyndromes, hb, ite_false, map_add, map_mul]
      rw [φ.map_pow Polynomial.X]
      change f (syndrome x u j ^ q) + z ^ q * f (syndrome x v j ^ q) = _
      rw [← syndrome_frobenius q x hfix, ← syndrome_frobenius q x hfix,
        map_syndrome, map_syndrome]
      simpa only [w, hb, ite_false, one_mul] using
        (Principal.syndrome_linear y (fun i => f (u i ^ q)) (fun i => f (v i ^ q)) 1 (z ^ q) j).symm
  have hnodes (i : ι) :
      (P 0).eval (y i) * w 0 i + (P 1).eval (y i) * w 1 i =
        (R.output.map φ).eval (y i) := by
    have he := congrArg φ (R.nodes i)
    simpa only [P, y, f, RingHom.comp_apply, z, w, zero_ne_one, one_ne_zero,
      ite_true, ite_false, map_add, map_mul, map_pow, eval_map_apply] using he
  have hP (b : Fin 2) : (P b).natDegree ≤ h := natDegree_map_le.trans (R.x_degree b)
  rw [Strata.parameterRelation_map]
  apply (Strata.relation_equations _ m h _).mpr
  intro j
  have hcoeff (b : Fin 2) (l : Fin (h + 1)) :
      φ (R.coefficients (b, l)) = (P b).coeff l.val := by
    change φ (R.coefficients (b, l)) =
      ((Principal.assemble (fun j => R.coefficients (b, j))).map φ).coeff l.val
    rw [coeff_map, Principal.assemble_coeff]
  change (∑ b : Fin 2, ∑ l : Fin (h + 1),
    φ (R.coefficients (b, l)) * φ (Principal.parameterSyndromes q x u v b (l.val + j.val))) = 0
  simp only [Fin.sum_univ_two, hmoment, hcoeff]
  change (∑ l : Fin (h + 1), (P 0).coeff l.val * syndrome y (w 0) (l.val + j.val)) +
    (∑ l : Fin (h + 1), (P 1).coeff l.val * syndrome y (w 1) (l.val + j.val)) = 0
  rw [← Strata.syndrome_polynomial_multiple y (w 0) _ _ _ (hP 0),
    ← Strata.syndrome_polynomial_multiple y (w 1) _ _ _ (hP 1)]
  have hlin := Principal.syndrome_linear y
    (fun i => (P 0).eval (y i) * w 0 i) (fun i => (P 1).eval (y i) * w 1 i) 1 1 j.val
  simp only [one_mul] at hlin
  rw [← hlin]
  simp_rw [hnodes]
  exact Strata.syndrome_eval_zero y (f.injective.comp hx) _ (k + h) j.val
    (degree_map_le.trans_lt R.output_degree) (by have := j.isLt; omega)

/-- The graph image is a polynomial multiple of the given primitive
graph relation. The same seed factor multiplies both streams. -/
theorem graph_content (u : Words) (T : TwoActive u) (R : Relation T)
    (Q : Fin 2 × Fin (T.height + 1) → Seeds K)
    (hQ : (planeSlice p node (u 0) (u 1) 131072 T.height).mulVec Q = 0)
    (hgraph : (fun j => graph p (Q j)) ≠ 0) :
    ∃ c : K[X], c ≠ 0 ∧ ∀ j, graph p (Q j) = c * R.coefficients j := by
  classical
  let f := algebraMap K[X] Frac
  let M := (Strata.parameterRelation p node (u 0) (u 1) 131072 T.height).map f
  let E := fun j => f (R.coefficients j)
  let V := fun j => f (graph p (Q j))
  obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout R.coefficients).mp R.primitive
  have hinj := IsFractionRing.injective K[X] Frac
  have hE : E ≠ 0 := by
    intro he
    have hzero (j : Fin 2 × Fin (T.height + 1)) : R.coefficients j = 0 :=
      hinj ((congrFun he j).trans (map_zero f).symm)
    simp only [hzero, mul_zero, Finset.sum_const_zero, zero_ne_one] at ha
  have hME : M.mulVec E = 0 :=
    certificate_kernel p node (u 0) (u 1) IRSProfile.domain.injective
      Native.native_domain_fixed 131072 131072 T.height
      (by rw [IRSProfile.card_index]) R
  have hMV : M.mulVec V = 0 := by
    change ((Strata.parameterRelation p node (u 0) (u 1) 131072 T.height).map f).mulVec V = 0
    rw [← graph_slice_map]
    change ((planeSlice p node (u 0) (u 1) 131072 T.height).map
      (f.comp (graph p).toRingHom)).mulVec
      (fun j => (f.comp (graph p).toRingHom) (Q j)) = 0
    rw [mulVec_map, hQ]
    funext j
    rw [Pi.zero_apply, map_zero, Pi.zero_apply]
  obtain ⟨b, hb⟩ := GenericRank.kernel_line_of_finrank M
    (first_slice_nullity u T) E hE hME V hMV
  let c := ∑ j, a j * graph p (Q j)
  have hc : f c = b := by
    have hbe := congrArg f ha
    simp only [map_sum, map_mul, map_one] at hbe
    simp only [c, map_sum, map_mul]
    have he (j : Fin 2 × Fin (T.height + 1)) : f (graph p (Q j)) = b * f (R.coefficients j) :=
      congrFun hb j
    simp_rw [he, mul_left_comm (f (a _)) b, ← Finset.mul_sum, hbe, mul_one]
  have he (j : Fin 2 × Fin (T.height + 1)) : graph p (Q j) = c * R.coefficients j := by
    apply hinj
    rw [map_mul, hc]
    exact congrFun hb j
  refine ⟨c, ?_, he⟩
  intro hzero
  apply hgraph
  funext j
  rw [he, hzero, zero_mul, Pi.zero_apply]

end

end K21_11_1
end Port_K1_11_1Native

section Port_K1_11Marks
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K21_11
noncomputable section

open K21 FrobeniusLocator

def nativePuncture (deleted : Finset I) : Puncture deleted := by
  classical
  let kept := Finset.univ \ deleted
  let idx := kept.equivFin.symm
  refine ⟨kept.card, idx.toEmbedding.trans (Function.Embedding.subtype _), ?_, ?_⟩
  · intro i
    constructor
    · rintro ⟨j, rfl⟩
      exact (Finset.mem_sdiff.mp (idx j).property).2
    · intro hi
      let old : kept := ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
      exact ⟨idx.symm old, congrArg Subtype.val (idx.apply_symm_apply old)⟩
  · simpa only [kept, Finset.card_univ, ProximityPrize.Benchmark.IRSProfile.card_index] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ deleted)

def selectMarks {u : Words} {T : TwoActive u} {R : Relation T} (D : Reduction u T R)
    {Γ : Finset K} (hΓ : BadFamily u Γ) (hn : ∀ γ ∈ Γ, Normal u γ) :
    Marks u (fixedNodes R) Γ where
  mark γ hγ := Classical.choice (K21.bad_mark u Γ hΓ γ hγ)
  survives γ hγ i hi hid :=
    (D.deleted_error γ (hn γ hγ) _ i hid)
      ((Classical.choice (K21.bad_mark u Γ hΓ γ hγ)).hits i hi)

def indexedSupport {deleted : Finset I} (P : Puncture deleted) (S : Finset I) : Finset (Fin P.N) :=
  Finset.univ.filter fun i => P.index i ∈ S

theorem mem_indexedSupport {deleted : Finset I} (P : Puncture deleted) (S : Finset I)
    (i : Fin P.N) : i ∈ indexedSupport P S ↔ P.index i ∈ S := by simp [indexedSupport]

theorem indexedSupport_card {deleted : Finset I} (P : Puncture deleted) (S : Finset I)
    (hS : ∀ i ∈ S, i ∉ deleted) : (indexedSupport P S).card = S.card := by
  have heq : (indexedSupport P S).map P.index = S := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact (mem_indexedSupport P S j).mp hj
    · intro hi
      obtain ⟨j, hj⟩ := (P.retained i).mpr (hS i hi)
      refine Finset.mem_map.mpr ⟨j, (mem_indexedSupport P S j).mpr ?_, hj⟩
      rwa [hj]
  calc
    (indexedSupport P S).card = ((indexedSupport P S).map P.index).card := (Finset.card_map _).symm
    _ = S.card := congrArg Finset.card heq

theorem mark_degree {u : Words} {γ : K} (M : BadMark u γ) :
    M.decoder.natDegree ≤ 131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ M.degree

theorem correctOn_mark {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {γ : K} (M : BadMark u γ) :
    correctOn u P M.decoder (M.decoder.map twist) γ (γ ^ p) (indexedSupport P M.support) := by
  intro i hi
  have h := M.hits (P.index i) ((mem_indexedSupport P M.support i).mp hi)
  refine ⟨h, ?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i) ^ p + γ ^ p * u 1 (P.index i) ^ p
  rw [Strata.eval_coefficient_map twist M.decoder _ (Native.native_domain_fixed (P.index i)), h]
  simp only [map_add, map_mul, K21.twist, frobenius_def]

end
end K21_11
end Port_K1_11Marks

section Port_K1_11_2Defs
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K21_11_2
noncomputable section

open K21 K21_11 MvPolynomial

def OmitsMessages {F : Type*} [Field F] (Q : MvPolynomial (Fin 5) F) : Prop :=
  Q.degreeOf 1 = 0 ∧ Q.degreeOf 2 = 0

/-- Specialize the independent parameters to Z and Z^q. -/
def graph {F : Type*} [Field F] (q : ℕ) :
    MvPolynomial (Fin 5) F →ₐ[F] Polynomial (Polynomial F) :=
  aeval ![Polynomial.X, 0, 0, Polynomial.C Polynomial.X, (Polynomial.C Polynomial.X)^q]

def nodeWordImages {F : Type*} [Field F] (x a b c d : F) : Fin 5 → MvPolynomial (Fin 5) F :=
  ![MvPolynomial.C x, MvPolynomial.C a + MvPolynomial.X 3 * MvPolynomial.C b,
    MvPolynomial.C c + MvPolynomial.X 4 * MvPolynomial.C d, MvPolynomial.X 3, MvPolynomial.X 4]

/-- Evaluate the coordinate and both received pencils while retaining the plane parameters. -/
def nodeWordMap {F : Type*} [Field F] (x a b c d : F) :
    MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval (nodeWordImages x a b c d)

def sWeight {F : Type*} [Field F] (U V : MvPolynomial (Fin 5) F) : ℕ :=
  max (1 + U.degreeOf 3) (V.degreeOf 3)

def tWeight {F : Type*} [Field F] (U V : MvPolynomial (Fin 5) F) : ℕ :=
  max (U.degreeOf 4) (1 + V.degreeOf 4)

/-- Reduced plane pair, still carrying the scalar content of the graph lift. -/
structure ReducedPair {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : IndependentLift R) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : OmitsMessages U
  V_omits : OmitsMessages V
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  relPrime : IsRelPrime U V
  height : max (U.degreeOf 0) (V.degreeOf 0) = D.height
  boxes : U.degreeOf 3 ≤ 2 ∧ U.degreeOf 4 ≤ 3 ∧ V.degreeOf 3 ≤ 3 ∧ V.degreeOf 4 ≤ 2
  graphU : graph p U = Polynomial.C A.content * D.U
  graphV : graph p V = Polynomial.C A.content * D.V

/-- The output of the reduced plane relation at the retained original nodes. -/
structure PlaneOutput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (H : ℕ) (U V : MvPolynomial (Fin 5) K) where
  W : MvPolynomial (Fin 5) K
  omits : OmitsMessages W
  height : W.degreeOf 0 ≤ 131071 + H
  degreeS : W.degreeOf 3 ≤ sWeight U V
  degreeT : W.degreeOf 4 ≤ tWeight U V
  node : ∀ i : Fin P.N,
    nodeWordMap (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
      (u 0 (P.index i)^p) (u 1 (P.index i)^p) (U * MvPolynomial.X 1 + V * MvPolynomial.X 2 - W) = 0

end
end K21_11_2
end Port_K1_11_2Defs

section Port_K1_11_2Contact
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K21_11_2
noncomputable section
open K21_11 MvPolynomial
variable {F : Type*} [Field F]
def contactConstant : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval ![0,0,0,MvPolynomial.X 3,MvPolynomial.X 4]

theorem contactConstant_monomial (e : Fin 5 →₀ ℕ) (a : F) :
    contactConstant (monomial e a)=if e.weight contactWeight<1 then monomial e a else 0 := by
  classical
  rw [contactConstant,aeval_monomial]
  by_cases h0 : e 0=0 <;> by_cases h1 : e 1=0 <;> by_cases h2 : e 2=0 <;>
    simp [Finsupp.prod_fintype,Fin.prod_univ_succ,contactWeight,weight5,
      h0,h1,h2,monomial_eq]

theorem truncation_one_monomial (e : Fin 5 →₀ ℕ) (a : F) :
    weightedTruncation contactWeight 1 (monomial e a)=
      if e.weight contactWeight<1 then monomial e a else 0 := by
  classical
  ext f
  by_cases hfe : e=f
  · subst f
    split_ifs <;> simp_all [coeff_weightedTruncation,MvPolynomial.coeff_monomial]
  · split_ifs <;> simp_all [coeff_weightedTruncation,MvPolynomial.coeff_monomial]

theorem contactConstant_eq_truncation (P : MvPolynomial (Fin 5) F) :
    contactConstant P=weightedTruncation contactWeight 1 P := by
  induction P using MvPolynomial.induction_on' with
  | monomial e a => rw [contactConstant_monomial,truncation_one_monomial]
  | add P Q hp hq => simp only [map_add,hp,hq]

/-- A nonzero contact partial derivative at the parameter-polynomial node
gives contact order one, even when the derivative vanishes at some parameter points. -/
theorem exact_contact_one_of_gradient (P : MvPolynomial (Fin 5) F) (i : Fin 5)
    (hi : contactWeight i=1) (hvalue : contactConstant P=0)
    (hgradient : contactConstant (pderiv i P)≠0) :
    (contactLift contactWeight P).natTrailingDegree=1 := by
  have hzero : P∈restrictWeightedOrder contactWeight 1 := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mp
    rwa [← contactConstant_eq_truncation]
  obtain ⟨e,he⟩ := support_nonempty.mpr hgradient
  have hec := mem_support_iff.mp he
  rw [contactConstant_eq_truncation,coeff_weightedTruncation] at hec
  have heweight : e.weight contactWeight<1 := by
    by_contra hn
    exact hec (ite_eq_right hn)
  rw [ite_eq_left heweight,coeff_pderiv] at hec
  have hcoeff : P.coeff (e+Finsupp.single i 1)≠0 := left_ne_zero_of_mul hec
  have hweight : (e+Finsupp.single i 1).weight contactWeight=1 := by
    rw [map_add,Finsupp.weight_single,one_smul,hi]
    omega
  exact contact_order_one_of_coefficient contactWeight P hzero _ hweight hcoeff

theorem pderiv_zero_of_degree_zero (i : Fin 5) (P : MvPolynomial (Fin 5) F)
    (hP : P.degreeOf i=0) : pderiv i P=0 := by
  ext e
  rw [coeff_pderiv]
  have hc : P.coeff (e+Finsupp.single i 1)=0 := by
    apply notMem_support_iff.mp
    apply notMem_support_of_degreeOf_lt i
    simp [hP]
  simp [hc]

theorem linear_form_message_derivatives (U V R : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hR : OmitsMessages R) :
    pderiv 1 (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R)=U ∧ pderiv 2 (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R)=V := by
  constructor <;> simp [pderiv_zero_of_degree_zero _ U hU.1,
    pderiv_zero_of_degree_zero _ U hU.2,pderiv_zero_of_degree_zero _ V hV.1,
    pderiv_zero_of_degree_zero _ V hV.2,pderiv_zero_of_degree_zero _ R hR.1,
    pderiv_zero_of_degree_zero _ R hR.2]

/-- Affine node translation commutes with each decoder-variable partial
derivative because the two received pencils depend only on the parameters. -/
theorem contactShift_message_derivative (x a b c d : F) (P : MvPolynomial (Fin 5) F)
    (i : Fin 5) (hi : i=1 ∨ i=2) :
    pderiv i (contactShift x a b c d P)=contactShift x a b c d (pderiv i P) := by
  have hvar (j : Fin 5) : pderiv i (contactShift x a b c d (MvPolynomial.X j))=
      contactShift x a b c d (pderiv i (MvPolynomial.X j)) := by
    rcases hi with rfl | rfl
    all_goals fin_cases j <;> simp [contactShift,shiftImages]
  induction P using MvPolynomial.induction_on with
  | C r => simp [contactShift]
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P j hp => simp only [map_mul,pderiv_mul,map_add,hp,hvar]

/-- Compute contact order by differentiating before specializing the parameters. -/
theorem linear_relation_node_contact_one (x a b c d : F)
    (U V R : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hR : OmitsMessages R)
    (hnode : contactConstant (contactShift x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R))=0)
    (hnonzero : contactConstant (contactShift x a b c d U)≠0 ∨
      contactConstant (contactShift x a b c d V)≠0) :
    (contactLift contactWeight (contactShift x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R))).natTrailingDegree=1 := by
  have hd := linear_form_message_derivatives U V R hU hV hR
  rcases hnonzero with hu | hv
  · apply exact_contact_one_of_gradient _ 1 (by decide) hnode
    rw [contactShift_message_derivative x a b c d _ 1 (Or.inl rfl),hd.1]
    exact hu
  · apply exact_contact_one_of_gradient _ 2 (by decide) hnode
    rw [contactShift_message_derivative x a b c d _ 2 (Or.inr rfl),hd.2]
    exact hv

def messageTag (P : MvPolynomial (Fin 5) F) (a b : ℕ) : Prop :=
  ∀ e∈P.support,e 1=a ∧ e 2=b

theorem omitted_message_tag (P : MvPolynomial (Fin 5) F) (hP : OmitsMessages P) : messageTag P 0 0 := by
  rcases hP with ⟨hP1,hP2⟩
  intro e he
  have h1 := le_degreeOf_of_mem_support 1 he
  have h2 := le_degreeOf_of_mem_support 2 he
  exact ⟨by omega,by omega⟩

theorem relatively_prime_not_both_eval_zero {R : Type*} [CommRing R] [IsDomain R]
    (U V : Polynomial R) (hUV : IsRelPrime U V) (x : R) : U.eval x≠0 ∨ V.eval x≠0 := by
  by_contra hn
  push Not at hn
  have hu : Polynomial.X-Polynomial.C x∣U := Polynomial.dvd_iff_isRoot.mpr hn.1
  have hv : Polynomial.X-Polynomial.C x∣V := Polynomial.dvd_iff_isRoot.mpr hn.2
  exact Polynomial.not_isUnit_X_sub_C x (hUV hu hv)

def partialXMap (x : F) : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval ![C x,MvPolynomial.X 1,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

theorem contactConstant_shift (x a b c d : F) (P : MvPolynomial (Fin 5) F) :
    contactConstant (contactShift x a b c d P)=nodeWordMap x a b c d P := by
  rw [contactShift,aeval_eq_bind₁,contactConstant,aeval_bind₁]
  have hf : (fun i => aeval ![0,0,0,MvPolynomial.X 3,MvPolynomial.X 4] (shiftImages x a b c d i))=
      nodeWordImages x a b c d := by
    funext i
    fin_cases i <;> simp [shiftImages,nodeWordImages]
  rw [hf]
  rfl

theorem nodeWord_omitted_eq_partialX (x a b c d : F) (P : MvPolynomial (Fin 5) F)
    (hP : OmitsMessages P) : nodeWordMap x a b c d P=partialXMap x P := by
  change eval₂ C (nodeWordImages x a b c d) P=eval₂ C ![C x,MvPolynomial.X 1,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4] P
  apply eval₂_congr
  intro i e hi hc
  have he : e∈P.support := mem_support_iff.mpr hc
  have ht := omitted_message_tag P hP e he
  have hin : e i≠0 := Finsupp.mem_support_iff.mp hi
  have h1 : i≠1 := by intro hi1; subst i; exact hin ht.1
  have h2 : i≠2 := by intro hi2; subst i; exact hin ht.2
  fin_cases i <;> simp [nodeWordImages] at *

theorem partialX_via_polynomial (x : F) (P : MvPolynomial (Fin 5) F) :
    partialXMap x P=rename Fin.succ ((finSuccEquiv F 4 P).eval (C x)) := by
  have heq : (partialXMap x).toRingHom=
      (rename (Fin.succ : Fin 4 → Fin 5)).toRingHom.comp ((Polynomial.evalRingHom (C x)).comp (finSuccEquiv F 4).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [partialXMap,finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [partialXMap, finSuccEquiv_X_zero]
      · change partialXMap x (MvPolynomial.X j.succ) =
          rename Fin.succ ((finSuccEquiv F 4 (MvPolynomial.X j.succ)).eval (C x))
        rw [finSuccEquiv_X_succ, Polynomial.eval_C, rename_X]
        fin_cases j <;> simp [partialXMap]
  exact RingHom.congr_fun heq P

theorem relatively_prime_polynomial_view (U V : MvPolynomial (Fin 5) F)
    (hUV : IsRelPrime U V) : IsRelPrime (finSuccEquiv F 4 U) (finSuccEquiv F 4 V) := by
  intro d hdU hdV
  have hu : (finSuccEquiv F 4).symm d∣U := by
    obtain ⟨q,hq⟩ := hdU
    refine ⟨(finSuccEquiv F 4).symm q,?_⟩
    apply (finSuccEquiv F 4).injective
    simpa only [map_mul,AlgEquiv.apply_symm_apply] using hq
  have hv : (finSuccEquiv F 4).symm d∣V := by
    obtain ⟨q,hq⟩ := hdV
    refine ⟨(finSuccEquiv F 4).symm q,?_⟩
    apply (finSuccEquiv F 4).injective
    simpa only [map_mul,AlgEquiv.apply_symm_apply] using hq
  have hu' := (hUV hu hv).map (finSuccEquiv F 4).toRingHom
  change IsUnit ((finSuccEquiv F 4) ((finSuccEquiv F 4).symm d)) at hu'
  simpa only [AlgEquiv.apply_symm_apply] using hu'

/-- A common node zero over the parameter ring would make X-x a
common factor of U and V. -/
theorem relatively_prime_node_nondegenerate (x a b c d : F)
    (U V : MvPolynomial (Fin 5) F) (hUV : IsRelPrime U V)
    (hU : OmitsMessages U) (hV : OmitsMessages V) :
    nodeWordMap x a b c d U≠0 ∨ nodeWordMap x a b c d V≠0 := by
  have hn := relatively_prime_not_both_eval_zero (finSuccEquiv F 4 U) (finSuccEquiv F 4 V)
    (relatively_prime_polynomial_view U V hUV) (C x)
  rw [nodeWord_omitted_eq_partialX x a b c d U hU,
    nodeWord_omitted_eq_partialX x a b c d V hV,partialX_via_polynomial,partialX_via_polynomial]
  have hinj : Function.Injective (rename (R:=F) (Fin.succ : Fin 4 → Fin 5)) :=
    rename_injective _ (Fin.succ_injective 4)
  rcases hn with hu | hv
  · left
    exact fun hz => hu (hinj (hz.trans (map_zero _).symm))
  · right
    exact fun hz => hv (hinj (hz.trans (map_zero _).symm))

/-- The plane relation has order one at the node as a formal polynomial
in the two parameters and the three translated contact coordinates. -/
theorem linear_relation_contact_order_one (x a b c d : F)
    (U V R : MvPolynomial (Fin 5) F) (hUV : IsRelPrime U V)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hR : OmitsMessages R)
    (hnode : nodeWordMap x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R)=0) :
    (contactLift contactWeight (contactShift x a b c d (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R))).natTrailingDegree=1 := by
  apply linear_relation_node_contact_one x a b c d U V R hU hV hR
  · rwa [contactConstant_shift]
  · simpa only [contactConstant_shift] using relatively_prime_node_nondegenerate x a b c d U V hUV hU hV

end
end K21_11_2
end Port_K1_11_2Contact

section Port_K1_11Pencil
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace K21_11
noncomputable section

open K21 FrobeniusLocator MvPolynomial
open scoped BigOperators

variable {u : Words} {deleted : Finset I} {P : Puncture deleted}
  {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}

private theorem seed_eq_of_mismatch {F : Type*} [Field F] {s t a b c d : F}
    (hs : a + s * b = c + s * d) (ht : a + t * b = c + t * d)
    (hm : a ≠ c ∨ b ≠ d) : s = t := by
  have hz : (s - t) * (b - d) = 0 := by linear_combination hs - ht
  rcases mul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · have hb := sub_eq_zero.mp h
    exact False.elim (hm.elim
      (fun hne => hne (by simpa only [hb, add_left_inj] using hs))
      (fun hne => hne hb))

private theorem pencil_bad_count (hsub : Λ ⊆ Γ) (P₀ P₁ : Polynomial K)
    (h₀ : P₀.degree < (131072 : ℕ)) (h₁ : P₁.degree < (131072 : ℕ))
    (pencil : ∀ γ (hγ : γ ∈ Λ),
      (F.mark γ (hsub hγ)).decoder = P₀ + Polynomial.C γ * P₁) :
    Λ.card ≤ P.N := by
  classical
  have mismatch (γ : Λ) :
      ∃ i : Fin P.N,
        (P₀.eval (P.nodes i) ≠ u 0 (P.index i) ∨ P₁.eval (P.nodes i) ≠ u 1 (P.index i)) ∧
        P₀.eval (P.nodes i) + (γ : K) * P₁.eval (P.nodes i) =
          u 0 (P.index i) + (γ : K) * u 1 (P.index i) := by
    let M := F.mark γ (hsub γ.property)
    obtain ⟨idx, hi, hm⟩ :
        ∃ idx ∈ M.support, P₀.eval (node idx) ≠ u 0 idx ∨ P₁.eval (node idx) ≠ u 1 idx := by
      by_contra hn
      push Not at hn
      exact M.nonjoint ⟨⟨P₀, h₀, fun j hj => (hn j hj).1⟩, ⟨P₁, h₁, fun j hj => (hn j hj).2⟩⟩
    obtain ⟨i, rfl⟩ := (P.retained idx).mpr (F.survives γ (hsub γ.property) idx hi)
    refine ⟨i, hm, ?_⟩
    have hh := M.hits (P.index i) hi
    change (F.mark (γ : K) (hsub γ.property)).decoder.eval (P.nodes i) = _ at hh
    simpa only [pencil _ γ.property, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C] using hh
  let f : Λ → Fin P.N := fun γ => Classical.choose (mismatch γ)
  have hf : Function.Injective f := by
    intro γ δ he
    apply Subtype.ext
    obtain ⟨hm, hγ⟩ := Classical.choose_spec (mismatch γ)
    have hδ := (Classical.choose_spec (mismatch δ)).2
    change f γ = f δ at he
    change
      (P₀.eval (P.nodes (f γ)) ≠ u 0 (P.index (f γ)) ∨
        P₁.eval (P.nodes (f γ)) ≠ u 1 (P.index (f γ))) at hm
    change P₀.eval (P.nodes (f γ)) + (γ : K) * P₁.eval (P.nodes (f γ)) =
      u 0 (P.index (f γ)) + (γ : K) * u 1 (P.index (f γ)) at hγ
    change P₀.eval (P.nodes (f δ)) + (δ : K) * P₁.eval (P.nodes (f δ)) =
      u 0 (P.index (f δ)) + (δ : K) * u 1 (P.index (f δ)) at hδ
    rw [← he] at hδ
    exact seed_eq_of_mismatch (F := K) hγ hδ hm
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

variable (chart : TaylorChart u P F b Λ)

theorem chart_cut_iff (γ : K) (hγ : γ ∈ Λ) (i : Fin P.N) :
    MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0 ↔
      (F.mark γ (chart.subset hγ)).decoder.eval (P.nodes i) =
        u 0 (P.index i) + γ * u 1 (P.index i) := by
  let val := MvPolynomial.eval (chart.point γ)
  let x := algebraMap K Frac (P.nodes i)
  change val (nodeCut u P chart.numerator chart.denominator i) = 0 ↔ _
  have heval := Polynomial.eval_map_apply val (C x) (p := chart.numerator)
  unfold nodeCut
  change val (chart.numerator.eval (C x) - _) = 0 ↔ _
  rw [map_sub, ← heval]
  change (chart.numerator.map val).eval (val (C x)) - _ = 0 ↔ _
  rw [show val (C x) = x by simp [val], show chart.numerator.map val = _ from chart.reconstruction γ hγ]
  rw [Polynomial.eval_mul, Polynomial.eval_C, show x = algebraMap K Frac (P.nodes i) from rfl,
    Polynomial.eval_map_apply, map_mul, map_add, map_mul]
  simp only [val, eval_C, eval_X, chart.slope γ hγ]
  rw [← map_mul, ← map_add, sub_eq_zero]
  constructor
  · intro h
    exact (algebraMap K Frac).injective (mul_left_cancel₀ (chart.regular γ hγ) h)
  · intro h
    rw [h]

theorem chart_agreements (γ : K) (hγ : γ ∈ Λ) :
    180169 ≤ {i | MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0}.ncard := by
  let M := F.mark γ (chart.subset hγ)
  have hsub : (indexedSupport P M.support : Set (Fin P.N)) ⊆
      {i | MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0} := by
    intro i hi
    exact (chart_cut_iff chart γ hγ i).mpr (M.hits _ ((mem_indexedSupport P M.support i).mp hi))
  have h := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, indexedSupport_card P M.support (F.survives γ (chart.subset hγ))] at h
  exact M.agreement.trans h

theorem chart_persistent (J : Ideal (MvPolynomial (Fin 3) Frac)) (W : Finset K) (hW : W ⊆ Λ)
    (hzero : ∀ γ ∈ W, chart.point γ ∈ zeroLocus Frac J)
    (hpersist : 131072 ≤ {i | nodeCut u P chart.numerator chart.denominator i ∈ J}.ncard) :
    W.card ≤ P.N := by
  classical
  let keep := Finset.univ.filter fun i => nodeCut u P chart.numerator chart.denominator i ∈ J
  have hk : 131072 ≤ keep.card := by
    rw [← Set.ncard_coe_finset]
    exact hpersist.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hk
  let P₀ := Lagrange.interpolate S P.nodes (fun i => u 0 (P.index i))
  let P₁ := Lagrange.interpolate S P.nodes (fun i => u 1 (P.index i))
  have hinj : Set.InjOn P.nodes (S : Set (Fin P.N)) := nodes_injective.injOn
  have hd₀ : P₀.degree < (131072 : ℕ) := by
    simpa only [P₀, hcard] using Lagrange.degree_interpolate_lt (fun i => u 0 (P.index i)) hinj
  have hd₁ : P₁.degree < (131072 : ℕ) := by
    simpa only [P₁, hcard] using Lagrange.degree_interpolate_lt (fun i => u 1 (P.index i)) hinj
  apply pencil_bad_count (P := P) (F := F) (fun _ hg => chart.subset (hW hg)) P₀ P₁ hd₀ hd₁
  intro γ hγ
  let M := F.mark γ (chart.subset (hW hγ))
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (mark_degree M)))
  · rw [hcard]
    have hm : (Polynomial.C γ * P₁).degree ≤ P₁.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a := γ)) P₁.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hd₀ (hm.trans_lt hd₁))
  · intro i hi
    have hcut : nodeCut u P chart.numerator chart.denominator i ∈ J := (Finset.mem_filter.mp (hS hi)).2
    have hz : MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0 :=
      hzero γ hγ _ hcut
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact (chart_cut_iff chart γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi, Lagrange.eval_interpolate_at_node _ hinj hi])

end
end K21_11
end Port_K1_11Pencil

section Port_K1_11_1Encoding
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K21_11_1

noncomputable section

open Polynomial FrobeniusLocator
open scoped BigOperators

variable {F : Type} [Field F]

theorem degreeOf_coordinate {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (b i : Fin 2) (j : Fin (h + 1)) : (Q (b, j)).degreeOf i ≤ blockDegree Q b i :=
  Finset.le_sup (f := fun j : Fin (h + 1) => (Q (b, j)).degreeOf i) (Finset.mem_univ j)

theorem seedPositions_injective : Function.Injective seedPositions := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | contradiction

private theorem rename_degree_zero (a : Seeds F) (i : Fin 5) (hi : i ∉ Set.range seedPositions) :
    (MvPolynomial.rename seedPositions a).degreeOf i = 0 := by
  by_contra h
  obtain ⟨j, _, hej⟩ := MvPolynomial.mem_vars_rename seedPositions a
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr h)
  exact hi ⟨j, hej⟩

private theorem intoFive_degree {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (b : Fin 2) (i : Fin 5) (a d : ℕ)
    (ha : ∀ j : Fin (h + 1), (MvPolynomial.rename seedPositions (Q (b, j))).degreeOf i ≤ a)
    (hd : ∀ j : Fin (h + 1), ((MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) F) ^ j.val).degreeOf i ≤ d) :
    (intoFive (planePair Q b)).degreeOf i ≤ a + d := by
  classical
  simp only [planePair, Principal.assemble, map_sum, intoFive, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_monomial, AlgHom.toRingHom_eq_coe]
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  exact Finset.sup_le fun j _ => (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add (ha j) (hd j))

theorem intoFive_height {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2) :
    (intoFive (planePair Q b)).degreeOf 0 ≤ h := by
  simpa only [zero_add] using intoFive_degree Q b 0 0 h
    (fun j => (rename_degree_zero (Q (b, j)) 0 (by
      rintro ⟨i, hi⟩
      fin_cases i <;> contradiction)).le)
    (fun j => by rw [MvPolynomial.degreeOf_X_self_pow]; omega)

theorem intoFive_seed_degree {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (b i : Fin 2) :
    (intoFive (planePair Q b)).degreeOf (seedPositions i) ≤ blockDegree Q b i := by
  simpa only [add_zero] using intoFive_degree Q b (seedPositions i) (blockDegree Q b i) 0
    (fun j => by rw [MvPolynomial.degreeOf_rename_of_injective seedPositions_injective]; exact degreeOf_coordinate Q b i j)
    (fun j => (MvPolynomial.degreeOf_X_pow_of_ne _ (by fin_cases i <;> decide)).le)

theorem intoFive_omitted {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2)
    (i : Fin 5) (hi : i = 1 ∨ i = 2) :
    (intoFive (planePair Q b)).degreeOf i = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [zero_add] using intoFive_degree Q b i 0 0
    (fun j => (rename_degree_zero (Q (b, j)) i (by
      rintro ⟨l, rfl⟩
      fin_cases l <;> rcases hi with he | he <;> contradiction)).le)
    (fun j => (MvPolynomial.degreeOf_X_pow_of_ne _ (by rcases hi with rfl | rfl <;> decide)).le)

private def fromFive : MvPolynomial (Fin 5) F →ₐ[F] (Seeds F)[X] :=
  MvPolynomial.aeval ![Polynomial.X, 0, 0, Polynomial.C (MvPolynomial.X 0), Polynomial.C (MvPolynomial.X 1)]

private theorem fromFive_rename (a : Seeds F) :
    fromFive (MvPolynomial.rename seedPositions a) = Polynomial.C a := by
  have he : (fromFive (F := F)).toRingHom.comp (MvPolynomial.rename seedPositions).toRingHom =
      Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [fromFive]
    · intro i
      fin_cases i <;> simp [fromFive, seedPositions]
  exact RingHom.congr_fun he a

private theorem fromFive_intoFive (A : (Seeds F)[X]) : fromFive (intoFive A) = A := by
  have he : (fromFive (F := F)).toRingHom.comp intoFive = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a
      change fromFive (intoFive (Polynomial.C a)) = Polynomial.C a
      rw [intoFive, coe_eval₂RingHom, eval₂_C]
      exact fromFive_rename a
    · simp [fromFive, intoFive]
  exact RingHom.congr_fun he A

theorem intoFive_primitive {h : ℕ} (Q : Fin 2 × Fin (h + 1) → Seeds F)
    (hQ : coefficientPrimitive Q) (a : Seeds F)
    (hU : MvPolynomial.rename seedPositions a ∣ intoFive (planePair Q 0))
    (hV : MvPolynomial.rename seedPositions a ∣ intoFive (planePair Q 1)) :
    IsUnit a := by
  have hd (b : Fin 2) : Polynomial.C a ∣ planePair Q b := by
    have hb : MvPolynomial.rename seedPositions a ∣ intoFive (planePair Q b) := by
      fin_cases b
      · exact hU
      · exact hV
    have ht := map_dvd (fromFive (F := F)) hb
    simpa only [fromFive_rename, fromFive_intoFive] using ht
  apply hQ
  rintro ⟨b, j⟩
  simpa only [planePair, Principal.assemble_coeff] using
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mp (hd b) j.val

private def graphFive (q : ℕ) : MvPolynomial (Fin 5) F →ₐ[F] F[X][X] :=
  MvPolynomial.aeval ![Polynomial.X, 0, 0, Polynomial.C (Polynomial.X : F[X]),
    (Polynomial.C (Polynomial.X : F[X])) ^ q]

private theorem graphFive_rename (q : ℕ) (a : Seeds F) :
    graphFive q (MvPolynomial.rename seedPositions a) = Polynomial.C (graph q a) := by
  have he : (graphFive (F := F) q).toRingHom.comp (MvPolynomial.rename seedPositions).toRingHom =
      Polynomial.C.comp (graph q).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [graphFive, graph]
    · intro i
      fin_cases i <;> simp [graphFive, graph, seedPositions]
  exact RingHom.congr_fun he a

theorem graph_intoFive (q : ℕ) (A : (Seeds F)[X]) :
    MvPolynomial.aeval ![Polynomial.X, 0, 0, Polynomial.C (Polynomial.X : F[X]),
      (Polynomial.C (Polynomial.X : F[X])) ^ q] (intoFive A) =
      A.map (graph q).toRingHom := by
  change graphFive q (intoFive A) = _
  have he : (graphFive (F := F) q).toRingHom.comp intoFive = Polynomial.mapRingHom (graph q).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change graphFive q (intoFive (Polynomial.C a)) = (Polynomial.C a).map (graph q).toRingHom
      rw [intoFive, coe_eval₂RingHom, eval₂_C, Polynomial.map_C]
      exact graphFive_rename q a
    · simp [graphFive, intoFive]
  exact RingHom.congr_fun he A

theorem graph_pair {u : K21.Words} {T : K21.TwoActive u} (R : K21.Relation T) (q : ℕ)
    (Q : Fin 2 × Fin (T.height + 1) → Seeds K21.K)
    (c : K21.K[X]) (hQ : ∀ j, graph q (Q j) = c * R.coefficients j)
    (b : Fin 2) :
    (planePair Q b).map (graph q).toRingHom =
      Polynomial.C c * Principal.assemble (fun j => R.coefficients (b, j)) := by
  rw [planePair, Principal.map_assemble]
  change Principal.assemble (fun j => graph q (Q (b, j))) = _
  simp only [hQ, Principal.assemble, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.C_mul_monomial]

end

end K21_11_1
end Port_K1_11_1Encoding

section Port_K1_11_3Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K21_11_3
noncomputable section

open K21 K21_11 MvPolynomial

/-- Derivatives in the decoder coordinate, leaving the two seeds independent. -/
def derivativeChart {F : Type*} [CommRing F] (G : MvPolynomial (Fin 4) F) (j : ℕ) :
    MvPolynomial (Fin 4) F :=
  (fun H : MvPolynomial (Fin 4) F => pderiv 1 H)^[j] G

/-- At the generic evaluation coordinate, the marked decoder is a simple root of the chart. -/
def SimpleRoot {F : Type*} [Field F] (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) : Prop :=
  aeval (scalarImages D s t) G = 0 ∧
    aeval (scalarImages D s t) (pderiv 1 G) ≠ 0

/-- The polynomial derivation along an implicit branch, multiplied by its separant. -/
def implicitDeriv {F : Type*} [CommRing F] (G H : MvPolynomial (Fin 4) F) :
    MvPolynomial (Fin 4) F :=
  pderiv 1 G * pderiv 0 H - pderiv 0 G * pderiv 1 H

/-- Numerator of ordinary derivative order n+1, with separant exponent 2n+1. -/
def implicitNumerator {F : Type*} [CommRing F] (G : MvPolynomial (Fin 4) F) :
    ℕ → MvPolynomial (Fin 4) F
  | 0 => -pderiv 0 G
  | n + 1 =>
    pderiv 1 G * implicitDeriv G (implicitNumerator G n) -
      C (↑(2 * n + 1) : F) * implicitNumerator G n * implicitDeriv G (pderiv 1 G)

/-- Taylor coefficient with the common separant power 2w−1 cleared. -/
def paddedTaylorCoeff {F : Type*} [Field F] (G : MvPolynomial (Fin 4) F)
    (w : ℕ) : ℕ → MvPolynomial (Fin 4) F
  | 0 => MvPolynomial.X 1 * pderiv 1 G ^ (2 * w - 1)
  | n + 1 =>
    C ((↑(Nat.factorial (n + 1)) : F)⁻¹) *
      implicitNumerator G n * pderiv 1 G ^ (2 * w - 1 - (2 * n + 1))

end
end K21_11_3
end Port_K1_11_3Defs

section Port_K1_11_1Height
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K21_11_1

noncomputable section

open Polynomial FrobeniusLocator K21
open scoped BigOperators

private theorem graph_binomial {F : Type} [Field F] (q r : ℕ) (hr : r ≠ 0)
    (A : Seeds F) (h : ∀ e ∈ A.support, graphExponent q e = 0 ∨ graphExponent q e = r) :
    ∃ a b : F, graph q A = Polynomial.C a + Polynomial.X ^ r * Polynomial.C b := by
  classical
  let a (e : Fin 2 →₀ ℕ) := if graphExponent q e = 0 then A.coeff e else 0
  let b (e : Fin 2 →₀ ℕ) := if graphExponent q e = 0 then 0 else A.coeff e
  refine ⟨∑ e ∈ A.support, a e, ∑ e ∈ A.support, b e, ?_⟩
  calc
    _ = ∑ e ∈ A.support, graph q (MvPolynomial.monomial e (A.coeff e)) := by
      conv_lhs => rw [A.as_sum, map_sum]
    _ = ∑ e ∈ A.support, (Polynomial.C (a e) + Polynomial.X ^ r * Polynomial.C (b e)) := by
      apply Finset.sum_congr rfl
      intro e he
      rcases h e he with he₀ | he₁
      · simp [a, b, graph_monomial, he₀]
      · simp [a, b, graph_monomial, he₁, hr, mul_comm (Polynomial.X ^ r), C_mul_X_pow_eq_monomial]
    _ = _ := by rw [map_sum, map_sum, Finset.mul_sum, Finset.sum_add_distrib]

/-- A block affine in the opposite parameter becomes affine in the
corresponding graph monomial. -/
private theorem graph_affine_block {F : Type} [Field F] {h : ℕ} (q : ℕ) (hq : 0 < q)
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2)
    (h0 : blockDegree Q b b = 0) (h1 : blockDegree Q b (1 - b) ≤ 1) :
    ∃ a d : F[X], (planePair Q b).map (graph q).toRingHom =
      a.map Polynomial.C + (Polynomial.C (Polynomial.X : F[X])) ^ (if b = 0 then q else 1) * d.map Polynomial.C := by
  classical
  let r : ℕ := if b = 0 then q else 1
  have hr : r ≠ 0 := by
    dsimp only [r]
    split_ifs <;> omega
  have hc (j : Fin (h + 1)) :
      ∃ a d : F, graph q (Q (b, j)) = Polynomial.C a + Polynomial.X ^ r * Polynomial.C d := by
    apply graph_binomial q r hr
    intro e he
    have he₀ : e b = 0 :=
      Nat.eq_zero_of_le_zero ((MvPolynomial.le_degreeOf_of_mem_support b he).trans ((degreeOf_coordinate Q b b j).trans h0.le))
    have he₁ : e (1 - b) ≤ 1 :=
      (MvPolynomial.le_degreeOf_of_mem_support _ he).trans ((degreeOf_coordinate Q b (1 - b) j).trans h1)
    have hi : e (1 - b) = 0 ∨ e (1 - b) = 1 := by omega
    rcases hi with hi | hi <;> fin_cases b
    · left
      change e 0 = 0 at he₀
      change e 1 = 0 at hi
      simp [graphExponent, he₀, hi]
    · left
      change e 1 = 0 at he₀
      change e 0 = 0 at hi
      simp [graphExponent, he₀, hi]
    · right
      change e 0 = 0 at he₀
      change e 1 = 1 at hi
      simp [r, graphExponent, he₀, hi]
    · right
      change e 1 = 0 at he₀
      change e 0 = 1 at hi
      simp [r, graphExponent, he₀, hi]
  choose a d had using hc
  refine ⟨Principal.assemble a, Principal.assemble d, ?_⟩
  rw [planePair, Principal.map_assemble, Principal.map_assemble, Principal.map_assemble]
  simp only [Principal.assemble, Finset.mul_sum, ← Polynomial.C_pow]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [C_mul_monomial]
  change Polynomial.monomial j.val (graph q (Q (b, j))) = _
  rw [had j, map_add]

private theorem affine_columns_dependent {F : Type} [Field F] (q : ℕ) (A B : F[X])
    (a d c e : F) (hn : a ≠ 0 ∨ d ≠ 0)
    (he : (Polynomial.C c + Polynomial.X * Polynomial.C e) * A =
      (Polynomial.C a + Polynomial.X ^ q * Polynomial.C d) * B) :
    Module.finrank F (Submodule.span F (Set.range
      (![A, Polynomial.X * A, B, Polynomial.X ^ q * B] : Fin 4 → F[X]))) ≠ 4 := by
  intro hr
  let f : Fin 4 → F[X] := ![A, Polynomial.X * A, B, Polynomial.X ^ q * B]
  have hli : LinearIndependent F f := linearIndependent_iff_card_eq_finrank_span.mpr
    (by simpa only [Fintype.card_fin, Set.finrank, f] using hr.symm)
  let w : Fin 4 → F := ![c, e, -a, -d]
  have hw : (∑ j, w j • f j) = 0 := by
    simp only [w, f, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Polynomial.smul_eq_C_mul, map_neg]
    linear_combination he
  have hz := Fintype.linearIndependent_iff.mp hli w hw
  have hz₂ : -a = 0 := hz 2
  have hz₃ : -d = 0 := hz 3
  rcases hn with ha | hd
  · exact ha (neg_eq_zero.mp hz₂)
  · exact hd (neg_eq_zero.mp hz₃)

private def swapEmbed : Bivar →+* Frac[X] :=
  (Polynomial.mapRingHom (algebraMap K[X] Frac)).comp (Polynomial.Bivariate.swap (R := K)).toRingHom

private theorem swapEmbed_lift (A : K[X]) :
    swapEmbed (liftX A) = Polynomial.C (algebraMap K[X] Frac A) := by
  change (Polynomial.Bivariate.swap (A.map Polynomial.C)).map (algebraMap K[X] Frac) = _
  rw [Polynomial.Bivariate.swap_map_C, Polynomial.map_C]

private theorem swapEmbed_seed : swapEmbed seed = Polynomial.X := by
  change (Polynomial.Bivariate.swap (R := K) (Polynomial.C Polynomial.X)).map
    (algebraMap K[X] Frac) = _
  rw [Polynomial.Bivariate.swap_X, Polynomial.map_X]

private theorem exclude_affine_shapes {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (q : ℕ) (hr : K21_8.columnRankAt q D.U D.V = 4)
    (s a d c e : K[X]) (hs : s ≠ 0)
    (hU : Polynomial.C s * leftU R = liftX a + seed ^ q * liftX d)
    (hV : Polynomial.C s * leftV R = liftX c + seed * liftX e) : False := by
  have hUleft : leftU R ≠ 0 := by
    rw [D.U_factor]
    exact mul_ne_zero ((Polynomial.map_ne_zero_iff C_injective).mpr (locator_monic node (fixedNodes R)).ne_zero) D.U_ne
  have hn : a ≠ 0 ∨ d ≠ 0 := by
    by_contra! h
    have he : Polynomial.C s * leftU R = 0 := by
      rw [hU, h.1, h.2]
      simp [liftX]
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hs) hUleft) he
  have hcross : (liftX c + seed * liftX e) * D.U =
      (liftX a + seed ^ q * liftX d) * D.V := by
    rw [← hV, ← hU, D.U_factor, D.V_factor]
    ring
  have hφ := congrArg swapEmbed hcross
  simp only [map_mul, map_add, map_pow, swapEmbed_lift, swapEmbed_seed] at hφ
  let f := algebraMap K[X] Frac
  have hf : Function.Injective f := IsFractionRing.injective K[X] Frac
  have hn' : f a ≠ 0 ∨ f d ≠ 0 := by
    rcases hn with ha | hd
    · left
      exact fun hz => ha (hf (hz.trans (map_zero f).symm))
    · right
      exact fun hz => hd (hf (hz.trans (map_zero f).symm))
  apply affine_columns_dependent q (swapEmbed D.U) (swapEmbed D.V) (f a) (f d) (f c) (f e) hn' hφ
  unfold K21_8.columnRankAt at hr
  have heq : (fun j : Fin 4 => swapEmbed
      (if j = 0 then D.U else if j = 1 then seed * D.U else if j = 2 then D.V else seed ^ q * D.V)) =
      ![swapEmbed D.U, Polynomial.X * swapEmbed D.U, swapEmbed D.V, Polynomial.X ^ q * swapEmbed D.V] := by
    funext j
    fin_cases j
    · rfl
    · change swapEmbed (seed * D.U) = Polynomial.X * swapEmbed D.U
      rw [map_mul, swapEmbed_seed]
    · rfl
    · change swapEmbed (seed ^ q * D.V) = Polynomial.X ^ q * swapEmbed D.V
      rw [map_mul, map_pow, swapEmbed_seed]
  rw [← heq]
  exact hr

/-- Rank four excludes the two opposite affine blocks, even after a
common seed factor and a common fixed-node factor are removed. -/
theorem exclude_affine {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (q : ℕ) (hq : 0 < q) (hr : K21_8.columnRankAt q D.U D.V = 4)
    (Q : Fin 2 × Fin (T.height + 1) → Seeds K)
    (s : K[X]) (hs : s ≠ 0) (hQ : ∀ j, graph q (Q j) = s * R.coefficients j)
    (h00 : blockDegree Q 0 0 = 0) (h01 : blockDegree Q 0 1 ≤ 1)
    (h10 : blockDegree Q 1 0 ≤ 1) (h11 : blockDegree Q 1 1 = 0) : False := by
  obtain ⟨a, d, hA⟩ := graph_affine_block q hq Q 0 h00 h01
  obtain ⟨c, e, hB⟩ := graph_affine_block q hq Q 1 h11 h10
  simp only [ite_eq_right (one_ne_zero : (1 : Fin 2) ≠ 0), pow_one] at hB
  exact exclude_affine_shapes D q hr s a d c e hs
    ((graph_pair R q Q s hQ 0).symm.trans hA)
    ((graph_pair R q Q s hQ 1).symm.trans hB)

end

end K21_11_1
end Port_K1_11_1Height

section Port_K1_11_2Equation
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K21_11_2
noncomputable section
open K21_11 MvPolynomial Finset
variable {F : Type*} [Field F]
theorem multiply_message_tag (P : MvPolynomial (Fin 5) F) (hP : OmitsMessages P) :
    messageTag (P*MvPolynomial.X 1) 1 0 ∧ messageTag (P*MvPolynomial.X 2) 0 1 := by
  constructor
  all_goals
    intro e he
    rw [support_mul_X] at he
    obtain ⟨f,hf,rfl⟩ := mem_map.mp he
    have hh := omitted_message_tag P hP f hf
    simpa [Finsupp.add_apply,Finsupp.single_apply] using hh

theorem supports_disjoint_of_tags (P Q : MvPolynomial (Fin 5) F) (a b c d : ℕ)
    (hP : messageTag P a b) (hQ : messageTag Q c d) (hne : (a,b)≠(c,d)) :
    Disjoint P.support Q.support := by
  apply disjoint_left.mpr
  intro e heP heQ
  have h1 := hP e heP
  have h2 := hQ e heQ
  exact hne (Prod.ext (by omega) (by omega))

theorem weighted_add_of_disjoint (v : Fin 5 → ℕ) (P Q : MvPolynomial (Fin 5) F)
    (h : Disjoint P.support Q.support) :
    (P+Q).weightedTotalDegree v=max (P.weightedTotalDegree v) (Q.weightedTotalDegree v) := by
  have hs : (P+Q).support=P.support∪Q.support := Finsupp.support_add_eq h
  simp only [weightedTotalDegree,hs,Finset.sup_union]

/-- The exact four degrees follow from disjoint Y monomials. This is the
actual linear-form lemma; no irreducibility assumption is required. -/
theorem linear_form_weight (v : Fin 5 → ℕ) (U V R : MvPolynomial (Fin 5) F)
    (hU : U≠0) (hV : V≠0) (hUm : OmitsMessages U) (hVm : OmitsMessages V)
    (hRm : OmitsMessages R) :
    (U*MvPolynomial.X 1+V*MvPolynomial.X 2-R).weightedTotalDegree v=
      max (max (U.weightedTotalDegree v+v 1) (V.weightedTotalDegree v+v 2))
        (R.weightedTotalDegree v) := by
  have htU := (multiply_message_tag U hUm).1
  have htV := (multiply_message_tag V hVm).2
  have hd := supports_disjoint_of_tags _ _ 1 0 0 1 htU htV (by decide)
  have hsum : (U*MvPolynomial.X 1+V*MvPolynomial.X 2).support=(U*MvPolynomial.X 1).support∪(V*MvPolynomial.X 2).support :=
    Finsupp.support_add_eq hd
  have hdR : Disjoint (U*MvPolynomial.X 1+V*MvPolynomial.X 2).support (-R).support := by
    apply disjoint_left.mpr
    intro e he heR
    have hR : e∈R.support := by simpa using heR
    have hRtag := omitted_message_tag R hRm e hR
    rw [hsum] at he
    rcases mem_union.mp he with hu | hv
    · have hh := htU e hu
      omega
    · have hh := htV e hv
      omega
  rw [sub_eq_add_neg,weighted_add_of_disjoint _ _ _ hdR,
    weighted_add_of_disjoint _ _ _ hd,
    weightedTotalDegree_mul _ _ _ hU (X_ne_zero 1),
    weightedTotalDegree_mul _ _ _ hV (X_ne_zero 2)]
  have hx (i : Fin 5) : (MvPolynomial.X i : MvPolynomial (Fin 5) F).weightedTotalDegree v=v i := by
    rw [MvPolynomial.X, weightedTotalDegree_monomial _ _ _ one_ne_zero]
    simp [Finsupp.weight_single]
  rw [hx 1,hx 2]
  have hn : (-R).weightedTotalDegree v=R.weightedTotalDegree v := by simp [weightedTotalDegree]
  rw [hn]

theorem omitted_source_weights (w : ℕ) (P : MvPolynomial (Fin 5) F)
    (hP : OmitsMessages P) (q : Fin 4) :
    P.weightedTotalDegree (sourceWeights w q)=![P.degreeOf 0,0,P.degreeOf 3,P.degreeOf 4] q := by
  have ht := omitted_message_tag P hP
  fin_cases q
  · change P.weightedTotalDegree (sourceWeights w 0)=P.degreeOf 0
    rw [weightedTotalDegree,degreeOf_eq_sup]
    apply Finset.sup_congr rfl
    intro e he
    have hh := ht e he
    simp [sourceWeights,weight5,hh.1,hh.2]
  · change P.weightedTotalDegree (sourceWeights w 1)=0
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro e he
    have hh := ht e he
    simp [sourceWeights,weight5,hh.1,hh.2]
  · change P.weightedTotalDegree (sourceWeights w 2)=P.degreeOf 3
    rw [weightedTotalDegree,degreeOf_eq_sup]
    apply Finset.sup_congr rfl
    intro e he
    have hh := ht e he
    simp [sourceWeights,weight5,hh.1,hh.2]
  · change P.weightedTotalDegree (sourceWeights w 3)=P.degreeOf 4
    rw [weightedTotalDegree,degreeOf_eq_sup]
    apply Finset.sup_congr rfl
    intro e he
    have hh := ht e he
    simp [sourceWeights,weight5,hh.1,hh.2]

theorem equation_degrees (w H : ℕ) (U V W : MvPolynomial (Fin 5) F)
    (hU : U ≠ 0) (hV : V ≠ 0)
    (hUm : OmitsMessages U) (hVm : OmitsMessages V) (hWm : OmitsMessages W)
    (hH : max (U.degreeOf 0) (V.degreeOf 0) = H) (hWX : W.degreeOf 0 ≤ w + H)
    (hWS : W.degreeOf 3 ≤ sWeight U V) (hWT : W.degreeOf 4 ≤ tWeight U V) :
    ∀ j, (U * MvPolynomial.X 1 + V * MvPolynomial.X 2 - W).weightedTotalDegree
      (sourceWeights w j) = sourceBounds (w + H) 1 (sWeight U V) (tWeight U V) j := by
  intro j
  rw [linear_form_weight _ U V W hU hV hUm hVm hWm, omitted_source_weights w U hUm,
    omitted_source_weights w V hVm, omitted_source_weights w W hWm]
  fin_cases j
  · simp [sourceWeights, sourceBounds]
    omega
  · simp [sourceWeights, sourceBounds]
  · simp [sourceWeights, sourceBounds, sWeight] at hWS ⊢
    omega
  · simp [sourceWeights, sourceBounds, tWeight] at hWT ⊢
    omega

private theorem polynomialView_constant (Q : MvPolynomial (Fin 5) F)
    (hQ : OmitsMessages Q) : polynomialView Q = Polynomial.C ((polynomialView Q).coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_le_zero
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hn
  obtain ⟨f, hf⟩ := support_nonempty.mpr hn
  obtain ⟨e, he, _, _, he2, _, _⟩ := polynomialView_coeff_support Q j f hf
  have he0 := (omitted_message_tag Q hQ e he).2
  omega

def equation (U V W : MvPolynomial (Fin 5) F) : MvPolynomial (Fin 5) F :=
  U * MvPolynomial.X 1 + V * MvPolynomial.X 2 - W

def decoderNumerator (U W : MvPolynomial (Fin 5) F) : MvPolynomial (Fin 4) F :=
  (polynomialView W).coeff 0 - (polynomialView U).coeff 0 * MvPolynomial.X 1

def decoderDenominator (V : MvPolynomial (Fin 5) F) : MvPolynomial (Fin 4) F :=
  (polynomialView V).coeff 0

theorem equation_linear (U V W : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hW : OmitsMessages W) :
    polynomialView (equation U V W) =
      Polynomial.C (decoderDenominator V) * Polynomial.X -
        Polynomial.C (decoderNumerator U W) := by
  simp only [equation, map_sub, map_add, map_mul, polynomialView_X]
  rw [polynomialView_constant U hU, polynomialView_constant V hV, polynomialView_constant W hW]
  simp [decoderDenominator, decoderNumerator, map_sub, map_mul]
  ring

theorem decoderDenominator_ne (V : MvPolynomial (Fin 5) F)
    (hV : OmitsMessages V) (hn : V ≠ 0) : decoderDenominator V ≠ 0 := by
  intro h
  apply hn
  apply (polynomialView (F:=F)).injective
  have he : polynomialView V = Polynomial.C (decoderDenominator V) :=
    polynomialView_constant V hV
  rw [he, h, Polynomial.C_0]
  exact (map_zero (polynomialView (F:=F))).symm

/-- A common divisor of the two Y₁ coefficients divides V and is
independent of Y₀. Differentiating in Y₀ shows that it also divides U. -/
theorem equation_primitive (U V W : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hW : OmitsMessages W)
    (hn : V ≠ 0) (hUV : IsRelPrime U V) :
    (Polynomial.C (decoderDenominator V) * Polynomial.X -
        Polynomial.C (decoderNumerator U W)).IsPrimitive := by
  apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro d hd
  have hc := (Polynomial.C_dvd_iff_dvd_coeff d _).mp hd
  have hdV : d ∣ decoderDenominator V := by
    simpa [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X] using hc 1
  have hdN : d ∣ decoderNumerator U W := by
    simpa [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X] using hc 0
  let e := (polynomialView (F:=F)).symm (Polynomial.C d)
  have heV : e ∣ V := by
    apply (map_dvd_iff (polynomialView (F:=F))).mp
    change polynomialView ((polynomialView (F:=F)).symm (Polynomial.C d)) ∣ polynomialView V
    rw [AlgEquiv.apply_symm_apply, polynomialView_constant V hV]
    exact map_dvd Polynomial.C hdV
  have heN : e ∣ W - U * MvPolynomial.X 1 := by
    apply (map_dvd_iff (polynomialView (F:=F))).mp
    change polynomialView ((polynomialView (F:=F)).symm (Polynomial.C d)) ∣
      polynomialView (W - U * MvPolynomial.X 1)
    rw [AlgEquiv.apply_symm_apply, map_sub, map_mul, polynomialView_X,
      polynomialView_constant W hW, polynomialView_constant U hU]
    change Polynomial.C d ∣ Polynomial.C ((polynomialView W).coeff 0) -
      Polynomial.C ((polynomialView U).coeff 0) * Polynomial.C (MvPolynomial.X 1)
    rw [← map_mul, ← map_sub]
    exact map_dvd Polynomial.C hdN
  obtain ⟨v, hv⟩ := heV
  have he : e ≠ 0 := by intro hz; apply hn; rw [hv, hz, zero_mul]
  have hv_ne : v ≠ 0 := by intro hz; apply hn; rw [hv, hz, mul_zero]
  have heomits : e.degreeOf 1 = 0 := by
    have hdeg := congrArg (degreeOf (1 : Fin 5)) hv
    rw [hV.1, degreeOf_mul_eq he hv_ne] at hdeg
    omega
  obtain ⟨q, hq⟩ := heN
  have hh : -U = e * pderiv 1 q := by
    simpa [map_sub, pderiv_mul, pderiv_zero_of_degree_zero _ _ hW.1,
      pderiv_zero_of_degree_zero _ _ hU.1,
      pderiv_zero_of_degree_zero _ _ heomits] using congrArg (pderiv (R:=F) (1 : Fin 5)) hq
  have heU : e ∣ U := by
    refine ⟨-pderiv 1 q, ?_⟩
    rw [mul_neg, ← hh, neg_neg]
  have hu := (hUV heU ⟨v, hv⟩).map (polynomialView (F:=F)).toRingHom
  change IsUnit (polynomialView e) at hu
  exact Polynomial.isUnit_C.mp (by simpa only [e, AlgEquiv.apply_symm_apply] using hu)

/-- Read the original quotient filtration on the two coefficients of Y₁. -/
theorem decoder_bounds (w H s t : ℕ) (U V W : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) (hW : OmitsMessages W) (hVn : V ≠ 0)
    (hQ : equation U V W ∈ filtered (sourceWeights w) (sourceBounds (w + H) 1 s t)) :
    (decoderNumerator U W).weightedTotalDegree scalarWeightY ≤ 1 ∧
    (decoderDenominator V).weightedTotalDegree scalarWeightY ≤ 0 ∧
    (decoderNumerator U W).weightedTotalDegree scalarWeightYS ≤ s ∧
    (decoderDenominator V).weightedTotalDegree scalarWeightYS ≤ s ∧
    (decoderNumerator U W).weightedTotalDegree scalarWeightT ≤ t ∧
    (decoderDenominator V).weightedTotalDegree scalarWeightT ≤ t - 1 := by
  obtain ⟨hY, hS, hT⟩ := polynomialView_source_coefficients (w + H) w 1 s t _ hQ
  have h0 : (polynomialView (equation U V W)).coeff 0 = -decoderNumerator U W := by
    rw [equation_linear U V W hU hV hW]
    simp [Polynomial.coeff_sub]
  have h1 : (polynomialView (equation U V W)).coeff 1 = decoderDenominator V := by
    rw [equation_linear U V W hU hV hW]
    simp [Polynomial.coeff_sub]
  have hV' : (polynomialView (equation U V W)).coeff 1 ≠ 0 := by
    rw [h1]
    exact decoderDenominator_ne V hV hVn
  have hy1 := hY 1 le_rfl hV'
  have hs1 := hS 1 le_rfl hV'
  have ht1 := hT 1 le_rfl hV'
  rw [h1] at hy1 hs1 ht1
  refine ⟨?_, by omega, ?_, hs1, ?_, by omega⟩
  all_goals
    by_cases hn : decoderNumerator U W = 0
    · simp [hn, weightedTotalDegree]
    · have hn' : (polynomialView (equation U V W)).coeff 0 ≠ 0 := by simpa [h0] using hn
      first
      | simpa [h0, weightedTotalDegree] using hY 0 (by decide) hn'
      | simpa [h0, weightedTotalDegree] using hS 0 (by decide) hn'
      | simpa [h0, weightedTotalDegree] using hT 0 (by decide) hn'

end
end K21_11_2
end Port_K1_11_2Equation

section Port_K1_11Incidence
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K21_11
noncomputable section

open MvPolynomial
open scoped BigOperators

private theorem ncard_inter_filter {A : Type*} (S : Finset A) (locus : Set A) [DecidablePred (· ∈ locus)] :
    ((S : Set A) ∩ locus).ncard = (S.filter (· ∈ locus)).card := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  rfl

/-- A rational point supplies a chain of proper linear sections through it.
Bézout along the chain reduces the degree lower bound to dimension zero. -/
private theorem one_le_degree_of_point {F σ : Type*} [Field F] [Finite σ]
    (J : Ideal (MvPolynomial σ F)) [J.IsPrime] (x : σ → F) (hx : x ∈ zeroLocus F J) :
    1 ≤ affineDegree J := by
  classical
  generalize hd : (affineHilbertPolynomial J).natDegree = d
  induction d using Nat.strong_induction_on generalizing J with
  | h d ih =>
    by_cases h0 : d = 0
    · have hfin := finite_zeroLocus_and_ncard_le_affineDegree (K := F) J (hd.trans h0)
      have hxone : 1 ≤ (zeroLocus F J).ncard := by
        simpa using Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hx) hfin.1
      exact (by exact_mod_cast hxone : (1 : ℚ) ≤ _).trans hfin.2
    have hproper : ∃ i, MvPolynomial.X i - C (x i) ∉ J := by
      by_contra hn
      push Not at hn
      let φ := Ideal.Quotient.mk J
      have hmaps : φ = φ.comp (C.comp (MvPolynomial.eval x)) := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [φ]
        · intro i
          simp only [RingHom.comp_apply, eval_X]
          exact sub_eq_zero.mp (by rw [← map_sub]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hn i))
      have hsurj : Function.Surjective (algebraMap F (MvPolynomial σ F ⧸ J)) := by
        intro q
        obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
        refine ⟨MvPolynomial.eval x g, ?_⟩
        exact (RingHom.congr_fun hmaps g).symm
      letI : Module.Finite F (MvPolynomial σ F ⧸ J) :=
        Module.Finite.of_surjective (Algebra.linearMap F (MvPolynomial σ F ⧸ J)) hsurj
      exact h0 (by rw [← hd, affineHilbertPolynomial_eq_C_finrank, Polynomial.natDegree_C])
    obtain ⟨i, hi⟩ := hproper
    let f := MvPolynomial.X i - C (x i)
    have hxf : aeval x f = 0 := by simp [f]
    have hfdeg : f.totalDegree ≤ 1 := by
      exact (totalDegree_sub _ _).trans (by simp)
    have hxp : x ∈ zeroLocus F (J ⊔ Ideal.span {f}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hx, hxf⟩
    obtain ⟨Q, hQ, hxQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      (J ⊔ Ideal.span {f}) (1 : MvPolynomial σ F) x hxp (by simp)
    have hQmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
    letI : Q.IsPrime := hQmin.isPrime
    have hd' := principalCut_natDegree_affineHilbertPolynomial_add_one hi hQmin
    have hone := ih _ (by omega) Q hxQ rfl
    have hsum := principalCut_sum_affineDegree_retainedMinimalPrimes_le
      (1 : MvPolynomial σ F) hi hfdeg
    have hQsum := Finset.single_le_sum (f := affineDegree)
      (fun A _ => affineDegree_nonneg A) hQ
    simpa only [Nat.cast_one, one_mul] using hone.trans (hQsum.trans hsum)

/-- The degree-weighted induction admits a bounded terminal set on a prime
with many persistent node equations. Each other step uses a proper cut. -/
private theorem prime_count_with_terminal {F σ ι : Type*} [Field F] [Finite σ] [Fintype ι]
    (s : MvPolynomial σ F) (cuts : ι → MvPolynomial σ F) {A L M : ℕ}
    (hLA : L ≤ A) (hdeg : ∀ i, (cuts i).totalDegree ≤ M) {R : ℚ} (hR : 1 ≤ R)
    (hratio : ∀ m < L, (((Fintype.card ι - m) * M : ℕ) : ℚ) ≤ R * ((A - m : ℕ) : ℚ))
    (S : Finset (σ → F)) (hreg : ∀ x ∈ S, aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard)
    (hterminal : ∀ J : Ideal (MvPolynomial σ F), L ≤ {i | cuts i ∈ J}.ncard →
      (((S : Set (σ → F)) ∩ zeroLocus F J).ncard : ℚ) ≤ R)
    (P : Ideal (MvPolynomial σ F)) [P.IsPrime] (W : Finset (σ → F)) (hW : W ⊆ S)
    (hzero : ∀ x ∈ W, x ∈ zeroLocus F P) :
    (W.card : ℚ) ≤ affineDegree P * R ^ (affineHilbertPolynomial P).natDegree := by
  classical
  generalize hd : (affineHilbertPolynomial P).natDegree = d
  induction d using Nat.strong_induction_on generalizing P W with
  | h d ih =>
    rcases W.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simpa using mul_nonneg (affineDegree_nonneg P) (pow_nonneg (zero_le_one.trans hR) d)
    rcases d with _ | e
    · have hfin := finite_zeroLocus_and_ncard_le_affineDegree (K := F) P hd
      have hcard := Set.ncard_le_ncard
        (fun x (hx : x ∈ (W : Set (σ → F))) => hzero x hx) hfin.1
      rw [Set.ncard_coe_finset] at hcard
      simpa using (by exact_mod_cast hcard : (W.card : ℚ) ≤ _).trans hfin.2
    let keep : Finset ι := Finset.univ.filter fun i => cuts i ∈ P
    have hkeep : keep.card = {i | cuts i ∈ P}.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp [keep]
    by_cases hpers : L ≤ keep.card
    · have hc : W.card ≤ ((S : Set (σ → F)) ∩ zeroLocus F P).ncard := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard (fun x hx => ⟨hW hx, hzero x hx⟩)
      have hdegP := one_le_degree_of_point P x₀ (hzero x₀ hx₀)
      calc
        (W.card : ℚ) ≤ (((S : Set (σ → F)) ∩ zeroLocus F P).ncard : ℚ) := by exact_mod_cast hc
        _ ≤ R := hterminal P (hkeep ▸ hpers)
        _ ≤ affineDegree P * R ^ (e+1) := by
          calc
            R = 1 * R ^ (1 : ℕ) := by ring
            _ ≤ affineDegree P * R ^ (e+1) :=
              mul_le_mul hdegP (pow_le_pow_right₀ hR (by omega)) (by positivity) (by linarith)
    let rel : (σ → F) → ι → Prop := fun x i => aeval x (cuts i) = 0
    let c : ℚ := ((A - keep.card : ℕ) : ℚ)
    have hc : 0 < c := by
      change (0 : ℚ) < ((A - keep.card : ℕ) : ℚ)
      exact_mod_cast (by omega : 0 < A - keep.card)
    have hlowNat : W.card * (A - keep.card) ≤ ∑ i ∈ keepᶜ, (W.bipartiteBelow rel i).card := by
      refine Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow rel keep fun x hx => ?_
      rw [← Set.ncard_coe_finset, Finset.coe_bipartiteAbove]
      simpa [rel] using hA x (hW hx)
    have hlow : (W.card : ℚ) * c ≤ ∑ i ∈ keepᶜ, ((W.bipartiteBelow rel i).card : ℚ) := by
      change (W.card : ℚ) * ((A - keep.card : ℕ) : ℚ) ≤ _
      exact_mod_cast hlowNat
    have hcut : ∀ i ∈ keepᶜ, ((W.bipartiteBelow rel i).card : ℚ) ≤ M * affineDegree P * R^e := by
      intro i hi
      have hiP : cuts i ∉ P := by simpa [keep] using hi
      rw [← Set.ncard_coe_finset, Finset.coe_bipartiteBelow]
      refine ncard_inter_cut_le_of_retained_le s hiP (hdeg i) W
        (fun x hx => ⟨hzero x hx, hreg x (hW hx)⟩) (by positivity) fun Q hQ => ?_
      have hQmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
      letI : Q.IsPrime := hQmin.isPrime
      have hQdim : (affineHilbertPolynomial Q).natDegree = e := by
        have := principalCut_natDegree_affineHilbertPolynomial_add_one hiP hQmin
        omega
      rw [ncard_inter_filter]
      exact ih e (by omega) Q _ (fun _ hx => hW (Finset.mem_filter.mp hx).1)
        (fun _ hx => (Finset.mem_filter.mp hx).2) hQdim
    have hupp : ∑ i ∈ keepᶜ, ((W.bipartiteBelow rel i).card : ℚ) ≤
        ((Fintype.card ι - keep.card : ℕ) : ℚ) * (M * affineDegree P * R^e) := by
      refine (Finset.sum_le_card_nsmul _ _ _ hcut).trans_eq ?_
      rw [nsmul_eq_mul, Finset.card_compl]
    refine le_of_mul_le_mul_right (hlow.trans (hupp.trans ?_)) hc
    calc
      ((Fintype.card ι - keep.card : ℕ) : ℚ) * (M * affineDegree P * R^e) =
          (((Fintype.card ι - keep.card) * M : ℕ) : ℚ) * (affineDegree P * R^e) := by
        rw [Nat.cast_mul]
        ring
      _ ≤ (R * c) * (affineDegree P * R^e) :=
        mul_le_mul_of_nonneg_right (hratio keep.card (by omega))
          (mul_nonneg (affineDegree_nonneg P) (pow_nonneg (zero_le_one.trans hR) e))
      _ = (affineDegree P * R^(e+1)) * c := by rw [pow_succ]; ring

private theorem surface_count_with_terminal {F ι : Type*} [Field F] [Fintype ι]
    (g s : MvPolynomial (Fin 3) F) (hg : g ≠ 0) (cuts : ι → MvPolynomial (Fin 3) F)
    {A L M E : ℕ} (hLA : L ≤ A) (hgdeg : g.totalDegree ≤ E) (hdeg : ∀ i, (cuts i).totalDegree ≤ M)
    {R : ℚ} (hR : 1 ≤ R)
    (hratio : ∀ m < L, (((Fintype.card ι - m) * M : ℕ) : ℚ) ≤ R * ((A - m : ℕ) : ℚ))
    (S : Finset (Fin 3 → F)) (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard)
    (hterminal : ∀ J : Ideal (MvPolynomial (Fin 3) F), L ≤ {i | cuts i ∈ J}.ncard →
      (((S : Set (Fin 3 → F)) ∩ zeroLocus F J).ncard : ℚ) ≤ R) :
    (S.card : ℚ) ≤ E * R^2 := by
  classical
  let family := (Ideal.span {g}).retainedMinimalPrimes s
  have hmem (Q) (hQ : Q ∈ family) : g ∈ Q :=
    (Ideal.mem_retainedMinimalPrimes.mp hQ).1.le (Ideal.mem_span_singleton_self g)
  have hdim : ∀ Q ∈ family, (affineHilbertPolynomial Q).natDegree ≤ 2 := by
    intro Q hQ
    simpa [Nat.card_eq_fintype_card] using natDegree_affineHilbertPolynomial_le_of_mem hg (hmem Q hQ)
  have hsum : ∑ Q ∈ family, affineDegree Q ≤ (E : ℚ) := by
    letI : (⊥ : Ideal (MvPolynomial (Fin 3) F)).IsPrime := Ideal.isPrime_bot
    have hnot : g ∉ (⊥ : Ideal (MvPolynomial (Fin 3) F)) := by simpa using hg
    simpa only [family, bot_sup_eq, affineDegree_bot, mul_one] using
      principalCut_sum_affineDegree_retainedMinimalPrimes_le s hnot hgdeg
  refine card_le_mul_pow_of_forall_mem_zeroLocus family hdim hsum hR S (fun x hx => ?_) ?_
  · have hxg : x ∈ zeroLocus F (Ideal.span {g}) := mem_zeroLocus_iff_le_ker_aeval.mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (hS x hx).1))
    exact exists_retainedMinimalPrime_of_mem_zeroLocus _ s x hxg (hS x hx).2
  · intro Q hQ
    letI : Q.IsPrime := (Ideal.mem_retainedMinimalPrimes.mp hQ).1.isPrime
    rw [ncard_inter_filter]
    exact prime_count_with_terminal s cuts hLA hdeg hR hratio S
      (fun x hx => (hS x hx).2) hA hterminal Q _
      (fun _ hx => (Finset.mem_filter.mp hx).1) (fun _ hx => (Finset.mem_filter.mp hx).2)

open K21

theorem chart_count {u : Words} {deleted : Finset I} {P : Puncture deleted}
    {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
    (chart : TaylorChart u P F b Λ) : (Λ.card : ℚ) ≤ b.chartFee := by
  classical
  let S := Λ.image chart.point
  let R : ℚ := (131073 / 49098 : ℚ) * b.M
  have hRbig : (262144 : ℚ) ≤ R := by
    cases b <;> norm_num [R, Bank.M, Bank.E, Bank.a, Bank.b, Bank.s, Bank.t, Bank.dS, Bank.dT]
  have hR : 1 ≤ R := (by norm_num : (1 : ℚ) ≤ 262144).trans hRbig
  have hN : P.N ≤ 262144 := by have := P.size; omega
  have hinj : Set.InjOn chart.point (Λ : Set K) := by
    intro γ hγ δ hδ he
    apply (algebraMap K Frac).injective
    exact (chart.slope γ hγ).symm.trans ((congrFun he 1).trans (chart.slope δ hδ))
  have hcard : S.card = Λ.card := Finset.card_image_of_injOn hinj
  let cuts := nodeCut u P chart.numerator chart.denominator
  have hratio (m : ℕ) (hm : m < 131072) :
      (((Fintype.card (Fin P.N) - m) * b.M : ℕ) : ℚ) ≤ R * ((180169 - m : ℕ) : ℚ) := by
    have hnat : (P.N - m) * 49098 ≤ 131073 * (180169 - m) := by omega
    have hrat : ((P.N - m : ℕ) : ℚ) * 49098 ≤ 131073 * ((180169 - m : ℕ) : ℚ) := by
      exact_mod_cast hnat
    have hh : ((P.N - m : ℕ) : ℚ) ≤ (131073/49098 : ℚ) * ((180169 - m : ℕ) : ℚ) := by
      linarith
    rw [Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (b.M : ℚ))).trans_eq (by dsimp [R]; ring)
  rw [← hcard]
  refine surface_count_with_terminal chart.equation chart.denominator chart.equation_ne cuts
    (L := 131072) (A := 180169) (by decide) chart.equation_degree chart.cut_degree hR hratio S
    (fun x hx => ?_) (fun x hx => ?_) (fun J hJ => ?_)
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨chart.on_equation γ hγ, chart.regular γ hγ⟩
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact chart_agreements chart γ hγ
  · let W := Λ.filter fun γ => chart.point γ ∈ zeroLocus Frac J
    have hW : W ⊆ Λ := Finset.filter_subset _ _
    have hWimage : W.image chart.point = S.filter (· ∈ zeroLocus Frac J) := by
      ext x
      simp only [W, S, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨γ, ⟨hγ, hJγ⟩, rfl⟩
        exact ⟨⟨γ, hγ, rfl⟩, hJγ⟩
      · rintro ⟨⟨γ, hγ, rfl⟩, hJγ⟩
        exact ⟨γ, ⟨hγ, hJγ⟩, rfl⟩
    have hbound := chart_persistent chart J W hW (fun γ hγ => (Finset.mem_filter.mp hγ).2) hJ
    rw [ncard_inter_filter, ← hWimage, Finset.card_image_of_injOn (hinj.mono hW)]
    exact (by exact_mod_cast hbound.trans hN : (W.card : ℚ) ≤ 262144).trans hRbig

end
end K21_11
end Port_K1_11Incidence

section Port_K1_11_3Assignment
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace K21_11_3
noncomputable section

open K21 K21_11 MvPolynomial

section Field
variable {F : Type*} [Field F]

/-- Put Y first, with X,S,T following in that order. -/
private def swapXY : Fin 4 ≃ Fin 4 := Equiv.swap 0 1

private def yView : MvPolynomial (Fin 4) F ≃ₐ[F]
    Polynomial (MvPolynomial (Fin 3) F) :=
  (renameEquiv F swapXY).trans (MvPolynomial.finSuccEquiv F 3)

private theorem yView_X (i : Fin 4) :
    yView (MvPolynomial.X i : MvPolynomial (Fin 4) F) =
      ![Polynomial.C (MvPolynomial.X 0), Polynomial.X, Polynomial.C (MvPolynomial.X 1), Polynomial.C (MvPolynomial.X 2)] i := by
  change MvPolynomial.finSuccEquiv F 3 (rename swapXY (MvPolynomial.X i)) = _
  rw [rename_X]
  fin_cases i
  · change (MvPolynomial.finSuccEquiv F 3) (MvPolynomial.X (0 : Fin 3).succ) = _
    exact finSuccEquiv_X_succ
  · change (MvPolynomial.finSuccEquiv F 3) (MvPolynomial.X 0) = _
    exact finSuccEquiv_X_zero
  · change (MvPolynomial.finSuccEquiv F 3) (MvPolynomial.X (1 : Fin 3).succ) = _
    exact finSuccEquiv_X_succ
  · change (MvPolynomial.finSuccEquiv F 3) (MvPolynomial.X (2 : Fin 3).succ) = _
    exact finSuccEquiv_X_succ

private def seedValues (s t : F) : Fin 3 → Polynomial F :=
  ![Polynomial.X, Polynomial.C s, Polynomial.C t]

private def specializeY (G : MvPolynomial (Fin 4) F) (s t : F) :
    Polynomial (Polynomial F) :=
  (yView G).map (aeval (seedValues s t)).toRingHom

private theorem specializeY_eval (G : MvPolynomial (Fin 4) F) (D : Polynomial F) (s t : F) :
    (specializeY G s t).eval D = aeval (scalarImages D s t) G := by
  let ev : MvPolynomial (Fin 3) F →+* Polynomial F := (aeval (seedValues s t)).toRingHom
  have h : (Polynomial.evalRingHom D).comp ((Polynomial.mapRingHom ev).comp yView.toRingHom) =
      (aeval (scalarImages D s t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ev, yView, finSuccEquiv_apply]
    · intro i
      change (specializeY (MvPolynomial.X i) s t).eval D = _
      unfold specializeY
      rw [yView_X]
      fin_cases i <;> simp [seedValues, scalarImages]
  exact RingHom.congr_fun h G

private theorem specializeY_derivative (G : MvPolynomial (Fin 4) F) (s t : F) :
    specializeY (pderiv 1 G) s t = Polynomial.derivative (specializeY G s t) := by
  let f : MvPolynomial (Fin 4) F →+* Polynomial (Polynomial F) :=
    (Polynomial.mapRingHom (aeval (seedValues s t)).toRingHom).comp yView.toRingHom
  change f (pderiv 1 G) = Polynomial.derivative (f G)
  have hC (a : F) : f (C a) = Polynomial.C (Polynomial.C a) := by
    simp [f, yView, finSuccEquiv_apply]
  have hX (i : Fin 4) : f (MvPolynomial.X i) = ![Polynomial.C Polynomial.X, Polynomial.X,
      Polynomial.C (Polynomial.C s), Polynomial.C (Polynomial.C t)] i := by
    change (yView (MvPolynomial.X i)).map _ = _
    rw [yView_X]
    fin_cases i <;> simp [seedValues]
  induction G using MvPolynomial.induction_on with
  | C a => simp [hC]
  | add a b ha hb => simp [ha, hb]
  | mul_X a i ha =>
      simp only [pderiv_mul, map_add, map_mul, Polynomial.derivative_mul, ha, hX]
      fin_cases i <;> simp

private theorem specializeY_iterate (G : MvPolynomial (Fin 4) F) (s t : F) (j : ℕ) :
    specializeY (derivativeChart G j) s t =
      (fun H : Polynomial (Polynomial F) => Polynomial.derivative H)^[j] (specializeY G s t) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      unfold derivativeChart at *
      simp only [Function.iterate_succ_apply', specializeY_derivative, ih]

private theorem yView_degree (G : MvPolynomial (Fin 4) F) :
    (yView G).natDegree = G.weightedTotalDegree scalarWeightY := by
  change (MvPolynomial.finSuccEquiv F 3 (rename swapXY G)).natDegree = _
  rw [natDegree_finSuccEquiv, show (0 : Fin 4) = swapXY 1 by decide,
    degreeOf_rename_of_injective swapXY.injective, ← weightedTotalDegree_piSingle]
  congr 1
  funext i
  fin_cases i <;> decide

private theorem coefficient_support (G : MvPolynomial (Fin 4) F) (i j : ℕ)
    (e : Fin 2 →₀ ℕ) (he : e ∈
      ((MvPolynomial.finSuccEquiv F 2 ((yView G).coeff j)).coeff i).support) :
    ∃ m ∈ G.support, m 2 = e 0 ∧ m 3 = e 1 := by
  rw [mem_support_coeff_finSuccEquiv] at he
  change e.cons i ∈ ((MvPolynomial.finSuccEquiv F 3 (rename swapXY G)).coeff j).support at he
  rw [mem_support_coeff_finSuccEquiv] at he
  obtain ⟨m, hm, hcoeff⟩ := coeff_rename_ne_zero swapXY G ((e.cons i).cons j)
    (mem_support_iff.mp he)
  refine ⟨m, mem_support_iff.mpr hcoeff, ?_, ?_⟩
  · have h := congrArg (fun z : Fin 4 →₀ ℕ => z (swapXY 2)) hm
    simp only [Finsupp.mapDomain_apply_of_injective swapXY.injective] at h
    rw [show swapXY 2 = (0 : Fin 2).succ.succ by decide] at h
    simpa only [Finsupp.cons_succ] using h
  · have h := congrArg (fun z : Fin 4 →₀ ℕ => z (swapXY 3)) hm
    simp only [Finsupp.mapDomain_apply_of_injective swapXY.injective] at h
    rw [show swapXY 3 = (1 : Fin 2).succ.succ by decide] at h
    simpa only [Finsupp.cons_succ] using h

private theorem seedValues_map (H : MvPolynomial (Fin 3) F) (s t : F) :
    aeval (seedValues s t) H =
      (MvPolynomial.finSuccEquiv F 2 H).map (MvPolynomial.eval ![s,t]) := by
  change (aeval (seedValues s t)).toRingHom H =
    ((Polynomial.mapRingHom (MvPolynomial.eval ![s,t])).comp (MvPolynomial.finSuccEquiv F 2).toRingHom) H
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [finSuccEquiv_apply]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [seedValues, finSuccEquiv_X_zero]
    · change aeval (seedValues s t) (MvPolynomial.X j.succ) =
        ((MvPolynomial.finSuccEquiv F 2) (MvPolynomial.X j.succ)).map _
      rw [finSuccEquiv_X_succ]
      fin_cases j <;> simp [seedValues]

/-- Keep one nonzero coefficient in X,Y, then charge all of its graph roots. -/
private theorem exceptions (G : MvPolynomial (Fin 4) F) (hG : G ≠ 0)
    (q a b : ℕ) (hq : 0 < q) (ha : a < q)
    (hS : G.weightedTotalDegree scalarWeightYS ≤ a)
    (hT : G.weightedTotalDegree scalarWeightT ≤ b) (Γ : Finset F) :
    ∃ exceptional : Finset F, exceptional.card ≤ a + q * b ∧
      ∀ γ ∈ Γ, γ ∉ exceptional → specializeY G γ (γ ^ q) ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr
    (show yView G ≠ 0 from fun hz => hG (yView.injective (hz.trans (map_zero yView).symm)))
  have hn : MvPolynomial.finSuccEquiv F 2 ((yView G).coeff j) ≠ 0 := by
    intro hz
    apply Polynomial.mem_support_iff.mp hj
    exact (MvPolynomial.finSuccEquiv F 2).injective
      (hz.trans (map_zero (MvPolynomial.finSuccEquiv F 2)).symm)
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hn
  let c := (MvPolynomial.finSuccEquiv F 2 ((yView G).coeff j)).coeff i
  have hc : c ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hmono (e : Fin 2 →₀ ℕ) (he : e ∈ c.support) : e 0 ≤ a ∧ e 1 ≤ b := by
    obtain ⟨m, hm, h0, h1⟩ := coefficient_support G i j e he
    have hs := (Finset.le_sup (f := fun m => m.weight scalarWeightYS) hm).trans hS
    have ht := (Finset.le_sup (f := fun m => m.weight scalarWeightT) hm).trans hT
    simp [scalarWeightYS, scalarWeightT, Finsupp.weight_apply, Finsupp.sum_fintype,
      Fin.sum_univ_succ, smul_eq_mul] at hs ht
    omega
  have hca : c.degreeOf 0 ≤ a := by
    rw [degreeOf_eq_sup]
    exact Finset.sup_le fun e he => (hmono e he).1
  have hcb : c.degreeOf 1 ≤ b := by
    rw [degreeOf_eq_sup]
    exact Finset.sup_le fun e he => (hmono e he).2
  let E := Γ.filter fun γ => MvPolynomial.eval ![γ, γ ^ q] c = 0
  refine ⟨E, K1_10.frobenius_coefficient_exception_count q a b hq c hc hca ha hcb E
    (fun γ hγ => (Finset.mem_filter.mp hγ).2), ?_⟩
  intro γ hγ houtside hz
  apply houtside
  apply Finset.mem_filter.mpr
  refine ⟨hγ, ?_⟩
  have he := congrArg (fun R : Polynomial (Polynomial F) => (R.coeff j).coeff i) hz
  simpa [specializeY, seedValues_map, c] using he

end Field

/-- Cover the surviving slopes by derivatives that are simple at the actual decoders. -/
theorem assign {u : Words} {deleted : Finset I} {Γ : Finset K}
    {F : Marks u deleted Γ} {b : Bank} (A : Annihilator F b) :
    ∃ (exceptional : Finset K) (charts : Fin 5 → Finset K),
      exceptional.card ≤ b.zeroFee ∧
      (∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j) ∧
      ∀ j, ∃ hsub : charts j ⊆ Γ, ∀ γ (hγ : γ ∈ charts j),
        SimpleRoot (derivativeChart A.Q j) (F.mark γ (hsub hγ)).decoder γ (γ ^ p) := by
  classical
  obtain ⟨exceptional, hfee, hex⟩ := exceptions A.Q A.nonzero p b.a b.b (by decide)
    (by cases b <;> decide) A.degreeS A.degreeT Γ
  have hassign (γ : K) (hγ : γ ∈ Γ) (hn : γ ∉ exceptional) :
      ∃ j : Fin 5, SimpleRoot (derivativeChart A.Q j) (F.mark γ hγ).decoder γ (γ ^ p) := by
    let f := specializeY A.Q γ (γ ^ p)
    have hdeg : f.natDegree ≤ 5 :=
      (Polynomial.natDegree_map_le).trans ((yView_degree A.Q).le.trans A.degreeY)
    have hroot : f.IsRoot (F.mark γ hγ).decoder :=
      (specializeY_eval A.Q _ γ (γ ^ p)).trans (A.vanishes γ hγ)
    obtain ⟨j, hj, hz, hnz⟩ := exists_simple_derivative_at_root p 5 f
      (hex γ hγ hn) hdeg (by decide) _ hroot
    refine ⟨⟨j,hj⟩, ?_, ?_⟩
    · rw [← specializeY_eval, specializeY_iterate]
      exact hz
    · rw [← specializeY_eval, specializeY_derivative, specializeY_iterate]
      exact hnz
  let charts (j : Fin 5) := Γ.filter fun γ =>
    ∃ hγ : γ ∈ Γ, SimpleRoot (derivativeChart A.Q j) (F.mark γ hγ).decoder γ (γ ^ p)
  refine ⟨exceptional, charts, hfee, ?_, ?_⟩
  · intro γ hγ
    by_cases he : γ ∈ exceptional
    · exact Or.inl he
    · obtain ⟨j,hj⟩ := hassign γ hγ he
      exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨hγ, hγ, hj⟩⟩
  · intro j
    refine ⟨fun _ hγ => (Finset.mem_filter.mp hγ).1, ?_⟩
    intro γ hγ
    obtain ⟨_, h⟩ := (Finset.mem_filter.mp hγ).2
    exact h

end
end K21_11_3
end Port_K1_11_3Assignment

section Port_K1_11_2Bank
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K21_11_2
noncomputable section

open MvPolynomial
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A single parameter of degree at most one gives an affine image,
with coefficients obtained by evaluating only the X-coordinate. -/
private theorem affine_image (Q : MvPolynomial (Fin 5) F)
    (j : Fin 5) (hj : j = 3 ∨ j = 4) (x : E) (v : Fin 5 → Polynomial E)
    (hv : v 0 = Polynomial.C x) (hl : Q.degreeOf j ≤ 1)
    (hzero : ∀ i : Fin 5, i ≠ 0 → i ≠ j → Q.degreeOf i = 0) :
    ∃ a b : E, aeval v Q = Polynomial.C a + Polynomial.C b * v j := by
  classical
  let c (e : Fin 5 →₀ ℕ) := algebraMap F E (Q.coeff e) * x ^ e 0
  let a (e : Fin 5 →₀ ℕ) := if e j = 0 then c e else 0
  let b (e : Fin 5 →₀ ℕ) := if e j = 0 then 0 else c e
  refine ⟨∑ e ∈ Q.support, a e, ∑ e ∈ Q.support, b e, ?_⟩
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hdz (i : Fin 5) (hi : i ≠ 0) (hij : i ≠ j) : e i = 0 :=
    Nat.eq_zero_of_le_zero ((le_degreeOf_of_mem_support i he).trans (hzero i hi hij).le)
  have hmono :
      aeval v (monomial e (Q.coeff e)) = Polynomial.C (c e) * v j ^ e j := by
    rw [aeval_monomial]
    rcases hj with rfl | rfl
    · simp [Finsupp.prod_fintype, Fin.prod_univ_succ, hv, c,
        hdz 1 (by decide) (by decide), hdz 2 (by decide) (by decide),
        hdz 4 (by decide) (by decide), Polynomial.algebraMap_apply, mul_assoc]
    · simp [Finsupp.prod_fintype, Fin.prod_univ_succ, hv, c,
        hdz 1 (by decide) (by decide), hdz 2 (by decide) (by decide),
        hdz 3 (by decide) (by decide), Polynomial.algebraMap_apply, mul_assoc]
  rw [hmono]
  have he' := (le_degreeOf_of_mem_support j he).trans hl
  by_cases h : e j = 0
  · simp [a, b, h]
  · have he1 : e j = 1 := by omega
    simp [a, b, he1]

private def transpose (f : Polynomial F →+* E) :
    Polynomial (Polynomial F) →+* Polynomial E :=
  (Polynomial.mapRingHom f).comp (Polynomial.Bivariate.swap (R:=F)).toRingHom

private theorem transpose_graph (f : Polynomial F →ₐ[F] E) (q : ℕ)
    (Q : MvPolynomial (Fin 5) F) :
    transpose f.toRingHom (graph q Q) =
      aeval ![Polynomial.C (f Polynomial.X), 0, 0,
        Polynomial.X, (Polynomial.X (R:=E)) ^ q] Q := by
  have h : (transpose f.toRingHom).comp (graph (F:=F) q).toRingHom =
      (aeval ![Polynomial.C (f Polynomial.X), 0, 0,
        Polynomial.X, (Polynomial.X (R:=E)) ^ q]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [transpose, graph, Polynomial.algebraMap_apply, Polynomial.Bivariate.swap_C_C]
      exact f.commutes r
    · intro i
      fin_cases i <;> simp [transpose, graph, Polynomial.Bivariate.swap_X,
        Polynomial.Bivariate.swap_Y]
  exact RingHom.congr_fun h Q

private def columns (z U V : Polynomial E) : Fin 4 → Polynomial E :=
  ![U, Polynomial.X * U, V, z * V]

/-- The putative (1,1) plane shape gives a nontrivial dependence after
specialization, even if the lift carries a common graph content. -/
private theorem dependent_of_affine (z U V g : Polynomial E)
    (a b c d : E) (hU : U ≠ 0) (hg : g ≠ 0)
    (hA : g * U = Polynomial.C a + Polynomial.C b * z)
    (hB : g * V = Polynomial.C c + Polynomial.C d * Polynomial.X) :
    ¬ LinearIndependent E (columns z U V) := by
  intro hi
  have hrel : (Polynomial.C c + Polynomial.C d * Polynomial.X) * U =
      (Polynomial.C a + Polynomial.C b * z) * V := by
    rw [← hB, ← hA]
    ring
  have hcomb : ∑ i : Fin 4, (![c, d, -a, -b] : Fin 4 → E) i • columns z U V i = 0 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, columns,
      Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, Polynomial.smul_eq_C_mul, map_neg]
    linear_combination hrel
  have hz := Fintype.linearIndependent_iff.mp hi _ hcomb
  have ha : a = 0 := by simpa using hz 2
  have hb : b = 0 := by simpa using hz 3
  exact mul_ne_zero hg hU (by simpa [ha, hb] using hA)

private theorem no_pair_one_one_of_graph (q : ℕ) (f : Polynomial F →ₐ[F] E)
    (hf : Function.Injective f) (g : Polynomial F)
    (U V : MvPolynomial (Fin 5) F) (U' V' : Polynomial (Polynomial F))
    (hg : g ≠ 0) (hu : U' ≠ 0) (hU : OmitsMessages U) (hV : OmitsMessages V)
    (hGU : graph q U = Polynomial.C g * U') (hGV : graph q V = Polynomial.C g * V')
    (hr : Module.finrank E (Submodule.span E (Set.range
      (columns (Polynomial.X ^ q) (transpose f.toRingHom U') (transpose f.toRingHom V')))) = 4)
    (hs : sWeight U V = 1) (ht : tWeight U V = 1) : False := by
  let ψ := transpose f.toRingHom
  let v : Fin 5 → Polynomial E :=
    ![Polynomial.C (f Polynomial.X), 0, 0, Polynomial.X, Polynomial.X ^ q]
  have htrans (Q : MvPolynomial (Fin 5) F) : ψ (graph q Q) = aeval v Q :=
    transpose_graph f q Q
  have hU3 : U.degreeOf 3 = 0 := by unfold sWeight at hs; omega
  have hV4 : V.degreeOf 4 = 0 := by unfold tWeight at ht; omega
  obtain ⟨hU1, hU2⟩ := hU
  obtain ⟨hV1, hV2⟩ := hV
  have haxisU : ∀ i : Fin 5, i ≠ 0 → i ≠ 4 → U.degreeOf i = 0 := by
    intro i hi hj
    fin_cases i <;> simp_all
  have haxisV : ∀ i : Fin 5, i ≠ 0 → i ≠ 3 → V.degreeOf i = 0 := by
    intro i hi hj
    fin_cases i <;> simp_all
  have hU4 : U.degreeOf 4 ≤ 1 := by
    unfold tWeight at ht
    omega
  have hV3 : V.degreeOf 3 ≤ 1 := by
    unfold sWeight at hs
    omega
  obtain ⟨a, b, hab⟩ := affine_image U 4 (Or.inr rfl) _ v rfl hU4 haxisU
  obtain ⟨c, d, hcd⟩ := affine_image V 3 (Or.inl rfl) _ v rfl hV3 haxisV
  have hv4 : v 4 = (Polynomial.X (R:=E)) ^ q := rfl
  have hv3 : v 3 = (Polynomial.X (R:=E)) := rfl
  rw [← htrans, hGU, map_mul, hv4] at hab
  rw [← htrans, hGV, map_mul, hv3] at hcd
  have hψ : Function.Injective ψ :=
    (Polynomial.map_injective f.toRingHom hf).comp (Polynomial.Bivariate.swap (R:=F)).injective
  have hu' : ψ U' ≠ 0 := by
    intro h
    exact hu (hψ (h.trans (map_zero ψ).symm))
  have hg' : ψ (Polynomial.C g) ≠ 0 := by
    intro h
    exact hg (Polynomial.C_eq_zero.mp (hψ (h.trans (map_zero ψ).symm)))
  have hi : LinearIndependent E (columns (Polynomial.X ^ q) (ψ U') (ψ V')) :=
    linearIndependent_iff_card_eq_finrank_span.mpr
      (by simpa only [Set.finrank, Fintype.card_fin] using hr.symm)
  exact dependent_of_affine (Polynomial.X ^ q) (ψ U') (ψ V') (ψ (Polynomial.C g))
    a b c d hu' hg' hab hcd hi

open K21 K21_11

private theorem native_column_rank (q : ℕ) (U V : Bivar) :
    K21_8.columnRankAt q U V =
      Module.finrank Frac (Submodule.span Frac (Set.range (columns (Polynomial.X ^ q)
        (extendSeed (Polynomial.Bivariate.swap U)) (extendSeed (Polynomial.Bivariate.swap V))))) := by
  have hcols : (fun j : Fin 4 => extendSeed (Polynomial.Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V
        else seed ^ q * V))) = columns (Polynomial.X ^ q)
          (extendSeed (Polynomial.Bivariate.swap U)) (extendSeed (Polynomial.Bivariate.swap V)) := by
    funext j
    fin_cases j <;> simp [columns, extendSeed, seed, Polynomial.Bivariate.swap_X]
  unfold K21_8.columnRankAt
  rw [hcols]

private theorem no_pair_one_one {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) (hs : sWeight B.U B.V = 1) (ht : tWeight B.U B.V = 1) :
    False := by
  let f : Polynomial K →ₐ[K] Frac := IsScalarTower.toAlgHom K (Polynomial K) Frac
  have hf : Function.Injective f := IsFractionRing.injective (Polynomial K) Frac
  have hr' : K21_8.columnRankAt p D.U D.V = 4 := hr
  rw [native_column_rank] at hr'
  exact no_pair_one_one_of_graph p f hf A.content B.U B.V D.U D.V A.content_ne D.U_ne
    B.U_omits B.V_omits B.graphU B.graphV hr' hs ht

theorem actual_bank {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) :
    ∃ bank : Bank, sWeight B.U B.V = bank.dS ∧ tWeight B.U B.V = bank.dT := by
  obtain ⟨huS, huT, hvS, hvT⟩ := B.boxes
  have hS : sWeight B.U B.V = 1 ∨ sWeight B.U B.V = 2 ∨ sWeight B.U B.V = 3 := by
    unfold sWeight
    omega
  have hT : tWeight B.U B.V = 1 ∨ tWeight B.U B.V = 2 ∨ tWeight B.U B.V = 3 := by
    unfold tWeight
    omega
  rcases hS with hs | hs | hs <;> rcases hT with ht | ht | ht
  · exact (no_pair_one_one B hr hs ht).elim
  · exact ⟨.lowS, hs, ht⟩
  · exact ⟨.oneThree, hs, ht⟩
  · exact ⟨.lowT, hs, ht⟩
  · exact ⟨.symmetric, hs, ht⟩
  · exact ⟨.twoThree, hs, ht⟩
  · exact ⟨.threeOne, hs, ht⟩
  · exact ⟨.threeTwo, hs, ht⟩
  · exact ⟨.threeThree, hs, ht⟩

end
end K21_11_2
end Port_K1_11_2Bank

section Port_K1_11Annihilator
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace K21_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]

private theorem scalar_total_weight_le (G : MvPolynomial (Fin 4) F) (a b : ℕ)
    (hA : G.weightedTotalDegree scalarWeightYS ≤ a)
    (hB : G.weightedTotalDegree scalarWeightT ≤ b) :
    G.weightedTotalDegree scalarWeightTotal ≤ a + b := by
  apply Finset.sup_le
  intro e he
  have ha := (le_weightedTotalDegree scalarWeightYS he).trans hA
  have hb := (le_weightedTotalDegree scalarWeightT he).trans hB
  simp [scalarWeightYS,scalarWeightT,scalarWeightTotal,Finsupp.weight_apply,
    Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul] at ha hb ⊢
  omega

open K21

private theorem bank_cancel (b : Bank) : 1 + (b.dT - 1) = b.dT := by cases b <;> rfl

theorem exists_annihilator {u : Words} {deleted : Finset I} {P : Puncture deleted}
    {b : Bank} {H : ℕ} (C : ContactInput u P b H) (h : ℕ)
    (hmin : 24549 ≤ h) (hmax : h ≤ 32872) (hH : H + deleted.card = h)
    {Γ : Finset K} (F : Marks u deleted Γ) : Nonempty (Annihilator F b) := by
  obtain ⟨G, hG, hgAnn⟩ := exists_two_decoder_source C h hmin hmax hH
  let Q := scalarEliminant 5 G.val C.numerator C.denominator
  have hne : Q ≠ 0 := scalarEliminant_ne_zero 720675 131071 5 b.s b.t
    G.val C.L G.property hG C.numerator C.denominator C.denominator_ne C.linear C.primitive
  obtain ⟨hY, hS, hT⟩ := polynomialView_source_coefficients 720675 131071 5 b.s b.t G.val G.property
  have hy : Q.weightedTotalDegree scalarWeightY ≤ 5 := by
    simpa [Q, scalarEliminant] using
      clearedEval_weight_bound scalarWeightY 5 5 1 1 0 (polynomialView G.val)
        C.numerator C.denominator (by simpa using hY) C.numerator_Y C.denominator_Y (by omega)
  have hs : Q.weightedTotalDegree scalarWeightYS ≤ b.a := by
    simpa [Q, scalarEliminant, Bank.a] using
      clearedEval_weight_bound scalarWeightYS 5 b.s 0 b.dS b.dS (polynomialView G.val)
        C.numerator C.denominator (by simpa using hS) C.numerator_S C.denominator_S (by omega)
  have ht : Q.weightedTotalDegree scalarWeightT ≤ b.b := by
    simpa [Q, scalarEliminant, Bank.b] using
      clearedEval_weight_bound scalarWeightT 5 b.t 1 b.dT (b.dT-1) (polynomialView G.val)
        C.numerator C.denominator (by simpa using hT) C.numerator_T C.denominator_T (bank_cancel b).ge
  refine ⟨⟨Q, hne, hy, hs, ht, scalar_total_weight_le Q b.a b.b hs ht, ?_⟩⟩
  intro γ hγ
  let M := F.mark γ hγ
  let S := indexedSupport P M.support
  have hS : 180169 ≤ S.card := by
    rw [indexedSupport_card P M.support (F.survives γ hγ)]
    exact M.agreement
  have hd := mark_degree M
  have hd' : (M.decoder.map twist).natDegree ≤ 131071 :=
    Polynomial.natDegree_map_le.trans hd
  have hcorrect := correctOn_mark P M
  have hrel := relation_annihilates C (by omega) _ _ hd hd' γ (γ ^ p) S hS hcorrect
  exact scalarEliminant_annihilates 720675 131071 5 b.s b.t G.val C.L G.property
    C.numerator C.denominator C.linear _ _ γ (γ^p) hrel
    (hgAnn _ _ hd hd' γ (γ^p) S hS hcorrect)

end
end K21_11
end Port_K1_11Annihilator

section Port_K1_11_2_2AuxGraph
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace K21_11_2_2
noncomputable section

open MvPolynomial K21_11_2

variable {F : Type*} [Field F]

/-- Evaluate the X-coordinate while retaining the two formal parameters. -/
def parameterNode (x : F) : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval ![C x, 0, 0, MvPolynomial.X 3, MvPolynomial.X 4]

theorem nodeWord_omits (x a b c d : F) (Q : MvPolynomial (Fin 5) F)
    (hQ : OmitsMessages Q) : nodeWordMap x a b c d Q = parameterNode x Q := by
  change eval₂ C (nodeWordImages x a b c d) Q = eval₂ C ![C x, 0, 0, MvPolynomial.X 3, MvPolynomial.X 4] Q
  apply eval₂_congr
  intro i e hi hc
  have ht := omitted_message_tag Q hQ e (mem_support_iff.mpr hc)
  have hin := Finsupp.mem_support_iff.mp hi
  fin_cases i <;> simp_all [nodeWordImages]

/-- Substitute the formal parameters by Z and Z^q after evaluating X. -/
def seedEval (q : ℕ) : MvPolynomial (Fin 5) F →ₐ[F] Polynomial F :=
  aeval ![0, 0, 0, Polynomial.X, Polynomial.X ^ q]

theorem eval_graph (q : ℕ) (x : F) (Q : MvPolynomial (Fin 5) F) :
    (graph q Q).eval (Polynomial.C x) = seedEval q (parameterNode x Q) := by
  have heq : (Polynomial.evalRingHom (Polynomial.C x)).comp (graph (F := F) q).toRingHom =
      (seedEval q).toRingHom.comp (parameterNode x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [graph, seedEval, parameterNode, Polynomial.algebraMap_apply]
    · intro i
      fin_cases i <;> simp [graph, seedEval, parameterNode]
  exact RingHom.congr_fun heq Q

end
end K21_11_2_2
end Port_K1_11_2_2AuxGraph

section Port_K1_11Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K21_11
open K21

/-- The original minimal relation admits a low-bidegree independent lift
up to seed content. The height floor concerns the unpunctured kernel. -/
def c1 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    NormalSaturation R → columnRank D.U D.V = 4 →
    (∃ γ, Normal u γ ∧ Nonempty (BadMark u γ)) →
    Nonempty (IndependentLift R)

/-- Pass from the independent lift to the primitive punctured equation,
its actual bank, and its exact formal contact with the original words. -/
def c2 : Prop :=
  ∀ (u : Words) (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    columnRank D.U D.V = 4 → T.height ≤ 32872 →
    ∀ (_L : IndependentLift R) (P : Puncture (fixedNodes R)),
      ∃ b, Nonempty (ContactInput u P b D.height)

/-- One coefficient pays the zero specializations. At most five derivative
charts carry the remaining actual decoders with their Taylor node cuts. -/
def c3 : Prop :=
  ∀ (u : Words) (deleted : Finset I) (P : Puncture deleted)
    (Γ : Finset K) (F : Marks u deleted Γ) (b : Bank),
    Annihilator F b →
    ∃ (exceptional : Finset K) (charts : Fin 5 → Finset K),
      exceptional.card ≤ b.zeroFee ∧
      (∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j) ∧
      ∀ j, charts j = ∅ ∨ Nonempty (TaylorChart u P F b (charts j))

private theorem card_from_cover (b : Bank) (Γ exceptional : Finset K)
    (charts : Fin 5 → Finset K) (hfee : exceptional.card ≤ b.zeroFee)
    (hcover : ∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j)
    (hcharts : ∀ j, ((charts j).card : ℚ) ≤ b.chartFee) :
    Γ.card ≤ 150000000000000000 := by
  classical
  have hsub : Γ ⊆ exceptional ∪ Finset.univ.biUnion charts := by
    intro γ hγ
    exact Finset.mem_union.mpr ((hcover γ hγ).imp id (fun ⟨j, hj⟩ =>
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩))
  have hcount := (Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _ |>.trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hbound : (Γ.card : ℚ) ≤ b.zeroFee + 5 * b.chartFee := by
    calc
      (Γ.card : ℚ) ≤ (exceptional.card : ℚ) + ∑ j : Fin 5, ((charts j).card : ℚ) := by
        exact_mod_cast hcount
      _ ≤ (b.zeroFee : ℚ) + ∑ _j : Fin 5, b.chartFee := by
        exact add_le_add (by exact_mod_cast hfee) (Finset.sum_le_sum fun j _ => hcharts j)
      _ = _ := by simp
  exact_mod_cast hbound.trans (final_fee b)

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K21.c11 := by
  intro u hu T R D hsat hr Γ hΓ hn
  classical
  rcases Γ.eq_empty_or_nonempty with rfl | ⟨γ, hγ⟩
  · simp
  have hmax : T.height ≤ 32872 := by
    unfold TwoActive.height
    have := T.nullitySum
    have := T.degreeSum
    have := hu.1
    omega
  obtain ⟨L⟩ := h1 u hu T R D hsat hr ⟨γ, hn γ hγ, K21.bad_mark u Γ hΓ γ hγ⟩
  let P := nativePuncture (fixedNodes R)
  let F := selectMarks D hΓ hn
  obtain ⟨b, ⟨C⟩⟩ := h2 u T R D hr hmax L P
  obtain ⟨Q⟩ := exists_annihilator C T.height L.original_height hmax D.height_eq F
  obtain ⟨exceptional, charts, hfee, hcover, hcharts⟩ :=
    h3 u (fixedNodes R) P Γ F b Q
  refine card_from_cover b Γ exceptional charts hfee hcover fun j => ?_
  rcases hcharts j with he | chart
  · simpa [he] using chartFee_nonneg b
  · exact chart_count (Classical.choice chart)

end K21_11
end Port_K1_11Split

section Port_K1_11_3Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace K21_11_3
noncomputable section

open K21 K21_11 MvPolynomial

/-- The common Taylor numerators have controlled total degree in Y,S,T. -/
def c1 : Prop :=
  ∀ {F : Type} [Field F] (G : MvPolynomial (Fin 4) F) (w E : ℕ),
    2 ≤ E → G.weightedTotalDegree scalarWeightTotal ≤ E →
    ∀ n ≤ w, (paddedTaylorCoeff G w n).weightedTotalDegree scalarWeightTotal ≤
      (2 * w - 1) * (E - 1) + 1

/-- The marked solution's Hasse coefficients are the specialized common numerators
after multiplication by the separant power. -/
def c2 : Prop :=
  ∀ {F : Type} [Field F] (G : MvPolynomial (Fin 4) F) (w : ℕ)
    (D : Polynomial F) (s t : F),
    aeval (scalarImages D s t) G = 0 →
    ∀ n ≤ w, (↑(Nat.factorial n) : F) ≠ 0 →
      aeval (scalarImages D s t) (paddedTaylorCoeff G w n) =
        aeval (scalarImages D s t) (pderiv 1 G) ^ (2 * w - 1) *
          Polynomial.hasseDeriv n D

section Field
variable {F : Type} [Field F]

private abbrev XF (F : Type) [Field F] := FractionRing (Polynomial F)

private def ξ : XF F := algebraMap (Polynomial F) (XF F) Polynomial.X

private def centerImages : Fin 4 → MvPolynomial (Fin 3) (XF F) :=
  ![C (ξ (F := F)), MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2]

private def atCenter : MvPolynomial (Fin 4) F →ₐ[F] MvPolynomial (Fin 3) (XF F) :=
  aeval centerImages

private def centerPoint (D : Polynomial F) (s t : F) : Fin 3 → XF F :=
  ![algebraMap (Polynomial F) (XF F) D, algebraMap F (XF F) s, algebraMap F (XF F) t]

private theorem atCenter_degree (G : MvPolynomial (Fin 4) F) :
    (atCenter G).totalDegree ≤ G.weightedTotalDegree scalarWeightTotal := by
  let ι := algebraMap F (XF F)
  have hm : aeval (R := XF F) (centerImages (F := F)) (MvPolynomial.map ι G) =
      atCenter G := MvPolynomial.aeval_map_algebraMap (A := XF F) _ _
  rw [← hm, ← weightedTotalDegree_one]
  refine (weightedTotalDegree_aeval_le_of_le scalarWeightTotal (1 : Fin 3 → ℕ)
    centerImages (MvPolynomial.map ι G) ?_).trans ?_
  · intro i
    fin_cases i <;> simp [centerImages, scalarWeightTotal, weightedTotalDegree_one]
  · exact Finset.sup_mono (support_map_subset _ _)

private theorem pderiv_atCenter (G : MvPolynomial (Fin 4) F) :
    pderiv (0 : Fin 3) (atCenter G) = atCenter (pderiv 1 G) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a => simp [atCenter]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a j ha =>
    simp only [map_mul, pderiv_mul, map_add, ha]
    fin_cases j <;> simp [atCenter, centerImages]

private theorem emb_C (a : F) :
    algebraMap (Polynomial F) (XF F) (Polynomial.C a) = algebraMap F (XF F) a := by
  rw [IsScalarTower.algebraMap_apply F (Polynomial F) (XF F), Polynomial.algebraMap_eq]

private theorem eval_atCenter (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) :
    MvPolynomial.eval (centerPoint D s t) (atCenter G) =
      algebraMap (Polynomial F) (XF F) (aeval (scalarImages D s t) G) := by
  have h : (MvPolynomial.eval (centerPoint D s t)).comp atCenter.toRingHom =
      (algebraMap (Polynomial F) (XF F)).comp (aeval (scalarImages D s t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [atCenter, Polynomial.algebraMap_eq, emb_C]
    · intro i
      fin_cases i <;> simp [atCenter, centerImages, centerPoint, scalarImages, ξ, emb_C]
  exact RingHom.congr_fun h G

private theorem eval_at_ξ (D : Polynomial F) :
    (D.map (algebraMap F (XF F))).eval (ξ (F := F)) =
      algebraMap (Polynomial F) (XF F) D := by
  rw [Polynomial.eval_map]
  have h : Polynomial.eval₂RingHom (algebraMap F (XF F)) ξ =
      algebraMap (Polynomial F) (XF F) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [emb_C]
    · simp [ξ]
  exact RingHom.congr_fun h D

private theorem derivativeChart_degree (G : MvPolynomial (Fin 4) F) (j : ℕ) :
    (derivativeChart G j).weightedTotalDegree scalarWeightTotal ≤
      G.weightedTotalDegree scalarWeightTotal := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      unfold derivativeChart at *
      rw [Function.iterate_succ_apply']
      exact (weightedTotalDegree_pderiv_le _ _ _).trans ih

private def denominator (G : MvPolynomial (Fin 4) F) (w : ℕ) :
    MvPolynomial (Fin 3) (XF F) :=
  atCenter (pderiv 1 G) ^ (2 * w - 1)

private def numerator (G : MvPolynomial (Fin 4) F) (w : ℕ) :
    Polynomial (MvPolynomial (Fin 3) (XF F)) :=
  Polynomial.centeredCoefficientPrefix (C ξ) (fun n => atCenter (paddedTaylorCoeff G w n)) (w + 1)

private theorem natDegree_le_of_degree_lt_succ {R : Type} [Semiring R]
    {D : Polynomial R} {w : ℕ} (h : D.degree < ↑(w + 1)) : D.natDegree ≤ w := by
  by_cases hz : D = 0
  · simp [hz]
  · exact Nat.le_of_lt_succ ((Polynomial.natDegree_lt_iff_degree_lt hz).mpr h)

private theorem numerator_degree (G : MvPolynomial (Fin 4) F) (w : ℕ) :
    (numerator G w).natDegree ≤ w :=
  natDegree_le_of_degree_lt_succ
    (Polynomial.degree_centeredCoefficientPrefix_lt
      (C ξ) (fun n => atCenter (paddedTaylorCoeff G w n)) (w + 1))

private theorem numerator_eval_degree (h1 : c1) (G : MvPolynomial (Fin 4) F) (w E : ℕ)
    (hE : 2 ≤ E) (hG : G.weightedTotalDegree scalarWeightTotal ≤ E) (x : XF F) :
    ((numerator G w).eval (C x)).totalDegree ≤ (2 * w - 1) * (E - 1) + 1 := by
  unfold numerator Polynomial.centeredCoefficientPrefix
  rw [Polynomial.taylor_eval, Polynomial.eval_finsetSum]
  apply totalDegree_finsetSum_le
  intro n _
  rw [Polynomial.eval_monomial, ← map_neg, ← map_add, ← map_pow]
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, add_zero]
    exact (atCenter_degree _).trans (h1 G w E hE hG n (Nat.le_of_lt_succ n.isLt)))

private theorem denominator_degree (G : MvPolynomial (Fin 4) F) (w E : ℕ)
    (hG : G.weightedTotalDegree scalarWeightTotal ≤ E) :
    (denominator G w).totalDegree ≤ (2 * w - 1) * (E - 1) := by
  apply (totalDegree_pow _ _).trans
  apply Nat.mul_le_mul_left
  exact (atCenter_degree _).trans
    ((weightedTotalDegree_pderiv_le_sub scalarWeightTotal 1 G).trans
      (Nat.sub_le_sub_right hG 1))

private theorem reconstruct (h2 : c2) (G : MvPolynomial (Fin 4) F) (w : ℕ)
    (D : Polynomial F) (s t : F) (hD : D.natDegree ≤ w)
    (hroot : aeval (scalarImages D s t) G = 0)
    (hfactor : ∀ n ≤ w, (↑(Nat.factorial n) : F) ≠ 0) :
    (numerator G w).map (MvPolynomial.eval (centerPoint D s t)) =
      Polynomial.C (MvPolynomial.eval (centerPoint D s t) (denominator G w)) *
        D.map (algebraMap F (XF F)) := by
  let ev := MvPolynomial.eval (centerPoint D s t)
  change (numerator G w).map ev = Polynomial.C (ev (denominator G w)) * _
  apply Polynomial.taylor_injective ξ
  ext n
  have hm := Polynomial.map_taylor (numerator G w) (C (ξ (F := F))) ev
  change _ = Polynomial.taylor (ev (C ξ)) _ at hm
  rw [MvPolynomial.eval_C] at hm
  rw [← hm, Polynomial.coeff_map, numerator, Polynomial.coeff_taylor_centeredCoefficientPrefix]
  rw [show Polynomial.taylor ξ (Polynomial.C (ev (denominator G w)) *
      D.map (algebraMap F (XF F))) =
      Polynomial.C (ev (denominator G w)) *
        Polynomial.taylor ξ (D.map (algebraMap F (XF F))) by
    calc
      _ = Polynomial.taylor ξ (Polynomial.C (ev (denominator G w))) *
          Polynomial.taylor ξ (D.map (algebraMap F (XF F))) :=
        map_mul (Polynomial.taylorAlgHom ξ) _ _
      _ = _ := by rw [Polynomial.taylor_C]]
  rw [Polynomial.coeff_C_mul]
  split_ifs with hn
  · have h := h2 G w D s t hroot n (Nat.le_of_lt_succ hn) (hfactor n (Nat.le_of_lt_succ hn))
    rw [show ev (atCenter (paddedTaylorCoeff G w n)) = _ from eval_atCenter _ D s t,
      h, map_mul, map_pow, Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_at_ξ]
    simp only [denominator, map_pow, ev, eval_atCenter]
  · have hd : (Polynomial.taylor ξ (D.map (algebraMap F (XF F)))).natDegree < n := by
      rw [Polynomial.natDegree_taylor]
      exact Polynomial.natDegree_map_le.trans_lt (hD.trans_lt (by omega))
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd, mul_zero, map_zero]

end Field

private theorem build_chart (h1 : c1) (h2 : c2)
    {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank)
    (Λ : Finset K) (hsub : Λ ⊆ Γ) (hne : Λ.Nonempty)
    (G : MvPolynomial (Fin 4) K) (hG : G.weightedTotalDegree scalarWeightTotal ≤ b.E)
    (hroot : ∀ γ (hγ : γ ∈ Λ),
      SimpleRoot G (F.mark γ (hsub hγ)).decoder γ (γ ^ p)) :
    Nonempty (TaylorChart u P F b Λ) := by
  classical
  let point (γ : K) : Fin 3 → Frac := if h : γ ∈ Λ then
    centerPoint (F.mark γ (hsub h)).decoder γ (γ ^ p) else fun _ => 0
  have hpnt (γ : K) (hγ : γ ∈ Λ) :
      point γ = centerPoint (F.mark γ (hsub hγ)).decoder γ (γ ^ p) := by
    simp [point, hγ]
  refine ⟨{
    subset := hsub
    equation := atCenter G
    equation_ne := ?_
    equation_degree := (atCenter_degree G).trans hG
    numerator := numerator G 131071
    numerator_degree := numerator_degree _ _
    denominator := denominator G 131071
    cut_degree := ?_
    point := point
    slope := fun γ hγ => by rw [hpnt γ hγ]; rfl
    on_equation := fun γ hγ => by rw [hpnt γ hγ, eval_atCenter, (hroot γ hγ).1, map_zero]
    regular := ?_
    reconstruction := ?_ }⟩
  · obtain ⟨γ, hγ⟩ := hne
    have hn := (hroot γ hγ).2
    intro hz
    apply hn
    apply (IsFractionRing.injective (Polynomial K) Frac)
    rw [map_zero, ← eval_atCenter, ← pderiv_atCenter, hz, map_zero, map_zero]
  · intro i
    unfold nodeCut
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact numerator_eval_degree h1 G 131071 b.E (by cases b <;> decide) hG _
    · apply (totalDegree_mul _ _).trans
      have ha : (C (σ := Fin 3) (algebraMap K Frac (u 0 (P.index i))) +
          MvPolynomial.X 1 * C (algebraMap K Frac (u 1 (P.index i)))).totalDegree ≤ 1 := by
        exact (totalDegree_add _ _).trans (max_le (by simp)
          ((totalDegree_mul _ _).trans (by simp)))
      exact Nat.add_le_add (denominator_degree G 131071 b.E hG) ha
  · intro γ hγ
    rw [hpnt γ hγ, denominator, map_pow, eval_atCenter]
    exact pow_ne_zero _ (fun h => (hroot γ hγ).2
      ((IsFractionRing.injective (Polynomial K) Frac) (h.trans (map_zero _).symm)))
  · intro γ hγ
    rw [hpnt γ hγ]
    apply reconstruct h2
    · exact natDegree_le_of_degree_lt_succ (F.mark γ (hsub hγ)).degree
    · exact (hroot γ hγ).1
    · intro n hn
      have pp := CharP.char_is_prime_of_two_le K p (by decide)
      intro hz
      have hn' := pp.dvd_factorial.mp ((CharP.cast_eq_zero_iff K p _).mp hz)
      exact (not_lt_of_ge (hn'.trans hn)) (by decide)

theorem of_children (h1 : c1) (h2 : c2) : K21_11.c3 := by
  intro u deleted P Γ F b A
  obtain ⟨exceptional, charts, hfee, hcover, hcharts⟩ := assign A
  refine ⟨exceptional, charts, hfee, hcover, fun j => ?_⟩
  rcases (charts j).eq_empty_or_nonempty with he | hn
  · exact Or.inl he
  · obtain ⟨hsub, hroot⟩ := hcharts j
    exact Or.inr (build_chart h1 h2 P F b (charts j) hsub hn (derivativeChart A.Q j)
      ((derivativeChart_degree A.Q j).trans A.degreeTotal) hroot)

end
end K21_11_3
end Port_K1_11_3Split

section Port_K1_11_2Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K21_11_2
noncomputable section

open K21 K21_11 MvPolynomial

/-- Divide the independent lift by the fixed node locator and retain the
plane pair with its exact reduced height and no common nonunit divisor. -/
def c1 : Prop :=
  ∀ (u : Words) (T : TwoActive u) (R : Relation T) (D : Reduction u T R)
    (A : IndependentLift R), Nonempty (ReducedPair D A)

/-- Interpolate the actual retained-node output within the reduced height
and the two parameter degrees of the received-pencil combination. -/
def c2 : Prop :=
  ∀ (u : Words) (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    T.height ≤ 32872 →
    ∀ (A : IndependentLift R) (B : ReducedPair D A) (P : Puncture (fixedNodes R)),
      Nonempty (PlaneOutput u P D.height B.U B.V)

theorem of_children (h1 : c1) (h2 : c2) : K21_11.c2 := by
  intro u T R D hr hH A P
  obtain ⟨B⟩ := h1 u T R D A
  obtain ⟨W⟩ := h2 u T R D hH A B P
  obtain ⟨bank, hs, ht⟩ := actual_bank B hr
  let L := equation B.U B.V W.W
  have hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) =
      sourceBounds (131071 + D.height) 1 bank.dS bank.dT j := by
    simpa only [L, equation, hs, ht] using equation_degrees 131071 D.height B.U B.V W.W
      B.U_ne B.V_ne B.U_omits B.V_omits W.omits B.height W.height W.degreeS W.degreeT
  have hL : L ≠ 0 := by
    intro hz
    have he := hdeg 1
    simp [hz, sourceBounds, weightedTotalDegree] at he
  have hf : L ∈ filtered (sourceWeights 131071)
      (sourceBounds (131071 + D.height) 1 bank.dS bank.dT) :=
    (mem_filtered _ _ _).mpr fun j => (hdeg j).le
  obtain ⟨hy, hdy, hns, hds, hnt, hdt⟩ := decoder_bounds 131071 D.height bank.dS bank.dT
    B.U B.V W.W B.U_omits B.V_omits W.omits B.V_ne hf
  refine ⟨bank, ⟨{
    L := L
    L_ne := hL
    degrees := hdeg
    order_one := ?_
    numerator := decoderNumerator B.U W.W
    denominator := decoderDenominator B.V
    denominator_ne := decoderDenominator_ne B.V B.V_omits B.V_ne
    linear := equation_linear B.U B.V W.W B.U_omits B.V_omits W.omits
    primitive := equation_primitive B.U B.V W.W B.U_omits B.V_omits W.omits B.V_ne B.relPrime
    numerator_Y := hy
    denominator_Y := hdy
    numerator_S := hns
    denominator_S := hds
    numerator_T := hnt
    denominator_T := hdt
  }⟩⟩
  intro i
  exact linear_relation_contact_order_one _ _ _ _ _ B.U B.V W.W B.relPrime
    B.U_omits B.V_omits W.omits (W.node i)

end
end K21_11_2
end Port_K1_11_2Split

section Port_K1_11_1Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace K21_11_1

noncomputable section

open Polynomial Matrix FrobeniusLocator K21

/-- The shift minors are primitive, and a single-block minor attains
each positive coefficient degree after multiplication by the shift count. -/
def c1 : Prop :=
  ∀ (F : Type) [Field F] (h L s : ℕ)
    (Q : Fin 2 × Fin (h + 1) → Seeds F),
    h + s = L → 0 < s → Q ≠ 0 → coefficientPrimitive Q →
    let W := K1_6.shifts (planePair Q) L s
    coefficientPrimitive (K1_6.maximalMinors W) ∧
      ∀ b i : Fin 2, 0 < blockDegree Q b i →
        ∃ rows : Fin s → Fin L,
          (K1_6.maximalMinors W (fun j => (b, rows j))).degreeOf i =
            s * blockDegree Q b i

/-- A primitive shift wedge has the complementary-minor degree bound.
A minor supported in one block omits exactly s positions in that block. -/
def c2 : Prop :=
  ∀ (F : Type) [Field F] (L w s : ℕ)
    (M : Matrix (Fin 2 × Fin L) (Fin w) (Seeds F))
    (W : Matrix (Fin 2 × Fin L) (Fin s) (Seeds F)),
    0 < s → s ≤ L →
    (M.map (algebraMap (Seeds F) (PlaneField F))).rank + s = 2 * L →
    W.transpose * M = 0 →
    (∀ b j (i : Fin 2), (M b j).degreeOf i ≤ if b.1 = i then 1 else 0) →
    coefficientPrimitive (K1_6.maximalMinors W) →
    ∀ (b i : Fin 2) (rows : Fin s → Fin L),
      (K1_6.maximalMinors W (fun j => (b, rows j))).degreeOf i ≤
        if b = i then L - s else L

private theorem degree_lt_of_product (s d n bound : ℕ)
    (hd : s * d ≤ bound) (hn : bound < s * n) : d < n := by
  by_contra! h
  have := Nat.mul_le_mul_left s h
  omega

theorem of_children (h1 : c1) (h2 : c2) : K21_11.c1 := by
  intro u front T R D _ hr _
  classical
  let h := T.height
  let s := 49097 - h
  have hBalance : 49097 + h + nullity u = 81976 ∧ h ≤ 32872 ∧ h < 49097 :=
    Native6921Balance (nullity u) T.a T.b T.c
      T.top T.degreeSum T.nullitySum (by have := front.1; omega)
  obtain ⟨hbal, hhi, hL⟩ := hBalance
  have hsum : h + s = 49097 := by omega
  have hs : 16225 ≤ s := by omega
  have hSlice := plane_first_slice_nullity u T hhi
  obtain ⟨Q, hQne, hQ, hPrim⟩ := plane_generator _ (by rw [hSlice]; decide)
  let M := planeStack p node (u 0) (u 1) 49097 81975
  let W := K1_6.shifts (planePair Q) 49097 s
  have hRank : (M.map (algebraMap (Seeds K) (PlaneField K))).rank + s = 2 * 49097 := by
    rw [plane_stack_rank u, K21.actual_stackRank u]
    omega
  have hker : W.transpose * M = 0 :=
    shifts_annihilate p node (u 0) (u 1) h 49097 s 81975 hsum Q hQ
  obtain ⟨hMP, hattain⟩ := h1 K h 49097 s Q hsum (by omega) hQne hPrim
  have hprod (b i : Fin 2) :
      s * blockDegree Q b i ≤ if b = i then h else 49097 := by
    by_cases hd : blockDegree Q b i = 0
    · simp [hd]
    obtain ⟨rows, hdet⟩ := hattain b i (Nat.pos_of_ne_zero hd)
    have hb := h2 K 49097 81976 s M W (by omega) (by omega) hRank hker
      (plane_stack_degree u) hMP b i rows
    rw [hdet] at hb
    simpa only [show 49097 - s = h by omega] using hb
  have h00 : blockDegree Q 0 0 ≤ 2 := by
    apply Nat.le_of_lt_succ
    exact degree_lt_of_product s _ 3 h (by simpa using hprod 0 0) (by omega)
  have h01 : blockDegree Q 0 1 ≤ 3 := by
    apply Nat.le_of_lt_succ
    exact degree_lt_of_product s _ 4 49097 (by simpa using hprod 0 1) (by omega)
  have h10 : blockDegree Q 1 0 ≤ 3 := by
    apply Nat.le_of_lt_succ
    exact degree_lt_of_product s _ 4 49097 (by simpa using hprod 1 0) (by omega)
  have h11 : blockDegree Q 1 1 ≤ 2 := by
    apply Nat.le_of_lt_succ
    exact degree_lt_of_product s _ 3 h (by simpa using hprod 1 1) (by omega)
  have hgraph : (fun j => graph p (Q j)) ≠ 0 := by
    intro hz
    apply hQne
    funext j
    change Q j = 0
    by_contra hne
    have hdeg : (Q j).degreeOf 0 ≤ 3 := by
      obtain ⟨b, j⟩ := j
      apply (degreeOf_coordinate Q b 0 j).trans
      fin_cases b
      · exact h00.trans (by decide)
      · exact h10
    exact graph_ne_zero p (by decide) _ hne (hdeg.trans_lt (by decide)) (congrFun hz j)
  obtain ⟨c, hc, hgraphQ⟩ := graph_content u T R Q hQ hgraph
  have hlo : 24549 ≤ T.height := by
    by_contra! hh
    change h < 24549 at hh
    apply exclude_affine D p (by decide) hr Q c hc hgraphQ
    · exact Nat.lt_one_iff.mp
        (degree_lt_of_product s _ 1 h (by simpa using hprod 0 0) (by omega))
    · exact Nat.le_of_lt_succ
        (degree_lt_of_product s _ 2 49097 (by simpa using hprod 0 1) (by omega))
    · exact Nat.le_of_lt_succ
        (degree_lt_of_product s _ 2 49097 (by simpa using hprod 1 0) (by omega))
    · exact Nat.lt_one_iff.mp
        (degree_lt_of_product s _ 1 h (by simpa using hprod 1 1) (by omega))
  refine ⟨{
    U := intoFive (planePair Q 0)
    V := intoFive (planePair Q 1)
    omitted := ⟨intoFive_omitted Q 0 1 (Or.inl rfl), intoFive_omitted Q 0 2 (Or.inr rfl),
      intoFive_omitted Q 1 1 (Or.inl rfl), intoFive_omitted Q 1 2 (Or.inr rfl)⟩
    heights := ⟨intoFive_height Q 0, intoFive_height Q 1⟩
    boxes := ⟨(intoFive_seed_degree Q 0 0).trans h00, (intoFive_seed_degree Q 0 1).trans h01,
      (intoFive_seed_degree Q 1 0).trans h10, (intoFive_seed_degree Q 1 1).trans h11⟩
    primitive := intoFive_primitive Q hPrim
    content := c
    content_ne := hc
    graphU := (graph_intoFive p (planePair Q 0)).trans (graph_pair R p Q c hgraphQ 0)
    graphV := (graph_intoFive p (planePair Q 1)).trans (graph_pair R p Q c hgraphQ 1)
    original_height := hlo
  }⟩


end

end K21_11_1
end Port_K1_11_1Split

section Port_K1_11_2_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K21_11_2_1
noncomputable section

open K21 K21_11 K21_11_2 MvPolynomial FrobeniusLocator

variable {F : Type*} [Field F]

/-- The graph map on the coefficients of the polynomial in the node coordinate. -/
def coefficientGraph (q : ℕ) : MvPolynomial (Fin 4) F →ₐ[F] Polynomial F :=
  aeval ![0, 0, Polynomial.X, Polynomial.X ^ q]

theorem graph_eq_map (q : ℕ) (P : MvPolynomial (Fin 5) F) :
    graph q P = (finSuccEquiv F 4 P).map (coefficientGraph q).toRingHom := by
  have h : graph (F := F) q =
      (Polynomial.mapAlgHom (coefficientGraph q)).comp (finSuccEquiv F 4).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change graph q (MvPolynomial.X 0) =
        (finSuccEquiv F 4 (MvPolynomial.X 0)).map (coefficientGraph q).toRingHom
      simp [graph, finSuccEquiv_X_zero]
    · change graph q (MvPolynomial.X j.succ) =
        (finSuccEquiv F 4 (MvPolynomial.X j.succ)).map (coefficientGraph q).toRingHom
      rw [finSuccEquiv_X_succ, Polynomial.map_C]
      fin_cases j <;> simp [graph, coefficientGraph]
  exact DFunLike.congr_fun h P

private def coefficientVars : Fin 2 → Fin 4 := ![2, 3]

private theorem coefficientVars_injective : Function.Injective coefficientVars := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | contradiction

theorem coefficientGraph_ne_zero (q : ℕ) (hq : 0 < q) (Q : MvPolynomial (Fin 4) F)
    (hQ : Q ≠ 0) (h0 : Q.degreeOf 0 = 0) (h1 : Q.degreeOf 1 = 0)
    (hS : Q.degreeOf 2 < q) : coefficientGraph q Q ≠ 0 := by
  classical
  obtain ⟨R, rfl⟩ := exists_rename_eq_of_vars_subset_range Q coefficientVars
    coefficientVars_injective (by
      intro i hi
      have hi' := mem_vars_iff_degreeOf_ne_zero.mp hi
      fin_cases i
      · exact (hi' h0).elim
      · exact (hi' h1).elim
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)
  have hR : R ≠ 0 := fun h => hQ (by rw [h, map_zero])
  have hdeg : R.degreeOf 0 < q := by
    rw [← degreeOf_rename_of_injective coefficientVars_injective (0 : Fin 2)]
    exact hS
  have he : coefficientGraph (F := F) q (rename coefficientVars R) =
      K1_14.frobeniusGraph q R := by
    have hv : (![0, 0, Polynomial.X, Polynomial.X ^ q] : Fin 4 → Polynomial F) ∘
        coefficientVars = ![Polynomial.X, Polynomial.X ^ q] := by
      funext i
      fin_cases i <;> rfl
    rw [coefficientGraph, aeval_rename, hv, K1_14.frobeniusGraph]
  rw [he]
  exact K1_14.frobeniusGraph_ne_zero q hq R hR hdeg

theorem coefficientGraph_coeff_ne_zero (q : ℕ) (hq : 0 < q)
    (P : MvPolynomial (Fin 5) F) (hP : OmitsMessages P)
    (hS : P.degreeOf 3 < q) (i : ℕ) (hi : (finSuccEquiv F 4 P).coeff i ≠ 0) :
    coefficientGraph q ((finSuccEquiv F 4 P).coeff i) ≠ 0 := by
  apply coefficientGraph_ne_zero q hq _ hi
  · exact Nat.eq_zero_of_le_zero ((degreeOf_coeff_finSuccEquiv P 0 i).trans hP.1.le)
  · exact Nat.eq_zero_of_le_zero ((degreeOf_coeff_finSuccEquiv P 1 i).trans hP.2.le)
  · exact (degreeOf_coeff_finSuccEquiv P 2 i).trans_lt hS

theorem graph_natDegree (q : ℕ) (hq : 0 < q) (P : MvPolynomial (Fin 5) F)
    (hP : OmitsMessages P) (hS : P.degreeOf 3 < q) :
    (graph q P).natDegree = P.degreeOf 0 := by
  by_cases hz : P = 0
  · simp [hz]
  have hv : finSuccEquiv F 4 P ≠ 0 := by
    intro h
    exact hz ((finSuccEquiv F 4).injective (h.trans (map_zero _).symm))
  rw [graph_eq_map, Polynomial.natDegree_map_of_leadingCoeff_ne_zero, natDegree_finSuccEquiv]
  exact coefficientGraph_coeff_ne_zero q hq P hP hS _
    (Polynomial.leadingCoeff_ne_zero.mpr hv)

theorem x_eval_zero_of_graph (q : ℕ) (hq : 0 < q) (P : MvPolynomial (Fin 5) F)
    (hP : OmitsMessages P) (hS : P.degreeOf 3 < q) (x : F)
    (h : (graph q P).eval (Polynomial.C x) = 0) :
    (finSuccEquiv F 4 P).eval (C x) = 0 := by
  let Q := (finSuccEquiv F 4 P).eval (C x)
  have hQ (j : Fin 4) : Q.degreeOf j ≤ P.degreeOf j.succ := by
    let V := finSuccEquiv F 4 P
    change (V.eval (C x)).degreeOf j ≤ _
    rw [Polynomial.eval_eq_sum_range]
    apply (degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro i _
    exact (degreeOf_mul_le j _ _).trans (by
      simpa only [← map_pow, degreeOf_C, add_zero] using degreeOf_coeff_finSuccEquiv P j i)
  have h0 : coefficientGraph q Q = 0 := by
    have hc : coefficientGraph q (C x : MvPolynomial (Fin 4) F) = Polynomial.C x := by
      simp [coefficientGraph]
    have he := Polynomial.eval_map_apply (coefficientGraph q).toRingHom (C x)
      (p := finSuccEquiv F 4 P)
    change ((finSuccEquiv F 4 P).map (coefficientGraph q).toRingHom).eval
      (coefficientGraph q (C x)) = coefficientGraph q Q at he
    rw [hc, ← graph_eq_map] at he
    exact he.symm.trans h
  by_contra hn
  exact coefficientGraph_ne_zero q hq Q hn
    (Nat.eq_zero_of_le_zero ((hQ 0).trans hP.1.le))
    (Nat.eq_zero_of_le_zero ((hQ 1).trans hP.2.le))
    ((hQ 2).trans_lt hS) h0

/-- Divisibility by the node locator descends from the coefficient fraction field
because the locator is monic. -/
private theorem locator_dvd (S : Finset I) (P : Polynomial (MvPolynomial (Fin 4) K))
    (h : ∀ i ∈ S, P.eval (C (node i)) = 0) :
    (locator node S).map C ∣ P := by
  classical
  let R := MvPolynomial (Fin 4) K
  let f : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R (FractionRing R)
  apply (Polynomial.map_dvd_map f hf ((locator_monic node S).map C)).mp
  rw [Polynomial.map_map, locator_map]
  apply Strata.locator_dvd_of_eval_zero _
    ((hf.comp (MvPolynomial.C_injective (Fin 4) K)).comp
      ProximityPrize.Benchmark.IRSProfile.domain.injective)
  intro i hi
  change (P.map f).eval (f (C (node i))) = 0
  rw [Polynomial.eval_map_apply, h i hi, map_zero]

private def planeLocator (S : Finset I) : MvPolynomial (Fin 5) K :=
  (finSuccEquiv K 4).symm ((locator node S).map C)

private theorem graph_planeLocator (S : Finset I) : graph p (planeLocator S) =
    liftX (locator node S) := by
  rw [graph_eq_map, planeLocator, AlgEquiv.apply_symm_apply, Polynomial.map_map]
  congr 1
  ext a
  simp [coefficientGraph]

private theorem degreeOf_le_of_dvd {Q P : MvPolynomial (Fin 5) F} (hP : P ≠ 0)
    (h : Q ∣ P) (j : Fin 5) : Q.degreeOf j ≤ P.degreeOf j := by
  obtain ⟨E, hE⟩ := h
  have hQ : Q ≠ 0 := fun hz => hP (by rw [hE, hz, zero_mul])
  have hEn : E ≠ 0 := fun hz => hP (by rw [hE, hz, mul_zero])
  rw [hE, degreeOf_mul_eq hQ hEn]
  exact Nat.le_add_right _ _

private theorem omits_of_dvd {Q P : MvPolynomial (Fin 5) F} (hP : P ≠ 0)
    (ho : OmitsMessages P) (h : Q ∣ P) : OmitsMessages Q :=
  ⟨Nat.eq_zero_of_le_zero ((degreeOf_le_of_dvd hP h 1).trans ho.1.le),
    Nat.eq_zero_of_le_zero ((degreeOf_le_of_dvd hP h 2).trans ho.2.le)⟩

private theorem native_p_pos : 0 < p := by decide

private theorem divide_plane (S : Finset I) (P : MvPolynomial (Fin 5) K)
    (Q : Bivar) (content : Polynomial K) (hQ : Q ≠ 0) (hc : content ≠ 0)
    (hP : OmitsMessages P) (hS : P.degreeOf 3 < p)
    (h : graph p P = Polynomial.C content * (liftX (locator node S) * Q)) :
    ∃ E : MvPolynomial (Fin 5) K, P = planeLocator S * E ∧ E ≠ 0 ∧
      graph p E = Polynomial.C content * Q := by
  have hd := locator_dvd S (finSuccEquiv K 4 P) (fun i hi => by
    apply x_eval_zero_of_graph p native_p_pos P hP hS
    rw [h, Polynomial.eval_mul, Polynomial.eval_mul, K21_8.eval_liftX,
      locator_eval_zero node S i hi, Polynomial.C_0, zero_mul, mul_zero])
  obtain ⟨E', hE'⟩ := hd
  let E := (finSuccEquiv K 4).symm E'
  have he : P = planeLocator S * E := by
    apply (finSuccEquiv K 4).injective
    simpa [planeLocator, E, map_mul] using hE'
  have hm : liftX (locator node S) ≠ 0 :=
    ((locator_monic node S).map (Polynomial.C : K →+* Polynomial K)).ne_zero
  have hgE : graph p E = Polynomial.C content * Q := by
    apply mul_left_cancel₀ hm
    calc
      liftX (locator node S) * graph p E = graph p P := by
        rw [he, map_mul, graph_planeLocator]
      _ = liftX (locator node S) * (Polynomial.C content * Q) := h.trans (mul_left_comm _ _ _)
  have hen : E ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hgE
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hQ) hgE.symm
  exact ⟨E, he, hen, hgE⟩

private theorem seedRelPrime {U V : Bivar} (hUV : IsCoprime (extendSeed U) (extendSeed V))
    {content : Polynomial K} (hc : content ≠ 0) :
    IsRelPrime (extendSeed (Polynomial.C content * U))
      (extendSeed (Polynomial.C content * V)) := by
  have hu : IsUnit (Polynomial.C (K21_8.seedInclusion content)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ K21_8.seedInclusion_injective).mpr hc))
  have hmap (Q : Bivar) : extendSeed (Polynomial.C content * Q) =
      Polynomial.C (K21_8.seedInclusion content) * extendSeed Q := by
    change (Polynomial.C content * Q).map K21_8.seedInclusion = _ * Q.map K21_8.seedInclusion
    rw [Polynomial.map_mul, Polynomial.map_C]
  intro d hdU hdV
  rw [hmap, hu.dvd_mul_left] at hdU hdV
  exact hUV.isRelPrime hdU hdV

private theorem parameter_only {d : MvPolynomial (Fin 5) K}
    (ho : OmitsMessages d) (hx : d.degreeOf 0 = 0) :
    ∃ q : MvPolynomial (Fin 2) K, rename (![3, 4] : Fin 2 → Fin 5) q = d := by
  classical
  apply exists_rename_eq_of_vars_subset_range
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction
  · intro i hi
    have hi' := mem_vars_iff_degreeOf_ne_zero.mp hi
    fin_cases i
    · exact (hi' hx).elim
    · exact (hi' ho.1).elim
    · exact (hi' ho.2).elim
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

private theorem reduced_relPrime {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : IndependentLift R)
    {U V : MvPolynomial (Fin 5) K} (hU : U ≠ 0) (hUo : OmitsMessages U)
    (hS : U.degreeOf 3 < p)
    (hfU : A.U = planeLocator (fixedNodes R) * U) (hfV : A.V = planeLocator (fixedNodes R) * V)
    (hgU : graph p U = Polynomial.C A.content * D.U)
    (hgV : graph p V = Polynomial.C A.content * D.V) :
    IsRelPrime U V := by
  intro d hdU hdV
  let f := (Polynomial.mapRingHom K21_8.seedInclusion).comp (graph (F := K) p).toRingHom
  have hfdU : f d ∣ extendSeed (Polynomial.C A.content * D.U) := by
    rw [← hgU]
    exact _root_.map_dvd f hdU
  have hfdV : f d ∣ extendSeed (Polynomial.C A.content * D.V) := by
    rw [← hgV]
    exact _root_.map_dvd f hdV
  have hu := seedRelPrime D.coprime A.content_ne hfdU hfdV
  have hx := Polynomial.natDegree_eq_zero_of_isUnit hu
  change ((graph p d).map K21_8.seedInclusion).natDegree = 0 at hx
  rw [Polynomial.natDegree_map_eq_of_injective K21_8.seedInclusion_injective,
    graph_natDegree p native_p_pos d (omits_of_dvd hU hUo hdU)
      ((degreeOf_le_of_dvd hU hdU 3).trans_lt hS)] at hx
  obtain ⟨q, rfl⟩ := parameter_only (omits_of_dvd hU hUo hdU) hx
  have hA : IsUnit q := A.primitive q
    (hdU.trans (hfU.symm ▸ dvd_mul_left U (planeLocator (fixedNodes R))))
    (hdV.trans (hfV.symm ▸ dvd_mul_left V (planeLocator (fixedNodes R))))
  exact hA.map (rename (![3, 4] : Fin 2 → Fin 5))

theorem proof : K21_11_2.c1 := by
  intro u T R D A
  have hp1 : 2 < p := by decide
  have hp2 : 3 < p := by decide
  have hUo : OmitsMessages A.U := ⟨A.omitted.1, A.omitted.2.1⟩
  have hVo : OmitsMessages A.V := A.omitted.2.2
  have hGU : graph p A.U = Polynomial.C A.content * leftU R := A.graphU
  have hGV : graph p A.V = Polynomial.C A.content * leftV R := A.graphV
  obtain ⟨U, hfU, hU, hgU⟩ := divide_plane (fixedNodes R) A.U D.U A.content D.U_ne
    A.content_ne hUo (A.boxes.1.trans_lt hp1) (hGU.trans (by rw [D.U_factor]))
  obtain ⟨V, hfV, hV, hgV⟩ := divide_plane (fixedNodes R) A.V D.V A.content D.V_ne
    A.content_ne hVo (A.boxes.2.2.1.trans_lt hp2) (hGV.trans (by rw [D.V_factor]))
  have hAdU : U ∣ A.U := hfU.symm ▸ dvd_mul_left U (planeLocator (fixedNodes R))
  have hAdV : V ∣ A.V := hfV.symm ▸ dvd_mul_left V (planeLocator (fixedNodes R))
  have hl : planeLocator (fixedNodes R) ≠ 0 := by
    simpa only [planeLocator, EmbeddingLike.map_ne_zero_iff] using
      ((locator_monic node (fixedNodes R)).map
        (MvPolynomial.C : K →+* MvPolynomial (Fin 4) K)).ne_zero
  have hAu : A.U ≠ 0 := hfU.symm ▸ mul_ne_zero hl hU
  have hAv : A.V ≠ 0 := hfV.symm ▸ mul_ne_zero hl hV
  have hUo' := omits_of_dvd hAu hUo hAdU
  have hVo' := omits_of_dvd hAv hVo hAdV
  have hUS := (degreeOf_le_of_dvd hAu hAdU 3).trans A.boxes.1
  have hUT := (degreeOf_le_of_dvd hAu hAdU 4).trans A.boxes.2.1
  have hVS := (degreeOf_le_of_dvd hAv hAdV 3).trans A.boxes.2.2.1
  have hVT := (degreeOf_le_of_dvd hAv hAdV 4).trans A.boxes.2.2.2
  refine ⟨⟨U, V, hUo', hVo', hU, hV, reduced_relPrime D A hU hUo' (hUS.trans_lt hp1)
    hfU hfV hgU hgV, ?_, ⟨hUS, hUT, hVS, hVT⟩, hgU, hgV⟩⟩
  rw [← graph_natDegree p native_p_pos U hUo' (hUS.trans_lt hp1),
    ← graph_natDegree p native_p_pos V hVo' (hVS.trans_lt hp2), hgU, hgV,
    Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr A.content_ne) D.U_ne,
    Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr A.content_ne) D.V_ne,
    Polynomial.natDegree_C, zero_add, zero_add, D.max_degree]

end
end K21_11_2_1
end Port_K1_11_2_1Proof

section Port_K1_11_3_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K21_11_3_2

open K21_11 K21_11_3 MvPolynomial

variable {F : Type} [Field F]

private theorem derivative_specialize (H : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) :
    Polynomial.derivative (aeval (scalarImages D s t) H) =
      aeval (scalarImages D s t) (pderiv 0 H) +
        aeval (scalarImages D s t) (pderiv 1 H) * Polynomial.derivative D := by
  induction H using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_eq]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ]
    ring
  | mul_X P i hP =>
    simp only [map_mul, aeval_X, Polynomial.derivative_mul, pderiv_mul, map_add, hP]
    fin_cases i <;> simp [scalarImages] <;> ring

private theorem first_derivative (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) (hroot : aeval (scalarImages D s t) G = 0) :
    -aeval (scalarImages D s t) (pderiv 0 G) =
      aeval (scalarImages D s t) (pderiv 1 G) * Polynomial.derivative D := by
  have h := derivative_specialize G D s t
  rw [hroot, Polynomial.derivative_zero] at h
  exact neg_eq_of_add_eq_zero_right h.symm

private theorem specialize_implicitDeriv (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) (hroot : aeval (scalarImages D s t) G = 0)
    (H : MvPolynomial (Fin 4) F) :
    aeval (scalarImages D s t) (implicitDeriv G H) =
      aeval (scalarImages D s t) (pderiv 1 G) *
        Polynomial.derivative (aeval (scalarImages D s t) H) := by
  simp only [implicitDeriv, map_sub, map_mul]
  rw [derivative_specialize, sub_eq_add_neg, ← neg_mul, first_derivative G D s t hroot]
  ring

/-- The two terms involving the derivative of the separant cancel in the product rule. -/
private theorem cleared_step (A V : Polynomial F) (m : ℕ) :
    A * (A * Polynomial.derivative (A ^ (m + 1) * V)) -
      Polynomial.C (↑(m + 1) : F) * (A ^ (m + 1) * V) *
        (A * Polynomial.derivative A) =
      A ^ (m + 1 + 2) * Polynomial.derivative V := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_pow_succ,
    pow_succ A (m + 1 + 1), pow_succ A (m + 1), pow_succ A m]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private theorem specialize_implicitNumerator (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) (hroot : aeval (scalarImages D s t) G = 0) (n : ℕ) :
    aeval (scalarImages D s t) (implicitNumerator G n) =
      aeval (scalarImages D s t) (pderiv 1 G) ^ (2 * n + 1) *
        (Polynomial.derivative^[n + 1]) D := by
  induction n with
  | zero => simpa [implicitNumerator] using first_derivative G D s t hroot
  | succ n ih =>
    have hm : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by omega
    simp only [implicitNumerator, map_sub, map_mul, aeval_C, Polynomial.algebraMap_eq,
      specialize_implicitDeriv G D s t hroot, ih]
    rw [hm, Function.iterate_succ_apply' Polynomial.derivative (n + 1) D]
    exact cleared_step _ _ (2 * n)

theorem proof : K21_11_3.c2 := by
  intro F _ G w D s t hroot n hn hfactor
  cases n with
  | zero =>
    simp [paddedTaylorCoeff, aeval_X, scalarImages, mul_comm]
  | succ n =>
    have hfactorial : (Polynomial.derivative^[n + 1]) D =
        Polynomial.C (↑(n + 1).factorial : F) * Polynomial.hasseDeriv (n + 1) D := by
      rw [← Polynomial.factorial_smul_hasseDeriv]
      rw [LinearMap.smul_apply, nsmul_eq_mul, Polynomial.C_eq_natCast]
    have hpad : (2 * n + 1) + (2 * w - 1 - (2 * n + 1)) = 2 * w - 1 := by omega
    simp only [paddedTaylorCoeff, map_mul, map_pow, aeval_C, Polynomial.algebraMap_eq,
      specialize_implicitNumerator G D s t hroot, hfactorial]
    set A := aeval (scalarImages D s t) (pderiv 1 G)
    set f : F := ↑(n + 1).factorial
    set H := Polynomial.hasseDeriv (n + 1) D
    have hcancel : Polynomial.C f⁻¹ * Polynomial.C f = 1 := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hfactor, Polynomial.C_1]
    calc
      _ = (Polynomial.C f⁻¹ * Polynomial.C f) *
          (A ^ (2 * n + 1) * A ^ (2 * w - 1 - (2 * n + 1))) * H := by ring
      _ = _ := by rw [hcancel, one_mul, ← pow_add, hpad]

end K21_11_3_2
end Port_K1_11_3_2Proof

section Port_K1_11_3_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K21_11_3_1

open K21_11 K21_11_3 MvPolynomial

local notation "deg" => weightedTotalDegree scalarWeightTotal

section DegreeBounds

variable {F : Type} [Field F]
variable {P Q : MvPolynomial (Fin 4) F} {a b : ℕ}

private theorem degree_mul_le (hP : deg P ≤ a) (hQ : deg Q ≤ b) :
    deg (P * Q) ≤ a + b :=
  (weightedTotalDegree_mul_le scalarWeightTotal P Q).trans (Nat.add_le_add hP hQ)

private theorem degree_sub_le (hP : deg P ≤ a) (hQ : deg Q ≤ a) :
    deg (P - Q) ≤ a := by
  rw [← mem_restrictWeightedDegree_iff_weightedTotalDegree_le] at hP hQ ⊢
  exact (restrictWeightedDegree (R := F) scalarWeightTotal a).sub_mem hP hQ

private theorem degree_const_mul_le (c : F) (P : MvPolynomial (Fin 4) F) :
    deg (C c * P) ≤ deg P := by
  simpa only [weightedTotalDegree_C, zero_add] using
    weightedTotalDegree_mul_le scalarWeightTotal (C c) P

private theorem degree_pderiv_y_le (hP : deg P ≤ a) :
    deg (pderiv 1 P) ≤ a - 1 :=
  (weightedTotalDegree_pderiv_le_sub scalarWeightTotal 1 P).trans
    (Nat.sub_le_sub_right hP 1)

/-- The implicit derivation adds at most the separant's degree cap. -/
private theorem implicitDeriv_degree {G H : MvPolynomial (Fin 4) F} {d m : ℕ}
    (hY : deg (pderiv 1 G) ≤ d) (hX : deg (pderiv 0 G) ≤ d + 1)
    (hH : deg H ≤ m) (hm : 1 ≤ m) :
    deg (implicitDeriv G H) ≤ m + d := by
  unfold implicitDeriv
  apply degree_sub_le
  · have hx := (weightedTotalDegree_pderiv_le scalarWeightTotal 0 H).trans hH
    exact (degree_mul_le hY hx).trans_eq (Nat.add_comm d m)
  · exact (degree_mul_le hX (degree_pderiv_y_le hH)).trans (by omega)

/-- The numerator of derivative order `n + 1` has cap `(2n + 1)d + 1`. -/
private theorem implicitNumerator_degree {G : MvPolynomial (Fin 4) F} {d : ℕ}
    (hd : 1 ≤ d) (hY : deg (pderiv 1 G) ≤ d) (hX : deg (pderiv 0 G) ≤ d + 1)
    (n : ℕ) : deg (implicitNumerator G n) ≤ (2 * n + 1) * d + 1 := by
  have hFlow := implicitDeriv_degree hY hX hY hd
  induction n with
  | zero =>
    simpa only [implicitNumerator, weightedTotalDegree, support_neg, mul_zero, zero_add, one_mul]
      using hX
  | succ n ih =>
    rw [implicitNumerator]
    apply degree_sub_le
    · have hN := implicitDeriv_degree hY hX ih (by omega)
      exact (degree_mul_le hY hN).trans_eq (by ring)
    · have hN := (degree_const_mul_le (↑(2 * n + 1) : F) _).trans ih
      exact (degree_mul_le hN hFlow).trans_eq (by ring)

end DegreeBounds

theorem proof : K21_11_3.c1 := by
  intro F _ G w E hE hG n hn
  let d := E - 1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hY : deg (pderiv 1 G) ≤ d := degree_pderiv_y_le hG
  have hX : deg (pderiv 0 G) ≤ d + 1 :=
    (weightedTotalDegree_pderiv_le scalarWeightTotal 0 G).trans (by dsimp [d]; omega)
  have hPow (k : ℕ) : deg (pderiv 1 G ^ k) ≤ k * d :=
    (weightedTotalDegree_pow_le scalarWeightTotal _ k).trans (Nat.mul_le_mul_left k hY)
  change deg (paddedTaylorCoeff G w n) ≤ (2 * w - 1) * d + 1
  cases n with
  | zero =>
    rw [paddedTaylorCoeff]
    have h₀ : deg (MvPolynomial.X 1 : MvPolynomial (Fin 4) F) ≤ 1 :=
      mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
        (X_mem_restrictWeightedDegree scalarWeightTotal 1 1 (by rfl))
    exact (degree_mul_le h₀ (hPow _)).trans_eq (Nat.add_comm _ _)
  | succ n =>
    rw [paddedTaylorCoeff]
    have hN := (degree_const_mul_le ((↑(Nat.factorial (n + 1)) : F)⁻¹) _).trans
      (implicitNumerator_degree hd hY hX n)
    apply (degree_mul_le hN (hPow _)).trans_eq
    have hpad : 2 * n + 1 ≤ 2 * w - 1 := by omega
    calc
      _ = ((2 * n + 1) + (2 * w - 1 - (2 * n + 1))) * d + 1 := by ring
      _ = _ := by rw [Nat.add_comm (2 * n + 1), Nat.sub_add_cancel hpad]

end K21_11_3_1
end Port_K1_11_3_1Proof

section Port_K1_11_1_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K21_11_1_2

open Matrix MvPolynomial FrobeniusLocator K21_11_1
open scoped BigOperators

private theorem exists_pivot {E row col : Type} [Field E] [Fintype row] [Fintype col]
    (N : Matrix row col E) :
    ∃ (rows : Fin N.rank → row) (cols : Fin N.rank → col),
      (N.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' E N.col
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = N.rank := by
    rw [← finrank_span_eq_card hli, hspan, Matrix.rank_eq_finrank_span_cols]
  let e := (Fintype.equivFinOfCardEq hc).symm
  let cols : Fin N.rank → col := a ∘ e
  have hcols : LinearIndependent E (fun j : Fin N.rank => N.col (cols j)) :=
    hli.comp e e.injective
  obtain ⟨rows, hpivot⟩ := GenericRank.exists_rows_det_ne_zero (N.submatrix id cols) (by
    intro v hv
    have hsum : (∑ j, v j • N.col (cols j)) = 0 := by
      funext i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
        Matrix.col, Matrix.transpose_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
        id_eq] using congrFun hv i
    funext j
    exact Fintype.linearIndependent_iff.mp hcols v hsum j)
  exact ⟨rows, cols, hpivot⟩

private def unitColumns {R row col : Type} [Zero R] [One R] [DecidableEq row]
    (I : col → row) : Matrix row col R :=
  fun i j => (Pi.single (I j) 1 : row → R) i

private theorem transpose_mul_unitColumns {R row col pick : Type}
    [CommRing R] [Fintype row] [DecidableEq row]
    (W : Matrix row col R) (I : pick → row) :
    W.transpose * unitColumns I = (W.submatrix I id).transpose := by
  ext i j
  change W.transpose.mulVec (Pi.single (I j) 1) i = _
  rw [Matrix.mulVec_single_one]
  rfl

/-- The pivot rows and the annihilator turn every augmentation into a block
triangular matrix with the same pivot block. -/
private theorem augmentation_identity {R : Type} [CommRing R] {r s : ℕ}
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) R)
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) R)
    (hWC : W.transpose * C = 0)
    (pivot : Fin r → Fin r ⊕ Fin s) (I : Fin s → Fin r ⊕ Fin s) :
    (Matrix.fromRows (unitColumns pivot : Matrix _ _ R).transpose W.transpose).det *
        (Matrix.fromCols C (unitColumns I)).det =
      (C.submatrix pivot id).det * (W.submatrix I id).det := by
  have htop : (unitColumns pivot : Matrix _ _ R).transpose * C =
      C.submatrix pivot id := by
    have h := congrArg Matrix.transpose (transpose_mul_unitColumns C pivot)
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h
  rw [← Matrix.det_mul, Matrix.fromRows_mul_fromCols, htop, hWC,
    transpose_mul_unitColumns W I, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose]

/-- A primitive family of minors removes the common denominator in the
determinant identity by taking a finite gcd. -/
private theorem factor_of_primitive {R ι : Type} [CommRing R] [IsDomain R]
    [NormalizedGCDMonoid R] [Fintype ι] (P A : ι → R) (t d : R)
    (ht : t ≠ 0) (hprim : coefficientPrimitive P)
    (hdet : ∀ I, t * A I = d * P I) :
    ∃ q : R, ∀ I, A I = q * P I := by
  let g := Finset.univ.gcd P
  have hg : IsUnit g := hprim g (fun I => Finset.gcd_dvd (Finset.mem_univ I))
  have hd : t ∣ Finset.univ.gcd (fun I => d * P I) :=
    Finset.dvd_gcd (fun I _ => ⟨A I, (hdet I).symm⟩)
  have hgd : t ∣ d * g := hd.trans (Finset.gcd_mul_left' Finset.univ P d).dvd
  obtain ⟨q, hq⟩ : t ∣ d := hgd.trans (by
    simpa only [mul_one] using mul_dvd_mul (dvd_refl d) (isUnit_iff_dvd_one.mp hg))
  refine ⟨q, fun I => mul_left_cancel₀ ht ?_⟩
  rw [hdet I, hq, mul_assoc]

/-- In each nonzero determinant summand the unit columns reserve their rows.
They consume one unit of the degree budget exactly when their rows lie in
the block for the chosen seed. -/
private theorem augmented_degree {F : Type} [Field F] {r s : ℕ}
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) (Seeds F))
    (block : Fin r ⊕ Fin s → Fin 2) (b i : Fin 2)
    (I : Fin s → Fin r ⊕ Fin s) (hI : ∀ j, block (I j) = b)
    (hC : ∀ u j, (C u j).degreeOf i ≤ if block u = i then 1 else 0)
    (L : ℕ) (htotal : (∑ u, if block u = i then 1 else 0) = L) :
    (Matrix.fromCols C (unitColumns I)).det.degreeOf i ≤ if b = i then L - s else L := by
  classical
  let A := Matrix.fromCols C (unitColumns I)
  let weight (u : Fin r ⊕ Fin s) : ℕ := if block u = i then 1 else 0
  let saving : Fin r ⊕ Fin s → ℕ := Sum.elim (fun _ => 0) (fun _ => if b = i then 1 else 0)
  change A.det.degreeOf i ≤ _
  rw [Matrix.det_apply']
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  by_cases hz : (∏ j, A (σ j) j) = 0
  · simp [hz]
  have hsign : ((↑↑(Equiv.Perm.sign σ) : Seeds F)).degreeOf i = 0 := by
    rw [← map_intCast (MvPolynomial.C : F →+* Seeds F), degreeOf_C]
  have hpoint (j : Fin r ⊕ Fin s) :
      (A (σ j) j).degreeOf i + saving j ≤ weight (σ j) := by
    cases j with
    | inl j => simpa only [A, Matrix.fromCols_apply_inl, saving, Sum.elim_inl, add_zero]
        using hC (σ (Sum.inl j)) j
    | inr j =>
      have he : I j = σ (Sum.inr j) := by
        by_contra h
        apply hz
        apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inr j))
        simp [A, unitColumns, h]
      simp [A, unitColumns, ← he, weight, hI, saving]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
  have hsave : (∑ j, saving j) = if b = i then s else 0 := by
    by_cases h : b = i <;> simp [saving, Fintype.sum_sum_type, h]
  rw [Finset.sum_add_distrib, hsave, Equiv.sum_comp σ weight, htotal] at hsum
  apply (degreeOf_mul_le _ _ _).trans
  rw [hsign, zero_add]
  apply (degreeOf_prod_le _ _ _).trans
  by_cases h : b = i
  · simp only [ite_eq_left h] at hsum ⊢
    omega
  · simpa only [ite_eq_right h, Nat.add_zero] using hsum

theorem proof : K21_11_1.c2 := by
  intro F _ L w s M W _ _ hrank hWM hdegree hprim b i rows
  classical
  by_cases hzero : K1_6.maximalMinors W (fun j => (b, rows j)) = 0
  · simp [hzero]
  let φ := algebraMap (Seeds F) (PlaneField F)
  let r := (M.map φ).rank
  obtain ⟨pivot, cols, hpivot⟩ := exists_pivot (M.map φ)
  let e : (Fin r ⊕ Fin s) ≃ Fin 2 × Fin L :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      using hrank)
  let C := M.submatrix e cols
  let V := W.submatrix e id
  let p : Fin r → Fin r ⊕ Fin s := e.symm ∘ pivot
  let I : Fin s → Fin r ⊕ Fin s := fun j => e.symm (b, rows j)
  have hpmap : (C.submatrix p id).map φ = (M.map φ).submatrix pivot cols := by
    ext u j
    simp only [C, p, Matrix.map_apply, Matrix.submatrix_apply, Function.comp_apply,
      Equiv.apply_symm_apply, id_eq]
  have hp : (C.submatrix p id).det ≠ 0 := by
    intro h
    apply hpivot
    rw [← hpmap, ← RingHom.mapMatrix_apply, ← φ.map_det, h, map_zero]
  have hVC : V.transpose * C = 0 := by
    apply Matrix.ext
    intro u j
    change (∑ t : Fin r ⊕ Fin s, W (e t) u * M (e t) (cols j)) = 0
    rw [Equiv.sum_comp e (fun t => W t u * M t (cols j))]
    exact congrFun (congrFun hWM u) (cols j)
  let P (J : Fin s → Fin r ⊕ Fin s) := (V.submatrix J id).det
  let A (J : Fin s → Fin r ⊕ Fin s) := (Matrix.fromCols C (unitColumns J)).det
  let t := (Matrix.fromRows (unitColumns p : Matrix _ _ (Seeds F)).transpose V.transpose).det
  have hminor (J : Fin s → Fin 2 × Fin L) :
      P (e.symm ∘ J) = K1_6.maximalMinors W J := by
    change K1_6.maximalMinors W (e ∘ (e.symm ∘ J)) = _
    congr 1
    funext j
    exact e.apply_symm_apply (J j)
  have hP : P I ≠ 0 := by
    change P (e.symm ∘ (fun j => (b, rows j))) ≠ 0
    rwa [hminor]
  have hdet (J : Fin s → Fin r ⊕ Fin s) : t * A J = (C.submatrix p id).det * P J :=
    augmentation_identity C V hVC p J
  have ht : t ≠ 0 := by
    intro hz
    have he := hdet I
    rw [hz, zero_mul] at he
    exact mul_ne_zero hp hP he.symm
  have hprimP : coefficientPrimitive P := by
    intro q hq
    apply hprim q
    intro J
    rw [← hminor J]
    exact hq _
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := Seeds F)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Seeds F)
  obtain ⟨q, hq⟩ := factor_of_primitive P A t _ ht hprimP hdet
  have hq0 : q ≠ 0 := by
    intro hz
    have he := hdet I
    rw [hq I, hz, zero_mul, mul_zero] at he
    exact mul_ne_zero hp hP he.symm
  let block (u : Fin r ⊕ Fin s) := (e u).1
  have hblock (j : Fin s) : block (I j) = b := by
    simp only [block, I, Equiv.apply_symm_apply]
  have htotal : (∑ u, if block u = i then 1 else 0) = L := by
    dsimp only [block]
    rw [Equiv.sum_comp e (fun u : Fin 2 × Fin L => if u.1 = i then (1 : ℕ) else 0)]
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    fin_cases i <;> simp
  have hbound := augmented_degree C block b i I hblock (fun u j => hdegree (e u) (cols j) i)
    L htotal
  change (A I).degreeOf i ≤ _ at hbound
  rw [hq I, degreeOf_mul_eq hq0 hP] at hbound
  rw [← hminor (fun j => (b, rows j))]
  exact (Nat.le_add_left (degreeOf i (P I)) (degreeOf i q)).trans hbound

end K21_11_1_2
end Port_K1_11_1_2Proof

section Port_K1_11_1_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K21_11_1_1

noncomputable section

open Polynomial Matrix FrobeniusLocator K1_6 K21_11_1

/-- After applying a zero-preserving function to the entries, select consecutive rows
starting at the last surviving coefficient. The resulting minor is triangular. -/
private theorem exists_shift_minor {A R : Type} [CommRing A] [CommRing R] [IsDomain R]
    (P : Fin 2 → A[X]) (h s : ℕ) (hdegree : ∀ b, (P b).natDegree ≤ h)
    (f : A → R) (hf : f 0 = 0) (b : Fin 2) (j : Fin (h + 1))
    (hj : f ((P b).coeff j.val) ≠ 0) :
    ∃ rows : Fin s → Fin (h + s),
      (((shifts P (h + s) s).submatrix (fun k => (b, rows k)) id).map f).det ≠ 0 := by
  classical
  let S := (Finset.range (h + 1)).filter (fun d => f ((P b).coeff d) ≠ 0)
  have hS : S.Nonempty := ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, hj⟩⟩
  let d := S.max' hS
  have hd : d ∈ S := S.max'_mem hS
  have hdle : d ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hd).1)
  have hdne : f ((P b).coeff d) ≠ 0 := (Finset.mem_filter.mp hd).2
  have hlarge (k : ℕ) (hk : d < k) : f ((P b).coeff k) = 0 := by
    by_cases hkh : k < h + 1
    · by_contra hne
      exact (not_le_of_gt hk) (S.le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkh, hne⟩))
    · have hk' : (P b).natDegree < k := (hdegree b).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk', hf]
  let rows (k : Fin s) : Fin (h + s) := ⟨d + k.val, by omega⟩
  let M := ((shifts P (h + s) s).submatrix (fun k => (b, rows k)) id).map f
  have htri : M.IsUpperTriangular := by
    intro k l hkl
    change l.val < k.val at hkl
    change f ((P b * Polynomial.X ^ l.val).coeff (d + k.val)) = 0
    rw [Polynomial.coeff_mul_X_pow', ite_eq_left (by omega)]
    exact hlarge _ (by omega)
  have hdiag (k : Fin s) : M k k = f ((P b).coeff d) := by
    change f ((P b * Polynomial.X ^ k.val).coeff (d + k.val)) = _
    rw [Polynomial.coeff_mul_X_pow]
  refine ⟨rows, ?_⟩
  change M.det ≠ 0
  rw [Matrix.det_of_isUpperTriangular htri]
  simp only [hdiag, Fin.prod_const]
  exact pow_ne_zero _ hdne

private theorem planePair_degree {F : Type} [Field F] {h : ℕ}
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2) : (planePair Q b).natDegree ≤ h :=
  Principal.assemble_natDegree_le _

private theorem planePair_coeff {F : Type} [Field F] {h : ℕ}
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2) (j : Fin (h + 1)) :
    (planePair Q b).coeff j.val = Q (b, j) :=
  Principal.assemble_coeff _ _

/-- A nonzero common nonunit divisor would supply an irreducible modulo which
all maximal minors vanish, although at least one coefficient of the pair survives. -/
private theorem primitive_shift_minors {F : Type} [Field F] (h s : ℕ)
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (hQ : Q ≠ 0) (hprim : coefficientPrimitive Q) :
    coefficientPrimitive (maximalMinors (shifts (planePair Q) (h + s) s)) := by
  classical
  intro q hq
  have hqne : q ≠ 0 := by
    intro hz
    obtain ⟨⟨b, j⟩, hj⟩ := Function.ne_iff.mp hQ
    have hj' : id ((planePair Q b).coeff j.val) ≠ 0 := by
      simpa only [id_eq, planePair_coeff, Pi.zero_apply] using hj
    obtain ⟨rows, hr⟩ := exists_shift_minor (planePair Q) h s (planePair_degree Q)
      id rfl b j hj'
    have he := hq (fun k => (b, rows k))
    rw [hz, zero_dvd_iff] at he
    apply hr
    change (((shifts (planePair Q) (h + s) s).submatrix (fun k => (b, rows k)) id).map id).det = 0
    rw [Matrix.map_id]
    exact he
  by_contra hqnu
  obtain ⟨p, hp, hpq⟩ := WfDvdMonoid.exists_irreducible_factor hqnu hqne
  let I : Ideal (Seeds F) := Ideal.span {p}
  let : I.IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp)
  let φ := Ideal.Quotient.mk I
  have hsurvives : ∃ k, φ (Q k) ≠ 0 := by
    by_contra! hall
    exact hp.not_isUnit (hprim p (fun k =>
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hall k))))
  obtain ⟨⟨b, j⟩, hj⟩ := hsurvives
  obtain ⟨rows, hr⟩ := exists_shift_minor (planePair Q) h s (planePair_degree Q)
    φ (map_zero φ) b j (by rwa [planePair_coeff])
  let M := (shifts (planePair Q) (h + s) s).submatrix (fun k => (b, rows k)) id
  have hz : φ M.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (hpq.trans (hq (fun k => (b, rows k)))))
  rw [φ.map_det, RingHom.mapMatrix_apply] at hz
  exact hr hz

/-- At the uniform entry-degree bound, the coefficient of the determinant
is the determinant of the entry coefficients at that bound. -/
private theorem coeff_det_uniform {R : Type} [CommRing R] {s : ℕ}
    (M : Matrix (Fin s) (Fin s) R[X]) (H : ℕ) (hdegree : ∀ k l, (M k l).natDegree ≤ H) :
    M.det.coeff (s * H) = (M.map (fun q => q.coeff H)).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Polynomial.coeff_smul]
  congr 1
  simpa only [Finset.card_univ, Fintype.card_fin, Matrix.map_apply] using
    Polynomial.coeff_prod_of_natDegree_le (Finset.univ : Finset (Fin s))
      (fun k => M (σ k) k) H (fun k _ => hdegree (σ k) k)

private theorem natDegree_det_uniform {R : Type} [CommRing R] {s : ℕ}
    (M : Matrix (Fin s) (Fin s) R[X]) (H : ℕ) (hdegree : ∀ k l, (M k l).natDegree ≤ H) :
    M.det.natDegree ≤ s * H := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hprod : (∏ k, M (σ k) k).natDegree ≤ s * H := by
    calc
      _ ≤ ∑ k, (M (σ k) k).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _ : Fin s, H := Finset.sum_le_sum (fun k _ => hdegree (σ k) k)
      _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · simpa only [hsign, one_smul] using hprod
  · simpa only [hsign, Units.neg_smul, one_smul, Polynomial.natDegree_neg] using hprod

set_option maxHeartbeats 600000 in
/-- Regard the chosen seed as the polynomial variable. Its leading coefficients
have a nonzero shift minor in the chosen block. -/
private theorem shift_minor_degree {F : Type} [Field F] (h s : ℕ)
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b i : Fin 2) (hpos : 0 < blockDegree Q b i) :
    ∃ rows : Fin s → Fin (h + s),
      (maximalMinors (shifts (planePair Q) (h + s) s) (fun k => (b, rows k))).degreeOf i =
        s * blockDegree Q b i := by
  classical
  let R := MvPolynomial {j : Fin 2 // j ≠ i} F
  let φ : Seeds F →+* R[X] :=
    ((MvPolynomial.renameEquiv F (Equiv.optionSubtypeNe i).symm).trans
      (MvPolynomial.optionEquivLeft F {j : Fin 2 // j ≠ i})).toRingHom
  have hφ (q : Seeds F) : (φ q).natDegree = q.degreeOf i :=
    (MvPolynomial.degreeOf_eq_natDegree i q).symm
  let H := blockDegree Q b i
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (h + 1)))
    Finset.univ_nonempty (fun k => (Q (b, k)).degreeOf i)
  have hj' : (φ (Q (b, j))).natDegree = H := (hφ _).trans hj.symm
  have htop : (φ ((planePair Q b).coeff j.val)).coeff H ≠ 0 := by
    rw [planePair_coeff, ← hj', Polynomial.coeff_natDegree]
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hj'
    exact (Nat.ne_of_gt hpos) hj'.symm
  obtain ⟨rows, hr⟩ := exists_shift_minor (planePair Q) h s (planePair_degree Q)
    (fun q => (φ q).coeff H) (by rw [map_zero, Polynomial.coeff_zero]) b j htop
  let A := (shifts (planePair Q) (h + s) s).submatrix (fun k => (b, rows k)) id
  let M := A.map φ
  have hcoeff (k : ℕ) : (φ ((planePair Q b).coeff k)).natDegree ≤ H := by
    by_cases hk : k < h + 1
    · let j' : Fin (h + 1) := ⟨k, hk⟩
      change (φ ((planePair Q b).coeff j'.val)).natDegree ≤ H
      rw [planePair_coeff, hφ]
      exact degreeOf_coordinate Q b i j'
    · have hk' : (planePair Q b).natDegree < k := (planePair_degree Q b).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk', map_zero, Polynomial.natDegree_zero]
      exact Nat.zero_le H
  have hM (k l : Fin s) : (M k l).natDegree ≤ H := by
    simp only [M, A, Matrix.map_apply, Matrix.submatrix_apply, K1_6.shifts, id_eq]
    rw [Polynomial.coeff_mul_X_pow']
    split_ifs
    · exact hcoeff _
    · rw [map_zero, Polynomial.natDegree_zero]
      exact Nat.zero_le H
  have htopDet : M.det.coeff (s * H) ≠ 0 := by
    rw [coeff_det_uniform M H hM]
    exact hr
  refine ⟨rows, ?_⟩
  change A.det.degreeOf i = s * H
  have hdet : φ A.det = M.det := φ.map_det A
  rw [← hφ, hdet]
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (natDegree_det_uniform M H hM) htopDet

theorem proof : K21_11_1.c1 := by
  intro F inst h L s Q hL _ hQ hprim
  subst L
  exact ⟨primitive_shift_minors h s Q hQ hprim, shift_minor_degree h s Q⟩

end

end K21_11_1_1
end Port_K1_11_1_1Proof

section Port_K1_11_2_2AuxInterp
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace K21_11_2_2
noncomputable section

open MvPolynomial K21_11_2

variable {F : Type*} [Field F]

private def pencil (j : Fin 5) (a b : F) : MvPolynomial (Fin 5) F := C a + MvPolynomial.X j * C b

/-- The formal received combination at one physical node. -/
def nodeValue (x a b c d : F) (U V : MvPolynomial (Fin 5) F) : MvPolynomial (Fin 5) F :=
  parameterNode x U * pencil 3 a b + parameterNode x V * pencil 4 c d

theorem nodeWord_combination (x a b c d : F) (U V : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) :
    nodeWordMap x a b c d (U * MvPolynomial.X 1 + V * MvPolynomial.X 2) = nodeValue x a b c d U V := by
  simp only [map_add, map_mul, nodeWord_omits x a b c d U hU, nodeWord_omits x a b c d V hV]
  simp [nodeWordMap, nodeWordImages, nodeValue, pencil]

theorem seedEval_nodeValue (q : ℕ) (x a b c d : F) (U V : MvPolynomial (Fin 5) F) :
    seedEval q (nodeValue x a b c d U V) =
      (graph q U).eval (Polynomial.C x) * (Polynomial.C a + Polynomial.X * Polynomial.C b) +
      (graph q V).eval (Polynomial.C x) *
        (Polynomial.C c + Polynomial.X ^ q * Polynomial.C d) := by
  simp only [nodeValue, map_add, map_mul, ← eval_graph]
  simp [pencil, seedEval]

theorem parameterNode_nodeValue (x y a b c d : F) (U V : MvPolynomial (Fin 5) F) :
    parameterNode y (nodeValue x a b c d U V) = nodeValue x a b c d U V := by
  have h : (parameterNode y).comp (parameterNode x) = parameterNode x := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [parameterNode]
  simp only [nodeValue, map_add, map_mul, ← AlgHom.comp_apply (parameterNode y) (parameterNode x), h]
  simp [pencil, parameterNode]

private theorem degreeOf_parameterNode_le (j : Fin 5) (x : F) (Q : MvPolynomial (Fin 5) F) :
    (parameterNode x Q).degreeOf j ≤ Q.degreeOf j := by
  rw [← weightedTotalDegree_piSingle j (parameterNode x Q), ← weightedTotalDegree_piSingle j Q]
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  rw [weightedTotalDegree_piSingle]
  fin_cases i <;> simp [Pi.single_apply, degreeOf_X, eq_comm]

private theorem degreeOf_parameterNode_eq_zero (j : Fin 5) (x : F) (Q : MvPolynomial (Fin 5) F)
    (h3 : j ≠ 3) (h4 : j ≠ 4) : (parameterNode x Q).degreeOf j = 0 := by
  have h := weightedTotalDegree_aeval_le_of_le (fun _ : Fin 5 => 0) (Pi.single j 1)
    (![C x, 0, 0, MvPolynomial.X 3, MvPolynomial.X 4] : Fin 5 → MvPolynomial (Fin 5) F) Q (by
      intro i
      rw [weightedTotalDegree_piSingle]
      fin_cases i <;> simp [degreeOf_X, h3, h4])
  have hz : Q.weightedTotalDegree (fun _ => (0 : ℕ)) = 0 := by
    simp [weightedTotalDegree, Finsupp.weight_apply]
  rw [weightedTotalDegree_piSingle, hz] at h
  exact Nat.eq_zero_of_le_zero h

private theorem degreeOf_pencil_le (i j : Fin 5) (a b : F) :
    (pencil j a b).degreeOf i ≤ if i = j then 1 else 0 := by
  refine (degreeOf_add_le i _ _).trans (max_le ?_ ?_)
  · simp
  · exact (degreeOf_mul_C_le (MvPolynomial.X j) i b).trans_eq (degreeOf_X i j)

theorem degreeOf_nodeValue_le (j : Fin 5) (x a b c d : F) (U V : MvPolynomial (Fin 5) F) :
    (nodeValue x a b c d U V).degreeOf j ≤
      if j = 3 then sWeight U V else if j = 4 then tWeight U V else 0 := by
  refine (degreeOf_add_le j _ _).trans (max_le ?_ ?_)
  · refine (degreeOf_mul_le j _ _).trans ?_
    have hp := degreeOf_pencil_le j 3 a b
    have hu := degreeOf_parameterNode_le j x U
    by_cases h3 : j = 3
    · subst j
      simp [sWeight] at hp hu ⊢
      omega
    by_cases h4 : j = 4
    · subst j
      simp [tWeight, h3] at hp hu ⊢
      omega
    rw [degreeOf_parameterNode_eq_zero j x U h3 h4]
    simpa [h3, h4] using hp
  · refine (degreeOf_mul_le j _ _).trans ?_
    have hp := degreeOf_pencil_le j 4 c d
    have hv := degreeOf_parameterNode_le j x V
    by_cases h3 : j = 3
    · subst j
      simp [sWeight] at hp hv ⊢
      omega
    by_cases h4 : j = 4
    · subst j
      simp [tWeight, h3] at hp hv ⊢
      omega
    rw [degreeOf_parameterNode_eq_zero j x V h3 h4]
    simpa [h3, h4] using hp

private def liftCoordinate (f : Polynomial F) : MvPolynomial (Fin 5) F :=
  Polynomial.aeval (MvPolynomial.X 0) f

private theorem parameterNode_liftCoordinate (x : F) (f : Polynomial F) :
    parameterNode x (liftCoordinate f) = C (f.eval x) := by
  rw [liftCoordinate, ← Polynomial.aeval_algHom_apply (parameterNode x)]
  simp only [parameterNode, aeval_X, Matrix.cons_val_zero, Polynomial.aeval_def, algebraMap_eq]
  exact Polynomial.eval₂_at_apply _ _

private theorem degreeOf_liftCoordinate (j : Fin 5) (f : Polynomial F) :
    (liftCoordinate f).degreeOf j ≤ f.natDegree * (MvPolynomial.X 0 : MvPolynomial (Fin 5) F).degreeOf j := by
  rw [liftCoordinate, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun n hn => ?_)
  rw [algebraMap_eq]
  exact (degreeOf_C_mul_le _ j _).trans ((degreeOf_pow_le j _ n).trans
    (Nat.mul_le_mul_right _ (Polynomial.le_natDegree_of_mem_supp n hn)))

/-- Lagrange interpolation with coefficient values in the parameter ring. -/
def interpolant {N : ℕ} (x : Fin N → F) (v : Fin N → MvPolynomial (Fin 5) F) :
    MvPolynomial (Fin 5) F :=
  ∑ i, liftCoordinate (Lagrange.basis Finset.univ x i) * v i

theorem parameterNode_interpolant {N : ℕ} (x : Fin N → F) (hx : Function.Injective x)
    (v : Fin N → MvPolynomial (Fin 5) F) (hv : ∀ i, parameterNode (x i) (v i) = v i)
    (j : Fin N) : parameterNode (x j) (interpolant x v) = v j := by
  rw [interpolant, map_sum]
  simp only [map_mul, parameterNode_liftCoordinate]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · rw [Lagrange.eval_basis_self hx.injOn (Finset.mem_univ j), map_one, one_mul, hv]
  · intro i _ hij
    rw [Lagrange.eval_basis_of_ne hij (Finset.mem_univ j), map_zero, zero_mul]

theorem degreeOf_interpolant_le {N : ℕ} (x : Fin N → F) (hx : Function.Injective x)
    (v : Fin N → MvPolynomial (Fin 5) F) (j : Fin 5) (b : ℕ)
    (hv : ∀ i, (v i).degreeOf j ≤ b) :
    (interpolant x v).degreeOf j ≤ (N - 1) * (MvPolynomial.X 0 : MvPolynomial (Fin 5) F).degreeOf j + b := by
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun i hi => ?_)
  have h := degreeOf_liftCoordinate j (Lagrange.basis Finset.univ x i)
  rw [Lagrange.natDegree_basis hx.injOn hi, Finset.card_univ, Fintype.card_fin] at h
  exact (degreeOf_mul_le j _ _).trans (Nat.add_le_add h (hv i))

end
end K21_11_2_2
end Port_K1_11_2_2AuxInterp

section Port_K1_11_2_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace K21_11_2_2
noncomputable section

open K21 K21_11 K21_11_2 MvPolynomial

-- Keep the power exponent abstract when transporting the node equation.
private theorem relationOn_eq : relationOn = K21_8.relationOnAt p := rfl

private theorem nodeValue_of_relation (q : ℕ) {u : Words} {deleted : Finset I}
    {P : Puncture deleted} {U V : MvPolynomial (Fin 5) K} {G : Bivar}
    (hrel : K21_8.relationOnAt q u deleted (graph q U) (graph q V) G) (i : Fin P.N) :
    seedEval q (nodeValue (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
      (u 0 (P.index i) ^ q) (u 1 (P.index i) ^ q) U V) = G.eval (Polynomial.C (P.nodes i)) := by
  have hkeep : P.index i ∉ deleted := (P.retained _).mp ⟨i, rfl⟩
  rw [seedEval_nodeValue]
  exact hrel (P.index i) hkeep

theorem proof : K21_11_2.c2 := by
  intro u T R D hH A B P
  let x : Fin P.N → K := P.nodes
  let a (i : Fin P.N) : K := u 0 (P.index i)
  let b (i : Fin P.N) : K := u 1 (P.index i)
  let v (i : Fin P.N) := nodeValue (x i) (a i) (b i) (a i ^ p) (b i ^ p) B.U B.V
  let W := interpolant x v
  have hx : Function.Injective x :=
    ProximityPrize.Benchmark.IRSProfile.domain.injective.comp P.index.injective
  have hnodes (i : Fin P.N) : parameterNode (x i) W = v i :=
    parameterNode_interpolant x hx v (fun _ => parameterNode_nodeValue ..) i
  have hdeg (j : Fin 5) : W.degreeOf j ≤
      (P.N - 1) * (MvPolynomial.X 0 : MvPolynomial (Fin 5) K).degreeOf j +
      (if j = 3 then sWeight B.U B.V else if j = 4 then tWeight B.U B.V else 0) :=
    degreeOf_interpolant_le x hx v j _ (fun i => degreeOf_nodeValue_le j
      (x i) (a i) (b i) (a i ^ p) (b i ^ p) B.U B.V)
  have hm : OmitsMessages W := ⟨Nat.eq_zero_of_le_zero (by simpa [degreeOf_X] using hdeg 1),
    Nat.eq_zero_of_le_zero (by simpa [degreeOf_X] using hdeg 2)⟩
  have hs : W.degreeOf 3 ≤ sWeight B.U B.V := by simpa [degreeOf_X] using hdeg 3
  have ht : W.degreeOf 4 ≤ tWeight B.U B.V := by simpa [degreeOf_X] using hdeg 4
  have hbound : 131072 + D.height ≤ P.N := by
    have hD := D.height_eq
    have hP := P.size
    omega
  have hsmall : W.degreeOf 3 < p := by
    obtain ⟨huS, _, hvS, _⟩ := B.boxes
    unfold sWeight at hs
    change W.degreeOf 3 < 2130706433
    omega
  have hdegree := K21_11_2_1.graph_natDegree p (by decide) W hm hsmall
  have hWdeg : (graph p W).natDegree < P.N := by
    rw [hdegree]
    have hh : W.degreeOf 0 ≤ P.N - 1 := by simpa [degreeOf_X] using hdeg 0
    omega
  let G := Polynomial.C A.content * D.output
  have hDdeg : D.output.natDegree ≤ 131071 + D.height := by
    by_cases hz : D.output = 0
    · simp [hz]
    have hd := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr D.output_degree
    omega
  have hGdeg : G.natDegree ≤ 131071 + D.height :=
    (Polynomial.natDegree_C_mul_le A.content D.output).trans hDdeg
  have hrel : K21_8.relationOnAt p u (fixedNodes R) (graph p B.U) (graph p B.V) G := by
    rw [B.graphU, B.graphV, ← relationOn_eq]
    exact K21_8.reduced_scaled_relation D A.content
  have heval (i : Fin P.N) : (graph p W).eval (Polynomial.C (x i)) = G.eval (Polynomial.C (x i)) := by
    rw [eval_graph, hnodes]
    exact nodeValue_of_relation p (P := P) hrel i
  have hgraph : graph p W = G := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (Polynomial.C_injective.comp hx) heval
    rw [Fintype.card_fin]
    exact max_lt hWdeg (by omega)
  have hheight : W.degreeOf 0 ≤ 131071 + D.height := by
    rw [← hdegree, hgraph]
    exact hGdeg
  refine ⟨⟨W, hm, hheight, hs, ht, ?_⟩⟩
  intro i
  change nodeWordMap (x i) (a i) (b i) (a i ^ p) (b i ^ p) (B.U * MvPolynomial.X 1 + B.V * MvPolynomial.X 2 - W) = 0
  rw [map_sub, nodeWord_combination _ _ _ _ _ _ _ B.U_omits B.V_omits,
    nodeWord_omits _ _ _ _ _ W hm, hnodes]
  exact sub_self _

end
end K21_11_2_2
end Port_K1_11_2_2Proof
