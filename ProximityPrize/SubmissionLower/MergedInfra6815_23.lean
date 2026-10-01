import ProximityPrize.SubmissionLower.MergedInfra6815_17
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.WholeSpacePowerBox6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814

variable {K : Type*} [Field K]

structure Box where
  q : ℕ
  loB : ℕ
  hiB : ℕ
  loU : ℕ
  loT : ℕ
  deriving DecidableEq

def Box.R (a : Box) := 31-a.q*a.loB
def Box.U (a : Box) := 98-a.q*a.loU
def Box.T (a : Box) := 1700-a.q*a.loT
def Box.C (a : Box) := 13050360-a.q*(131071*a.loU-a.hiB)
def Box.n (a : Box) := a.R/2+1
def Box.receipt (a : Box) : ℕ :=
  a.n*(a.R+2-a.n)*(a.U+1)*(2*a.C-131071*a.U)*(a.T+1)

def Box.Covers (a : Box) (b u t : ℕ) : Prop :=
  a.loB≤b ∧ b≤a.hiB ∧ a.loU≤u ∧ a.loT≤t

abbrev Index (a : Box) := Σ j : Fin a.n, Σ r : Fin (a.R+1-2*j.val),
  Σ y : Fin (a.U+1), Fin (a.C-131071*y.val) × Fin (a.T+1)

def exponent (a : Box) (i : Index a) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.2.1.val,i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

theorem twice_sum_affine (n c w : ℕ) (h : w*(n-1)≤c) :
    2*(∑ i : Fin n, (c-w*i.val))=n*(2*c-w*(n-1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n=0
    · subst n; simp
    have hnw : w*n≤c := by simpa using h
    have hprev : w*(n-1)≤c := (Nat.mul_le_mul_left w (Nat.sub_le n 1)).trans hnw
    have hi := ih hprev
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    simp only [Nat.add_sub_cancel]
    have hsub := Nat.sub_add_cancel hnw
    have hsub' := Nat.sub_add_cancel hprev
    have hdouble := Nat.sub_add_cancel (show w*n≤2*c by omega)
    have hdouble' := Nat.sub_add_cancel (show w*(n-1)≤2*c by omega)
    have hn1 : n-1+1=n := by omega
    nlinarith

theorem card_twice (a : Box) (h : 131071*a.U≤a.C) :
    2*Fintype.card (Index a)=a.receipt := by
  classical
  have hn : 2*(a.n-1)≤a.R := by dsimp [Box.n]; omega
  have hj := twice_sum_affine a.n (a.R+1) 2 (by omega)
  have hy := twice_sum_affine (a.U+1) a.C 131071 (by simpa using h)
  have hnj : a.n≤a.R+2 := by dsimp [Box.n]; omega
  have hclosed : (∑ j : Fin a.n, (a.R+1-2*j.val))=a.n*(a.R+2-a.n) := by
    have hp := Nat.sub_add_cancel hn
    have hq := Nat.sub_add_cancel hnj
    have hnn : a.n-1+1=a.n := by simp [Box.n]
    have hr := Nat.sub_add_cancel (show 2*(a.n-1)≤2*(a.R+1) by omega)
    nlinarith
  simp only [Index,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  simp only [←Finset.sum_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  rw [hclosed]
  simp only [Nat.add_sub_cancel] at hy
  unfold Box.receipt
  calc
    _ = a.n*(a.R+2-a.n)*(2*(∑ i : Fin (a.U+1), (a.C-131071*i.val)))*(a.T+1) := by ring
    _ = _ := by rw [hy]; ring

theorem support_box (a : Box) (Q : Poly (K := K))
    (hc : weightedTotalDegree codeWeights Q<a.C)
    (ht : weightedTotalDegree totalWeights Q≤a.T)
    (hu : weightedTotalDegree middleWeights Q≤a.U)
    (hb : weightedTotalDegree slopeWeights Q≤a.R) :
    ∀ e∈Q.support, e∈Set.range (exponent a) := by
  intro e he
  have hc' := (Finset.le_sup (f := Finsupp.weight codeWeights) he).trans_lt hc
  have ht' := (Finset.le_sup (f := Finsupp.weight totalWeights) he).trans ht
  have hu' := (Finset.le_sup (f := Finsupp.weight middleWeights) he).trans hu
  have hb' := (Finset.le_sup (f := Finsupp.weight slopeWeights) he).trans hb
  simp [weight_coords,codeWeights,totalWeights,middleWeights,slopeWeights] at hc' ht' hu' hb'
  refine ⟨⟨⟨e 1,?_⟩,⟨e 3,?_⟩,⟨e 2,by omega⟩,⟨e 0,?_⟩,⟨e 4,by omega⟩⟩,?_⟩
  · dsimp [Box.n]; omega
  · change e 3<a.R+1-2*e 1; omega
  · change e 0<a.C-131071*e 2; omega
  · ext i; fin_cases i <;> simp [exponent]

theorem factor_code_lower (J : Poly (K := K)) (hJ : J≠0) (u b : ℕ)
    (hu : u≤weightedTotalDegree middleWeights J)
    (hb : weightedTotalDegree slopeWeights J≤b) :
    131071*u-b≤weightedTotalDegree codeWeights J := by
  obtain ⟨e,he,hmax⟩ := Finset.exists_mem_eq_sup J.support
    (support_nonempty.mpr hJ) (Finsupp.weight middleWeights)
  have hm : u≤Finsupp.weight middleWeights e := by
    change u≤J.support.sup (Finsupp.weight middleWeights) at hu
    rwa [hmax] at hu
  have hs := (Finset.le_sup (f := Finsupp.weight slopeWeights) he).trans hb
  have hc : Finsupp.weight codeWeights e≤weightedTotalDegree codeWeights J := Finset.le_sup he
  simp [weight_coords,codeWeights,middleWeights,slopeWeights] at hm hs hc
  dsimp only [codeWeights]
  omega

def powerQuotient (V : Submodule K (Poly (K := K))) (J : Poly (K := K)) (q : ℕ)
    (hd : ∀ v : V, J^q∣v.val) (v : V) : Poly (K := K) := Classical.choose (hd v)

theorem powerQuotient_spec (V : Submodule K (Poly (K := K))) (J : Poly (K := K)) (q : ℕ)
    (hd : ∀ v : V, J^q∣v.val) (v : V) : v.val=J^q*powerQuotient V J q hd v :=
  Classical.choose_spec (hd v)

def powerQuotientLinear (V : Submodule K (Poly (K := K))) (J : Poly (K := K)) (q : ℕ)
    (hJ : J≠0) (hd : ∀ v : V, J^q∣v.val) : V →ₗ[K] Poly (K := K) where
  toFun := powerQuotient V J q hd
  map_add' v u := by
    apply mul_left_cancel₀ (pow_ne_zero q hJ)
    rw [mul_add,←powerQuotient_spec,←powerQuotient_spec,←powerQuotient_spec]
    rfl
  map_smul' c v := by
    apply mul_left_cancel₀ (pow_ne_zero q hJ)
    rw [←powerQuotient_spec]
    change c • v.val=J^q*(c • powerQuotient V J q hd v)
    rw [powerQuotient_spec V J q hd v]
    simp only [MvPolynomial.smul_eq_C_mul]
    ac_rfl

theorem exists_not_dvd_power
    (V : Submodule K (Poly (K := K))) [Module.Finite K V]
    (hdim : 627003341034≤Module.finrank K V)
    (hcode : ∀ P∈V, weightedTotalDegree codeWeights P<13050360)
    (htotal : ∀ P∈V, weightedTotalDegree totalWeights P≤1700)
    (hmiddle : ∀ P∈V, weightedTotalDegree middleWeights P≤98)
    (hslope : ∀ P∈V, weightedTotalDegree slopeWeights P≤31)
    (J : Poly (K := K)) (hJ : J≠0) (a : Box)
    (ha : a.Covers (weightedTotalDegree slopeWeights J)
      (weightedTotalDegree middleWeights J) (weightedTotalDegree totalWeights J))
    (hlin : 131071*a.U≤a.C) (hfit : a.receipt<2*627003341034) :
    ∃ P∈V, ¬J^a.q∣P := by
  classical
  by_contra hno
  have hd : ∀ P∈V, J^a.q∣P := by simpa only [not_exists,not_and,not_not] using hno
  let hv : ∀ v : V, J^a.q∣v.val := fun v => hd v.val v.property
  let f := powerQuotientLinear V J a.q hJ hv
  have hf : Function.Injective f := by
    intro v u he
    apply Subtype.ext
    rw [powerQuotient_spec V J a.q hv v,powerQuotient_spec V J a.q hv u]
    exact congrArg (fun Q => J^a.q*Q) he
  have hs : ∀ v : V, ∀ e∈(f v).support, e∈Set.range (exponent a) := by
    intro v e he
    have hq : f v≠0 := by intro hz; simpa [hz] using he
    have hval : v.val=J^a.q*f v := powerQuotient_spec V J a.q hv v
    have hc := hcode v.val v.property
    have ht := htotal v.val v.property
    have hu := hmiddle v.val v.property
    have hb := hslope v.val v.property
    rw [hval,weight_mul _ _ _ (pow_ne_zero _ hJ) hq,weight_pow _ _ hJ] at hc ht hu hb
    have hcJ := factor_code_lower J hJ a.loU a.hiB ha.2.2.1 ha.2.1
    have hcq := Nat.mul_le_mul_left a.q hcJ
    have hbq := Nat.mul_le_mul_left a.q ha.1
    have huq := Nat.mul_le_mul_left a.q ha.2.2.1
    have htq := Nat.mul_le_mul_left a.q ha.2.2.2
    apply support_box a (f v) _ _ _ _ e he
    · dsimp [Box.C]; omega
    · dsimp [Box.T]; omega
    · dsimp [Box.U]; omega
    · dsimp [Box.R]; omega
  have hcard := finrank_le_coefficients (exponent a) f hf hs
  have htwice := card_twice a hlin
  omega

end
end ProximityPrize.SubmissionLower.WholeSpacePowerBox6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.PacketExactIndex6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 20000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts

abbrev Index (C T R U : ℕ) :=
  SecondJetRelaxedGlobalIndex.Index (fun _ => C) 131071 T R (R/2) U

def exponent (C T R U : ℕ) (i : Index C T R U) : Fin 5 →₀ ℕ :=
  SecondJetRelaxedGlobalIndex.exponent i

theorem exponent_injective (C T R U : ℕ) : Function.Injective (exponent C T R U) :=
  SecondJetRelaxedGlobalIndex.exponent_injective _ _ _ _ _ _

theorem card_eq (C T R U : ℕ) (hUT : U≤T) :
    Fintype.card (Index C T R U)=coefficientCount (fun _ => C) 131071 T R (R/2) U :=
  card_index_closed _ _ _ _ _ _ hUT

theorem mem_range_of_bounds (C T R U : ℕ) (e : Fin 5 →₀ ℕ)
    (hc : e 0+131069*e 1+131071*e 2+131070*e 3<C)
    (ht : e 1+e 2+e 3+e 4≤T)
    (hr : 2*e 1+e 3≤R) (hu : e 1+e 2+e 3≤U) :
    e∈Set.range (exponent C T R U) := by
  have hh : e 1<R/2+1 := by omega
  have hrr : e 3<R-2*e 1+1 := by omega
  have hx : e 0<budget (fun _ => C) 131071 (e 1) (e 3)-131071*e 2 := by
    simp only [budget]
    omega
  have hy : e 2<yCount (fun _ => C) 131071 U (e 1) (e 3) := by
    simp only [yCount,budget]
    omega
  have hz : e 4<T+1-e 1-e 3-e 2 := by omega
  refine ⟨⟨⟨e 1,hh⟩,⟨e 3,hrr⟩,⟨e 2,hy⟩,⟨e 0,hx⟩,⟨e 4,hz⟩⟩,?_⟩
  ext i
  fin_cases i <;> simp [exponent,SecondJetRelaxedGlobalIndex.exponent]

variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.PacketExactIndex6815
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.PacketBoundedIndex6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts

abbrev Index (C T R S U : ℕ) :=
  SecondJetRelaxedGlobalIndex.Index (fun _ => C) 131071 T R S U

def exponent (C T R S U : ℕ) (i : Index C T R S U) : Fin 5 →₀ ℕ :=
  SecondJetRelaxedGlobalIndex.exponent i

theorem card_eq (C T R S U : ℕ) (hUT : U≤T) :
    Fintype.card (Index C T R S U)=coefficientCount (fun _ => C) 131071 T R S U :=
  card_index_closed _ _ _ _ _ _ hUT

theorem mem_range_of_bounds (C T R S U : ℕ) (e : Fin 5 →₀ ℕ)
    (hc : e 0+131069*e 1+131071*e 2+131070*e 3<C)
    (ht : e 1+e 2+e 3+e 4≤T)
    (hr : 2*e 1+e 3≤R) (hs : e 1≤S) (hu : e 1+e 2+e 3≤U) :
    e∈Set.range (exponent C T R S U) := by
  have hh : e 1<S+1 := by omega
  have hrr : e 3<R-2*e 1+1 := by omega
  have hx : e 0<budget (fun _ => C) 131071 (e 1) (e 3)-131071*e 2 := by
    simp only [budget]
    omega
  have hy : e 2<yCount (fun _ => C) 131071 U (e 1) (e 3) := by
    simp only [yCount,budget]
    omega
  have hz : e 4<T+1-e 1-e 3-e 2 := by omega
  refine ⟨⟨⟨e 1,hh⟩,⟨e 3,hrr⟩,⟨e 2,hy⟩,⟨e 0,hx⟩,⟨e 4,hz⟩⟩,?_⟩
  ext i
  fin_cases i <;> simp [exponent,SecondJetRelaxedGlobalIndex.exponent]

variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.PacketBoundedIndex6815
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.PacketPortfolioAvoidance6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 30000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpacePowerBox6814 SecondJetRelaxedGlobalCounts

structure SourceCaps where
  C : ℕ
  T : ℕ
  B : ℕ
  S : ℕ
  U : ℕ

structure OwnerBox where
  q : ℕ
  loB : ℕ
  hiB : ℕ
  loS : ℕ
  loU : ℕ
  loT : ℕ

def remC (p : SourceCaps) (a : OwnerBox) := p.C-a.q*(131071*a.loU-a.hiB)
def remT (p : SourceCaps) (a : OwnerBox) := p.T-a.q*a.loT
def remB (p : SourceCaps) (a : OwnerBox) := p.B-a.q*a.loB
def remU (p : SourceCaps) (a : OwnerBox) := min (p.U-a.q*a.loU) (remT p a)
def remS (p : SourceCaps) (a : OwnerBox) := min (p.S-a.q*a.loS) (min (remB p a/2) (remU p a))
def count (p : SourceCaps) (a : OwnerBox) :=
  coefficientCount (fun _ => remC p a) 131071 (remT p a) (remB p a) (remS p a) (remU p a)
def Impossible (p : SourceCaps) (a : OwnerBox) : Prop :=
  p.B<a.q*a.loB ∨ p.S<a.q*a.loS ∨ p.U<a.q*a.loU ∨ p.T<a.q*a.loT ∨
    p.C≤a.q*(131071*a.loU-a.hiB)

variable {K : Type*} [Field K]

def Bounds (p : SourceCaps) (P : Poly (K:=K)) : Prop :=
  weightedTotalDegree codeWeights P<p.C ∧ weightedTotalDegree totalWeights P≤p.T ∧
  weightedTotalDegree slopeWeights P≤p.B ∧ P.degreeOf 1≤p.S ∧
  weightedTotalDegree middleWeights P≤p.U

def Covers (a : OwnerBox) (J : Poly (K:=K)) : Prop :=
  a.loB≤weightedTotalDegree slopeWeights J ∧ weightedTotalDegree slopeWeights J≤a.hiB ∧
  a.loS≤J.degreeOf 1 ∧ a.loU≤weightedTotalDegree middleWeights J ∧
  a.loT≤weightedTotalDegree totalWeights J

theorem quotient_bounds (p : SourceCaps) (a : OwnerBox)
    (P J Q : Poly (K:=K)) (hJ : J≠0) (hQ : Q≠0)
    (heq : P=J^a.q*Q) (hP : Bounds p P) (ha : Covers a J) :
    ¬Impossible p a ∧
    weightedTotalDegree codeWeights Q<remC p a ∧
    weightedTotalDegree totalWeights Q≤remT p a ∧
    weightedTotalDegree slopeWeights Q≤remB p a ∧
    Q.degreeOf 1≤p.S-a.q*a.loS ∧
    weightedTotalDegree middleWeights Q≤p.U-a.q*a.loU := by
  obtain ⟨hc,ht,hb,hs,hu⟩ := hP
  obtain ⟨hb0,hb1,hs0,hu0,ht0⟩ := ha
  rw [heq,weight_mul _ _ _ (pow_ne_zero _ hJ) hQ,weight_pow _ _ hJ] at hc ht hb hu
  rw [heq,degreeOf_mul_eq (pow_ne_zero _ hJ) hQ,degreeOf_pow_eq _ _ _ hJ] at hs
  have hcode := factor_code_lower J hJ a.loU a.hiB hu0 hb1
  have hbc := Nat.mul_le_mul_left a.q hb0
  have hsc := Nat.mul_le_mul_left a.q hs0
  have huc := Nat.mul_le_mul_left a.q hu0
  have htc := Nat.mul_le_mul_left a.q ht0
  have hcc := Nat.mul_le_mul_left a.q hcode
  simp only [Impossible,remC,remT,remB]
  omega

theorem quotient_support (p : SourceCaps) (a : OwnerBox)
    (P J Q : Poly (K:=K)) (hJ : J≠0) (hQ : Q≠0)
    (heq : P=J^a.q*Q) (hP : Bounds p P) (ha : Covers a J) :
    ∀ e∈Q.support, e∈Set.range
      (PacketBoundedIndex6815.exponent (remC p a) (remT p a) (remB p a) (remS p a) (remU p a)) := by
  obtain ⟨_,hc,ht,hb,hs,hu⟩ := quotient_bounds p a P J Q hJ hQ heq hP ha
  intro e he
  have c := (le_weightedTotalDegree codeWeights he).trans_lt hc
  have t := (le_weightedTotalDegree totalWeights he).trans ht
  have b := (le_weightedTotalDegree slopeWeights he).trans hb
  have s := (MvPolynomial.monomial_le_degreeOf 1 he).trans hs
  have u := (le_weightedTotalDegree middleWeights he).trans hu
  simp [weight_coords,codeWeights,totalWeights,slopeWeights,middleWeights] at c t b u
  apply PacketBoundedIndex6815.mem_range_of_bounds
  all_goals
    try dsimp only [remS,remU]
    omega

theorem exists_not_dvd_power (p : SourceCaps) (a : OwnerBox) (Kdim : ℕ)
    (V : Submodule K (Poly (K:=K))) [Module.Finite K V]
    (hdim : Kdim≤Module.finrank K V)
    (hb : ∀ P∈V, Bounds p P)
    (J : Poly (K:=K)) (hJ : J≠0) (ha : Covers a J)
    (hgood : (Impossible p a ∧ 0<Kdim) ∨ count p a<Kdim) :
    ∃ P∈V, ¬J^a.q∣P := by
  by_contra hno
  have hd : ∀ P∈V, J^a.q∣P := by simpa only [not_exists,not_and,not_not] using hno
  let hv : ∀ v : V, J^a.q∣v.val := fun v => hd v.val v.property
  let f := powerQuotientLinear V J a.q hJ hv
  have hf : Function.Injective f := by
    intro v u he
    apply Subtype.ext
    rw [powerQuotient_spec V J a.q hv v,powerQuotient_spec V J a.q hv u]
    exact congrArg (fun Q => J^a.q*Q) he
  rcases hgood with ⟨hbad,hpos⟩ | hcount
  · have hz : ∀ v, f v=0 := by
      intro v
      by_contra hn
      exact (quotient_bounds p a v.val J (f v) hJ hn
        (powerQuotient_spec V J a.q hv v) (hb v.val v.property) ha).1 hbad
    have hcard := finrank_le_coefficients (fun i : Fin 0 => Fin.elim0 i) f hf
      (by intro v e he; simp [hz v] at he)
    simp only [Fintype.card_fin] at hcard
    omega
  · have hsupport : ∀ v, ∀ e∈(f v).support, e∈Set.range
        (PacketBoundedIndex6815.exponent (remC p a) (remT p a) (remB p a) (remS p a) (remU p a)) := by
      intro v e he
      have hn : f v≠0 := by intro hz; simp [hz] at he
      exact quotient_support p a v.val J (f v) hJ hn
        (powerQuotient_spec V J a.q hv v) (hb v.val v.property) ha e he
    have hcard := finrank_le_coefficients _ f hf hsupport
    have hUT : remU p a≤remT p a := min_le_right _ _
    rw [PacketBoundedIndex6815.card_eq (remC p a) (remT p a) (remB p a)
      (remS p a) (remU p a) hUT] at hcard
    change Module.finrank K V≤count p a at hcard
    omega

end
end ProximityPrize.SubmissionLower.PacketPortfolioAvoidance6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingSourceSaturation6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open UniqueFactorizationMonoid MovingSourceClearing6814 MovingSourceProperness6814 RCN259

variable {R : Type*} [CommRing R] [IsDomain R]
  [GCDMonoid (Polynomial R)] [NormalizationMonoid (Polynomial R)]
  [UniqueFactorizationMonoid (Polynomial R)]

theorem cleared_gcd_nonzero_at {E : Type*} [CommRing E] [IsDomain E]
    (P Q : Polynomial R) (n m : ℕ) (h q : R)
    (hP : P≠0) (hn : P.natDegree ≤ n) (hm : Q.natDegree ≤ m) (hh : h≠0)
    (hrel : IsRelPrime P Q) (ev : Polynomial R →+* E) (hev : ev (Polynomial.C h)≠0) :
    ev (gcd (targetPolynomial P n h q) (targetPolynomial Q m h q))≠0 := by
  classical
  let A := targetPolynomial P n h q
  let B := targetPolynomial Q m h q
  have hA : A≠0 := targetPolynomial_ne_zero P n h q hP hn hh
  have hG : gcd A B≠0 := gcd_ne_zero_of_left hA
  intro hz
  have hassoc := Associated.map ev (prod_normalizedFactors hG)
  rw [hz] at hassoc
  have hp : ev (normalizedFactors (gcd A B)).prod=0 := (associated_zero_iff_eq_zero _).mp hassoc
  rw [map_multiset_prod] at hp
  obtain ⟨f,hf,hfzero⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  have hfi : Irreducible f := irreducible_of_normalized_factor f hf
  have hfg := dvd_of_mem_normalizedFactors hf
  have hfh : f ∣ Polynomial.C h := common_prime_dvd_denominator P Q n m h q hn hm hh hrel
    f hfi.prime (hfg.trans (gcd_dvd_left A B)) (hfg.trans (gcd_dvd_right A B))
  obtain ⟨g,hg⟩ := hfh
  apply hev
  rw [hg,map_mul,hfzero,zero_mul]

end
end ProximityPrize.SubmissionLower.MovingSourceSaturation6814
end MergedPart4
