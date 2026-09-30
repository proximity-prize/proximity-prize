import ProximityPrize.SubmissionLower.PacketBoundedIndex6815
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
