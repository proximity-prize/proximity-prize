import ProximityPrize.SubmissionLower.KoalaBoxLift
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
import ProximityPrize.SubmissionLower.KoalaRawNodes

set_option autoImplicit false
set_option maxHeartbeats 900000
namespace SplitCut.PointCount
noncomputable section
open MvPolynomial Filter
open scoped BigOperators Polynomial
variable {F E σ α : Type*} [Field F] [Field E] [Algebra F E] [Finite σ]

/-- A curve has positive integral degree. The slope is a difference of two consecutive
    values of its eventually linear Hilbert function. -/
theorem curve_degree_nat {P : Ideal (MvPolynomial σ F)} (hP : P ≠ ⊤)
    (hd : (affineHilbertPolynomial P).natDegree = 1) : ∃ d : ℕ, 0 < d ∧ affineDegree P = (d:ℚ) := by
  let H := affineHilbertPolynomial P
  have heq := Polynomial.eq_X_add_C_of_natDegree_le_one hd.le
  have hlin (n : ℕ) : H.eval (n:ℚ) = H.coeff 1*n+H.coeff 0 := by
    calc H.eval (n:ℚ) = (Polynomial.C (H.coeff 1)*Polynomial.X+Polynomial.C (H.coeff 0)).eval n :=
          congrArg (fun q : ℚ[X] => q.eval (n:ℚ)) heq
      _ = _ := by simp
  obtain ⟨n,hn⟩ := eventually_atTop.mp (eventually_eval_affineHilbertPolynomial P)
  have h₀ := hn n le_rfl
  have h₁ := hn (n+1) (by omega)
  have hd' : affineDegree P = H.coeff 1 := by simp [affineDegree,Polynomial.leadingCoeff,hd,H]
  have hpos := affineDegree_pos hP
  rw [hd'] at hpos
  change H.eval _ = _ at h₀ h₁
  rw [hlin] at h₀ h₁
  push_cast at h₁
  have ht : (affineHilbertFunction P n : ℚ) < affineHilbertFunction P (n+1) := by
    linarith
  have ht' : affineHilbertFunction P n+1 ≤ affineHilbertFunction P (n+1) := by
    exact Nat.succ_le_of_lt (Nat.cast_lt.mp ht)
  refine ⟨affineHilbertFunction P (n+1)-affineHilbertFunction P n, by omega, ?_⟩
  rw [hd',Nat.cast_sub (by omega)]
  linarith

theorem curve_degree {P : Ideal (MvPolynomial σ F)} (hP : P ≠ ⊤)
    (hd : (affineHilbertPolynomial P).natDegree = 1) : 1 ≤ affineDegree P := by
  obtain ⟨d,hd,he⟩ := curve_degree_nat hP hd
  rw [he]
  exact_mod_cast hd

/-- A finite set of distinct marked points on a proper cut of an affine curve. -/
theorem cut_points {P : Ideal (MvPolynomial σ F)} [P.IsPrime]
    (hd : (affineHilbertPolynomial P).natDegree = 1)
    {f : MvPolynomial σ F} (hf : f ∉ P) {b : ℕ} (hb : f.totalDegree ≤ b)
    {x : α → σ → E} (T : Finset α) (hinj : Set.InjOn x (T : Set α))
    (hP : ∀ i ∈ T, x i ∈ zeroLocus E P) (hz : ∀ i ∈ T, aeval (x i) f = 0) :
    (T.card : ℚ) ≤ (b:ℚ)*affineDegree P := by
  classical
  let S := T.image x
  have hS : ∀ y ∈ S, y ∈ zeroLocus E P ∧ aeval y (1 : MvPolynomial σ F) ≠ 0 := by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    exact ⟨hP _ hi, by simp⟩
  have hset : (S : Set (σ → E)) ∩ {y | aeval y f = 0} = S :=
    Set.inter_eq_left.mpr (by
      intro y hy
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
      exact hz _ hi)
  have he := ncard_inter_cut_le_of_retained_le (1 : MvPolynomial σ F) hf hb S hS
    (c := 1) (by norm_num) (fun Q hQ => by
      have hqd := principalCut_natDegree_affineHilbertPolynomial_add_one hf
        (Ideal.mem_retainedMinimalPrimes.mp hQ).1
      have hzero : (affineHilbertPolynomial Q).natDegree = 0 := by omega
      obtain ⟨hfin,hcard⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K:=E) Q hzero
      simpa using (le_trans (Nat.cast_le.mpr (Set.ncard_le_ncard Set.inter_subset_right hfin)) hcard))
  rw [hset,Set.ncard_coe_finset,mul_one] at he
  simpa only [S,Finset.card_image_of_injOn hinj] using he

/-- Decomposing a marked finite family into the minimal components over an ideal. -/
theorem cover (I : Ideal (MvPolynomial σ F)) {x : α → σ → E} (T : Finset α)
    (hon : ∀ i ∈ T, x i ∈ zeroLocus E I)
    [DecidableRel (fun (i : α) (Q : Ideal (MvPolynomial σ F)) => x i ∈ zeroLocus E Q)] :
    T.card ≤ ∑ Q ∈ I.minimalPrimesFinset, (T.filter (fun i => x i ∈ zeroLocus E Q)).card := by
  classical
  refine (Finset.card_le_card ?_).trans Finset.card_biUnion_le
  intro i hi
  let p := RingHom.ker (aeval (R:=F) (x i))
  have hp : p.IsPrime := RingHom.ker_isPrime _
  have hI : I ≤ p := fun f hf => RingHom.mem_ker.mpr (hon _ hi f hf)
  obtain ⟨Q,hQ,hQp⟩ := Ideal.exists_minimalPrimes_le hI
  exact Finset.mem_biUnion.mpr ⟨Q,Ideal.mem_minimalPrimesFinset.mpr hQ,
    Finset.mem_filter.mpr ⟨hi,fun f hf => RingHom.mem_ker.mp (hQp hf)⟩⟩

end
end SplitCut.PointCount
#print axioms SplitCut.PointCount.curve_degree
#print axioms SplitCut.PointCount.cut_points
#print axioms SplitCut.PointCount.cover
