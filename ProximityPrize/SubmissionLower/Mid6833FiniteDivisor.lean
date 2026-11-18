/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Common-root selection adapted from the 68.32 release's
Koala6831MovingExceptions. The fixed divisor and simultaneous divisibility result
are used to reconstruct the two original received coordinates. -/
import ProximityPrize.SubmissionLower.Mid6833GenuineTypes
namespace ProximityPrize.SubmissionLower.Genuine6969
open Polynomial Finset Koala6831Moving
open scoped Polynomial Classical
noncomputable section
variable {K : Type*} [Field K]
private theorem affine_at_common_root {L : Type*} [Field L]
    (c : K →+* L) (a₀ a₁ : Polynomial K) (hA : IsCoprime a₀ a₁)
    (g : K) (x : L) (hz : (affineDenominator a₀ a₁ g).eval₂ c x = 0) :
    a₀.eval₂ c x = -(c g * a₁.eval₂ c x) ∧ a₁.eval₂ c x ≠ 0 := by
  have hs : a₀.eval₂ c x + c g * a₁.eval₂ c x = 0 := by
    simpa only [affineDenominator, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C] using hz
  refine ⟨eq_neg_of_add_eq_zero_left hs, ?_⟩
  intro h₁
  have h₀ : a₀.eval₂ c x = 0 := by simpa only [h₁, mul_zero, add_zero] using hs
  obtain ⟨U, V, hUV⟩ := hA
  have he := congrArg (Polynomial.eval₂ c x) hUV
  exact zero_ne_one (by simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_one, h₀, h₁, mul_zero, zero_add] using he)

private theorem seed_eq_of_common_root {L : Type*} [Field L]
    (c : K →+* L) (a₀ a₁ : Polynomial K) (hA : IsCoprime a₀ a₁)
    (g h : K) (x : L)
    (hg : (affineDenominator a₀ a₁ g).eval₂ c x = 0)
    (hh : (affineDenominator a₀ a₁ h).eval₂ c x = 0) : g = h := by
  obtain ⟨h₀, h₁⟩ := affine_at_common_root c a₀ a₁ hA g x hg
  have eq := h₀.symm.trans (affine_at_common_root c a₀ a₁ hA h x hh).1
  exact c.injective (mul_right_cancel₀ h₁ (neg_injective eq))

private theorem isUnit_of_natDegree_zero_ne_zero {P : Polynomial K}
    (hdeg : P.natDegree = 0) (hP : P ≠ 0) : IsUnit P := by
  have he := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hcoeff : P.coeff 0 ≠ 0 := by
    intro hz
    exact hP (by rw [he, hz, map_zero])
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map Polynomial.C

private theorem common_root_of_not_relPrime (A B : Polynomial K) (hA : A ≠ 0)
    (hbad : ¬ IsRelPrime A B) :
    ∃ x : AlgebraicClosure K,
      A.eval₂ (algebraMap K (AlgebraicClosure K)) x = 0 ∧
      B.eval₂ (algebraMap K (AlgebraicClosure K)) x = 0 := by
  classical
  change ¬ ∀ D : Polynomial K, D ∣ A → D ∣ B → IsUnit D at hbad
  push Not at hbad
  obtain ⟨D, hDA, hDB, hunit⟩ := hbad
  obtain ⟨U, hU⟩ := hDA
  obtain ⟨V, hV⟩ := hDB
  have hd : D ≠ 0 := by
    intro hz
    exact hA (by rw [hU, hz, zero_mul])
  have hdegree : 0 < D.natDegree := Nat.pos_of_ne_zero fun h =>
    hunit (isUnit_of_natDegree_zero_ne_zero h hd)
  let c := algebraMap K (AlgebraicClosure K)
  have hmap : 0 < (D.map c).natDegree := by rwa [Polynomial.natDegree_map_eq_of_injective c.injective]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (D.map c)
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hmap))
  have hroot : D.eval₂ c x = 0 := by
    rw [← Polynomial.eval_map]
    exact hx
  exact ⟨x, by rw [hU, Polynomial.eval₂_mul, hroot, zero_mul],
    by rw [hV, Polynomial.eval₂_mul, hroot, zero_mul]⟩

theorem fixed_divisor_exceptions (d : K[X]) (nd : d≠0) (A : Fin 2 → K[X])
    (cp : IsCoprime (A 0) (A 1)) (S : Finset K)
    (irregular : ∀g∈S, ¬IsCoprime d (affineDenominator (A 0) (A 1) g)) : S.card≤d.natDegree := by
  classical
  let c := algebraMap K (AlgebraicClosure K)
  have points (g : S) : ∃ x : AlgebraicClosure K, d.eval₂ c x=0 ∧
      (affineDenominator (A 0) (A 1) g).eval₂ c x=0 :=
    common_root_of_not_relPrime _ _ nd (fun r => irregular g g.property r.isCoprime)
  choose pt valid using points
  have inj : Function.Injective pt := by
    intro g h eq
    apply Subtype.ext
    exact seed_eq_of_common_root c _ _ cp g h (pt g) (valid g).2 (eq ▸ (valid h).2)
  by_contra! big
  have zero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (d.map c) inj
    (fun g => (Polynomial.eval_map ..).trans (valid g).1)
    (by rw [Polynomial.natDegree_map_eq_of_injective c.injective,Fintype.card_coe]; exact big)
  exact Polynomial.map_ne_zero nd zero

theorem separate_divisors (d p t : K[X]) (A B : Fin 2 → K[X]) (g : K)
    (reg : IsCoprime d (affineDenominator (A 0) (A 1) g))
    (det : d∣A 0*B 1-A 1*B 0)
    (row : d*p+affineDenominator (B 0) (B 1) g=affineDenominator (A 0) (A 1) g*t) :
    ∀j,d∣A j*t-B j := by
  obtain ⟨v,dv⟩ := det
  intro j
  apply reg.dvd_of_dvd_mul_left
  unfold affineDenominator at *
  fin_cases j <;> simp only [Fin.zero_eta,Fin.mk_one] <;> change _
  · refine ⟨A 0*p+C g*v,?_⟩
    linear_combination -(A 0)*row + C g*dv
  · refine ⟨A 1*p-v,?_⟩
    linear_combination -(A 1)*row - dv

theorem quotient_reconstructs {I : Type*} (x : I → K) (u : Fin 2 → I → K)
    (S : Finset I) (d : K[X]) (nd : d≠0) (T : K[X]) (A B : Fin 2 → K[X])
    (w : ℕ) (regular : ∀i∈S,d.eval (x i)≠0)
    (fits : ∀i∈S,∀j,d.eval (x i)*u j i+(B j).eval (x i)=(A j).eval (x i)*T.eval (x i))
    (divide : ∀j,d∣A j*T-B j) (low : ∀j,(A j*T-B j).natDegree≤w+d.natDegree) :
    ∃ V W : K[X], V.natDegree≤w ∧ W.natDegree≤w ∧ ∀i∈S,V.eval (x i)=u 0 i ∧ W.eval (x i)=u 1 i := by
  choose v hv using divide
  have degree (j) : (v j).natDegree≤w := by
    by_cases z : v j=0
    · simp [z]
    have sz := low j
    rw [hv,natDegree_mul nd z] at sz
    omega
  have value (j) (i) (hi:i∈S) : (v j).eval (x i)=u j i := by
    have ev := congrArg (Polynomial.eval (x i)) (hv j)
    simp only [eval_sub,eval_mul] at ev
    apply mul_left_cancel₀ (regular i hi)
    linear_combination -ev - fits i hi j
  exact ⟨v 0,v 1,degree 0,degree 1,fun i hi => ⟨value 0 i hi,value 1 i hi⟩⟩
#print axioms fixed_divisor_exceptions
#print axioms separate_divisors
#print axioms quotient_reconstructs
end
end ProximityPrize.SubmissionLower.Genuine6969
