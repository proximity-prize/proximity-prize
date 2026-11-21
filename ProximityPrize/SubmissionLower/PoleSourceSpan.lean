import ProximityPrize.SubmissionLower.Fast065

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24

set_option maxHeartbeats 1200000

namespace PoleSourceSpan

open K1_14 (Shape)
open K1_14_1 (seedWeight otherBlock)
open K1_14_1_7
open K1_14_1_7_2 (inputTaylor)
open Polynomial
open scoped BigOperators Polynomial

open private taylor_seed_degree from ProximityPrize.SubmissionLower.Fast065

noncomputable section

abbrev sourceSeed {F : Type} [Field F] : Seed F →+* TrueSource F :=
  Polynomial.C.comp (Polynomial.C.comp Polynomial.C)

def sourceX {F : Type} [Field F] (α : F) : TrueSource F :=
  Polynomial.C (Polynomial.C (Polynomial.X - Polynomial.C (algebraMap F (Seed F) α)))

abbrev sourceY {F : Type} [Field F] : TrueSource F :=
  Polynomial.C (Polynomial.X (R := (Seed F)[X]))

abbrev sourceV {F : Type} [Field F] : TrueSource F := Polynomial.X

def centeredMonomial {F : Type} [Field F] (α : F) (side : Fin 2)
    (a i u q j : ℕ) : TrueSource F :=
  sourceX α ^ a * (sourceSeed (MvPolynomial.X side)) ^ i *
    (sourceSeed (MvPolynomial.X (otherBlock side))) ^ u * sourceY ^ (q-j) * sourceV ^ j

def sourceMonomials {F : Type} [Field F] (s : Shape) (α : F) (side : Fin 2) :
    Set (TrueSource F) :=
  {P | ∃ a i u q j, q ≤ s.B ∧ j ≤ min q s.J ∧ i+u ≤ s.U ∧
    P = centeredMonomial α side a i u q j}

private theorem seedWeight_split (side : Fin 2) (e : Exponent) :
    seedWeight e = e side + e (otherBlock side) := by
  rw [seedWeight, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  fin_cases side <;> simp [otherBlock, Nat.add_comm]

private theorem seed_expand {F : Type} [Field F] (side : Fin 2) (e : Exponent) :
    (MvPolynomial.monomial e (1 : F)) =
      MvPolynomial.X side ^ (e side) * MvPolynomial.X (otherBlock side) ^ (e (otherBlock side)) := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, one_mul]
  have he : e = Finsupp.single side (e side) + Finsupp.single (otherBlock side) (e (otherBlock side)) := by
    apply Finsupp.ext
    intro k
    fin_cases side <;> fin_cases k <;> simp [otherBlock]
  rw [← he]

private theorem centered_product {F : Type} [Field F] (α : F) (p : Seed F)
    (a y j : ℕ) :
    sourceSeed p * sourceX α ^ a * sourceY ^ y * sourceV ^ j =
      Polynomial.monomial j (Polynomial.monomial y
        (Polynomial.C p * (Polynomial.X - Polynomial.C (algebraMap F (Seed F) α)) ^ a)) := by
  simp only [sourceSeed, RingHom.comp_apply, sourceX, sourceY, sourceV, ← map_pow, ← map_mul,
    Polynomial.C_mul_X_pow_eq_monomial]

private theorem sourceSeed_scalar {F : Type} [Field F] (e : Exponent) (c : F) :
    sourceSeed (MvPolynomial.monomial e c) = c • sourceSeed (MvPolynomial.monomial e 1) := by
  rw [Algebra.smul_def]
  change _ = sourceSeed (MvPolynomial.C c) * _
  rw [← map_mul, MvPolynomial.C_mul_monomial, mul_one]

/-- Every shaped source belongs to the span of true centered X-monomials,
with exact jet and seed caps and arbitrary abscissa exponent. -/
theorem shaped_mem_span {F : Type} [Field F] {s : Shape} (α : F) (side : Fin 2)
    {P : TrueSource F} (hP : Shaped s P) :
    P ∈ Submodule.span F (sourceMonomials s α side) := by
  let M := Submodule.span F (sourceMonomials s α side)
  change P ∈ M
  rw [P.as_sum_support]
  apply M.sum_mem
  intro j _
  rw [show Polynomial.monomial j (P.coeff j) =
      Polynomial.monomial j (∑ y ∈ (P.coeff j).support, Polynomial.monomial y ((P.coeff j).coeff y)) from
    congrArg _ (P.coeff j).as_sum_support, map_sum]
  apply M.sum_mem
  intro y hy
  let p := (P.coeff j).coeff y
  let r := algebraMap F (Seed F) α
  have hp : p ≠ 0 := Polynomial.mem_support_iff.mp hy
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hp
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp ha)
  have hbox := hP j y a e (MvPolynomial.mem_support_iff.mp he)
  change Polynomial.monomial j (Polynomial.monomial y p) ∈ M
  rw [← Polynomial.sum_taylor_eq p r, Polynomial.sum]
  simp only [map_sum]
  apply M.sum_mem
  intro a _
  let Q := (Polynomial.taylor r p).coeff a
  change Polynomial.monomial j (Polynomial.monomial y (Polynomial.C Q * (Polynomial.X - Polynomial.C r)^a)) ∈ M
  rw [show Q = ∑ e ∈ Q.support, MvPolynomial.monomial e (Q.coeff e) from Q.as_sum]
  simp only [map_sum, Finset.sum_mul]
  apply M.sum_mem
  intro e he
  have hdeg : seedWeight e ≤ s.U :=
    (MvPolynomial.le_totalDegree he).trans (taylor_seed_degree s α P hP j y a)
  change Polynomial.monomial j (Polynomial.monomial y
    (Polynomial.C (MvPolynomial.monomial e (Q.coeff e)) * (Polynomial.X - Polynomial.C r)^a)) ∈ M
  rw [← centered_product α _ a y j, sourceSeed_scalar, smul_mul_assoc, smul_mul_assoc,
    smul_mul_assoc]
  apply M.smul_mem
  rw [seed_expand side, map_mul, map_pow, map_pow]
  apply Submodule.subset_span
  refine ⟨a,e side,e (otherBlock side),y+j,j,hbox.1,
    le_min (Nat.le_add_left _ _) hbox.2.1, ?_, ?_⟩
  · simpa only [← seedWeight_split side] using hdeg
  · have hy : y+j-j = y := by omega
    simp only [centeredMonomial, hy]
    have hcomm (x c d : TrueSource F) : c*d*x = x*c*d :=
      (mul_comm (c*d) x).trans (mul_assoc x c d).symm
    exact congrArg (fun t : TrueSource F ↦ t * sourceY^y * sourceV^j)
      (hcomm (sourceX α^a) ((sourceSeed (MvPolynomial.X side)) ^ e side)
        ((sourceSeed (MvPolynomial.X (otherBlock side))) ^ e (otherBlock side)))

end
end PoleSourceSpan
