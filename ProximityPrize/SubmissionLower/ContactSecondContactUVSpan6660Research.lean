import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSecondContactSFreeInterpolation6660Research

 












namespace ProximityPrize.SubmissionLower.ContactSecondContactUVSpan6660Research

open ContactSecondContactSFreeInterpolation6660Research
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.checkUnivs false

noncomputable section

variable (K : Type*) [Field K]

abbrev Coeff := MvPolynomial (Fin 4) K
abbrev Outer := Polynomial (Coeff K)
abbrev LowJet (m : ℕ) := Fin m → Coeff K

 
def lowJet (m : ℕ) : Outer K →ₗ[K] LowJet K m where
  toFun P j := P.coeff j.val
  map_add' P Q := by
    funext j
    simp
  map_smul' a P := by
    funext j
    simp

def contactTail : Outer K :=
  -Polynomial.C (MvPolynomial.C ((2 : K)⁻¹)) *
      Polynomial.C (MvPolynomial.X 2) +
    Polynomial.X * Polynomial.C (MvPolynomial.X 0)

def contactV : Outer K := Polynomial.X ^ 2 * contactTail K

def contactU : Outer K :=
  Polynomial.X * Polynomial.C (MvPolynomial.X 1) + contactV K

theorem contactU_eq_XR_add_contactV :
    contactU K = Polynomial.X * Polynomial.C (MvPolynomial.X 1) + contactV K := by
  rfl

theorem X_sq_dvd_contactV :
    (Polynomial.X : Outer K) ^ 2 ∣ contactV K := by
  exact ⟨contactTail K, rfl⟩

theorem X_dvd_contactU :
    (Polynomial.X : Outer K) ∣ contactU K := by
  apply dvd_add
  · exact ⟨Polynomial.C (MvPolynomial.X 1), rfl⟩
  · exact (dvd_pow_self Polynomial.X (by omega)).trans (X_sq_dvd_contactV K)

 
structure UVLabel (m C rCap : ℕ) where
  d : Fin (C + 1)
  beta : Fin (min d.val rCap + 1)
  z : Fin (C + 1 - d.val)
  k : Fin (m - (d.val - rCap) - 2 * beta.val)
deriving Fintype

def uvLabelEquiv (m C rCap : ℕ) : UVLabel m C rCap ≃ UVSpanIndex m C rCap where
  toFun i := ⟨i.d, ⟨i.beta, ⟨i.z, i.k⟩⟩⟩
  invFun i := ⟨i.1, i.2.1, i.2.2.1, i.2.2.2⟩
  left_inv i := by cases i; rfl
  right_inv i := by rcases i with ⟨d, β, z, k⟩; rfl

def uvGenerator (m C rCap : ℕ) (i : UVLabel m C rCap) : Outer K :=
  Polynomial.X ^ i.k.val *
    contactU K ^ (i.d.val - rCap) *
    Polynomial.C (MvPolynomial.X 1) ^ (min i.d.val rCap - i.beta.val) *
    contactV K ^ i.beta.val *
    Polynomial.C (MvPolynomial.X 3) ^ i.z.val

def uvSpanVector (m C rCap : ℕ) (i : UVLabel m C rCap) :
    LowJet K m := lowJet K m (uvGenerator K m C rCap i)

def uvSpan (m C rCap : ℕ) : Submodule K (LowJet K m) :=
  Submodule.span K (Set.range (uvSpanVector K m C rCap))

theorem span_range_finrank_le (m C rCap : ℕ)
    (b : UVLabel m C rCap → LowJet K m) :
    Module.finrank K (Submodule.span K (Set.range b)) ≤
      localUVRankBound m C rCap := by
  calc
    Module.finrank K (Submodule.span K (Set.range b)) ≤
        Fintype.card (UVLabel m C rCap) :=
      finrank_range_le_card (R := K) b
    _ = Fintype.card (UVSpanIndex m C rCap) :=
      Fintype.card_congr (uvLabelEquiv m C rCap)
    _ = localUVRankBound m C rCap := uv_span_index_card m C rCap

section GenericUV

variable {A : Type*} [CommRing A]

 

theorem pow_dvd_uv_product (t u vv r zeta : A) (k l q β z : ℕ)
    (hu : t ∣ u) (hv : t ^ 2 ∣ vv) :
    t ^ (k + l + 2 * β) ∣ t ^ k * u ^ l * r ^ q * vv ^ β * zeta ^ z := by
  have hul : t ^ l ∣ u ^ l := by
    simpa only [pow_mul] using pow_dvd_pow_of_dvd hu l
  have hvβ : t ^ (2 * β) ∣ vv ^ β := by
    simpa only [pow_mul] using pow_dvd_pow_of_dvd hv β
  have hfirst : t ^ (k + l) ∣ t ^ k * u ^ l := by
    simpa only [pow_add] using mul_dvd_mul (dvd_refl (t ^ k)) hul
  have hall : t ^ (k + l + 2 * β) ∣ (t ^ k * u ^ l) * vv ^ β := by
    simpa only [pow_add] using mul_dvd_mul hfirst hvβ
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hall (r ^ q)) (zeta ^ z)

 
theorem sourceGenerator_uv_expansion
    (T R U V : A) (hU : U = V + T * R) (l q v : ℕ) (hv : v ≤ q) :
    U ^ (l + v) * R ^ (q - v) =
      ∑ β ∈ Finset.range (v + 1),
        ((v.choose β : ℕ) : A) * T ^ (v - β) * U ^ l *
          R ^ (q - β) * V ^ β := by
  have hUv : U ^ v = (V + T * R) ^ v := congrArg (fun W : A => W ^ v) hU
  rw [pow_add, hUv, add_pow, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro β hβ
  have hβv : β ≤ v := by
    have := Finset.mem_range.mp hβ
    omega
  simp only [mul_pow]
  have hq : (v - β) + (q - v) = q - β := by omega
  calc
    U ^ l * (V ^ β * (T ^ (v - β) * R ^ (v - β)) *
          ((v.choose β : ℕ) : A)) * R ^ (q - v) =
        ((v.choose β : ℕ) : A) * T ^ (v - β) * U ^ l *
          (R ^ (v - β) * R ^ (q - v)) * V ^ β := by ring
    _ = ((v.choose β : ℕ) : A) * T ^ (v - β) * U ^ l *
          R ^ (q - β) * V ^ β := by rw [← pow_add, hq]

end GenericUV

theorem lowJet_eq_zero_of_X_pow_dvd (m : ℕ) (P : Outer K)
    (hP : (Polynomial.X : Outer K) ^ m ∣ P) : lowJet K m P = 0 := by
  funext j
  exact (Polynomial.X_pow_dvd_iff.mp hP) j.val j.isLt

theorem lowJet_natCast_mul (m n : ℕ) (P : Outer K) :
    lowJet K m (((n : ℕ) : Outer K) * P) =
      (n : K) • lowJet K m P := by
  funext j
  change (Polynomial.C (MvPolynomial.C (n : K)) * P).coeff j.val =
    (n : K) • P.coeff j.val
  rw [Polynomial.coeff_C_mul]
  simp only [MvPolynomial.smul_eq_C_mul]

theorem uvSpanVector_mem (m C rCap : ℕ) (i : UVLabel m C rCap) :
    uvSpanVector K m C rCap i ∈ uvSpan K m C rCap := by
  exact Submodule.subset_span ⟨i, rfl⟩

def centeredGenerator (k y r z : ℕ) : Outer K :=
  Polynomial.X ^ k * contactU K ^ y *
    Polynomial.C (MvPolynomial.X 1) ^ r *
    Polynomial.C (MvPolynomial.X 3) ^ z

 

theorem lowJet_centeredGenerator_mem_uvSpan
    (m C rCap k y r z : ℕ) (hr : r ≤ rCap) (htotal : y + r + z ≤ C) :
    lowJet K m (centeredGenerator K k y r z) ∈ uvSpan K m C rCap := by
  classical
  let d := y + r
  let l := d - rCap
  let q := min d rCap
  let v := y - l
  have hld : l + q = d := by
    dsimp only [l, q]
    exact tsub_add_min
  have hly : l ≤ y := by
    dsimp only [l, d]
    omega
  have hlv : l + v = y := by
    dsimp only [v]
    exact Nat.add_sub_of_le hly
  have hqv : v ≤ q := by
    dsimp only [d] at hld
    omega
  have hqvr : q - v = r := by omega
  have hU : contactU K = contactV K +
      (Polynomial.X : Outer K) * Polynomial.C (MvPolynomial.X 1) := by
    rw [contactU_eq_XR_add_contactV K, add_comm]
  have hexp := sourceGenerator_uv_expansion
    (A := Outer K) Polynomial.X (Polynomial.C (MvPolynomial.X 1))
      (contactU K) (contactV K) hU l q v hqv
  rw [hlv, hqvr] at hexp
  have hpoly : centeredGenerator K k y r z =
      ∑ β ∈ Finset.range (v + 1),
        (((v.choose β : ℕ) : Outer K) *
          (Polynomial.X ^ (k + (v - β)) * contactU K ^ l *
            Polynomial.C (MvPolynomial.X 1) ^ (q - β) * contactV K ^ β *
            Polynomial.C (MvPolynomial.X 3) ^ z)) := by
    calc
      centeredGenerator K k y r z =
          Polynomial.X ^ k *
            (contactU K ^ y * Polynomial.C (MvPolynomial.X 1) ^ r) *
            Polynomial.C (MvPolynomial.X 3) ^ z := by
        simp only [centeredGenerator]
        ring
      _ = Polynomial.X ^ k *
            (∑ β ∈ Finset.range (v + 1),
              (((v.choose β : ℕ) : Outer K) * Polynomial.X ^ (v - β) *
                contactU K ^ l * Polynomial.C (MvPolynomial.X 1) ^ (q - β) *
                contactV K ^ β)) * Polynomial.C (MvPolynomial.X 3) ^ z := by
        rw [hexp]
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro β hβ
        rw [pow_add]
        ring
  rw [hpoly]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro β hβ
  have hβv : β ≤ v := by
    have := Finset.mem_range.mp hβ
    omega
  by_cases hactive : k + (v - β) < m - l - 2 * β
  · have hdC : d < C + 1 := by dsimp only [d]; omega
    have hβq : β < min d rCap + 1 := by dsimp only [q] at hqv; omega
    have hzC : z < C + 1 - d := by dsimp only [d]; omega
    let i : UVLabel m C rCap :=
      { d := ⟨d, hdC⟩
        beta := ⟨β, hβq⟩
        z := ⟨z, hzC⟩
        k := ⟨k + (v - β), by
          dsimp only
          simpa only using hactive⟩ }
    have hi := uvSpanVector_mem K m C rCap i
    have hterm :
        (((v.choose β : ℕ) : Outer K) *
          (Polynomial.X ^ (k + (v - β)) * contactU K ^ l *
            Polynomial.C (MvPolynomial.X 1) ^ (q - β) * contactV K ^ β *
            Polynomial.C (MvPolynomial.X 3) ^ z)) =
        ((v.choose β : ℕ) : Outer K) * uvGenerator K m C rCap i := by
      simp only [uvGenerator, i, l, q, mul_assoc]
    rw [hterm, lowJet_natCast_mul]
    exact Submodule.smul_mem _ _ hi
  · have hval : m ≤ k + (v - β) + l + 2 * β := by omega
    have hbase := pow_dvd_uv_product
      (A := Outer K) Polynomial.X (contactU K) (contactV K)
        (Polynomial.C (MvPolynomial.X 1)) (Polynomial.C (MvPolynomial.X 3))
        (k + (v - β)) l (q - β) β z
        (X_dvd_contactU K) (X_sq_dvd_contactV K)
    have hm : (Polynomial.X : Outer K) ^ m ∣
        (((v.choose β : ℕ) : Outer K) *
          (Polynomial.X ^ (k + (v - β)) * contactU K ^ l *
            Polynomial.C (MvPolynomial.X 1) ^ (q - β) * contactV K ^ β *
            Polynomial.C (MvPolynomial.X 3) ^ z)) := by
      have hsmall : (Polynomial.X : Outer K) ^ m ∣
          Polynomial.X ^ (k + (v - β) + l + 2 * β) :=
        pow_dvd_pow Polynomial.X hval
      have hinner : (Polynomial.X : Outer K) ^ m ∣
          Polynomial.X ^ (k + (v - β)) * contactU K ^ l *
            Polynomial.C (MvPolynomial.X 1) ^ (q - β) * contactV K ^ β *
            Polynomial.C (MvPolynomial.X 3) ^ z :=
        hsmall.trans hbase
      exact dvd_mul_of_dvd_right hinner (((v.choose β : ℕ) : Outer K))
    rw [lowJet_eq_zero_of_X_pow_dvd K m _ hm]
    exact (uvSpan K m C rCap).zero_mem

end

end ProximityPrize.SubmissionLower.ContactSecondContactUVSpan6660Research

#print axioms ProximityPrize.SubmissionLower.ContactSecondContactUVSpan6660Research.span_range_finrank_le
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactUVSpan6660Research.pow_dvd_uv_product
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactUVSpan6660Research.sourceGenerator_uv_expansion
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactUVSpan6660Research.lowJet_centeredGenerator_mem_uvSpan
