import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research

/-! .
 -/

namespace ProximityPrize.SubmissionLower.ContactMovingProjection6676Research

open scoped Classical BigOperators Pointwise
open ContactFlagBezout6543Research

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K

def filteredCut {R : Type*} [CommRing R] (k : ℕ) (B : Fin (k+1) → R)
    (H G : R) : R := ∑ j, B j * H ^ (k-j.val) * G ^ j.val

def movingEquation (H G Q U : Poly) (t : K) : Poly :=
  H * (MvPolynomial.C t - Q) - U * G

def eliminatedCut (k : ℕ) (B : Fin (k+1) → Poly) (Q U : Poly) (t : K) : Poly :=
  filteredCut k B U (MvPolynomial.C t - Q)

theorem map_filteredCut {R S : Type*} [CommRing R] [CommRing S]
    (ev : R →+* S) (k : ℕ) (B : Fin (k+1) → R) (H G : R) :
    ev (filteredCut k B H G) = filteredCut k (fun j ↦ ev (B j)) (ev H) (ev G) := by
  simp [filteredCut]

theorem binary_clearing {R : Type*} [CommRing R] (k : ℕ) (B : Fin (k+1) → R)
    (H G U V : R) (hrel : H * V = U * G) :
    H ^ k * filteredCut k B U V = U ^ k * filteredCut k B H G := by
  unfold filteredCut
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : k-j.val+j.val=k := Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
  have hh : H^k=H^(k-j.val)*H^j.val := by rw [← pow_add, hj]
  have hu : U^k=U^(k-j.val)*U^j.val := by rw [← pow_add, hj]
  calc
    _ = B j * H^(k-j.val) * U^(k-j.val) * (H*V)^j.val := by
      rw [hh, mul_pow]; ring
    _ = B j * H^(k-j.val) * U^(k-j.val) * (U*G)^j.val := by rw [hrel]
    _ = _ := by rw [hu, mul_pow]; ring

theorem clearing_at_equation {R : Type*} [CommRing R] (ev : Poly →+* R)
    (k : ℕ) (B : Fin (k+1) → Poly) (H G Q U : Poly) (t : K)
    (hN : ev (movingEquation H G Q U t) = 0) :
    ev H ^ k * ev (eliminatedCut k B Q U t) =
      ev U ^ k * ev (filteredCut k B H G) := by
  have hrel : ev H * ev (MvPolynomial.C t-Q) = ev U * ev G := by
    simpa [movingEquation, sub_eq_zero] using hN
  simp only [eliminatedCut, map_filteredCut]
  exact binary_clearing k _ _ _ _ _ hrel

theorem eliminatedCut_zero_iff {L : Type*} [Field L] (ev : Poly →+* L)
    (k : ℕ) (B : Fin (k+1) → Poly) (H G Q U : Poly) (t : K)
    (hN : ev (movingEquation H G Q U t)=0) (hH : ev H ≠ 0) (hU : ev U ≠ 0) :
    ev (eliminatedCut k B Q U t)=0 ↔ ev (filteredCut k B H G)=0 := by
  have heq := clearing_at_equation ev k B H G Q U t hN
  constructor
  · intro hz
    rw [hz, mul_zero] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hU)
  · intro hz
    rw [hz, mul_zero] at heq
    exact (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ hH)

/-- .
 -/
theorem original_mem_of_eliminated_mem (P : Ideal Poly) [P.IsPrime]
    (k : ℕ) (B : Fin (k+1) → Poly) (H G Q U : Poly) (t : K)
    (hN : movingEquation H G Q U t ∈ P)
    (hT : eliminatedCut k B Q U t ∈ P) (hU : U ∉ P) :
    filteredCut k B H G ∈ P := by
  let ev := Ideal.Quotient.mk P
  have heq := clearing_at_equation ev k B H G Q U t
    (Ideal.Quotient.eq_zero_iff_mem.mpr hN)
  have hzero : ev (eliminatedCut k B Q U t) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hT
  have hUne : ev U ≠ 0 := fun h ↦ hU (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [hzero, mul_zero] at heq
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    ((mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hUne))

theorem inFlag_const (p : FlagDegree) (c : K) : PolynomialInFlag p (MvPolynomial.C c) := by
  intro d hd
  have hd0 : d=0 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (MvPolynomial.coeff_C_of_ne_zero h _)
  subst d
  exact inFlag_zero p

private theorem flag_eq {p q : FlagDegree} (hx : p.zOnly=q.zOnly)
    (hy : p.yz=q.yz) (hz : p.all=q.all) : p=q := by
  cases p; cases q; simp_all

theorem inFlag_map {E : Type*} [Field E] (f : K →+* E)
    {p : FlagDegree} {A : Poly} (hA : PolynomialInFlag p A) :
    PolynomialInFlag p (MvPolynomial.map f A) := by
  intro d hd
  exact hA d (MvPolynomial.support_map_subset f A hd)

theorem inFlag_add_poly {p : FlagDegree} {A B : Poly}
    (hA : PolynomialInFlag p A) (hB : PolynomialInFlag p B) :
    PolynomialInFlag p (A+B) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hA d h
  · exact hB d h

theorem inFlag_sub_poly {p : FlagDegree} {A B : Poly}
    (hA : PolynomialInFlag p A) (hB : PolynomialInFlag p B) :
    PolynomialInFlag p (A-B) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_sub (Fin 3) A B hd) with h | h
  · exact hA d h
  · exact hB d h

theorem inFlag_mul_poly {p q : FlagDegree} {A B : Poly}
    (hA : PolynomialInFlag p A) (hB : PolynomialInFlag q B) :
    PolynomialInFlag (p+q) (A*B) := by
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul A B hd)
  exact inFlag_add (hA a ha) (hB b hb)

theorem inFlag_pow_poly {p : FlagDegree} {A : Poly} (hA : PolynomialInFlag p A) (k : ℕ) :
    PolynomialInFlag (k • p) (A^k) := by
  induction k with
  | zero => simpa using inFlag_const (0 • p) (1 : K)
  | succ k ih =>
    have heq : (k+1) • p = k • p+p := by
      apply flag_eq <;> simp only [nsmul_zOnly, nsmul_yz, nsmul_all,
        add_zOnly, add_yz, add_all] <;> ring
    rw [pow_succ, heq]
    exact inFlag_mul_poly ih hA

theorem inFlag_sum_poly {ι : Type*} (s : Finset ι) (p : FlagDegree) (A : ι → Poly)
    (hA : ∀ i ∈ s, PolynomialInFlag p (A i)) : PolynomialInFlag p (∑ i ∈ s, A i) := by
  intro d hd
  obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  exact hA i hi d hdi

/-- . -/
theorem eliminatedCut_inFlag (k : ℕ) (B : Fin (k+1) → Poly) (Q U : Poly) (t : K)
    (c : Fin (k+1) → FlagDegree) (P : FlagDegree)
    (hB : ∀ j, PolynomialInFlag (c j) (B j))
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hU : PolynomialInFlag unitYZFlag U)
    (hc : ∀ j, c j+(k-j.val) • unitYZFlag+j.val • (2 • unitAllFlag)=P) :
    PolynomialInFlag P (eliminatedCut k B Q U t) := by
  unfold eliminatedCut filteredCut
  apply inFlag_sum_poly
  intro j _
  rw [← hc j]
  exact inFlag_mul_poly (inFlag_mul_poly (hB j) (inFlag_pow_poly hU _))
    (inFlag_pow_poly (inFlag_sub_poly (inFlag_const _ _) hQ) _)

/-- .
 -/
theorem eliminatedCut_small_flag (a b s k : ℕ) (C : FlagDegree)
    (B : Fin (k+1) → Poly) (Q U : Poly) (t : K)
    (c : Fin (k+1) → FlagDegree)
    (hB : ∀ j, PolynomialInFlag (c j) (B j))
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hU : PolynomialInFlag unitYZFlag U)
    (hc : ∀ j, c j+(k-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree)+
      j.val • (⟨a,b,s+3⟩ : FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩ : FlagDegree)) :
    PolynomialInFlag (C+k • (⟨a,b+1,s+2⟩ : FlagDegree)) (eliminatedCut k B Q U t) := by
  apply eliminatedCut_inFlag k B Q U t c _ hB hQ hU
  intro j
  have hx := congrArg FlagDegree.zOnly (hc j)
  have hy := congrArg FlagDegree.yz (hc j)
  have hz := congrArg FlagDegree.all (hc j)
  have hj : k-j.val+j.val=k := Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
  apply flag_eq
  all_goals simp only [add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz,
    nsmul_all, unitYZFlag, unitAllFlag] at *
  all_goals nlinarith

theorem movingEquation_inFlag (a b s : ℕ) (H G Q U : Poly) (t : K)
    (hH : PolynomialInFlag ⟨a,b+1,s+1⟩ H)
    (hG : PolynomialInFlag ⟨a,b,s+3⟩ G)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hU : PolynomialInFlag unitYZFlag U) :
    PolynomialInFlag ⟨a,b+1,s+3⟩ (movingEquation H G Q U t) := by
  apply inFlag_sub_poly
  · have hc : (⟨a,b+1,s+1⟩ : FlagDegree)+2 • unitAllFlag=⟨a,b+1,s+3⟩ := by
      apply flag_eq
      all_goals simp only [add_zOnly, add_yz, add_all, nsmul_zOnly,
        nsmul_yz, nsmul_all, unitAllFlag]
      omega
    rw [← hc]
    exact inFlag_mul_poly hH (inFlag_sub_poly (inFlag_const _ _) hQ)
  · have hc : unitYZFlag+(⟨a,b,s+3⟩ : FlagDegree)=⟨a,b+1,s+3⟩ := by
      apply flag_eq <;> simp only [add_zOnly, add_yz, add_all, unitYZFlag] <;> omega
    rw [← hc]
    exact inFlag_mul_poly hU hG

theorem small_projection_cap_identity (a b s k : ℕ) (C : FlagDegree) :
    let f : FlagDegree := ⟨a,b+1,s+2⟩
    let h : FlagDegree := ⟨a,b+1,s+1⟩
    let g : FlagDegree := ⟨a,b,s+3⟩
    let D : FlagDegree := ⟨2*a,2*b+1,2*s+3⟩
    let E : FlagDegree := ⟨a,b+1,s+3⟩
    let P := C+k • D
    a*flagMixed f P unitZFlag+b*flagMixed f P unitYZFlag+
      s*flagMixed f P unitAllFlag+flagMixed f E (C+k • f)+k*flagMixed f h g =
      flagMixed f P D+2*k*flagMixed f unitAllFlag unitYZFlag := by
  dsimp only
  simp only [flagMixed, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz,
    nsmul_all, unitZFlag, unitYZFlag, unitAllFlag]
  ring

end
end ProximityPrize.SubmissionLower.ContactMovingProjection6676Research
