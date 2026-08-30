import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower
open Polynomial
open Polynomial.Bivariate
variable {F:Type} [Field F]
theorem bivariate_resultant_eval (B H:F[X][Y]) (n m:ℕ) (z:F):
    (Polynomial.resultant B H n m).eval z=
      Polynomial.resultant (B.map (Polynomial.evalRingHom z))
        (H.map (Polynomial.evalRingHom z)) n m:=by
  simp
theorem bivariate_resultant_eval_fixed_original_degrees (B H:F[X][Y]) (z:F):
    (Polynomial.resultant B H).eval z=
      Polynomial.resultant (B.map (Polynomial.evalRingHom z))
        (H.map (Polynomial.evalRingHom z)) B.natDegree H.natDegree:=by
  exact bivariate_resultant_eval B H B.natDegree H.natDegree z
theorem resultant_eq_zero_of_common_root {p q:F[X]} {t:F}
    (hne:p≠0∨q≠0) (hp:p.eval t=0) (hq:q.eval t=0):
    Polynomial.resultant p q=0:=by
  rw [Polynomial.resultant_eq_zero_iff]
  refine ⟨hne,?_⟩
  rintro ⟨a,b,hab⟩
  have heval:=congrArg (fun r:F[X] => r.eval t) hab
  simp [Polynomial.eval_add,Polynomial.eval_mul,hp,hq] at heval
theorem resultant_fixed_degree_eq_zero_of_common_root_of_monic_right
    {p q:F[X]} {m n:ℕ} {t:F}
    (hpdeg:p.natDegree ≤ m) (hqmonic:q.Monic) (hqdeg:q.natDegree=n)
    (hp:p.eval t=0) (hq:q.eval t=0):
    Polynomial.resultant p q m n=0:=by
  have hstd:Polynomial.resultant p q=0:=
    resultant_eq_zero_of_common_root (Or.inr hqmonic.ne_zero) hp hq
  have hm:p.natDegree+(m-p.natDegree)=m:=Nat.add_sub_of_le hpdeg
  rw [←hm, ←hqdeg]
  rw [Polynomial.resultant_add_left_deg]
  · simp [hstd]
  · exact le_rfl
theorem resultant_fixed_degree_eq_zero_of_common_root
    {p q:F[X]} {m n:ℕ} {t:F}
    (hpdeg:p.natDegree ≤ m) (hqdeg:q.natDegree ≤ n)
    (hsize:0 < m+n) (hp:p.eval t=0) (hq:q.eval t=0):
    Polynomial.resultant p q m n=0:=by
  by_cases hne:p≠0∨q≠0
  · have hstd:Polynomial.resultant p q=0:=
      resultant_eq_zero_of_common_root hne hp hq
    have hm:p.natDegree+(m-p.natDegree)=m:=Nat.add_sub_of_le hpdeg
    have hn:q.natDegree+(n-q.natDegree)=n:=Nat.add_sub_of_le hqdeg
    rw [←hm, ←hn]
    rw [Polynomial.resultant_add_left_deg]
    · rw [Polynomial.resultant_add_right_deg]
      · simp [hstd]
      · exact le_rfl
    · exact le_rfl
  · push Not at hne
    rcases hne with ⟨rfl,rfl⟩
    rcases m with _ | m <;> rcases n with _ | n <;> simp_all
theorem bivariate_resultant_eval_eq_zero_of_common_root
    (B H:F[X][Y]) (n m:ℕ) (z t:F)
    (hBdeg:(B.map (Polynomial.evalRingHom z)).natDegree ≤ n)
    (hHdeg:(H.map (Polynomial.evalRingHom z)).natDegree ≤ m)
    (hsize:0 < n+m)
    (hBroot:(B.map (Polynomial.evalRingHom z)).eval t=0)
    (hHroot:(H.map (Polynomial.evalRingHom z)).eval t=0):
    (Polynomial.resultant B H n m).eval z=0:=by
  rw [bivariate_resultant_eval]
  exact resultant_fixed_degree_eq_zero_of_common_root hBdeg hHdeg hsize hBroot hHroot
theorem bivariate_resultant_eval_eq_zero_of_common_root_original_degrees
    (B H:F[X][Y]) (z t:F)
    (hsize:0 < B.natDegree+H.natDegree)
    (hBroot:(B.map (Polynomial.evalRingHom z)).eval t=0)
    (hHroot:(H.map (Polynomial.evalRingHom z)).eval t=0):
    (Polynomial.resultant B H).eval z=0:=by
  rw [bivariate_resultant_eval_fixed_original_degrees]
  exact resultant_fixed_degree_eq_zero_of_common_root
    Polynomial.natDegree_map_le Polynomial.natDegree_map_le hsize hBroot hHroot
theorem bivariate_resultant_natDegree_le (B H:F[X][Y]) (n m:ℕ):
    (Polynomial.resultant B H n m).natDegree ≤
      m*degreeX B+n*degreeX H:=by
  exact ps_nat_degree_resultant_le H B m n
theorem bivariate_resultant_natDegree_le_of_declared_Y_degrees
    (B H:F[X][Y]) (n m:ℕ)
    (hBY:B.natDegree=n) (hHY:H.natDegree=m):
    (Polynomial.resultant B H).natDegree ≤
      m*degreeX B+n*degreeX H:=by
  simpa [hBY,hHY] using bivariate_resultant_natDegree_le B H n m
theorem irreducible_dvd_of_resultant_eq_zero
    (B H:F[X][Y]) (hHmonic:H.Monic) (hHirreducible:Irreducible H)
    (hres:Polynomial.resultant B H=0):H∣B:=by
  classical
  let K:=FractionRing F[X]
  let f:F[X] →+*K:=algebraMap F[X] K
  have hf:Function.Injective f:=IsFractionRing.injective F[X] K
  have hBdeg:(B.map f).natDegree=B.natDegree:=
    Polynomial.natDegree_map_eq_of_injective hf B
  have hHdeg:(H.map f).natDegree=H.natDegree:=
    Polynomial.natDegree_map_eq_of_injective hf H
  have hresFixed:
      Polynomial.resultant (B.map f) (H.map f) B.natDegree H.natDegree=0:=by
    rw [Polynomial.resultant_map_map]
    rw [hres]
    exact map_zero f
  have hresK:Polynomial.resultant (B.map f) (H.map f)=0:=by
    simpa only [hBdeg,hHdeg] using hresFixed
  have hnotCoprime:¬ IsCoprime (B.map f) (H.map f):=
    (Polynomial.resultant_eq_zero_iff.mp hresK).2
  have hHirreducibleK:Irreducible (H.map f):=by
    exact (hHmonic.irreducible_iff_irreducible_map_fraction_map).mp hHirreducible
  have hdvdK:H.map f∣B.map f:=
    (Irreducible.dvd_iff_not_isCoprime hHirreducibleK).2 fun hc =>
      hnotCoprime hc.symm
  exact hHmonic.isPrimitive.dvd_of_fraction_map_dvd_fraction_map hdvdK
theorem irreducible_dvd_of_many_bivariate_common_roots
    (B H:F[X][Y]) (n m:ℕ) (S:Finset F) (t:F → F)
    (hBY:B.natDegree=n) (hHY:H.natDegree=m)
    (hHmonic:H.Monic) (hHirreducible:Irreducible H)
    (hmany:m*degreeX B+n*degreeX H < S.card)
    (hroots:∀ z∈S,
      (B.map (Polynomial.evalRingHom z)).eval (t z)=0∧
      (H.map (Polynomial.evalRingHom z)).eval (t z)=0):
    H∣B:=by
  let R:F[X]:=Polynomial.resultant B H n m
  have hReval:∀ z∈S,R.eval z=0:=by
    intro z hz
    rw [bivariate_resultant_eval]
    exact resultant_fixed_degree_eq_zero_of_common_root_of_monic_right
      (Polynomial.natDegree_map_le.trans hBY.le)
      (hHmonic.map (Polynomial.evalRingHom z))
      ((hHmonic.natDegree_map (Polynomial.evalRingHom z)).trans hHY)
      (hroots z hz).1 (hroots z hz).2
  have hRdeg:R.natDegree ≤ m*degreeX B+n*degreeX H:=by
    exact bivariate_resultant_natDegree_le B H n m
  have hRzero:R=0:=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R S hReval
      (hRdeg.trans_lt hmany)
  apply irreducible_dvd_of_resultant_eq_zero B H hHmonic hHirreducible
  simpa only [R,hBY,hHY] using hRzero
theorem quotient_mk_eq_zero_of_many_bivariate_common_roots
    (B H:F[X][Y]) (n m:ℕ) (S:Finset F) (t:F → F)
    (hBY:B.natDegree=n) (hHY:H.natDegree=m)
    (hHmonic:H.Monic) (hHirreducible:Irreducible H)
    (hmany:m*degreeX B+n*degreeX H < S.card)
    (hroots:∀ z∈S,
      (B.map (Polynomial.evalRingHom z)).eval (t z)=0∧
      (H.map (Polynomial.evalRingHom z)).eval (t z)=0):
    Ideal.Quotient.mk (Ideal.span {H}) B=0:=by
  rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]
  exact irreducible_dvd_of_many_bivariate_common_roots B H n m S t hBY hHY
    hHmonic hHirreducible hmany hroots
theorem exists_common_specialization_eval_C_ne_zero
    [Fintype F] {ρ:Type} [DecidableEq ρ]
    (S:Finset ρ) (p:ρ → F[X][Y])
    (hp:∀ r∈S,p r≠0)
    (hdeg:(∑ r∈S,(p r).natDegree) < Fintype.card F):
    ∃ x₀:F,∀ r∈S,Polynomial.eval (Polynomial.C x₀) (p r)≠0:=by
  classical
  let P:F[X][Y]:=∏ r∈S,p r
  have hPne:P≠0:=by
    change (∏ r∈S,p r)≠0
    rw [Finset.prod_ne_zero_iff]
    exact hp
  have hPdeg:P.natDegree < Fintype.card F:=by
    exact (Polynomial.natDegree_prod_le S p).trans_lt hdeg
  by_contra hgood
  push Not at hgood
  have hPeval:∀ x:F,P.eval (Polynomial.C x)=0:=by
    intro x
    obtain ⟨r,hrS,hrzero⟩:=hgood x
    change Polynomial.eval (Polynomial.C x) (∏ r∈S,p r)=0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hrS hrzero
  have hPzero:P=0:=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      P Polynomial.C_injective hPeval hPdeg
  exact hPne hPzero
theorem exists_common_specialization_eval_C_ne_zero_univ
    [Fintype F] {ρ:Type} [Fintype ρ] [DecidableEq ρ]
    (p:ρ → F[X][Y]) (hp:∀ r,p r≠0)
    (hdeg:(∑ r,(p r).natDegree) < Fintype.card F):
    ∃ x₀:F,∀ r,Polynomial.eval (Polynomial.C x₀) (p r)≠0:=by
  simpa only [Finset.mem_univ,forall_const] using
    exists_common_specialization_eval_C_ne_zero (F:=F) Finset.univ p
      (fun r _ => hp r) hdeg
end ProximityPrize.SubmissionLower
