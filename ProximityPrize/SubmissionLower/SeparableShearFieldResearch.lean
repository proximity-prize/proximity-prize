import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CharacteristicFreeInseparableDichotomyResearch
namespace ProximityPrize.SubmissionLower.SeparableShearFieldResearch
open scoped Classical
noncomputable section
theorem add_not_mem_frobenius_range_of_mem_not_mem
    (L:Type*) [Field L] (p:ℕ) [ExpChar L p]
    {r z:L} (hr:r∈(frobenius L p).range)
    (hz:z∉(frobenius L p).range):
    r+z∉(frobenius L p).range:=by
  intro hrs
  apply hz
  have hsub:(r+z)-r∈(frobenius L p).range:=
    Subring.sub_mem (frobenius L p).range hrs hr
  simpa only [add_sub_cancel_left] using hsub
theorem pow_prime_mem_base_of_pure_degree_prime
    (F E:Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsPurelyInseparable F E]
    (p:ℕ) [ExpChar F p] (hp:p.Prime)
    (hdegree:Module.finrank F E=p) (x:E):
    x^p∈(algebraMap F E).range:=by
  obtain ⟨n,y,hmin⟩:=
    IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p x
  have hmin_degree:(minpoly F x).natDegree=p^n:=by
    rw [hmin,Polynomial.natDegree_sub_C,Polynomial.natDegree_X_pow]
  have hpow_le:p^n ≤ p:=by
    calc
      p^n=(minpoly F x).natDegree:=hmin_degree.symm
      _ ≤ Module.finrank F E:=minpoly.natDegree_le x
      _=p:=hdegree
  have hn_le:n ≤ 1:=by
    apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
    simpa only [pow_one] using hpow_le
  have hrel:x^p^n=algebraMap F E y:=by
    have hroot:=minpoly.aeval F x
    rw [hmin,map_sub,Polynomial.aeval_X_pow,Polynomial.aeval_C,
      sub_eq_zero] at hroot
    exact hroot
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn_le with rfl | rfl
  · have hx:x∈(algebraMap F E).range:=by
      refine ⟨y,?_⟩
      simpa only [pow_zero,pow_one] using hrel.symm
    exact Subring.pow_mem (algebraMap F E).range hx p
  · exact ⟨y,by simpa only [pow_one] using hrel.symm⟩
theorem separating_add_of_differential_criterion
    (K L:Type*) [Field K] [Field L] [Algebra K L]
    (D:Derivation K L L) (Separating:L → Prop)
    (hcriterion:∀ f,Separating f ↔ D f≠0)
    {r z:L} (hr:¬ Separating r) (hz:Separating z):
    Separating (r+z):=by
  rw [hcriterion]
  have hDr:D r=0:=by
    by_contra hne
    exact hr ((hcriterion r).mpr hne)
  have hDz:D z≠0:=(hcriterion z).mp hz
  rw [map_add,hDr,zero_add]
  exact hDz
theorem sheared_box_cost_le_old_add_two_penalty
    (cY cR cZ dY dR dZ dS:ℕ) (hS:dS ≤ dR+dZ):
    cY*dY+cR*dS+(cZ+cR)*dZ ≤
      (cY*dY+cR*dR+cZ*dZ)+2*cR*dZ:=by
  calc
    cY*dY+cR*dS+(cZ+cR)*dZ ≤
        cY*dY+cR*(dR+dZ)+(cZ+cR)*dZ:=by
          exact Nat.add_le_add_right
            (Nat.add_le_add_left (Nat.mul_le_mul_left cR hS) (cY*dY))
            ((cZ+cR)*dZ)
    _=(cY*dY+cR*dR+cZ*dZ)+2*cR*dZ:=by
      ring
end
end ProximityPrize.SubmissionLower.SeparableShearFieldResearch
