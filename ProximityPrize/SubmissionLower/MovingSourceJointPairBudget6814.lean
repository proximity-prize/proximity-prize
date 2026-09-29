import ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814

/-! Keep the two directional pair prices coupled. Their separate maxima
cannot occur together. This saves 2187 units of the U price, without
claiming the false standalone inequality pairU <= 26233. -/
namespace ProximityPrize.SubmissionLower.MovingSourceJointPairBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open RCN095

private theorem oriented (a b x y z v : ℤ)
    (ha : 2≤a) (hb : 2≤b) (hax : a≤x) (hby : b≤y)
    (hz : 0≤z) (hv : 0≤v) (hr : a+b≤31) (hm : x+y≤112)
    (ht : x+y+z+v≤1009) (hdir : 5*b+y≤5*a+x) :
    5*(a*(y+v)+b*(x+z)-a*b)+x*(y+v)+y*z≤230055 := by
  have ha29 : a≤29 := by omega
  have hx110 : x≤110 := by omega
  have hzero : 0≤5*a+x := by omega
  have hmove := mul_le_mul_of_nonneg_left hdir hz
  have htotal := mul_le_mul_of_nonneg_left ht hzero
  have hrem : b≤31-a := by omega
  have hremmul := mul_le_mul_of_nonneg_right hrem (show 0≤x-a by omega)
  have hstep :
      5*(a*(y+v)+b*(x+z)-a*b)+x*(y+v)+y*z≤
        5*a*(978+a-2*x)+x*(1164-x) := by
    nlinarith
  have hxprod : 0≤(110-x)*(1054-10*a-x) :=
    mul_nonneg (by omega) (by omega)
  have haprod : 0≤(29-a)*(787+a) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

theorem joint_pair_bound (p q : FlagDegree)
    (hp : 2≤p.all) (hq : 2≤q.all)
    (hr : p.all+q.all≤31)
    (hy : p.yz+p.all+q.yz+q.all≤112)
    (ht : p.zOnly+p.yz+p.all+q.zOnly+q.yz+q.all≤1009) :
    5*flagMixed p q unitYZFlag+flagMixed p q unitAllFlag≤230055 := by
  have hpq : ∀ p q : FlagDegree, 2≤p.all → 2≤q.all →
      p.all+q.all≤31 → p.yz+p.all+q.yz+q.all≤112 →
      p.zOnly+p.yz+p.all+q.zOnly+q.yz+q.all≤1009 →
      5*(q.all:ℤ)+(q.yz+q.all:ℕ)≤5*(p.all:ℤ)+(p.yz+p.all:ℕ) →
      5*flagMixed p q unitYZFlag+flagMixed p q unitAllFlag≤230055 := by
    intro p q hp hq hr hy ht hd
    have hh := oriented (p.all:ℤ) (q.all:ℤ)
      ((p.yz+p.all:ℕ):ℤ) ((q.yz+q.all:ℕ):ℤ) (p.zOnly:ℤ) (q.zOnly:ℤ)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hd
    simp only [flagMixed,unitYZFlag,unitAllFlag]
    push_cast at hh
    zify
    nlinarith
  rcases le_total (5*(q.all:ℤ)+(q.yz+q.all:ℕ))
      (5*(p.all:ℤ)+(p.yz+p.all:ℕ)) with h | h
  · exact hpq p q hp hq hr hy ht h
  · have hh := hpq q p hq hp (by omega) (by omega) (by omega) h
    simp only [flagMixed,unitYZFlag,unitAllFlag] at hh ⊢
    nlinarith

theorem weighted_joint_bound (u v cu cv : ℕ)
    (hj : 5*u+v≤230055) (hv : v≤98890) (hc : cu≤5*cv) :
    cu*u+cv*v≤cu*26233+cv*98890 := by
  have h1 := Nat.mul_le_mul_left cu hj
  have h2 := Nat.mul_le_mul_left (5*cv-cu) hv
  have h3 := Nat.sub_add_cancel hc
  nlinarith

theorem same_source_weighted_pair_bound {K : Type} [Field K]
    (F : MvPolynomial (Fin 4) K) (S : MovingFiberThreeSources6811.Source F)
    (hS : MovingSourceTwoProfiles6814.Profile S 31 98 995 14 2 3)
    (J D : MvPolynomial (Fin 5) K) (hJ : J≠0) (hD : D≠0)
    (hcop : IsRelPrime J D) (hJP : J∣S.P) (hDP : D∣S.P)
    (hsJ : 0<MovingSourceCoupledClearing6814.order J)
    (hsD : 0<MovingSourceCoupledClearing6814.order D)
    (cu cv : ℕ) (hc : cu≤5*cv) :
    cu*flagMixed (MovingSourceCoupledClearing6814.ordinaryFlag J)
        (MovingSourceCoupledClearing6814.ordinaryFlag D) unitYZFlag+
      cv*flagMixed (MovingSourceCoupledClearing6814.ordinaryFlag J)
        (MovingSourceCoupledClearing6814.ordinaryFlag D) unitAllFlag≤
      cu*26233+cv*98890 := by
  obtain ⟨hj,hd,hb,hu,ht⟩ := MovingSourceSameSourceBudget6814.same_source_flag_budgets
    F S hS J D hJ hD hcop hJP hDP hsJ hsD
  have h := MovingSourceSameSourceBudget6814.same_source_pair_prices
    F S hS J D hJ hD hcop hJP hDP hsJ hsD
  exact weighted_joint_bound _ _ cu cv (joint_pair_bound _ _ hj hd hb hu ht) h.2.2 hc

#print axioms joint_pair_bound
#print axioms same_source_weighted_pair_bound
end
end ProximityPrize.SubmissionLower.MovingSourceJointPairBudget6814
