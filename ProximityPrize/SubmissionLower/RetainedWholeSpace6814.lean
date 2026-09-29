import ProximityPrize.SubmissionLower.MovingFiberProfile6811

/-!
Fully proved extraction from the existing source alternative.
This file uses the compiled 68.13 interface (181265 agreements, 80879
errors). It does not claim that the numerical 68.14 retune is compiled.
No desired new counting inequality is assumed.
-/

namespace ProximityPrize.SubmissionLower.RetainedWholeSpace6814
open scoped Classical
open MvPolynomial RCN095 RCN130 RCN135 RCN146 RCN156 RCN174 RCN222
  RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open MovingFiberRegularData6811 MovingFiberInterpolation6811
  MovingFiberTotalAvoidance6811 MovingFiberProfile6811
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem universal_retention_of_large_packet
    (S : Data nodes u0 u1) (cfg : Params) (hc : cfg.WellFormed)
    (hI : Fintype.card I = 262144)
    (hL : cfg.L < wt residualTotalWeights S.F)
    (hGates : S.PairGates (cfg.B+cfg.s*(S.r-1))
      (cfg.U+cfg.s*(S.y-1)) (cfg.L+cfg.s*(S.t-1)))
    (hlarge : helperCap S cfg < S.seeds.card) :
    ∀ P : SecondJetSupport.Poly (K := K),
      Interpolant cfg.m cfg.B cfg.s cfg.U cfg.L cfg.k cfg.n0 nodes u0 u1 P →
      cfg.n0 ≤ (SecondJetCoefficients.asS P).natDegree ∧
      ∀ d ≤ cfg.k, S.F ∣ SecondJetClearedHelper.helper P S.F (cfg.s-d) d := by
  classical
  intro P hP
  rcases hc with ⟨hsB,hBU,hUL,hks,hsm,hkn,hBn,hschar⟩
  have hf : ∀ d ≤ cfg.s, (d.factorial : K) ≠ 0 := by
    intro d hd
    exact SecondJetOwnShape.factorial_ne d (hd.trans_lt hschar)
  have alt := helper_or_divisibility P S.F cfg.m cfg.B cfg.s cfg.U cfg.L
    cfg.k cfg.n0 S.r S.y S.t nodes u0 u1 hP S.irreducible hL hsB
    (by omega) (by omega) hks hsm
    (by have := S.rpos; omega) (by have := S.ry; have := S.rpos; omega)
    (by have := S.yt; have := S.ry; have := S.rpos; omega) S.weights hf
  rcases alt with ⟨Q,hrel,hw,hzero⟩ | hret
  · have hb : S.seeds.card ≤ helperCap S cfg := by
      apply S.proper_count_left hI Q
        (cfg.B+cfg.s*(S.r-1)) (cfg.U+cfg.s*(S.y-1)) (cfg.L+cfg.s*(S.t-1)) hrel
        (SecondJetPairBounds.degree_caps_of_weights Q _ _ _ hw) hGates
      intro gamma hgamma
      apply hzero (S.selected gamma) (S.degree gamma hgamma) gamma
        (Finset.univ.filter (fun i =>
          (S.selected gamma).eval (nodes i) = u0 i+gamma*u1 i))
        (S.agreement gamma hgamma) _ (S.solution gamma hgamma)
      intro i hi
      simpa only [mul_comm] using (Finset.mem_filter.mp hi).2
    exact False.elim ((Nat.not_lt_of_ge hb) hlarge)
  · exact hret

#print axioms universal_retention_of_large_packet

theorem every_interpolant_has_common_root_power
    (S : Data nodes u0 u1) (cfg : Params) (hc : cfg.WellFormed)
    (hI : Fintype.card I = 262144)
    (hL : cfg.L < wt residualTotalWeights S.F)
    (hGates : S.PairGates (cfg.B+cfg.s*(S.r-1))
      (cfg.U+cfg.s*(S.y-1)) (cfg.L+cfg.s*(S.t-1)))
    (hlarge : helperCap S cfg < S.seeds.card)
    {E : Type} [Field E] [CharP E 2130706433]
    (phi : MvPolynomial (Fin 4) K →+* E)
    (hF : phi S.F = 0)
    (hH : phi (2*RCN313.polyH K S.F) ≠ 0) :
    ∀ P : SecondJetSupport.Poly (K := K),
      Interpolant cfg.m cfg.B cfg.s cfg.U cfg.L cfg.k cfg.n0 nodes u0 u1 P →
      (Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio phi S.F))^(cfg.k+1) ∣
        (SecondJetCoefficients.asS P).map phi := by
  classical
  intro P hP
  by_cases hz : (SecondJetCoefficients.asS P).map phi = 0
  · rw [hz]
    exact dvd_zero _
  have hret := universal_retention_of_large_packet S cfg hc hI hL hGates hlarge P hP
  have hf : (cfg.k.factorial : E) ≠ 0 := by
    apply SecondJetOwnShape.factorial_ne
    rcases hc with ⟨_,_,_,hks,_,_,_,hschar⟩
    omega
  exact SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd P S.F phi cfg.s cfg.k
    (fun e he => ((hP.2.1 e he).2.1)) hF hH hz hf hret.2

#print axioms every_interpolant_has_common_root_power

/-- Cross-multiplied curvature reduction for a parameter pencil. All symbols
are scalars here; in the application da,db are the code/contact derivatives
of a,b and ar,br are their slope partials. -/
theorem parameter_pencil_cross_identity
    {E : Type} [CommRing E] (a b ar br da db p q : E) :
    (a*br-b*ar)*(-da*q-db*p)-(b*da-a*db)*(ar*q+br*p) =
      (ar*db-br*da)*(a*q+b*p) := by
  ring

theorem parameter_pencil_cross_eq_of_relation
    {E : Type} [CommRing E] (a b ar br da db p q : E)
    (h : a*q+b*p=0) :
    (a*br-b*ar)*(-da*q-db*p)=(b*da-a*db)*(ar*q+br*p) := by
  apply sub_eq_zero.mp
  rw [parameter_pencil_cross_identity,h,mul_zero]

#print axioms parameter_pencil_cross_eq_of_relation

/-- A regular point can lose the unreduced pencil denominator only on
the coefficient base locus. This is the exceptional set paid in the count. -/
theorem parameter_pencil_denominator_ne
    {E : Type} [Field E] (a b ar br p q : E)
    (hF : a*q+b*p=0) (hreg : ar*q+br*p≠0)
    (hbase : a≠0 ∨ b≠0) : a*br-b*ar≠0 := by
  intro hz
  have ha : a*(ar*q+br*p)=0 := by
    calc
      _ = (a*br-b*ar)*p+ar*(a*q+b*p) := by ring
      _ = 0 := by rw [hz,hF]; ring
  have hb : b*(ar*q+br*p)=0 := by
    calc
      _ = br*(a*q+b*p)-(a*br-b*ar)*q := by ring
      _ = 0 := by rw [hz,hF]; ring
  rcases hbase with h | h
  · exact h ((mul_eq_zero.mp ha).resolve_right hreg)
  · exact h ((mul_eq_zero.mp hb).resolve_right hreg)

#print axioms parameter_pencil_denominator_ne

/-- Plane trapezoid cost in the nonnegative coordinates u=A-B, v=B.
This is the proper intersection of a tail factor with its flow derivative.
It is not a bound for arbitrary mixed-parameter factors. -/
def descendedPlaneCost (u v : ℕ) : ℕ :=
  2*u*v+v*v+6*u+24*v

theorem descendedPlaneCost_superadditive (u v u' v' : ℕ) :
    descendedPlaneCost u v + descendedPlaneCost u' v' ≤
      descendedPlaneCost (u+u') (v+v') := by
  dsimp [descendedPlaneCost]
  nlinarith

/-- Raise actual total degree and R degree, rather than subtracting two
independent caps to invent a bound on the sum of flag differences. -/
theorem descendedPlaneCost_le_of_cumulative
    (u v u' v' : ℕ) (ha : u+v ≤ u'+v') (hb : v ≤ v') :
    descendedPlaneCost u v ≤ descendedPlaneCost u' v' := by
  have h1 := Nat.mul_le_mul_right (2*v+6) ha
  have h2 : 0 ≤ (v'-v)*(2*u'+(v'-v)+18) := Nat.zero_le _
  have hsub := Nat.sub_add_cancel hb
  dsimp [descendedPlaneCost]
  nlinarith

theorem descended_plane_budget_fits :
    3561 * descendedPlaneCost (6291385-1441777) 1441777 +
      99009360 + 28462081871526 = 57228417618936663 ∧
      57228417618936663 < 72000000000000000 := by
  norm_num [descendedPlaneCost]

#print axioms descendedPlaneCost_le_of_cumulative
#print axioms descended_plane_budget_fits

/-- Looser rectangle count: it avoids needing a new mixed-volume endpoint. -/
def descendedRectCost (a b : ℕ) : ℕ := 2*a*b+6*a+24*b

theorem descendedRectCost_superadditive (a b a' b' : ℕ) :
    descendedRectCost a b + descendedRectCost a' b' ≤
      descendedRectCost (a+a') (b+b') := by
  dsimp [descendedRectCost]
  nlinarith

theorem descended_conservative_budget_fits :
    3561 * descendedRectCost 6291385 1441777 +
      (2*57*12+24*7+25*5)*80890 +
      80890*(21937127424+351141900) = 66405209671072778 ∧
      66405209671072778 < 72000000000000000 := by
  norm_num [descendedRectCost]

#print axioms descended_conservative_budget_fits

end
end ProximityPrize.SubmissionLower.RetainedWholeSpace6814
