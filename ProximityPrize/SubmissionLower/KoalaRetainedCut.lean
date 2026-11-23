import ProximityPrize.SubmissionLower.PortLowBase
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

set_option autoImplicit false
set_option Elab.async false

namespace KoalaRetainedCut
noncomputable section

open K1_13 (Row Geom Shape shape InBox jet shiftJet atJet OrderAt indexDegree)
open MvPolynomial
open scoped Polynomial

/-- Total Taylor order at the jet of the specified scalar polynomial. -/
def contactOrder (P : Row 4) (S : Geom[X]) : ℕ∞ :=
  ((shiftJet P S:Row 4):MvPowerSeries (Fin 4) Geom[X]).order

theorem orderAt_iff {P : Row 4} {S : Geom[X]} {d : ℕ} :
    OrderAt P S d↔(d:ℕ∞)≤contactOrder P S:=by
  constructor
  · intro h
    apply MvPowerSeries.nat_le_order
    intro m hm
    rw [MvPolynomial.coeff_coe]
    by_contra hnon
    have hle:=h m (MvPolynomial.mem_support_iff.mpr hnon)
    change d≤Finsupp.degree m at hle
    exact (Nat.not_lt_of_ge hle hm)
  · intro h m hm
    have he : MvPowerSeries.coeff m ((shiftJet P S : Row 4) :
        MvPowerSeries (Fin 4) Geom[X])≠0:=by
      rw [MvPolynomial.coeff_coe]
      exact MvPolynomial.mem_support_iff.mp hm
    exact_mod_cast h.trans (MvPowerSeries.order_le he)

private def shifting (S : Geom[X]) : Row 4 →+* Row 4 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i+MvPolynomial.C (jet S i))

theorem contactOrder_mul (H G : Row 4) (S : Geom[X]) :
    contactOrder (H*G) S=contactOrder H S+contactOrder G S:=by
  unfold contactOrder
  change ((shifting S (H*G):Row 4):MvPowerSeries (Fin 4) Geom[X]).order=_
  rw [map_mul,MvPolynomial.coe_mul,MvPowerSeries.order_mul]
  rfl

theorem contactOrder_off {H : Row 4} {S : Geom[X]} (h : atJet H S ≠ 0) :
    contactOrder H S=0:=by
  have het : (shiftJet H S).coeff 0 = atJet H S := by
    change (MvPolynomial.constantCoeff.comp (shifting S)) H=MvPolynomial.eval (jet S) H
    congr 1
    ext <;> simp [shifting]
  have hc : MvPowerSeries.coeff 0 ((shiftJet H S : Row 4) :
      MvPowerSeries (Fin 4) Geom[X])≠0:=by simpa only [MvPolynomial.coeff_coe,het] using h
  change ((shiftJet H S:Row 4):MvPowerSeries (Fin 4) Geom[X]).order=0
  exact le_bot_iff.mp (by simpa using MvPowerSeries.order_le hc)

theorem contactOrder_pow (H : Row 4) (S : Geom[X]) (v : ℕ) :
    contactOrder (H^v) S=v*contactOrder H S:=by
  induction v with
  | zero =>
    rw [pow_zero,Nat.cast_zero,zero_mul,contactOrder_off]
    simp [atJet]
  | succ v ih =>
    rw [pow_succ,contactOrder_mul,ih,Nat.cast_succ,add_mul,one_mul]

/-- At a scalar with Taylor multiplicity at most e, division costs at most e per factor. -/
theorem orderAt_quotient {H G : Row 4} {S : Geom[X]} {v e k : ℕ}
    (he:contactOrder H S≤(e:ℕ∞)) (h:OrderAt (H^v*G) S k) :
    OrderAt G S (k-v*e):=by
  rw [orderAt_iff,contactOrder_mul,contactOrder_pow] at h
  rw [orderAt_iff]
  have hle:=h.trans (add_le_add_left (mul_le_mul_right he (v:ℕ∞)) _)
  by_cases htop:contactOrder G S = ⊤
  · simp [htop]
  · obtain ⟨g,hg⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hg] at hle ⊢
    have hk:k≤v*e+g:=by exact_mod_cast hle
    exact_mod_cast (by omega:k-v*e≤g)

theorem orderAt_off_quotient {H G : Row 4} {S : Geom[X]} {v k : ℕ}
    (hoff:atJet H S≠0) (h:OrderAt (H^v*G) S k):OrderAt G S k:=by
  simpa using orderAt_quotient (e:=0) (le_of_eq (contactOrder_off hoff)) h

#print axioms orderAt_quotient
#print axioms orderAt_off_quotient

end
end KoalaRetainedCut
