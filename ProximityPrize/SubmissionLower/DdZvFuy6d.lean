import ProximityPrize.SubmissionLower.DdZkuTDfa
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit true
namespace P5_8_3
noncomputable section
open i4 P5_8 PolynomialDifferential MvPolynomial Finset ReedSolomon.HiddenDerivative
open scoped Polynomial BigOperators




def c3:Prop :=
  ∀ (F R:Equation) (l:ℕ),Irreducible F→0<jetTotalDegree F →
    jetTotalDegree F≤ smallCaps.B→R∈nativeBand donorCaps →
    (∀ (i:Fin 3) (r :ℕ),r<l→F∣jetDerivative R i r)→F^l∣R
def c4 :Prop :=
 ∀ (Q P:Equation),Q≠0→P≠0→Nonempty (CommonData Q P)
def c5:Prop :=
 ∀ (L R:Equation),IsRelPrime L R→ IsRelPrime (apQ.initial L) (apQ.initial R)
def c7:Prop :=
 ∀ s :Jn,Module.finrank K (symbolBand s)≤aMt s
set_option maxHeartbeats 400000
theorem mem_rows {w:Node→K} {T:ℕ} {R:Equation} :
  R∈rows w T↔R∈nativeBand donorCaps∧differentialWeightedDegree N R≤T ∧
    ∀ i,SatisfiesLocalConstraints bo8.m (node i) (w i) R:= by
 simp only [rows,Submodule.mem_inf,mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
  Submodule.mem_iInf,LinearMap.mem_ker,differentialWeightedDegree,SatisfiesLocalConstraints,
  and_assoc]
theorem derivative_band {s :Jn} {R:Equation} (hR:R∈nativeBand s)
  (i:Fin 3) (r :ℕ) :jetDerivative R i r∈nativeBand s := by
 obtain ⟨hB,hJ,hC⟩:=mem_nativeBand.mp hR
 have hi (r :ℕ) : (jetDerivative R i r).weightedTotalDegree indexWeight≤R.weightedTotalDegree indexWeight:= by
  induction r with
  | zero=>rw [jetDerivative_zero]
  | succ r ih =>
    rw [jetDerivative_succ,separant]
    exact (weightedTotalDegree_pderiv_le _ _ _).trans ih
 exact mem_nativeBand.mpr
  ⟨(jetTotalDegree_jetDerivative_le_sub R i r).trans ((Nat.sub_le _ _).trans hB),
    (hi r).trans hJ,(jetDegree_jetDerivative_le R i _ r).trans hC⟩
theorem initial_mul (Q P:Equation) :
  apQ.initial (Q*P)=apQ.initial Q*apQ.initial P:= by
 simp only [apQ.b6h,map_mul]
end
end P5_8_3
