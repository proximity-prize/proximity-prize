import ProximityPrize.SubmissionLower.R6966ProofNativeAffineTariff
import ProximityPrize.SubmissionLower.R6966ProofNativeAffineLedger
import ProximityPrize.SubmissionLower.High6966KnownRows

set_option Elab.async false

namespace Research6966.NearAffineHelper
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet FX Equation Seeds atX graphEval jetAt)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (SeedField SeedClosure Surface fibreRow)
open PadeNativeQuotient (Native)
open Lower6960.Rescue6966 (Model Family)
noncomputable section
set_option maxHeartbeats 850000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

private def φ := algebraMap Seeds SeedField
def graph (H:Jet) : Pade.Row SeedField := ⟨(H.coeff 1).map φ,-(H.coeff 0).map φ⟩

theorem graph_data {H:Jet} (ir:Irreducible H) (slope:H.natDegree=1) (deg:jetDegree H=1) :
    (graph H).primitive ∧ (graph H).graphDegree=1 ∧ ∃ N:Native (graph H), N.poly=H := by
  have hn:H.coeff 1≠0:=by rw [←slope,coeff_natDegree];exact leadingCoeff_ne_zero.mpr ir.ne_zero
  have cap (j:ℕ) (nz:H.coeff j≠0) : (H.coeff j).natDegree+j≤1 := by
    have node:(H.coeff j).coeff (H.coeff j).natDegree≠0:=by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr nz
    exact ((K1_14_2_2_2_1.jetDegree_le H 1).mp deg.le) _ _ node
  have an:(graph H).a≠0 := (Polynomial.map_ne_zero_iff (IsFractionRing.injective Seeds SeedField)).mpr hn
  have ad:(graph H).a.natDegree=0 := by
    have := cap 1 hn
    change ((H.coeff 1).map φ).natDegree=0
    rw [natDegree_map_eq_of_injective (show Function.Injective φ from IsFractionRing.injective Seeds SeedField)]
    omega
  have bd:(graph H).b.natDegree≤1 := by
    change (-(H.coeff 0).map φ).natDegree≤1
    rw [natDegree_neg]
    apply natDegree_map_le.trans
    by_cases zero:H.coeff 0=0
    · simp [zero]
    · simpa using cap 0 zero
  have cop:IsCoprime (graph H).a (graph H).b:=by
    have eq:=eq_C_of_natDegree_eq_zero ad
    have nz:(graph H).a.coeff 0≠0:=fun zero=>an (by rw [eq,zero,map_zero])
    refine ⟨C ((graph H).a.coeff 0)⁻¹,0,?_⟩
    conv_lhs => enter [1,2];rw [eq]
    simp [←Polynomial.C_mul,nz]
  refine ⟨⟨an,cop⟩,?_,?_⟩
  · unfold Pade.Row.graphDegree;rw [ad];omega
  · refine ⟨⟨H,ir.isPrimitive (by omega),1,one_ne_zero,?_⟩,rfl⟩
    let f:=algebraMap SeedField SeedClosure
    have comp (Q:Equation) : (Q.map φ).map f=Q.map K1_14_3.seedGeneric := by
      rw [Polynomial.map_map];rfl
    unfold Pade.Row.polynomial Pade.Row.map graph
    simp only [K1_14_1.jetConstant,map_one,one_mul,map_neg,map_neg,sub_neg_eq_add]
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one slope.le]
    simp [fibreRow,comp,f,φ,Polynomial.map_map,K1_14_3.seedGeneric]

private def point (z:K) (S:K[X]) : Jet →+* FX :=
  eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)

theorem helper_bound {u deleted} {M:Model u deleted} {Γ T:Finset K}
    (F:Family M Γ) (sub:T⊆Γ) (hi:M.overhead.toNat≤2499)
    {H:Jet} (ir:Irreducible H) (slope:H.natDegree=1) (degree:jetDegree H=1)
    (w:ℕ) (wp:0<w) (wide:seedDegree H≤w) (small:w<p)
    (zero:∀ γ∈T,jetAt H (M.label γ) (F.scalar γ)=0) :
    T.card ≤ p*w+(3*(133570*w)^2*(262144-133570)^3)/(179769-133570)^3 := by
  classical
  obtain ⟨gp,d,model,eq⟩:=graph_data ir slope degree
  let q (γ:K) : Surface := ⟨RingHom.ker (point (M.label γ) (F.scalar γ)), RingHom.ker_isPrime _⟩
  have own:NativeAffineRows.Owned F T (T.image q) model := by
    intro z hz
    refine ⟨q z,mem_image.mpr ⟨z,hz,rfl⟩,?_,fun _ h=>h⟩
    rw [eq]
    exact zero z hz
  have cap j i : (model.poly.coeff j).coeff i ∈ MvPolynomial.restrictWeightAtMost (fun _=>1) w := by
    rw [eq]
    apply MvPolynomial.mem_restrictWeightAtMost.mpr
    intro m hm
    rw [← Finsupp.degree_eq_weight_one]
    exact (MvPolynomial.le_totalDegree hm).trans ((K1_14_2_2_2_1.seedDegree_le H w).mp wide j i)
  exact NativeAffineTariff.price_floor F sub model gp d w wp cap small 133570 (by omega)
    (by decide) (by decide) (by decide) (by decide) own

end
end Research6966.NearAffineHelper
