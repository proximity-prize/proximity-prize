import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.J
import ProximityPrize.SubmissionLower.FS
import ProximityPrize.SubmissionLower.BT
import ProximityPrize.SubmissionLower.P4
namespace ProximityPrize.SubmissionLower.RCN068
open scoped Classical
open RCN051 RCN313 RCN136 RCN174
open RCN231 RCN238
open RCN289
noncomputable section
def capAt (v:DegreeVector):Fin 3 → ℕ:=![v.y,v.r,v.z]
def numeratorCaps (ell s L b:ℕ):DegreeVector:=
 ⟨1+2*b*ell,b*(2*s-1),2*b*L⟩
def agreementCaps (ell s L w:ℕ):DegreeVector:=
 ⟨1+2*w*ell,w*(2*s-1),2*w*L+1⟩
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def HasCaps (Q:MvPolynomial (Fin 3) Ω) (v:DegreeVector):Prop:=
 ∀ i,Q.degreeOf i ≤ capAt v i
variable (φ:Polynomial K →+*Ω)
def firstTailSurface (F:MvPolynomial (Fin 4) K) (w:ℕ):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (numerator K F (w+1))
theorem surface_numerator_caps
   (F:MvPolynomial (Fin 4) K) (ell s L:ℕ) (hs:1 ≤ s)
   (hY:F.degreeOf 1 ≤ ell) (hR:F.degreeOf 2 ≤ s) (hZ:F.degreeOf 3 ≤ L)
   (b:ℕ):HasCaps (surfaceMap φ (numerator K F b)) (numeratorCaps ell s L b):=by
 obtain ⟨hy,hr,hz⟩:=numerator_degree_bounds F ell s L hs hY hR hZ b
 intro i
 fin_cases i
 · exact (surfaceMap_degreeOf_le φ _ 0).trans hy
 · exact (surfaceMap_degreeOf_le φ _ 1).trans hr
 · exact (surfaceMap_degreeOf_le φ _ 2).trans hz
theorem surface_agreement_caps
   (F:MvPolynomial (Fin 4) K) (ell s L:ℕ) (hs:1 ≤ s)
   (hY:F.degreeOf 1 ≤ ell) (hR:F.degreeOf 2 ≤ s) (hZ:F.degreeOf 3 ≤ L)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   HasCaps (surfaceMap φ (agreementNumerator F w c x u₀ u₁))
     (agreementCaps ell s L w):=by
 obtain ⟨hy,hr,hz⟩:=agreementNumerator_degree_bounds F ell s L hs hY hR hZ w c x u₀ u₁
 intro i
 fin_cases i
 · exact (surfaceMap_degreeOf_le φ _ 0).trans hy
 · exact (surfaceMap_degreeOf_le φ _ 1).trans hr
 · exact (surfaceMap_degreeOf_le φ _ 2).trans hz
theorem fixed_firstTail_caps (F:MvPolynomial (Fin 4) K)
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (hY:F.degreeOf 1 ≤ yCap) (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3 ≤ seedTotalCap):
   HasCaps (firstTailSurface φ F w) firstTail:=by
 have hold:=surface_numerator_caps φ F yCap slopeCap seedTotalCap (by decide)
   hY hR hZ (w+1)
 have hsharp:=sharp_Y_bounds_of_mem_box F weightedCap w seedTotalCap slopeCap yCap
   (by norm_num [w]) (by norm_num [yCap,weightedCap,RCN051.multiplicity,
     agreements,w])
   (by norm_num [weightedCap,RCN051.multiplicity,agreements,
     w,yCap]) hbox (w+1) 0 (fun _ => 0) 0 0 0
 intro i
 fin_cases i
 · have hy:=(surfaceMap_degreeOf_le φ _ 0).trans hsharp.1
   simpa [firstTailSurface,firstTail,tailVector,capAt] using hy
 · simpa [firstTailSurface,firstTail,tailVector,numeratorCaps,capAt] using hold 1
 · simpa [firstTailSurface,firstTail,tailVector,numeratorCaps,capAt] using hold 2
theorem fixed_agreement_caps (F:MvPolynomial (Fin 4) K)
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (hY:F.degreeOf 1 ≤ yCap) (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3 ≤ seedTotalCap) (x u₀ u₁:K):
   HasCaps (agreementPolynomial φ F w x u₀ u₁) agreementVector:=by
 have hold:=surface_agreement_caps φ F yCap slopeCap seedTotalCap (by decide)
   hY hR hZ w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁
 have hsharp:=sharp_Y_bounds_of_mem_box F weightedCap w seedTotalCap slopeCap yCap
   (by norm_num [w]) (by norm_num [yCap,weightedCap,RCN051.multiplicity,
     agreements,w])
   (by norm_num [weightedCap,RCN051.multiplicity,agreements,
     w,yCap]) hbox 0 w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁
 intro i
 fin_cases i
 · have hy:=(surfaceMap_degreeOf_le φ _ 0).trans hsharp.2
   simpa [agreementPolynomial,agreementVector,capAt] using hy
 · simpa [agreementPolynomial,agreementVector,agreementCaps,capAt] using hold 1
 · simpa [agreementPolynomial,agreementVector,agreementCaps,capAt] using hold 2
theorem selected_firstTail_zero
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (γ:K) (w:ℕ) (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0):
   MvPolynomial.aeval (selectedPoint φ selected γ) (firstTailSurface φ F w)=0:=by
 change MvPolynomial.eval (selectedPoint φ selected γ)
   (surfaceMap φ (numerator K F (w+1)))=0
 rw [eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
     polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
 exact polynomialPoint_numerator_zero (φ.comp Polynomial.C) F (selected γ) γ
   (φ Polynomial.X) hsolution (w+1) (Nat.lt_succ_of_le hdegree)
theorem fixed_implicit_agreement_caps (F:MvPolynomial (Fin 4) K)
   (hY:F.degreeOf 1 ≤ RCN168.implicitYCap)
   (hR:F.degreeOf 2 ≤ 1) (hZ:F.degreeOf 3 ≤ algebraicCap)
   (x u₀ u₁:K):
   HasCaps (agreementPolynomial φ F w x u₀ u₁)
     RCN168.liftedAgreement:=by
 have h:=surface_agreement_caps φ F RCN168.implicitYCap 1
   algebraicCap (by decide) hY hR hZ w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁
 simpa [agreementPolynomial,agreementCaps,RCN168.liftedAgreement] using h
section MixedGates
variable (G T:MvPolynomial (Fin 3) Ω) (g t:DegreeVector)
theorem actual_pair_degree_le (hG:HasCaps G g) (hT:HasCaps T t) (j k:Fin 3):
   T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k ≤
     capAt t j*capAt g k+capAt g j*capAt t k:=
 Nat.add_le_add (Nat.mul_le_mul (hT j) (hG k)) (Nat.mul_le_mul (hG j) (hT k))
theorem pair_caps_below_of_mixed (p:ℕ)
   (hY:mixed g t unitY < p) (hR:mixed g t unitR < p) (hZ:mixed g t unitZ < p):
   ∀ j k:Fin 3,j≠k →
     capAt t j*capAt g k+capAt g j*capAt t k < p:=by
 intro j k hne
 fin_cases j <;> fin_cases k
 all_goals try exact (hne rfl).elim
 all_goals first
   | simpa [capAt,mixed,unitY,Nat.mul_comm,Nat.add_comm] using hY
   | simpa [capAt,mixed,unitR,Nat.mul_comm,Nat.add_comm] using hR
   | simpa [capAt,mixed,unitZ,Nat.mul_comm,Nat.add_comm] using hZ
theorem actual_characteristic_gates (p:ℕ)
   (hG:HasCaps G g) (hT:HasCaps T t)
   (hg:∀ j,capAt g j < p)
   (hY:mixed g t unitY < p) (hR:mixed g t unitR < p) (hZ:mixed g t unitZ < p):
   (∀ j,G.degreeOf j < p)∧
     ∀ j k:Fin 3,j≠k →
       T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p:=by
 refine ⟨fun j↦(hG j).trans_lt (hg j),?_⟩
 intro j k hjk
 exact (actual_pair_degree_le G T g t hG hT j k).trans_lt
   (pair_caps_below_of_mixed g t p hY hR hZ j k hjk)
end MixedGates
theorem fixed_surface_caps_below_characteristic:
   ∀ j,capAt RCN242.surfaceVector j < prime:=by
 intro j
 fin_cases j <;>
   norm_num [capAt,RCN242.surfaceVector,yCap,weightedCap,
     RCN051.multiplicity,agreements,w,slopeCap,seedTotalCap,prime]
theorem fixed_firstTail_nonR_characteristic_gates (G T:MvPolynomial (Fin 3) Ω)
   (hG:HasCaps G RCN242.surfaceVector) (hT:HasCaps T firstTail):
   (∀ j,G.degreeOf j < prime)∧
     T.degreeOf 1*G.degreeOf 2+G.degreeOf 1*T.degreeOf 2 < prime∧
     T.degreeOf 0*G.degreeOf 1+G.degreeOf 0*T.degreeOf 1 < prime:=by
 rcases RCN242.non_R_projection_caps_below_characteristic with
   ⟨hY,hZ,_,_⟩
 refine ⟨fun j => (hG j).trans_lt (fixed_surface_caps_below_characteristic j),
   (actual_pair_degree_le G T _ _ hG hT 1 2).trans_lt ?_,
   (actual_pair_degree_le G T _ _ hG hT 0 1).trans_lt ?_⟩
 · simpa [capAt,mixed,unitY,Nat.mul_comm,Nat.add_comm] using hY
 · simpa [capAt,mixed,unitZ,Nat.mul_comm,Nat.add_comm] using hZ
theorem fixed_agreement_nonR_characteristic_gates (G T:MvPolynomial (Fin 3) Ω)
   (hG:HasCaps G RCN242.surfaceVector) (hT:HasCaps T agreementVector):
   (∀ j,G.degreeOf j < prime)∧
     T.degreeOf 1*G.degreeOf 2+G.degreeOf 1*T.degreeOf 2 < prime∧
     T.degreeOf 0*G.degreeOf 1+G.degreeOf 0*T.degreeOf 1 < prime:=by
 rcases RCN242.non_R_projection_caps_below_characteristic with
   ⟨_,_,hY,hZ⟩
 refine ⟨fun j => (hG j).trans_lt (fixed_surface_caps_below_characteristic j),
   (actual_pair_degree_le G T _ _ hG hT 1 2).trans_lt ?_,
   (actual_pair_degree_le G T _ _ hG hT 0 1).trans_lt ?_⟩
 · simpa [capAt,mixed,unitY,Nat.mul_comm,Nat.add_comm] using hY
 · simpa [capAt,mixed,unitZ,Nat.mul_comm,Nat.add_comm] using hZ
theorem fixed_implicit_surface_caps_below_characteristic:
   ∀ j,capAt RCN168.liftedSurface j < prime:=by
 intro j
 fin_cases j <;>
   norm_num [capAt,RCN168.liftedSurface,
     RCN168.implicitYCap,RCN168.implicitWeightedCap,
     algebraicCap,weightedCap,RCN051.multiplicity,agreements,
     w,slopeCap,seedTotalCap,prime]
theorem fixed_implicit_characteristic_gates (G T:MvPolynomial (Fin 3) Ω)
   (hG:HasCaps G RCN168.liftedSurface)
   (hT:HasCaps T RCN168.implicitCut):
   (∀ j,G.degreeOf j < prime)∧
     ∀ j k:Fin 3,j≠k →
       T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < prime:=by
 rcases RCN168.lifted_projection_characteristic_gates with
   ⟨_,hY,hR,hZ⟩
 exact actual_characteristic_gates G T _ _ prime hG hT
   fixed_implicit_surface_caps_below_characteristic hY hR hZ
end
end ProximityPrize.SubmissionLower.RCN068
