/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833CubicSlice
import ProximityPrize.SubmissionLower.Koala6831SeparationNormalForm
import ProximityPrize.SubmissionLower.Koala6831PrimitiveLiftDegrees
import Mathlib.Tactic
namespace Frontier6969.Extract
open MvPolynomial ProximityPrize.SubmissionLower
open Koala6831Comparison Koala6831Separation Koala6831Ordinary Koala6831RankFour
open Koala6831CoefficientSystem (coefficientPolynomial)
open scoped BigOperators Polynomial Matrix Classical
noncomputable section
variable {R : Type*} [CommRing R]

def key (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a+Finsupp.single 1 b
theorem key_eq {i j a b : ℕ} : key i j=key a b ↔ i=a ∧ j=b := by
  constructor
  · intro h
    exact ⟨by simpa [key] using DFunLike.congr_fun h 0,by simpa [key] using DFunLike.congr_fun h 1⟩
  · rintro ⟨rfl,rfl⟩;rfl

def trm (a b : ℕ) (r : R) := monomial (key a b) r
theorem trm_eq (a b : ℕ) (r : R) : trm a b r=C r*(MvPolynomial.X (0:Fin 2))^a*(MvPolynomial.X 1)^b := by
  simp [trm,key,X_pow_eq_monomial,C_mul_monomial]
def affine3 (r s t : R) : MvPolynomial (Fin 2) R := C r+C s*MvPolynomial.X 0+C t*MvPolynomial.X 1
def square6 (a b c d e f : R) : MvPolynomial (Fin 2) R :=
  trm 0 0 a+trm 1 0 b+trm 0 1 c+trm 2 0 d+trm 1 1 e+trm 0 2 f

theorem expand_tuple (a b c d e f u v s t : R) :
    affine3 a b c*(C u+C v*MvPolynomial.X 0) + affine3 d e f*(C s+C t*MvPolynomial.X 1) =
    square6 (a*u+d*s) (b*u+a*v+e*s) (c*u+f*s+d*t) (b*v) (c*v+e*t) (f*t) := by
  simp only [affine3,square6,trm_eq,map_add,map_mul,pow_zero,pow_one]
  ring

theorem extract6 (a b c d e f : R) : let V := square6 a b c d e f
    V.coeff (key 0 0)=a ∧ V.coeff (key 1 0)=b ∧ V.coeff (key 0 1)=c ∧
    V.coeff (key 2 0)=d ∧ V.coeff (key 1 1)=e ∧ V.coeff (key 0 2)=f := by
  simp [square6,trm,coeff_monomial,key_eq]


variable {K : Type*} [Field K]
open Koala6831SeparationFactors (affine)
private theorem from_seed_support (P : SeedCoefficients K) (j : ℕ) (z : Fin 2 →₀ ℕ)
    (hz : z ∈ (P.coeff j).support) :
    ∃ e ∈ (retainCarrier (carrierOfSeedCoefficients P)).support, e 3 = z 0 ∧ e 4 = z 1 := by
  let R := (MvPolynomial.optionEquivLeft K (Fin 2)).symm P
  let f := carrierCoordinates ∘ carrierCoefficientCoordinates
  let d := z.optionElim j
  have hdf : d ∈ R.support := by
    apply MvPolynomial.mem_support_iff.mpr
    have he := MvPolynomial.optionEquivLeft_coeff_coeff K R j z
    change ((((MvPolynomial.optionEquivLeft K (Fin 2))
      ((MvPolynomial.optionEquivLeft K (Fin 2)).symm P)).coeff j).coeff z) = R.coeff d at he
    rw [AlgEquiv.apply_symm_apply] at he
    exact he ▸ MvPolynomial.mem_support_iff.mp hz
  have hf : Function.Injective f := by
    change ∀ i j : Option (Fin 2), f i = f j → i = j
    decide
  have hLift : retainCarrier (carrierOfSeedCoefficients P) = MvPolynomial.rename f R := by
    rw [retainCarrier, carrierOfSeedCoefficients]
    change MvPolynomial.rename carrierCoordinates (MvPolynomial.rename carrierCoefficientCoordinates R) = _
    rw [MvPolynomial.rename_rename]
  refine ⟨Finsupp.mapDomain f d, ?_, ?_, ?_⟩
  · rw [hLift, MvPolynomial.support_rename_of_injective hf]
    exact Finset.mem_image.mpr ⟨d, hdf, rfl⟩
  · change Finsupp.mapDomain f d (f (some 0)) = _
    rw [Finsupp.mapDomain_apply_of_injective hf]
    simp [d]
  · change Finsupp.mapDomain f d (f (some 1)) = _
    rw [Finsupp.mapDomain_apply_of_injective hf]
    simp [d]

private theorem zero_high (P : SeedCoefficients K) (h : weightDegree totalWeights
    (retainCarrier (carrierOfSeedCoefficients P)) ≤ 1)
    (z : Fin 2 →₀ ℕ) (hz : 1 < z 0 + z 1) (δ : ℕ) :
    coefficientPolynomial P z δ = 0 := by
  unfold coefficientPolynomial
  apply Finset.sum_eq_zero
  intro j _
  suffices (P.coeff j).coeff z = 0 by rw [this, Polynomial.monomial_zero_right]
  by_contra! hne
  obtain ⟨e, he, h₀, h₁⟩ := from_seed_support P j z (MvPolynomial.mem_support_iff.mpr hne)
  have hdegree := (MvPolynomial.le_weightedTotalDegree totalWeights he).trans h
  rw [total_weight, h₀, h₁] at hdegree
  omega

private theorem small_key (z : Fin 2 →₀ ℕ) (hz : z 0 + z 1 ≤ 1) :
    z = 0 ∨ z = Finsupp.single 0 1 ∨ z = Finsupp.single 1 1 := by
  by_cases h₀ : z 0 = 0
  · by_cases h₁ : z 1 = 0
    · left; ext i; fin_cases i <;> assumption
    · right; right; ext i; fin_cases i <;> simp <;> omega
  · right; left; ext i; fin_cases i <;> simp <;> omega

private theorem affine_regroup (P : SeedCoefficients K) (h : weightDegree totalWeights
    (retainCarrier (carrierOfSeedCoefficients P)) ≤ 1) (D : ℕ) (hp : P.natDegree ≤ D) :
    let b := fun k => coefficientPolynomial P k D
    regroup P = affine 0 (b 0) (b (Finsupp.single 0 1)) +
      affine 1 0 (b (Finsupp.single 1 1)) := by
  dsimp only
  ext z
  rw [coeff_regroup_eq _ _ _ hp]
  have h01 : (Finsupp.single (0:Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro he
    have he' := DFunLike.congr_fun he 0
    simp at he'
  have zn (i : Fin 2) : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro he
    have hh := DFunLike.congr_fun he i
    simp at hh
  by_cases hz : z 0 + z 1 ≤ 1
  · rcases small_key z hz with rfl | rfl | rfl <;>
      simp [affine, coeff_X, h01, Ne.symm h01, zn]
  · have h0 : z ≠ 0 := by rintro rfl; simp at hz
    have hl : z ≠ Finsupp.single 0 1 := by rintro rfl; simp at hz
    have hr : z ≠ Finsupp.single 1 1 := by rintro rfl; simp at hz
    rw [zero_high P h z (by omega) D]
    simp [affine, coeff_X, Ne.symm h0, Ne.symm hl, Ne.symm hr]


def get (q : SymbolicRow (SeedRing K)) (w δ : ℕ) : Form K[X] :=
  let A := fun j => coefficientPolynomial q.first j δ
  let B := fun j => coefficientPolynomial q.second j δ
  let V := fun i j => coefficientPolynomial (-q.beta) (key i j) (w+δ)
  ⟨A 0,A (Finsupp.single 0 1),A (Finsupp.single 1 1),
   B 0,B (Finsupp.single 0 1),B (Finsupp.single 1 1),
   V 0 0,V 1 0,V 0 1,V 2 0,V 1 1,V 0 2⟩

theorem get_caps (q : SymbolicRow (SeedRing K)) (w δ : ℕ) : Caps (get q w δ) w δ := by
  constructor <;> exact Koala6831CoefficientSystem.coefficientPolynomial_degree _ _ _

theorem both_forms (q : SymbolicRow (SeedRing K)) (w δ : ℕ)
    (ha : q.first≠0) (hb : q.second≠0) (hA : q.first.natDegree≤δ) (hB : q.second.natDegree≤δ)
    (hd : weightDegree totalWeights (primitiveRowLift q)≤2) :
    let f := get q w δ
    regroup q.first=affine3 f.a₀ f.ax f.ay ∧ regroup q.second=affine3 f.c₀ f.cx f.cy := by
  obtain ⟨_,φ,ψ⟩ := primitiveRowLift_total_weight_caps q ha hb
  refine ⟨?_,?_⟩
  · simpa [get,affine,affine3] using affine_regroup q.first (φ.trans (by omega)) δ hA
  · simpa [get,affine,affine3] using affine_regroup q.second (ψ.trans (by omega)) δ hB

theorem fit_at_node (q : SymbolicRow (SeedRing K)) (w δ : ℕ) (x u v s t : K)
    (ha : q.first≠0) (hb : q.second≠0) (hA : q.first.natDegree≤δ) (hB : q.second.natDegree≤δ)
    (hβ : q.beta.natDegree≤w+δ) (hd : weightDegree totalWeights (primitiveRowLift q)≤2)
    (hn : q.atNode (C x) (C u+MvPolynomial.X 0*C v) (C s+MvPolynomial.X 1*C t)=0) :
    Fits (get q w δ) x u v s t := by
  let f := get q w δ
  obtain ⟨af,cf⟩ := both_forms q w δ ha hb hA hB hd
  let E := Polynomial.evalRingHom x
  have maplin (a b c : K[X]) : map E (affine3 a b c)=affine3 (a.eval x) (b.eval x) (c.eval x) := by
    simp [affine3,E]
  have av : q.first.eval (C x)=affine3 (f.a₀.eval x) (f.ax.eval x) (f.ay.eval x) := by
    rw [← map_eval_regroup,af]; exact maplin _ _ _
  have cv : q.second.eval (C x)=affine3 (f.c₀.eval x) (f.cx.eval x) (f.cy.eval x) := by
    rw [← map_eval_regroup,cf]; exact maplin _ _ _
  unfold SymbolicRow.atNode at hn
  rw [av,cv,mul_comm (MvPolynomial.X 0) (C v),mul_comm (MvPolynomial.X 1) (C t)] at hn
  have e := expand_tuple (f.a₀.eval x) (f.ax.eval x) (f.ay.eval x)
    (f.c₀.eval x) (f.cx.eval x) (f.cy.eval x) u v s t
  have eq : square6 (f.a₀.eval x*u+f.c₀.eval x*s) (f.ax.eval x*u+f.a₀.eval x*v+f.cx.eval x*s)
    (f.ay.eval x*u+f.cy.eval x*s+f.c₀.eval x*t) (f.ax.eval x*v) (f.ay.eval x*v+f.cx.eval x*t) (f.cy.eval x*t) = (-q.beta).eval (C x) := by
    rw [←e,Polynomial.eval_neg];linear_combination hn
  have h := extract6 (f.a₀.eval x*u+f.c₀.eval x*s) (f.ax.eval x*u+f.a₀.eval x*v+f.cx.eval x*s)
    (f.ay.eval x*u+f.cy.eval x*s+f.c₀.eval x*t) (f.ax.eval x*v) (f.ay.eval x*v+f.cx.eval x*t) (f.cy.eval x*t)
  dsimp only at h
  rw [eq] at h
  have hb' : (-q.beta).natDegree≤w+δ := by simpa using hβ
  simp_rw [← Koala6831CoefficientSystem.eval_coefficientPolynomial (-q.beta) _ (w+δ) x hb'] at h
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := h
  exact ⟨h0.symm,h1.symm,h2.symm,h3.symm,h4.symm,h5.symm⟩

theorem no_relation (q : SymbolicRow (SeedRing K)) (w δ : ℕ)
    (ha : q.first≠0) (hb : q.second≠0) (hA : q.first.natDegree≤δ) (hB : q.second.natDegree≤δ)
    (hd : weightDegree totalWeights (primitiveRowLift q)≤2) (keys : Fin 4 → Fin 2 →₀ ℕ)
    (hn : (Koala6831RankFour.matrix q keys δ).det≠0) :
    NoRel (get q w δ) := by
  let f := get q w δ
  obtain ⟨af,cf⟩ := both_forms q w δ ha hb hA hB hd
  intro u v s t e₀ e₁ e₂ e₃ e₄ e₅
  let word : Fin 4 → K[X] := ![u,v,s,t]
  have exp := expand_tuple f.a₀ f.ax f.ay f.c₀ f.cx f.cy u v s t
  have nul : regroup q.first*(C u+C v*MvPolynomial.X 0)+regroup q.second*(C s+C t*MvPolynomial.X 1) = 0 := by
    rw [af,cf]
    change affine3 f.a₀ f.ax f.ay*_+affine3 f.c₀ f.cx f.cy*_=0
    rw [exp,e₀,e₁,e₂,e₃,e₄,e₅]
    simp [square6,trm]
  have deg (j : Fin 4) : (columns q j).natDegree≤δ := by
    fin_cases j
    · exact hA
    · exact (Polynomial.natDegree_C_mul_le _ _).trans hA
    · exact hB
    · exact (Polynomial.natDegree_C_mul_le _ _).trans hB
  have he : (∑ j, C (word j)*regroup (columns q j))=0 := by
    simp only [Fin.sum_univ_succ,word,columns, Matrix.cons_val_zero,Matrix.cons_val_succ, Finset.univ_eq_empty,Finset.sum_empty,
      add_zero,map_mul,regroup_C,map_X]
    linear_combination nul
  have hmul : (Koala6831RankFour.matrix q keys δ)*ᵥword=0 := by
    funext i
    have hcoeff := congrArg (fun P : MvPolynomial (Fin 2) K[X] => P.coeff (keys i)) he
    simp only [coeff_sum,coeff_C_mul,AddMonoidAlgebra.coeff_zero] at hcoeff
    simp_rw [coeff_regroup_eq _ _ δ (deg _)] at hcoeff
    change (∑ j,word j*coefficientPolynomial (columns q j) (keys i) δ)=0 at hcoeff
    simpa only [Koala6831RankFour.matrix,Matrix.mulVec,dotProduct,Matrix.of_apply,mul_comm,Pi.zero_apply] using hcoeff
  have hzero (i : Fin 4) : word i=0 := by
    by_contra h
    exact hn (Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hmul (mem_nonZeroDivisors_iff_ne_zero.mpr h))
  exact ⟨hzero 0,hzero 1,hzero 2,hzero 3⟩

theorem rank_three_actual {I : Type*} [DecidableEq K]
    (σ : K ≃+* K) (dom : I ↪ K) (hfix : ∀ i, σ (dom i)=dom i)
    (seeds : Finset K) (ag : K → Finset I) (sel : K → K[X]) (u v : I → K)
    (q : SymbolicRow (SeedRing K)) (w δ e : ℕ)
    (hA : q.first.natDegree≤δ) (hB : q.second.natDegree≤δ) (hβ : q.beta.natDegree≤w+δ)
    (ha : q.first≠0) (hb : q.second≠0) (hc : weightDegree totalWeights (primitiveRowLift q)≤2)
    (keys : Fin 4 → Fin 2 →₀ ℕ) (hn : (Koala6831RankFour.matrix q keys δ).det≠0)
    (hg : ∀ g∈seeds, ∀ i∈ag g,
      q.atNode (C (dom i)) (C (u i)+MvPolynomial.X 0*C (v i)) (C (σ (u i))+MvPolynomial.X 1*C (σ (v i)))=0)
    (hd : ∀ g∈seeds, (sel g).natDegree≤w)
    (hsize : ∀ g∈seeds, w+3*δ<(ag g).card)
    (hv : ∀ g∈seeds, ∀ i∈ag g, (sel g).eval (dom i)=u i+g*v i)
    (hp : ∀ F G : K[X], F.natDegree≤w → G.natDegree≤w →
      (seeds.filter (fun g => sel g=F+Polynomial.C g*G)).card≤e+1) : seeds.card≤e+1 :=
  both_orientations σ dom hfix seeds ag sel u v _ w δ e (get_caps q w δ)
    (no_relation q w δ ha hb hA hB hc keys hn)
    (fun g hgi i hi => fit_at_node q w δ (dom i) _ _ _ _ ha hb hA hB hβ hc (hg g hgi i hi))
    hd hsize hv hp

#print axioms rank_three_actual
#print axioms fit_at_node
#print axioms no_relation
#print axioms expand_tuple
#print axioms extract6
end
end Frontier6969.Extract
