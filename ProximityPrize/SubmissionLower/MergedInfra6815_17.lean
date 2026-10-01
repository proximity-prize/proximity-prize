import ProximityPrize.SubmissionLower.MergedInfra6815_14
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_16
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingFiberProfile6811
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider
open MovingFiberRegularData6811 MovingFiberThreeSources6811 MovingFiberInterpolation6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

structure Params where
  m : ℕ
  B : ℕ
  s : ℕ
  U : ℕ
  L : ℕ
  k : ℕ
  n0 : ℕ
  deriving DecidableEq, Repr

def Params.d (P : Params) : ℕ := P.k+1
def Params.flag (P : Params) : FlagDegree := SecondJetRelaxedFlag.budgetFlag P.B P.U P.L P.d P.n0
def Params.WellFormed (P : Params) : Prop :=
  2*P.s ≤ P.B ∧ P.B ≤ P.U ∧ P.U ≤ P.L ∧ P.k ≤ P.s ∧ P.s < P.m ∧
    P.k+1 ≤ P.n0 ∧ 2*(P.n0-(P.k+1)) ≤ P.B ∧ P.s < 2130706433
def number (cfg : Fin 3 → Params) (scale t y r : ℕ) (f : FlagDegree) : ℕ :=
  scale/3*flagMixed f (MovingFiberRetainedStage6811.hfreeFirst t y r) (cellNormal t y r) +
    ∑ j : Fin 3, (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(cfg j).d))+
      65539*weight (MovingFiberRetainedStage6811.rawFirstFlag t y r) j*(scale/(cfg j).d))*
      flagMixed f (MovingFiberThreeSources6811.direction j) (cfg j).flag

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {nodes : I ↪ K} {u0 u1 : I → K}

def helperCap (S : Data nodes u0 u1) (P : Params) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (S.pair (P.B+P.s*(S.r-1)) (P.U+P.s*(S.y-1)) (P.L+P.s*(S.t-1)))
def coefficientCap (S : Data nodes u0 u1) (P : Params) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (S.pair P.B P.U P.L)
def bound (S : Data nodes u0 u1) (cfg : Fin 3 → Params) (scale : ℕ) : ℕ :=
  max (Finset.univ.sup (fun j : Fin 3 => helperCap S (cfg j)))
    (number cfg scale S.t S.y S.r (originalCumulativeFlag S.F)/scale +
      ∑ j : Fin 3, coefficientCap S (cfg j))

end
end ProximityPrize.SubmissionLower.MovingFiberProfile6811
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.RetainedWholeSpace6814
open scoped Classical
open MvPolynomial RCN095 RCN130 RCN135 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open MovingFiberRegularData6811 MovingFiberInterpolation6811 MovingFiberProfile6811
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.RetainedWholeSpace6814
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.ContactPencilDirection6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MvPolynomial

variable {K : Type*} [CommRing K]
abbrev JetPoly := MvPolynomial (Fin 5) K

def contactMap (x u0 u1 : K) : JetPoly (K := K) →ₐ[K] JetPoly (K := K) :=
  MvPolynomial.aeval ![MvPolynomial.C x+MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4+
      MvPolynomial.X 0*MvPolynomial.X 3-MvPolynomial.X 0^2*MvPolynomial.X 1+
      MvPolynomial.X 0^3*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

end
end ProximityPrize.SubmissionLower.ContactPencilDirection6814
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.UniqueCurvatureOwner6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial

variable {E : Type*} [Field E]

theorem rootMultiplicity_power (j : Polynomial E) (t : E) (e : ℕ)
    (hj : j ≠ 0) : (j^e).rootMultiplicity t = e * j.rootMultiplicity t := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hj) hj), ih]
    ring

theorem unique_owner_order_le (j q : Polynomial E) (t : E) (d e : ℕ)
    (hj : j ≠ 0) (hq : q.eval t ≠ 0)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ j^e*q) :
    d ≤ e*j.rootMultiplicity t := by
  have hq0 : q ≠ 0 := by
    intro hz
    exact hq (by rw [hz]; simp)
  have hprod : j^e*q ≠ 0 := mul_ne_zero (pow_ne_zero _ hj) hq0
  have hm := (Polynomial.le_rootMultiplicity_iff hprod).mpr hd
  rw [Polynomial.rootMultiplicity_mul hprod,rootMultiplicity_power j t e hj,
    Polynomial.rootMultiplicity_eq_zero hq,add_zero] at hm
  exact hm

open RCN095

end
end ProximityPrize.SubmissionLower.UniqueCurvatureOwner6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.CofactorOwnership6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Polynomial UniqueCurvatureOwner6814

variable {ι E : Type*} [Field E]
local instance : DecidableEq ι := Classical.decEq ι

end
end ProximityPrize.SubmissionLower.CofactorOwnership6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.WholeSpaceCube6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K]
abbrev Poly := MvPolynomial (Fin 5) K

def weightEmbed (w : Fin 5 → ℕ) : (Fin 5 →₀ ℕ) →+ (Fin 6 →₀ ℕ) where
  toFun d := Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
    Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)+Finsupp.single 4 (d 4)+
    Finsupp.single 5 (Finsupp.weight w d)
  map_zero' := by simp
  map_add' d e := by ext i; fin_cases i <;> simp [Finsupp.add_apply,map_add]

theorem weightEmbed_coord (w : Fin 5 → ℕ) (d : Fin 5 →₀ ℕ) (i : Fin 5) :
    weightEmbed w d i.castSucc = d i := by
  fin_cases i <;> simp [weightEmbed]

theorem weightEmbed_injective (w : Fin 5 → ℕ) : Function.Injective (weightEmbed w) := by
  intro d e h
  ext i
  simpa only [weightEmbed_coord] using congrArg (fun x : Fin 6 →₀ ℕ => x i.castSucc) h

def weightedLift (w : Fin 5 → ℕ) : Poly (K := K) →+* MvPolynomial (Fin 6) K :=
  AddMonoidAlgebra.mapDomainRingHom K (weightEmbed w)

theorem weightedLift_injective (w : Fin 5 → ℕ) : Function.Injective (weightedLift (K := K) w) :=
  AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective w)

theorem weightedLift_degree (w : Fin 5 → ℕ) (P : Poly (K := K)) :
    (weightedLift w P).degreeOf 5 = weightedTotalDegree w P := by
  have hs : (weightedLift w P).support = P.support.image (weightEmbed w) :=
    Finsupp.mapDomain_support_of_injective (weightEmbed_injective w) _
  rw [degreeOf_eq_sup,hs,Finset.sup_image]
  change P.support.sup (fun d => weightEmbed w d 5) = P.support.sup (Finsupp.weight w)
  congr 1
  funext d
  simp [weightEmbed]

theorem weight_mul (w : Fin 5 → ℕ) (P Q : Poly (K := K)) (hP : P≠0) (hQ : Q≠0) :
    weightedTotalDegree w (P*Q) = weightedTotalDegree w P+weightedTotalDegree w Q := by
  have hn (A : Poly (K := K)) (hA : A≠0) : weightedLift w A ≠ 0 := by
    intro hz
    apply hA
    exact weightedLift_injective w (by simpa only [map_zero] using hz)
  rw [←weightedLift_degree,map_mul,degreeOf_mul_eq (hn P hP) (hn Q hQ),
    weightedLift_degree,weightedLift_degree]

theorem weight_pow (w : Fin 5 → ℕ) (P : Poly (K := K)) (hP : P≠0) (n : ℕ) :
    weightedTotalDegree w (P^n) = n*weightedTotalDegree w P := by
  induction n with
  | zero => simp [weightedTotalDegree]
  | succ n ih =>
    rw [pow_succ,weight_mul w _ _ (pow_ne_zero _ hP) hP,ih]
    ring

def codeWeights : Fin 5 → ℕ := ![1,131069,131071,131070,0]
def middleWeights : Fin 5 → ℕ := ![0,1,1,1,0]
def totalWeights : Fin 5 → ℕ := ![0,1,1,1,1]

theorem weight_coords (w : Fin 5 → ℕ) (e : Fin 5 →₀ ℕ) :
    Finsupp.weight w e = e 0*w 0+e 1*w 1+e 2*w 2+e 3*w 3+e 4*w 4 := by
  have he : e = Finsupp.single 0 (e 0)+Finsupp.single 1 (e 1)+
      Finsupp.single 2 (e 2)+Finsupp.single 3 (e 3)+Finsupp.single 4 (e 4) := by
    ext i; fin_cases i <;> simp
  rw [he,map_add,map_add,map_add,map_add]
  simp [Finsupp.weight_single]

theorem factor_code_lower (J : Poly (K := K)) (hJ : J≠0)
    (hmid : weightedTotalDegree middleWeights J=30)
    (hB : ∀ e ∈ J.support, 2*e 1+e 3 ≤ 9) :
    3932121 ≤ weightedTotalDegree codeWeights J := by
  obtain ⟨e,he,hmax⟩ := Finset.exists_mem_eq_sup J.support (support_nonempty.mpr hJ)
    (Finsupp.weight middleWeights)
  have hm : Finsupp.weight middleWeights e=30 := hmax.symm.trans hmid
  have hc : Finsupp.weight codeWeights e ≤ weightedTotalDegree codeWeights J := Finset.le_sup he
  have hb := hB e he
  have hm' : e 1+e 2+e 3=30 := by simpa [weight_coords,middleWeights] using hm
  have hc' : e 0+131069*e 1+131071*e 2+131070*e 3 ≤ weightedTotalDegree codeWeights J := by
    simpa [weight_coords,codeWeights,Nat.mul_comm] using hc
  omega

theorem quotient_bounds (J Q : Poly (K := K)) (hJ : J≠0) (hQ : Q≠0)
    (hmid : weightedTotalDegree middleWeights J=30)
    (hB : ∀ e ∈ J.support, 2*e 1+e 3 ≤ 9)
    (ht : weightedTotalDegree totalWeights J=331)
    (hcode : weightedTotalDegree codeWeights (J^3*Q) < 13050360)
    (htotal : weightedTotalDegree totalWeights (J^3*Q) ≤ 995) :
    weightedTotalDegree codeWeights Q < 1253997 ∧
      weightedTotalDegree totalWeights Q ≤ 2 := by
  have hl := factor_code_lower J hJ hmid hB
  rw [weight_mul _ _ _ (pow_ne_zero _ hJ) hQ,weight_pow _ _ hJ] at hcode htotal
  rw [ht] at htotal
  omega

abbrev QuotientIndex := Fin 1253997 × (Fin 4 → Fin 3)

def quotientExponent (i : QuotientIndex) : Fin 5 →₀ ℕ :=
  Finsupp.cons i.1.val (Finsupp.equivFunOnFinite.symm (fun j => (i.2 j).val))

theorem quotient_support (Q : Poly (K := K))
    (hcode : weightedTotalDegree codeWeights Q < 1253997)
    (htotal : weightedTotalDegree totalWeights Q ≤ 2) :
    ∀ e ∈ Q.support, e ∈ Set.range quotientExponent := by
  intro e he
  have hc := (Finset.le_sup (f := Finsupp.weight codeWeights) he).trans_lt hcode
  have ht := (Finset.le_sup (f := Finsupp.weight totalWeights) he).trans htotal
  simp [weight_coords,codeWeights,totalWeights] at hc ht
  have hx : e 0 < 1253997 := by omega
  have hrest : ∀ i : Fin 4, e i.succ < 3 := by
    intro i
    fin_cases i
    · change e 1 < 3; omega
    · change e 2 < 3; omega
    · change e 3 < 3; omega
    · change e 4 < 3; omega
  refine ⟨(⟨e 0,hx⟩,fun i => ⟨e i.succ,hrest i⟩),?_⟩
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [quotientExponent]

theorem finrank_le_coefficients {W I : Type*} [AddCommGroup W] [Module K W]
    [Fintype I] (e : I → Fin 5 →₀ ℕ) (f : W →ₗ[K] Poly (K := K))
    (hf : Function.Injective f)
    (hs : ∀ v : W, ∀ d ∈ (f v).support, d ∈ Set.range e) :
    Module.finrank K W ≤ Fintype.card I := by
  let A : W →ₗ[K] (I → K) := LinearMap.pi (fun i => (MvPolynomial.lcoeff K (e i)).comp f)
  have hi : Function.Injective A := by
    intro v u h
    apply hf
    ext d
    have hh (i : I) : (f v).coeff (e i)=(f u).coeff (e i) := congrFun h i
    by_cases hv : d ∈ (f v).support
    · obtain ⟨i,rfl⟩ := hs v d hv
      exact hh i
    by_cases hu : d ∈ (f u).support
    · obtain ⟨i,rfl⟩ := hs u d hu
      exact hh i
    rw [MvPolynomial.notMem_support_iff.mp hv,MvPolynomial.notMem_support_iff.mp hu]
  simpa using LinearMap.finrank_le_finrank_of_injective hi

end
end ProximityPrize.SubmissionLower.WholeSpaceCube6814
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial WholeSpaceCube6814

variable {K : Type*} [Field K]
def slopeWeights : Fin 5 → ℕ := ![0,2,0,1,0]

open RCN095 UniqueCurvatureOwner6814

end
end ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceCounts6814
open scoped BigOperators
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cutoff (h : ℕ) : ℕ :=
  72*181255-SecondJetRelaxedDifferentiation.reserve 2 3 h*50186

end ProximityPrize.SubmissionLower.WholeSpaceSourceCounts6814
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
open scoped BigOperators
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpaceSourceCounts6814
open SecondJetSupport SecondJetGlobalSupport
open SecondJetGlobalMap (coefficientLocal untruncate_contact)

variable {K N I : Type*} [Field K] [Fintype N] [Fintype I]

def Bounds (P : WholeSpaceCube6814.Poly (K := K)) : Prop :=
  ∀ e ∈ P.support, 2*e 1+e 3 ≤ 31 ∧ e 1 ≤ 14 ∧
    e 1+e 2+e 3 ≤ 98 ∧ e 1+e 2+e 3+e 4 ≤ 1700 ∧
    e 0+131071*e 2+131070*e 3+131069*e 1 < cutoff (e 1)

theorem exists_contact_kernel
    (e : I → Fin 5 →₀ ℕ) (he : Function.Injective e)
    (m L B s U w : ℕ) (D : ℕ → ℕ) (hw : 2 ≤ w)
    (hb : ∀ i, 2*e i 1+e i 3 ≤ B) (hs : ∀ i, e i 1 ≤ s)
    (hu : ∀ i, e i 1+e i 2+e i 3 ≤ U)
    (hl : ∀ i, e i 1+e i 2+e i 3+e i 4 ≤ L)
    (hd : ∀ i, e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1 < D (e i 1))
    (nodes : N ↪ K) (u0 u1 : N → K) (bound : ℕ)
    (hcard : bound+Fintype.card N*
      SecondJetRelaxedGlobalMap.rankBound m L B s U
        (fun h => (D h+B-1)/w) ≤ Fintype.card I) :
    ∃ V : Submodule K (WholeSpaceCube6814.Poly (K := K)), Module.Finite K V ∧
      bound ≤ Module.finrank K V ∧
      (∀ P ∈ V, ∀ d ∈ P.support, d ∈ Set.range e) ∧
      (∀ P ∈ V, ∀ n, MvPolynomial.X 0^m ∣ SecondJetDifferentiation.substitute (K := K)
        (localize (nodes n) (u0 n) (u1 n) P)) := by
  classical
  let caps := fun h => (D h+B-1)/w
  let f := SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps
  letI : AddCommGroup f.range := inferInstance
  letI : Module K f.range := f.range.module
  letI : FiniteDimensional K f.range := by
    change FiniteDimensional K
      (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range
    infer_instance
  let ell (n : N) : (I → K) →ₗ[K] SecondJetRelaxedSpace.source (K := K) m L B s U caps :=
    (coefficientLocal e m (nodes n) (u0 n) (u1 n)).codRestrict _
      (SecondJetRelaxedGlobalMap.coefficientLocal_mem e m L B s U w D hw
        (nodes n) (u0 n) (u1 n) hb hs hu hl hd)
  let g : (I → K) →ₗ[K] (N → f.range) :=
    LinearMap.pi (fun n => f.rangeRestrict.comp (ell n))
  have htarget : Module.finrank K (N → f.range) ≤
      Fintype.card N*SecondJetRelaxedGlobalMap.rankBound m L B s U caps := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    exact Nat.mul_le_mul_left _
      (SecondJetRelaxedGlobalMap.local_rank_le_count m L B s U caps)
  have hrange := g.range.finrank_le
  have hsum := g.finrank_range_add_finrank_ker
  have hdimI : Module.finrank K (I → K)=Fintype.card I := by simp
  have hkernel : bound ≤ Module.finrank K g.ker := by
    dsimp only [caps] at htarget
    omega
  let recon : g.ker →ₗ[K] WholeSpaceCube6814.Poly (K := K) :=
    (FiniteMonomials.reconstruct e).comp g.ker.subtype
  have hrecon : Function.Injective recon := by
    intro a b hh
    apply Subtype.ext
    exact FiniteMonomials.reconstruct_injective e he hh
  let V := recon.range
  have hdimV : bound ≤ Module.finrank K V := by
    rw [LinearMap.finrank_range_of_inj hrecon]
    exact hkernel
  refine ⟨V,inferInstance,hdimV,?_,?_⟩
  · rintro P ⟨c,rfl⟩
    exact (FiniteMonomials.mem_range_iff e he _).mp ⟨c.val,rfl⟩
  · rintro P ⟨c,rfl⟩ n
    have hc : g c.val=0 := c.property
    have hz := congrArg Subtype.val (congrFun hc n)
    change SecondJetRank.contactMap (K := K) m
      (coefficientLocal e m (nodes n) (u0 n) (u1 n) c.val)=0 at hz
    have hc' : Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (coefficientLocal e m (nodes n) (u0 n) (u1 n) c.val) :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hz
    have hh := untruncate_contact (SecondJetLocal.contact (K := K)).toRingHom
      Polynomial.X m _ SecondJetLocal.contact_X hc'
    exact SecondJetGlobalDifferentiation.nested_to_flat_contact _ m hh

end
end ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.MovingSourceClearing6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open MvPolynomial RCN095 RCN136 RCN207
open SecondJetCoefficients SecondJetClearedHelper

section Polynomial
variable {R : Type*} [CommRing R]

def targetPolynomial (P : Polynomial R) (n : ℕ) (h q : R) : Polynomial R :=
  cleared (P.map Polynomial.C) n (Polynomial.C h) (Polynomial.X-Polynomial.C q)

def inverseSubstitution (h q : R) : Polynomial R →+* Polynomial R :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C h*Polynomial.X+Polynomial.C q)

theorem inverseSubstitution_C (h q a : R) :
    inverseSubstitution h q (Polynomial.C a)=Polynomial.C a := by
  simp [inverseSubstitution]

theorem inverseSubstitution_target (P : Polynomial R) (n : ℕ) (h q : R)
    (hn : P.natDegree ≤ n) :
    inverseSubstitution h q (targetPolynomial P n h q)=(Polynomial.C h)^n*P := by
  have hc : (inverseSubstitution h q).comp Polynomial.C=Polynomial.C := by
    apply RingHom.ext
    intro a
    exact inverseSubstitution_C h q a
  rw [targetPolynomial,map_cleared,Polynomial.map_map,hc]
  simp only [inverseSubstitution_C,map_sub]
  have hx : inverseSubstitution h q Polynomial.X-Polynomial.C q=Polynomial.C h*Polynomial.X := by
    simp [inverseSubstitution]
  rw [hx,cleared_eval (P.map Polynomial.C) n (Polynomial.natDegree_map_le.trans hn)
    (Polynomial.C h) (Polynomial.C h*Polynomial.X) Polynomial.X rfl]
  rw [Polynomial.eval_map,Polynomial.eval₂_C_X]

theorem eval_targetPolynomial {S : Type*} [CommRing S] (f : R →+* S)
    (P : Polynomial R) (n : ℕ) (h q : R) (t : S) :
    Polynomial.eval₂ f t (targetPolynomial P n h q)=
      cleared (P.map f) n (f h) (t-f q) := by
  change (Polynomial.eval₂RingHom f t) (targetPolynomial P n h q)=_
  have hc : (Polynomial.eval₂RingHom f t).comp Polynomial.C=f := by
    apply RingHom.ext
    intro a
    simp
  rw [targetPolynomial,map_cleared,Polynomial.map_map]
  rw [hc]
  simp

end Polynomial

section Surface
variable {K E : Type*} [Field K] [Field E]
local notation "Poly3" => MvPolynomial (Fin 3) E

def coefficients (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K)) :
    Polynomial Poly3 := (asS P).map (surfaceMap phi)

def movingCut (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (s : ℕ) (Q A : Poly3) (target : E) : Poly3 :=
  cleared (coefficients phi P) s (2*A) (MvPolynomial.C target-Q)

theorem twice_linear_flag (A : Poly3) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag unitYZFlag (2*A) := by
  intro e he
  have he' : e ∈ ((2 : E) • A).support := by
    simpa only [MvPolynomial.smul_eq_C_mul,map_ofNat] using he
  exact hA e (MvPolynomial.support_smul he')

end Surface
end
end ProximityPrize.SubmissionLower.MovingSourceClearing6814
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.MovingSourceProperness6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MovingSourceClearing6814

section GCD
variable {A : Type*} [CommMonoidWithZero A] [GCDMonoid A]

theorem common_dvd_scalar (a p q d : A) (h : IsRelPrime p q)
    (hp : d ∣ a*p) (hq : d ∣ a*q) : d ∣ a := by
  have hg : IsUnit (gcd p q) := h (gcd_dvd_left p q) (gcd_dvd_right p q)
  have hh : d ∣ a*gcd p q := (dvd_gcd hp hq).trans (gcd_mul_left' a p q).dvd
  exact hg.dvd_mul_right.mp hh

end GCD

section Polynomial
variable {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid (Polynomial R)]

theorem inverseSubstitution_degree (P : Polynomial R) (h q : R) (hh : h≠0) :
    (inverseSubstitution h q P).natDegree=P.natDegree := by
  change (P.comp (Polynomial.C h*Polynomial.X+Polynomial.C q)).natDegree=P.natDegree
  rw [Polynomial.natDegree_comp,Polynomial.natDegree_add_C,
    Polynomial.natDegree_C_mul_X h hh,mul_one]

theorem targetPolynomial_ne_zero (P : Polynomial R) (n : ℕ) (h q : R)
    (hP : P≠0) (hn : P.natDegree ≤ n) (hh : h≠0) : targetPolynomial P n h q≠0 := by
  intro hz
  have he := inverseSubstitution_target P n h q hn
  rw [hz,map_zero] at he
  exact mul_ne_zero (pow_ne_zero n (Polynomial.C_ne_zero.mpr hh)) hP he.symm

theorem common_prime_dvd_denominator (P Q : Polynomial R) (n m : ℕ) (h q : R)
    (hn : P.natDegree ≤ n) (hm : Q.natDegree ≤ m) (hh : h≠0)
    (hrel : IsRelPrime P Q) (D : Polynomial R) (hD : Prime D)
    (hDP : D ∣ targetPolynomial P n h q)
    (hDQ : D ∣ targetPolynomial Q m h q) : D ∣ Polynomial.C h := by
  by_contra hnot
  have hp := map_dvd (inverseSubstitution h q) hDP
  have hq := map_dvd (inverseSubstitution h q) hDQ
  rw [inverseSubstitution_target P n h q hn] at hp
  rw [inverseSubstitution_target Q m h q hm] at hq
  have hp' : inverseSubstitution h q D ∣ (Polynomial.C h)^(n+m)*P := by
    apply hp.trans
    refine ⟨(Polynomial.C h)^m,?_⟩
    rw [pow_add]; ring
  have hq' : inverseSubstitution h q D ∣ (Polynomial.C h)^(n+m)*Q := by
    apply hq.trans
    refine ⟨(Polynomial.C h)^n,?_⟩
    rw [pow_add]; ring
  have hscalar := common_dvd_scalar ((Polynomial.C h)^(n+m)) P Q
    (inverseSubstitution h q D) hrel hp' hq'
  have hdegree := Polynomial.natDegree_le_of_dvd hscalar
    (pow_ne_zero (n+m) (Polynomial.C_ne_zero.mpr hh))
  rw [inverseSubstitution_degree D h q hh] at hdegree
  have hdegree0 : D.natDegree=0 := by
    simpa using Nat.eq_zero_of_le_zero (by simpa using hdegree)
  have hconstant := Polynomial.eq_C_of_natDegree_eq_zero hdegree0
  have hinverse : inverseSubstitution h q D=D := by
    rw [hconstant,inverseSubstitution_C]
  rw [hinverse] at hp hq
  have hnp : ¬ D ∣ (Polynomial.C h)^n := fun hpow => hnot (hD.dvd_of_dvd_pow hpow)
  have hnq : ¬ D ∣ (Polynomial.C h)^m := fun hpow => hnot (hD.dvd_of_dvd_pow hpow)
  have hdP : D ∣ P := (hD.dvd_or_dvd hp).resolve_left hnp
  have hdQ : D ∣ Q := (hD.dvd_or_dvd hq).resolve_left hnq
  exact hD.irreducible.not_isUnit (hrel hdP hdQ)

end Polynomial

end
end ProximityPrize.SubmissionLower.MovingSourceProperness6814
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.MovingSourceFlatBaseChange6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open UniqueFactorizationMonoid

section Flat
variable {A B : Type*} [CommRing A] [IsDomain A]
  [UniqueFactorizationMonoid A]
  [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B] [IsNoetherianRing B]
  [Algebra A B] [Module.Flat A B]

theorem map_isRelPrime_of_flat (hinj : Function.Injective (algebraMap A B))
    (P Q : A) (hP : P≠0) (hrel : IsRelPrime P Q) :
    IsRelPrime (algebraMap A B P) (algebraMap A B Q) := by
  classical
  apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
  · rintro ⟨hz,_⟩
    exact hP (hinj (by simpa only [map_zero] using hz))
  intro g hg hgP hgQ
  let I : Ideal B := Ideal.span {g}
  haveI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hg.prime
  let psi : A →+* B ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap A B)
  have hz : psi P=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hgP)
  obtain ⟨factors,hfactors,hprod⟩ := WfDvdMonoid.exists_factors P hP
  have hassoc := Associated.map psi hprod
  rw [hz] at hassoc
  have hp : psi factors.prod=0 := (associated_zero_iff_eq_zero _).mp hassoc
  rw [map_multiset_prod] at hp
  obtain ⟨f,hf,hfzero⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  have hfi : Irreducible f := hfactors f hf
  have hgf : g ∣ algebraMap A B f :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hfzero)
  have he := RCN350.under_prime_factor_eq hinj f hfi.prime g hg.prime hgf
  have hQmem : Q ∈ (Ideal.span ({g} : Set B)).under A := Ideal.mem_span_singleton.mpr hgQ
  rw [he] at hQmem
  exact hfi.not_isUnit (hrel ((Multiset.dvd_prod hf).trans hprod.dvd) (Ideal.mem_span_singleton.mp hQmem))

end Flat

section Coefficients
variable {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat R S]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_map_flat : Module.Flat (MvPolynomial σ R) (MvPolynomial σ S) := by
  exact Module.Flat.of_linearEquiv
    (Algebra.IsPushout.equiv R (MvPolynomial σ R) S (MvPolynomial σ S)).symm.toLinearEquiv

end Coefficients

section Equivalence
variable {A B : Type*} [CommRing A] [CommRing B]

theorem isRelPrime_equiv (e : A ≃+* B) (P Q : A) (h : IsRelPrime P Q) :
    IsRelPrime (e P) (e Q) := by
  intro d hdP hdQ
  have hP := map_dvd e.symm hdP
  have hQ := map_dvd e.symm hdQ
  simp only [RingEquiv.symm_apply_apply] at hP hQ
  have hu := (h hP hQ).map e.toMonoidHom
  change IsUnit (e (e.symm d)) at hu
  simpa only [RingEquiv.apply_symm_apply] using hu

end Equivalence

end
end ProximityPrize.SubmissionLower.MovingSourceFlatBaseChange6814
end MergedPart11
