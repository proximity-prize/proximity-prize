import ProximityPrize.SubmissionLower.RecoveryCore00
set_option autoImplicit false
set_option linter.all false
set_option Elab.async true
section
set_option linter.all false

section Compact_PackedLocatorTail

section PackedLocator_ChainAmort

open Finset

namespace ChainAmort

end ChainAmort

namespace ChainAmort

end ChainAmort

namespace ChainAmort

end ChainAmort

namespace ChainGroupMaj
open ProximityPrize.SubmissionLower.RCN260 ProximityPrize.SubmissionLower.RCN294

end ChainGroupMaj

end PackedLocator_ChainAmort

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorNestedProjection
namespace ProximityPrize.SubmissionLower.IL
open scoped BigOperators
open RCN081 RCN156 RCN180 RCN234
noncomputable section
variable {K:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K
def FDR (D w T YS S:ℕ):Set (Fin 4→₀ ℕ):=
  {d | d 1+d 2+d 3≤T∧d 1+d 2≤YS∧d 2≤S∧
    d 0+w*d 1+(w-1)*d 2<D}
def PQ (K:Type*) [Field K] (D w T YS S:ℕ):
    Submodule K (MvPolynomial (Fin 4) K):=
  MvPolynomial.restrictSupport K (FDR D w T YS S)

def ADH (f:ℕ→ℕ):ℕ→ℕ:=KernelEval.sumRange f

theorem BKB (f:ℕ→ℕ) (n:ℕ):
    ADH f (n+1)=ADH f n+f n:=by
  exact KernelEval.FSU f n

theorem VJ (f:ℕ→ℕ) (n:ℕ):
    ADH f n= ∑ i ∈ Finset.range n,f i:=by
  exact KernelEval.sumRange_eq f n

theorem FGL (a m:ℕ) (h:m≤a):
    ∑ r ∈ Finset.range (m+1),(a-r)=
      (m+1)*a-(m+1)*m/2:=by
  exact KernelEval.sum_range_sub a m h

def channelCount (T YS S:ℕ):ℕ:=
  ADH (fun y=>
    let M:=min S (min (T-y) (YS-y))
    (M+1)*(T+1-y)-(M+1)*M/2) (min T YS+1)

theorem EJB (T YS S:ℕ):
    channelCount T YS S=
      ∑ y ∈ Finset.range (min T YS+1),
        ∑ r ∈ Finset.range (min S (min (T-y) (YS-y))+1),
          (T+1-y-r):=by
  rw [channelCount,VJ]
  refine Finset.sum_congr rfl (fun y _=> ?_)
  let M:=min S (min (T-y) (YS-y))
  have hM:M≤T+1-y:=by
    have hMT:M≤T-y:=by
      exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    omega
  simpa [M] using (FGL (T+1-y) M hM).symm
abbrev BXU (delta T YS S:ℕ):=
  (y:Fin (min T YS+1)) ×
    (r:Fin (min S (min (T-y.val) (YS-y.val))+1)) ×
      (Fin (T+1-y.val-r.val) × Fin delta)
theorem EMV (delta T YS S:ℕ):
    Fintype.card (BXU delta T YS S)=delta*channelCount T YS S:=by
  rw [EJB]
  simp [BXU,Fintype.card_sigma,
    Finset.sum_range,Finset.mul_sum,Nat.mul_comm]
def DHI (w Dlow:ℕ) {delta T YS S:ℕ}
    (c:BXU delta T YS S):Fin 4→₀ ℕ:=
  Finsupp.single 0 (Dlow-w*c.1.val-(w-1)*c.2.1.val+c.2.2.2.val)+
    Finsupp.single 1 c.1.val+Finsupp.single 2 c.2.1.val+
      Finsupp.single 3 c.2.2.1.val
def highBandMap (w Dlow delta T YS S:ℕ):
    MvPolynomial (Fin 4) K→ₗ[K] (BXU delta T YS S→K):=
  LinearMap.pi (fun c=>MvPolynomial.lcoeff K (DHI w Dlow c))
@[simp] theorem FQS (w Dlow delta T YS S:ℕ)
    (P:MvPolynomial (Fin 4) K) (c:BXU delta T YS S):
    highBandMap w Dlow delta T YS S P c=
      AddMonoidAlgebra.coeff P (DHI w Dlow c):=rfl
theorem ESW {D w T YS S:ℕ} {P:MvPolynomial (Fin 4) K}
    (hP:P ∈ PQ K D w T YS S):
    P ∈ RCN100.BA K D w T S:=by
  intro d hd
  have h:=hP hd
  exact ⟨h.1,h.2.2.1,h.2.2.2⟩
theorem DLI {D w T YS S:ℕ} {P:MvPolynomial (Fin 4) K}
    (hP:P ∈ PQ K D w T YS S) (hne:P ≠ 0):
    wt AT P≤T∧wt BC P≤YS∧
      wt BE P≤S∧wt (BV w) P<D:=by
  have hD:0<D:=by
    obtain ⟨d,hd⟩:=MvPolynomial.support_nonempty.mpr hne
    have h:=(hP hd).2.2.2
    omega
  have h:=(JT P D w T S hD).mp
    (ESW hP)
  refine ⟨h.1,?_,h.2.1,by omega⟩
  apply (KN BC P YS).mpr
  intro d hd
  have hdYS:=(hP hd).2.1
  rw [weight_fin4]
  simpa [BC] using hdYS
theorem EQT (D w L s YS:ℕ) (hw:1≤w)
    (hshape:D+s≤w*(YS+1)) (P:MvPolynomial (Fin 4) K)
    (hP:P ∈ RCN100.BA K D w L s):
    wt BC P≤YS:=by
  apply (KN BC P YS).mpr
  intro d hd
  have hs:=(hP hd).2.1
  have hc:=(hP hd).2.2
  have hwr:w*d 2=(w-1)*d 2+d 2:=by
    calc
      w*d 2=((w-1)+1)*d 2:=by rw [Nat.sub_add_cancel hw]
      _=(w-1)*d 2+d 2:=by ring
  have hm:w*(d 1+d 2)<w*(YS+1):=by
    rw [Nat.mul_add,hwr]
    omega
  have hlt:d 1+d 2<YS+1:=
    (Nat.mul_lt_mul_left (by omega:0<w)).mp hm
  rw [weight_fin4]
  simpa [BC] using (Nat.le_of_lt_succ hlt)
section LinearSelection
variable {V:Type*} [AddCommGroup V] [Module K V]
end LinearSelection
end
end ProximityPrize.SubmissionLower.IL
end PackedLocator_LocatorNestedProjection

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorContact
namespace ProximityPrize.SubmissionLower.FKN
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN122 RCN156 RCN180 RCN234 RCN313 BY
noncomputable section
variable {K I:Type*} [Field K] [Fintype I]
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
abbrev P4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
theorem EWS (weights:Fin 4→ℕ) (Q:P4 K)
    (hder:MvPolynomial.pderiv (2:Fin 4) Q ≠ 0):
    wt weights (MvPolynomial.pderiv (2:Fin 4) Q)+weights 2≤wt weights Q:=by
  classical
  obtain ⟨d,hd,heq⟩:=Finset.exists_mem_eq_sup
    (MvPolynomial.pderiv (2:Fin 4) Q).support
    (MvPolynomial.support_nonempty.mpr hder) (Finsupp.weight weights)
  have hbefore:=AFO (2:Fin 4) Q d hd
  have hbound:=MvPolynomial.le_weightedTotalDegree weights hbefore
  change wt weights (MvPolynomial.pderiv (2:Fin 4) Q)=
    Finsupp.weight weights d at heq
  rw [heq]
  simpa only [wt,map_add,Finsupp.weight_single,one_nsmul] using hbound
end
end ProximityPrize.SubmissionLower.FKN
end PackedLocator_LocatorContact

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorLowQuotient
namespace ProximityPrize.SubmissionLower.IL
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
variable {K I:Type*} [Field K] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
theorem CBL
    (D w L s m c t r:ℕ) (nodes u0 u1:I→K)
    (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hdiv:∀v:IJ (K:=K) D w L s m nodes u0 u1,
      F ∣ LZ (K:=K) D w L s m nodes u0 u1 v)
    (hc:c≤wt (BV w) F)
    (ht:t≤wt AT F) (hr:r≤wt BE F):
    ∀v:IJ (K:=K) D w L s m nodes u0 u1,
      ZK (LZ (K:=K) D w L s m nodes u0 u1)
        F hdiv v ∈ BA K (D-c) w (L-t) (s-r):=by
  let recon:=LZ (K:=K) D w L s m nodes u0 u1
  intro v
  by_cases hv:v=0
  · subst v
    have hz:ZK recon F hdiv 0=0:=
      (ARF recon F hF hdiv).map_zero
    rw [hz]
    exact (BA K _ _ _ _).zero_mem
  · have hQ:recon v ≠ 0:=by
      intro hz
      apply hv
      apply APB (K:=K) D w L s m nodes u0 u1
      simpa only [map_zero] using hz
    have heq:=LR recon F hdiv v
    have hq:ZK recon F hdiv v ≠ 0:=by
      intro hz
      exact hQ (by rw [heq,hz,mul_zero])
    have hReconBox:recon v ∈ BA K D w L s:=by
      change reconstruct K D w L s v.1 ∈ BA K D w L s
      exact LG K D w L s v.1
    exact ZP
      (recon v) F (ZK recon F hdiv v)
      D w L s c t r hQ hF hq hReconBox heq hc ht hr
end
end ProximityPrize.SubmissionLower.IL
end PackedLocator_LocatorLowQuotient

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorFifthPowerAvoidance

namespace ProximityPrize.SubmissionLower.KI
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
  UniqueFactorizationMonoid.strongNormalizationMonoid
private theorem AMN
    (H:MvPolynomial (Fin 4) K) (F:RCN266.RegularIndex H):
    F.1 ∈ normalizedFactors H:=by
  have hactive:F.1 ∈ RCN082.HR H:=
    (Finset.mem_filter.mp F.2).1
  have hnf:F.1 ∈ (normalizedFactors H).toFinset:=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf
def EBE (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):RCN052.RegularIndex F.1:=by
  have hF:=RCN167.KR H F.1 F.2
  refine ⟨F.1,?_⟩
  change F.1 ∈ (RCN082.HR F.1).filter (fun G=>0<G.degreeOf 2)
  refine Finset.mem_filter.mpr ⟨?_,hF.2.2⟩
  change F.1 ∈ (normalizedFactors F.1).toFinset.filter
    (fun G=>0<G.degreeOf 1+G.degreeOf 2+G.degreeOf 3)
  refine Finset.mem_filter.mpr ⟨?_,by omega⟩
  apply Multiset.mem_toFinset.mpr
  rw [normalizedFactors_irreducible hF.1,
    normalize_normalized_factor F.1 (AMN H F)]
  exact Multiset.mem_singleton_self _
@[simp] theorem ASI (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):(EBE H F).1=F.1:=rfl
theorem CRA (P:DG)
    (F:MvPolynomial (Fin 4) K)
    (hY:F.degreeOf 1≤P.leftY) (hR:F.degreeOf 2≤P.leftR)
    (hZ:F.degreeOf 3≤P.leftZ):
    (RCN052.OX P F).y≤P.mixedCost.y∧
      (RCN052.OX P F).r≤P.mixedCost.r∧
      (RCN052.OX P F).z≤P.mixedCost.z:=by
  exact ⟨Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hR)
      (Nat.mul_le_mul_right P.rightR hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hY)
      (Nat.mul_le_mul_right P.rightY hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightR hY)
      (Nat.mul_le_mul_right P.rightY hR)⟩
end
end ProximityPrize.SubmissionLower.KI

namespace ProximityPrize.SubmissionLower.ABI

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open IL KI

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

variable {K V I:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K

theorem BPI
    (P F Q:MvPolynomial (Fin 4) K) (D w T YS S:ℕ)
    (hP:P ≠ 0) (hF:F ≠ 0) (hQ:Q ≠ 0)
    (hbox:P ∈ PQ K D w T YS S)
    (heq:P=F*Q):
    Q ∈ PQ K
      (D-wt (BV w) F) w
      (T-wt AT F) (YS-wt BC F)
      (S-wt BE F):=by
  have hglobal:
      Q ∈ BA K
        (D-wt (BV w) F) w
        (T-wt AT F) (S-wt BE F):=
    ZP P F Q D w T S
      (wt (BV w) F) (wt AT F)
      (wt BE F) hP hF hQ (ESW hbox) heq
      le_rfl le_rfl le_rfl
  have hPYS:wt BC P≤YS:=
    (DLI hbox hP).2.1
  have hmul:=UP BC F Q hF hQ
  have hsum:wt BC F+wt BC Q≤YS:=by
    change MvPolynomial.weightedTotalDegree BC F+
      MvPolynomial.weightedTotalDegree BC Q≤YS
    rw [← hmul,← heq]
    exact hPYS
  have hQYS:wt BC Q≤YS-wt BC F:=by
    omega
  intro d hd
  have hb:=hglobal hd
  have hy:=MvPolynomial.le_weightedTotalDegree BC hd
  rw [weight_fin4] at hy
  simp only [wt] at hQYS
  simp only [BC] at hy ⊢
  refine ⟨hb.1,?_,hb.2.1,hb.2.2⟩
  change d 1+d 2≤YS-
    MvPolynomial.weightedTotalDegree BC F
  simpa [BC] using hy.trans hQYS

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section SecondDerivative

variable [Fintype I]
local instance:DecidableEq I:=Classical.decEq I

end SecondDerivative

end

end ProximityPrize.SubmissionLower.ABI

namespace ProximityPrize.SubmissionLower.EHJ

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open IL KI
open ABI

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

variable {K V I:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section ThirdDerivative

variable [Fintype I]
local instance:DecidableEq I:=Classical.decEq I

end ThirdDerivative

end

end ProximityPrize.SubmissionLower.EHJ

namespace ProximityPrize.SubmissionLower.EDG

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open IL KI
open ABI

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

variable {K V I:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section FourthDerivative

variable [Fintype I]
local instance:DecidableEq I:=Classical.decEq I

end FourthDerivative

end

end ProximityPrize.SubmissionLower.EDG

namespace ProximityPrize.SubmissionLower.EHD

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open IL KI
open ABI

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

variable {K V I:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section FifthDerivative

variable [Fintype I]
local instance:DecidableEq I:=Classical.decEq I

end FifthDerivative

end

end ProximityPrize.SubmissionLower.EHD
end PackedLocator_LocatorFifthPowerAvoidance

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorQuotientMonotone
namespace ProximityPrize.SubmissionLower.IL
open scoped BigOperators
theorem DUP {T T' YS YS' S S':ℕ}
    (ht:T≤T') (hy:YS≤YS') (hs:S≤S'):
    channelCount T YS S≤channelCount T' YS' S':=by
  rw [EJB,EJB]
  calc
    _≤ ∑ y ∈ Finset.range (min T YS+1),
        ∑ r ∈ Finset.range (min S' (min (T' -y) (YS' -y))+1),
          (T' +1-y-r):=by
      apply Finset.sum_le_sum
      intro y _
      have hin:Finset.range (min S (min (T-y) (YS-y))+1) ⊆
          Finset.range (min S' (min (T'-y) (YS'-y))+1):=by
        apply Finset.range_mono
        have h:=min_le_min hs
          (min_le_min (Nat.sub_le_sub_right ht y) (Nat.sub_le_sub_right hy y))
        omega
      exact (Finset.sum_le_sum (fun r _=>by omega)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hin (fun _ _ _=>Nat.zero_le _))
    _≤_:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.add_le_add_right (min_le_min ht hy) 1)
      · intro _ _ _
        exact Nat.zero_le _
end ProximityPrize.SubmissionLower.IL
end PackedLocator_LocatorQuotientMonotone

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorArbitraryPowerAvoidance

namespace ProximityPrize.SubmissionLower.CS

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open IL KI ABI

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K V:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K

def LH
    (delta dT dY dS T YS S:ℕ):ℕ→ℕ
  | 0=>0
  | k+1=>
      delta*channelCount T YS S+
        LH delta dT dY dS
          (T-dT) (YS-dY) (S-dS) k

theorem BRL
    (delta dT₁ dY₁ dS₁ T₁ Y₁ S₁ dT₂ dY₂ dS₂ T₂ Y₂ S₂ k:ℕ)
    (hT:T₁≤T₂) (hY:Y₁≤Y₂) (hS:S₁≤S₂)
    (hdT:dT₂≤dT₁) (hdY:dY₂≤dY₁)
    (hdS:dS₂≤dS₁):
    LH delta dT₁ dY₁ dS₁ T₁ Y₁ S₁ k≤
      LH delta dT₂ dY₂ dS₂ T₂ Y₂ S₂ k:=by
  induction k generalizing T₁ Y₁ S₁ T₂ Y₂ S₂ with
  | zero=>
      simp only [LH]
      exact Nat.zero_le _
  | succ k ih=>
      simp only [LH]
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left delta (DUP hT hY hS)
      · apply ih
        · omega
        · omega
        · omega

def thinTop (w Dhigh S:ℕ):ℕ:=(Dhigh+S-1)/w

theorem thinTop_mono {w D D' S S' :ℕ} (hD:D≤D') (hS:S≤S'):
    thinTop w D S≤thinTop w D' S' :=
  Nat.div_le_div_right (by omega)

theorem GVM (Dhigh w T YS S:ℕ) (hw:1≤w) (d:Fin 4→₀ ℕ)
    (hd:d ∈ FDR Dhigh w T YS S):
    d 1+d 2≤thinTop w Dhigh S:=by
  rcases hd with ⟨_,_,hS,hD⟩
  have hwr:w*d 2=(w-1)*d 2+d 2:=by
    calc
      w*d 2=((w-1)+1)*d 2:=by rw [Nat.sub_add_cancel hw]
      _=(w-1)*d 2+d 2:=by ring
  have hmul:(d 1+d 2)*w≤Dhigh+S-1:=by
    rw [Nat.mul_comm,Nat.mul_add,hwr]
    omega
  exact (Nat.le_div_iff_mul_le (by omega)).mpr hmul

theorem BGZ
    (Dhigh Dlow w delta T YS S:ℕ) (hw:1≤w)
    (hwidth:Dhigh≤Dlow+delta) (P:MvPolynomial (Fin 4) K)
    (hP:P ∈ PQ K Dhigh w T YS S)
    (hzero:highBandMap w Dlow delta T (min YS (thinTop w Dhigh S)) S P=0):
    P ∈ PQ K Dlow w T YS S:=by
  intro d hd
  rcases hP hd with ⟨hT,hYS,hS,hD⟩
  have htop:=GVM Dhigh w T YS S hw d ⟨hT,hYS,hS,hD⟩
  refine ⟨hT,hYS,hS,?_⟩
  by_contra hnot
  have hy:d 1<min T (min YS (thinTop w Dhigh S))+1:=by omega
  have hr:d 2<min S (min (T-d 1) (min YS (thinTop w Dhigh S)-d 1))+1:=by
    omega
  have hz:d 3<T+1-d 1-d 2:=by omega
  have hstart:Dlow-w*d 1-(w-1)*d 2≤d 0:=by omega
  have hx:d 0-(Dlow-w*d 1-(w-1)*d 2)<delta:=by omega
  let c:BXU delta T (min YS (thinTop w Dhigh S)) S:=
    ⟨⟨d 1,hy⟩,⟨⟨d 2,hr⟩,
      ⟨⟨d 3,hz⟩,⟨d 0-(Dlow-w*d 1-(w-1)*d 2),hx⟩⟩⟩⟩
  have he:DHI w Dlow c=d:=by
    ext i
    fin_cases i<;>simp [DHI,c]<;>omega
  have hc:=congrFun hzero c
  have hcoeff:AddMonoidAlgebra.coeff P d=0:=by
    simpa only [FQS,he,Pi.zero_apply] using hc
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff

theorem FAK (w:ℕ) (hw:1≤w) (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0):
    w*wt BC F-wt BE F≤
      wt (BV w) F:=by
  obtain ⟨d,hd,hsup⟩:=Finset.exists_mem_eq_sup F.support
    (MvPolynomial.support_nonempty.mpr hF) (Finsupp.weight BC)
  have hys:wt BC F=d 1+d 2:=by
    change MvPolynomial.weightedTotalDegree BC F=d 1+d 2
    rw [MvPolynomial.weightedTotalDegree,hsup,weight_fin4]
    simp [BC]
  have hs:d 2≤wt BE F:=by
    have h:=MvPolynomial.le_weightedTotalDegree BE hd
    rw [weight_fin4] at h
    change d 0*0+d 1*0+d 2*1+d 3*0≤wt BE F at h
    omega
  have hc:d 0+w*d 1+(w-1)*d 2≤wt (BV w) F:=by
    have h:=MvPolynomial.le_weightedTotalDegree (BV w) hd
    rw [BBL] at h
    exact h
  have hwr:w*d 2=(w-1)*d 2+d 2:=by
    calc
      w*d 2=((w-1)+1)*d 2:=by rw [Nat.sub_add_cancel hw]
      _=(w-1)*d 2+d 2:=by ring
  rw [hys,Nat.mul_add,hwr]
  omega

def HN
    (w Dh delta dc dT dY dS T YS S:ℕ):ℕ→ℕ
  | 0=>0
  | k+1=>
      delta*channelCount T (min YS (thinTop w Dh S)) S+
        HN w (Dh-delta-dc) delta dc dT dY dS
          (T-dT) (YS-dY) (S-dS) k

theorem CCZ (w delta dc dT dY dS:ℕ):
    ∀(k Dh T YS S:ℕ),
      HN w Dh delta dc dT dY dS T YS S k≤
        LH delta dT dY dS T YS S k:=by
  intro k
  induction k with
  | zero=>intro _ _ _ _;simp [HN,LH]
  | succ k ih=>
      intro Dh T YS S
      simp only [HN,LH]
      exact Nat.add_le_add
        (Nat.mul_le_mul_left delta
          (DUP le_rfl (Nat.min_le_left _ _) le_rfl))
        (ih _ _ _ _)

theorem AZD (w delta:ℕ):
    ∀(k Dh₁ dc₁ dT₁ dY₁ dS₁ T₁ Y₁ S₁ Dh₂ dc₂ dT₂ dY₂ dS₂ T₂ Y₂ S₂:ℕ),
      Dh₁≤Dh₂→dc₂≤dc₁→T₁≤T₂→Y₁≤Y₂→S₁≤S₂→
      dT₂≤dT₁→dY₂≤dY₁→dS₂≤dS₁→
      HN w Dh₁ delta dc₁ dT₁ dY₁ dS₁ T₁ Y₁ S₁ k≤
        HN w Dh₂ delta dc₂ dT₂ dY₂ dS₂ T₂ Y₂ S₂ k:=by
  intro k
  induction k with
  | zero=>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      simp [HN]
  | succ k ih=>
      intro Dh₁ dc₁ dT₁ dY₁ dS₁ T₁ Y₁ S₁ Dh₂ dc₂ dT₂ dY₂ dS₂ T₂ Y₂ S₂
        hD hdc hT hY hS hdT hdY hdS
      simp only [HN]
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left delta
          (DUP hT (min_le_min hY (thinTop_mono hD hS)) hS)
      · apply ih
        · omega
        · exact hdc
        · omega
        · omega
        · omega
        · exact hdT
        · exact hdY
        · exact hdS

theorem ECT
    (w Dh delta dc dT dY dS T YS S k:ℕ):
    HN w Dh delta dc dT dY dS T YS S k≤
      HN w Dh delta dc dT dY dS T YS S (k+1):=by
  induction k generalizing Dh T YS S with
  | zero=>
      simp only [HN]
      exact Nat.zero_le _
  | succ k ih=>
      simp only [HN]
      exact Nat.add_le_add_left (ih _ _ _ _) _

theorem DUI
    (w Dh delta dc dT dY dS T YS S:ℕ) {k₁ k₂:ℕ} (hk:k₁≤k₂):
    HN w Dh delta dc dT dY dS T YS S k₁≤
      HN w Dh delta dc dT dY dS T YS S k₂:=by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hk
  induction d with
  | zero=>simp
  | succ d ih=>
      calc
        HN w Dh delta dc dT dY dS T YS S k₁≤
            HN w Dh delta dc dT dY dS T YS S (k₁+d):=
          ih (Nat.le_add_right _ _)
        _≤HN w Dh delta dc dT dY dS T YS S ((k₁+d)+1):=
          ECT w Dh delta dc dT dY dS T YS S (k₁+d)
        _=HN w Dh delta dc dT dY dS T YS S (k₁+d.succ):=by
          congr 1

end

end ProximityPrize.SubmissionLower.CS
end PackedLocator_LocatorArbitraryPowerAvoidance

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorArbitraryPowerContact

namespace ProximityPrize.SubmissionLower.TB

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open IL

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K I:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K

abbrev P4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K

def NY (j:ℕ) (Q:P4 K):P4 K:=
  (fun H:P4 K=>MvPolynomial.pderiv (2:Fin 4) H)^[j] Q

@[simp] theorem EEE (Q:P4 K):
    NY 0 Q=Q:=rfl

theorem APD (j:ℕ) (Q:P4 K):
    NY (j+1) Q=
      MvPolynomial.pderiv (2:Fin 4) (NY j Q):=by
  simp only [NY,Function.iterate_succ_apply']

@[simp] theorem EON (j:ℕ):
    NY (K:=K) j 0=0:=by
  induction j with
  | zero=>rfl
  | succ j ih=>
      rw [APD,ih,map_zero]

theorem DUS
    (x u0 u1:K) (m j:ℕ) (Q:P4 K)
    (hQ:BY.VE K x u0 u1 m Q):
    BY.VE K x u0 u1 (m-j)
      (NY j Q):=by
  induction j with
  | zero=>simpa only [EEE,Nat.sub_zero] using hQ
  | succ j ih=>
      rw [APD]
      have hnext:=BY.DKX
        K x u0 u1 (m-j) (NY j Q) ih
      simpa only [Nat.sub_sub] using hnext

theorem BRN
    (Q:P4 K) (j:ℕ)
    (hne:NY (j+1) Q ≠ 0):
    NY j Q ≠ 0:=by
  intro hz
  apply hne
  rw [APD,hz,map_zero]

theorem DWZ
    (weights:Fin 4→ℕ) (Q:P4 K) (j:ℕ)
    (hne:NY j Q ≠ 0):
    wt weights (NY j Q)+j*weights 2≤wt weights Q:=by
  induction j with
  | zero=>
      simp only [EEE,Nat.zero_mul,Nat.add_zero]
      exact le_rfl
  | succ j ih=>
      have hprev:NY j Q ≠ 0:=
        BRN Q j (by
          simpa only [Nat.succ_eq_add_one] using hne)
      have hstepNe:
          MvPolynomial.pderiv (2:Fin 4) (NY j Q) ≠ 0:=by
        simpa only [Nat.succ_eq_add_one,APD] using hne
      have hstep:=FKN.EWS
        weights (NY j Q) hstepNe
      calc
        wt weights (NY (Nat.succ j) Q)+
              Nat.succ j*weights 2=
            (wt weights (MvPolynomial.pderiv (2:Fin 4)
              (NY j Q))+weights 2)+j*weights 2:=by
              simp only [Nat.succ_eq_add_one,APD,
                Nat.add_mul,one_mul]
              ac_rfl
        _≤wt weights (NY j Q)+j*weights 2:=
          Nat.add_le_add_right hstep _
        _≤wt weights Q:=ih hprev

theorem DXF
    (weights:Fin 4→ℕ) (Q:P4 K) (j d:ℕ)
    (hne:NY j Q ≠ 0)
    (hQ:wt weights Q≤d):
    wt weights (NY j Q)≤d-j*weights 2:=by
  exact Nat.le_sub_of_add_le
    ((DWZ weights Q j hne).trans hQ)

section KernelVanishing

variable [Fintype I]
local instance:DecidableEq I:=Classical.decEq I

theorem AUM
    (j D Dlow w L s m:ℕ) (nodes:I ↪ K) (u0 u1:I→K)
    (v:IJ (K:=K) D w L s m nodes u0 u1)
    (hlow:reconstruct K D w L s v.1 ∈
      BA K Dlow w L s)
    (P:Polynomial K) (gamma:K) (support:Finset I)
    (hj:1≤j) (hw:1≤w) (hP:P.natDegree≤w)
    (hcapacity:Dlow≤(m-j)*support.card+j*(w-1))
    (hvalues: ∀i ∈ support,
      P.eval (nodes i)=u0 i+gamma*u1 i):
    RCN319.BM K P gamma
      (NY j (reconstruct K D w L s v.1))=0:=by
  classical
  cases j with
  | zero=>omega
  | succ k=>
      let H:=reconstruct K D w L s v.1
      by_contra hne
      have hfinal:NY (Nat.succ k) H ≠ 0:=by
        intro hz
        apply hne
        rw [hz,map_zero]
      have hprev:NY k H ≠ 0:=by
        apply BRN H k
        simpa only [Nat.succ_eq_add_one] using hfinal
      have hH:H ≠ 0:=by
        intro hz
        apply hfinal
        rw [hz,EON]
      have hDlow:0<Dlow:=by
        obtain ⟨d,hd⟩:=MvPolynomial.support_nonempty.mpr hH
        have h:=(hlow hd).2.2
        omega
      have hHweight:wt (BV w) H≤Dlow-1:=
        ((JT H Dlow w L s hDlow).mp hlow).2.2
      have hprevWeight:
          wt (BV w) (NY k H)≤
            Dlow-1-k*(w-1):=by
        have hbound:=DXF
          (BV w) H k (Dlow-1) hprev hHweight
        change wt (BV w) (NY k H)≤
          Dlow-1-k*(w-1) at hbound
        exact hbound
      have hregular:RCN319.BM K P gamma
          (MvPolynomial.pderiv (2:Fin 4) (NY k H)) ≠ 0:=by
        simpa only [Nat.succ_eq_add_one,APD] using hne
      have hdegree:=BY.BOO K
        (NY k H) P gamma w
        (Dlow-1-k*(w-1)) hP hprevWeight hregular
      have hdegreeStrict:
          (RCN122.BM K P gamma
            (NY (Nat.succ k) H)).natDegree<
              (m-Nat.succ k)*support.card:=by
        rw [Nat.succ_eq_add_one,APD]
        rw [RCN101.BKH]
        rw [RCN101.BKH] at hdegree
        have hkc:k*(w-1)≤Dlow-1:=by
          by_contra hnot
          have hlt:Dlow-1<k*(w-1):=Nat.lt_of_not_ge hnot
          have hzero:Dlow-1-k*(w-1)=0:=
            Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
          rw [hzero] at hdegree
          have hwOne:w-1=0:=by omega
          rw [hwOne,Nat.mul_zero] at hlt
          omega
        have hsplit:
            (Dlow-1-k*(w-1))+k*(w-1)=Dlow-1:=
          Nat.sub_add_cancel hkc
        have hwSplit:w-1+1=w:=Nat.sub_add_cancel hw
        simp only [Nat.succ_eq_add_one,Nat.add_mul,one_mul] at hcapacity
        omega
      have hcontact: ∀i ∈ support,∀r:ℕ,
          IA K^(m-Nat.succ k-r) ∣
            (RCN122.EM K (nodes i) (u0 i) (u1 i)
              (NY (Nat.succ k) H)).coeff r:=by
        intro i _hi
        apply (BY.QW
          K (nodes i) (u0 i) (u1 i) (m-Nat.succ k) _).mp
        exact DUS
          (nodes i) (u0 i) (u1 i) m (Nat.succ k) H
          (BY.DZA
            K D w L s m nodes u0 u1 v.1 v.2 i)
      have hz:=RCN122.WH K
        (NY (Nat.succ k) H) P gamma nodes u0 u1 support
        (m-Nat.succ k) hcontact hvalues hdegreeStrict
      apply hne
      simpa only [H,RCN101.BKH] using hz

end KernelVanishing

private theorem CTC: ∀{n p:ℕ},
    p.Prime→(p ∣ n.factorial ↔ p≤n)
  | 0,_,hp=>iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
  | n+1,p,hp=>by
      rw [Nat.factorial_succ,hp.dvd_mul,CTC hp]
      exact ⟨fun h=>h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
        fun h=>(_root_.lt_or_eq_of_le h).elim
          (Or.inr ∘ Nat.le_of_lt_succ) fun h=>Or.inl<| by rw [h]⟩

theorem DYA
    (p j:ℕ) [CharP K p] (hp:p.Prime) (hj:j<p):
    (j.factorial:K) ≠ 0:=by
  intro hz
  have hdvd:p ∣ j.factorial:=
    (CharP.cast_eq_zero_iff K p j.factorial).mp hz
  exact (not_le_of_gt hj) ((CTC hp).mp hdvd)

theorem AVQ
    (j:ℕ) (P:Polynomial K) (gamma:K) (F Q:P4 K)
    (hfactorial:(j.factorial:K) ≠ 0)
    (hFzero:RCN319.BM K P gamma F=0)
    (hregular:RCN319.BM K P gamma
      (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0)
    (hpower:RCN319.BM K P gamma
      (NY j (F^j*Q))=0):
    RCN319.BM K P gamma Q=0:=by
  obtain ⟨error,herror⟩:=RCN324.CWT
    (MvPolynomial.pderiv (2:Fin 4)) F Q j j le_rfl
  have hexpansion:
      NY j (F^j*Q)=
        (j.descFactorial j:P4 K)*F^(j-j)*Q*
            (MvPolynomial.pderiv (2:Fin 4) F)^j+
          F^(j-j+1)*error:=by
    simpa only [NY] using herror
  rw [hexpansion] at hpower
  have hmul:
      (j.factorial:Polynomial K)*
          RCN319.BM K P gamma Q*
            (RCN319.BM K P gamma
              (MvPolynomial.pderiv (2:Fin 4) F))^j=0:=by
    simpa only [Nat.descFactorial_self,Nat.sub_self,pow_zero,one_mul,mul_one,
      zero_add,pow_one,map_add,map_mul,map_pow,map_natCast,
      map_one,hFzero,zero_mul,add_zero] using hpower
  have hfactorialPoly:(j.factorial:Polynomial K) ≠ 0:=by
    intro hz
    apply hfactorial
    have heval:=congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hcoef:
      (j.factorial:Polynomial K)*
          (RCN319.BM K P gamma
            (MvPolynomial.pderiv (2:Fin 4) F))^j ≠ 0:=
    mul_ne_zero hfactorialPoly (pow_ne_zero j hregular)
  have hmul' :
      ((j.factorial:Polynomial K)*
          (RCN319.BM K P gamma
            (MvPolynomial.pderiv (2:Fin 4) F))^j)*
        RCN319.BM K P gamma Q=0:=by
    calc
      _=(j.factorial:Polynomial K)*
          RCN319.BM K P gamma Q*
            (RCN319.BM K P gamma
              (MvPolynomial.pderiv (2:Fin 4) F))^j:=by ring
      _=0:=hmul
  exact (mul_eq_zero.mp hmul').resolve_left hcoef

end

end ProximityPrize.SubmissionLower.TB
end PackedLocator_LocatorArbitraryPowerContact

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorTwoFactorAvoidance

namespace ProximityPrize.SubmissionLower.CTY

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open IL KI ABI CS TB

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K

private theorem AMN
    (H:P4 K) (F:RCN266.RegularIndex H):
    F.1 ∈ normalizedFactors H:=by
  have hactive:F.1 ∈ RCN082.HR H:=
    (Finset.mem_filter.mp F.2).1
  have hnf:F.1 ∈ (normalizedFactors H).toFinset:=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf

theorem BWW
    (H:P4 K) (F G:RCN266.RegularIndex H) (hne:F.1 ≠ G.1):
    IsRelPrime F.1 G.1:=by
  have hFs:=RCN167.KR H F.1 F.2
  have hGs:=RCN167.KR H G.1 G.2
  apply hFs.1.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hne
  apply UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
    (AMN H F) (AMN H G)
  exact (hFs.1.dvd_irreducible_iff_associated hGs.1).mp hd

theorem CQY
    [AddCommGroup V] [Module K V]
    (D w T YS S:ℕ) (q:V→ₗ[K] P4 K)
    (hq:Function.Injective q)
    (hmem: ∀v,q v ∈ PQ K D w T YS S)
    (F:P4 K) (hF:F ≠ 0) (hdiv: ∀v,F ∣ q v):
    Function.Injective (ARF q F hF hdiv)∧
      (∀v,q v=F*ARF q F hF hdiv v)∧
      ∀v,ARF q F hF hdiv v ∈ PQ K
        (D-wt (BV w) F) w
        (T-wt AT F)
        (YS-wt BC F)
        (S-wt BE F):=by
  classical
  let qF:=ARF q F hF hdiv
  have hqF:Function.Injective qF:=
    BPR q hq F hF hdiv
  have hprod (v:V):q v=F*qF v:=
    LR q F hdiv v
  refine ⟨hqF,hprod,?_⟩
  intro v
  by_cases hv:v=0
  · subst v
    rw [map_zero]
    exact (PQ K _ _ _ _ _).zero_mem
  · have hqv:q v ≠ 0:=by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    have hqFv:qF v ≠ 0:=by
      intro hz
      apply hqv
      rw [hprod v,hz,mul_zero]
    exact BPI
      (q v) F (qF v) D w T YS S hqv hF hqFv (hmem v) (hprod v)

theorem wt_pow_eq (weights:Fin 4→ℕ) (F:P4 K) (hF:F ≠ 0)
    (j:ℕ):wt weights (F^j)=j*wt weights F:=by
  unfold wt
  induction j with
  | zero=>simp [pow_zero,MvPolynomial.weightedTotalDegree]
  | succ j ih=>
      rw [pow_succ',UP weights F (F^j) hF
        (pow_ne_zero j hF),ih]
      simp only [Nat.succ_eq_add_one,Nat.add_mul,one_mul]
      omega

end

end ProximityPrize.SubmissionLower.CTY
end PackedLocator_LocatorTwoFactorAvoidance

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorFactorAggregate
namespace ProximityPrize.SubmissionLower.DY
open scoped BigOperators
open RCN095
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
def middle (p:FlagDegree):ℕ:=p.yz+p.all
def total (p:FlagDegree):ℕ:=p.zOnly+p.yz+p.all
def Below (p q:FlagDegree):Prop:=
  p.all≤q.all∧middle p≤middle q∧total p≤total q
theorem DQE (p q r:FlagDegree):
    flagMixed p q r=
      (q.all*r.all+q.yz*r.all+q.all*r.yz)*total p+
      (q.zOnly*r.all+q.all*r.zOnly)*middle p+
      (q.yz*r.yz+q.zOnly*r.yz+q.yz*r.zOnly)*p.all:=by
  simp only [flagMixed,middle,total]
  ring
theorem CKM {p P:FlagDegree} (h:Below p P) (q r:FlagDegree):
    flagMixed p q r≤flagMixed P q r:=by
  rw [DQE p q r,DQE P q r]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ h.2.2) (Nat.mul_le_mul_left _ h.2.1))
    (Nat.mul_le_mul_left _ h.1)
theorem FYR (p:FlagDegree) {q Q:FlagDegree}
    (h:Below q Q) (r:FlagDegree):flagMixed p q r≤flagMixed p Q r:=by
  calc
    flagMixed p q r=flagMixed q p r:=by unfold flagMixed;ring
    _≤flagMixed Q p r:=CKM h p r
    _=flagMixed p Q r:=by unfold flagMixed;ring
theorem GCR (p q:FlagDegree) {r R:FlagDegree}
    (h:Below r R):flagMixed p q r≤flagMixed p q R:=by
  calc
    flagMixed p q r=flagMixed r q p:=by unfold flagMixed;ring
    _≤flagMixed R q p:=CKM h q p
    _=flagMixed p q R:=by unfold flagMixed;ring
theorem EDA (p:FlagDegree) {q Q r R:FlagDegree}
    (hq:Below q Q) (hr:Below r R):flagMixed p q r≤flagMixed p Q R:=
  (FYR p hq r).trans (GCR p Q hr)
theorem sum_mixed_le {I:Type*} [Fintype I]
    (p:I→FlagDegree) (P q r:FlagDegree)
    (hs:(∑ i,(p i).all)≤P.all)
    (hy:(∑ i,middle (p i))≤middle P)
    (ht:(∑ i,total (p i))≤total P):
    (∑ i,flagMixed (p i) q r)≤flagMixed P q r:=by
  rw [Finset.sum_congr rfl (fun i _=>DQE (p i) q r),
    DQE P q r]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)
def padS (p:FlagDegree):ℕ:=max p.all 2
def padY (p:FlagDegree):ℕ:=max (middle p) (padS p+1)
def padT (p:FlagDegree):ℕ:=max (total p) (padY p)
def paddedTail (p:FlagDegree) (d:ℕ):FlagDegree:=
  ⟨2*(padT p-padY p)*d,
    1+2*(padY p-padS p)*d,
    2*(padS p-1)*d⟩
def paddedCost (d e:ℕ) (p:FlagDegree):ℕ:=
  flagMixed p (paddedTail p d) (paddedTail p e)
theorem CPP (p:FlagDegree) (d:ℕ):
    (paddedTail p d).all=2*(padS p-1)*d∧
    middle (paddedTail p d)=1+2*(padY p-1)*d∧
    total (paddedTail p d)=1+2*(padT p-1)*d:=by
  have hs:1≤padS p:=by
    have h:2≤padS p:=le_max_right _ _
    omega
  have hy:padS p+1≤padY p:=le_max_right _ _
  have ht:padY p≤padT p:=le_max_right _ _
  have hyadd:padY p-padS p+(padS p-1)=padY p-1:=by omega
  have htadd:padT p-padY p+(padY p-padS p)+(padS p-1)=
      padT p-1:=by omega
  refine ⟨rfl,?_,?_⟩
  · change (1+2*(padY p-padS p)*d)+2*(padS p-1)*d=_
    calc
      _=1+2*(padY p-padS p+(padS p-1))*d:=by ring
      _=_:=by rw [hyadd]
  · change (2*(padT p-padY p)*d+
      (1+2*(padY p-padS p)*d))+2*(padS p-1)*d=_
    calc
      _=1+2*(padT p-padY p+(padY p-padS p)+
        (padS p-1))*d:=by ring
      _=_:=by rw [htadd]
theorem padding_mono {p q:FlagDegree} (h:Below p q):
    padS p≤padS q∧padY p≤padY q∧padT p≤padT q:=by
  have hs:padS p≤padS q:=max_le_max h.1 (Nat.le_refl 2)
  have hy:padY p≤padY q:=max_le_max h.2.1 (Nat.add_le_add_right hs 1)
  have ht:padT p≤padT q:=max_le_max h.2.2 hy
  exact ⟨hs,hy,ht⟩
theorem FEY (d:ℕ) {p q:FlagDegree} (h:Below p q):
    Below (paddedTail p d) (paddedTail q d):=by
  have hp:=CPP p d
  have hq:=CPP q d
  have hc:=padding_mono h
  have hm {a b:ℕ} (hab:a≤b):2*(a-1)*d≤2*(b-1)*d:=
    Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hab 1))
  unfold Below
  rw [hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2]
  exact ⟨hm hc.1,Nat.add_le_add_left (hm hc.2.1) 1,
    Nat.add_le_add_left (hm hc.2.2) 1⟩
theorem GGS (d e:ℕ) {p q:FlagDegree} (h:Below p q):
    paddedCost d e p≤paddedCost d e q:=by
  exact (CKM h _ _).trans
    (EDA q (FEY d h) (FEY e h))
theorem ATD (p:FlagDegree):p.all≤middle p:=by
  dsimp [middle]
  omega
theorem AIS (p:FlagDegree):middle p≤total p:=by
  dsimp [middle,total]
  omega
end ProximityPrize.SubmissionLower.DY
end PackedLocator_LocatorFactorAggregate

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorHybridCost

namespace ProximityPrize.SubmissionLower.AFI

open scoped BigOperators
open RCN095 DY

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

def rationalFlag (p:FlagDegree):FlagDegree:=
  ⟨131072*(padT p-padY p)+2*(padT p-padY p),
    131072*(padY p-padS p-1)+2*(padY p-padS p-1)+2,
    131072*(padS p-2)+2*(padS p-2)+3⟩

def movingFiber (p:FlagDegree):FlagDegree:=
  ⟨padT p-padY p,padY p-padS p,padS p+1⟩

def movingCut (p:FlagDegree):FlagDegree:=
  rationalFlag p+⟨0,131072,262144⟩

def FXZ (p:FlagDegree):Prop:=2≤p.all∧p.all+2≤middle p

instance (p:FlagDegree):Decidable (FXZ p):=by
  unfold FXZ;infer_instance

theorem pad_bounds (p:FlagDegree):
    2≤padS p∧padS p+1≤padY p∧padY p≤padT p:=
  ⟨le_max_right _ _,le_max_right _ _,le_max_right _ _⟩

theorem DOZ (p:FlagDegree):
    (movingFiber p).all=padS p+1∧
      middle (movingFiber p)=padY p+1∧
      total (movingFiber p)=padT p+1:=by
  have h:=pad_bounds p
  dsimp only [movingFiber,middle,total]
  refine ⟨?_,?_,?_⟩<;>omega

theorem EAN (p:FlagDegree):
    (movingCut p).all=131074*(padS p-2)+262147∧
      middle (movingCut p)=131074*(padY p-3)+393221∧
      total (movingCut p)=131074*(padT p-3)+393221:=by
  have h:=pad_bounds p
  dsimp only [movingCut,rationalFlag,middle,total,add_zOnly,add_yz,add_all]
  refine ⟨?_,?_,?_⟩<;>omega

theorem FZQ {p q:FlagDegree} (h:Below p q):
    Below (movingFiber p) (movingFiber q):=by
  have hp:=DOZ p
  have hq:=DOZ q
  have hc:=padding_mono h
  unfold Below
  rw [hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2]
  omega

theorem GQO {p q:FlagDegree} (h:Below p q):
    Below (movingCut p) (movingCut q):=by
  have hp:=EAN p
  have hq:=EAN q
  have hc:=padding_mono h
  have hb:=pad_bounds p
  have hb' :=pad_bounds q
  unfold Below
  rw [hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2]
  omega

end ProximityPrize.SubmissionLower.AFI
end PackedLocator_LocatorHybridCost

section PackedLocator_LocatorHybridCostC1

namespace ProximityPrize.SubmissionLower.AVP

open scoped BigOperators
open RCN095 DY AFI

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

def ASZ (p:FlagDegree):FlagDegree:=rationalFlag p

def FFM (p:FlagDegree):Prop:=3≤p.all∧p.all+2≤middle p

instance (p:FlagDegree):Decidable (FFM p):=by
  unfold FFM;infer_instance

theorem ESL (p:FlagDegree):
    (rationalFlag p).all=131074*(padS p-2)+3∧
      middle (rationalFlag p)=131074*(padY p-3)+5∧
      total (rationalFlag p)=131074*(padT p-3)+5:=by
  have h:=pad_bounds p
  dsimp only [rationalFlag,middle,total]
  refine ⟨?_,?_,?_⟩<;>omega

theorem BUN (p:FlagDegree):
    (ASZ p).all=131074*(padS p-2)+3∧
      middle (ASZ p)=131074*(padY p-3)+5∧
      total (ASZ p)=131074*(padT p-3)+5:=
  ESL p

theorem EQU {p q:FlagDegree} (h:Below p q):
    Below (ASZ p) (ASZ q):=by
  have hp:=BUN p
  have hq:=BUN q
  have hc:=padding_mono h
  have hb:=pad_bounds p
  have hb' :=pad_bounds q
  unfold Below
  rw [hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2]
  omega

end ProximityPrize.SubmissionLower.AVP
end PackedLocator_LocatorHybridCostC1

section PackedLocator_LocatorHybridCostC2

namespace ProximityPrize.SubmissionLower.AAJ

open scoped BigOperators
open RCN095 DY AFI AVP

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

def reducedTail (p:FlagDegree):FlagDegree:=paddedTail p 131072

theorem DOY (p:FlagDegree):
    (reducedTail p).all=2*(padS p-1)*131072∧
      middle (reducedTail p)=1+2*(padY p-1)*131072∧
      total (reducedTail p)=1+2*(padT p-1)*131072:=
  CPP p 131072

theorem GBU {p q:FlagDegree} (h:Below p q):
    Below (reducedTail p) (reducedTail q):=by
  have hp:=DOY p
  have hq:=DOY q
  have hc:=padding_mono h
  have hb:=pad_bounds p
  have hb' :=pad_bounds q
  unfold Below
  rw [hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2]
  omega

def hybridCostC2 (p:FlagDegree):ℕ:=
  flagMixed p (reducedTail p) (ASZ p)+
    131076*flagMixed p (movingFiber p) (movingCut p)

def UG (p:FlagDegree):Prop:=3≤p.all∧p.all+2≤middle p

instance (p:FlagDegree):Decidable (UG p):=by
  unfold UG;infer_instance

theorem FXT {p q:FlagDegree} (h:Below p q):
    hybridCostC2 p≤hybridCostC2 q:=by
  unfold hybridCostC2
  apply Nat.add_le_add
  · exact (CKM h _ _).trans
      (EDA q (GBU h) (EQU h))
  · apply Nat.mul_le_mul_left
    exact (CKM h _ _).trans
      (EDA q (FZQ h) (GQO h))

end ProximityPrize.SubmissionLower.AAJ
end PackedLocator_LocatorHybridCostC2

section PackedLocator_LocatorHybridCostSelect

namespace ProximityPrize.SubmissionLower.AFI

open RCN095 DY AAJ

def ANG (p:FlagDegree):ℕ:=
  if UG p then hybridCostC2 p else paddedCost 131072 131073 p

end ProximityPrize.SubmissionLower.AFI
end PackedLocator_LocatorHybridCostSelect

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorBatchProductRoute

namespace ProximityPrize.SubmissionLower.KZ

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open IL KI CS TB CTY

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K

def dvdSubmodule [AddCommGroup V] [Module K V]
    (q:V→ₗ[K] P4 K) (F:P4 K):Submodule K V where
  carrier:={v | F ∣ q v}
  zero_mem' :=by simp
  add_mem' :=by
    intro x y hx hy
    change F ∣ q x at hx
    change F ∣ q y at hy
    change F ∣ q (x+y)
    rw [map_add]
    exact dvd_add hx hy
  smul_mem' :=by
    intro a x hx
    change F ∣ q x at hx
    change F ∣ q (a • x)
    rw [map_smul,MvPolynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hx _

@[simp] theorem GCY [AddCommGroup V] [Module K V]
    (q:V→ₗ[K] P4 K) (F:P4 K) (v:V):
    v ∈ dvdSubmodule q F ↔ F ∣ q v:=Iff.rfl

theorem CSA
    [AddCommGroup V] [Module K V]
    (q:V→ₗ[K] P4 K) (F:P4 K)
    (h: ¬ ∀v,F ∣ q v):
    dvdSubmodule q F ≠ ⊤ :=by
  intro htop
  apply h
  intro v
  have hv:v ∈ dvdSubmodule q F:=by rw [htop];trivial
  exact hv

theorem AZM
    [AddCommGroup V] [Module K V]
    {A:Type} [DecidableEq A] (s:Finset A) (hs:s.Nonempty)
    (q:V→ₗ[K] P4 K) (factor:A→P4 K)
    (hnonuniversal: ∀a ∈ s,¬ ∀v,factor a ∣ q v)
    (hcard:s.card<ENat.card K):
    ∃v,v ≠ 0∧ ∀a ∈ s,¬factor a ∣ q v:=by
  classical
  let bad:s→Submodule K V:=fun a=>dvdSubmodule q (factor a.1)
  have hproper: ∀a:s,bad a ≠ ⊤ :=by
    intro a
    exact CSA q (factor a.1)
      (hnonuniversal a.1 a.2)
  have hsmall:(Finset.univ:Finset s).card<ENat.card K:=by
    simpa using hcard
  have hss:=RCN133.CNP
    (Finset.univ:Finset s) bad hproper hsmall
  obtain ⟨v,hv⟩:=Set.ssubset_univ_iff_nonempty_compl.mp hss
  have havoid: ∀a:s,v ∉ bad a:=by
    intro a hmem
    apply hv
    simp only [Set.mem_iUnion,Finset.mem_univ,true_and]
    exact ⟨a,trivial,hmem⟩
  have hv0:v ≠ 0:=by
    intro hz
    obtain ⟨a,ha⟩:=hs
    have hnot:=havoid ⟨a,ha⟩
    apply hnot
    subst v
    change factor a ∣ q 0
    simp
  refine ⟨v,hv0,?_⟩
  intro a ha
  simpa only [bad,GCY] using havoid ⟨a,ha⟩

def CK (H:P4 K) (A:Finset (RCN266.RegularIndex H)):P4 K:=
  ∏ F ∈ A,F.1

def WR (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (F:RCN266.RegularIndex H):P4 K:=
  ∏ G ∈ A.erase F,G.1

theorem BMK (H:P4 K) (F:RCN266.RegularIndex H):
    F.1 ≠ 0:=
  (RCN167.KR H F.1 F.2).1.ne_zero

theorem AHD (H:P4 K)
    (A:Finset (RCN266.RegularIndex H)):CK H A ≠ 0:=by
  classical
  unfold CK
  apply Finset.prod_ne_zero_iff.mpr
  intro F hF
  exact BMK H F

theorem DKE (H:P4 K)
    (A:Finset (RCN266.RegularIndex H)) (F:RCN266.RegularIndex H):
    WR H A F ≠ 0:=by
  classical
  unfold WR
  apply Finset.prod_ne_zero_iff.mpr
  intro G hG
  exact BMK H G

theorem CRC
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (F:RCN266.RegularIndex H) (hFA:F ∈ A):
    F.1*WR H A F=CK H A:=by
  classical
  simpa only [CK,WR] using
    Finset.mul_prod_erase A (fun G=>G.1) hFA

theorem DEC
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (F:RCN266.RegularIndex H) (hFA:F ∈ A):
    IsRelPrime F.1 (WR H A F):=by
  classical
  unfold WR
  apply IsRelPrime.prod_right
  intro G hG
  have hGe:=Finset.mem_erase.mp hG
  apply BWW H F G
  intro heq
  apply hGe.1
  exact Subtype.ext heq.symm

theorem EGX
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (F:RCN266.RegularIndex H) (hFA:F ∈ A)
    (j:ℕ) (J:P4 K):
    CK H A^j*J=
      F.1^j*(WR H A F^j*J):=by
  rw [← CRC H A F hFA,mul_pow]
  ring

theorem COG
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (F:RCN266.RegularIndex H) (hFA:F ∈ A)
    (j:ℕ) (J:P4 K) (hnot: ¬F.1 ∣ J):
    IsRelPrime F.1 (WR H A F^j*J):=by
  have hFirred:=(RCN167.KR H F.1 F.2).1
  apply hFirred.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hnot
  exact ((DEC H A F hFA).pow_right)
    |>.dvd_of_dvd_mul_left hd

theorem ARP
    (weights:Fin 4→ℕ) (B j:ℕ) (F C J:P4 K)
    (hF:F ≠ 0) (hC:C ≠ 0) (hJ:J ≠ 0)
    (hfeasible:j*wt weights (F*C)≤B)
    (hbound:wt weights J≤B-j*wt weights (F*C)):
    wt weights (C^j*J)≤B-j*wt weights F:=by
  have hFC:=UP weights F C hF hC
  have hCJ:=UP weights (C^j) J
    (pow_ne_zero j hC) hJ
  have hCp:=wt_pow_eq weights C hC j
  unfold wt at hfeasible hbound hFC hCJ hCp ⊢
  rw [hFC,Nat.mul_add] at hfeasible hbound
  rw [hCp] at hCJ
  rw [hCJ]
  let f:=MvPolynomial.weightedTotalDegree weights F
  let c:=MvPolynomial.weightedTotalDegree weights C
  let x:=MvPolynomial.weightedTotalDegree weights J
  change j*f+j*c≤B at hfeasible
  change x≤B-(j*f+j*c) at hbound
  change j*c+x≤B-j*f
  have htotal:j*f+(j*c+x)≤B:=by
    calc
      j*f+(j*c+x)=(j*f+j*c)+x:=by omega
      _≤(j*f+j*c)+(B-(j*f+j*c)):=
        Nat.add_le_add_left hbound _
      _=B:=Nat.add_sub_of_le hfeasible
  have htotal' :(j*c+x)+j*f≤B:=by
    simpa only [Nat.add_comm] using htotal
  exact Nat.le_sub_of_add_le htotal'

theorem DWV
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (F:RCN266.RegularIndex H) (hFA:F ∈ A)
    (T YS S j:ℕ) (J:P4 K) (hJ:J ≠ 0)
    (hT:wt AT J≤
      T-j*wt AT (CK H A))
    (hY:wt BC J≤
      YS-j*wt BC (CK H A))
    (hS:wt BE J≤
      S-j*wt BE (CK H A))
    (hTfeasible:j*wt AT (CK H A)≤T)
    (hYfeasible:j*wt BC (CK H A)≤YS)
    (hSfeasible:j*wt BE (CK H A)≤S):
    wt AT (WR H A F^j*J)≤
        T-j*wt AT F.1∧
      wt BC (WR H A F^j*J)≤
        YS-j*wt BC F.1∧
      wt BE (WR H A F^j*J)≤
        S-j*wt BE F.1:=by
  have hfactor:=CRC H A F hFA
  have hF0:=BMK H F
  have hC0:=DKE H A F
  rw [← hfactor] at hT hY hS hTfeasible hYfeasible hSfeasible
  exact ⟨
    ARP AT T j F.1
      (WR H A F) J hF0 hC0 hJ hTfeasible hT,
    ARP BC YS j F.1
      (WR H A F) J hF0 hC0 hJ hYfeasible hY,
    ARP BE S j F.1
      (WR H A F) J hF0 hC0 hJ hSfeasible hS⟩

noncomputable def AKV
    [AddCommGroup V] [Module K V]
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (q:V→ₗ[K] P4 K):Finset (RCN266.RegularIndex H):=by
  classical
  exact A.filter fun F=> ∀v,F.1 ∣ q v

@[simp] theorem ASD
    [AddCommGroup V] [Module K V]
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (q:V→ₗ[K] P4 K) (F:RCN266.RegularIndex H):
    F ∈ AKV H A q ↔ F ∈ A∧ ∀v,F.1 ∣ q v:=by
  classical
  simp only [AKV,Finset.mem_filter]

theorem BTP
    [AddCommGroup V] [Module K V]
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (q:V→ₗ[K] P4 K):AKV H A q ⊆ A:=by
  intro F hF
  exact (ASD H A q F).mp hF |>.1

theorem CQX
    (H:P4 K) (A:Finset (RCN266.RegularIndex H)) (Q:P4 K)
    (hdiv: ∀F ∈ A,F.1 ∣ Q):CK H A ∣ Q:=by
  classical
  induction A using Finset.induction_on with
  | empty=>simp only [CK,Finset.notMem_empty,
      Finset.prod_empty,one_dvd]
  | @insert F A hFA ih=>
      have hFdiv:F.1 ∣ Q:=hdiv F (Finset.mem_insert_self F A)
      have hAdiv:CK H A ∣ Q:=by
        apply ih
        intro G hGA
        exact hdiv G (Finset.mem_insert_of_mem hGA)
      have hrel:IsRelPrime F.1 (CK H A):=by
        unfold CK
        apply IsRelPrime.prod_right
        intro G hGA
        apply BWW H F G
        intro heq
        apply hFA
        have hFG:F=G:=Subtype.ext heq
        rwa [hFG]
      have hprod:CK H (insert F A)=
          F.1*CK H A:=by
        simp only [CK,Finset.prod_insert hFA]
      rw [hprod]
      exact hrel.mul_dvd hFdiv hAdiv

theorem ZQ
    (H:P4 K) (A:Finset (RCN266.RegularIndex H)):
    CK H A ∣ H:=by
  apply CQX
  intro F _hFA
  exact (RCN167.KR H F.1 F.2).2.1

theorem BAZ
    [AddCommGroup V] [Module K V]
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (q:V→ₗ[K] P4 K):
    ∀v,CK H (AKV H A q) ∣ q v:=by
  intro v
  apply CQX
  intro F hF
  exact (ASD H A q F).mp hF |>.2 v

theorem DXG
    {I:Type} [Fintype I]
    (D w L S m YS:ℕ) (nodes u0 u1:I→K)
    (hw:1≤w) (hshape:D+S≤w*(YS+1)):
    ∀v:IJ (K:=K) D w L S m nodes u0 u1,
      LZ (K:=K) D w L S m nodes u0 u1 v ∈
        PQ K D w L YS S:=by
  intro v d hd
  have hglobal:=LG K D w L S v.1
  have hb:=hglobal hd
  have hYS:=EQT D w L S YS hw hshape
    (reconstruct K D w L S v.1) hglobal
  have hy:=(MvPolynomial.le_weightedTotalDegree BC hd).trans hYS
  rw [weight_fin4] at hy
  simp only [BC] at hy
  refine ⟨hb.1,?_,hb.2.1,hb.2.2⟩
  simpa [BC] using hy

theorem CRZ
    {I:Type} [Fintype I]
    (D w L S m YS:ℕ) (nodes u0 u1:I→K)
    (hw:1≤w) (hshape:D+S≤w*(YS+1))
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (hdiv:∀v:IJ (K:=K) D w L S m nodes u0 u1,
      CK H A ∣ reconstruct K D w L S v.1):
    ∃q:IJ (K:=K) D w L S m nodes u0 u1→ₗ[K] P4 K,
      Function.Injective q∧
      (∀v,reconstruct K D w L S v.1=CK H A*q v)∧
      ∀v,q v ∈ PQ K
        (D-wt (BV w) (CK H A)) w
        (L-wt AT (CK H A))
        (YS-wt BC (CK H A))
        (S-wt BE (CK H A)):=by
  let recon:=LZ (K:=K) D w L S m nodes u0 u1
  have hdiv':∀v,CK H A ∣ recon v:=by
    intro v
    simpa only [recon,SE] using hdiv v
  obtain ⟨hq,hprod,hbox⟩:=CQY D w L YS S recon
    (APB (K:=K) D w L S m nodes u0 u1)
    (DXG D w L S m YS nodes u0 u1 hw hshape)
    (CK H A) (AHD H A) hdiv'
  let q:=ARF recon (CK H A)
    (AHD H A) hdiv'
  refine ⟨q,hq,?_,?_⟩
  · intro v
    simpa only [recon,SE,q] using hprod v
  · exact hbox

def DUW
    [AddCommGroup V] [Module K V]
    (fuel Dlow w delta T YS S:ℕ)
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (q:V→ₗ[K] P4 K):Prop:=
  ∃(j:Fin fuel) (U:Finset (RCN266.RegularIndex H)) (v:V) (J:P4 K),
    U ⊂ A∧v ≠ 0∧J ≠ 0∧
      CK H A^j.val*J=q v∧
      J ∈ PQ K
        (Dlow-j.val*delta-
          j.val*wt (BV w) (CK H A)) w
        (T-j.val*wt AT (CK H A))
        (YS-j.val*wt BC (CK H A))
        (S-j.val*wt BE (CK H A))∧
      ∀F ∈ A \ U,¬F.1 ∣ J

theorem BON
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S:ℕ)
    (hw:1≤w) (hDlow:Dlow=Dhigh-delta)
    (q:V→ₗ[K] P4 K) (hq:Function.Injective q)
    (hmem: ∀v,q v ∈ PQ K Dhigh w T YS S)
    (H:P4 K) (A:Finset (RCN266.RegularIndex H)) (hA:A.Nonempty)
    (hsource:
      CS.HN w Dhigh delta
          (wt (BV w) (CK H A))
          (wt AT (CK H A))
          (wt BC (CK H A))
          (wt BE (CK H A))
          T YS S (steps+1)<Module.finrank K V)
    (hterminal:
      T-steps*wt AT (CK H A)<
          wt AT (CK H A)∨
      YS-steps*wt BC (CK H A)<
          wt BC (CK H A)∨
      S-steps*wt BE (CK H A)<
          wt BE (CK H A))
    (hfield:A.card<ENat.card K):
    DUW (steps+1) Dlow w delta T YS S H A q:=by
  classical
  let P:=CK H A
  have hP:P ≠ 0:=by
    simpa only [P] using AHD H A
  change CS.HN w Dhigh delta
      (wt (BV w) P)
      (wt AT P) (wt BC P)
      (wt BE P) T YS S (steps+1)<
    Module.finrank K V at hsource
  change
    T-steps*wt AT P<wt AT P∨
    YS-steps*wt BC P<wt BC P∨
    S-steps*wt BE P<wt BE P at hterminal
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero=>
      let bandOne:=(highBandMap (K:=K) w Dlow delta T
        (min YS (CS.thinTop w Dhigh S)) S).comp q
      let lowOne:=LinearMap.ker bandOne
      have hwidth:Dhigh≤Dlow+delta:=by omega
      have hrangeOne:Module.finrank K bandOne.range≤
          delta*channelCount T
            (min YS (CS.thinTop w Dhigh S)) S:=by
        calc
          Module.finrank K bandOne.range≤
              Module.finrank K (BXU delta T
                (min YS (CS.thinTop w Dhigh S)) S→K):=
            bandOne.range.finrank_le
          _=delta*channelCount T
              (min YS (CS.thinTop w Dhigh S)) S:=by
            rw [Module.finrank_fintype_fun_eq_card,EMV]
      have hlowOneRank:0<Module.finrank K lowOne:=by
        have hsum:=bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range+Module.finrank K lowOne=
          Module.finrank K V at hsum
        have hfirst:delta*channelCount T
            (min YS (CS.thinTop w Dhigh S)) S<
              Module.finrank K V:=by
          simpa only [CS.HN,
            Nat.add_zero] using hsource
        omega
      let qOne:lowOne→ₗ[K] P4 K:=q.comp lowOne.subtype
      have hqOne:Function.Injective qOne:=by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne,LinearMap.comp_apply,Submodule.coe_subtype] using hab
      have hqOneBox: ∀v:lowOne,
          qOne v ∈ PQ K Dlow w T YS S:=by
        intro v
        have hzero:highBandMap w Dlow delta T
            (min YS (CS.thinTop w Dhigh S)) S (q v.1)=0:=by
          have hv:=v.2
          change bandOne v.1=0 at hv
          simpa only [bandOne,qOne,LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne,LinearMap.comp_apply,Submodule.coe_subtype] using
          CS.BGZ
            Dhigh Dlow w delta T YS S hw hwidth (q v.1) (hmem v.1) hzero
      let U:=AKV H A qOne
      have hUsub:U ⊆ A:=BTP H A qOne
      by_cases hall:U=A
      · have hdivP: ∀v:lowOne,P ∣ qOne v:=by
          intro v
          have hv:=BAZ H A qOne v
          change CK H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        exfalso
        obtain ⟨v,hv⟩:=
          Module.finrank_pos_iff_exists_ne_zero.mp hlowOneRank
        have hqv:qOne v ≠ 0:=by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        have hb:=DLI (hqOneBox v) hqv
        have hdivT:wt AT P≤
            wt AT (qOne v):=by
          simpa only [wt] using
            IQ AT P
              (qOne v) (hdivP v) hqv
        have hdivY:wt BC P≤
            wt BC (qOne v):=by
          simpa only [wt] using
            IQ BC P
              (qOne v) (hdivP v) hqv
        have hdivS:wt BE P≤
            wt BE (qOne v):=by
          simpa only [wt] using
            IQ BE P
              (qOne v) (hdivP v) hqv
        rcases hterminal with ht | hy | hs
        · apply (not_lt_of_ge (hdivT.trans hb.1))
          simpa only [Nat.zero_mul,Nat.sub_zero] using ht
        · apply (not_lt_of_ge (hdivY.trans hb.2.1))
          simpa only [Nat.zero_mul,Nat.sub_zero] using hy
        · apply (not_lt_of_ge (hdivS.trans hb.2.2.1))
          simpa only [Nat.zero_mul,Nat.sub_zero] using hs
      · have hproper:U ⊂ A:=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub,hall⟩
        have hN:(A \ U).Nonempty:=by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon: ∀F ∈ A \ U,¬ ∀v,F.1 ∣ qOne v:=by
          intro F hFN hdiv
          have hp:=Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (ASD H A qOne F).mpr ⟨hp.1,hdiv⟩
        have hNcard:(A \ U).card<ENat.card K:=by
          calc
            ((A \ U).card:ENat)≤(A.card:ENat):=by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _<ENat.card K:=hfield
        obtain ⟨v,hv,havoid⟩:=AZM
          (A \ U) hN qOne (fun F=>F.1) hnon hNcard
        have hqv:qOne v ≠ 0:=by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0,by omega⟩,U,v.1,qOne v,hproper,?_,hqv,?_,?_,?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero,pow_zero,one_mul,qOne,
            LinearMap.comp_apply,Submodule.coe_subtype]
        · simpa only [Fin.val_zero,zero_mul,Nat.sub_zero] using hqOneBox v
        · exact havoid
  | succ steps ih=>
      let bandOne:=(highBandMap (K:=K) w Dlow delta T
        (min YS (CS.thinTop w Dhigh S)) S).comp q
      let lowOne:=LinearMap.ker bandOne
      have hwidth:Dhigh≤Dlow+delta:=by omega
      have hrangeOne:Module.finrank K bandOne.range≤
          delta*channelCount T
            (min YS (CS.thinTop w Dhigh S)) S:=by
        calc
          Module.finrank K bandOne.range≤
              Module.finrank K (BXU delta T
                (min YS (CS.thinTop w Dhigh S)) S→K):=
            bandOne.range.finrank_le
          _=delta*channelCount T
              (min YS (CS.thinTop w Dhigh S)) S:=by
            rw [Module.finrank_fintype_fun_eq_card,EMV]
      have hlowOneRank:
          CS.HN w
              (Dhigh-delta-wt (BV w) P) delta
              (wt (BV w) P)
              (wt AT P) (wt BC P)
              (wt BE P)
              (T-wt AT P)
              (YS-wt BC P)
              (S-wt BE P) (steps+1)<
            Module.finrank K lowOne:=by
        have hsum:=bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range+Module.finrank K lowOne=
          Module.finrank K V at hsum
        have hbudget:
            delta*channelCount T
                (min YS (CS.thinTop w Dhigh S)) S+
                CS.HN w
                  (Dhigh-delta-wt (BV w) P) delta
                  (wt (BV w) P)
                  (wt AT P) (wt BC P)
                  (wt BE P)
                  (T-wt AT P)
                  (YS-wt BC P)
                  (S-wt BE P) (steps+1)<
              Module.finrank K V:=by
          simpa only [CS.HN,
            Nat.succ_eq_add_one,Nat.add_assoc] using hsource
        omega
      let qOne:lowOne→ₗ[K] P4 K:=q.comp lowOne.subtype
      have hqOne:Function.Injective qOne:=by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne,LinearMap.comp_apply,Submodule.coe_subtype] using hab
      have hqOneBox: ∀v:lowOne,
          qOne v ∈ PQ K Dlow w T YS S:=by
        intro v
        have hzero:highBandMap w Dlow delta T
            (min YS (CS.thinTop w Dhigh S)) S (q v.1)=0:=by
          have hv:=v.2
          change bandOne v.1=0 at hv
          simpa only [bandOne,qOne,LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne,LinearMap.comp_apply,Submodule.coe_subtype] using
          CS.BGZ
            Dhigh Dlow w delta T YS S hw hwidth (q v.1) (hmem v.1) hzero
      let U:=AKV H A qOne
      have hUsub:U ⊆ A:=BTP H A qOne
      by_cases hall:U=A
      · have hdivP: ∀v:lowOne,P ∣ qOne v:=by
          intro v
          have hv:=BAZ H A qOne v
          change CK H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        let qTwo:=ARF qOne P hP hdivP
        obtain ⟨hqTwo,_hprodTwo,hqTwoBox⟩:=
          CQY Dlow w T YS S qOne hqOne hqOneBox
            P hP hdivP
        let DOneHigh:=Dlow-wt (BV w) P
        let DOneLow:=Dlow-delta-wt (BV w) P
        let TOne:=T-wt AT P
        let YOne:=YS-wt BC P
        let SOne:=S-wt BE P
        have hDlowRest:DOneLow=DOneHigh-delta:=by
          simp only [DOneHigh,DOneLow]
          omega
        have hterminalRest:
            TOne-steps*wt AT P<
                wt AT P∨
            YOne-steps*wt BC P<
                wt BC P∨
            SOne-steps*wt BE P<
                wt BE P:=by
          rcases hterminal with ht | hy | hs
          · left
            simpa only [TOne,Nat.sub_sub,Nat.add_mul,one_mul,
              Nat.succ_eq_add_one,Nat.add_comm] using ht
          · right;left
            simpa only [YOne,Nat.sub_sub,Nat.add_mul,one_mul,
              Nat.succ_eq_add_one,Nat.add_comm] using hy
          · right;right
            simpa only [SOne,Nat.sub_sub,Nat.add_mul,one_mul,
              Nat.succ_eq_add_one,Nat.add_comm] using hs
        obtain ⟨j,child,v,J,hchild,hv,hJ,heq,hbox,havoid⟩:=
          ih DOneHigh DOneLow TOne YOne SOne hDlowRest qTwo hqTwo
            (by simpa only [qTwo,DOneHigh,TOne,YOne,SOne] using hqTwoBox)
            (by simpa only [DOneHigh,TOne,YOne,SOne,hDlow] using hlowOneRank)
            hterminalRest
        let jUp:Fin (Nat.succ steps+1):=⟨j.val+1,by omega⟩
        refine ⟨jUp,child,v.1,J,hchild,?_,hJ,?_,?_,havoid⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · change P^(j.val+1)*J=q v.1
          calc
            P^(j.val+1)*J=P*(P^j.val*J):=by
              rw [pow_succ']
              ring
            _=P*qTwo v:=by rw [heq]
            _=qOne v:=
              (LR qOne P hdivP v).symm
            _=q v.1:=rfl
        · have hD:
              DOneLow-j.val*delta-
                  j.val*wt (BV w) P=
                Dlow-(j.val+1)*delta-
                  (j.val+1)*wt (BV w) P:=by
              simp only [DOneLow,Nat.sub_sub,Nat.add_mul,one_mul]
              congr 1
              omega
          have hT:TOne-j.val*wt AT P=
              T-(j.val+1)*wt AT P:=by
            simp only [TOne,Nat.sub_sub,Nat.add_mul,one_mul]
            congr 1
            omega
          have hY:YOne-j.val*wt BC P=
              YS-(j.val+1)*wt BC P:=by
            simp only [YOne,Nat.sub_sub,Nat.add_mul,one_mul]
            congr 1
            omega
          have hS:SOne-j.val*wt BE P=
              S-(j.val+1)*wt BE P:=by
            simp only [SOne,Nat.sub_sub,Nat.add_mul,one_mul]
            congr 1
            omega
          change J ∈ PQ K
            (DOneLow-j.val*delta-
              j.val*wt (BV w) P) w
            (TOne-j.val*wt AT P)
            (YOne-j.val*wt BC P)
            (SOne-j.val*wt BE P) at hbox
          change J ∈ PQ K
            (Dlow-(j.val+1)*delta-
              (j.val+1)*wt (BV w) P) w
            (T-(j.val+1)*wt AT P)
            (YS-(j.val+1)*wt BC P)
            (S-(j.val+1)*wt BE P)
          rw [hD,hT,hY,hS] at hbox
          exact hbox
      · have hproper:U ⊂ A:=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub,hall⟩
        have hN:(A \ U).Nonempty:=by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon: ∀F ∈ A \ U,¬ ∀v,F.1 ∣ qOne v:=by
          intro F hFN hdiv
          have hp:=Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (ASD H A qOne F).mpr ⟨hp.1,hdiv⟩
        have hNcard:(A \ U).card<ENat.card K:=by
          calc
            ((A \ U).card:ENat)≤(A.card:ENat):=by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _<ENat.card K:=hfield
        obtain ⟨v,hv,havoid⟩:=AZM
          (A \ U) hN qOne (fun F=>F.1) hnon hNcard
        have hqv:qOne v ≠ 0:=by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0,by omega⟩,U,v.1,qOne v,hproper,?_,hqv,?_,?_,?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero,pow_zero,one_mul,qOne,
            LinearMap.comp_apply,Submodule.coe_subtype]
        · simpa only [Fin.val_zero,zero_mul,Nat.sub_zero] using hqOneBox v
        · exact havoid

theorem CNH
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (F:RCN266.RegularIndex H) (hFA:F ∈ A)
    (j:ℕ) (P:Polynomial K) (gamma:K) (J:P4 K)
    (hfactorial:(j.factorial:K) ≠ 0)
    (hFzero:RCN319.BM K P gamma F.1=0)
    (hregular:RCN319.BM K P gamma
      (MvPolynomial.pderiv (2:Fin 4) F.1) ≠ 0)
    (hpower:RCN319.BM K P gamma
      (NY j (CK H A^j*J))=0):
    RCN319.BM K P gamma
      (WR H A F^j*J)=0:=by
  rw [EGX H A F hFA j J] at hpower
  exact AVQ
    j P gamma F.1 (WR H A F^j*J)
    hfactorial hFzero hregular hpower

theorem DFY
    {I:Type} [Fintype I] [DecidableEq I]
    (j D Dlow w L S m agreements p:ℕ)
    [CharP K p] (hp:p.Prime)
    (nodes:I ↪ K) (u0 u1:I→K)
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (F:RCN266.RegularIndex H) (hFA:F ∈ A)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (v:IJ (K:=K) D w L S m nodes u0 u1)
    (J:P4 K)
    (hj:1≤j) (hjchar:j<p) (hw:1≤w)
    (hdegree: ∀gamma ∈ Gamma,(selected gamma).natDegree≤w)
    (hagreement: ∀gamma ∈ Gamma,agreements≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hcapacity:Dlow≤(m-j)*agreements+j*(w-1))
    (hlow:reconstruct K D w L S v.1 ∈
      BA K Dlow w L S)
    (heq:CK H A^j*J=reconstruct K D w L S v.1):
    ∀gamma ∈ regularSeeds H selected Gamma F,
      RCN319.BM K (selected gamma) gamma
        (WR H A F^j*J)=0:=by
  classical
  intro gamma hgamma
  have hgammaG:=ACS H selected Gamma F hgamma
  let support:=(Finset.univ:Finset I).filter (fun i↦
    (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)
  have hcard:agreements≤support.card:=hagreement gamma hgammaG
  have hcap:Dlow≤(m-j)*support.card+j*(w-1):=
    hcapacity.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left (m-j) hcard) _)
  have hvalues: ∀i ∈ support,
      (selected gamma).eval (nodes i)=u0 i+gamma*u1 i:=by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hder:=AUM
    j D Dlow w L S m nodes u0 u1 v hlow
    (selected gamma) gamma support hj hw (hdegree gamma hgammaG)
    hcap hvalues
  rw [← heq] at hder
  obtain ⟨hFzero,hregular⟩:=(Finset.mem_filter.mp hgamma).2
  exact CNH H A F hFA j
    (selected gamma) gamma J
    (DYA p j hp hjchar)
    hFzero hregular hder

end

end ProximityPrize.SubmissionLower.KZ
end PackedLocator_LocatorBatchProductRoute

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorGenericHelperFactorSwitch

namespace ProximityPrize.SubmissionLower.AAV

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open KI IL

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

end

end ProximityPrize.SubmissionLower.AAV
end PackedLocator_LocatorGenericHelperFactorSwitch

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorGenericPowerRoute

namespace ProximityPrize.SubmissionLower.BPN

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open KI IL
open CS TB
open AAV

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

end

end ProximityPrize.SubmissionLower.BPN
end PackedLocator_LocatorGenericPowerRoute

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorPhase6800Oracle

namespace ProximityPrize.SubmissionLower.FV

open scoped BigOperators
open RCN095 DY
open IL CS
open BPN AAV

set_option autoImplicit false
set_option maxRecDepth 100000

structure Potential where
  totalCoeff:ℕ
  middleCoeff:ℕ
  slopeCoeff:ℕ
  deriving DecidableEq,Repr

def Potential.eval (q:Potential) (p:FlagDegree):ℕ:=
  q.totalCoeff*total p+q.middleCoeff*middle p+q.slopeCoeff*p.all

structure EA where
  totalCap:ℕ
  middleCap:ℕ
  slopeCap:ℕ
  gap:ℕ
  deriving DecidableEq,Repr

def sourceR1200:EA:=
  ⟨526750,10983,2450,36963750380693986577⟩

def sourceC:EA:=
  ⟨328400,6641,1480,5090867013182078230⟩

def GRU:EA:=
  ⟨165000,3320,750,315862958949324685⟩

def GOH:EA:=
  ⟨19500,539,120,91073661700890⟩

def EA.fuel (s:EA) (p:FlagDegree):ℕ:=
  min (s.totalCap/total p)
    (min (s.middleCap/middle p) (s.slopeCap/p.all))

def EA.band (s:EA) (p:FlagDegree):ℕ:=
  LH 50293 (total p) (middle p) p.all
    (s.totalCap-total p) (s.middleCap-middle p)
    (s.slopeCap-p.all) (s.fuel p)

def contactDec (p:FlagDegree):ℕ:=131071*middle p-p.all

def EA.contactCap (s:EA) (p:FlagDegree):ℕ:=
  (131071*(s.middleCap+1)-s.slopeCap)-contactDec p

def EA.bandThin (s:EA) (p:FlagDegree):ℕ:=
  HN 131071 (s.contactCap p) 50293 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap-total p) (s.middleCap-middle p)
    (s.slopeCap-p.all) (s.fuel p)

def EA.Routeable (s:EA) (p:FlagDegree):Prop:=
  1≤p.all∧total p≤s.totalCap∧middle p≤s.middleCap∧
    p.all≤s.slopeCap∧(s.band p<s.gap∨s.bandThin p<s.gap)

instance (s:EA) (p:FlagDegree):Decidable (s.Routeable p):=
  by unfold EA.Routeable;infer_instance

def rawFlag (r v z:ℕ):FlagDegree:=⟨z,v,r⟩

@[simp] theorem rawFlag_all (r v z:ℕ):(rawFlag r v z).all=r:=rfl
@[simp] theorem AVF (r v z:ℕ):middle (rawFlag r v z)=r+v:=by
  simp [rawFlag,middle,Nat.add_comm]
@[simp] theorem BTK (r v z:ℕ):total (rawFlag r v z)=r+v+z:=by
  simp [rawFlag,total,Nat.add_comm,Nat.add_left_comm]

def sumFlag {ι:Type} (s:Finset ι) (p:ι→FlagDegree):FlagDegree:=
  ⟨∑ i ∈ s,(p i).zOnly,∑ i ∈ s,(p i).yz,
    ∑ i ∈ s,(p i).all⟩

@[simp] theorem sumFlag_all {ι:Type} (s:Finset ι)
    (p:ι→FlagDegree):
    (sumFlag s p).all= ∑ i ∈ s,(p i).all:=rfl

@[simp] theorem AQT {ι:Type} (s:Finset ι)
    (p:ι→FlagDegree):
    middle (sumFlag s p)= ∑ i ∈ s,middle (p i):=by
  simp only [sumFlag,middle,Finset.sum_add_distrib]

@[simp] theorem AXF {ι:Type} (s:Finset ι)
    (p:ι→FlagDegree):
    total (sumFlag s p)= ∑ i ∈ s,total (p i):=by
  simp only [sumFlag,total,Finset.sum_add_distrib]

structure DGY where
  r:ℕ
  v:ℕ
  r1200:ℕ
  sourceC:ℕ
  split500:ℕ
  split1200:ℕ
  split390:ℕ
  deriving DecidableEq,Repr

def BJE (s:EA) (r v threshold:ℕ):Prop:=
  let maxZ:=6677-(r+v)
  if threshold=0 then s.Routeable (rawFlag r v 0)
  else if threshold≤maxZ then
    ¬s.Routeable (rawFlag r v (threshold-1))∧
      s.Routeable (rawFlag r v threshold)
  else threshold=maxZ+1∧ ¬s.Routeable (rawFlag r v maxZ)

instance (s:EA) (r v threshold:ℕ):
    Decidable (BJE s r v threshold):=by
  unfold BJE
  infer_instance

def DGY.Valid (q:DGY):Prop:=
  1≤q.r∧q.r≤29∧q.r+q.v≤135∧
    BJE sourceR1200 q.r q.v q.r1200∧
    BJE FV.sourceC q.r q.v q.sourceC∧
    BJE GRU q.r q.v q.split500∧
    BJE GOH q.r q.v q.split390

instance (q:DGY):Decidable q.Valid:=by
  unfold DGY.Valid
  infer_instance

structure BaseSegment where
  start:ℕ
  valueAtStart:ℕ
  slope:ℕ
  deriving DecidableEq,Repr

def BaseSegment.evalAt (q:BaseSegment) (z:ℕ):ℕ:=
  q.valueAtStart+q.slope*(z-q.start)

structure BaseRow where
  r:ℕ
  v:ℕ
  z0:ℕ
  z1:ℕ
  z2:ℕ
  segments:List BaseSegment
  deriving DecidableEq,Repr

def EZD:List BaseSegment→ℕ→ℕ
  | [],_=>0
  | q::qs,z=>
      (qs.foldl (fun best next=>if next.start≤z then next else best) q).evalAt z

def BaseRow.evalAt (q:BaseRow) (z:ℕ):ℕ:=
  if z=0 then q.z0
  else if z=1 then q.z1
  else if z=2 then q.z2
  else EZD q.segments z

def baseRowIndex (r v:ℕ):ℕ:=
  (r-1)*136-((r-1)*r)/2+v

def GSX:BaseRow:=⟨0,0,0,0,0,[]⟩

def EJY (rows:Array BaseRow) (r v:ℕ):BaseRow:=
  (rows[baseRowIndex r v]?).getD GSX

def baseTableCap (rows:Array BaseRow) (p:FlagDegree):ℕ:=
  (EJY rows p.all p.yz).evalAt p.zOnly

def FFK (rows:Array BaseRow):Prop:=
  rows.size=3509∧
    ∀r ∈ (List.range 29).map (fun q=>q+1),
      ∀v ∈ List.range (136-r),
        let q:=EJY rows r v
        q.r=r∧q.v=v

instance (rows:Array BaseRow):Decidable (FFK rows):=by
  unfold FFK
  infer_instance

def BaseRow.FTH (q:BaseRow):Prop:=
  1≤q.r∧q.r≤29∧q.r+q.v≤135∧
    q.segments ≠ []∧q.segments.head?.map BaseSegment.start=some 3∧
    q.segments.Pairwise (fun a b=>a.start<b.start)∧
    ∀s ∈ q.segments,s.start≤6677-(q.r+q.v)

instance (q:BaseRow):Decidable q.FTH:=by
  unfold BaseRow.FTH
  infer_instance

def RawBelow (q p:FlagDegree):Prop:=
  q.all≤p.all∧q.yz≤p.yz∧q.zOnly≤p.zOnly

def AVS (q p:FlagDegree):Prop:=
  RawBelow q p∧q.all<p.all

end ProximityPrize.SubmissionLower.FV
end PackedLocator_LocatorPhase6800Oracle

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower.UB

open RCN095 DY AFI AVP AAJ

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def rawCost (r v z:ℕ):ℕ:=ANG ⟨z,v,r⟩

theorem DRY (r v z:ℕ) (hr:3≤r) (hv:2≤v):
    UG (⟨z,v,r⟩:FlagDegree):=by
  change 3≤r∧r+2≤v+r
  omega

theorem DQJ (r v z:ℕ) (hr:2≤r):
    padS (⟨z,v,r⟩:FlagDegree)=r:=by
  simp only [padS]
  omega

theorem DRD (r v z:ℕ) (hr:2≤r) (hv:2≤v):
    padY (⟨z,v,r⟩:FlagDegree)=r+v:=by
  simp only [padY,middle,DQJ r v z hr]
  omega

theorem EJF (r v z:ℕ) (hr:2≤r) (hv:2≤v):
    padT (⟨z,v,r⟩:FlagDegree)=r+v+z:=by
  simp only [padT,total,DRD r v z hr hv]
  omega

theorem DMJ (r v z:ℕ) (hr:2≤r) (hv:2≤v):
    reducedTail (⟨z,v,r⟩:FlagDegree)=
      ⟨2*z*131072,1+2*v*131072,2*(r-1)*131072⟩:=by
  unfold reducedTail paddedTail
  rw [DQJ r v z hr,DRD r v z hr hv,
    EJF r v z hr hv]
  congr<;>omega

theorem DGA (r v z:ℕ) (hr:2≤r) (hv:2≤v):
    rationalFlag (⟨z,v,r⟩:FlagDegree)=
      ⟨131074*z,131074*(v-1)+2,131074*(r-2)+3⟩:=by
  unfold rationalFlag
  rw [DQJ r v z hr,DRD r v z hr hv,
    EJF r v z hr hv]
  congr<;>omega

theorem DWK (r v z:ℕ) (hr:2≤r) (hv:2≤v):
    movingFiber (⟨z,v,r⟩:FlagDegree)=⟨z,v,r+1⟩:=by
  unfold movingFiber
  rw [DQJ r v z hr,DRD r v z hr hv,
    EJF r v z hr hv]
  congr<;>omega

theorem ERT (r v z:ℕ) (hr:3≤r) (hv:2≤v):
    2*hybridCostC2 (⟨z+1,v,r⟩:FlagDegree)=
      hybridCostC2 ⟨z,v,r⟩+hybridCostC2 ⟨z+2,v,r⟩:=by
  have hr2:2≤r:=by omega
  unfold hybridCostC2 ASZ movingCut
  rw [DMJ r v z hr2 hv,
    DMJ r v (z+1) hr2 hv,
    DMJ r v (z+2) hr2 hv,
    DGA r v z hr2 hv,
    DGA r v (z+1) hr2 hv,
    DGA r v (z+2) hr2 hv,
    DWK r v z hr2 hv,
    DWK r v (z+1) hr2 hv,
    DWK r v (z+2) hr2 hv]
  unfold flagMixed
  simp only [add_zOnly,add_yz,add_all]
  ring

theorem EOF (r v z:ℕ) (hr:3≤r) (hv:2≤v):
    2*rawCost r v (z+1)=rawCost r v z+rawCost r v (z+2):=by
  rw [rawCost,rawCost,rawCost]
  simp only [ANG,if_pos (DRY r v z hr hv),
    if_pos (DRY r v (z+1) hr hv),
    if_pos (DRY r v (z+2) hr hv)]
  exact ERT r v z hr hv

theorem ZW (r v z d:ℕ)
    (hr:2≤r) (hv:1≤v):
    paddedTail (⟨z,v,r⟩:FlagDegree) d=
      ⟨2*z*d,1+2*v*d,2*(r-1)*d⟩:=by
  unfold paddedTail
  have hs:padS (⟨z,v,r⟩:FlagDegree)=r:=by
    simp only [padS]
    omega
  have hy:padY (⟨z,v,r⟩:FlagDegree)=r+v:=by
    simp only [padY,middle,hs]
    omega
  have ht:padT (⟨z,v,r⟩:FlagDegree)=r+v+z:=by
    simp only [padT,total,hy]
    omega
  rw [hs,hy,ht]
  congr<;>omega

theorem AZJ (r v z:ℕ)
    (hr:2≤r) (hv:1≤v):
    2*paddedCost 131072 131073 (⟨z+1,v,r⟩:FlagDegree)=
      paddedCost 131072 131073 ⟨z,v,r⟩+
        paddedCost 131072 131073 ⟨z+2,v,r⟩:=by
  unfold paddedCost
  rw [ZW r v z 131072 hr hv,
    ZW r v z 131073 hr hv,
    ZW r v (z+1) 131072 hr hv,
    ZW r v (z+1) 131073 hr hv,
    ZW r v (z+2) 131072 hr hv,
    ZW r v (z+2) 131073 hr hv]
  unfold flagMixed
  ring

theorem DUA (r z:ℕ) (hr:2≤r):
    2*rawCost r 1 (z+1)=rawCost r 1 z+rawCost r 1 (z+2):=by
  have hn (x:ℕ): ¬UG (⟨x,1,r⟩:FlagDegree):=by
    intro h
    have hbad:=h.2
    change r+2≤1+r at hbad
    omega
  simp only [rawCost,ANG,if_neg (hn z),if_neg (hn (z+1)),
    if_neg (hn (z+2))]
  exact AZJ r 1 z hr (by decide)

theorem DVS (v z:ℕ) (hv:2≤v):
    2*rawCost 2 v (z+1)=rawCost 2 v z+rawCost 2 v (z+2):=by
  have hn (x:ℕ): ¬UG (⟨x,v,2⟩:FlagDegree):=by
    intro h
    have hbad:=h.1
    change 3≤2 at hbad
    omega
  simp only [rawCost,ANG,if_neg (hn z),if_neg (hn (z+1)),
    if_neg (hn (z+2))]
  exact AZJ 2 v z (le_refl 2) (by omega)

theorem ZV (v z d:ℕ) (hv:2≤v):
    paddedTail (⟨z,v,1⟩:FlagDegree) d=
      ⟨2*z*d,1+2*(v-1)*d,2*d⟩:=by
  have hs:padS (⟨z,v,1⟩:FlagDegree)=2:=by rfl
  have hy:padY (⟨z,v,1⟩:FlagDegree)=v+1:=by
    unfold padY
    rw [hs]
    change max (v+1) 3=v+1
    omega
  have ht:padT (⟨z,v,1⟩:FlagDegree)=v+1+z:=by
    unfold padT
    rw [hy]
    change max (z+v+1) (v+1)=v+1+z
    omega
  change (⟨2*(padT (⟨z,v,1⟩:FlagDegree)-
      padY ⟨z,v,1⟩)*d,
    1+2*(padY (⟨z,v,1⟩:FlagDegree)-
      padS ⟨z,v,1⟩)*d,
    2*(padS (⟨z,v,1⟩:FlagDegree)-1)*d⟩:FlagDegree)=_
  rw [ht,hy,hs]
  have hz:v+1+z-(v+1)=z:=by omega
  have hvsub:v+1-2=v-1:=by omega
  rw [hz,hvsub]

theorem CRR (v z:ℕ) (hv:2≤v):
    2*paddedCost 131072 131073 (⟨z+1,v,1⟩:FlagDegree)=
      paddedCost 131072 131073 ⟨z,v,1⟩+
        paddedCost 131072 131073 ⟨z+2,v,1⟩:=by
  unfold paddedCost
  rw [ZV v z 131072 hv,
    ZV v z 131073 hv,
    ZV v (z+1) 131072 hv,
    ZV v (z+1) 131073 hv,
    ZV v (z+2) 131072 hv,
    ZV v (z+2) 131073 hv]
  unfold flagMixed
  ring

theorem DWE (v z:ℕ) (hv:2≤v):
    2*rawCost 1 v (z+1)=rawCost 1 v z+rawCost 1 v (z+2):=by
  have hn (x:ℕ): ¬UG (⟨x,v,1⟩:FlagDegree):=by
    intro h
    have hbad:=h.1
    change 3≤1 at hbad
    omega
  simp only [rawCost,ANG,if_neg (hn z),if_neg (hn (z+1)),
    if_neg (hn (z+2))]
  exact CRR v z hv

theorem YN (r z d:ℕ)
    (hr:2≤r) (hz:1≤z):
    paddedTail (⟨z,0,r⟩:FlagDegree) d=
      ⟨2*(z-1)*d,1+2*d,2*(r-1)*d⟩:=by
  have hs:padS (⟨z,0,r⟩:FlagDegree)=r:=by
    unfold padS
    change max r 2=r
    omega
  have hy:padY (⟨z,0,r⟩:FlagDegree)=r+1:=by
    unfold padY middle
    rw [hs]
    change max (0+r) (r+1)=r+1
    omega
  have ht:padT (⟨z,0,r⟩:FlagDegree)=r+z:=by
    unfold padT total
    rw [hy]
    change max (z+0+r) (r+1)=r+z
    omega
  change (⟨2*(padT (⟨z,0,r⟩:FlagDegree)-
      padY ⟨z,0,r⟩)*d,
    1+2*(padY (⟨z,0,r⟩:FlagDegree)-
      padS ⟨z,0,r⟩)*d,
    2*(padS (⟨z,0,r⟩:FlagDegree)-1)*d⟩:FlagDegree)=_
  rw [ht,hy,hs]
  have hzsub:r+z-(r+1)=z-1:=by omega
  rw [hzsub]
  congr<;>omega

theorem CMY (r z:ℕ)
    (hr:2≤r) (hz:1≤z):
    2*paddedCost 131072 131073 (⟨z+1,0,r⟩:FlagDegree)=
      paddedCost 131072 131073 ⟨z,0,r⟩+
        paddedCost 131072 131073 ⟨z+2,0,r⟩:=by
  unfold paddedCost
  rw [YN r z 131072 hr hz,
    YN r z 131073 hr hz,
    YN r (z+1) 131072 hr (by omega),
    YN r (z+1) 131073 hr (by omega),
    YN r (z+2) 131072 hr (by omega),
    YN r (z+2) 131073 hr (by omega)]
  have h1:z+1-1=z:=by omega
  have h2:z+2-1=z+1:=by omega
  rw [h1,h2]
  have hzsplit:z=(z-1)+1:=by omega
  rw [hzsplit]
  simp only [Nat.add_sub_cancel]
  unfold flagMixed
  ring

theorem DQW (r z:ℕ)
    (hr:2≤r) (hz:1≤z):
    2*rawCost r 0 (z+1)=rawCost r 0 z+rawCost r 0 (z+2):=by
  have hn (x:ℕ): ¬UG (⟨x,0,r⟩:FlagDegree):=by
    intro h
    have hbad:=h.2
    change r+2≤0+r at hbad
    omega
  simp only [rawCost,ANG,if_neg (hn z),if_neg (hn (z+1)),
    if_neg (hn (z+2))]
  exact CMY r z hr hz

theorem AEN (z d:ℕ) (hz:1≤z):
    paddedTail (⟨z,1,1⟩:FlagDegree) d=
      ⟨2*(z-1)*d,1+2*d,2*d⟩:=by
  unfold paddedTail padT padY padS middle total
  norm_num
  have hm:max (z+2) 3=z+2:=by omega
  rw [hm]
  congr<;>omega

theorem ACZ (z d:ℕ) (hz:2≤z):
    paddedTail (⟨z,0,1⟩:FlagDegree) d=
      ⟨2*(z-2)*d,1+2*d,2*d⟩:=by
  unfold paddedTail padT padY padS middle total
  norm_num
  have hm:max (z+1) 3=z+1:=by omega
  rw [hm]
  congr<;>omega

theorem FZC (r v z₁ z₂:ℕ) (hz:z₁≤z₂):
    Below (⟨z₁,v,r⟩:FlagDegree) ⟨z₂,v,r⟩:=by
  change r≤r∧v+r≤v+r∧z₁+v+r≤z₂+v+r
  omega

theorem GML (r v:ℕ):Monotone (rawCost r v):=by
  intro z₁ z₂ hz
  have hb:=FZC r v z₁ z₂ hz
  by_cases ha:UG (⟨z₁,v,r⟩:FlagDegree)
  · have ha' :UG (⟨z₂,v,r⟩:FlagDegree):=by
      rcases ha with ⟨hr,hv⟩
      exact ⟨hr,hv⟩
    simp only [rawCost,ANG,if_pos ha,if_pos ha']
    exact FXT hb
  · have ha' : ¬UG (⟨z₂,v,r⟩:FlagDegree):=by
      intro h
      apply ha
      rcases h with ⟨hr,hv⟩
      exact ⟨hr,hv⟩
    simp only [rawCost,ANG,if_neg ha,if_neg ha']
    exact GGS 131072 131073 hb

def forwardDiff (f:ℕ→ℕ) (n:ℕ):ℕ:=f (n+1)-f n

theorem EFS (z:ℕ) (hz:1≤z):
    2*rawCost 1 1 (z+1)=rawCost 1 1 z+rawCost 1 1 (z+2):=by
  have hn (x:ℕ): ¬UG (⟨x,1,1⟩:FlagDegree):=by
    intro h
    have hbad:=h.1
    change 3≤1 at hbad
    omega
  simp only [rawCost,ANG,if_neg (hn z),if_neg (hn (z+1)),
    if_neg (hn (z+2))]
  unfold paddedCost
  rw [AEN z 131072 hz,
    AEN z 131073 hz,
    AEN (z+1) 131072 (by omega),
    AEN (z+1) 131073 (by omega),
    AEN (z+2) 131072 (by omega),
    AEN (z+2) 131073 (by omega)]
  have h1:z+1-1=z:=by omega
  have h2:z+2-1=z+1:=by omega
  rw [h1,h2]
  have hzsplit:z=(z-1)+1:=by omega
  rw [hzsplit]
  simp only [Nat.add_sub_cancel]
  unfold flagMixed
  ring

theorem EDR (z:ℕ) (hz:2≤z):
    2*rawCost 1 0 (z+1)=rawCost 1 0 z+rawCost 1 0 (z+2):=by
  have hn (x:ℕ): ¬UG (⟨x,0,1⟩:FlagDegree):=by
    intro h
    have hbad:=h.1
    change 3≤1 at hbad
    omega
  simp only [rawCost,ANG,if_neg (hn z),if_neg (hn (z+1)),
    if_neg (hn (z+2))]
  unfold paddedCost
  rw [ACZ z 131072 hz,
    ACZ z 131073 hz,
    ACZ (z+1) 131072 (by omega),
    ACZ (z+1) 131073 (by omega),
    ACZ (z+2) 131072 (by omega),
    ACZ (z+2) 131073 (by omega)]
  have h1:z+1-2=z-1:=by omega
  have h2:z+2-2=z:=by omega
  rw [h1,h2]
  have hzsplit:z=(z-2)+2:=by omega
  rw [hzsplit]
  norm_num
  unfold flagMixed
  ring

theorem DWS (r v z:ℕ)
    (hr:1≤r) (hz:2≤z):
    2*rawCost r v (z+1)=rawCost r v z+rawCost r v (z+2):=by
  by_cases hr1:r=1
  · subst r
    by_cases hv0:v=0
    · subst v
      exact EDR z hz
    · by_cases hv1:v=1
      · subst v
        exact EFS z (by omega)
      · exact DWE v z (by omega)
  · have hr2:2≤r:=by omega
    by_cases hv0:v=0
    · subst v
      exact DQW r z hr2 (by omega)
    · by_cases hv1:v=1
      · subst v
        exact DUA r z hr2
      · by_cases hr3:r=2
        · subst hr3
          exact DVS v z (by omega)
        · exact EOF r v z (by omega) (by omega)

theorem DUB
    (f:ℕ→ℕ) (hmono:Monotone f)
    (n:ℕ) (hstep:2*f (n+1)=f n+f (n+2)):
    forwardDiff f n=forwardDiff f (n+1):=by
  have h₀:=hmono (Nat.le_add_right n 1)
  have h₁:=hmono (Nat.le_add_right (n+1) 1)
  unfold forwardDiff
  rw [show n+1+1=n+2 by omega]
  omega

theorem EIG
    (f:ℕ→ℕ) (hmono:Monotone f)
    (hstep: ∀n,2≤n→2*f (n+1)=f n+f (n+2))
    (z:ℕ) (hz:3≤z):
    f z=f 3+(f 4-f 3)*(z-3):=by
  have hdiffStep (n:ℕ) (hn:2≤n):
      forwardDiff f n=forwardDiff f (n+1):=
    DUB f hmono n (hstep n hn)
  have hdiff: ∀n,3≤n→forwardDiff f n=forwardDiff f 3:=by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base=>rfl
    | succ n hn ih=>exact (hdiffStep n (by omega)).symm.trans ih
  induction z,hz using Nat.le_induction with
  | base=>simp
  | succ n hn ih=>
      have hmn:=hmono (Nat.le_add_right n 1)
      have hd:=hdiff n hn
      have hd' :f (n+1)-f n=f 4-f 3:=by
        simpa only [forwardDiff,show 3+1=4 by decide] using hd
      calc
        f (n+1)=f n+(f (n+1)-f n):=
          (Nat.add_sub_of_le hmn).symm
        _=f n+(f 4-f 3):=by rw [hd']
        _=(f 3+(f 4-f 3)*(n-3))+(f 4-f 3):=by
          rw [ih]
        _=f 3+(f 4-f 3)*(n+1-3):=by
          have hnsub:n+1-3=(n-3)+1:=by omega
          rw [hnsub]
          ring

end ProximityPrize.SubmissionLower.UB
end PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorOrdinaryConcentration

namespace ProximityPrize.SubmissionLower.DWQ

open scoped BigOperators
open UB

set_option autoImplicit false

end ProximityPrize.SubmissionLower.DWQ
end PackedLocator_LocatorOrdinaryConcentration

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorPhase6800Audit

namespace ProximityPrize.SubmissionLower.DSA

open scoped BigOperators
open RCN095 DY CS
open FV

set_option autoImplicit false
set_option maxRecDepth 100000

theorem EQR
    (delta dT dY dS T YS S k:ℕ):
    LH delta dT dY dS T YS S k≤
      LH delta dT dY dS T YS S (k+1):=by
  induction k generalizing T YS S with
  | zero=>
      simp only [LH,Nat.zero_add]
      exact Nat.zero_le _
  | succ k ih=>
      simp only [LH]
      exact Nat.add_le_add_left
        (ih (T:=T-dT) (YS:=YS-dY) (S:=S-dS)) _

theorem CVK
    (delta dT dY dS T YS S:ℕ) {k₁ k₂:ℕ} (hk:k₁≤k₂):
    LH delta dT dY dS T YS S k₁≤
      LH delta dT dY dS T YS S k₂:=by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hk
  induction d with
  | zero=>simp
  | succ d ih=>
      calc
        LH delta dT dY dS T YS S k₁≤
            LH delta dT dY dS T YS S (k₁+d):=
          ih (Nat.le_add_right _ _)
        _≤LH delta dT dY dS T YS S ((k₁+d)+1):=
          EQR delta dT dY dS T YS S (k₁+d)
        _=LH delta dT dY dS T YS S (k₁+d.succ):=by
          congr 1

def baseZeroCap (rows:Array BaseRow) (r v:ℕ):ℕ:=
  if r=0 then 0 else baseTableCap rows (rawFlag r v 0)

def ESG (r v:ℕ):ℕ:=
  UB.rawCost r v 4-
    UB.rawCost r v 3

def EIB (rows:Array BaseRow) (R V r v z:ℕ):ℕ:=
  UB.rawCost r v 3+
    baseZeroCap rows (R-r) (V-v)+ESG r v*(z-3)

def DRG (rows:Array BaseRow) (R V r v:ℕ):Prop:=
  let q:=EJY rows R V
  let zero:=baseZeroCap rows (R-r) (V-v)
  UB.rawCost r v 0+zero≤q.z0∧
  UB.rawCost r v 1+zero≤q.z1∧
  UB.rawCost r v 2+zero≤q.z2∧
  match q.segments with
  | [s]=>
      s.start=3∧EIB rows R V r v s.start≤s.valueAtStart∧
        ESG r v≤s.slope
  | [s₁,s₂]=>
      s₁.start=3∧s₁.start<s₂.start∧
        EIB rows R V r v s₁.start≤s₁.valueAtStart∧
        EIB rows R V r v (s₂.start-1)≤
          s₁.evalAt (s₂.start-1)∧
        EIB rows R V r v s₂.start≤s₂.valueAtStart∧
        ESG r v≤s₂.slope
  | _=>False

instance (rows:Array BaseRow) (R V r v:ℕ):
    Decidable (DRG rows R V r v):=by
  unfold DRG
  dsimp only
  generalize hq:EJY rows R V=q
  cases hs:q.segments with
  | nil=>
      simp only [hs]
      infer_instance
  | cons s tail=>
      cases ht:tail with
      | nil=>
          simp only [hs,ht]
          infer_instance
      | cons s₂ rest=>
          cases hu:rest with
          | nil=>
              simp only [hs,ht,hu]
              infer_instance
          | cons s₃ rest₃=>
              simp only [hs,ht,hu]
              infer_instance

def EIY (rows:Array BaseRow) (R:ℕ):Prop:=
  ∀V ∈ List.range (136-R),
    ∀r ∈ List.range (R+1),1≤r→
      ∀v ∈ List.range (V+1),(r<R∨v=V)→
        DRG rows R V r v

instance (rows:Array BaseRow) (R:ℕ):Decidable (EIY rows R):=by
  unfold EIY
  infer_instance

def EHH (rows:Array BaseRow):Prop:=
  ∀R ∈ List.range 30,1≤R→EIY rows R

instance (rows:Array BaseRow):Decidable (EHH rows):=by
  unfold EHH
  infer_instance

end ProximityPrize.SubmissionLower.DSA
end PackedLocator_LocatorPhase6800Audit

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorBatchPowerRoute

namespace ProximityPrize.SubmissionLower.DOH

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open IL KI CS TB AAV BPN KZ

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

end

end ProximityPrize.SubmissionLower.DOH
end PackedLocator_LocatorBatchPowerRoute

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorFastKernelArithmetic

namespace ProximityPrize.SubmissionLower.RZ

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 RCN302
open IL

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def _Q9 (ni nj offset L:ℕ):ℕ:=
  ni*nj*(L+1-offset)-
    (nj*(ni*(ni-1)/2)+ni*(nj*(nj-1)/2))

private theorem pairIndexSum (ni nj:ℕ):
    (∑ i ∈ Finset.range ni,∑ j ∈ Finset.range nj,(i+j))=
      nj*(ni*(ni-1)/2)+ni*(nj*(nj-1)/2):=by
  calc
    (∑ i ∈ Finset.range ni,∑ j ∈ Finset.range nj,(i+j))=
        ∑ i ∈ Finset.range ni,
          (nj*i+nj*(nj-1)/2):=by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_add_distrib,Finset.sum_range_id]
      simp only [Finset.sum_const,Finset.card_range,Nat.nsmul_eq_mul]
    _=nj*(ni*(ni-1)/2)+ni*(nj*(nj-1)/2):=by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_range_id]
      simp only [Finset.sum_const,Finset.card_range,Nat.nsmul_eq_mul]

theorem AOA (ni nj offset L:ℕ)
    (hbound:offset+(ni-1)+(nj-1)≤L):
    (∑ i ∈ Finset.range ni,
      ∑ j ∈ Finset.range nj,(L+1-offset-i-j))=
      _Q9 ni nj offset L:=by
  have hpoint: ∀i ∈ Finset.range ni,∀j ∈ Finset.range nj,
      (L+1-offset-i-j)+(i+j)=L+1-offset:=by
    intro i hi j hj
    have hil:i≤ni-1:=by
      have:=Finset.mem_range.mp hi
      omega
    have hjl:j≤nj-1:=by
      have:=Finset.mem_range.mp hj
      omega
    omega
  have hadd:
      (∑ i ∈ Finset.range ni,
        ∑ j ∈ Finset.range nj,(L+1-offset-i-j))+
          (∑ i ∈ Finset.range ni,
            ∑ j ∈ Finset.range nj,(i+j))=
        ni*nj*(L+1-offset):=by
    calc
      _= ∑ i ∈ Finset.range ni,
          ((∑ j ∈ Finset.range nj,(L+1-offset-i-j))+
            ∑ j ∈ Finset.range nj,(i+j)):=by
          rw [Finset.sum_add_distrib]
      _= ∑ i ∈ Finset.range ni,
          ∑ j ∈ Finset.range nj,
            ((L+1-offset-i-j)+(i+j)):=by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_add_distrib.symm
      _= ∑ i ∈ Finset.range ni,
          ∑ _j ∈ Finset.range nj,(L+1-offset):=by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hpoint i hi j hj
      _=ni*nj*(L+1-offset):=by
          simp only [Finset.sum_const,Finset.card_range,Nat.nsmul_eq_mul]
          ring
  rw [pairIndexSum] at hadd
  unfold _Q9
  omega

theorem BBK (M L s:ℕ)
    (hbound:M+s≤L):
    ALC M L s=_Q9 (M+1) (s+1) 0 L:=by
  simpa only [ALC,Nat.zero_add,Nat.sub_zero] using
    AOA (M+1) (s+1) 0 L (by omega)

theorem BYC (M L s h:ℕ)
    (hbound:M+s≤L):
    TS M L s h=
      _Q9 (M+1-h) (s+1-h) h L:=by
  by_cases hM:h≤M
  · by_cases hs:h≤s
    · have hL:h≤L:=by omega
      have hshape:M-h+(s-h)≤L-h:=by omega
      have heq:TS M L s h=
          ALC (M-h) (L-h) (s-h):=by
        have hMr:M+1-h=M-h+1:=by omega
        have hsr:s+1-h=s-h+1:=by omega
        have hLr:L+1-h=L-h+1:=by omega
        unfold TS ALC
        rw [hMr,hsr,hLr]
      rw [heq,BBK _ _ _ hshape]
      have hMr:M+1-h=M-h+1:=by omega
      have hsr:s+1-h=s-h+1:=by omega
      have hLr:L+1-h=L-h+1:=by omega
      unfold _Q9
      rw [hMr,hsr,hLr]
      simp only [Nat.sub_zero]
    · have hz:s+1-h=0:=by omega
      simp [TS,_Q9,hz]
  · have hz:M+1-h=0:=by omega
    simp [TS,_Q9,hz]

theorem CRY (M L s h:ℕ)
    (hbound:M+s≤L):
    AAT M L s h=
      _Q9 (M+1) (s+1) 0 L-
        _Q9 (M+1-h) (s+1-h) h L:=by
  unfold AAT
  rw [BBK M L s hbound,
    BYC M L s h hbound]

def AFW (m L s:ℕ):ℕ:=
  ADH (fun r=>
    let M:=min r L
    let h:=min (r+1) (m-r)
    _Q9 (M+1) (s+1) 0 L-
      _Q9 (M+1-h) (s+1-h) h L) m

theorem AZU (m L s:ℕ)
    (hshape:m+s≤L+1):
    ES m L s=AFW m L s:=by
  unfold ES AFW
  rw [VJ]
  apply Finset.sum_congr rfl
  intro r hr
  have hrm:r<m:=Finset.mem_range.mp hr
  have hb:min r L+s≤L:=by
    have hm:min r L≤r:=Nat.min_le_left _ _
    omega
  exact CRY
    (min r L) L s (min (r+1) (m-r)) hb

private theorem CIO (n:ℕ):
    2*n.choose 2+n=n*n:=by
  induction n with
  | zero=>decide
  | succ n ih=>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      calc
        2*(n+n.choose 2)+(n+1)=
            (2*n.choose 2+n)+(2*n+1):=by ring
        _=n*n+(2*n+1):=by rw [ih]
        _=(n+1)*(n+1):=by ring

private theorem DMX (n:ℕ):
    ADH (fun i=>i*i) n=
      2*n.choose 3+n.choose 2:=by
  induction n with
  | zero=>decide
  | succ n ih=>
      rw [BKB,ih,Nat.choose_succ_succ,
        Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      rw [← CIO n]
      ring

private theorem DEG (n:ℕ):
    (∑ i ∈ Finset.range n,i*i)=
      2*n.choose 3+n.choose 2:=by
  rw [← VJ,DMX]

private theorem DMQ (U C w N:ℕ):
    (∑ h ∈ Finset.range N,(U+h)*(C+w*h))=
      N*(U*C)+(U*w+C)*N.choose 2+
        w*(2*N.choose 3+N.choose 2):=by
  calc
    (∑ h ∈ Finset.range N,(U+h)*(C+w*h))=
        ∑ h ∈ Finset.range N,
          (U*C+(U*w+C)*h+w*(h*h)):=by
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _=N*(U*C)+(U*w+C)*N.choose 2+
          w*(2*N.choose 3+N.choose 2):=by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_range,Nat.nsmul_eq_mul]
      rw [← Finset.mul_sum,← Finset.mul_sum,Finset.sum_range_id,
        DEG,← Nat.choose_two_right]

private theorem BMH (n:ℕ):
    3*n.choose 3+2*n.choose 2=n*n.choose 2:=by
  induction n with
  | zero=>decide
  | succ n ih=>
      rw [Nat.choose_succ_succ,Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      calc
        3*(n.choose 2+n.choose 3)+
              2*(n+n.choose 2)=
            (3*n.choose 3+2*n.choose 2)+
              (2*n.choose 2+n)+(n.choose 2+n):=by ring
        _=n*n.choose 2+n*n+(n.choose 2+n):=by
          rw [ih,CIO]
        _=(n+1)*(n+n.choose 2):=by ring

private theorem FAE
    (U C w r j q N wm T V:ℕ)
    (hC:C=r+j) (hN:N+j=q+1) (hw:wm+2=w)
    (hsq:2*T+N=N*N)
    (hcub:3*V+2*T=N*T):
    N*(U*C)+(U*w+C)*T+w*(2*V+T)=
      U*(r+q)*N+
        (U*wm+r+q+(wm+1))*T+
          (2*wm+1)*V:=by
  have hCz:(C:ℤ)=(r:ℤ)+j:=by exact_mod_cast hC
  have hNz:(N:ℤ)+j=(q:ℤ)+1:=by exact_mod_cast hN
  have hwz:(wm:ℤ)+2=w:=by exact_mod_cast hw
  have hsqz:2*(T:ℤ)+N=N*N:=by exact_mod_cast hsq
  have hcubz:3*(V:ℤ)+2*T=N*T:=by exact_mod_cast hcub
  have hqz:(q:ℤ)=N+j-1:=by linarith
  apply Nat.cast_injective (R:=ℤ)
  push_cast
  rw [hCz,← hwz,hqz]
  linear_combination (U:ℤ)*hsqz+hcubz

private def BQC (q r w L j:ℕ):ℕ:=
  let U:=L+1-q
  let N:=q+1-j
  U*(r+q)*N.choose 1+
    (U*(w-2)+r+q+((w-2)+1))*N.choose 2+
      (2*(w-2)+1)*N.choose 3

private theorem BNK
    (q r w L j:ℕ) (hw:2≤w) (hj:j≤q)
    (hL:q≤L) (hres:r+j≤w):
    (∑ i ∈ Finset.range (q+1),
      (L+1-i-j)*
        (q*w+r-w*i-(w-1)*j))=
      BQC q r w L j:=by
  let N:=q+1-j
  let U:=L+1-q
  let C:=r+j
  have hNpos:0<N:=by simp only [N];omega
  have hNq:N≤q+1:=by simp only [N];omega
  have hsubset:Finset.range N ⊆ Finset.range (q+1):=
    Finset.range_mono hNq
  have htrim:
      (∑ i ∈ Finset.range N,
        (L+1-i-j)*
          (q*w+r-w*i-(w-1)*j))=
      ∑ i ∈ Finset.range (q+1),
        (L+1-i-j)*
          (q*w+r-w*i-(w-1)*j):=by
    apply Finset.sum_subset hsubset
    intro i hi hinot
    have hiq:i≤q:=by
      have:=Finset.mem_range.mp hi
      omega
    have hiN:N≤ i:=by
      by_contra hni
      exact hinot (Finset.mem_range.mpr (by omega))
    have hij:q+1≤ i+j:=by simp only [N] at hiN;omega
    have hr:r≤w-j:=by omega
    have hmul:w*(q+1)≤w*(i+j):=
      Nat.mul_le_mul_left w hij
    have hwj:w*j-j=(w-1)*j:=by
      symm
      rw [Nat.sub_mul]
      simp only [Nat.one_mul]
    have hweight:q*w+r≤w*i+(w-1)*j:=by
      calc
        q*w+r≤q*w+(w-j):=Nat.add_le_add_left hr _
        _=w*(q+1)-j:=by
          rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm w q]
          omega
        _≤w*(i+j)-j:=Nat.sub_le_sub_right hmul j
        _=w*i+(w-1)*j:=by
          have hjwj:j≤w*j:=
            Nat.le_mul_of_pos_left j (by omega)
          rw [Nat.mul_add,Nat.add_sub_assoc hjwj,hwj]
    have hz:q*w+r-w*i-(w-1)*j=0:=by
      rw [Nat.sub_sub]
      exact Nat.sub_eq_zero_of_le hweight
    simp only [hz,Nat.mul_zero]
  have hreflect:
      (∑ i ∈ Finset.range N,
        (L+1-i-j)*
          (q*w+r-w*i-(w-1)*j))=
      ∑ h ∈ Finset.range N,(U+h)*(C+w*h):=by
    rw [← Finset.sum_range_reflect (fun i=>
      (L+1-i-j)*
        (q*w+r-w*i-(w-1)*j)) N]
    apply Finset.sum_congr rfl
    intro h hh
    have hhN:h<N:=Finset.mem_range.mp hh
    have hidx:N-1-h=q-j-h:=by
      simp only [N]
      omega
    have hqsplit:q=(q-j-h)+j+h:=by omega
    have hwj:w*j=(w-1)*j+j:=by
      have hw' :w-1+1=w:=by omega
      calc
        w*j=(w-1+1)*j:=by rw [hw']
        _=(w-1)*j+j:=by ring
    have htotal:
        q*w+r=w*(q-j-h)+(w-1)*j+
          (r+j+w*h):=by
      calc
        q*w+r=((q-j-h)+j+h)*w+r:=by rw [← hqsplit]
        _=w*(q-j-h)+w*j+w*h+r:=by ring
        _=w*(q-j-h)+(w-1)*j+
            (r+j+w*h):=by rw [hwj];ring
    have hfirst:L+1-(N-1-h)-j=U+h:=by
      simp only [N,U]
      omega
    have hsecond:
        q*w+r-w*(N-1-h)-(w-1)*j=
          C+w*h:=by
      rw [hidx]
      simp only [C]
      omega
    rw [hfirst,hsecond]
  have hsum:=DMQ U C w N
  have hNj:N+j=q+1:=by simp only [N];omega
  have hwsub:w-2+2=w:=by omega
  have hsq:=CIO N
  have hcub:=BMH N
  rw [← htrim,hreflect,hsum]
  change N*(U*C)+(U*w+C)*N.choose 2+
      w*(2*N.choose 3+N.choose 2)=
    U*(r+q)*N.choose 1+
      (U*(w-2)+r+q+((w-2)+1))*N.choose 2+
        (2*(w-2)+1)*N.choose 3
  simp only [Nat.choose_one_right]
  exact FAE
    (U:=U) (C:=C) (w:=w) (r:=r) (j:=j) (q:=q)
    (N:=N) (wm:=w-2) (T:=N.choose 2) (V:=N.choose 3)
    (by rfl) hNj hwsub hsq hcub

private theorem DMD (N s k:ℕ)
    (hs:s≤N):
    (∑ j ∈ Finset.range (s+1),(N-j).choose k)+
        (N-s).choose (k+1)=(N+1).choose (k+1):=by
  induction s with
  | zero=>
      simp only [Nat.sub_zero,Finset.range_one,Finset.sum_singleton]
      exact (Nat.choose_succ_succ' N k).symm
  | succ s ih=>
      have hs' :s≤N:=by omega
      rw [Finset.sum_range_succ]
      have hold:=ih hs'
      have hpred:N-s=(N-(s+1))+1:=by omega
      have hp:=Nat.choose_succ_succ' (N-(s+1)) k
      rw [← hpred] at hp
      omega

private theorem BDW (N s k:ℕ)
    (hs:s≤N):
    (∑ j ∈ Finset.range (s+1),(N-j).choose k)=
      (N+1).choose (k+1)-(N-s).choose (k+1):=by
  have h:=DMD N s k hs
  omega

def smallChoose (n k:ℕ):ℕ:=
  n.descFactorial k/Nat.factorial k

private theorem APG (n k:ℕ):
    n.choose k=smallChoose n k:=by
  simpa only [smallChoose] using
    Nat.choose_eq_descFactorial_div_factorial n k

def OM (q r w L s:ℕ):ℕ:=
  let U:=L+1-q
  let c1:=U*(r+q)
  let c2:=U*(w-2)+r+q+((w-2)+1)
  let c3:=2*(w-2)+1
  c1*(smallChoose (q+2) 2-smallChoose (q+1-s) 2)+
    c2*(smallChoose (q+2) 3-smallChoose (q+1-s) 3)+
      c3*(smallChoose (q+2) 4-smallChoose (q+1-s) 4)

theorem GQ
    (q r w L s:ℕ) (hw:2≤w) (hsq:s≤q)
    (hL:q≤L) (hres:r+s≤w):
    AW (q*w+r) w L s=
      OM q r w L s:=by
  have hcutoff:q+1≤L+1:=by omega
  have hweight:q*w+r≤w*(q+1):=by
    have hrw:r≤w:=by omega
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm w q]
    omega
  rw [AJA
    (q*w+r) w L s (q+1) hcutoff hweight]
  rw [Finset.sum_comm]
  have hrows:
      (∑ j ∈ Finset.range (s+1),
        ∑ i ∈ Finset.range (q+1),
          (L+1-i-j)*
            (q*w+r-w*i-(w-1)*j))=
      ∑ j ∈ Finset.range (s+1),
        BQC q r w L j:=by
    apply Finset.sum_congr rfl
    intro j hj
    have hjs:j≤s:=by
      have:=Finset.mem_range.mp hj
      omega
    exact BNK q r w L j hw
      (hjs.trans hsq) hL ((Nat.add_le_add_left hjs r).trans hres)
  rw [hrows]
  let U:=L+1-q
  let c1:=U*(r+q)
  let c2:=U*(w-2)+r+q+((w-2)+1)
  let c3:=2*(w-2)+1
  have h1:=BDW (q+1) s 1 (by omega)
  have h2:=BDW (q+1) s 2 (by omega)
  have h3:=BDW (q+1) s 3 (by omega)
  unfold BQC
  change (∑ j ∈ Finset.range (s+1),
      (c1*(q+1-j).choose 1+
        c2*(q+1-j).choose 2+
          c3*(q+1-j).choose 3))=_
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,h1,h2,h3]
  unfold OM
  rw [← APG,← APG,
    ← APG,← APG,
    ← APG,← APG]

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index

theorem KJ
    (D L s m gap:ℕ) (u0 u1:I→K)
    (hnumeric:gap≤AW D 131071 L s-
      262144*ES m L s):
    gap≤Module.finrank K
      (IJ (K:=K) D 131071 L s m
        IRSProfile.domain u0 u1):=by
  have hcard:Fintype.card I=262144:=by
    norm_num [I,IRSProfile.Index]
  have hlo:=AZN
    (K:=K) D 131071 L s m IRSProfile.domain u0 u1
  have hlo' :=hcard ▸ hlo
  exact hnumeric.trans hlo'

end ProximityPrize.SubmissionLower.RZ
end PackedLocator_LocatorFastKernelArithmetic

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorBatchPhase6800

namespace ProximityPrize.SubmissionLower.MM

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266
open DY CS KZ DOH AAV FV

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

def BF (H:P4) (A:Finset (RegularIndex H)):FlagDegree:=
  sumFlag A (BG H)

private theorem BAB
    (weights:Fin 4→ℕ) (H:P4) (A:Finset (RegularIndex H)):
    wt weights (CK H A)= ∑ F ∈ A,wt weights F.1:=by
  have h:=EBV weights A
    (fun F:RegularIndex H=>F.1)
    (fun F _hF=>BMK H F)
  simpa only [CK,wt] using h

theorem JM (H:P4) (A:Finset (RegularIndex H)):
    (BF H A).all=
      wt BE (CK H A):=by
  rw [BF,sumFlag_all]
  calc
    (∑ F ∈ A,(BG H F).all)=
        ∑ F ∈ A,wt BE F.1:=by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (GX F.1).1
    _=wt BE (CK H A):=
      (BAB BE H A).symm

theorem IF (H:P4)
    (A:Finset (RegularIndex H)):
    middle (BF H A)=
      wt BC (CK H A):=by
  rw [BF,AQT]
  calc
    (∑ F ∈ A,middle (BG H F))=
        ∑ F ∈ A,wt BC F.1:=by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (GX F.1).2.1
    _=wt BC (CK H A):=
      (BAB BC H A).symm

theorem KH (H:P4)
    (A:Finset (RegularIndex H)):
    total (BF H A)=
      wt AT (CK H A):=by
  rw [BF,AXF]
  calc
    (∑ F ∈ A,total (BG H F))=
        ∑ F ∈ A,wt AT F.1:=by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (GX F.1).2.2
    _=wt AT (CK H A):=
      (BAB AT H A).symm

theorem LY (H:P4)
    {A B:Finset (RegularIndex H)} (hAB:A ⊆ B):
    (BF H A).all≤(BF H B).all∧
      middle (BF H A)≤
        middle (BF H B)∧
      total (BF H A)≤
        total (BF H B):=by
  simp only [BF,sumFlag_all,AQT,AXF]
  exact ⟨Finset.sum_le_sum_of_subset hAB,
    Finset.sum_le_sum_of_subset hAB,Finset.sum_le_sum_of_subset hAB⟩

theorem AAN (H:P4)
    {A B:Finset (RegularIndex H)} (hAB:A ⊂ B):
    (BF H A).all<(BF H B).all:=by
  have hnBA: ¬B ⊆ A:=by
    intro hBA
    exact hAB.ne (Finset.Subset.antisymm hAB.subset hBA)
  rw [Finset.subset_iff] at hnBA
  push_neg at hnBA
  obtain ⟨F,hFB,hFA⟩:=hnBA
  simp only [BF,sumFlag_all]
  exact Finset.sum_lt_sum_of_subset hAB.subset hFB hFA
    (JH H F)
    (fun _ _ _=>Nat.zero_le _)

theorem AML (H:P4)
    {A B:Finset (RegularIndex H)} (hAB:A ⊆ B):
    RawBelow (BF H A) (BF H B):=by
  refine ⟨?_,?_,?_⟩
  · change (∑ F ∈ A,(BG H F).all)≤
      ∑ F ∈ B,(BG H F).all
    exact Finset.sum_le_sum_of_subset hAB
  · change (∑ F ∈ A,(BG H F).yz)≤
      ∑ F ∈ B,(BG H F).yz
    exact Finset.sum_le_sum_of_subset hAB
  · change (∑ F ∈ A,(BG H F).zOnly)≤
      ∑ F ∈ B,(BG H F).zOnly
    exact Finset.sum_le_sum_of_subset hAB

theorem BCO (q:Potential) (H:P4)
    (A:Finset (RegularIndex H)):
    (∑ F ∈ A,q.eval (BG H F))=
      q.eval (BF H A):=by
  simp only [Potential.eval,Finset.sum_add_distrib,← Finset.mul_sum,
    BF,AXF,AQT,sumFlag_all]

end

end ProximityPrize.SubmissionLower.MM
end PackedLocator_LocatorBatchPhase6800

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorHybridCells

namespace ProximityPrize.SubmissionLower.FA
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def cellA (t y:Nat):Nat:=t-y
def cellB (y r:Nat):Nat:=y-r-1
def cellS (r:Nat):Nat:=r-2

def cellSupport (t y r:Nat):BT:=
  support (cellA t y) (cellB y r) (cellS r)

def TX (t y r:Nat):FlagDegree:=
  CI (cellSupport t y r) (w+1)

def BGD (t y r:Nat):FlagDegree:=
  RCN206.ZR (cellA t y) (cellB y r) (cellS r)

def cellRational (t y r:Nat):FlagDegree:=
  ⟨(w+1)*cellA t y+(BGD t y r).zOnly,
    (w+1)*cellB y r+(BGD t y r).yz+1,
    (w+1)*cellS r+(BGD t y r).all⟩

def BZO (t y r:Nat):FlagDegree:=
  RCN206.fiberFlag (cellA t y) (cellB y r) (cellS r)

def BUV (t y r:Nat):FlagDegree:=
  cellRational t y r+⟨0,w+1,2*(w+1)⟩

theorem flag_ext {f g:FlagDegree} (h1:f.zOnly=g.zOnly)
    (h2:f.yz=g.yz) (h3:f.all=g.all):f=g:=by
  cases f;cases g;simp_all

theorem ECN (t y r:Nat):
    BUV t y r=
      center (cellA t y) (cellB y r) (cellS r)+
        (w+1) • RCN206.surfaceFlag (cellA t y) (cellB y r) (cellS r):=by
  refine flag_ext ?_ ?_ ?_<;>
    simp only [center,direction,unitYZFlag,BUV,cellRational,
      BGD,RCN206.ZR,RCN206.surfaceFlag,
      add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]<;>ring

theorem CUY
    {Omega:Type} [Field Omega]
    {G T H:MvPolynomial (Fin 3) Omega}
    {surfaceFlag firstTailFlag:FlagDegree}
    (B:FE (G:=G) (T:=T) (H:=H)
      surfaceFlag firstTailFlag)
    (C:AU Omega G T H)
    {f g:FlagDegree}
    (hz:f.zOnly≤g.zOnly) (hy:f.yz≤g.yz) (ha:f.all≤g.all):
    B.weightedCost f C≤B.weightedCost g C:=by
  simp only [FE.weightedCost]
  gcongr

theorem GHV (t y r:Nat):
    (cellRational t y r).yz=131074*cellB y r+2:=by
  simp only [cellRational,BGD,RCN206.ZR,w]
  omega

theorem FML (t y r errorCap:Nat) (hb:r+2≤y)
    (hcap:errorCap+1≤131076):
    errorCap+1≤(cellRational t y r).yz:=by
  rw [GHV]
  have hB:1≤cellB y r:=by
    simp only [cellB]
    omega
  have:=Nat.mul_le_mul_left 131074 hB
  omega

end
end ProximityPrize.SubmissionLower.FA
end PackedLocator_LocatorHybridCells

section PackedLocator_LocatorHybridCellsC1

namespace ProximityPrize.SubmissionLower.GJ
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
open FA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def MK (t y r:Nat):FlagDegree:=cellRational t y r

theorem FEW (s delay mult:ℕ) (hs:1≤s)
    (hdm:delay≤mult) (hm6:6≤mult):
    (2*s+3)*(131072+delay)≤mult*(131072*s+(2*s+3)):=by
  have key:131072*(2*s+3)≤mult*(131072*s):=by
    calc 131072*(2*s+3)≤131072*(6*s):=by omega
      _=6*(131072*s):=by ring
      _≤mult*(131072*s):=Nat.mul_le_mul_right _ hm6
  calc
    (2*s+3)*(131072+delay)≤(2*s+3)*(131072+mult):=
      Nat.mul_le_mul_left _ (by omega)
    _=131072*(2*s+3)+mult*(2*s+3):=by ring
    _≤mult*(131072*s)+mult*(2*s+3):=Nat.add_le_add_right key _
    _=mult*(131072*s+(2*s+3)):=by ring

theorem DOF (B delay mult:ℕ) (hB:1≤B)
    (hdm:delay≤mult) (hm6:6≤mult):
    1+(2*B+4)*(131072+delay)≤mult*(131072*B+2*B+5):=by
  have key:1+131072*(2*B+4)≤mult*(131072*B)+mult:=by
    have h6:6*(131072*B)+6≤mult*(131072*B)+mult:=by
      have:=Nat.mul_le_mul_right (131072*B) hm6
      omega
    have hB' :262144*B+524289≤786432*B+6:=by
      have:(524288:ℕ)≤524288*B:=by
        calc (524288:ℕ)=524288*1:=by ring
          _≤524288*B:=Nat.mul_le_mul_left _ hB
      omega
    calc 1+131072*(2*B+4)=262144*B+524289:=by ring
      _≤786432*B+6:=hB'
      _=6*(131072*B)+6:=by ring
      _≤mult*(131072*B)+mult:=h6
  calc
    1+(2*B+4)*(131072+delay)≤1+(2*B+4)*(131072+mult):=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    _=(1+131072*(2*B+4))+mult*(2*B+4):=by ring
    _≤(mult*(131072*B)+mult)+mult*(2*B+4):=
      Nat.add_le_add_right key _
    _=mult*(131072*B+2*B+5):=by ring

theorem EWB (A delay mult:ℕ) (hA:1≤A)
    (hdm:delay≤mult) (hm6:6≤mult):
    1+(2*A+4)*(131072+delay)≤mult*(131072*A+2*A+5):=
  DOF A delay mult hA hdm hm6

theorem FNF (t y r errorCap:Nat) (hb:r+2≤y)
    (hcap:errorCap+1≤131076):
    errorCap+1≤(MK t y r).yz:=
  FML t y r errorCap hb hcap

end
end ProximityPrize.SubmissionLower.GJ
end PackedLocator_LocatorHybridCellsC1

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorHybridTailProvider

namespace ProximityPrize.SubmissionLower.IB
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

section BoundedProvider
variable {K0 Omega Iota:Type} [Field K0] [Field Omega] [IsAlgClosed Omega]
  {phi:Polynomial K0→+*Omega} {Gamma0:Finset K0} {x0:Iota→K0}
  {pchar errorCap d:ℕ} [CharP Omega pchar]
  {flag0 tailFlag1 tailFlag2:FlagDegree}
  {support0:RCN275.BT}

structure AKI
    (S:FH phi Gamma0 x0 pchar errorCap flag0 d support0)
    (divisorBound:optParam ℕ (flagMixed flag0 tailFlag1 tailFlag2)) where
  budgetFamily:FE
    (G:=S.G) (T:=_Q2 phi S.F (d+1))
    (H:=CR phi S.F) flag0 tailFlag1
  multiplicity:CM S→ℕ
  cost:CM S→ℕ
  one_le_multiplicity: ∀C,1≤multiplicity C
  EHX:errorCap+1≤tailFlag2.yz
  cost_sum_le:(∑ C,cost C)≤divisorBound
  CRK: ∀C,
    (HF Omega S.G (_Q2 phi S.F (d+1))
      (CR phi S.F) Gamma0
      (DK phi S.selected) C).card≤cost C
  dichotomy: ∀C,
    (∃delay,1≤delay∧delay≤multiplicity C∧
      _Q2 phi S.F (d+1+delay) ∉ C.1)∨
    ((∀delay,_Q2 phi S.F (d+1+delay) ∈ C.1)∧
      (HF Omega S.G (_Q2 phi S.F (d+1))
        (CR phi S.F) Gamma0
        (DK phi S.selected) C).card≤
          (errorCap+1)*budgetFamily.yzCost C)

theorem BIF
    (S:FH phi Gamma0 x0 pchar errorCap flag0 d support0)
    {divisorBound:ℕ}
    (P:AKI
      (tailFlag1:=tailFlag1) (tailFlag2:=tailFlag2) S divisorBound):
    Gamma0.card≤divisorBound:=by
  classical
  let T1:=_Q2 phi S.F (d+1)
  let H:=CR phi S.F
  let point:=DK phi S.selected
  have hG: ∀gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) S.G=0:=S.on_component
  have hT1: ∀gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) T1=0:=by
    intro gamma hgamma
    exact CJY phi S.F S.selected gamma d
      (S.degree_le gamma hgamma) (S.solution gamma hgamma)
  have hH: ∀gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) H ≠ 0:=by
    intro gamma hgamma
    exact WQ phi S.selected gamma
      (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
  have hcover:Gamma0.card≤
      ∑ C:AU Omega S.G T1 H,
        (HF Omega S.G T1 H Gamma0 point C).card:=
    WX Omega S.G T1 H Gamma0 point hG hT1 hH
  calc
    Gamma0.card≤ ∑ C:AU Omega S.G T1 H,
        (HF Omega S.G T1 H Gamma0 point C).card:=hcover
    _≤ ∑ C:AU Omega S.G T1 H,P.cost C:=
      Finset.sum_le_sum (fun C _↦P.CRK C)
    _≤divisorBound:=P.cost_sum_le

end BoundedProvider

variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap:ℕ}

end
end ProximityPrize.SubmissionLower.IB
end PackedLocator_LocatorHybridTailProvider

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorDerivativeChain

namespace ProximityPrize.SubmissionLower.UA

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
  UniqueFactorizationMonoid.strongNormalizationMonoid

def dR (j:ℕ) (F:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
  (MvPolynomial.pderiv (2:Fin 4))^[j] F

@[simp] theorem dR_zero (F:MvPolynomial (Fin 4) K):dR 0 F=F:=rfl

theorem dR_succ (j:ℕ) (F:MvPolynomial (Fin 4) K):
    dR (j+1) F=MvPolynomial.pderiv (2:Fin 4) (dR j F):=by
  unfold dR
  exact Function.iterate_succ_apply' _ _ _

theorem GBV (Q:MvPolynomial (Fin 4) K) (D w L s:ℕ)
    (hbox:Q ∈ BA K D w L s):
    MvPolynomial.pderiv (2:Fin 4) Q ∈ BA K D w L s:=by
  intro d hd
  have hmem:=AFO (2:Fin 4) Q d hd
  obtain ⟨ht,hs,hc⟩:=hbox hmem
  have h0:((d+Finsupp.single (2:Fin 4) 1:Fin 4→₀ ℕ):Fin 4→ℕ) 0=d 0:=by
    simp [Finsupp.single_apply]
  have h1:((d+Finsupp.single (2:Fin 4) 1:Fin 4→₀ ℕ):Fin 4→ℕ) 1=d 1:=by
    simp [Finsupp.single_apply]
  have h2:((d+Finsupp.single (2:Fin 4) 1:Fin 4→₀ ℕ):Fin 4→ℕ) 2=d 2+1:=by
    simp [Finsupp.single_apply]
  have h3:((d+Finsupp.single (2:Fin 4) 1:Fin 4→₀ ℕ):Fin 4→ℕ) 3=d 3:=by
    simp [Finsupp.single_apply]
  simp only [h0,h1,h2,h3] at ht hs hc
  have hw1:(w-1)*d 2≤(w-1)*(d 2+1):=Nat.mul_le_mul_left _ (by omega)
  exact ⟨by omega,by omega,by omega⟩

theorem dR_mem_box (j:ℕ) (Q:MvPolynomial (Fin 4) K) (D w L s:ℕ)
    (hbox:Q ∈ BA K D w L s):
    dR j Q ∈ BA K D w L s:=by
  induction j with
  | zero=>simpa using hbox
  | succ k ih=>
      rw [dR_succ]
      exact GBV _ D w L s ih

theorem BLP (j:ℕ) (F:MvPolynomial (Fin 4) K):
    (dR j F).degreeOf 2≤F.degreeOf 2-j:=by
  induction j with
  | zero=>simp
  | succ k ih=>
      rw [dR_succ]
      have h:=OC (2:Fin 4) (dR k F) (F.degreeOf 2-k) ih
      omega

theorem EUD (Q:MvPolynomial (Fin 4) K) (D w L s:ℕ)
    (hbox:Q ∈ BA K D w L s) (hR:Q.degreeOf 2=0):
    Q ∈ BA K D w L 1:=by
  intro d hd
  obtain ⟨ht,_,hc⟩:=hbox hd
  have hd2:d 2≤Q.degreeOf 2:=MvPolynomial.monomial_le_degreeOf (2:Fin 4) hd
  exact ⟨ht,by omega,hc⟩

theorem BCL (F:MvPolynomial (Fin 4) K):
    ∃j,(dR j F).degreeOf 2=0:=
  ⟨F.degreeOf 2,Nat.eq_zero_of_le_zero (by simpa using BLP (F.degreeOf 2) F)⟩

def chainLength (F:MvPolynomial (Fin 4) K):ℕ:=
  Nat.find (BCL F)

theorem EDK (F:MvPolynomial (Fin 4) K):
    (dR (chainLength F) F).degreeOf 2=0:=
  Nat.find_spec (BCL F)

theorem GJV (F:MvPolynomial (Fin 4) K):chainLength F≤F.degreeOf 2:=
  Nat.find_min' (BCL F)
    (Nat.eq_zero_of_le_zero (by simpa using BLP (F.degreeOf 2) F))

theorem DEZ (F:MvPolynomial (Fin 4) K) (j:ℕ)
    (hj:j<chainLength F):0<(dR j F).degreeOf 2:=
  Nat.pos_of_ne_zero (Nat.find_min (BCL F) hj)

theorem FEE (F:MvPolynomial (Fin 4) K) (hpos:0<F.degreeOf 2):
    1≤chainLength F:=by
  by_contra h
  have h0:chainLength F=0:=by omega
  have:=EDK F
  rw [h0] at this
  simp at this
  omega

theorem dR_ne_zero (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0) (p:ℕ) [CharP K p]
    (hsmall:F.degreeOf 2<p) (j:ℕ) (hj:j≤chainLength F):dR j F ≠ 0:=by
  induction j with
  | zero=>simpa using hF
  | succ k ih=>
      rw [dR_succ]
      have hk:k<chainLength F:=by omega
      have hpos:=DEZ F k hk
      have hle:(dR k F).degreeOf 2<p:=by
        have:=BLP k F
        omega
      exact CWI (dR k F) p hpos hle

theorem DIF (Q:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0)
    (P:Polynomial K) (γ:K) (hsol:BM K P γ Q=0):
    ∃F ∈ HR Q,BM K P γ F=0:=by
  classical
  let φ:=AL K
  let v:Fin 3→GenericField K:=fun i=>initialPoint K P γ i.succ
  have heval (F:MvPolynomial (Fin 4) K):
      MvPolynomial.eval v (surfaceMap φ F)=0 ↔ BM K P γ F=0:=by
    simpa only [HP] using
      (SU K P γ F)
  obtain ⟨F,hF,hz⟩:=XF φ
    (DI K) Q hQ v ((heval Q).mpr hsol)
  exact ⟨F,hF,(heval F).mp hz⟩

theorem EVN (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
    (p:ℕ) [CharP K p] (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<p)
    (j:ℕ) (hj1:1≤j) (hj:j≤chainLength F): ¬F ∣ dR j F:=by
  intro hdiv
  have hne:dR j F ≠ 0:=dR_ne_zero F hF.ne_zero p hsmall j hj
  have hle:=OI (2:Fin 4) F (dR j F) hdiv hne
  have hdeg:=BLP j F
  omega

section Counting

variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota

def tailSeeds (F:MvPolynomial (Fin 4) K)
    (selected:K→Polynomial K) (Gamma:Finset K):Finset K:=
  Gamma.filter fun γ=>BM K (selected γ) γ (dR (chainLength F) F)=0

def rfreeProduct (Q:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
  ∏ F ∈ (HR Q).filter (fun F=>F.degreeOf 2=0),F

def rfreeSeeds (Q:MvPolynomial (Fin 4) K)
    (selected:K→Polynomial K) (Gamma:Finset K):Finset K:=
  Gamma.filter fun γ=>BM K (selected γ) γ (rfreeProduct Q)=0

theorem GCE (F:MvPolynomial (Fin 4) K)
    (selected:K→Polynomial K) (Gamma:Finset K):
    tailSeeds F selected Gamma ⊆ Gamma:=Finset.filter_subset _ _

theorem FXI (Q:MvPolynomial (Fin 4) K)
    (selected:K→Polynomial K) (Gamma:Finset K):
    rfreeSeeds Q selected Gamma ⊆ Gamma:=Finset.filter_subset _ _

theorem EZM (Q:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0):
    rfreeProduct Q ∣ Q:=by
  classical
  unfold rfreeProduct
  exact (Finset.prod_dvd_prod_of_subset _ (HR Q) id
    (Finset.filter_subset _ _)).trans (AUQ Q hQ)

theorem FEQ (Q:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0):
    rfreeProduct Q ≠ 0:=
  ne_zero_of_dvd_ne_zero hQ (EZM Q hQ)

theorem DWN (Q:MvPolynomial (Fin 4) K):
    (rfreeProduct Q).degreeOf 2=0:=by
  classical
  unfold rfreeProduct
  apply Nat.eq_zero_of_le_zero
  refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
  apply Nat.le_of_eq
  apply Finset.sum_eq_zero
  intro F hF
  exact (Finset.mem_filter.mp hF).2

theorem FHV
    (S:GH) (J:MvPolynomial (Fin 4) K) (hJ:J ≠ 0)
    (p:ℕ) [CharP K p]
    (hbox:J ∈ BA K S.D S.w S.L S.s) (hJR:J.degreeOf 2=0) (hSs:S.s=1)
    (hp:1<p) (hw:1≤S.w) (hchar:S.w<p) (hDw:S.w<S.kappa*S.D)
    (hj:1≤S.algebraicCap) (hjYSmall:S.implicitYCap<p) (hjZSmall:S.algebraicCap<p)
    (hmixedSmall:2*S.implicitYCap*S.algebraicCap<p)
    (hwa:S.w<S.a) (han:S.a≤S.n)
    (selected:K→Polynomial K) (Delta:Finset K)
    (nodes:Finset Iota) (x u0 u1:Iota→K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card=S.n)
    (hdegree: ∀γ ∈ Delta,(selected γ).natDegree≤S.w)
    (hsol: ∀γ ∈ Delta,BM K (selected γ) γ J=0)
    (hagreement: ∀γ ∈ Delta,S.a≤(nodes.filter (fun i=>
      (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
    (hnoPencil:BL selected Delta S.w S.errors):
    Delta.card≤S.countCap:=by
  classical
  have hs1:1≤S.s:=by omega
  have hsp:S.s<p:=by omega
  have hcover:=DHV J J hJ S.D S.w S.L S.s p
    hs1 hsp hw (by simpa [GH.kappa] using hDw)
    (by simpa [GH.algebraicCap,GH.kappa] using hj)
    (by simpa [GH.algebraicCap,GH.kappa] using hjZSmall)
    hbox selected Delta hsol hsol
  have hregZero:(∑ F' :RegularIndex J,(NQ J J selected Delta F').card)=0:=by
    apply Finset.sum_eq_zero
    intro F' _
    exfalso
    obtain ⟨_,hdvd,hpos⟩:=KR J F'.1 F'.2
    have:=OI (2:Fin 4) F'.1 J hdvd hJ
    omega
  have hsingularOld:=RCN292.GH.DMF
    S J hJ hbox hs1 hsp hw hchar hDw hj hjYSmall hjZSmall hmixedSmall
    hwa han selected Delta nodes x u0 u1 hinj hnodes hdegree hagreement hnoPencil
  have hsingular:(RCN052.ASS J selected Delta).card≤S.countCap:=by
    change (RCN291.ASS J selected Delta).card≤S.countCap
    exact hsingularOld
  omega

end Counting

section Assembly

variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota

end Assembly

end

end ProximityPrize.SubmissionLower.UA
end PackedLocator_LocatorDerivativeChain

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorFixedChain

namespace ProximityPrize.SubmissionLower.ESN

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243 RCN140 UA

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
  UniqueFactorizationMonoid.strongNormalizationMonoid
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota

theorem DXJ (Q:MvPolynomial (Fin 4) K)
    (selected:K→Polynomial K) (Gamma:Finset K) (F:RegularIndex Q):
    NQ Q Q selected Gamma F ⊆ regularSeeds Q selected Gamma F:=by
  intro γ hγ
  simp only [NQ,regularSeeds,Finset.mem_filter] at hγ ⊢
  exact ⟨hγ.1,hγ.2.1⟩

end

end ProximityPrize.SubmissionLower.ESN
end PackedLocator_LocatorFixedChain

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorHybridTailProviderC1

namespace ProximityPrize.SubmissionLower.ND
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA GJ IB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap:ℕ}

theorem ESP (a B delay mult:ℕ) (hA:1≤a+B)
    (hdm:delay≤mult) (hm6:6≤mult):
    1+(2*a+2*B+4)*(131072+delay)≤
      mult*(131074*a+131072*B+2*B+5):=by
  have h:=EWB (a+B) delay mult hA hdm hm6
  have e1:2*(a+B)+4=2*a+2*B+4:=by ring
  have e2:131072*(a+B)+2*(a+B)+5=
      131074*a+131072*B+2*B+5:=by ring
  rw [e1,e2] at h
  exact h

theorem CUW
    (t y r:Nat) (hr3:3≤r) (_hry:r<y)
    (S:FH (AL K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (delay mult:ℕ) (_hd:1≤delay) (hdm:delay≤mult) (hm6:6≤mult):
    BI (mult • MK t y r)
      (_Q2 (AL K) S.F (w+1+delay)):=by
  have hs1:1≤cellS r:=by simp only [cellS];omega
  have hB1:1≤cellB y r+cellS r:=by omega
  have hA1:1≤cellA t y+(cellB y r+cellS r):=by omega
  have hsy:(cellSupport t y r).s<(cellSupport t y r).ys:=by
    simp only [cellSupport,cellA,cellB,cellS,RCN198.support]
    omega
  have hsharp:BI
      (DL (cellSupport t y r) (w+1+delay))
      (_Q2 (AL K) S.F (w+1+delay)):=by
    exact ANZ hsy (AL K)
      ⟨S.AFS,S.ACG,S.UT⟩
      (w+1+delay) (tailSelector (w+1+delay)) 0 0 0
  intro exponent hexp
  have h:=hsharp exponent hexp
  obtain ⟨hall,hys,htot⟩:=h
  have hallV:(DL (cellSupport t y r)
      (w+1+delay)).all=(2*cellS r+3)*(131072+delay):=by
    have e1: ∀m:ℕ,2*(m+2)-1=2*m+3:=fun m=>by omega
    have e2: ∀m2 m3:ℕ,
        2*(m2+m3+3-(m3+2))-1=2*m2+1:=fun m2 m3=>by omega
    have e3: ∀m1 m2 m3:ℕ,
        m1+m2+m3+3-(m2+m3+3)=m1:=fun m1 m2 m3=>by omega
    simp only [DL,SS,
      cellSupport,RCN198.support,w,e3,e2,e1]
  have hysV:(DL (cellSupport t y r)
        (w+1+delay)).yz+
      (DL (cellSupport t y r)
        (w+1+delay)).all=
      1+(2*(cellB y r+cellS r)+4)*(131072+delay):=by
    have e1: ∀m:ℕ,2*(m+2)-1=2*m+3:=fun m=>by omega
    have e2: ∀m2 m3:ℕ,
        2*(m2+m3+3-(m3+2))-1=2*m2+1:=fun m2 m3=>by omega
    have e3: ∀m1 m2 m3:ℕ,
        m1+m2+m3+3-(m2+m3+3)=m1:=fun m1 m2 m3=>by omega
    simp only [DL,SS,
      cellSupport,RCN198.support,w,e3,e2,e1]
    all_goals ring
  have htotV:(DL (cellSupport t y r)
        (w+1+delay)).zOnly+
      (DL (cellSupport t y r)
        (w+1+delay)).yz+
      (DL (cellSupport t y r)
        (w+1+delay)).all=
      1+(2*cellA t y+2*(cellB y r+cellS r)+4)*
        (131072+delay):=by
    have e1: ∀m:ℕ,2*(m+2)-1=2*m+3:=fun m=>by omega
    have e2: ∀m2 m3:ℕ,
        2*(m2+m3+3-(m3+2))-1=2*m2+1:=fun m2 m3=>by omega
    have e3: ∀m1 m2 m3:ℕ,
        m1+m2+m3+3-(m2+m3+3)=m1:=fun m1 m2 m3=>by omega
    simp only [DL,SS,
      cellSupport,RCN198.support,w,e3,e2,e1]
    all_goals ring
  have hhallV:(mult • MK t y r).all=
      mult*(131072*cellS r+(2*cellS r+3)):=by
    simp only [MK,cellRational,BGD,
      RCN206.ZR,nsmul_all,w]
  have hhysV:(mult • MK t y r).yz+
      (mult • MK t y r).all=
      mult*(131072*(cellB y r+cellS r)+
        2*(cellB y r+cellS r)+5):=by
    simp only [MK,cellRational,BGD,
      RCN206.ZR,nsmul_yz,nsmul_all,w]
    ring
  have hhtotV:(mult • MK t y r).zOnly+
      (mult • MK t y r).yz+
      (mult • MK t y r).all=
      mult*(131074*cellA t y+131072*(cellB y r+cellS r)+
        2*(cellB y r+cellS r)+5):=by
    simp only [MK,cellRational,BGD,
      RCN206.ZR,nsmul_zOnly,nsmul_yz,nsmul_all,w]
    ring
  refine ⟨?_,?_,?_⟩
  · exact (hallV ▸ hall).trans (hhallV ▸
      FEW (cellS r) delay mult hs1 hdm hm6)
  · exact (hysV ▸ hys).trans (hhysV ▸
      DOF (cellB y r+cellS r) delay mult hB1 hdm hm6)
  · exact (htotV ▸ htot).trans (hhtotV ▸
      ESP (cellA t y) (cellB y r+cellS r) delay mult
        hA1 hdm hm6)

end
end ProximityPrize.SubmissionLower.ND
end PackedLocator_LocatorHybridTailProviderC1

section PackedLocator_LocatorHybridTransportC2

namespace ProximityPrize.SubmissionLower.JN
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN203 RCN201 RCN275 RCN287 RCN086 RCN085
open RCN066 RCN135 RCN159 RCN074 RCN237 RCN244 RCN327 RCN263 RCN206 RCN002 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

section Transport
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
  {G T T' H:MvPolynomial (Fin 3) Omega}

def YV (h:G ∣ T-T')
    {base' : ∀C:AU Omega G T' H,BP C.1}
    {p q:FlagDegree}
    (U:EE base' p q)
    (base: ∀C:AU Omega G T H,BP C.1):
    EE base p q where
  zProjection C:=U.zProjection (JA h C)
  yzProjection C:=U.yzProjection (JA h C)
  NV C:=U.NV (JA h C)
  zValue C:=U.zValue (JA h C)
  ACE C:=U.ACE (JA h C)
  zPole_eq C:=U.zPole_eq (JA h C)
  yzPole_eq C:=U.yzPole_eq (JA h C)
  allPole_eq C:=U.allPole_eq (JA h C)
  ARJ:=by
    refine Eq.trans_le ?_ U.ARJ
    exact Fintype.sum_equiv (JA h) _ _ (fun _=>rfl)
  ALE:=by
    refine Eq.trans_le ?_ U.ALE
    exact Fintype.sum_equiv (JA h) _ _ (fun _=>rfl)
  AQB:=by
    refine Eq.trans_le ?_ U.AQB
    exact Fintype.sum_equiv (JA h) _ _ (fun _=>rfl)

theorem AUD (h:G ∣ T-T')
    {base' : ∀C:AU Omega G T' H,BP C.1}
    {p q:FlagDegree}
    (U:EE base' p q)
    (base: ∀C:AU Omega G T H,BP C.1)
    (C:AU Omega G T H):
    (YV h U base).toFE.zCost C=
        (FE.AQQ h
          U.toFE).zCost C∧
      (YV h U base).toFE.yzCost C=
        (FE.AQQ h
          U.toFE).yzCost C∧
      (YV h U base).toFE.allCost C=
        (FE.AQQ h
          U.toFE).allCost C:=by
  refine ⟨?_,?_,?_⟩<;>rfl

end Transport

section Budgets
variable {K Ω E:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
  [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
  [IsScalarTower Ω (RatFunc Ω) E]

theorem DNR
    (φ:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (G T:MvPolynomial (Fin 3) Ω) (a b s w:ℕ) (hw:1≤w)
    (hT:T=_Q2 φ F (w+1))
    (hF:KW (support a b s) F) (flag:FlagDegree)
    (hG:G ≠ 0) (hdiv:G ∣ surfaceMap φ F) (hGflag:BI flag G)
    (base: ∀C:AU Ω G T (CR φ F),
      BP C.1)
    (tailFlag:FlagDegree)
    (unit:EE base flag tailFlag)
    (pchar:ℕ) [CharP E pchar]
    (hmix:2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4)<pchar):
    ∃budget: ∀C:AU Ω G T (CR φ F),
      RD C.1 (CR φ F) (surfaceMap φ (polyG K F)),
      (∀C,(budget C).zCost=unit.toFE.zCost C∧
        (budget C).yzCost=unit.toFE.yzCost C∧
        (budget C).allCost=unit.toFE.allCost C)∧
      (∑ C,(budget C).movingCost)≤flagMixed flag
        (RCN206.fiberFlag a b s)
        (center a b s+(w+1) • RCN206.surfaceFlag a b s):=by
  classical
  obtain ⟨coeffs,cflags,heq,hcoeff,hclass⟩:=EJW
    φ a b s F hF.IZ.2.1 hF.ys_weight hF.total_weight w hw
  obtain ⟨hHflag,hGcontact⟩:=DGW
    φ a b s F hF.IZ.2.1 hF.ys_weight hF.total_weight
  have hderiv:CR φ F ∈
      Ideal.span ({G,MvPolynomial.pderiv (1:Fin 3) G}:
        Set (MvPolynomial (Fin 3) Ω)):=by
    rw [CR,← RCN267.ZO]
    exact RCN076.EXV G (surfaceMap φ F) hdiv
  have hT' :T=filteredCut w coeffs (surfaceMap φ (polyH K F))
      (surfaceMap φ (polyG K F)):=hT.trans heq
  clear hT
  subst T
  obtain ⟨budget,hcost,hz,hyz,ha,hm⟩:=
    DKU (E:=E)
      G (CR φ F) (surfaceMap φ (polyG K F)) w coeffs
      base flag tailFlag unit hG hderiv hGflag
      a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
      (by convert hmix using 1<;>ring)
  refine ⟨budget,hcost,hm.trans ?_⟩
  rw [EMA,EMA]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ w)) _

end Budgets

end
end ProximityPrize.SubmissionLower.JN
end PackedLocator_LocatorHybridTransportC2

section PackedLocator_LocatorHybridTailProviderC2

namespace ProximityPrize.SubmissionLower.EBX
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA GJ IB
open ND JN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap:ℕ}

end
end ProximityPrize.SubmissionLower.EBX
end PackedLocator_LocatorHybridTailProviderC2

section PackedLocator_LocatorHybridTailRealizationC2

namespace ProximityPrize.SubmissionLower.DPV
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open FA GJ IB
open ND JN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 800000

variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap:ℕ}
variable {t y r:Nat}

end
end ProximityPrize.SubmissionLower.DPV
end PackedLocator_LocatorHybridTailRealizationC2

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorCover
open RCN259
noncomputable section
variable {R S I:Type*} [CommRing R] [GCDMonoid R]
 [CommRing S] [IsDomain S]
local instance:DecidableEq S:=Classical.decEq S
local instance:DecidableEq I:=Classical.decEq I
theorem GIR (phi:R→+*S) (a b:R)
    (ha:phi a=0) (hb:phi b=0) (hg:phi (gcd12 a b) ≠ 0):
    phi (quotientA a b)=0∧phi (quotientB a b)=0:=by
  rw [DBH a b,map_mul] at ha
  rw [DAP a b,map_mul] at hb
  exact ⟨(mul_eq_zero.mp ha).resolve_left hg,(mul_eq_zero.mp hb).resolve_left hg⟩
def fixed (phi:I→R→+*S) (seeds:Finset I) (a b:R):Finset I:=by
  classical
  exact seeds.filter (fun i=>phi i (gcd12 a b)=0)
def residual (phi:I→R→+*S) (seeds:Finset I) (a b:R):Finset I:=by
  classical
  exact seeds.filter (fun i=>phi i (gcd12 a b) ≠ 0)
theorem GNT (phi:I→R→+*S) (seeds:Finset I) (a b:R):
    (fixed phi seeds a b).card+(residual phi seeds a b).card=seeds.card:=by
  classical
  simpa only [fixed,residual] using
    Finset.card_filter_add_card_filter_not (s:=seeds)
      (fun i=>phi i (gcd12 a b)=0)
theorem fixed_vanish (phi:I→R→+*S) (seeds:Finset I) (a b:R)
    (i:I) (hi:i ∈ fixed phi seeds a b):phi i (gcd12 a b)=0:=by
  classical
  have hm:i ∈ seeds∧phi i (gcd12 a b)=0:=by
    simpa only [fixed,Finset.mem_filter] using hi
  exact hm.2
theorem GGN (phi:I→R→+*S) (seeds:Finset I) (a b:R)
    (ha:∀i ∈ seeds,phi i a=0) (hb:∀i ∈ seeds,phi i b=0)
    (i:I) (hi:i ∈ residual phi seeds a b):
    phi i (quotientA a b)=0∧phi i (quotientB a b)=0:=by
  classical
  have hm:i ∈ seeds∧phi i (gcd12 a b) ≠ 0:=by
    simpa only [residual,Finset.mem_filter] using hi
  exact GIR (phi i) a b (ha i hm.1) (hb i hm.1) hm.2
end
end ProximityPrize.SubmissionLower.LocatorCover
end PackedLocator_LocatorCover

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

end Compact_PackedLocatorTail

section Compact_AsymmetricLocator
namespace ProximityPrize.SubmissionLower.GB
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260 KI
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

def KP (P:DG):ℕ:=
  (P.n-P.w)*RCN294.dot P.KO P.mixedCost+
    (P.errors+1)*P.gap*P.mixedCost.z

def FU (P:DG):ℕ:=
  KP P/P.gap

theorem ZF
    (P:DG) (H Q:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H) (hrel:IsRelPrime F.1 Q)
    (p:ℕ) [CharP K p]
    (hFY:F.1.degreeOf 1≤P.leftY) (hFR:F.1.degreeOf 2≤P.leftR)
    (hFZ:F.1.degreeOf 3≤P.leftZ)
    (hQY:Q.degreeOf 1≤P.rightY) (hQR:Q.degreeOf 2≤P.rightR)
    (hQZ:Q.degreeOf 3≤P.rightZ)
    (hleftR:1≤P.leftR)
    (hleftYSmall:P.leftY<p) (hleftRSmall:P.leftR<p)
    (hleftZSmall:P.leftZ<p)
    (hmixedYSmall:P.mixedCost.y<p) (hmixedRSmall:P.mixedCost.r<p)
    (hmixedZSmall:P.mixedCost.z<p)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (nodes:Finset I) (x u0 u1:I→K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card=P.n)
    (hw:1≤P.w) (hchar:P.w<p) (hwa:P.w<P.a) (han:P.a≤P.n)
    (hdegree:∀gamma ∈ Gamma,(selected gamma).natDegree≤P.w)
    (hagreement:∀gamma ∈ Gamma,P.a≤
      (nodes.filter (fun i=>(selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma P.w P.errors)
    (hQzero:∀gamma ∈ RCN140.regularSeeds H selected Gamma F,
      RCN319.BM K (selected gamma) gamma Q=0):
    (RCN140.regularSeeds H selected Gamma F).card≤FU P:=by
  let Fself:=EBE H F
  have hcount:=CKD P F.1 Q hrel Fself p
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hw hchar hwa han hdegree hagreement hno
  have heq:RCN052.NQ F.1 Q selected Gamma Fself=
      RCN140.regularSeeds H selected Gamma F:=by
    ext gamma
    simp only [RCN052.NQ,RCN140.regularSeeds,Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1,h.2.1⟩
    · intro h
      exact ⟨h.1,h.2,hQzero gamma (Finset.mem_filter.mpr h)⟩
  rw [heq] at hcount
  have hv:=CRA P F.1 hFY hFR hFZ
  have hdot:RCN294.dot P.KO (RCN052.OX P F.1)≤
      RCN294.dot P.KO P.mixedCost:=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.KO.y hv.1)
        (Nat.mul_le_mul_left P.KO.r hv.2.1))
      (Nat.mul_le_mul_left P.KO.z hv.2.2)
  unfold FU
  apply (Nat.le_div_iff_mul_le (by unfold DG.gap;omega)).mpr
  exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n-P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors+1)*P.gap) hv.2.2))

end
end ProximityPrize.SubmissionLower.GB

end Compact_AsymmetricLocator

section Compact_AsymmetricLinear
namespace ProximityPrize.SubmissionLower.GB
open RCN260
set_option autoImplicit false
set_option maxHeartbeats 1000000

end ProximityPrize.SubmissionLower.GB

end Compact_AsymmetricLinear

section Compact_Helpers80791


section Adapted_LocatorGenericHelperFactorSwitch
namespace ProximityPrize.SubmissionLower.Lower80791.FactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open KI IL

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

end

end ProximityPrize.SubmissionLower.Lower80791.FactorSwitch

end Adapted_LocatorGenericHelperFactorSwitch

section Adapted_LocatorGenericPowerRoute
namespace ProximityPrize.SubmissionLower.Lower80791.PowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open KI IL
open CS TB
open Lower80791.FactorSwitch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

end

end ProximityPrize.SubmissionLower.Lower80791.PowerRoute

end Adapted_LocatorGenericPowerRoute

section Adapted_LocatorBatchPowerRoute
namespace ProximityPrize.SubmissionLower.Lower80791.AGR

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open IL KI CS TB Lower80791.FactorSwitch Lower80791.PowerRoute KZ

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

end

end ProximityPrize.SubmissionLower.Lower80791.AGR

end Adapted_LocatorBatchPowerRoute

end Compact_Helpers80791

section Compact_Oracle80791

namespace ProximityPrize.SubmissionLower.Lower80791.Oracle
open RCN095 DY IL CS
open Lower80791.PowerRoute Lower80791.FactorSwitch
open FV (Potential rawFlag sumFlag RawBelow AVS)
set_option autoImplicit false
set_option maxRecDepth 100000

structure EA where
  totalCap:ℕ
  middleCap:ℕ
  slopeCap:ℕ
  gap:ℕ
  deriving DecidableEq,Repr

def EA.fuel (s:EA) (p:FlagDegree):ℕ:=
  min (s.totalCap/total p)
    (min (s.middleCap/middle p) (s.slopeCap/p.all))

def EA.band (s:EA) (p:FlagDegree):ℕ:=
  LH 50283 (total p) (middle p) p.all
    (s.totalCap-total p) (s.middleCap-middle p)
    (s.slopeCap-p.all) (s.fuel p)

def contactDec (p:FlagDegree):ℕ:=131071*middle p-p.all

def EA.contactCap (s:EA) (p:FlagDegree):ℕ:=
  (131071*(s.middleCap+1)-s.slopeCap)-contactDec p

def EA.bandThin (s:EA) (p:FlagDegree):ℕ:=
  HN 131071 (s.contactCap p) 50283 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap-total p) (s.middleCap-middle p)
    (s.slopeCap-p.all) (s.fuel p)

def EA.Routeable (s:EA) (p:FlagDegree):Prop:=
  1≤p.all∧total p≤s.totalCap∧middle p≤s.middleCap∧
    p.all≤s.slopeCap∧(s.band p<s.gap∨s.bandThin p<s.gap)

instance (s:EA) (p:FlagDegree):Decidable (s.Routeable p):=
  by unfold EA.Routeable;infer_instance

end ProximityPrize.SubmissionLower.Lower80791.Oracle

end Compact_Oracle80791

section Compact_BatchPhase80791

namespace ProximityPrize.SubmissionLower.Lower80791.BatchPhase

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266
open DY CS KZ Lower80791.AGR Lower80791.FactorSwitch Lower80791.Oracle

open FV (Potential sumFlag sumFlag_all AQT AXF RawBelow AVS)
open MM (BF JM
  IF KH LY
  AAN AML BCO)

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

end

end ProximityPrize.SubmissionLower.Lower80791.BatchPhase

end Compact_BatchPhase80791

section Compact_ClosedRank

namespace ProximityPrize.SubmissionLower.ClosedRank
open scoped BigOperators
open RZ
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem BHS (a b h L:ℕ)
    (hb:h+(a-1)+(b-1)≤L):
    2*(_Q9 a b h L:ℤ)=
      (a:ℤ)*b*(2*(L+1-(h:ℤ))-a-b+2):=by
  by_cases ha:a=0
  · simp [ha,_Q9]
  by_cases hzero:b=0
  · simp [hzero,_Q9]
  have ha1:1≤a:=by omega
  have hb1:1≤b:=by omega
  have htA:a*(a-1)/2*2=a*(a-1):=
    Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one a)
  have htB:b*(b-1)/2*2=b*(b-1):=
    Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one b)
  have hmass:b*(a*(a-1)/2)+a*(b*(b-1)/2)≤
      a*b*(L+1-h):=by
    have hx:=Nat.mul_le_mul_left (a*b)
      (show (a-1)+(b-1)≤2*(L+1-h) by omega)
    have hi:=congrArg (fun x=>b*x) htA
    have hj:=congrArg (fun x=>a*x) htB
    nlinarith only [hx,hi,hj]
  have htAi:(a*(a-1)/2:ℕ)*(2:ℤ)=(a:ℤ)*(a-1):=by
    exact_mod_cast htA
  have htBi:(b*(b-1)/2:ℕ)*(2:ℤ)=(b:ℤ)*(b-1):=by
    exact_mod_cast htB
  unfold _Q9
  simp only [Nat.cast_sub hmass,Nat.cast_add,Nat.cast_mul,
    Nat.cast_sub (show h≤L+1 by omega),Nat.cast_one]
  nlinarith only [congrArg (fun x:ℤ=>b*x) htAi,congrArg (fun x:ℤ=>a*x) htBi]

theorem CUI (a b h L:ℕ)
    (hb:(a-1)+(b-1)≤L):
    _Q9 (a-h) (b-h) h L≤_Q9 a b 0 L:=by
  by_cases ha:a≤h
  · simp [Nat.sub_eq_zero_of_le ha,_Q9]
  by_cases hb' :b≤h
  · simp [Nat.sub_eq_zero_of_le hb',_Q9]
  have hshape:h+(a-h-1)+(b-h-1)≤L:=by omega
  rw [← AOA _ _ _ _ hshape,
    ← AOA a b 0 L (by omega)]
  calc
    _≤ ∑ i ∈ Finset.range (a-h),∑ j ∈ Finset.range (b-h),(L+1-0-i-j):=by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      omega
    _≤ ∑ i ∈ Finset.range a,∑ j ∈ Finset.range b,(L+1-0-i-j):=by
      apply le_trans (Finset.sum_le_sum (fun i _=>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le b h))
          (fun _ _ _=>Nat.zero_le _)))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le a h))
        (fun _ _ _=>Nat.zero_le _)

def rankRow (m L s r:ℕ):ℕ:=
  let h:=min (r+1) (m-r)
  _Q9 (r+1) (s+1) 0 L-_Q9 (r+1-h) (s+1-h) h L

theorem GXH (m L s r:ℕ) (hr:r<m)
    (hshape:m+s≤L+1) (hs:2*s≤m):
    2*(rankRow m L s r:ℤ)=
      (r+1:ℤ)*(s+1)*(2*L+2-r-s)-
      if r<m-s then 0 else
        (2*r+1-m:ℤ)*(s+1-m+r)*(2*L+2-r-s):=by
  let h:=min (r+1) (m-r)
  have hl:r+s≤L:=by omega
  have hle:=CUI (r+1) (s+1) h L (by omega)
  have hsource:=BHS (r+1) (s+1) 0 L (by omega)
  have hsource' :2*(_Q9 (r+1) (s+1) 0 L:ℤ)=
      (r+1:ℤ)*(s+1)*(2*L+2-r-s):=by
    push_cast at hsource
    nlinarith only [hsource]
  unfold rankRow
  change 2*((_Q9 (r+1) (s+1) 0 L-
    _Q9 (r+1-h) (s+1-h) h L:ℕ):ℤ)=_
  rw [Nat.cast_sub hle,mul_sub,hsource']
  by_cases hearly:r<m-s
  · rw [if_pos hearly]
    have hzero:r+1-h=0∨s+1-h=0:=by
      dsimp [h]
      omega
    rcases hzero with hzero | hzero<;>simp [hzero,_Q9]
  · rw [if_neg hearly]
    have heqh:h=m-r:=by dsimp [h];omega
    have hhr:h≤r+1:=by omega
    have hhs:h≤s+1:=by omega
    have hkernel:=BHS (r+1-h) (s+1-h) h L (by omega)
    simp only [Nat.cast_sub hhr,Nat.cast_sub hhs,Nat.cast_add,Nat.cast_one] at hkernel
    have hhcast:(h:ℤ)=m-r:=by rw [heqh,Nat.cast_sub (by omega:r≤m)]
    rw [hhcast] at hkernel
    nlinarith only [hkernel]

def sourceTwice (L s r:ℤ):ℤ:=(r+1)*(s+1)*(2*L+2-r-s)
def removedTwice (m L s j:ℤ):ℤ:=(m+1-2*j)*(s+1-j)*(2*L+2-m-s+j)

def sourceTwelve (m L s:ℤ):ℤ:=
  (s+1)*m*(m+1)*(6*(L+1)-2*(m-1)-3*s)

def AAL (m L s k:ℤ):ℤ:=
  let c:=2*L+2-m-s
  let p0:=(m+1)*(s+1)
  let p1:= -(m+2*s+3)
  6*p0*c*k+3*(p0+p1*c)*k*(k+1)+
    (p1+2*c)*k*(k+1)*(2*k+1)+3*k*k*(k+1)*(k+1)

theorem FEL (m:ℕ) (L s:ℤ):
    6*(∑ r ∈ Finset.range m,sourceTwice L s r)=sourceTwelve m L s:=by
  induction m with
  | zero=>simp [sourceTwelve]
  | succ m ih=>
    rw [Finset.sum_range_succ,mul_add,ih]
    simp only [Nat.cast_add,Nat.cast_one]
    unfold sourceTwice sourceTwelve
    ring

theorem EYZ (k:ℕ) (m L s:ℤ):
    6*(∑ j ∈ Finset.range k,removedTwice m L s (j+1))=
      AAL m L s k:=by
  induction k with
  | zero=>simp [AAL]
  | succ k ih=>
    rw [Finset.sum_range_succ,mul_add,ih]
    simp only [Nat.cast_add,Nat.cast_one]
    unfold removedTwice AAL
    ring

theorem GAK (m L s:ℕ) (hs:s≤m):
    (∑ r ∈ Finset.range m,if r<m-s then (0:ℤ) else
      removedTwice m L s ((m:ℤ)-r))=
      ∑ j ∈ Finset.range s,removedTwice m L s (j+1):=by
  let f:ℕ→ℤ:=fun r=>if r<m-s then 0 else removedTwice m L s ((m:ℤ)-r)
  change (∑ r ∈ Finset.range m,f r)=_
  have hsplit:=Finset.sum_range_add f (m-s) s
  rw [Nat.sub_add_cancel hs] at hsplit
  rw [hsplit]
  have hzero:(∑ r ∈ Finset.range (m-s),f r)=0:=by
    apply Finset.sum_eq_zero
    intro r hr
    simp [f,Finset.mem_range.mp hr]
  rw [hzero,zero_add]
  calc
    _= ∑ j ∈ Finset.range s,f (m-s+(s-1-j)):=
      (Finset.sum_range_reflect (fun r=>f (m-s+r)) s).symm
    _=_:=by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' :=Finset.mem_range.mp hj
      have hlate: ¬m-s+(s-1-j)<m-s:=by omega
      have hindex:(m:ℤ)-(m-s+(s-1-j):ℕ)=(j:ℤ)+1:=by
        have heq:m-s+(s-1-j)+j+1=m:=by omega
        have heqi:((m-s+(s-1-j):ℕ):ℤ)+j+1=m:=by exact_mod_cast heq
        omega
      simp only [f,if_neg hlate,hindex]

theorem EJS (m L s:ℕ)
    (hshape:m+s≤L+1) (hs:2*s≤m):
    12*(AFW m L s:ℤ)=
      sourceTwelve m L s-AAL m L s s:=by
  have hfast:AFW m L s= ∑ r ∈ Finset.range m,rankRow m L s r:=by
    unfold AFW
    rw [IL.VJ]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' :=Finset.mem_range.mp hr
    have hmin:min r L=r:=min_eq_left (by omega)
    simp only [hmin,rankRow]
  have hrow (r:ℕ) (hr:r ∈ Finset.range m):
      2*(rankRow m L s r:ℤ)=sourceTwice L s r-
        (if r<m-s then 0 else removedTwice m L s ((m:ℤ)-r)):=by
    rw [GXH m L s r (Finset.mem_range.mp hr) hshape hs]
    split_ifs<;>simp only [sourceTwice,removedTwice]<;>ring
  have hsum:2*(AFW m L s:ℤ)=
      (∑ r ∈ Finset.range m,sourceTwice L s r)-
        ∑ j ∈ Finset.range s,removedTwice m L s (j+1):=by
    rw [hfast,Nat.cast_sum,Finset.mul_sum]
    rw [Finset.sum_congr rfl hrow,Finset.sum_sub_distrib,
      GAK m L s (by omega)]
  have hscaled:=congrArg (fun z:ℤ=>6*z) hsum
  rw [mul_sub,FEL,EYZ] at hscaled
  nlinarith only [hscaled]

def CUD (m L s:ℕ):ℕ:=
  ((sourceTwelve m L s-AAL m L s s)/12).toNat

theorem DXR (m L s:ℕ)
    (hshape:m+s≤L+1) (hs:2*s≤m):
    AFW m L s=CUD m L s:=by
  unfold CUD
  rw [← EJS m L s hshape hs]
  simp

theorem RU (m L s:ℕ)
    (hshape:m+s≤L+1) (hs:2*s≤m):
    RCN119.ES m L s=CUD m L s:=by
  rw [AZU m L s hshape,
    DXR m L s hshape hs]

end ProximityPrize.SubmissionLower.ClosedRank

end Compact_ClosedRank

section Compact_OneResidueLower

namespace ProximityPrize.SubmissionLower.GGD
open scoped BigOperators
open RCN100 RCN302 RZ IL
set_option autoImplicit false
set_option maxHeartbeats 2000000

end ProximityPrize.SubmissionLower.GGD

end Compact_OneResidueLower

section Compact_Kernels80791

namespace ProximityPrize.SubmissionLower.Kernels80791
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 RZ IL
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace A

end A

namespace B

end B

namespace T

end T

namespace Source00

end Source00

namespace Source01

end Source01

namespace Source02

end Source02

namespace Source03

end Source03

namespace Source04

end Source04

namespace Source05

end Source05

end ProximityPrize.SubmissionLower.Kernels80791

end Compact_Kernels80791

section Compact_Sources80791

namespace ProximityPrize.SubmissionLower.Lower80791.SourceSound

open RCN095 RCN223 RCN260 RCN294 DY
open Lower80791.FactorSwitch Lower80791.PowerRoute
open Lower80791.Oracle
open FV (Potential)

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Phase00

end Phase00

namespace Phase01

end Phase01

namespace Phase02

end Phase02

namespace Phase03

end Phase03

namespace Phase04

end Phase04

namespace Phase05

end Phase05

end ProximityPrize.SubmissionLower.Lower80791.SourceSound

end Compact_Sources80791

section Compact_SecondJetHybridProvider

namespace ProximityPrize.SubmissionLower.EQZ
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA GJ IB
open ND JN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap:ℕ}

end
end ProximityPrize.SubmissionLower.EQZ

end Compact_SecondJetHybridProvider

section Compact_TriangularKernel

namespace ProximityPrize.SubmissionLower.EYL
noncomputable section
set_option autoImplicit false

variable {K:Type*} [Field K] {n:ℕ}
variable {V W:Fin n→Type*}
variable [∀i,AddCommGroup (V i)] [∀i,Module K (V i)]
variable [∀i,AddCommGroup (W i)] [∀i,Module K (W i)]

theorem EZV
    (F:(∀i,V i)→ₗ[K] (∀i,W i))
    (D: ∀i,V i→ₗ[K] W i)
    (hD: ∀i,Function.Injective (D i))
    (hdiag: ∀v i,(∀j,j.val< i.val→v j=0)→
      F v i=D i (v i))
    (v: ∀i,V i) (hv:F v=0):v=0:=by
  have hall: ∀k:ℕ,∀i:Fin n,i.val=k→v i=0:=by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih=>
      intro i hi
      apply hD i
      calc
        D i (v i)=F v i:=(hdiag v i (fun j hj=>
          ih j.val (by omega) j rfl)).symm
        _=0:=congrFun hv i
        _=D i 0:=(map_zero (D i)).symm
  funext i
  exact hall i.val i rfl

theorem ETC
    (F:(∀i,V i)→ₗ[K] (∀i,W i))
    (D: ∀i,V i→ₗ[K] W i)
    (hD: ∀i,Function.Injective (D i))
    (hdiag: ∀v i,(∀j,j.val< i.val→v j=0)→
      F v i=D i (v i)):Function.Injective F:=by
  intro v u h
  apply sub_eq_zero.mp
  apply EZV F D hD hdiag (v-u)
  rw [map_sub,h,sub_self]

end
end ProximityPrize.SubmissionLower.EYL

end Compact_TriangularKernel

section Compact_SecondJetBasis

namespace ProximityPrize.SubmissionLower.VV
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K B:Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
abbrev Jet (B:Type*) [CommRing B]:=Polynomial (Polynomial B)

def lift:B→ₐ[K] Jet B:=
  (Polynomial.CAlgHom (R:=K) (A:=Polynomial B)).comp
    (Polynomial.CAlgHom (R:=K) (A:=B))

def factor (v:B) (r h a b:ℕ):Jet B:=
  Polynomial.X^r*
    (Polynomial.C (Polynomial.X^h)*
      (Polynomial.C (Polynomial.C v)+
        Polynomial.X*Polynomial.C Polynomial.X)^a*
      Polynomial.C (Polynomial.C v)^b)

def term (v:B) (r h a b:ℕ):B→ₗ[K] Jet B:=
  (LinearMap.mulLeft K (factor v r h a b)).comp lift.toLinearMap

variable {m s:ℕ}

def truncate:Jet B→ₗ[K] (Fin m→Fin s→B):=
  LinearMap.pi (fun r=>LinearMap.pi (fun h=>
    ((Polynomial.lcoeff B h.val).restrictScalars K).comp
      ((Polynomial.lcoeff (Polynomial B) r.val).restrictScalars K)))

theorem GQD (P:Jet B) (r:Fin m) (h:Fin s):
    truncate (K:=K) P r h=(P.coeff r.val).coeff h.val:=rfl

theorem GHX (m r s h:ℕ) (hr:r≤m) (hh:h≤s):
    let q:=max ((m-r+1)/2) (m-r-(s-h))
    let a:=min q (s-h)
    let b:=q-a
    a+b=q∧h+a≤s∧m≤r+2*a+b:=by
  dsimp
  omega

end
end ProximityPrize.SubmissionLower.VV

end Compact_SecondJetBasis

section Compact_SecondJetTruncate

namespace ProximityPrize.SubmissionLower.VV
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K B:Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]

def AFQ (m:ℕ):Jet B→ₗ[K] Jet B:=
  (Polynomial.modByMonicHom (Polynomial.X^m:Jet B)).restrictScalars K

theorem EEY (m:ℕ) (P:Jet B) (r:ℕ) (hr:r<m):
    (AFQ (K:=K) m P).coeff r=P.coeff r:=by
  change (P%ₘ Polynomial.X^m).coeff r=P.coeff r
  have heq:=Polynomial.modByMonic_add_div P (Polynomial.X^m)
  have hc:=congrArg (fun Q:Jet B=>Q.coeff r) heq
  simpa only [Polynomial.coeff_add,Polynomial.coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hr),add_zero] using hc

theorem EPQ (m:ℕ) (P:Jet B) (r:ℕ) (hr:m≤r):
    (AFQ (K:=K) m P).coeff r=0:=by
  change (P%ₘ Polynomial.X^m).coeff r=0
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply (Polynomial.degree_modByMonic_lt P (Polynomial.monic_X_pow m)).trans_le
  simp only [Polynomial.degree_X_pow]
  exact_mod_cast hr

theorem EVZ {m s:ℕ} (P:Jet B):
    truncate (K:=K) (m:=m) (s:=s) (AFQ (K:=K) m P)=
      truncate (K:=K) (m:=m) (s:=s) P:=by
  funext r h
  exact congrArg (fun Q:Polynomial B=>Q.coeff h.val)
    (EEY (K:=K) m P r.val r.isLt)

theorem FBL {C:Type*} [CommRing C]
    (φ:Jet B→+*C) (t:C) (m:ℕ) (P:Jet B)
    (hε:φ Polynomial.X=t) (hP:t^m ∣ φ P):
    t^m ∣ φ (AFQ (K:=K) m P):=by
  have hd:t^m ∣ φ ((Polynomial.X^m:Jet B)*(P/ₘ Polynomial.X^m)):=by
    simp only [map_mul,map_pow,hε]
    exact dvd_mul_right _ _
  have heq:=congrArg φ (Polynomial.modByMonic_add_div P (Polynomial.X^m))
  rw [map_add] at heq
  have hsub:=dvd_sub hP hd
  rwa [← heq,add_sub_cancel_right] at hsub

end
end ProximityPrize.SubmissionLower.VV

end Compact_SecondJetTruncate

section Compact_SecondJetSupport

namespace ProximityPrize.SubmissionLower.DX
open scoped BigOperators Pointwise
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]
abbrev Poly:=MvPolynomial (Fin 5) K

def Box (lo a r s t:ℕ) (P:Poly (K:=K)):Prop:=
  ∀d ∈ P.support,lo≤d 0∧d 2≤a∧d 3≤r∧d 1≤s∧
    d 1+d 2+d 3+d 4≤t

def flatEquiv:Poly (K:=K) ≃ₐ[K] VV.Jet (MvPolynomial (Fin 3) K):=
  (MvPolynomial.finSuccEquiv K 4).trans (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv K 3))

theorem flatEquiv_X (j:Fin 5):
    flatEquiv (K:=K) (MvPolynomial.X j)=
      ![Polynomial.X,Polynomial.C Polynomial.X,
        Polynomial.C (Polynomial.C (MvPolynomial.X 0)),
        Polynomial.C (Polynomial.C (MvPolynomial.X 1)),
        Polynomial.C (Polynomial.C (MvPolynomial.X 2))] j:=by
  have h0:flatEquiv (K:=K) (MvPolynomial.X 0)=Polynomial.X:=by
    change Polynomial.map _ ((MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X 0))=_
    rw [MvPolynomial.finSuccEquiv_X_zero,Polynomial.map_X]
  have hs (i:Fin 4):flatEquiv (K:=K) (MvPolynomial.X i.succ)=
      Polynomial.C ((MvPolynomial.finSuccEquiv K 3) (MvPolynomial.X i)):=by
    change Polynomial.map _ ((MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X i.succ))=_
    rw [MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C]
    rfl
  fin_cases j
  · exact h0
  · change flatEquiv (K:=K) (MvPolynomial.X (0:Fin 4).succ)=Polynomial.C Polynomial.X
    rw [hs,MvPolynomial.finSuccEquiv_X_zero]
  · change flatEquiv (K:=K) (MvPolynomial.X ((0:Fin 3).succ).succ)=_
    rw [hs,MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change flatEquiv (K:=K) (MvPolynomial.X ((1:Fin 3).succ).succ)=_
    rw [hs,MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change flatEquiv (K:=K) (MvPolynomial.X ((2:Fin 3).succ).succ)=_
    rw [hs,MvPolynomial.finSuccEquiv_X_succ]
    rfl

theorem FDQ (P:Poly (K:=K)) (r h:ℕ) (d:Fin 3→₀ ℕ):
    AddMonoidAlgebra.coeff (((flatEquiv (K:=K) P).coeff r).coeff h) d=
      AddMonoidAlgebra.coeff P ((d.cons h).cons r):=by
  simp only [flatEquiv,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,Polynomial.coeff_map]
  change AddMonoidAlgebra.coeff (((MvPolynomial.finSuccEquiv K 3)
    (((MvPolynomial.finSuccEquiv K 4) P).coeff r)).coeff h) d=_
  rw [MvPolynomial.finSuccEquiv_coeff_coeff,MvPolynomial.finSuccEquiv_coeff_coeff]

def truncFlat (m:ℕ):Poly (K:=K)→ₗ[K] Poly (K:=K):=
  (flatEquiv (K:=K)).symm.toLinearMap.comp
    ((VV.AFQ (K:=K) m).comp (flatEquiv (K:=K)).toLinearMap)

theorem DGT (m:ℕ) (P:Poly (K:=K)):
    flatEquiv (K:=K) (truncFlat (K:=K) m P)=
      VV.AFQ (K:=K) m (flatEquiv (K:=K) P):=by
  simp [truncFlat]

theorem FDS (m r h:ℕ) (d:Fin 3→₀ ℕ) (P:Poly (K:=K)):
    AddMonoidAlgebra.coeff (truncFlat (K:=K) m P) ((d.cons h).cons r)=
      if r<m then AddMonoidAlgebra.coeff P ((d.cons h).cons r) else 0:=by
  rw [← FDQ,DGT]
  by_cases hr:r<m
  · rw [if_pos hr,VV.EEY m _ r hr,FDQ]
  · rw [if_neg hr,VV.EPQ m _ r (by omega)]
    simp

theorem EQF (m:ℕ) (P:Poly (K:=K)) (d:Fin 5→₀ ℕ)
    (hd:d ∈ (truncFlat (K:=K) m P).support):d 0<m∧d ∈ P.support:=by
  have heq:((d.tail.tail).cons (d.tail 0)).cons (d 0)=d:=by
    rw [Finsupp.cons_tail,Finsupp.cons_tail]
  have hne:=MvPolynomial.mem_support_iff.mp hd
  rw [← heq,FDS] at hne
  split_ifs at hne with h
  · refine ⟨h,MvPolynomial.mem_support_iff.mpr ?_⟩
    simpa only [heq] using hne
  · exact False.elim (hne rfl)

def Allowed (m L s1 s2:ℕ) (d:Fin 5→₀ ℕ):Prop:=
  d 0<m∧d 2≤d 0∧d 3≤s1∧d 1≤s2∧d 1+d 2+d 3+d 4≤L

end
end ProximityPrize.SubmissionLower.DX

end Compact_SecondJetSupport

section Compact_SecondJetLocal

namespace ProximityPrize.SubmissionLower.PX
open scoped BigOperators
open VV DX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]
abbrev Base:=MvPolynomial (Fin 3) K
abbrev Target:=Polynomial (MvPolynomial (Fin 4) K)

def baseEval:Base (K:=K)→ₐ[K] Target (K:=K):=
  MvPolynomial.aeval ![
    Polynomial.C (MvPolynomial.X 2)-Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
      Polynomial.X^2*Polynomial.C (MvPolynomial.X 1),
    Polynomial.C (MvPolynomial.X 2),Polynomial.C (MvPolynomial.X 3)]

def innerEval:Polynomial (Base (K:=K))→ₐ[K] Target (K:=K):=
  Polynomial.eval₂AlgHom baseEval (Polynomial.C (MvPolynomial.X 0)) (fun _=>Commute.all _ _)

def contact:Jet (Base (K:=K))→ₐ[K] Target (K:=K):=
  Polynomial.eval₂AlgHom innerEval Polynomial.X (fun _=>Commute.all _ _)

@[simp] theorem contact_X:contact (K:=K) Polynomial.X=Polynomial.X:=by
  simp [contact]

@[simp] theorem contact_C_C (p:Base (K:=K)):
    contact (K:=K) (Polynomial.C (Polynomial.C p))=baseEval (K:=K) p:=by
  simp [contact,innerEval]

@[simp] theorem contact_C_X:
    contact (K:=K) (Polynomial.C Polynomial.X)=Polynomial.C (MvPolynomial.X 0):=by
  simp [contact,innerEval]

def v:Base (K:=K):=MvPolynomial.X 0-MvPolynomial.X 1

theorem v_ne_zero:v (K:=K) ≠ 0:=by
  unfold v
  apply sub_ne_zero.mpr
  intro h
  have hh:=MvPolynomial.X_injective h
  exact (by decide:(0:Fin 3) ≠ 1) hh

theorem contact_v:contact (K:=K) (Polynomial.C (Polynomial.C v))=
    (Polynomial.X:Target (K:=K))*(-(Polynomial.C (MvPolynomial.X (0:Fin 4)):Target (K:=K))+
      Polynomial.X*Polynomial.C (MvPolynomial.X 1)):=by
  rw [contact_C_C]
  simp only [v,map_sub,baseEval,MvPolynomial.aeval_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

theorem contact_u:contact (K:=K)
    (Polynomial.C (Polynomial.C v)+Polynomial.X*Polynomial.C Polynomial.X)=
      Polynomial.X^2*Polynomial.C (MvPolynomial.X 1):=by
  rw [map_add,map_mul,contact_v,contact_X,contact_C_X]
  ring

end
end ProximityPrize.SubmissionLower.PX

end Compact_SecondJetLocal

section Compact_FiniteMonomials

namespace ProximityPrize.SubmissionLower.SC
open scoped BigOperators
noncomputable section
set_option autoImplicit false
variable {K σ I:Type*} [Field K] [Fintype I]
local instance:DecidableEq σ:=Classical.decEq σ
local instance:DecidableEq I:=Classical.decEq I

def reconstruct (e:I→σ→₀ ℕ):(I→K)→ₗ[K] MvPolynomial σ K:=
  ∑ i,(MvPolynomial.monomial (e i)).comp (LinearMap.proj i)

theorem CWA (e:I→σ→₀ ℕ) (c:I→K):
    reconstruct e c= ∑ i,MvPolynomial.monomial (e i) (c i):=by
  simp [reconstruct]

theorem ERW (e:I→σ→₀ ℕ) (he:Function.Injective e)
    (c:I→K) (i:I):AddMonoidAlgebra.coeff (reconstruct e c) (e i)=c i:=by
  classical
  rw [CWA,MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial,he.eq_iff]
  simp

theorem ABR (e:I→σ→₀ ℕ) (he:Function.Injective e):
    Function.Injective (reconstruct (K:=K) e):=by
  intro c d h
  funext i
  have hh:=congrArg (AddMonoidAlgebra.coeff · (e i)) h
  simpa only [ERW e he] using hh

theorem CLS (e:I→σ→₀ ℕ) (c:I→K)
    (d:σ→₀ ℕ) (hd:d ∉ Set.range e):
    AddMonoidAlgebra.coeff (reconstruct e c) d=0:=by
  classical
  rw [CWA,MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.coeff_monomial,if_neg (fun h=>hd ⟨i,h⟩)]

theorem mem_range_iff (e:I→σ→₀ ℕ) (he:Function.Injective e)
    (P:MvPolynomial σ K):P ∈ (reconstruct (K:=K) e).range ↔
      ∀d ∈ P.support,d ∈ Set.range e:=by
  classical
  constructor
  · rintro ⟨c,rfl⟩ d hd
    by_contra hn
    exact MvPolynomial.mem_support_iff.mp hd (CLS e c d hn)
  · intro h
    refine ⟨fun i=>P.coeff (e i),?_⟩
    ext d
    by_cases hd:d ∈ Set.range e
    · obtain ⟨i,rfl⟩:=hd
      exact ERW e he _ i
    · rw [CLS e _ d hd]
      exact (MvPolynomial.notMem_support_iff.mp (fun hs=>hd (h d hs))).symm

end
end ProximityPrize.SubmissionLower.SC

end Compact_FiniteMonomials

section Compact_SecondJetSpace

namespace ProximityPrize.SubmissionLower.ANF
open scoped BigOperators
open VV DX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

def bound (m L s1 s2:ℕ):Fin 5→ℕ:= ![m,s2+1,m,s1+1,L+1]

def Index (m L s1 s2:ℕ):=
  {d: ∀k,Fin (bound m L s1 s2 k)//
    (d 2).val≤(d 0).val∧(d 1).val+(d 2).val+(d 3).val+(d 4).val≤L}

instance (m L s1 s2:ℕ):Fintype (Index m L s1 s2):=by
  unfold Index
  infer_instance

def exponent {m L s1 s2:ℕ} (d:Index m L s1 s2):Fin 5→₀ ℕ:=
  Finsupp.equivFunOnFinite.symm (fun k=>(d.val k).val)

@[simp] theorem AUW {m L s1 s2:ℕ} (d:Index m L s1 s2) (k:Fin 5):
    exponent d k=(d.val k).val:=by simp [exponent]

theorem ACD (m L s1 s2:ℕ):
    Function.Injective (exponent (m:=m) (L:=L) (s1:=s1) (s2:=s2)):=by
  intro d e h
  apply Subtype.ext
  funext k
  apply Fin.ext
  simpa only [AUW] using congrArg (fun f:Fin 5→₀ ℕ=>f k) h

theorem EZJ {m L s1 s2:ℕ} (d:Index m L s1 s2):
    Allowed m L s1 s2 (exponent d):=by
  have h0:(d.val 0).val<m:=(d.val 0).isLt
  have h1:(d.val 1).val<s2+1:=(d.val 1).isLt
  have h3:(d.val 3).val<s1+1:=(d.val 3).isLt
  simp only [Allowed,AUW]
  exact ⟨h0,d.property.1,by omega,by omega,d.property.2⟩

theorem DMI (m L s1 s2:ℕ) (d:Fin 5→₀ ℕ):
    d ∈ Set.range (exponent (m:=m) (L:=L) (s1:=s1) (s2:=s2)) ↔
      Allowed m L s1 s2 d:=by
  constructor
  · rintro ⟨e,rfl⟩
    exact EZJ e
  · intro h
    dsimp only [Allowed] at h
    have hb: ∀k,d k<bound m L s1 s2 k:=by
      intro k
      fin_cases k
      · exact h.1
      · change d 1<s2+1
        omega
      · change d 2<m
        omega
      · change d 3<s1+1
        omega
      · change d 4<L+1
        omega
    let e:Index m L s1 s2:=⟨fun k=>⟨d k,hb k⟩,h.2.1,h.2.2.2.2⟩
    refine ⟨e,?_⟩
    ext k
    simp [e,exponent]

def sourceMap (m L s1 s2:ℕ):(Index m L s1 s2→K)→ₗ[K]
    Jet (MvPolynomial (Fin 3) K):=
  (flatEquiv (K:=K)).toLinearMap.comp (SC.reconstruct exponent)

def source (m L s1 s2:ℕ):Submodule K (Jet (MvPolynomial (Fin 3) K)):=
  (sourceMap (K:=K) m L s1 s2).range

instance source_finite (m L s1 s2:ℕ):FiniteDimensional K (source (K:=K) m L s1 s2):=by
  unfold source
  infer_instance

end
end ProximityPrize.SubmissionLower.ANF

end Compact_SecondJetSpace

section Compact_SecondJetFacetSupport

namespace ProximityPrize.SubmissionLower.DUH
open scoped BigOperators Pointwise
open MvPolynomial DX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

end
end ProximityPrize.SubmissionLower.DUH

end Compact_SecondJetFacetSupport

section Compact_SecondJetFacetSpace

namespace ProximityPrize.SubmissionLower.DGJ
open scoped BigOperators
open VV DX DUH
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

def Index (m L B s:ℕ):=
  {d:ANF.Index m L B s//(d.val 1).val+(d.val 3).val≤B}

instance (m L B s:ℕ):Fintype (Index m L B s):=by
  unfold Index
  infer_instance

def exponent {m L B s:ℕ} (d:Index m L B s):Fin 5→₀ ℕ:=
  ANF.exponent d.val

def sourceMap (m L B s:ℕ):(Index m L B s→K)→ₗ[K]
    Jet (MvPolynomial (Fin 3) K):=
  (flatEquiv (K:=K)).toLinearMap.comp (SC.reconstruct exponent)

def source (m L B s:ℕ):Submodule K (Jet (MvPolynomial (Fin 3) K)):=
  (sourceMap (K:=K) m L B s).range

instance source_finite (m L B s:ℕ):FiniteDimensional K (source (K:=K) m L B s):=by
  unfold source
  infer_instance

end
end ProximityPrize.SubmissionLower.DGJ

end Compact_SecondJetFacetSpace

section Compact_SecondJetGlobalSupport

namespace ProximityPrize.SubmissionLower.HZ
open scoped BigOperators Pointwise
open MvPolynomial DX VV
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

def LocalBound (B s L:ℕ) (P:Poly (K:=K)):Prop:=
  ∀d ∈ P.support,d 2≤d 0∧d 1+d 3≤B∧d 1≤s∧d 1+d 2+d 3+d 4≤L

theorem LocalBound.mono {B s L B' s' L' :ℕ} {P:Poly (K:=K)}
    (h:LocalBound B s L P) (hB:B≤B') (hs:s≤s') (hL:L≤L'):
    LocalBound B' s' L' P:=by
  intro d hd
  have hh:=h d hd
  exact ⟨hh.1,hh.2.1.trans hB,hh.2.2.1.trans hs,hh.2.2.2.trans hL⟩

theorem LocalBound.mul {B s L B' s' L' :ℕ} {P Q:Poly (K:=K)}
    (hP:LocalBound B s L P) (hQ:LocalBound B' s' L' Q):
    LocalBound (B+B') (s+s') (L+L') (P*Q):=by
  intro d hd
  obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  have hp:=hP u hu
  have hq:=hQ v hv
  simp only [Finsupp.add_apply]
  omega

theorem LocalBound.add {B s L:ℕ} {P Q:Poly (K:=K)}
    (hP:LocalBound B s L P) (hQ:LocalBound B s L Q):LocalBound B s L (P+Q):=by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hP d h
  · exact hQ d h

theorem local_C (c:K):LocalBound 0 0 0 (MvPolynomial.C c:Poly (K:=K)):=by
  intro d hd
  have hd0:d=0:=Finset.mem_singleton.mp (MvPolynomial.support_C_subset hd)
  subst d
  simp

theorem LocalBound.pow {B s L:ℕ} {P:Poly (K:=K)}
    (hP:LocalBound B s L P) (n:ℕ):LocalBound (n*B) (n*s) (n*L) (P^n):=by
  induction n with
  | zero=>simpa using (local_C (K:=K) 1)
  | succ n ih=>simpa only [pow_succ,Nat.succ_mul] using ih.mul hP

def localize (x u0 u1:K):Poly (K:=K)→ₐ[K] Poly (K:=K):=
  MvPolynomial.aeval ![MvPolynomial.C x+MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4+
      MvPolynomial.X 0*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

theorem local_X (j:Fin 5) (hj:j ≠ 2):
    LocalBound (if j=1∨j=3 then 1 else 0) (if j=1 then 1 else 0)
      (if j=0 then 0 else 1) (MvPolynomial.X j:Poly (K:=K)):=by
  intro d hd
  simp only [MvPolynomial.support_X,Finset.mem_singleton] at hd
  subst d
  fin_cases j<;>norm_num [Finsupp.single_apply,Fin.ext_iff] at*

theorem GGO:LocalBound 0 0 1
    (MvPolynomial.X 0*MvPolynomial.X 2:Poly (K:=K)):=by
  intro d hd
  rw [MvPolynomial.X,MvPolynomial.X,MvPolynomial.monomial_mul] at hd
  have hd' :=MvPolynomial.support_monomial_subset hd
  have hd0:=Finset.mem_singleton.mp hd'
  subst d
  norm_num [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff]

theorem localize_X (x u0 u1:K) (j:Fin 5):
    LocalBound (if j=1∨j=3 then 1 else 0) (if j=1 then 1 else 0)
      (if j=0 then 0 else 1) (localize x u0 u1 (MvPolynomial.X j)):=by
  have hE:LocalBound 0 0 0 (MvPolynomial.X 0:Poly (K:=K)):=by
    simpa using local_X (K:=K) 0 (by decide)
  have hZ:LocalBound 0 0 1 (MvPolynomial.X 4:Poly (K:=K)):=by
    simpa using local_X (K:=K) 4 (by decide)
  fin_cases j
  · simpa [localize] using (local_C x).add hE
  · simpa [localize] using local_X (K:=K) 1 (by decide)
  · have hU:LocalBound 0 0 1 (MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4:Poly (K:=K)):=
      ((local_C u0).mono (by omega) (by omega) (by omega)).add
        ((local_C u1).mul hZ)
    simpa [localize] using hU.add (GGO (K:=K))
  · simpa [localize] using local_X (K:=K) 3 (by decide)
  · simpa [localize] using hZ

theorem FSX (x u0 u1:K) (d:Fin 5→₀ ℕ) (c:K):
    LocalBound (d 1+d 3) (d 1) (d 1+d 2+d 3+d 4)
      (localize x u0 u1 (MvPolynomial.monomial d c)):=by
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,map_mul,map_pow,
      map_C]
    have h0:=(localize_X x u0 u1 0).pow (d 0)
    have h1:=(localize_X x u0 u1 1).pow (d 1)
    have h2:=(localize_X x u0 u1 2).pow (d 2)
    have h3:=(localize_X x u0 u1 3).pow (d 3)
    have h4:=(localize_X x u0 u1 4).pow (d 4)
    simpa [Nat.add_assoc] using (local_C c).mul (h0.mul (h1.mul (h2.mul (h3.mul h4))))
  · intro i
    simp

end
end ProximityPrize.SubmissionLower.HZ

end Compact_SecondJetGlobalSupport

section Compact_SecondJetRank

namespace ProximityPrize.SubmissionLower.BMX
open scoped BigOperators
open VV DX PX ANF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

def q (m s2 r h:ℕ):=max ((m-r+1)/2) (m-r-(s2-h))
def a (m s2 r h:ℕ):=min (q m s2 r h) (s2-h)
def b (m s2 r h:ℕ):=q m s2 r h-a m s2 r h

theorem budgets (m s2 r h:ℕ) (hr:r≤m) (hh:h≤s2):
    a m s2 r h+b m s2 r h=q m s2 r h∧h+a m s2 r h≤s2∧
      m≤r+2*a m s2 r h+b m s2 r h:=
  GHX m r s2 h hr hh

def Block (m L s1 s2 r h:ℕ):=
  {d:Fin 3→Fin (L+1)//
    (d 0).val+q m s2 r h≤r∧(d 1).val+q m s2 r h≤s1∧
      (d 0).val+(d 1).val+(d 2).val+h+q m s2 r h≤L}

instance (m L s1 s2 r h:ℕ):Fintype (Block m L s1 s2 r h):=by
  unfold Block
  infer_instance

def DWA {m L s1 s2 r h:ℕ} (d:Block m L s1 s2 r h):Fin 3→₀ ℕ:=
  Finsupp.equivFunOnFinite.symm (fun k=>(d.val k).val)

@[simp] theorem FIY {m L s1 s2 r h:ℕ}
    (d:Block m L s1 s2 r h) (k:Fin 3):DWA d k=(d.val k).val:=by
  simp [DWA]

theorem EPZ (m L s1 s2 r h:ℕ):
    Function.Injective (DWA (m:=m) (L:=L) (s1:=s1) (s2:=s2) (r:=r) (h:=h)):=by
  intro d e hde
  apply Subtype.ext
  funext k
  apply Fin.ext
  simpa only [FIY] using congrArg (fun f:Fin 3→₀ ℕ=>f k) hde

theorem GLV (m L s1 s2 r h:ℕ) (d:Block m L s1 s2 r h):
    MvPolynomial.monomial (DWA d) (1:K)=
      MvPolynomial.X 0^(d.val 0).val*MvPolynomial.X 1^(d.val 1).val*
        MvPolynomial.X 2^(d.val 2).val:=by
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype]
  · simp [Fin.prod_univ_three]
  · intro i
    simp

def contactMap (m:ℕ):Jet (Base (K:=K))→ₗ[K] Target (K:=K):=
  ((Polynomial.modByMonicHom (Polynomial.X^m:Target (K:=K))).restrictScalars K).comp
    (contact (K:=K)).toLinearMap

end
end ProximityPrize.SubmissionLower.BMX

end Compact_SecondJetRank

section Compact_SecondJetFacetRank

namespace ProximityPrize.SubmissionLower.DLH
open scoped BigOperators
open VV DX PX DGJ
open BMX (q a b budgets Block DWA EPZ GLV contactMap)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

end
end ProximityPrize.SubmissionLower.DLH

end Compact_SecondJetFacetRank

section Compact_SecondJetCounts

namespace ProximityPrize.SubmissionLower.DPO
open scoped BigOperators
open ANF BMX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev DWO (m L s1 s2 r h:ℕ):=
  Σ i:Fin (r-q m s2 r h+1),Σ j:Fin (s1-q m s2 r h+1),
    Fin (L+1-h-q m s2 r h-i.val-j.val)

def blockEquiv (m L s1 s2 r h:ℕ) (hr:q m s2 r h≤r) (hs:q m s2 r h≤s1):
    Block m L s1 s2 r h ≃ DWO m L s1 s2 r h where
  toFun d:=by
    have hd:=d.property
    exact ⟨⟨(d.val 0).val,by omega⟩,⟨(d.val 1).val,by omega⟩,
      ⟨(d.val 2).val,by dsimp;omega⟩⟩
  invFun u:=by
    rcases u with ⟨i,j,z⟩
    have hi:=i.isLt
    have hj:=j.isLt
    have hz:=z.isLt
    let iv:Fin (L+1):=⟨i.val,by omega⟩
    let jv:Fin (L+1):=⟨j.val,by omega⟩
    let zv:Fin (L+1):=⟨z.val,by omega⟩
    refine ⟨![iv,jv,zv],?_,?_,?_⟩
    · change i.val+q m s2 r h≤r
      omega
    · change j.val+q m s2 r h≤s1
      omega
    · change i.val+j.val+z.val+h+q m s2 r h≤L
      omega
  left_inv d:=by
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k<;>rfl
  right_inv u:=by
    rcases u with ⟨i,j,z⟩
    rfl

theorem EBT (m L s1 s2 r h:ℕ)
    (hr:q m s2 r h≤r) (hs:q m s2 r h≤s1):
    Fintype.card (Block m L s1 s2 r h)=
      ∑ i:Fin (r-q m s2 r h+1),∑ j:Fin (s1-q m s2 r h+1),
        (L+1-h-q m s2 r h-i.val-j.val):=by
  rw [Fintype.card_congr (blockEquiv m L s1 s2 r h hr hs)]
  simp [DWO]

theorem CVB (m L s1 s2 r h:ℕ)
    (hq: ¬(q m s2 r h≤r∧q m s2 r h≤s1)):
    Fintype.card (Block m L s1 s2 r h)=0:=by
  letI:IsEmpty (Block m L s1 s2 r h):=⟨fun d=>by have hd:=d.property;omega⟩
  simp

def rectangle (A B C:ℕ):=
  A*B*C-B*(A*(A-1)/2)-A*(B*(B-1)/2)

theorem sum_fin_val (n:ℕ):(∑ i:Fin n,i.val)=n*(n-1)/2:=by
  rw [Fin.sum_univ_eq_sum_range (fun i:ℕ=>i),Finset.sum_range_id]

theorem FAH (A B C:ℕ) (h: ∀i:Fin A,∀j:Fin B,i.val+j.val≤C):
    (∑ i:Fin A,∑ j:Fin B,(C-i.val-j.val))=rectangle A B C:=by
  have hs:(∑ i:Fin A,∑ j:Fin B,((C-i.val-j.val)+i.val+j.val))=A*(B*C):=by
    calc
      _= ∑ _i:Fin A,∑ _j:Fin B,C:=by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hij:=h i j
        omega
      _=_:=by simp
  have hs' :(∑ i:Fin A,∑ j:Fin B,(C-i.val-j.val))+
      B*(A*(A-1)/2)+A*(B*(B-1)/2)=A*(B*C):=by
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,← Finset.mul_sum,sum_fin_val] using hs
  unfold rectangle
  rw [mul_assoc]
  omega

theorem DVH (m L s1 s2 r h:ℕ) (hL:m+s1+s2≤L)
    (hrm:r<m) (hhs:h≤s2):
    Fintype.card (Block m L s1 s2 r h)=
      if q m s2 r h≤r∧q m s2 r h≤s1 then
        rectangle (r-q m s2 r h+1) (s1-q m s2 r h+1) (L+1-h-q m s2 r h)
      else 0:=by
  split_ifs with hq
  · rw [EBT m L s1 s2 r h hq.1 hq.2]
    apply FAH
    intro i j
    have hi:=i.isLt
    have hj:=j.isLt
    omega
  · exact CVB m L s1 s2 r h hq

def kernelCell (m L s1 s2 r h:ℕ):ℕ:=
  if q m s2 r h≤r∧q m s2 r h≤s1 then
    rectangle (r-q m s2 r h+1) (s1-q m s2 r h+1) (L+1-h-q m s2 r h)
  else 0

variable {K:Type*} [Field K]

end
end ProximityPrize.SubmissionLower.DPO

end Compact_SecondJetCounts

section Compact_SecondJetFacetCounts

namespace ProximityPrize.SubmissionLower.DZU
open scoped BigOperators
open DGJ DLH
open BMX (Block)
open DPO (rectangle FAH kernelCell DVH)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K:Type*} [Field K]

end
end ProximityPrize.SubmissionLower.DZU

end Compact_SecondJetFacetCounts

section Compact_SecondJetGlobalMap

namespace ProximityPrize.SubmissionLower.DLW
open scoped BigOperators
open DX VV HZ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I N:Type*} [Field K] [Fintype I] [Fintype N]

def APX (e:I→Fin 5→₀ ℕ) (m:ℕ) (x u0 u1:K):
    (I→K)→ₗ[K] Jet (MvPolynomial (Fin 3) K):=
  (AFQ (K:=K) m).comp ((flatEquiv (K:=K)).toLinearMap.comp
    ((localize x u0 u1).toLinearMap.comp (SC.reconstruct e)))

theorem CMK {C:Type*} [CommRing C]
    (φ:Jet (MvPolynomial (Fin 3) K)→+*C) (t:C) (m:ℕ)
    (P:Jet (MvPolynomial (Fin 3) K)) (hε:φ Polynomial.X=t)
    (hP:t^m ∣ φ (AFQ (K:=K) m P)):t^m ∣ φ P:=by
  have hd:t^m ∣ φ ((Polynomial.X^m:Jet (MvPolynomial (Fin 3) K))*
      (P/ₘ Polynomial.X^m)):=by
    simp only [map_mul,map_pow,hε]
    exact dvd_mul_right _ _
  have heq:=congrArg φ (Polynomial.modByMonic_add_div P (Polynomial.X^m))
  rw [map_add] at heq
  exact heq ▸ dvd_add hP hd

end
end ProximityPrize.SubmissionLower.DLW

end Compact_SecondJetGlobalMap

section Compact_SecondJetGlobalIndex

namespace ProximityPrize.SubmissionLower.CSV
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K N:Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.CSV

end Compact_SecondJetGlobalIndex

section Compact_SecondJetGlobalCounts

namespace ProximityPrize.SubmissionLower.CPV
open scoped BigOperators
open CSV
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem EOU (n:ℕ):
    (∑ i ∈ Finset.range n,i^2)*6=n*(n-1)*(2*n-1):=by
  induction n with
  | zero=>simp
  | succ n ih=>
    rw [Finset.sum_range_succ]
    cases n with
    | zero=>simp
    | succ n=>
      have h1:2*(n+1)-1=2*n+1:=by omega
      have h2:2*(n+1+1)-1=2*n+3:=by omega
      simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel,h1] at ih
      simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel,h2]
      nlinarith [ih]

theorem GKE (n:ℕ):
    (∑ i:Fin n,i.val^2)=n*(n-1)*(2*n-1)/6:=by
  rw [Fin.sum_univ_eq_sum_range (fun i:ℕ=>i^2),← EOU]
  exact (Nat.mul_div_cancel _ (by decide:0<6)).symm

def weightedCell (q w C n:ℕ):ℕ:=
  n*q*C+w*(n*(n-1)*(2*n-1)/6)-(q+w*C)*(n*(n-1)/2)

theorem ESA (q w C n:ℕ)
    (hq: ∀y:Fin n,w*y.val≤q) (hC: ∀y:Fin n,y.val≤C):
    (∑ y:Fin n,(q-w*y.val)*(C-y.val))=weightedCell q w C n:=by
  have hcell: ∀y:Fin n,
      (q-w*y.val)*(C-y.val)+(q+w*C)*y.val=q*C+w*y.val^2:=by
    intro y
    have hqy:q=q-w*y.val+w*y.val:=(Nat.sub_add_cancel (hq y)).symm
    have hCy:C=C-y.val+y.val:=(Nat.sub_add_cancel (hC y)).symm
    calc
      _=(q-w*y.val)*(C-y.val)+((q-w*y.val+w*y.val)+w*(C-y.val+y.val))*y.val:=by
        conv_lhs=>arg 2;arg 1;rw [hqy,hCy]
      _=(q-w*y.val+w*y.val)*(C-y.val+y.val)+w*y.val^2:=by ring
      _=_:=by rw [← hqy,← hCy]
  have hs:=Finset.sum_congr (s₁:=Finset.univ) rfl (fun y _=>hcell y)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,DPO.sum_fin_val,GKE] at hs
  unfold weightedCell
  rw [mul_comm n q,mul_assoc]
  omega

end
end ProximityPrize.SubmissionLower.CPV

end Compact_SecondJetGlobalCounts

section Compact_SecondJetFacetReceipt

namespace ProximityPrize.SubmissionLower.FCB
open DZU DLH
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K:Type*} [Field K]

end ProximityPrize.SubmissionLower.FCB

end Compact_SecondJetFacetReceipt

section Compact_SecondJetGlobalReceipt

namespace ProximityPrize.SubmissionLower.EWF
open scoped BigOperators
open CSV CPV
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K N:Type*} [Field K] [Fintype N]

end ProximityPrize.SubmissionLower.EWF

end Compact_SecondJetGlobalReceipt

section Compact_SecondJetDifferentiation

namespace ProximityPrize.SubmissionLower.IM
open scoped BigOperators
open MvPolynomial DX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

def substitute:Poly (K:=K)→ₐ[K] Poly (K:=K):=
  MvPolynomial.aeval ![MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.X 3-MvPolynomial.X 0*MvPolynomial.X 1+
      MvPolynomial.X 0^2*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

theorem chain_X (j:Fin 5):
    MvPolynomial.X 0*substitute (K:=K) (pderiv 1 (MvPolynomial.X j))=
      MvPolynomial.X 0*pderiv 1 (substitute (K:=K) (MvPolynomial.X j))+
        pderiv 2 (substitute (K:=K) (MvPolynomial.X j)):=by
  fin_cases j<;>simp [substitute,pderiv_mul,pderiv_pow,Pi.single_apply]<;>ring

theorem chain_rule (P:Poly (K:=K)):
    MvPolynomial.X 0*substitute (K:=K) (pderiv 1 P)=
      MvPolynomial.X 0*pderiv 1 (substitute (K:=K) P)+
        pderiv 2 (substitute (K:=K) P):=by
  induction P using MvPolynomial.induction_on with
  | C c=>simp [substitute]
  | add P Q hP hQ=>
    simp only [map_add]
    linear_combination hP+hQ
  | mul_X P j hP=>
    have hX:=chain_X (K:=K) j
    simp only [pderiv_mul,map_add,map_mul]
    linear_combination substitute (K:=K) (MvPolynomial.X j)*hP+substitute (K:=K) P*hX

theorem DDF (P:Poly (K:=K)) (j:Fin 5) (hj:j ≠ 0) (m:ℕ)
    (hP:MvPolynomial.X 0^m ∣ P):MvPolynomial.X 0^m ∣ pderiv j P:=by
  obtain ⟨Q,rfl⟩:=hP
  rw [pderiv_mul,pderiv_pow,pderiv_X_of_ne (Ne.symm hj)]
  simp only [mul_zero,zero_mul,zero_add]
  exact dvd_mul_right _ _

theorem FNJ (P:Poly (K:=K)) (m:ℕ)
    (hP:MvPolynomial.X 0^(m+1) ∣ substitute (K:=K) P):
    MvPolynomial.X 0^m ∣ substitute (K:=K) (pderiv 1 P):=by
  have hs:=DDF (substitute (K:=K) P) 1 (by decide) (m+1) hP
  have ht:=DDF (substitute (K:=K) P) 2 (by decide) (m+1) hP
  have hh:MvPolynomial.X 0^(m+1) ∣
      MvPolynomial.X 0*substitute (K:=K) (pderiv 1 P):=by
    rw [chain_rule]
    exact dvd_add (dvd_mul_of_dvd_right hs _) ht
  rw [pow_succ'] at hh
  exact (mul_dvd_mul_iff_left (MvPolynomial.X_ne_zero (0:Fin 5))).mp hh

theorem EEG (P:Poly (K:=K)) (m d:ℕ)
    (hP:MvPolynomial.X 0^(m+d) ∣ substitute (K:=K) P):
    MvPolynomial.X 0^m ∣ substitute (K:=K) ((pderiv 1)^[d] P):=by
  induction d generalizing P with
  | zero=>simpa using hP
  | succ d ih=>
    have hfirst:=FNJ P (m+d) (by simpa only [Nat.add_assoc] using hP)
    simpa only [Function.iterate_succ_apply] using ih (pderiv 1 P) hfirst

theorem FMB (P:Poly (K:=K)):
    (MvPolynomial.finSuccEquiv K 4) (substitute (K:=K) P)=
      PX.contact (K:=K) (flatEquiv (K:=K) P):=by
  have h0:(MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (0:Fin 5))=Polynomial.X:=
    MvPolynomial.finSuccEquiv_X_zero
  have h1:(MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (1:Fin 5))=
      Polynomial.C (MvPolynomial.X (0:Fin 4)):=MvPolynomial.finSuccEquiv_X_succ (j:=0)
  have h2:(MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (2:Fin 5))=
      Polynomial.C (MvPolynomial.X (1:Fin 4)):=MvPolynomial.finSuccEquiv_X_succ (j:=1)
  have h3:(MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (3:Fin 5))=
      Polynomial.C (MvPolynomial.X (2:Fin 4)):=MvPolynomial.finSuccEquiv_X_succ (j:=2)
  have h4:(MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (4:Fin 5))=
      Polynomial.C (MvPolynomial.X (3:Fin 4)):=MvPolynomial.finSuccEquiv_X_succ (j:=3)
  have h:(MvPolynomial.finSuccEquiv K 4).toAlgHom.comp (substitute (K:=K))=
      (PX.contact (K:=K)).comp (flatEquiv (K:=K)).toAlgHom:=by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j<;>
      simp [substitute,DX.flatEquiv_X,PX.baseEval,
        h0,h1,h2,h3,h4]<;>ring
  exact DFunLike.congr_fun h P

end
end ProximityPrize.SubmissionLower.IM

end Compact_SecondJetDifferentiation

section Compact_SecondJetGlobalDifferentiation

namespace ProximityPrize.SubmissionLower.KL
open MvPolynomial DX HZ IM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

theorem GLF (P:Poly (K:=K)) (d:Fin 5→₀ ℕ)
    (hd:d ∈ (pderiv 1 P).support):d+Finsupp.single 1 1 ∈ P.support:=by
  have h:=MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_pderiv] at h
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  exact h (by rw [hz,zero_mul])

theorem CAJ (P:Poly (K:=K)) (n:ℕ) (d:Fin 5→₀ ℕ)
    (hd:d ∈ ((pderiv 1)^[n] P).support):d+Finsupp.single 1 n ∈ P.support:=by
  induction n generalizing d with
  | zero=>simpa using hd
  | succ n ih=>
    rw [Function.iterate_succ_apply'] at hd
    have hh:=ih (d+Finsupp.single 1 1) (GLF _ d hd)
    have he:d+Finsupp.single 1 1+Finsupp.single 1 n=d+Finsupp.single 1 (n+1):=by
      rw [add_assoc,← Finsupp.single_add,Nat.add_comm 1 n]
    rwa [he] at hh

theorem GIH (x u0 u1:K) (P:Poly (K:=K)):
    localize x u0 u1 (pderiv 1 P)=pderiv 1 (localize x u0 u1 P):=by
  have hX (j:Fin 5):localize x u0 u1 (pderiv 1 (MvPolynomial.X j))=
      pderiv 1 (localize x u0 u1 (MvPolynomial.X j)):=by
    fin_cases j<;>simp [localize,pderiv_mul,Pi.single_apply]
  induction P using MvPolynomial.induction_on with
  | C c=>simp [localize]
  | add P Q hP hQ=>simp only [map_add,hP,hQ]
  | mul_X P j hP=>simp only [pderiv_mul,map_add,map_mul,hP,hX]

theorem GBX (x u0 u1:K) (P:Poly (K:=K)) (n:ℕ):
    localize x u0 u1 ((pderiv 1)^[n] P)=(pderiv 1)^[n] (localize x u0 u1 P):=by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [Function.iterate_succ_apply',Function.iterate_succ_apply',GIH,ih]

theorem ADR (x u0 u1:K) (P:Poly (K:=K)) (m d:ℕ)
    (hP:MvPolynomial.X 0^(m+d) ∣ substitute (K:=K) (localize x u0 u1 P)):
    MvPolynomial.X 0^m ∣ substitute (K:=K) (localize x u0 u1 ((pderiv 1)^[d] P)):=by
  rw [GBX]
  exact EEG (localize x u0 u1 P) m d hP

theorem CGJ (P:Poly (K:=K)) (m:ℕ)
    (hP:Polynomial.X^m ∣ PX.contact (K:=K) (flatEquiv (K:=K) P)):
    MvPolynomial.X 0^m ∣ substitute (K:=K) P:=by
  obtain ⟨Q,hQ⟩:=hP
  refine ⟨(MvPolynomial.finSuccEquiv K 4).symm Q,?_⟩
  apply (MvPolynomial.finSuccEquiv K 4).injective
  rw [FMB,map_mul,map_pow,MvPolynomial.finSuccEquiv_X_zero,
    AlgEquiv.apply_symm_apply]
  exact hQ

end
end ProximityPrize.SubmissionLower.KL

end Compact_SecondJetGlobalDifferentiation

section Compact_SecondJet6804

namespace ProximityPrize.SubmissionLower.GTY
open MvPolynomial DX HZ IM
open KL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N:Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.GTY

end Compact_SecondJet6804

section Compact_SecondJetContact

namespace ProximityPrize.SubmissionLower.EZK
open Polynomial
noncomputable section
set_option autoImplicit false

variable {K:Type*} [CommRing K]

theorem EXT (q:Polynomial K):
    (Polynomial.X:Polynomial K)^3 ∣
      q-C (q.coeff 0)-Polynomial.X*q.derivative+Polynomial.X^2*hasseDeriv 2 q:=by
  rw [X_pow_dvd_iff]
  intro d hd
  interval_cases d<;>
    simp [coeff_sub,coeff_add,coeff_X_pow_mul',coeff_X_mul,
      coeff_derivative,hasseDeriv_coeff]<;>ring

theorem DNA (q:Polynomial K):
    ∃U:Polynomial K,
      q-C (q.coeff 0)=
        Polynomial.X*(q.derivative-Polynomial.X*hasseDeriv 2 q+Polynomial.X^2*U):=by
  obtain ⟨U,hU⟩:=EXT q
  refine ⟨U,?_⟩
  linear_combination hU

theorem FBF (f:Polynomial K) (x:K):
    ∃U:Polynomial K,
      taylor x f-C (f.eval x)=
        Polynomial.X*((taylor x f).derivative-Polynomial.X*hasseDeriv 2 (taylor x f)+Polynomial.X^2*U):=by
  simpa only [taylor_coeff_zero] using DNA (taylor x f)

end
end ProximityPrize.SubmissionLower.EZK

end Compact_SecondJetContact

section Compact_SecondJetSpecialize

namespace ProximityPrize.SubmissionLower.HH
open MvPolynomial DX HZ IM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]

theorem hasse_taylor (f:Polynomial K) (x:K) (n:ℕ):
    Polynomial.hasseDeriv n (Polynomial.taylor x f)=
      Polynomial.taylor x (Polynomial.hasseDeriv n f):=by
  ext i
  rw [Polynomial.hasseDeriv_coeff,Polynomial.taylor_coeff,Polynomial.taylor_coeff]
  have hc:=congrArg (fun T:Polynomial K→ₗ[K] Polynomial K=>(T f).eval x)
    (Polynomial.hasseDeriv_comp (R:=K) i n)
  simp only [LinearMap.comp_apply,LinearMap.smul_apply,Polynomial.eval_smul,
    nsmul_eq_mul] at hc
  rw [hc]
  simp [Nat.choose_symm_add,mul_comm]

theorem BVR (f:Polynomial K) (x:K):
    (Polynomial.taylor x f).derivative=Polynomial.taylor x f.derivative:=by
  simpa only [Polynomial.hasseDeriv_one] using hasse_taylor f x 1

def specialize (f:Polynomial K) (z:K):Poly (K:=K)→ₐ[K] Polynomial K:=
  MvPolynomial.aeval ![Polynomial.X,Polynomial.hasseDeriv 2 f,f,f.derivative,Polynomial.C z]

def realize (q U:Polynomial K) (z:K):Poly (K:=K)→ₐ[K] Polynomial K:=
  MvPolynomial.aeval ![Polynomial.X,Polynomial.hasseDeriv 2 q,U,q.derivative,Polynomial.C z]

theorem GGK (f U:Polynomial K) (x u0 u1 z:K)
    (hagree:f.eval x=u0+u1*z)
    (hU:Polynomial.taylor x f-Polynomial.C (f.eval x)=
      Polynomial.X*((Polynomial.taylor x f).derivative-
        Polynomial.X*Polynomial.hasseDeriv 2 (Polynomial.taylor x f)+Polynomial.X^2*U))
    (P:Poly (K:=K)):
    realize (Polynomial.taylor x f) U z (substitute (K:=K) (localize x u0 u1 P))=
      Polynomial.taylor x (specialize f z P):=by
  have heq:(realize (Polynomial.taylor x f) U z).comp
      ((substitute (K:=K)).comp (localize x u0 u1))=
      (Polynomial.taylorAlgHom x).comp (specialize f z):=by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j<;>
      simp [realize,substitute,localize,specialize,hasse_taylor,BVR]
    · ring
    · rw [hagree,map_add,map_mul] at hU
      simp only [BVR,hasse_taylor] at hU
      linear_combination-hU
  exact DFunLike.congr_fun heq P

theorem root_contact (P:Poly (K:=K)) (f:Polynomial K) (x u0 u1 z:K) (m:ℕ)
    (hagree:f.eval x=u0+u1*z)
    (hP:MvPolynomial.X 0^m ∣ substitute (K:=K) (localize x u0 u1 P)):
    (Polynomial.X-Polynomial.C x)^m ∣ specialize f z P:=by
  obtain ⟨U,hU⟩:=EZK.FBF f x
  have hd:=map_dvd (realize (Polynomial.taylor x f) U z).toRingHom hP
  change realize (Polynomial.taylor x f) U z (MvPolynomial.X 0^m) ∣
    realize (Polynomial.taylor x f) U z (substitute (K:=K) (localize x u0 u1 P)) at hd
  rw [map_pow,GGK f U x u0 u1 z hagree hU P] at hd
  have hx:realize (Polynomial.taylor x f) U z (MvPolynomial.X 0)=Polynomial.X:=by
    simp [realize]
  rw [hx] at hd
  obtain ⟨Q,hQ⟩:=hd
  refine ⟨(Polynomial.taylorEquiv x).symm Q,?_⟩
  apply Polynomial.taylor_injective x
  rw [Polynomial.taylor_mul,Polynomial.taylor_pow]
  have hh:Polynomial.taylor x (Polynomial.X-Polynomial.C x)=Polynomial.X:=by simp
  rw [hh]
  change Polynomial.taylor x (specialize f z P)=Polynomial.X^m*
    ((Polynomial.taylorEquiv x) ((Polynomial.taylorEquiv x).symm Q))
  rw [AlgEquiv.apply_symm_apply]
  exact hQ

theorem GIB (f:Polynomial K) (z:K) (w:ℕ) (hf:f.natDegree≤w)
    (d:Fin 5→₀ ℕ) (c:K):
    (specialize f z (MvPolynomial.monomial d c)).natDegree≤
      d 0+w*d 2+(w-1)*d 3+(w-2)*d 1:=by
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,map_mul,map_pow]
    have hc:(specialize f z (MvPolynomial.C c)).natDegree≤0:=by simp [specialize]
    have h0:(specialize f z (MvPolynomial.X 0)^d 0).natDegree≤d 0:=by simp [specialize]
    have hs:(Polynomial.hasseDeriv 2 f).natDegree≤w-2:=
      (Polynomial.natDegree_hasseDeriv_le f 2).trans (Nat.sub_le_sub_right hf 2)
    have hr:f.derivative.natDegree≤w-1:=
      (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1)
    have h1:(specialize f z (MvPolynomial.X 1)^d 1).natDegree≤d 1*(w-2):=by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 1) hs
    have h2:(specialize f z (MvPolynomial.X 2)^d 2).natDegree≤d 2*w:=by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 2) hf
    have h3:(specialize f z (MvPolynomial.X 3)^d 3).natDegree≤d 3*(w-1):=by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 3) hr
    have h4:(specialize f z (MvPolynomial.X 4)^d 4).natDegree≤0:=by simp [specialize]
    have hh:=Polynomial.natDegree_mul_le_of_le hc (Polynomial.natDegree_mul_le_of_le h0
      (Polynomial.natDegree_mul_le_of_le h1 (Polynomial.natDegree_mul_le_of_le h2
        (Polynomial.natDegree_mul_le_of_le h3 h4))))
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Nat.mul_comm] using hh
  · intro i
    simp

theorem DRK (P:Poly (K:=K)) (f:Polynomial K) (z:K) (w D:ℕ)
    (hf:f.natDegree≤w) (hD:0<D)
    (hP: ∀d ∈ P.support,d 0+w*d 2+(w-1)*d 3+(w-2)*d 1<D):
    (specialize f z P).natDegree<D:=by
  classical
  have hterms: ∀d ∈ P.support,
      (specialize f z (MvPolynomial.monomial d (AddMonoidAlgebra.coeff P d))).natDegree≤D-1:=by
    intro d hd
    have hw:=hP d hd
    have hh:=GIB f z w hf d (AddMonoidAlgebra.coeff P d)
    omega
  rw [MvPolynomial.as_sum P,map_sum]
  have hh:=Polynomial.natDegree_sum_le_of_forall_le P.support
    (fun d=>specialize f z (MvPolynomial.monomial d (AddMonoidAlgebra.coeff P d))) hterms
  exact lt_of_le_of_lt hh (by omega)

end
end ProximityPrize.SubmissionLower.HH

end Compact_SecondJetSpecialize

section Compact_SecondJetVanish

namespace ProximityPrize.SubmissionLower.CAG
open MvPolynomial DX HZ IM HH
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq N:=Classical.decEq N

theorem ALK (P:Poly (K:=K)) (f:Polynomial K) (z:K)
    (nodes:N ↪ K) (u0 u1:N→K) (S:Finset N) (m:ℕ)
    (hcontact: ∀i ∈ S,MvPolynomial.X 0^m ∣ substitute (K:=K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (hvalues: ∀i ∈ S,f.eval (nodes i)=u0 i+u1 i*z)
    (hdegree:(specialize f z P).natDegree<m*S.card):specialize f z P=0:=by
  classical
  by_contra hn
  have hmult: ∀i ∈ S,m≤(specialize f z P).rootMultiplicity (nodes i):=by
    intro i hi
    exact (Polynomial.le_rootMultiplicity_iff hn).mpr
      (root_contact P f (nodes i) (u0 i) (u1 i) z m (hvalues i hi) (hcontact i hi))
  have hh:=BCHKSSubstitutionVanish.AFP
    (specialize f z P) nodes S m hmult
  exact (Nat.not_le_of_gt hdegree) hh

variable [Fintype N]

end
end ProximityPrize.SubmissionLower.CAG

end Compact_SecondJetVanish

section Compact_SecondJetCoefficients

namespace ProximityPrize.SubmissionLower.BX
open MvPolynomial DX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

def asS:Poly (K:=K) ≃ₐ[K] Polynomial (MvPolynomial (Fin 4) K):=
  (MvPolynomial.renameEquiv K (Equiv.swap (0:Fin 5) 1)).trans (MvPolynomial.finSuccEquiv K 4)

def liftExponent (j:ℕ) (d:Fin 4→₀ ℕ):Fin 5→₀ ℕ:=
  Finsupp.mapDomain (Equiv.swap (0:Fin 5) 1) (d.cons j)

theorem swap_lift (j:ℕ) (d:Fin 4→₀ ℕ):
    Finsupp.mapDomain (Equiv.swap (0:Fin 5) 1) (liftExponent j d)=d.cons j:=by
  ext i
  simp [liftExponent,Finsupp.mapDomain_equiv_apply]

set_option maxRecDepth 40000 in
theorem _Q17 (j:ℕ) (d:Fin 4→₀ ℕ):
    liftExponent j d 0=d 0∧liftExponent j d 1=j∧
      liftExponent j d 2=d 1∧liftExponent j d 3=d 2∧liftExponent j d 4=d 3:=by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals try simp [liftExponent,Finsupp.mapDomain_equiv_apply,
    Equiv.swap_apply_def]
  all_goals rfl

theorem asS_coeff (P:Poly (K:=K)) (j:ℕ) (d:Fin 4→₀ ℕ):
    AddMonoidAlgebra.coeff ((asS (K:=K) P).coeff j) d=
      AddMonoidAlgebra.coeff P (liftExponent j d):=by
  change AddMonoidAlgebra.coeff (((MvPolynomial.finSuccEquiv K 4)
    (MvPolynomial.rename (Equiv.swap (0:Fin 5) 1) P)).coeff j) d=_
  rw [MvPolynomial.finSuccEquiv_coeff_coeff,← swap_lift j d,
    MvPolynomial.coeff_rename_mapDomain _ (Equiv.swap (0:Fin 5) 1).injective]

theorem AJU (P:Poly (K:=K)) (j:ℕ) (d:Fin 4→₀ ℕ)
    (hd:d ∈ ((asS (K:=K) P).coeff j).support):liftExponent j d ∈ P.support:=by
  simpa only [MvPolynomial.mem_support_iff,asS_coeff] using hd

end
end ProximityPrize.SubmissionLower.BX

end Compact_SecondJetCoefficients

section Compact_RootMultiplicityValuation

namespace ProximityPrize.SubmissionLower.ALF
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L:Type*} [Field L]
abbrev Value:=WithZero (Multiplicative ℤ)

def polyValue (v:Valuation L Value) (P:Polynomial L):Value:=
  P.support.sup (fun i=>v (P.coeff i))

end
end ProximityPrize.SubmissionLower.ALF

end Compact_RootMultiplicityValuation

section Compact_RootMultiplicityHeight

namespace ProximityPrize.SubmissionLower.DNX
open scoped Classical BigOperators WithZero
open RCN026 RCN187 ALF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable (K L:Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem EPP (c:L) (hc:c ≠ 0) (W:Finset (Place K L))
    (hW:placesFor K L c hc ⊆ W):(∑ v ∈ W,(v.val c).log)=0:=by
  classical
  have hz:(∑ v ∈ placesFor K L c hc,(v.val c).log)=0:=by
    simpa only [order,Finset.sum_neg_distrib,neg_eq_zero] using
      DAL K L c hc
  calc
    (∑ v ∈ W,(v.val c).log)= ∑ v ∈ placesFor K L c hc,(v.val c).log:=by
      symm
      apply Finset.sum_subset hW
      intro v hv hnot
      have ho:order K L v c=0:=by
        by_contra h
        exact hnot (ALB K L c hc v h)
      simpa only [order,neg_eq_zero] using ho
    _=0:=hz

end
end ProximityPrize.SubmissionLower.DNX

end Compact_RootMultiplicityHeight

section Compact_RootMultiplicityFlag

namespace ProximityPrize.SubmissionLower._Q24
open scoped Classical BigOperators WithZero
open RCN026 RCN095 RCN187 RCN204
open RCN344 (NP)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable (K L:Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

end
end ProximityPrize.SubmissionLower._Q24

end Compact_RootMultiplicityFlag

section Compact_SecondJetFlagCoefficients

namespace ProximityPrize.SubmissionLower.AUS
open scoped BigOperators
open MvPolynomial RCN095 BX DX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]

def freeze (x:K):MvPolynomial (Fin 4) K→ₐ[K] MvPolynomial (Fin 3) K:=
  MvPolynomial.aeval ![MvPolynomial.C x,MvPolynomial.X 0,MvPolynomial.X 1,MvPolynomial.X 2]

theorem GFZ (x:K) (d:Fin 4→₀ ℕ) (c:K):
    freeze x (MvPolynomial.monomial d c)=MvPolynomial.monomial d.tail (c*x^d 0):=by
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype]
  · rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype]
    · simp [freeze,Fin.prod_univ_four,Fin.prod_univ_three,Finsupp.tail_apply,
        map_mul,map_pow,mul_assoc]
    · intro i
      simp
  · intro i
    simp

theorem GVR (P:MvPolynomial (Fin 4) K) (x:K) (p:FlagDegree)
    (hP: ∀d ∈ P.support,InFlag p d.tail):BI p (freeze x P):=by
  rw [MvPolynomial.as_sum P,map_sum]
  intro e he
  obtain ⟨d,hd,hed⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  rw [GFZ] at hed
  have heq:e=d.tail:=Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
  subst e
  exact hP d hd

end
end ProximityPrize.SubmissionLower.AUS

end Compact_SecondJetFlagCoefficients

section Compact_RootMultiplicityWeightedValuation

namespace ProximityPrize.SubmissionLower.AOU
open scoped BigOperators WithZero
open ALF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L:Type*} [Field L]

theorem GIN (v:Valuation L Value) (x y:L) (b B:Value)
    (hx:v x*b≤B) (hy:v y*b≤B):v (x-y)*b≤B:=by
  exact (mul_le_mul_left (v.map_sub x y) b).trans (by rw [max_mul];exact max_le hx hy)

theorem CWO (v:Valuation L Value) (x y:L) (b B:Value)
    (hx:v x*b≤B) (hy:v y*b≤B):v (x+y)*b≤B:=by
  exact (mul_le_mul_left (v.map_add x y) b).trans (by rw [max_mul];exact max_le hx hy)

theorem FVS (v:Valuation L Value) (b:Value) (t:L)
    (Q:Polynomial L) (B:Value) (ht:b≤v t)
    (hP: ∀i,v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i≤B):
    ∀i,v (Q.coeff i)*b^i*v t≤B:=by
  intro i
  induction i with
  | zero=>
    simpa [sub_mul,Polynomial.coeff_sub,Polynomial.coeff_C_mul,map_mul,
      mul_comm] using hP 0
  | succ i ih=>
    have hprev:v (Q.coeff i)*b^(i+1)≤B:=by
      rw [pow_succ,← mul_assoc]
      exact (mul_le_mul_right ht _).trans ih
    have heq:t*Q.coeff (i+1)=Q.coeff i-((Polynomial.X-Polynomial.C t)*Q).coeff (i+1):=by
      simp only [sub_mul,Polynomial.coeff_sub,Polynomial.coeff_X_mul,Polynomial.coeff_C_mul]
      ring
    have hb:=GIN v _ _ _ _ hprev (hP (i+1))
    rw [← heq,map_mul] at hb
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hb

theorem FYS (v:Valuation L Value) (b:Value) (t:L)
    (Q:Polynomial L) (B:Value) (ht:v t≤b)
    (hP: ∀i,v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i≤B):
    ∀i,v (Q.coeff i)*b^i*b≤B:=by
  have hbound: ∀n i:ℕ,Q.natDegree+1≤ i+n→v (Q.coeff i)*b^i*b≤B:=by
    intro n
    induction n with
    | zero=>
      intro i hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),map_zero,zero_mul,zero_mul]
      exact zero_le
    | succ n ih=>
      intro i hi
      have hnext:=ih (i+1) (by omega)
      have hmul:v (t*Q.coeff (i+1))*b^(i+1)≤B:=by
        rw [map_mul]
        have hb:=(mul_le_mul_right ht (v (Q.coeff (i+1))*b^(i+1))).trans hnext
        simpa only [mul_comm,mul_left_comm,mul_assoc] using hb
      have heq:Q.coeff i=((Polynomial.X-Polynomial.C t)*Q).coeff (i+1)+t*Q.coeff (i+1):=by
        simp only [sub_mul,Polynomial.coeff_sub,Polynomial.coeff_X_mul,Polynomial.coeff_C_mul]
        ring
      rw [mul_assoc,← pow_succ,heq]
      exact CWO v _ _ _ _ (hP (i+1)) hmul
  exact fun i=>hbound (Q.natDegree+1) i (by omega)

theorem ELE (v:Valuation L Value) (b:Value) (t:L)
    (Q:Polynomial L) (B:Value)
    (hP: ∀i,v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i≤B):
    ∀i,v (Q.coeff i)*b^i*max b (v t)≤B:=by
  by_cases ht:b≤v t
  · rw [max_eq_right ht]
    exact FVS v b t Q B ht hP
  · rw [max_eq_left (le_of_not_ge ht)]
    exact FYS v b t Q B (le_of_not_ge ht) hP

def ATJ (v:Valuation L Value) (b:Value) (P:Polynomial L):Value:=
  P.support.sup (fun i=>v (P.coeff i)*b^i)

theorem DOE (v:Valuation L Value) (b:Value) (P:Polynomial L) (i:ℕ):
    v (P.coeff i)*b^i≤ATJ v b P:=by
  classical
  by_cases hi:i ∈ P.support
  · exact Finset.le_sup (f:=fun i=>v (P.coeff i)*b^i) hi
  · have hz:P.coeff i=0:=by simpa only [Polynomial.mem_support_iff,not_not] using hi
    rw [hz,map_zero,zero_mul]
    exact zero_le

theorem GBR (v:Valuation L Value) (b:Value) (P:Polynomial L) (B:Value)
    (h: ∀i,v (P.coeff i)*b^i≤B):ATJ v b P≤B:=by
  exact Finset.sup_le (fun i _=>h i)

theorem EBI (v:Valuation L Value) (b:Value) (t:L) (Q:Polynomial L):
    ATJ v b Q*max b (v t)≤ATJ v b ((Polynomial.X-Polynomial.C t)*Q):=by
  classical
  by_cases hQ:Q=0
  · subst Q
    simp [ATJ]
  obtain ⟨i,_,hi⟩:=Finset.exists_mem_eq_sup Q.support
    (Polynomial.support_nonempty.mpr hQ) (fun i=>v (Q.coeff i)*b^i)
  change Q.support.sup (fun i=>v (Q.coeff i)*b^i)*_≤_
  rw [hi]
  exact ELE v b t Q _ (DOE v b _) i

theorem ENY (v:Valuation L Value) (b:Value) (t:L)
    (Q:Polynomial L) (d:ℕ):
    ATJ v b Q*(max b (v t))^d≤
      ATJ v b ((Polynomial.X-Polynomial.C t)^d*Q):=by
  induction d with
  | zero=>simp
  | succ d ih=>
    calc
      ATJ v b Q*(max b (v t))^(d+1)=
          (ATJ v b Q*(max b (v t))^d)*max b (v t):=by rw [pow_succ,mul_assoc]
      _≤ATJ v b ((Polynomial.X-Polynomial.C t)^d*Q)*max b (v t):=
        mul_le_mul_left ih _
      _≤ATJ v b ((Polynomial.X-Polynomial.C t)*((Polynomial.X-Polynomial.C t)^d*Q)):=
        EBI v b t _
      _=ATJ v b ((Polynomial.X-Polynomial.C t)^(d+1)*Q):=by
        rw [pow_succ'];congr 1;ring

theorem EXW (v:Valuation L Value) (b:Value) (t:L)
    (Q:Polynomial L) (d:ℕ) (B:Value)
    (hP: ∀i,v (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*b^i≤B) (i:ℕ):
    v (Q.coeff i)*b^i*(max b (v t))^d≤B:=by
  exact (mul_le_mul_left (DOE v b Q i) _).trans
    ((ENY v b t Q d).trans (GBR v b _ B hP))

end
end ProximityPrize.SubmissionLower.AOU

end Compact_RootMultiplicityWeightedValuation

section Compact_RootMultiplicityWeightedHeight

namespace ProximityPrize.SubmissionLower.BQK
open scoped Classical BigOperators WithZero
open RCN026 RCN187 ALF DNX
open AOU
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L:Type*} [Field L]

theorem log_max_exp (v:Valuation L Value) (t:L) (lambda:ℤ) (hl:0≤lambda):
    (max (WithZero.exp lambda) (v t)).log=max lambda (poleOrder v t):=by
  by_cases ht:v t=0
  · simp [ht,poleOrder,max_eq_left hl]
  by_cases h:WithZero.exp lambda≤v t
  · have hlog:lambda≤(v t).log:=by
      rw [← WithZero.exp_log ht] at h
      exact WithZero.exp_le_exp.mp h
    rw [max_eq_right h]
    simp only [poleOrder,max_eq_right (hl.trans hlog),max_eq_right hlog]
  · have hv:v t≤WithZero.exp lambda:=le_of_not_ge h
    have hlog:=(WithZero.log_le_iff_le_exp ht).mpr hv
    rw [max_eq_left hv]
    simp only [WithZero.log_exp,poleOrder,max_eq_left (max_le hl hlog)]

theorem ENW (v:Valuation L Value) (P:Polynomial L)
    (B lambda:ℤ)
    (hP: ∀i,v (P.coeff i)≤WithZero.exp (B-(i:ℤ)*lambda)):
    ∀i,v (P.coeff i)*(WithZero.exp lambda)^i≤WithZero.exp B:=by
  intro i
  calc
    v (P.coeff i)*(WithZero.exp lambda)^i≤
        WithZero.exp (B-(i:ℤ)*lambda)*(WithZero.exp lambda)^i:=
      mul_le_mul_left (hP i) _
    _=WithZero.exp B:=by
      rw [← WithZero.exp_nsmul,← WithZero.exp_add]
      simp

theorem EFN (v:Valuation L Value) (t:L)
    (Q:Polynomial L) (d:ℕ) (B lambda:ℤ) (hl:0≤lambda)
    (hP: ∀i,v (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*
      (WithZero.exp lambda)^i≤WithZero.exp B)
    (i:ℕ) (hi:Q.coeff i ≠ 0):
    (v (Q.coeff i)).log+(i:ℤ)*lambda+
      (d:ℤ)*max lambda (poleOrder v t)≤B:=by
  have hv:v (Q.coeff i) ≠ 0:=v.ne_zero_iff.mpr hi
  have hb:(WithZero.exp lambda:Value) ≠ 0:=WithZero.exp_ne_zero
  have ht:max (WithZero.exp lambda) (v t) ≠ 0:=by
    intro h
    have hle:=le_max_left (WithZero.exp lambda) (v t)
    rw [h] at hle
    exact hb (le_antisymm hle zero_le)
  have hh:=(WithZero.log_le_iff_le_exp
    (mul_ne_zero (mul_ne_zero hv (pow_ne_zero i hb)) (pow_ne_zero d ht))).mpr
    (AOU.EXW
      v (WithZero.exp lambda) t Q d (WithZero.exp B) hP i)
  simpa only [WithZero.log_mul (mul_ne_zero hv (pow_ne_zero i hb)) (pow_ne_zero d ht),
    WithZero.log_mul hv (pow_ne_zero i hb),WithZero.log_pow,WithZero.log_exp,
    nsmul_eq_mul,log_max_exp v t lambda hl] using hh

theorem EQA {ι:Type*} (W:Finset ι)
    (v:ι→Valuation L Value) (t:L) (Q:Polynomial L) (d:ℕ)
    (B lambda:ι→ℤ) (hl: ∀w ∈ W,0≤lambda w)
    (hP: ∀w ∈ W,∀i,v w (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*
      (WithZero.exp (lambda w))^i≤WithZero.exp (B w))
    (i:ℕ) (hi:Q.coeff i ≠ 0)
    (hbalance:(∑ w ∈ W,(v w (Q.coeff i)).log)=0):
    (i:ℤ)*(∑ w ∈ W,lambda w)+
      (d:ℤ)*(∑ w ∈ W,max (lambda w) (poleOrder (v w) t))≤ ∑ w ∈ W,B w:=by
  have hsum:=Finset.sum_le_sum (fun w hw=>
    EFN (v w) t Q d (B w) (lambda w) (hl w hw) (hP w hw) i hi)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,hbalance,zero_add] using hsum

section FunctionField
variable (K:Type*) [Field K] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem FIX (P:Polynomial L) (hP:P ≠ 0) (t:L) (d:ℕ)
    (hd:(Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta:Place K L→ℤ) (C:ℤ)
    (ha: ∀v,0≤alpha v) (hba: ∀v,beta v≤alpha v)
    (hcoeff: ∀v (i:ℕ),v.val (P.coeff i)≤
      WithZero.exp (B v-(i:ℤ)*(2*alpha v-beta v)))
    (hbudget: ∀V:Finset (Place K L),
      (∑ v ∈ V,(B v+(d:ℤ)*beta v-
        ((P.natDegree-d:ℕ):ℤ)*(2*alpha v-beta v)))≤C)
    (W:Finset (Place K L)):
    (d:ℤ)*(∑ v ∈ W,max (2*alpha v) (beta v+poleOrder v.val t))≤C:=by
  obtain ⟨Q,rfl⟩:=hd
  have hQ:Q ≠ 0:=right_ne_zero_of_mul hP
  have hf:(Polynomial.X-Polynomial.C t)^d ≠ 0:=left_ne_zero_of_mul hP
  have hi:Q.coeff Q.natDegree ≠ 0:=Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hdeg:((Polynomial.X-Polynomial.C t)^d*Q).natDegree-d=Q.natDegree:=by
    rw [Polynomial.natDegree_mul hf hQ,Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C]
    omega
  simp only [hdeg] at hbudget
  let V:=W ∪ placesFor K L (Q.coeff Q.natDegree) hi
  have hbalance:=EPP K L (Q.coeff Q.natDegree) hi V
    Finset.subset_union_right
  have hl: ∀v,0≤2*alpha v-beta v:=by intro v;have:=ha v;have:=hba v;omega
  have hh:=EQA V (fun v=>v.val) t Q d B
    (fun v=>2*alpha v-beta v) (fun v _=>hl v)
    (fun v _=>ENW v.val _ _ _ (hcoeff v)) Q.natDegree hi hbalance
  have heq (v:Place K L):
      max (2*alpha v) (beta v+poleOrder v.val t)=
        beta v+max (2*alpha v-beta v) (poleOrder v.val t):=by omega
  have hbound:(d:ℤ)*(∑ v ∈ V,max (2*alpha v) (beta v+poleOrder v.val t))≤C:=by
    have hbud:=hbudget V
    simp_rw [heq]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hbud ⊢
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at hh
    nlinarith
  apply le_trans _ hbound
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg d)
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
  intro v _ _
  exact (by have:=ha v;omega:0≤2*alpha v).trans (le_max_left _ _)

theorem DWF (P:Polynomial L) (hP:P ≠ 0)
    (t:L) (d n0:ℕ) (hn:n0≤P.natDegree)
    (hd:(Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta:Place K L→ℤ) (C:ℤ)
    (ha: ∀v,0≤alpha v) (hba: ∀v,beta v≤alpha v)
    (hcoeff: ∀v (i:ℕ),v.val (P.coeff i)≤
      WithZero.exp (B v-(i:ℤ)*(2*alpha v-beta v)))
    (hbudget: ∀V:Finset (Place K L),
      (∑ v ∈ V,(B v+(d:ℤ)*beta v-
        ((n0-d:ℕ):ℤ)*(2*alpha v-beta v)))≤C)
    (W:Finset (Place K L)):
    (d:ℤ)*(∑ v ∈ W,max (2*alpha v) (beta v+poleOrder v.val t))≤C:=by
  apply FIX K P hP t d hd B alpha beta C ha hba hcoeff _ W
  intro V
  apply le_trans _ (hbudget V)
  apply Finset.sum_le_sum
  intro v _
  have hl:0≤2*alpha v-beta v:=by have:=ha v;have:=hba v;omega
  have hsub:((n0-d:ℕ):ℤ)≤((P.natDegree-d:ℕ):ℤ):=by
    exact_mod_cast Nat.sub_le_sub_right hn d
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hsub hl) _

end FunctionField
end
end ProximityPrize.SubmissionLower.BQK

end Compact_RootMultiplicityWeightedHeight

section Compact_SecondJetRelaxedFlag

namespace ProximityPrize.SubmissionLower.EJ
open scoped BigOperators WithZero
open ProximityPrize.SubmissionLower.ALF
open MvPolynomial RCN095 RCN026 RCN187 RCN204
open BX DX AUS
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K L:Type*} [Field K] [Field L]

def LJ (B U T j:ℕ):FlagDegree:=⟨T-U,U-B+j,B-2*j⟩

def budgetFlag (B U T d n0:ℕ):FlagDegree:=⟨T-U,U-B+n0,B-2*(n0-d)⟩

theorem ENB (P:Poly (K:=K)) (B U T:ℕ)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (j:ℕ) (e:Fin 4→₀ ℕ) (he:e ∈ ((asS (K:=K) P).coeff j).support):
    2*j+e 2≤B∧j+e 1+e 2≤U∧j+e 1+e 2+e 3≤T:=by
  have hh:=hP _ (AJU P j e he)
  obtain ⟨h0,h1,h2,h3,h4⟩:=_Q17 j e
  rwa [h1,h2,h3,h4] at hh

theorem ESJ (P:Poly (K:=K)) (x:K) (B U T:ℕ)
    (hBU:B≤U) (hUT:U≤T)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T) (j:ℕ):
    BI (LJ B U T j) (freeze x ((asS (K:=K) P).coeff j)):=by
  apply GVR
  intro e he
  have hb:=ENB P B U T hP j e he
  change e 2≤B-2*j∧e 1+e 2≤U-B+j+(B-2*j)∧
    e 1+e 2+e 3≤T-U+(U-B+j)+(B-2*j)
  omega

theorem FAM (v:Valuation L Value) (x:Fin 3→L)
    (B U T j:ℕ) (hj:2*j≤B):
    flagPole v x (LJ B U T j)=
      flagPole v x (LJ B U T 0)-
        (j:ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag):=by
  simp only [flagPole,LJ,unitAllFlag,unitYZFlag,Nat.mul_zero,Nat.sub_zero,Nat.add_zero]
  rw [Nat.cast_sub hj]
  push_cast
  ring

theorem GAF (v:Valuation L Value) (x:Fin 3→L)
    (B U T d n0:ℕ) (hd:d≤n0) (hB:2*(n0-d)≤B):
    flagPole v x (budgetFlag B U T d n0)=
      flagPole v x (LJ B U T 0)+(d:ℤ)*flagPole v x unitYZFlag-
        ((n0-d:ℕ):ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag):=by
  simp only [flagPole,budgetFlag,LJ,unitAllFlag,unitYZFlag,Nat.mul_zero,Nat.sub_zero,Nat.add_zero]
  simp only [Nat.cast_sub hB,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hd,Nat.cast_add]
  ring

theorem DYT (P:Poly (K:=K)) (freezeX:K)
    (B U T:ℕ) (hBU:B≤U) (hUT:U≤T)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (v:Valuation L Value) (coeff:K→+*L) (hc: ∀c,v (coeff c)≤1)
    (x:Fin 3→L) (j:ℕ):
    v (MvPolynomial.eval₂Hom coeff x (freeze freezeX ((asS (K:=K) P).coeff j)))≤
      WithZero.exp (flagPole v x (LJ B U T 0)-
        (j:ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag)):=by
  by_cases hz:(asS (K:=K) P).coeff j=0
  · simp only [hz,map_zero]
    exact zero_le
  have hs:((asS (K:=K) P).coeff j).support.Nonempty:=
    MvPolynomial.support_nonempty.mpr hz
  obtain ⟨e,he⟩:=hs
  have hj:2*j≤B:=by have:=ENB P B U T hP j e he;omega
  rw [← FAM v x B U T j hj]
  exact ADJ v coeff hc x (LJ B U T j) _
    (ESJ P freezeX B U T hBU hUT hP j)

section FunctionField
variable [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem moving_bound (P:Poly (K:=K)) (freezeX:K) (B U T d n0:ℕ)
    (hBU:B≤U) (hUT:U≤T) (hdn:d≤n0) (hB:2*(n0-d)≤B)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (x:Fin 3→L) (Q:Polynomial L)
    (hQcoeff: ∀j,Q.coeff j=MvPolynomial.eval₂Hom (algebraMap K L) x
      (freeze freezeX ((asS (K:=K) P).coeff j)))
    (hQ:Q ≠ 0) (hn:n0≤Q.natDegree) (t:L)
    (hd:(Polynomial.X-Polynomial.C t)^d ∣ Q) (C:ℤ)
    (hbudget: ∀V:Finset (Place K L),
      (∑ v ∈ V,flagPole v.val x (budgetFlag B U T d n0))≤C)
    (V:Finset (Place K L)):
    (d:ℤ)*(∑ v ∈ V,max (2*flagPole v.val x unitAllFlag)
      (flagPole v.val x unitYZFlag+poleOrder v.val t))≤C:=by
  apply BQK.DWF K Q hQ t d n0 hn hd
    (fun v=>flagPole v.val x (LJ B U T 0))
    (fun v=>flagPole v.val x unitAllFlag) (fun v=>flagPole v.val x unitYZFlag) C
    (fun v=>ALZ v.val x unitAllFlag) ?_ ?_ ?_ V
  · intro v
    rw [CWP,BPD]
    exact le_max_right _ _
  · intro v j
    rw [hQcoeff j]
    exact DYT P freezeX B U T hBU hUT hP v.val
      (algebraMap K L) (RCN344.NP K L v) x j
  · intro W
    convert hbudget W using 1
    apply Finset.sum_congr rfl
    intro v _
    exact (GAF v.val x B U T d n0 hdn hB).symm

end FunctionField

end
end ProximityPrize.SubmissionLower.EJ

end Compact_SecondJetRelaxedFlag

section Compact_SecondJetSurfaceMap

namespace ProximityPrize.SubmissionLower.BZJ
open MvPolynomial DX BX AUS
open RCN136
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K E:Type*} [Field K] [Field E]

theorem GHR (f:K→+*E) (P:Poly (K:=K)) (j:ℕ):
    (asS (MvPolynomial.map f P)).coeff j=MvPolynomial.map f ((asS P).coeff j):=by
  ext e
  rw [asS_coeff,MvPolynomial.coeff_map,MvPolynomial.coeff_map,asS_coeff]

theorem FBD (φ:Polynomial K→+*E) (P:MvPolynomial (Fin 4) K):
    freeze (φ Polynomial.X) (MvPolynomial.map (φ.comp Polynomial.C) P)=surfaceMap φ P:=by
  induction P using MvPolynomial.induction_on with
  | C c=>simp [freeze]
  | add P Q hp hq=>simp only [map_add,hp,hq]
  | mul_X P i hp=>
    simp only [map_mul,hp,MvPolynomial.map_X]
    congr 1
    refine Fin.cases ?_ (fun j=> ?_) i
    · simp [freeze]
    · rw [AMP]
      fin_cases j<;>simp [freeze]

theorem ELF (φ:Polynomial K→+*E) (P:Poly (K:=K)) (j:ℕ):
    freeze (φ Polynomial.X) ((asS (MvPolynomial.map (φ.comp Polynomial.C) P)).coeff j)=
      surfaceMap φ ((asS P).coeff j):=by
  rw [GHR,FBD]

theorem DVE (f:K→+*E) (P:Poly (K:=K)) (B U T:ℕ)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T):
    ∀e ∈ (MvPolynomial.map f P).support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T:=by
  intro e he
  exact hP e (MvPolynomial.support_map_subset f P he)

end
end ProximityPrize.SubmissionLower.BZJ

end Compact_SecondJetSurfaceMap

section Compact_SecondJetCoefficientSpecialization

namespace ProximityPrize.SubmissionLower.JQ
open MvPolynomial DX BX HH
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

theorem lift_succ (j:ℕ) (d:Fin 4→₀ ℕ):
    liftExponent (j+1) d=liftExponent j d+Finsupp.single 1 1:=by
  ext i
  obtain ⟨h0,h1,h2,h3,h4⟩:=_Q17 j d
  obtain ⟨g0,g1,g2,g3,g4⟩:=_Q17 (j+1) d
  fin_cases i<;>simp [Finsupp.add_apply,Finsupp.single_apply,h0,h1,h2,h3,h4,g0,g1,g2,g3,g4]

theorem asS_pderiv (P:Poly (K:=K)):
    asS (pderiv 1 P)=(asS P).derivative:=by
  ext j d
  rw [asS_coeff,MvPolynomial.coeff_pderiv,Polynomial.coeff_derivative]
  rw [show ((j:MvPolynomial (Fin 4) K)+1)=MvPolynomial.C (j+1:K) by simp,
    mul_comm ((asS P).coeff (j+1)) (MvPolynomial.C (j+1:K)),
    MvPolynomial.coeff_C_mul,asS_coeff]
  rw [← lift_succ,(_Q17 j d).2.1]
  simp [mul_comm]

theorem asS_iterate (P:Poly (K:=K)) (d:ℕ):
    asS ((pderiv 1)^[d] P)=(Polynomial.derivative)^[d] (asS P):=by
  induction d with
  | zero=>rfl
  | succ d ih=>rw [Function.iterate_succ_apply',Function.iterate_succ_apply',asS_pderiv,ih]

def FL (f:Polynomial K) (z:K):
    MvPolynomial (Fin 4) K→ₐ[K] Polynomial K:=
  MvPolynomial.aeval ![Polynomial.X,f,f.derivative,Polynomial.C z]

def evaluateS (f:Polynomial K) (z:K):
    Polynomial (MvPolynomial (Fin 4) K)→ₐ[K] Polynomial K:=
  {Polynomial.eval₂RingHom (FL f z).toRingHom (Polynomial.hasseDeriv 2 f) with
    commutes' :=by intro c;simp [FL]}

theorem FAP (P:Poly (K:=K)) (f:Polynomial K) (z:K):
    specialize f z P=(asS P).eval₂ (FL f z).toRingHom
      (Polynomial.hasseDeriv 2 f):=by
  have heq:specialize f z=(evaluateS f z).comp (asS (K:=K)).toAlgHom:=by
    apply MvPolynomial.algHom_ext
    intro i
    have h1 (A:Polynomial (MvPolynomial (Fin 4) K)) (g:Fin 4→Polynomial (MvPolynomial (Fin 4) K)):
        Fin.cases A g (1:Fin 5)=g 0:=rfl
    have h2 (A:Polynomial (MvPolynomial (Fin 4) K)) (g:Fin 4→Polynomial (MvPolynomial (Fin 4) K)):
        Fin.cases A g (2:Fin 5)=g 1:=rfl
    have h3 (A:Polynomial (MvPolynomial (Fin 4) K)) (g:Fin 4→Polynomial (MvPolynomial (Fin 4) K)):
        Fin.cases A g (3:Fin 5)=g 2:=rfl
    have h4 (A:Polynomial (MvPolynomial (Fin 4) K)) (g:Fin 4→Polynomial (MvPolynomial (Fin 4) K)):
        Fin.cases A g (4:Fin 5)=g 3:=rfl
    fin_cases i<;>simp [specialize,asS,FL,evaluateS,
      Equiv.swap_apply_def,MvPolynomial.finSuccEquiv_apply,h1,h2,h3,h4]
  exact DFunLike.congr_fun heq P

end
end ProximityPrize.SubmissionLower.JQ

end Compact_SecondJetCoefficientSpecialization

section Compact_SecondJetClearedHelper

namespace ProximityPrize.SubmissionLower.FR
open scoped BigOperators
open MvPolynomial DX BX HH
open JQ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]

def cleared {R:Type*} [CommRing R] (P:Polynomial R) (n:ℕ) (H G:R):R:=
  ∑ j:Fin (n+1),P.coeff j.val*H^(n-j.val)*G^j.val

theorem map_cleared {R T:Type*} [CommRing R] [CommRing T] (φ:R→+*T)
    (P:Polynomial R) (n:ℕ) (H G:R):
    φ (cleared P n H G)=cleared (P.map φ) n (φ H) (φ G):=by
  simp [cleared,Polynomial.coeff_map]

theorem cleared_eval {R:Type*} [CommRing R] (P:Polynomial R) (n:ℕ)
    (hn:P.natDegree≤n) (H G t:R) (hrel:H*t=G):
    cleared P n H G=H^n*P.eval t:=by
  rw [Polynomial.eval_eq_sum_range' (by omega:P.natDegree<n+1)]
  rw [← Fin.sum_univ_eq_sum_range (fun j:ℕ=>P.coeff j*t^j)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hrel,mul_pow]
  have hh:H^(n-j.val)*H^j.val=H^n:=by rw [← pow_add,Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)]
  calc
    _=P.coeff j.val*(H^(n-j.val)*H^j.val)*t^j.val:=by ring
    _=_:=by rw [hh];ring

theorem ENM (f:Polynomial K) (z:K):
    (FL f z).toRingHom=RCN319.BM K f z:=by
  rfl

theorem hasse_two (f:Polynomial K):
    (2:Polynomial K)*Polynomial.hasseDeriv 2 f=f.derivative.derivative:=by
  have hh:=congrFun (Polynomial.factorial_smul_hasseDeriv (R:=K) (k:=2)) f
  simpa [Function.iterate_succ_apply',nsmul_eq_mul] using hh

def helper (P:Poly (K:=K)) (F:MvPolynomial (Fin 4) K) (n d:ℕ):
    MvPolynomial (Fin 4) K:=
  cleared (asS ((pderiv 1)^[d] P)) n (2*RCN313.polyH K F) (RCN313.polyG K F)

theorem FAI (P:Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (n d:ℕ) (hn:(asS ((pderiv 1)^[d] P)).natDegree≤n)
    (f:Polynomial K) (z:K)
    (hF:RCN319.BM K f z F=0)
    (hP:specialize f z ((pderiv 1)^[d] P)=0):
    RCN319.BM K f z (helper P F n d)=0:=by
  have hrel:RCN319.BM K f z (2*RCN313.polyH K F)*Polynomial.hasseDeriv 2 f=
      RCN319.BM K f z (RCN313.polyG K F):=by
    rw [map_mul,map_ofNat]
    calc
      _=RCN319.BM K f z (RCN313.polyH K F)*
          ((2:Polynomial K)*Polynomial.hasseDeriv 2 f):=by ring
      _=_:=by rw [hasse_two];exact RCN231.DJZ K F f z hF
  change (RCN319.BM K f z).toRingHom
    (cleared (asS ((pderiv 1)^[d] P)) n (2*RCN313.polyH K F) (RCN313.polyG K F))=0
  rw [map_cleared]
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe]
  rw [cleared_eval _ n (Polynomial.natDegree_map_le.trans hn) _ _ _ hrel]
  have hv:((asS ((pderiv 1)^[d] P)).map (RCN319.BM K f z)).eval
      (Polynomial.hasseDeriv 2 f)=0:=by
    rw [Polynomial.eval_map,← ENM,← FAP]
    exact hP
  rw [hv,mul_zero]

end
end ProximityPrize.SubmissionLower.FR

end Compact_SecondJetClearedHelper

section Compact_SecondJetHelperWeights

namespace ProximityPrize.SubmissionLower.OR
open scoped BigOperators
open MvPolynomial DX BX JQ
open FR RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]

theorem DUV (P:Poly (K:=K)) (B U L d j:ℕ)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤L)
    (e:Fin 4→₀ ℕ) (he:e ∈ ((asS ((pderiv 1)^[d] P)).coeff j).support):
    2*(j+d)+e 2≤B∧j+d+e 1+e 2≤U∧j+d+e 1+e 2+e 3≤L:=by
  have hb:=hP _ (KL.CAJ P d _
    (AJU ((pderiv 1)^[d] P) j e he))
  obtain ⟨h0,h1,h2,h3,h4⟩:=_Q17 j e
  simpa [Finsupp.add_apply,Finsupp.single_apply,h0,h1,h2,h3,h4] using hb

theorem OE (P:Poly (K:=K)) (B U L d j:ℕ)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤L):
    wt BE ((asS ((pderiv 1)^[d] P)).coeff j)≤B-2*d-2*j∧
    wt BC ((asS ((pderiv 1)^[d] P)).coeff j)≤U-d-j∧
    wt AT ((asS ((pderiv 1)^[d] P)).coeff j)≤L-d-j:=by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply (RCN081.KN _ _ _).mpr
    intro e he
    have hb:=DUV P B U L d j hP e he
  · simp [BE,RCN081.weight_fin4]
    omega
  · simp [BC,RCN081.weight_fin4]
    omega
  · simp [AT,RCN081.weight_fin4]
    omega

theorem AFG (P:Poly (K:=K)) (s d:ℕ)
    (hP: ∀e ∈ P.support,e 1≤s):
    (asS ((pderiv 1)^[d] P)).natDegree≤s-d:=by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hn
  obtain ⟨e,he⟩:=MvPolynomial.support_nonempty.mpr hn
  have hb:=hP _ (KL.CAJ P d _
    (AJU ((pderiv 1)^[d] P) j e he))
  have h1:=(_Q17 j e).2.1
  simp [Finsupp.add_apply,Finsupp.single_apply,h1] at hb
  omega

theorem BUF (weights:Fin 4→ℕ) (P:Polynomial (MvPolynomial (Fin 4) K))
    (n C slope Hcap:ℕ) (H G:MvPolynomial (Fin 4) K)
    (hC:slope*n≤C)
    (hP: ∀j:Fin (n+1),wt weights (P.coeff j.val)≤C-slope*j.val)
    (hH:wt weights H≤Hcap) (hG:wt weights G≤Hcap+slope):
    wt weights (cleared P n H G)≤C+n*Hcap:=by
  unfold cleared
  apply RCN235.CLG
  intro j _
  have hj:=j.isLt
  have hp:=hP j
  have hh:=(wt_pow_le weights H (n-j.val)).trans (Nat.mul_le_mul_left _ hH)
  have hg:=(wt_pow_le weights G j.val).trans (Nat.mul_le_mul_left _ hG)
  have ht:=(wt_mul_le weights (P.coeff j.val*H^(n-j.val)) (G^j.val)).trans
    (Nat.add_le_add ((wt_mul_le weights (P.coeff j.val) (H^(n-j.val))).trans
      (Nat.add_le_add hp hh)) hg)
  have hjn:j.val≤n:=by omega
  have hjC:slope*j.val≤C:=(Nat.mul_le_mul_left slope hjn).trans hC
  have hc:C-slope*j.val+slope*j.val=C:=Nat.sub_add_cancel hjC
  have hn:n-j.val+j.val=n:=Nat.sub_add_cancel hjn
  nlinarith

theorem EUI (P:Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (B U L s d capT capY capR:ℕ) (hsB:2*s≤B) (hsU:s≤U) (hsL:s≤L)
    (hd:d≤s) (hR:1≤capR) (hY:1≤capY) (hT:1≤capT)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤L)
    (hF:wt BE F≤capR∧wt BC F≤capY∧
      wt AT F≤capT):
    wt BE (helper P F (s-d) d)≤B-2*d+(s-d)*(capR-1)∧
    wt BC (helper P F (s-d) d)≤U-d+(s-d)*(capY-1)∧
    wt AT (helper P F (s-d) d)≤L-d+(s-d)*(capT-1):=by
  have hw (weights:Fin 4→ℕ) (cap:ℕ) (hR1:weights 2=1)
      (hFcap:wt weights F≤cap):wt weights (2*RCN313.polyH K F)≤cap-1:=by
    have hh:=wt_polyH_le weights F cap hFcap
    have hm:=wt_mul_le weights (2:MvPolynomial (Fin 4) K) (RCN313.polyH K F)
    have hc:wt weights (2:MvPolynomial (Fin 4) K)=0:=wt_natCast weights 2
    rw [hR1] at hh
    omega
  refine ⟨?_,?_,?_⟩
  · apply BUF BE _ (s-d) (B-2*d) 2 (capR-1) _ _ (by omega)
      (fun j=>(OE P B U L d j.val hP).1)
      (hw _ capR rfl hF.1)
    have hg:=wt_polyG_le BE rfl F capR hF.1
    change wt BE (RCN313.polyG K F)≤capR-1+2
    change wt BE (RCN313.polyG K F)≤capR+1 at hg
    omega
  · apply BUF BC _ (s-d) (U-d) 1 (capY-1) _ _ (by omega)
      (fun j=>by simpa using (OE P B U L d j.val hP).2.1)
      (hw _ capY rfl hF.2.1)
    have hg:=RCN179.COF BC rfl F capY (by decide) hY hF.2.1
    omega
  · apply BUF AT _ (s-d) (L-d) 1 (capT-1) _ _ (by omega)
      (fun j=>by simpa using (OE P B U L d j.val hP).2.2)
      (hw _ capT rfl hF.2.2)
    have hg:=RCN179.COF AT rfl F capT (by decide) hT hF.2.2
    omega

end
end ProximityPrize.SubmissionLower.OR

end Compact_SecondJetHelperWeights

section Compact_RootMultiplicityDichotomy

namespace ProximityPrize.SubmissionLower.BMM
noncomputable section
set_option autoImplicit false
variable {L:Type*} [Field L]

theorem BOS (P:Polynomial L) (hP:P ≠ 0)
    (t:L) (k:ℕ) (hk:(k.factorial:L) ≠ 0):
    (∃d≤k,((Polynomial.derivative)^[d] P).eval t ≠ 0)∨
      (Polynomial.X-Polynomial.C t)^(k+1) ∣ P:=by
  classical
  rcases Classical.em (∀d≤k,((Polynomial.derivative)^[d] P).eval t=0) with hroot | hroot
  · right
    have hm:=Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
      hP hroot (mem_nonZeroDivisors_iff_ne_zero.mpr hk)
    exact (pow_dvd_pow (Polynomial.X-Polynomial.C t) hm).trans (P.pow_rootMultiplicity_dvd t)
  · left
    push_neg at hroot
    exact hroot

end
end ProximityPrize.SubmissionLower.BMM

end Compact_RootMultiplicityDichotomy

section Compact_SecondJetCarrierDichotomy

namespace ProximityPrize.SubmissionLower.DP
open MvPolynomial DX BX
open JQ FR OR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K E:Type*} [Field K] [Field E]

def ratio (φ:MvPolynomial (Fin 4) K→+*E) (F:MvPolynomial (Fin 4) K):E:=
  φ (RCN313.polyG K F)/φ (2*RCN313.polyH K F)

theorem CNM (P:Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (φ:MvPolynomial (Fin 4) K→+*E) (s d:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s) (hH:φ (2*RCN313.polyH K F) ≠ 0):
    φ (helper P F (s-d) d)=φ (2*RCN313.polyH K F)^(s-d)*
      ((Polynomial.derivative)^[d] ((asS P).map φ)).eval (ratio φ F):=by
  rw [helper,map_cleared]
  have hdegree:((asS ((pderiv 1)^[d] P)).map φ).natDegree≤s-d:=
    Polynomial.natDegree_map_le.trans (AFG P s d hS)
  have hrel:φ (2*RCN313.polyH K F)*ratio φ F=φ (RCN313.polyG K F):=by
    unfold ratio
    field_simp
  rw [cleared_eval _ (s-d) hdegree _ _ _ hrel,asS_iterate,← Polynomial.iterate_derivative_map]

theorem EXM (P:Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (φ:MvPolynomial (Fin 4) K→+*E) (s k:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s) (hF:φ F=0)
    (hH:φ (2*RCN313.polyH K F) ≠ 0)
    (hP:(asS P).map φ ≠ 0) (hk:(k.factorial:E) ≠ 0):
    (∃d≤k,¬F ∣ helper P F (s-d) d)∨
      (Polynomial.X-Polynomial.C (ratio φ F))^(k+1) ∣ (asS P).map φ:=by
  rcases BMM.BOS
    ((asS P).map φ) hP (ratio φ F) k hk with hder | hroot
  · left
    obtain ⟨d,hd,hne⟩:=hder
    refine ⟨d,hd,?_⟩
    intro hdiv
    have hh:=map_dvd φ hdiv
    rw [hF,zero_dvd_iff,CNM P F φ s d hS hH] at hh
    exact (mul_ne_zero (pow_ne_zero _ hH) hne) hh
  · exact Or.inr hroot

theorem BEQ (P:Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (φ:MvPolynomial (Fin 4) K→+*E) (s k:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s) (hF:φ F=0)
    (hH:φ (2*RCN313.polyH K F) ≠ 0)
    (hP:(asS P).map φ ≠ 0) (hk:(k.factorial:E) ≠ 0)
    (hdiv: ∀d≤k,F ∣ helper P F (s-d) d):
    (Polynomial.X-Polynomial.C (ratio φ F))^(k+1) ∣ (asS P).map φ:=by
  rcases EXM P F φ s k hS hF hH hP hk with h | h
  · obtain ⟨d,hd,hn⟩:=h
    exact False.elim (hn (hdiv d hd))
  · exact h

end
end ProximityPrize.SubmissionLower.DP

end Compact_SecondJetCarrierDichotomy

section Compact_SecondJetCoefficientAvoidance

namespace ProximityPrize.SubmissionLower.AYT
open MvPolynomial DX BX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K:Type*} [Field K]

theorem EAF {R T:Type*} [CommRing R] [CommRing T]
    (P:Polynomial R) (φ:R→+*T) (hC:φ P.leadingCoeff ≠ 0):
    P.map φ ≠ 0∧(P.map φ).natDegree=P.natDegree:=by
  constructor
  · intro hz
    have hh:=congrArg (fun Q:Polynomial T=>Q.coeff P.natDegree) hz
    simp only [Polynomial.coeff_map,Polynomial.coeff_zero,Polynomial.coeff_natDegree] at hh
    exact hC hh
  · exact Polynomial.natDegree_map_eq_iff.mpr (Or.inl hC)

end
end ProximityPrize.SubmissionLower.AYT

end Compact_SecondJetCoefficientAvoidance

section Compact_SecondJetComponentRoots

namespace ProximityPrize.SubmissionLower.CT
open MvPolynomial DX BX FR
open RCN002 RCN136
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K E:Type} [Field K] [Field E]

def GP (φ:Polynomial K→+*E) (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]:
    MvPolynomial (Fin 4) K→+*AJ E C:=
  (BR E C).toRingHom.comp (surfaceMap φ)

def AGC (φ:Polynomial K→+*E) (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P:Poly (K:=K)):Polynomial (AJ E C):=
  (asS P).map (GP φ C)

theorem AAE (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (Q:MvPolynomial (Fin 3) E):BR E C Q=0 ↔ Q ∈ C:=by
  change Q ∈ RingHom.ker (BR E C).toRingHom ↔ Q ∈ C
  rw [FB]

theorem ELO (φ:Polynomial K→+*E) (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P:Poly (K:=K)) (hlead:surfaceMap φ (asS P).leadingCoeff ∉ C):
    AGC φ C P ≠ 0∧(AGC φ C P).natDegree=(asS P).natDegree:=by
  apply AYT.EAF
  change BR E C (surfaceMap φ (asS P).leadingCoeff) ≠ 0
  exact fun hz=>hlead ((AAE C _).mp hz)

theorem coefficients (φ:Polynomial K→+*E) (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P:Poly (K:=K)) (j:ℕ):
    (AGC φ C P).coeff j=
      MvPolynomial.eval₂Hom (algebraMap E (AJ E C)) (coordinate E C)
        (AUS.freeze (φ Polynomial.X)
          ((asS (MvPolynomial.map (φ.comp Polynomial.C) P)).coeff j)):=by
  rw [BZJ.ELF]
  rw [AGC,Polynomial.coeff_map]
  change BR E C _=_
  rw [HJ]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _)

theorem FKC (φ:Polynomial K→+*E) (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P:Poly (K:=K)) (F:MvPolynomial (Fin 4) K) (s k:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hF:surfaceMap φ F ∈ C) (hH:surfaceMap φ (RCN313.polyH K F) ∉ C)
    (hlead:surfaceMap φ (asS P).leadingCoeff ∉ C)
    (hdiv: ∀d≤k,F ∣ helper P F (s-d) d)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0):
    (Polynomial.X-Polynomial.C (RCN064.movingRatio C
      (surfaceMap φ (RCN313.polyH K F)) (surfaceMap φ (RCN313.polyG K F))/2))^(k+1) ∣
      AGC φ C P:=by
  have hf:GP φ C F=0:=(AAE C _).mpr hF
  have hh:BR E C (surfaceMap φ (RCN313.polyH K F)) ≠ 0:=
    fun hz=>hH ((AAE C _).mp hz)
  have h2e:(2:AJ E C) ≠ 0:=by
    simpa only [map_ofNat,map_zero] using (algebraMap E (AJ E C)).injective.ne h2
  have hfe:(k.factorial:AJ E C) ≠ 0:=by
    simpa only [map_natCast,map_zero] using (algebraMap E (AJ E C)).injective.ne hfact
  have hden:GP φ C (2*RCN313.polyH K F) ≠ 0:=by
    rw [map_mul,map_ofNat]
    exact mul_ne_zero h2e hh
  have hr:=DP.BEQ P F (GP φ C)
    s k hS hf hden (ELO φ C P hlead).1 hfe hdiv
  have heq:DP.ratio (GP φ C) F=
      RCN064.movingRatio C (surfaceMap φ (RCN313.polyH K F))
        (surfaceMap φ (RCN313.polyG K F))/2:=by
    simp only [DP.ratio,GP,RingHom.comp_apply,
      RCN064.movingRatio,map_mul,map_ofNat,AlgHom.toRingHom_eq_coe,RingHom.coe_coe]
    field_simp
    <;>ring
  rwa [heq] at hr

end
end ProximityPrize.SubmissionLower.CT

end Compact_SecondJetComponentRoots

section Compact_SecondJetMovingDegree

namespace ProximityPrize.SubmissionLower.FAB
open scoped BigOperators
open RCN026 RCN095 RCN187 RCN204 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable (K L:Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]

variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

end
end ProximityPrize.SubmissionLower.FAB

end Compact_SecondJetMovingDegree

section Compact_SecondJetPoleScaling

namespace ProximityPrize.SubmissionLower.CWV
open RCN026 RCN187
noncomputable section
set_option autoImplicit false
variable {K E:Type*} [Field K] [Field E] [Algebra K E]

theorem FSB (v:Place K E) (a:K) (ha:a ≠ 0) (x:E):
    poleOrder v.val (x/algebraMap K E a)=poleOrder v.val x:=by
  letI:v.val.IsTrivialOn K:=v.property.2
  have hc:v.val (algebraMap K E a)=1:=Valuation.IsTrivialOn.eq_one a ha
  simp only [poleOrder,Valuation.map_div,hc,div_one]

theorem pole_half (v:Place K E) (h2:(2:K) ≠ 0) (x:E):
    poleOrder v.val (x/2)=poleOrder v.val x:=by
  simpa only [map_ofNat] using FSB v 2 h2 x

end
end ProximityPrize.SubmissionLower.CWV

end Compact_SecondJetPoleScaling

section Compact_SecondJetActiveMovingBudget

namespace ProximityPrize.SubmissionLower.EBG
open scoped BigOperators
open RCN005 RCN006 RCN064 RCN002 RCN095 RCN187 RCN204 RCN207 RCN264 RCN341 RCN046 RCN199
open RCN344 (DB DQ)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K:Type} [Field K] [IsAlgClosed K]

end
end ProximityPrize.SubmissionLower.EBG

end Compact_SecondJetActiveMovingBudget

section Compact_SecondJetRetainedBudgets

namespace ProximityPrize.SubmissionLower.ENV
open scoped Classical BigOperators
open MvPolynomial DX BX FR
open RCN002 RCN136 RCN264 RCN341 RCN046 RCN095 RCN199
open RCN344 (DQ)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]

end
end ProximityPrize.SubmissionLower.ENV

end Compact_SecondJetRetainedBudgets

section Compact_SecondJetExceptionalComponents

namespace ProximityPrize.SubmissionLower.AEF
open MvPolynomial RCN264
open scoped Classical
noncomputable section
set_option autoImplicit false
variable {K:Type} [Field K] {Seed:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Seed:=Classical.decEq Seed

theorem BOK (F A H T:MvPolynomial (Fin 3) K)
    (Gamma:Finset Seed) (point:Seed→Fin 3→K)
    (C:AU K F A H) (hT:T ∈ C.1)
    (hne: ∀x ∈ Gamma,MvPolynomial.eval (point x) T ≠ 0):
    (HF K F A H Gamma point C).card=0:=by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxG:=LU K F A H Gamma point C hx
  have hpoint:=MC K F A H Gamma point C x hx
  have hz:=hpoint hT
  exact hne x hxG hz

end
end ProximityPrize.SubmissionLower.AEF

end Compact_SecondJetExceptionalComponents

section Compact_SecondJetRetainedStage

namespace ProximityPrize.SubmissionLower.EVW
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA GJ IB
open ND JN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap:ℕ}

end
end ProximityPrize.SubmissionLower.EVW

end Compact_SecondJetRetainedStage

section Compact_C2Geometry80788


section Adapted_LocatorFixedStage
namespace ProximityPrize.SubmissionLower.Lower80788.FixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN146 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def w:ℕ:=131071
def prime:ℕ:=2130706433
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,RCN223.prime] using
    RCN128.FJ
def firstTail (a b s:ℕ):FlagDegree:=
  CI (RCN198.support a b s) (w+1)
def secondTail (a b s:ℕ):FlagDegree:=
  CI (RCN198.support a b s) (w+2)
theorem BRF (a b s d:ℕ):
    CI (RCN198.support a b s) d=
      ⟨2*a*d,1+2*(b+1)*d,2*(s+1)*d⟩:=by
  have ht:a+b+s+3-(b+s+3)=a:=by omega
  have hy:b+s+3-(s+2)=b+1:=by omega
  have hs:2*(s+2)-2=2*(s+1):=by omega
  simp only [CI,UH,RCN198.support]
  rw [ht,hy,hs]
theorem APP (flag:FlagDegree) (a b s:ℕ):
    IY flag a b s w=
      flag.zOnly*(393219+262146*s)+
      flag.yz*(786438+524292*s)+
      flag.all*(1048586+262146*a+524292*b+524292*s):=by
  simp only [IY,paddedCut,
    RCN206.centreFlag,
    RCN206.ZR,
    flagMixed,unitZFlag,unitYZFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all,w]
  ring
theorem CVP (flag:FlagDegree) (a b s:ℕ)
    (hpos:0<flag.zOnly+flag.yz+flag.all):
    1≤IY flag a b s w:=by
  rw [APP]
  have hz:=Nat.mul_le_mul_left flag.zOnly
    (show 1≤393219+262146*s by omega)
  have hy:=Nat.mul_le_mul_left flag.yz
    (show 1≤786438+524292*s by omega)
  have ha:=Nat.mul_le_mul_left flag.all
    (show 1≤1048586+262146*a+524292*b+524292*s by omega)
  simp only [Nat.mul_one] at hz hy ha
  omega
end
end ProximityPrize.SubmissionLower.Lower80788.FixedStage

end Adapted_LocatorFixedStage

section Adapted_LocatorFixed
namespace ProximityPrize.SubmissionLower.Lower80788.Fixed
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 DY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.FJ
def padB (p:FlagDegree):ℕ:=padY p-padS p-1
def padSlope (p:FlagDegree):ℕ:=padS p-2

end
end ProximityPrize.SubmissionLower.Lower80788.Fixed

end Adapted_LocatorFixed

section Adapted_LocatorHybridIdentityC2
namespace ProximityPrize.SubmissionLower.Lower80788.YM

open RCN095 RCN146 RCN203 RCN206 DY AFI
open AVP AAJ RCN198

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def w:ℕ:=131071

theorem APP (flag:FlagDegree) (a b s:ℕ):
    IY flag a b s w=
      flag.zOnly*(393219+262146*s)+
      flag.yz*(786438+524292*s)+
      flag.all*(1048586+262146*a+524292*b+524292*s):=by
  simp only [IY,paddedCut,
    RCN206.centreFlag,RCN206.ZR,
    flagMixed,unitZFlag,unitYZFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all,w]
  ring

def reducedABS (a b s:ℕ):FlagDegree:=
  ⟨2*a*131072,1+(2*b+2)*131072,(2*s+2)*131072⟩
def rationalABS (a b s:ℕ):FlagDegree:=
  ⟨131072*a+2*a,131072*b+2*b+2,131072*s+2*s+3⟩
def mfibABS (a b s:ℕ):FlagDegree:=⟨a,b+1,s+3⟩
def mcutABS (a b s:ℕ):FlagDegree:=rationalABS a b s+⟨0,131072,262144⟩

end ProximityPrize.SubmissionLower.Lower80788.YM

end Adapted_LocatorHybridIdentityC2

section Adapted_LocatorHybridGatesC2
namespace ProximityPrize.SubmissionLower.Lower80788.FBJ
open RCN095 FA GJ

end ProximityPrize.SubmissionLower.Lower80788.FBJ

end Adapted_LocatorHybridGatesC2

section Adapted_LocatorFixedHybridC2
namespace ProximityPrize.SubmissionLower.Lower80788.GWE
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 RCN146 RCN287 RCN136 RCN086 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
open DY AFI AVP AAJ
open Lower80788.YM FA GJ
open IB ND
open Lower80788.FBJ Lower80788.Fixed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.FJ

end
end ProximityPrize.SubmissionLower.Lower80788.GWE

end Adapted_LocatorFixedHybridC2

section Adapted_LocatorHybridRealizeC2
namespace ProximityPrize.SubmissionLower.Lower80788.GHK
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open FA GJ IB
open DY AFI AVP AAJ
open ND
open Lower80788.FBJ
open Lower80788.Fixed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.FJ

end
end ProximityPrize.SubmissionLower.Lower80788.GHK

end Adapted_LocatorHybridRealizeC2

section Adapted_LocatorFixedOwnBoundC2
namespace ProximityPrize.SubmissionLower.Lower80788.GFK
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN275 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN159 RCN137 RCN198 RCN095
open DY AAJ Lower80788.Fixed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.FJ

end
end ProximityPrize.SubmissionLower.Lower80788.GFK

end Adapted_LocatorFixedOwnBoundC2

end Compact_C2Geometry80788

section Compact_SecondJetIdentity

namespace ProximityPrize.SubmissionLower.CWF
open RCN146 RCN086 RCN095 RCN198 RCN206 RCN263 RCN327 FA GJ
open Lower80788.YM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem GTP (t y r:ℕ):
    TX t y r=reducedABS (cellA t y) (cellB y r) (cellS r):=by
  unfold TX cellSupport
  rw [Lower80788.FixedStage.BRF]
  simp only [RCN327.w,reducedABS]
  congr 1<;>ring

theorem FKK (t y r:ℕ):
    MK t y r=rationalABS (cellA t y) (cellB y r) (cellS r):=by
  simp only [MK,cellRational,BGD,ZR,rationalABS,RCN327.w]
  congr 1<;>ring

end
end ProximityPrize.SubmissionLower.CWF

end Compact_SecondJetIdentity

section Compact_SecondJetFixedStage

namespace ProximityPrize.SubmissionLower.FIL
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA GJ IB
open ND JN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open RCN084 RCN146 RCN087 RCN335 RCN174 RCN275 RCN234 RCN156
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433
variable {Gamma:Finset K} {x:I→K} {flag:FlagDegree}

end
end ProximityPrize.SubmissionLower.FIL

end Compact_SecondJetFixedStage

section Compact_SecondJetRegularGeometry

namespace ProximityPrize.SubmissionLower.EPJ
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA GJ IB
open ND JN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open RCN084 RCN146 RCN087 RCN335 RCN174 RCN275 RCN234 RCN156
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433
variable {Gamma:Finset K} {x:I→K} {flag:FlagDegree}

open RCN081 RCN130 RCN221 RCN222 RCN137 RCN238 RCN275

end
end ProximityPrize.SubmissionLower.EPJ

end Compact_SecondJetRegularGeometry

section Compact_SecondJetProperCounting

namespace ProximityPrize.SubmissionLower.BCH
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174 RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001 RCN052
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K:Type} [Field K] {ι:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι

theorem BUM
   (P:DG) (F T:MvPolynomial (Fin 4) K)
   (hFirr:Irreducible F) (hFRpos:0<F.degreeOf 2) (hrel:IsRelPrime F T)
   (p:ℕ) [CharP K p]
   (hFY:F.degreeOf 1≤P.leftY)
   (hFR:F.degreeOf 2≤P.leftR)
   (hFZ:F.degreeOf 3≤P.leftZ)
   (hTY:T.degreeOf 1≤P.rightY)
   (hTR:T.degreeOf 2≤P.rightR)
   (hTZ:T.degreeOf 3≤P.rightZ)
   (hleftR:1≤P.leftR)
   (hleftYSmall:P.leftY<p) (hleftRSmall:P.leftR<p)
   (hleftZSmall:P.leftZ<p)
   (hmixedYSmall:P.mixedCost.y<p)
   (hmixedRSmall:P.mixedCost.r<p)
   (hmixedZSmall:P.mixedCost.z<p)
   (selected:K→Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι→K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1≤P.w) (hchar:P.w<p) (hwa:P.w<P.a)
   (han:P.a≤P.n)
   (hdegree:∀gamma∈Gamma,(selected gamma).natDegree≤P.w)
   (hagreement:∀gamma∈Gamma,
     P.a≤(nodes.filter (fun i=>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:BL selected Gamma P.w P.errors)
   (hsolution:∀gamma∈Gamma,BM K (selected gamma) gamma F=0)
   (hregular:∀gamma∈Gamma,BM K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hTsolution:∀gamma∈Gamma,BM K (selected gamma) gamma T=0):
   Gamma.card*P.gap≤
     (P.n-P.w)*dot P.KO (OX P F)+
       (P.errors+1)*P.gap*(OX P F).z:=by
 classical
 let phi:=AL K
 let Delta:=Gamma
 let carrierCap:RCN051.DegreeVector:=
   ⟨P.leftY,P.leftR,P.leftZ⟩
 let cutCap:RCN051.DegreeVector:=
   ⟨P.rightY,P.rightR,P.rightZ⟩
 have hFne:F≠0:=hFirr.ne_zero
 have hDeltaSub:Delta ⊆ Gamma:=Finset.Subset.refl _
 have hDeltaData (gamma:K) (hgamma:gamma∈Delta):
     AQL F (selected gamma) gamma∧
       BM K (selected gamma) gamma T=0:=
   ⟨⟨hsolution gamma hgamma,hregular gamma hgamma⟩,hTsolution gamma hgamma⟩
 have hproper (g:EX K F):¬g.1∣surfaceMap phi T:=by
   have hg:=ACQ phi F g.1 g.2
   have hpos:0<F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by omega
   have hgeo:g.1∣NB K (GenericField K) F:=by
     simpa only [HP] using hg.2
   intro hgT
   apply hFirr.not_isUnit
   apply hrel (dvd_refl F)
   apply (AIB K (GenericField K) F T hFirr hpos g.1 hg.1 hgeo).mp
   simpa only [HP] using hgT
 have hcover:=AAD K F hFne selected Delta
   (fun gamma hgamma=>(hDeltaData gamma hgamma).1.1)
 letI:CharP (GenericField K) p:=MP K p
 have hsingle (g:EX K F):
     (KK K F selected Delta g).card*P.gap≤
       (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.KO i*
           EB (GenericField K) g.1
             (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           EB (GenericField K) g.1
             (surfaceMap phi T) 2:=by
   have hgSpec:=ACQ phi F g.1 g.2
   have hsub:=WK K F selected Delta g
   have hgCaps:HasCaps g.1 carrierCap:=by
     intro i
     have hi:=AGP K F hFne g i
     fin_cases i
     · exact hi.trans hFY
     · exact hi.trans hFR
     · exact hi.trans hFZ
   have hTCaps:HasCaps (surfaceMap phi T) cutCap:=by
     intro i
     fin_cases i
     · exact (GO phi T 0).trans hTY
     · exact (GO phi T 1).trans hTR
     · exact (GO phi T 2).trans hTZ
   have hcarrierSmall:∀i,capAt carrierCap i<p:=by
     intro i
     fin_cases i
     · exact hleftYSmall
     · exact hleftRSmall
     · exact hleftZSmall
   have hgates:=APW g.1 (surfaceMap phi T)
     carrierCap cutCap p hgCaps hTCaps hcarrierSmall
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitY,DG.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedYSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitR,DG.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedRSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitZ,DG.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedZSmall)
   have hregular:∀gamma∈KK K F selected Delta g,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.HC (phi.comp Polynomial.C)
           (selected gamma) gamma (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) F)≠0:=by
     intro gamma hgamma
     exact VK K F selected gamma
       (hDeltaData gamma (hsub hgamma)).1.2
   have hTpoint:∀gamma∈KK K F selected Delta g,
       MvPolynomial.eval (DK phi selected gamma) (surfaceMap phi T)=0:=by
     intro gamma hgamma
     rw [UM,
       (hDeltaData gamma (hsub hgamma)).2,map_zero]
   have hcap (node:ι):∀j,
       (FK phi F P.w (x node) (u₀ node) (u₁ node)).degreeOf j≤
         regularCapAt P.KO j:=by
     have h:=BHT phi F P.leftY P.leftR P.leftZ hleftR
       hFY hFR hFZ P.w (fun j=>(j.factorial:K)⁻¹)
       (x node) (u₀ node) (u₁ node)
     intro j
     have hj:
         (FK phi F P.w (x node) (u₀ node) (u₁ node)).degreeOf j≤
           capAt (AMS P.leftY P.leftR P.leftZ P.w) j:=by
       simpa [FK] using h j
     fin_cases j<;>exact hj
   have hcount:=COT phi F g.1 (surfaceMap phi T)
     hgSpec.1 hgSpec.2 (hproper g)
     selected (KK K F selected Delta g) nodes x u₀ u₁ hinj
     p P.w P.a P.errors hw hchar hwa (by simpa [hnodes] using han)
     hgates.1 hgates.2
     (fun gamma hgamma=>hdegree gamma (hDeltaSub (hsub hgamma)))
     (fun gamma hgamma=>(hDeltaData gamma (hsub hgamma)).1.1)
     hregular (fun gamma hgamma=>(Finset.mem_filter.mp hgamma).2)
     hTpoint
     (fun gamma hgamma=>hagreement gamma (hDeltaSub (hsub hgamma)))
     (KX selected Gamma _ P.w P.errors
       (fun _ hgamma=>hDeltaSub (hsub hgamma)) hnoPencil)
     (regularCapAt P.KO) (fun node _=>hcap node)
   simpa [hnodes,DG.gap] using hcount
 have hbudget (i:Fin 3):=
   ABX P F T hFne hTY hTR hTZ i
 have hfubini:
     (∑ g:EX K F,∑ i:Fin 3,
         regularCapAt P.KO i*
           EB (GenericField K) g.1 (surfaceMap phi T) i)=
       ∑ i:Fin 3,regularCapAt P.KO i*
         (∑ g:EX K F,
           EB (GenericField K) g.1 (surfaceMap phi T) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Delta.card*P.gap≤
       (∑ g:EX K F,
         (KK K F selected Delta g).card)*P.gap:=
     Nat.mul_le_mul_right P.gap hcover
   _=∑ g:EX K F,
       (KK K F selected Delta g).card*P.gap:=by
     rw [Finset.sum_mul]
   _≤ ∑ g:EX K F,
       ((P.n-P.w)*(∑ i:Fin 3,regularCapAt P.KO i*
         EB (GenericField K) g.1 (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           EB (GenericField K) g.1 (surfaceMap phi T) 2):=
     Finset.sum_le_sum (fun g _=>hsingle g)
   _=(P.n-P.w)*(∑ i:Fin 3,regularCapAt P.KO i*
         (∑ g:EX K F,
           EB (GenericField K) g.1 (surfaceMap phi T) i))+
       (P.errors+1)*P.gap*
         (∑ g:EX K F,
           EB (GenericField K) g.1 (surfaceMap phi T) 2):=by
     rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hfubini]
   _≤(P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.KO i*regularCapAt (OX P F) i)+
       (P.errors+1)*P.gap*regularCapAt (OX P F) 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left _ (Finset.sum_le_sum
         (fun i _=>Nat.mul_le_mul_left _ (hbudget i))))
       (Nat.mul_le_mul_left _ (hbudget 2))
   _=(P.n-P.w)*dot P.KO (OX P F)+
       (P.errors+1)*P.gap*(OX P F).z:=by
     simp [Fin.sum_univ_three,regularCapAt,dot]

end
end ProximityPrize.SubmissionLower.BCH

end Compact_SecondJetProperCounting

section Compact_SecondJetPairBounds

namespace ProximityPrize.SubmissionLower.ZM
open MvPolynomial RCN260 RCN052 RCN294 RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K:Type} [Field K]

theorem ATW (Q:MvPolynomial (Fin 4) K) (r y t:ℕ)
    (hw:wt BE Q≤r∧wt BC Q≤y∧
      wt AT Q≤t):
    Q.degreeOf 1≤y∧Q.degreeOf 2≤r∧Q.degreeOf 3≤t:=by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
  · have h:=(RCN081.KN _ _ _).mp hw.2.1 e he
    simp only [BC,RCN081.weight_fin4] at h
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Fin.isValue,Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero] at h
    omega
  · have h:=(RCN081.KN _ _ _).mp hw.1 e he
    simpa [BE,RCN081.weight_fin4] using h
  · have h:=(RCN081.KN _ _ _).mp hw.2.2 e he
    simp [AT,RCN081.weight_fin4] at h
    omega

theorem FJS (P:DX.Poly (K:=K)) (B U L:ℕ)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤L):
    (BX.asS P).leadingCoeff.degreeOf 1≤U∧
    (BX.asS P).leadingCoeff.degreeOf 2≤B∧
    (BX.asS P).leadingCoeff.degreeOf 3≤L:=by
  apply ATW
  have h:=OR.OE P B U L 0
    (BX.asS P).natDegree hP
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at h
  change wt BE ((BX.asS P).coeff _)≤B∧
    wt BC ((BX.asS P).coeff _)≤U∧
    wt AT ((BX.asS P).coeff _)≤L
  omega

end
end ProximityPrize.SubmissionLower.ZM

end Compact_SecondJetPairBounds

section Compact_SecondJetRegularData

namespace ProximityPrize.SubmissionLower.CWX
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN260 RCN174 RCN275 RCN327
open RCN156 RCN234 FA GJ RCN130 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

namespace Data
variable {nodes:I ↪ K} {u0 u1:I→K}

end Data
end
end ProximityPrize.SubmissionLower.CWX

end Compact_SecondJetRegularData

section Compact_SecondJetWeightedContact

namespace ProximityPrize.SubmissionLower.RX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {B C:Type*} [CommRing B] [CommRing C]

def V (a r:B):Polynomial B:=Polynomial.C (a-r)
def U (a r s:B):Polynomial B:=
  V a r+Polynomial.X*Polynomial.C s
def J (a r s:B):Polynomial B:=
  Polynomial.C r*V a r+Polynomial.X*Polynomial.C (a*s)

theorem J_eq (a r s:B):
    J a r s=Polynomial.C r*U a r s+
      Polynomial.X*Polynomial.C s*V a r:=by
  simp only [J,U,V,map_sub,map_mul]
  ring

theorem contact_J (a r s:B) (φ:Polynomial B→+*C) (ε:C)
    (hε:φ Polynomial.X=ε)
    (hU:ε^2 ∣ φ (U a r s)) (hV:ε ∣ φ (V a r)):
    ε^2 ∣ φ (J a r s):=by
  obtain ⟨u,hu⟩:=hU
  obtain ⟨v,hv⟩:=hV
  refine ⟨φ (Polynomial.C r)*u+φ (Polynomial.C s)*v,?_⟩
  rw [J_eq,map_add,map_mul,map_mul,map_mul,hε,hu,hv]
  ring

def family (a r s z:B) (ρ h u v i j ℓ:ℕ):Polynomial B:=
  Polynomial.X^ρ*(Polynomial.C (s^h)*
    U a r s^(u-ℓ)*J a r s^ℓ*V a r^v*
    Polynomial.C (a^i*r^(j-ℓ)*z))

theorem GRN (a r s z:B) (ρ h u v i j ℓ:ℕ)
    (hℓ:ℓ≤u) (φ:Polynomial B→+*C) (ε:C)
    (hε:φ Polynomial.X=ε)
    (hU:ε^2 ∣ φ (U a r s)) (hV:ε ∣ φ (V a r)):
    ε^(ρ+2*u+v) ∣ φ (family a r s z ρ h u v i j ℓ):=by
  have hJ:=contact_J a r s φ ε hε hU hV
  obtain ⟨cu,hu⟩:=hU
  obtain ⟨cv,hv⟩:=hV
  obtain ⟨cj,hj⟩:=hJ
  refine ⟨φ (Polynomial.C (s^h))*cu^(u-ℓ)*cj^ℓ*cv^v*
    φ (Polynomial.C (a^i*r^(j-ℓ)*z)),?_⟩
  simp only [family,map_mul,map_pow,hε,hu,hv,hj,mul_pow]
  have he:ρ+2*u+v=ρ+2*(u-ℓ)+2*ℓ+v:=by omega
  rw [he]
  simp only [pow_add,pow_mul]
  ring

theorem GGT (a r s z:B) (ρ h u v i j ℓ d:ℕ)
    (hd:d<ρ):(family a r s z ρ h u v i j ℓ).coeff d=0:=by
  simp [family,Polynomial.coeff_X_pow_mul',Nat.not_le.mpr hd]

theorem FUD (a r s z:B) (ρ h u v i j ℓ:ℕ)
    (hu:ℓ≤u) (hj:ℓ≤j):
    (family a r s z ρ h u v i j ℓ).coeff ρ=
      s^h*(a-r)^(u+v)*(a^i*r^j*z):=by
  obtain ⟨u',rfl⟩:=Nat.exists_eq_add_of_le hu
  obtain ⟨j',rfl⟩:=Nat.exists_eq_add_of_le hj
  simp only [family,Polynomial.coeff_X_pow_mul',Nat.sub_self,if_pos (le_refl ρ)]
  simp [Polynomial.coeff_zero_eq_eval_zero,U,J,V,pow_add]
  rw [mul_pow]
  ring

end
end ProximityPrize.SubmissionLower.RX

end Compact_SecondJetWeightedContact

section Compact_SecondJetWeightedBasis

namespace ProximityPrize.SubmissionLower.AHC
open scoped BigOperators
open VV DX BMX PX
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]

theorem C_smul_base (c:K) (v:Base (K:=K)):
    Polynomial.C (c • v)=c • (Polynomial.C v:Polynomial (Base (K:=K))):=
  map_smul (Polynomial.CAlgHom (R:=K) (A:=Base (K:=K))) c v

def weightedTerm (r h a b:ℕ) (e:Fin 3→₀ ℕ):Jet (Base (K:=K)):=
  RX.family
    (Polynomial.C (MvPolynomial.X 0)) (Polynomial.C (MvPolynomial.X 1))
    Polynomial.X (Polynomial.C (MvPolynomial.X 2^(e 2)))
    r h a b (e 0) (e 1) (min a (e 1))

theorem FBZ (r h a b:ℕ) (e:Fin 3→₀ ℕ)
    (d:ℕ) (hd:d<r):(weightedTerm (K:=K) r h a b e).coeff d=0:=
  RX.GGT _ _ _ _ _ _ _ _ _ _ _ _ hd

theorem ERM (r h a b:ℕ) (e:Fin 3→₀ ℕ):
    (weightedTerm (K:=K) r h a b e).coeff r=Polynomial.X^h*
      Polynomial.C (PX.v^(a+b)*MvPolynomial.monomial e (1:K)):=by
  rw [weightedTerm,RX.FUD _ _ _ _ _ _ _ _ _ _ _
    (min_le_left _ _) (min_le_right _ _)]
  have hm:MvPolynomial.monomial e (1:K)=
      MvPolynomial.X 0^(e 0)*MvPolynomial.X 1^(e 1)*MvPolynomial.X 2^(e 2):=by
    rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype]
    · simp [Fin.prod_univ_three]
    · intro i;simp
  rw [hm]
  simp only [PX.v,map_sub,map_mul,map_pow,mul_assoc]

variable {m s:ℕ} {I:Fin m→Fin s→Type*} [∀r h,Fintype (I r h)]
abbrev Parameters:= ∀r:Fin m,∀h:Fin s,I r h→K

def weightedMake (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ):Parameters (K:=K) (I:=I)→ₗ[K] Jet (Base (K:=K)):=
  ∑ r,∑ h,∑ i,LinearMap.smulRight
    (((LinearMap.proj i:(I r h→K)→ₗ[K] K).comp
      (LinearMap.proj h:(∀h,I r h→K)→ₗ[K] (I r h→K))).comp (LinearMap.proj r:Parameters (K:=K) (I:=I)→ₗ[K] (∀h,I r h→K)))
    (weightedTerm r.val h.val (a r h) (b r h) (e r h i))

theorem DNG (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (p:Parameters (K:=K) (I:=I)):
    weightedMake a b e p= ∑ r,∑ h,∑ i,
      p r h i • weightedTerm r.val h.val (a r h) (b r h) (e r h i):=by
  simp [weightedMake]

theorem FFO (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (p:Parameters (K:=K) (I:=I)) (r:Fin m)
    (hp: ∀j,j.val<r.val→p j=0):
    (weightedMake a b e p).coeff r.val= ∑ h,Polynomial.X^h.val*
      Polynomial.C (PX.v^(a r h+b r h)*SC.reconstruct (e r h) (p r h)):=by
  rw [DNG,Polynomial.finsetSum_coeff,Finset.sum_eq_single r]
  · simp_rw [Polynomial.finsetSum_coeff,Polynomial.coeff_smul,ERM]
    apply Finset.sum_congr rfl
    intro h _
    rw [SC.CWA,Finset.mul_sum,map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hm:MvPolynomial.monomial (e r h i) (p r h i)=
        p r h i • MvPolynomial.monomial (e r h i) (1:K):=by
      simpa only [smul_eq_mul,mul_one] using
        (map_smul (MvPolynomial.monomial (e r h i)) (p r h i) (1:K))
    rw [hm]
    simp only [mul_smul_comm,C_smul_base]
  · intro j _ hj
    simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_smul]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro i _
    by_cases hlt:j.val<r.val
    · simp [hp j hlt]
    · rw [FBZ]
      · simp
      · have hne:j.val ≠ r.val:=fun he=>hj (Fin.ext he)
        omega
  · simp

theorem DRO (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (p:Parameters (K:=K) (I:=I)) (r:Fin m)
    (hp: ∀j,j.val<r.val→p j=0):
    truncate (K:=K) (m:=m) (s:=s) (weightedMake a b e p) r=
      fun h=>PX.v^(a r h+b r h)*SC.reconstruct (e r h) (p r h):=by
  funext h
  rw [GQD,FFO a b e p r hp,Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_mul_C,Polynomial.coeff_X_pow,Fin.val_inj]
  simp

theorem DMG (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (he: ∀r h,Function.Injective (e r h)):
    Function.Injective ((truncate (K:=K) (m:=m) (s:=s)).comp (weightedMake a b e)):=by
  let D: ∀r:Fin m,(∀h:Fin s,I r h→K)→ₗ[K] (Fin s→Base (K:=K)):=fun r=>
    LinearMap.pi (fun h=>(LinearMap.mulLeft K (PX.v^(a r h+b r h))).comp
      ((SC.reconstruct (e r h)).comp (LinearMap.proj h)))
  apply EYL.ETC _ D
  · intro r p q hpq
    funext h i
    have hh:=congrFun hpq h
    change PX.v^(a r h+b r h)*SC.reconstruct (e r h) (p h)=
      PX.v^(a r h+b r h)*SC.reconstruct (e r h) (q h) at hh
    have hz:=mul_left_cancel₀ (pow_ne_zero _ (PX.v_ne_zero (K:=K))) hh
    exact congrFun (SC.ABR (e r h) (he r h) hz) i
  · intro p r hp
    exact DRO a b e p r hp

theorem CSK (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (he: ∀r h,Function.Injective (e r h)):
    Function.Injective ((AFQ (K:=K) m).comp (weightedMake a b e)):=by
  intro p q hpq
  apply DMG a b e he
  have hh:=congrArg (truncate (K:=K) (m:=m) (s:=s)) hpq
  simpa only [LinearMap.comp_apply,EVZ] using hh

theorem FMA {T:Type*} [AddCommGroup T] [Module K T]
    (W:Submodule K (Jet (Base (K:=K)))) [FiniteDimensional K W]
    (f:W→ₗ[K] T) (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (he: ∀r h,Function.Injective (e r h))
    (hW: ∀p,AFQ (K:=K) m (weightedMake a b e p) ∈ W)
    (hzero: ∀p,f ⟨AFQ (K:=K) m (weightedMake a b e p),hW p⟩=0):
    Module.finrank K f.range+(∑ r:Fin m,∑ h:Fin s,Fintype.card (I r h))≤
      Module.finrank K W:=by
  let g:=(AFQ (K:=K) m).comp (weightedMake a b e)
  have hg:Function.Injective g:=CSK a b e he
  let gw:Parameters (K:=K) (I:=I)→ₗ[K] W:=g.codRestrict W hW
  let gk:Parameters (K:=K) (I:=I)→ₗ[K] f.ker:=gw.codRestrict f.ker hzero
  have hi:Function.Injective gk:=by
    intro p q hpq
    apply hg
    exact congrArg (fun x:f.ker=>(x.val:Jet (Base (K:=K)))) hpq
  letI:AddCommGroup W:=inferInstance
  letI:Module K W:=W.module
  letI:FiniteDimensional K f.ker:=inferInstance
  have hdim:=LinearMap.finrank_le_finrank_of_injective hi
  have hsum:=f.finrank_range_add_finrank_ker
  have hd:Module.finrank K (Parameters (K:=K) (I:=I))=
      ∑ r:Fin m,∑ h:Fin s,Fintype.card (I r h):=by
    simp [Parameters,Module.finrank_pi_fintype]
  rw [hd] at hdim
  omega

end
end ProximityPrize.SubmissionLower.AHC

end Compact_SecondJetWeightedBasis

section Compact_SecondJetWeightedSupport

namespace ProximityPrize.SubmissionLower.AYY
open scoped BigOperators Pointwise
open MvPolynomial DX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]

def weight (w:Fin 5→ℤ) (e:Fin 5→₀ ℕ):ℤ:= ∑ j,(e j:ℤ)*w j

def LinearBound (w:Fin 5→ℤ) (b:ℤ) (P:Poly (K:=K)):Prop:=
  ∀e ∈ P.support,weight w e≤b

theorem weight_add (w:Fin 5→ℤ) (e f:Fin 5→₀ ℕ):
    weight w (e+f)=weight w e+weight w f:=by
  simp [weight,Finsupp.add_apply,add_mul,Finset.sum_add_distrib]

theorem LinearBound.mono {w:Fin 5→ℤ} {b c:ℤ} {P:Poly (K:=K)}
    (h:LinearBound w b P) (hbc:b≤c):LinearBound w c P:=
  fun e he=>(h e he).trans hbc

theorem LinearBound.mul {w:Fin 5→ℤ} {b c:ℤ} {P Q:Poly (K:=K)}
    (hP:LinearBound w b P) (hQ:LinearBound w c Q):LinearBound w (b+c) (P*Q):=by
  intro e he
  obtain ⟨f,hf,g,hg,rfl⟩:=Finset.mem_add.mp (MvPolynomial.support_mul P Q he)
  rw [weight_add]
  exact add_le_add (hP f hf) (hQ g hg)

theorem LinearBound.add {w:Fin 5→ℤ} {b:ℤ} {P Q:Poly (K:=K)}
    (hP:LinearBound w b P) (hQ:LinearBound w b Q):LinearBound w b (P+Q):=by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hP e h
  · exact hQ e h

theorem LinearBound.neg {w:Fin 5→ℤ} {b:ℤ} {P:Poly (K:=K)}
    (hP:LinearBound w b P):LinearBound w b (-P):=by
  simpa only [LinearBound,MvPolynomial.support_neg] using hP

theorem linear_one (w:Fin 5→ℤ):LinearBound w 0 (1:Poly (K:=K)):=by
  intro e he
  simp only [MvPolynomial.support_one,Finset.mem_singleton] at he
  subst e
  simp [weight]

theorem LinearBound.pow {w:Fin 5→ℤ} {b:ℤ} {P:Poly (K:=K)}
    (hP:LinearBound w b P) (n:ℕ):LinearBound w ((n:ℤ)*b) (P^n):=by
  induction n with
  | zero=>simpa using linear_one (K:=K) w
  | succ n ih=>simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using ih.mul hP

theorem linear_X (w:Fin 5→ℤ) (j:Fin 5):
    LinearBound w (w j) (MvPolynomial.X j:Poly (K:=K)):=by
  intro e he
  simp only [MvPolynomial.support_X,Finset.mem_singleton] at he
  subst e
  simp [weight,Finsupp.single_apply]

def EAD (r h a b i j z l:ℕ):Poly (K:=K):=
  MvPolynomial.X 0^r*MvPolynomial.X 1^h*
    (MvPolynomial.X 2-MvPolynomial.X 3+MvPolynomial.X 0*MvPolynomial.X 1)^(a-l)*
    (MvPolynomial.X 3*(MvPolynomial.X 2-MvPolynomial.X 3)+
      MvPolynomial.X 0*MvPolynomial.X 2*MvPolynomial.X 1)^l*
    (MvPolynomial.X 2-MvPolynomial.X 3)^b*
    MvPolynomial.X 2^i*MvPolynomial.X 3^(j-l)*MvPolynomial.X 4^z

theorem AHS (w:Fin 5→ℤ) (r h a b i j z l:ℕ):
    LinearBound w ((r:ℤ)*w 0+(h:ℤ)*w 1+
      ((a-l:ℕ):ℤ)*max (max (w 2) (w 3)) (w 0+w 1)+
      (l:ℤ)*max (w 3+max (w 2) (w 3)) (w 0+w 2+w 1)+
      (b:ℤ)*max (w 2) (w 3)+(i:ℤ)*w 2+((j-l:ℕ):ℤ)*w 3+(z:ℤ)*w 4)
      (EAD (K:=K) r h a b i j z l):=by
  have hE:=linear_X (K:=K) w 0
  have hS:=linear_X (K:=K) w 1
  have hA:=linear_X (K:=K) w 2
  have hR:=linear_X (K:=K) w 3
  have hZ:=linear_X (K:=K) w 4
  have hV:LinearBound w (max (w 2) (w 3))
      (MvPolynomial.X 2-MvPolynomial.X 3:Poly (K:=K)):=by
    rw [sub_eq_add_neg]
    exact (hA.mono (le_max_left _ _)).add (hR.neg.mono (le_max_right _ _))
  have hU:=(hV.mono (le_max_left _ (w 0+w 1))).add
    ((hE.mul hS).mono (le_max_right _ _))
  have hJ:=((hR.mul hV).mono (le_max_left _ (w 0+w 2+w 1))).add
    (((hE.mul hA).mul hS).mono (le_max_right _ _))
  exact (((((((hE.pow r).mul (hS.pow h)).mul (hU.pow (a-l))).mul (hJ.pow l)).mul
    (hV.pow b)).mul (hA.pow i)).mul (hR.pow (j-l))).mul (hZ.pow z)

theorem EVK (r h a b i j z l:ℕ) (hla:l≤a) (hlj:l≤j)
    (e:Fin 5→₀ ℕ) (he:e ∈ (EAD (K:=K) r h a b i j z l).support):
    r≤e 0∧e 2≤ i+a+b∧e 3≤j+a+b∧h≤e 1∧e 1≤h+a∧
      e 1+e 2+e 3≤ i+j+h+a+b∧e 1+e 2+e 3+e 4≤ i+j+h+a+b+z∧
      2*e 1+e 3≤2*h+2*a+b+j-l:=by
  have h0:=AHS (K:=K) ![-1,0,0,0,0] r h a b i j z l e he
  have hA:=AHS (K:=K) ![0,0,1,0,0] r h a b i j z l e he
  have hR:=AHS (K:=K) ![0,0,0,1,0] r h a b i j z l e he
  have hSlo:=AHS (K:=K) ![0,-1,0,0,0] r h a b i j z l e he
  have hShi:=AHS (K:=K) ![0,1,0,0,0] r h a b i j z l e he
  have hM:=AHS (K:=K) ![0,1,1,1,0] r h a b i j z l e he
  have hT:=AHS (K:=K) ![0,1,1,1,1] r h a b i j z l e he
  have hB:=AHS (K:=K) ![0,2,0,1,0] r h a b i j z l e he
  norm_num [weight,Fin.sum_univ_five,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four] at h0 hA hR hSlo hShi hM hT hB
  omega

end
end ProximityPrize.SubmissionLower.AYY

end Compact_SecondJetWeightedSupport

section Compact_SecondJetWeightedLocal

namespace ProximityPrize.SubmissionLower.CFG
open VV DX PX AHC
open AYY MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]

theorem ENH (r h a b:ℕ) (e:Fin 3→₀ ℕ):
    flatEquiv (K:=K) (EAD (K:=K) r h a b (e 0) (e 1) (e 2) (min a (e 1)))=
      weightedTerm (K:=K) r h a b e:=by
  simp only [EAD,map_mul,map_pow,map_add,map_sub,flatEquiv_X,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four]
  simp only [Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Matrix.cons_val_succ,Matrix.cons_val_zero]
  simp only [weightedTerm,RX.family,RX.U,
    RX.V,RX.J,map_mul,map_pow,map_add,map_sub]
  ring

theorem FBI (m r h a b:ℕ) (e:Fin 3→₀ ℕ)
    (horder:m≤r+2*a+b):
    Polynomial.X^m ∣ contact (K:=K) (weightedTerm (K:=K) r h a b e):=by
  apply (pow_dvd_pow Polynomial.X horder).trans
  unfold weightedTerm
  apply RX.GRN _ _ _ _ _ _ _ _ _ _ _
    (min_le_left _ _) (contact (K:=K)).toRingHom Polynomial.X contact_X
  · have hu:(Polynomial.X:Target (K:=K))^2 ∣ contact (K:=K)
        (Polynomial.C (Polynomial.C PX.v)+Polynomial.X*Polynomial.C Polynomial.X):=
      ⟨Polynomial.C (MvPolynomial.X 1),contact_u⟩
    simpa only [RX.U,RX.V,
      PX.v,map_sub,AlgHom.toRingHom_eq_coe,RingHom.coe_coe] using hu
  · have hv:(Polynomial.X:Target (K:=K)) ∣
        contact (K:=K) (Polynomial.C (Polynomial.C PX.v)):=by
      rw [contact_v]
      exact dvd_mul_right _ _
    simpa only [RX.V,PX.v,map_sub,AlgHom.toRingHom_eq_coe,RingHom.coe_coe] using hv

end
end ProximityPrize.SubmissionLower.CFG

end Compact_SecondJetWeightedLocal

section Compact_SecondJetRelaxedSpace

namespace ProximityPrize.SubmissionLower.ABQ
open scoped BigOperators
open VV DX AYY CFG
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

def Index (m L B s U:ℕ) (caps:ℕ→ℕ):=
  {d:ANF.Index m L B s//2*(d.val 1).val+(d.val 3).val≤B∧
    (d.val 1).val+(d.val 2).val+(d.val 3).val≤U∧
    (d.val 1).val+(d.val 2).val+(d.val 3).val≤caps (d.val 1).val}

instance (m L B s U:ℕ) (caps:ℕ→ℕ):Fintype (Index m L B s U caps):=by
  unfold Index
  infer_instance

def exponent {m L B s U:ℕ} {caps:ℕ→ℕ} (d:Index m L B s U caps):Fin 5→₀ ℕ:=
  ANF.exponent d.val

theorem ACD (m L B s U:ℕ) (caps:ℕ→ℕ):
    Function.Injective (exponent (m:=m) (L:=L) (B:=B) (s:=s) (U:=U) (caps:=caps)):=
  (ANF.ACD m L B s).comp Subtype.val_injective

theorem DMI (m L B s U:ℕ) (caps:ℕ→ℕ) (d:Fin 5→₀ ℕ):
    d ∈ Set.range (exponent (m:=m) (L:=L) (B:=B) (s:=s) (U:=U) (caps:=caps)) ↔
      Allowed m L B s d∧2*d 1+d 3≤B∧d 1+d 2+d 3≤U∧d 1+d 2+d 3≤caps (d 1):=by
  constructor
  · rintro ⟨e,rfl⟩
    exact ⟨ANF.EZJ e.val,e.property⟩
  · rintro ⟨hd,hrs⟩
    obtain ⟨e,he⟩:=(ANF.DMI m L B s d).mpr hd
    have hrs' :2*(e.val 1).val+(e.val 3).val≤B∧(e.val 1).val+(e.val 2).val+(e.val 3).val≤U∧(e.val 1).val+(e.val 2).val+(e.val 3).val≤caps (e.val 1).val:=by
      simpa only [← he,ANF.AUW] using hrs
    exact ⟨⟨e,hrs'⟩,he⟩

def sourceMap (m L B s U:ℕ) (caps:ℕ→ℕ):(Index m L B s U caps→K)→ₗ[K]
    Jet (MvPolynomial (Fin 3) K):=
  (flatEquiv (K:=K)).toLinearMap.comp (SC.reconstruct exponent)

def source (m L B s U:ℕ) (caps:ℕ→ℕ):Submodule K (Jet (MvPolynomial (Fin 3) K)):=
  (sourceMap (K:=K) m L B s U caps).range

instance source_finite (m L B s U:ℕ) (caps:ℕ→ℕ):FiniteDimensional K (source (K:=K) m L B s U caps):=by
  unfold source
  infer_instance

theorem FHX (m L B s U:ℕ) (caps:ℕ→ℕ):
    Function.Injective (sourceMap (K:=K) m L B s U caps):=
  (flatEquiv (K:=K)).injective.comp
    (SC.ABR _ (ACD m L B s U caps))

theorem GSG (m L B s U:ℕ) (caps:ℕ→ℕ):
    Module.finrank K (source (K:=K) m L B s U caps)=Fintype.card (Index m L B s U caps):=by
  unfold source
  rw [← (LinearEquiv.ofInjective (sourceMap (K:=K) m L B s U caps)
    (FHX m L B s U caps)).finrank_eq]
  simp

theorem FKZ (m L B s U:ℕ) (caps:ℕ→ℕ) (P:Jet (MvPolynomial (Fin 3) K)):
    P ∈ source (K:=K) m L B s U caps ↔
      ∀d ∈ ((flatEquiv (K:=K)).symm P).support,
        Allowed m L B s d∧2*d 1+d 3≤B∧d 1+d 2+d 3≤U∧d 1+d 2+d 3≤caps (d 1):=by
  have hm:P ∈ source (K:=K) m L B s U caps ↔
      (flatEquiv (K:=K)).symm P ∈ (SC.reconstruct (K:=K)
        (exponent (m:=m) (L:=L) (B:=B) (s:=s) (U:=U) (caps:=caps))).range:=by
    constructor
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h:=congrArg (flatEquiv (K:=K)).symm hc
      simpa [sourceMap] using h
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h:=congrArg (flatEquiv (K:=K)) hc
      simpa [sourceMap] using h
  rw [hm,SC.mem_range_iff _ (ACD m L B s U caps)]
  simp only [DMI]

theorem EFF (m L B s U:ℕ) (caps:ℕ→ℕ)
    (r h a b:ℕ) (e:Fin 3→₀ ℕ)
    (hi:e 0+a+b≤r) (hS:h+a≤s)
    (hB:2*h+2*a+b+e 1-min a (e 1)≤B)
    (hU:e 0+e 1+h+a+b≤U)
    (hL:e 0+e 1+h+a+b+e 2≤L)
    (hcaps: ∀j,h≤j→j≤h+a→e 0+e 1+h+a+b≤caps j):
    AFQ (K:=K) m (AHC.weightedTerm r h a b e) ∈
      source (K:=K) m L B s U caps:=by
  rw [← ENH,← DGT,FKZ]
  simp only [AlgEquiv.symm_apply_apply]
  intro d hd
  have ht:=EQF m _ d hd
  obtain ⟨h0,hA,hR,hlo,hhi,hM,hT,hRS⟩:=EVK r h a b
    (e 0) (e 1) (e 2) (min a (e 1)) (min_le_left _ _) (min_le_right _ _) d ht.2
  refine ⟨?_,hRS.trans hB,hM.trans hU,hM.trans (hcaps (d 1) hlo hhi)⟩
  dsimp only [Allowed]
  exact ⟨ht.1,by omega,by omega,by omega,hT.trans hL⟩

end
end ProximityPrize.SubmissionLower.ABQ

end Compact_SecondJetRelaxedSpace

section Compact_SecondJetClippedRectangle

namespace ProximityPrize.SubmissionLower.BNC
open scoped BigOperators
open DPO
set_option autoImplicit false
set_option maxHeartbeats 4000000

def corner (A B H:ℕ):ℕ:=A+B-2-H

def DGZ (A B C H:ℕ):ℕ:=
  rectangle A B C- ∑ i ∈ Finset.range (corner A B H),
    ∑ j ∈ Finset.range (corner A B H),
      if i+j<corner A B H then C-(A-1-i)-(B-1-j) else 0

theorem outside_sum (A B C H:ℕ) (hA:0<A) (hB:0<B)
    (hkA:corner A B H≤A) (hkB:corner A B H≤B):
    (∑ i ∈ Finset.range A,∑ j ∈ Finset.range B,if H< i+j then C-i-j else 0)=
      ∑ i ∈ Finset.range (corner A B H),∑ j ∈ Finset.range (corner A B H),
        if i+j<corner A B H then C-(A-1-i)-(B-1-j) else 0:=by
  classical
  let s:=((Finset.range A) ×ˢ (Finset.range B)).filter (fun p=>H<p.1+p.2)
  let t:=((Finset.range (corner A B H)) ×ˢ (Finset.range (corner A B H))).filter
    (fun p=>p.1+p.2<corner A B H)
  have heq:(∑ p ∈ s,(C-p.1-p.2))=
      ∑ p ∈ t,(C-(A-1-p.1)-(B-1-p.2)):=by
    apply Finset.sum_bij (fun p _=>(A-1-p.1,B-1-p.2))
    · intro p hp
      simp only [s,Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hp
      obtain ⟨⟨hp1,hp2⟩,hp3⟩:=hp
      dsimp [corner] at hkA hkB
      simp only [t,Finset.mem_filter,Finset.mem_product,Finset.mem_range,corner]
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
      · exact Finset.mem_range.mpr (by omega)
      · exact Finset.mem_range.mpr (by omega)
      · show (A-1-p.1)+(B-1-p.2)<A+B-2-H
        omega
    · intro p hp q hq hpq
      simp only [s,Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hp hq
      have h1:=congrArg Prod.fst hpq
      have h2:=congrArg Prod.snd hpq
      apply Prod.ext<;>dsimp at h1 h2 ⊢ <;>omega
    · intro p hp
      simp only [t,Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hp
      refine ⟨(A-1-p.1,B-1-p.2),?_,?_⟩
      · simp only [s,Finset.mem_filter,Finset.mem_product,Finset.mem_range,Prod.fst,Prod.snd]
        dsimp [corner] at hp hkA hkB
        omega
      · apply Prod.ext<;>dsimp<;>omega
    · intro p hp
      have hpmem:(p.1<A∧p.2<B)∧H<p.1+p.2:=by
        simpa only [s,Finset.mem_filter,Finset.mem_product,Finset.mem_range] using hp
      change C-p.1-p.2=C-(A-1-(A-1-p.1))-(B-1-(B-1-p.2))
      omega
  simpa only [s,t,Finset.sum_filter,Finset.sum_product] using heq

theorem DSV (A B C H:ℕ) (hA:0<A) (hB:0<B)
    (hkA:corner A B H≤A) (hkB:corner A B H≤B)
    (hC: ∀i:Fin A,∀j:Fin B,i.val+j.val≤C):
    (∑ i:Fin A,∑ j:Fin B,if i.val+j.val≤H then C-i.val-j.val else 0)=
      DGZ A B C H:=by
  have hsum:
      (∑ i:Fin A,∑ j:Fin B,if i.val+j.val≤H then C-i.val-j.val else 0)+
      (∑ i:Fin A,∑ j:Fin B,if H< i.val+j.val then C-i.val-j.val else 0)=
        rectangle A B C:=by
    rw [← Finset.sum_add_distrib]
    calc
      _= ∑ i:Fin A,∑ j:Fin B,(C-i.val-j.val):=by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h:i.val+j.val≤H<;>simp [h,Nat.not_lt_of_ge,Nat.lt_of_not_ge]
      _=_:=FAH A B C hC
  have hout:=outside_sum A B C H hA hB hkA hkB
  have houtside:
      (∑ i:Fin A,∑ j:Fin B,if H< i.val+j.val then C-i.val-j.val else 0)=
      ∑ i ∈ Finset.range A,∑ j ∈ Finset.range B,if H< i+j then C-i-j else 0:=by
    rw [Fin.sum_univ_eq_sum_range (fun i:ℕ=> ∑ j:Fin B,if H< i+j.val then C-i-j.val else 0)]
    apply Finset.sum_congr rfl
    intro i _
    exact Fin.sum_univ_eq_sum_range (fun j:ℕ=>if H< i+j then C-i-j else 0) B
  rw [houtside,hout] at hsum
  unfold DGZ
  omega

end ProximityPrize.SubmissionLower.BNC

end Compact_SecondJetClippedRectangle

section Compact_SecondJetRelaxedSourceCounts

namespace ProximityPrize.SubmissionLower.CBK
open scoped BigOperators
open ABQ BNC
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev FKU (m L B s U:ℕ):=
  Σ r:Fin m,Σ h:Fin (s+1),Σ i:Fin (r.val+1),Σ j:Fin (B-2*h.val+1),
    Fin (if h.val+i.val+j.val≤U then L+1-h.val-i.val-j.val else 0)

def sourceEquiv (m L B s U:ℕ) (caps:ℕ→ℕ) (hsB:2*s≤B)
    (hcaps: ∀h,h≤s→U≤caps h):
    Index m L B s U caps ≃ FKU m L B s U where
  toFun d:=by
    have hi:=d.val.property.1
    have ht:=d.val.property.2
    have hd:=d.property
    refine ⟨d.val.val 0,d.val.val 1,⟨(d.val.val 2).val,by omega⟩,
      ⟨(d.val.val 3).val,by change (d.val.val 3).val<B-2*(d.val.val 1).val+1;omega⟩,
      ⟨(d.val.val 4).val,?_⟩⟩
    change (d.val.val 4).val<
      if (d.val.val 1).val+(d.val.val 2).val+(d.val.val 3).val≤U then
        L+1-(d.val.val 1).val-(d.val.val 2).val-(d.val.val 3).val else 0
    rw [if_pos hd.2.1]
    omega
  invFun u:=by
    rcases u with ⟨r,h,i,j,z⟩
    have hh:=h.isLt
    have hi:=i.isLt
    have hj:=j.isLt
    have hz:=z.isLt
    have hU:h.val+i.val+j.val≤U:=by
      by_contra hn
      simp only [if_neg hn] at hz
      omega
    simp only [if_pos hU] at hz
    let iv:Fin m:=⟨i.val,by have hr:=r.isLt;omega⟩
    let jv:Fin (B+1):=⟨j.val,by omega⟩
    let zv:Fin (L+1):=⟨z.val,by omega⟩
    let d: ∀k,Fin (ANF.bound m L B s k):=
      Fin.cases r (Fin.cases h (Fin.cases iv (Fin.cases jv (Fin.cases zv (fun i=>Fin.elim0 i)))))
    refine ⟨⟨d,?_,?_⟩,?_,?_,?_⟩
    · change i.val≤r.val
      omega
    · change h.val+i.val+j.val+z.val≤L
      omega
    · change 2*h.val+j.val≤B
      omega
    · exact hU
    · exact hU.trans (hcaps h.val (by omega))
  left_inv d:=by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k<;>rfl
  right_inv u:=by
    rcases u with ⟨r,h,i,j,z⟩
    rfl

theorem card_source (m L B s U:ℕ) (caps:ℕ→ℕ) (hsB:2*s≤B)
    (hcaps: ∀h,h≤s→U≤caps h):
    Fintype.card (Index m L B s U caps)=
      ∑ r:Fin m,∑ h:Fin (s+1),∑ i:Fin (r.val+1),∑ j:Fin (B-2*h.val+1),
        if h.val+i.val+j.val≤U then L+1-h.val-i.val-j.val else 0:=by
  rw [Fintype.card_congr (sourceEquiv m L B s U caps hsB hcaps)]
  simp [FKU]

def sourceCount (m L B s U:ℕ):ℕ:=
  ∑ r:Fin m,∑ h:Fin (s+1),
    DGZ (r.val+1) (B-2*h.val+1) (L+1-h.val) (U-h.val)

theorem FNY (m L B s U:ℕ) (caps:ℕ→ℕ)
    (hsB:2*s≤B) (hBm:B≤m) (hU:m+s≤U) (hL:m+B+s≤L)
    (hcaps: ∀h,h≤s→U≤caps h):
    Fintype.card (Index m L B s U caps)=sourceCount m L B s U:=by
  rw [card_source m L B s U caps hsB hcaps]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  have hr:=r.isLt
  have hh:=h.isLt
  have heq:
      (∑ i:Fin (r.val+1),∑ j:Fin (B-2*h.val+1),
        if h.val+i.val+j.val≤U then L+1-h.val-i.val-j.val else 0)=
      ∑ i:Fin (r.val+1),∑ j:Fin (B-2*h.val+1),
        if i.val+j.val≤U-h.val then (L+1-h.val)-i.val-j.val else 0:=by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hc:(h.val+i.val+j.val≤U) ↔ (i.val+j.val≤U-h.val):=by omega
    simp only [hc]
  rw [heq]
  apply DSV
  · omega
  · omega
  · dsimp [corner]
    omega
  · dsimp [corner]
    omega
  · intro i j
    have hi:=i.isLt
    have hj:=j.isLt
    omega

end
end ProximityPrize.SubmissionLower.CBK

end Compact_SecondJetRelaxedSourceCounts

section Compact_SecondJetRelaxedRank

namespace ProximityPrize.SubmissionLower.AEB
open scoped BigOperators
open VV DX PX ABQ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]

def q (m s r h:ℕ):=max ((m-r+1)/2) (m-r-(s-h))
def a (m s r h:ℕ):=m-r-q m s r h
def b (m s r h:ℕ):=q m s r h-a m s r h

theorem budgets (m s r h:ℕ) (hr:r≤m) (hh:h≤s):
    a m s r h+b m s r h=q m s r h∧h+a m s r h≤s∧
      r+2*a m s r h+b m s r h=m:=by
  dsimp [a,b,q]
  omega

def Block (m L B s U:ℕ) (caps:ℕ→ℕ) (r h:ℕ):=
  {e:Fin 3→Fin (L+1)//
    (e 0).val+q m s r h≤r∧(e 1).val+q m s r h+2*h≤B∧
    m-r+2*h≤B∧(e 0).val+(e 1).val+h+q m s r h≤U∧
    (e 0).val+(e 1).val+h+q m s r h+(e 2).val≤L∧
    ∀j:Fin (a m s r h+1),
      (e 0).val+(e 1).val+h+q m s r h≤caps (h+j.val)}

instance (m L B s U:ℕ) (caps:ℕ→ℕ) (r h:ℕ):
    Fintype (Block m L B s U caps r h):=by
  unfold Block
  infer_instance

def exponent {m L B s U:ℕ} {caps:ℕ→ℕ} {r h:ℕ}
    (e:Block m L B s U caps r h):Fin 3→₀ ℕ:=
  Finsupp.equivFunOnFinite.symm (fun j=>(e.val j).val)

@[simp] theorem AUW {m L B s U:ℕ} {caps:ℕ→ℕ} {r h:ℕ}
    (e:Block m L B s U caps r h) (j:Fin 3):exponent e j=(e.val j).val:=by
  simp [exponent]

theorem ACD (m L B s U:ℕ) (caps:ℕ→ℕ) (r h:ℕ):
    Function.Injective (exponent (m:=m) (L:=L) (B:=B) (s:=s) (U:=U)
      (caps:=caps) (r:=r) (h:=h)):=by
  intro e f hef
  apply Subtype.ext
  funext j
  apply Fin.ext
  simpa only [AUW] using congrArg (fun g:Fin 3→₀ ℕ=>g j) hef

abbrev Parameters (m L B s U:ℕ) (caps:ℕ→ℕ):=
  ∀r:Fin m,∀h:Fin (s+1),Block m L B s U caps r.val h.val→K

def make (m L B s U:ℕ) (caps:ℕ→ℕ):
    Parameters (K:=K) m L B s U caps→ₗ[K] Jet (Base (K:=K)):=
  (AFQ (K:=K) m).comp (AHC.weightedMake
    (fun r h=>a m s r.val h.val) (fun r h=>b m s r.val h.val)
    (fun _ _=>exponent))

theorem GIQ (m L B s U:ℕ) (caps:ℕ→ℕ)
    (p:Parameters (K:=K) m L B s U caps):
    make m L B s U caps p ∈ source (K:=K) m L B s U caps:=by
  simp only [make,LinearMap.comp_apply,AHC.DNG,map_sum,map_smul]
  apply Submodule.sum_mem
  intro r _
  apply Submodule.sum_mem
  intro h _
  apply Submodule.sum_mem
  intro e _
  apply Submodule.smul_mem
  have hb:=budgets m s r.val h.val (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)
  have he:=e.property
  apply EFF
  · simp only [AUW]
    omega
  · exact hb.2.1
  · simp only [AUW]
    omega
  · simp only [AUW]
    omega
  · simp only [AUW]
    omega
  · intro j hj hj'
    have hd:=he.2.2.2.2.2 (⟨j-h.val,by omega⟩:Fin (a m s r.val h.val+1))
    simp only [AUW]
    dsimp at hd
    have hjj:h.val+(j-h.val)=j:=by omega
    rw [hjj] at hd
    omega

def COQ (m L B s U:ℕ) (caps:ℕ→ℕ):
    source (K:=K) m L B s U caps→ₗ[K] Target (K:=K):=
  (BMX.contactMap (K:=K) m).comp (source (K:=K) m L B s U caps).subtype

theorem make_zero (m L B s U:ℕ) (caps:ℕ→ℕ)
    (p:Parameters (K:=K) m L B s U caps):
    BMX.contactMap (K:=K) m (make m L B s U caps p)=0:=by
  change contact (K:=K) (make m L B s U caps p)%ₘ Polynomial.X^m=0
  apply (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr
  change Polynomial.X^m ∣ contact (K:=K) (AFQ (K:=K) m _)
  apply FBL (K:=K) (contact (K:=K)).toRingHom Polynomial.X m _ contact_X
  change Polynomial.X^m ∣ contact (K:=K) _
  rw [AHC.DNG,map_sum]
  apply Finset.dvd_sum
  intro r _
  rw [map_sum]
  apply Finset.dvd_sum
  intro h _
  rw [map_sum]
  apply Finset.dvd_sum
  intro e _
  rw [map_smul,Algebra.smul_def]
  apply dvd_mul_of_dvd_right
  apply CFG.FBI
  exact le_of_eq (budgets m s r.val h.val (Nat.le_of_lt r.isLt)
    (Nat.le_of_lt_succ h.isLt)).2.2.symm

theorem GBK (m L B s U:ℕ) (caps:ℕ→ℕ):
    Module.finrank K (COQ (K:=K) m L B s U caps).range+
      (∑ r:Fin m,∑ h:Fin (s+1),Fintype.card (Block m L B s U caps r.val h.val))≤
        Fintype.card (Index m L B s U caps):=by
  have h:=AHC.FMA
    (source (K:=K) m L B s U caps) (COQ (K:=K) m L B s U caps)
    (fun r h=>a m s r.val h.val) (fun r h=>b m s r.val h.val)
    (fun _ _=>exponent) (fun r h=>ACD m L B s U caps r.val h.val)
    (GIQ m L B s U caps) (make_zero m L B s U caps)
  rwa [GSG] at h

end
end ProximityPrize.SubmissionLower.AEB

end Compact_SecondJetRelaxedRank

section Compact_SecondJetRelaxedKernelCounts

namespace ProximityPrize.SubmissionLower.CBH
open scoped BigOperators
open AEB BNC
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

abbrev DWO (m L B s U r h:ℕ):=
  Σ i:Fin (r-q m s r h+1),Σ j:Fin (B-2*h-q m s r h+1),
    Fin (if h+q m s r h+i.val+j.val≤U then L+1-h-q m s r h-i.val-j.val else 0)

def blockEquiv (m L B s U:ℕ) (caps:ℕ→ℕ) (r h:ℕ)
    (hrm:r≤m) (hhs:h≤s)
    (hr:q m s r h≤r) (hB:m-r+2*h≤B)
    (hcaps: ∀h,h≤s→U≤caps h):
    Block m L B s U caps r h ≃ DWO m L B s U r h where
  toFun d:=by
    have hd:=d.property
    refine ⟨⟨(d.val 0).val,by omega⟩,⟨(d.val 1).val,by omega⟩,
      ⟨(d.val 2).val,?_⟩⟩
    change (d.val 2).val< if h+q m s r h+(d.val 0).val+(d.val 1).val≤U then
      L+1-h-q m s r h-(d.val 0).val-(d.val 1).val else 0
    rw [if_pos (by omega)]
    omega
  invFun u:=by
    rcases u with ⟨i,j,z⟩
    have hi:=i.isLt
    have hj:=j.isLt
    have hz:=z.isLt
    have hU:h+q m s r h+i.val+j.val≤U:=by
      by_contra hn
      simp only [if_neg hn] at hz
      omega
    simp only [if_pos hU] at hz
    have hb:=budgets m s r h hrm hhs
    let iv:Fin (L+1):=⟨i.val,by omega⟩
    let jv:Fin (L+1):=⟨j.val,by omega⟩
    let zv:Fin (L+1):=⟨z.val,by omega⟩
    refine ⟨![iv,jv,zv],?_,?_,?_,?_,?_,?_⟩
    · change i.val+q m s r h≤r
      omega
    · change j.val+q m s r h+2*h≤B
      omega
    · exact hB
    · change i.val+j.val+h+q m s r h≤U
      omega
    · change i.val+j.val+h+q m s r h+z.val≤L
      omega
    · intro t
      change i.val+j.val+h+q m s r h≤caps (h+t.val)
      have ht:=t.isLt
      have hc:=hcaps (h+t.val) (by omega)
      omega
  left_inv d:=by
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k<;>rfl
  right_inv u:=by
    rcases u with ⟨i,j,z⟩
    rfl

theorem EBT (m L B s U:ℕ) (caps:ℕ→ℕ) (r h:ℕ)
    (hrm:r≤m) (hhs:h≤s)
    (hr:q m s r h≤r) (hB:m-r+2*h≤B)
    (hcaps: ∀h,h≤s→U≤caps h):
    Fintype.card (Block m L B s U caps r h)=
      ∑ i:Fin (r-q m s r h+1),∑ j:Fin (B-2*h-q m s r h+1),
        if h+q m s r h+i.val+j.val≤U then L+1-h-q m s r h-i.val-j.val else 0:=by
  rw [Fintype.card_congr (blockEquiv m L B s U caps r h hrm hhs hr hB hcaps)]
  simp [DWO]

theorem CVB (m L B s U:ℕ) (caps:ℕ→ℕ) (r h:ℕ)
    (hq: ¬(q m s r h≤r∧m-r+2*h≤B)):
    Fintype.card (Block m L B s U caps r h)=0:=by
  letI:IsEmpty (Block m L B s U caps r h):=⟨fun d=>by have hd:=d.property;omega⟩
  simp

def kernelCell (m L B s U r h:ℕ):ℕ:=
  if q m s r h≤r∧m-r+2*h≤B then
    DGZ (r-q m s r h+1) (B-2*h-q m s r h+1)
      (L+1-h-q m s r h) (U-h-q m s r h)
  else 0

theorem DVH (m L B s U:ℕ) (caps:ℕ→ℕ) (r h:ℕ)
    (hBm:B≤m) (hU:m+s≤U) (hL:m+B+s≤L)
    (hrm:r<m) (hhs:h≤s)
    (hcaps: ∀h,h≤s→U≤caps h):
    Fintype.card (Block m L B s U caps r h)=kernelCell m L B s U r h:=by
  unfold kernelCell
  split_ifs with hq
  · rw [EBT m L B s U caps r h (by omega) hhs hq.1 hq.2 hcaps]
    have hb:=budgets m s r h (by omega) hhs
    have heq:
        (∑ i:Fin (r-q m s r h+1),∑ j:Fin (B-2*h-q m s r h+1),
          if h+q m s r h+i.val+j.val≤U then L+1-h-q m s r h-i.val-j.val else 0)=
        ∑ i:Fin (r-q m s r h+1),∑ j:Fin (B-2*h-q m s r h+1),
          if i.val+j.val≤U-h-q m s r h then (L+1-h-q m s r h)-i.val-j.val else 0:=by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hc:(h+q m s r h+i.val+j.val≤U) ↔
          (i.val+j.val≤U-h-q m s r h):=by omega
      simp only [hc]
    rw [heq]
    apply DSV
    · omega
    · omega
    · dsimp [corner]
      omega
    · dsimp [corner]
      omega
    · intro i j
      have hi:=i.isLt
      have hj:=j.isLt
      omega
  · exact CVB m L B s U caps r h hq

def kernelCount (m L B s U:ℕ):ℕ:=
  ∑ r:Fin m,∑ h:Fin (s+1),kernelCell m L B s U r.val h.val

theorem GGV (m L B s U:ℕ) (caps:ℕ→ℕ)
    (hBm:B≤m) (hU:m+s≤U) (hL:m+B+s≤L)
    (hcaps: ∀h,h≤s→U≤caps h):
    (∑ r:Fin m,∑ h:Fin (s+1),Fintype.card (Block m L B s U caps r.val h.val))=
      kernelCount m L B s U:=by
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  exact DVH m L B s U caps r.val h.val hBm hU hL r.isLt
    (Nat.le_of_lt_succ h.isLt) hcaps

end
end ProximityPrize.SubmissionLower.CBH

end Compact_SecondJetRelaxedKernelCounts

section Compact_SecondJetRelaxedGlobalSupport

namespace ProximityPrize.SubmissionLower.BYD
open scoped BigOperators
open MvPolynomial DX VV HZ
open AYY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]

theorem linear_C (w:Fin 5→ℤ) (c:K):LinearBound w 0 (MvPolynomial.C c):=by
  intro e he
  have he0:e=0:=Finset.mem_singleton.mp (MvPolynomial.support_C_subset he)
  subst e
  simp [weight]

theorem CKY (w:Fin 5→ℤ) (hw0:w 0=0) (hw4:w 4=0)
    (hw2:0≤w 2) (x u0 u1:K) (j:Fin 5):
    LinearBound w (w j) (localize x u0 u1 (MvPolynomial.X j)):=by
  have hE:=linear_X (K:=K) w 0
  have hZ:=linear_X (K:=K) w 4
  fin_cases j
  · simpa [localize,hw0] using (linear_C w x).add (hE.mono (by omega))
  · simpa [localize] using linear_X (K:=K) w 1
  · have hU:LinearBound w (w 2)
        (MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4:Poly (K:=K)):=
      ((linear_C w u0).mono hw2).add (((linear_C w u1).mul hZ).mono (by omega))
    have hA:=linear_X (K:=K) w 2
    simpa [localize] using hU.add ((hE.mul hA).mono (by omega))
  · simpa [localize] using linear_X (K:=K) w 3
  · simpa [localize] using hZ

theorem BBM (w:Fin 5→ℤ) (hw0:w 0=0) (hw4:w 4=0)
    (hw2:0≤w 2) (x u0 u1:K) (e:Fin 5→₀ ℕ) (c:K):
    LinearBound w (weight w e) (localize x u0 u1 (MvPolynomial.monomial e c)):=by
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,map_mul,map_pow,map_C]
    have h0:=(CKY w hw0 hw4 hw2 x u0 u1 0).pow (e 0)
    have h1:=(CKY w hw0 hw4 hw2 x u0 u1 1).pow (e 1)
    have h2:=(CKY w hw0 hw4 hw2 x u0 u1 2).pow (e 2)
    have h3:=(CKY w hw0 hw4 hw2 x u0 u1 3).pow (e 3)
    have h4:=(CKY w hw0 hw4 hw2 x u0 u1 4).pow (e 4)
    simpa [weight,Fin.sum_univ_five,add_assoc] using
      (linear_C w c).mul (h0.mul (h1.mul (h2.mul (h3.mul h4))))
  · intro i
    simp

theorem FZA (x u0 u1:K) (e d:Fin 5→₀ ℕ) (c:K)
    (hd:d ∈ (localize x u0 u1 (MvPolynomial.monomial e c)).support):
    d 1=e 1∧2*d 1+d 3≤2*e 1+e 3∧d 1+d 2+d 3≤e 1+e 2+e 3:=by
  have hs:=BBM ![0,1,0,0,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hl:=BBM ![0,-1,0,0,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hB:=BBM ![0,2,0,1,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  have hM:=BBM ![0,1,1,1,0] (by rfl) (by rfl) (by decide) x u0 u1 e c d hd
  norm_num [weight,Fin.sum_univ_five,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four] at hs hl hB hM
  omega

theorem middle_cap (e:Fin 5→₀ ℕ) (w B D:ℕ) (hw:2≤w)
    (hB:2*e 1+e 3≤B)
    (hD:e 0+w*e 2+(w-1)*e 3+(w-2)*e 1<D):
    e 1+e 2+e 3≤(D+B-1)/w:=by
  apply (Nat.le_div_iff_mul_le (by omega:0<w)).mpr
  have h1:w-1+1=w:=by omega
  have h2:w-2+2=w:=by omega
  have hh:(e 1+e 2+e 3)*w<D+B:=by nlinarith
  omega

theorem DWW (x u0 u1:K) (m L B s U w:ℕ)
    (D:ℕ→ℕ) (hw:2≤w) (e:Fin 5→₀ ℕ) (c:K)
    (hB:2*e 1+e 3≤B) (hs:e 1≤s)
    (hU:e 1+e 2+e 3≤U) (hL:e 1+e 2+e 3+e 4≤L)
    (hD:e 0+w*e 2+(w-1)*e 3+(w-2)*e 1<D (e 1)):
    AFQ (K:=K) m (flatEquiv (K:=K)
      (localize x u0 u1 (MvPolynomial.monomial e c))) ∈
        ABQ.source (K:=K) m L B s U (fun h=>(D h+B-1)/w):=by
  rw [← DGT,ABQ.FKZ]
  simp only [AlgEquiv.symm_apply_apply]
  intro d hd
  obtain ⟨hm,hd'⟩:=EQF m _ d hd
  have hb:=FSX x u0 u1 e c d hd'
  obtain ⟨hS,hRS,hM⟩:=FZA x u0 u1 e d c hd'
  have hcap:=middle_cap e w B (D (e 1)) hw hB hD
  refine ⟨⟨hm,hb.1,by omega,by omega,hb.2.2.2.trans hL⟩,hRS.trans hB,hM.trans hU,?_⟩
  simpa only [hS] using hM.trans hcap

end
end ProximityPrize.SubmissionLower.BYD

end Compact_SecondJetRelaxedGlobalSupport

section Compact_SecondJetRelaxedGlobalMap

namespace ProximityPrize.SubmissionLower.EG
open scoped BigOperators
open DX VV HZ
open DLW (APX CMK)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I N:Type*} [Field K] [Fintype I] [Fintype N]

def rankBound (m L B s U:ℕ) (caps:ℕ→ℕ):ℕ:=
  Fintype.card (ABQ.Index m L B s U caps)-
    ∑ r:Fin m,∑ h:Fin (s+1),
      Fintype.card (AEB.Block m L B s U caps r.val h.val)

theorem EEU (m L B s U:ℕ) (caps:ℕ→ℕ):
    Module.finrank K (AEB.COQ (K:=K) m L B s U caps).range≤
      rankBound m L B s U caps:=by
  have hh:=AEB.GBK (K:=K) m L B s U caps
  unfold rankBound
  omega

theorem EAG (e:I→Fin 5→₀ ℕ) (m L B s U w:ℕ) (D:ℕ→ℕ)
    (hw:2≤w) (x u0 u1:K)
    (hB: ∀i,2*e i 1+e i 3≤B) (hs: ∀i,e i 1≤s)
    (hU: ∀i,e i 1+e i 2+e i 3≤U)
    (hL: ∀i,e i 1+e i 2+e i 3+e i 4≤L)
    (hD: ∀i,e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1<D (e i 1)) (c:I→K):
    APX e m x u0 u1 c ∈
      ABQ.source (K:=K) m L B s U (fun h=>(D h+B-1)/w):=by
  change AFQ (K:=K) m (flatEquiv (K:=K)
    (localize x u0 u1 (SC.reconstruct e c))) ∈ _
  rw [SC.CWA]
  simp_rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  exact BYD.DWW
    x u0 u1 m L B s U w D hw (e i) (c i) (hB i) (hs i) (hU i) (hL i) (hD i)

theorem FBQ (e:I→Fin 5→₀ ℕ) (he:Function.Injective e)
    (m L B s U w:ℕ) (D:ℕ→ℕ) (hw:2≤w)
    (hB: ∀i,2*e i 1+e i 3≤B) (hs: ∀i,e i 1≤s)
    (hU: ∀i,e i 1+e i 2+e i 3≤U)
    (hL: ∀i,e i 1+e i 2+e i 3+e i 4≤L)
    (hD: ∀i,e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1<D (e i 1))
    (x u0 u1:N→K)
    (hcard:Fintype.card N*rankBound m L B s U (fun h=>(D h+B-1)/w)<Fintype.card I):
    ∃P:Poly (K:=K),P ≠ 0∧(∀d ∈ P.support,d ∈ Set.range e)∧
      ∀n,Polynomial.X^m ∣ PX.contact (K:=K)
        (flatEquiv (K:=K) (localize (x n) (u0 n) (u1 n) P)):=by
  classical
  let caps:=fun h=>(D h+B-1)/w
  let f:=AEB.COQ (K:=K) m L B s U caps
  letI:AddCommGroup f.range:=inferInstance
  letI:Module K f.range:=f.range.module
  letI:FiniteDimensional K f.range:=by
    change FiniteDimensional K (AEB.COQ (K:=K) m L B s U caps).range
    infer_instance
  let ell (n:N):(I→K)→ₗ[K] ABQ.source (K:=K) m L B s U caps:=
    (APX e m (x n) (u0 n) (u1 n)).codRestrict _
      (EAG e m L B s U w D hw (x n) (u0 n) (u1 n) hB hs hU hL hD)
  let g:(I→K)→ₗ[K] (N→f.range):=
    LinearMap.pi (fun n=>f.rangeRestrict.comp (ell n))
  have hdim:Module.finrank K (N→f.range)≤Fintype.card N*rankBound m L B s U caps:=by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    exact Nat.mul_le_mul_left _ (EEU m L B s U caps)
  dsimp only [caps] at hdim
  have hrange:=g.range.finrank_le
  have hsum:=g.finrank_range_add_finrank_ker
  have hpos:0<Module.finrank K g.ker:=by
    have hdimI:Module.finrank K (I→K)=Fintype.card I:=by simp
    omega
  have hne:g.ker ≠ ⊥ :=by
    intro h
    rw [h] at hpos
    simp at hpos
  obtain ⟨c,hc,hc0⟩:=(Submodule.ne_bot_iff _).mp hne
  have hcz:g c=0:=LinearMap.mem_ker.mp hc
  refine ⟨SC.reconstruct e c,?_,?_,?_⟩
  · intro hz
    apply hc0
    apply SC.ABR e he
    simpa only [map_zero] using hz
  · exact (SC.mem_range_iff e he _).mp ⟨c,rfl⟩
  · intro n
    have hz:=congrArg Subtype.val (congrFun hcz n)
    change BMX.contactMap (K:=K) m (APX e m (x n) (u0 n) (u1 n) c)=0 at hz
    have hd:Polynomial.X^m ∣ PX.contact (K:=K)
        (APX e m (x n) (u0 n) (u1 n) c):=
      (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hz
    exact CMK (PX.contact (K:=K)).toRingHom Polynomial.X m _
      PX.contact_X hd

end
end ProximityPrize.SubmissionLower.EG

end Compact_SecondJetRelaxedGlobalMap

section Compact_SecondJetRelaxedCounts

namespace ProximityPrize.SubmissionLower.AR
open scoped BigOperators
open CBK CBH
noncomputable section
set_option autoImplicit false

def rankBound (m L B s U:ℕ):ℕ:=sourceCount m L B s U-kernelCount m L B s U

theorem IX (m L B s U:ℕ) (caps:ℕ→ℕ)
    (hsB:2*s≤B) (hBm:B≤m) (hU:m+s≤U) (hL:m+B+s≤L)
    (hcaps: ∀h,h≤s→U≤caps h):
    EG.rankBound m L B s U caps=rankBound m L B s U:=by
  unfold EG.rankBound rankBound
  rw [FNY m L B s U caps hsB hBm hU hL hcaps,
    GGV m L B s U caps hBm hU hL hcaps]

variable {K:Type*} [Field K]

end
end ProximityPrize.SubmissionLower.AR

end Compact_SecondJetRelaxedCounts

section Compact_SecondJetRelaxedGlobalIndex

namespace ProximityPrize.SubmissionLower.DD
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def budget (D:ℕ→ℕ) (w h r:ℕ):=D h-(w-2)*h-(w-1)*r
def yCount (D:ℕ→ℕ) (w U h r:ℕ):=
  min ((budget D w h r-1)/w+1) (U+1-h-r)
abbrev Index (D:ℕ→ℕ) (w L B s U:ℕ):=
  Σ h:Fin (s+1),Σ r:Fin (B-2*h.val+1),Σ y:Fin (yCount D w U h.val r.val),
    Fin (budget D w h.val r.val-w*y.val) × Fin (L+1-h.val-r.val-y.val)

def exponent {D:ℕ→ℕ} {w L B s U:ℕ} (i:Index D w L B s U):Fin 5→₀ ℕ:=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.2.1.val,i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

theorem ACD (D:ℕ→ℕ) (w L B s U:ℕ):
    Function.Injective (exponent (D:=D) (w:=w) (L:=L) (B:=B) (s:=s) (U:=U)):=by
  rintro ⟨h,r,y,x,z⟩ ⟨h',r',y',x',z'⟩ he
  have hv: ∀k:Fin 5,![x.val,h.val,y.val,r.val,z.val] k=
      ![x'.val,h'.val,y'.val,r'.val,z'.val] k:=by
    intro k
    simpa [exponent] using congrArg (fun d:Fin 5→₀ ℕ=>d k) he
  have hh:h=h' :=Fin.ext (hv 1)
  subst h'
  have hr:r=r' :=Fin.ext (hv 3)
  subst r'
  have hy:y=y' :=Fin.ext (hv 2)
  subst y'
  have hx:x=x' :=Fin.ext (hv 0)
  have hz:z=z' :=Fin.ext (hv 4)
  subst x'
  subst z'
  rfl

theorem BNO (D:ℕ→ℕ) (w L B s U:ℕ) (hsB:2*s≤B)
    (i:Index D w L B s U):
    2*exponent i 1+exponent i 3≤B∧exponent i 1≤s∧
      exponent i 1+exponent i 2+exponent i 3≤U∧
      exponent i 1+exponent i 2+exponent i 3+exponent i 4≤L∧
      exponent i 0+w*exponent i 2+(w-1)*exponent i 3+(w-2)*exponent i 1<D (exponent i 1):=by
  rcases i with ⟨h,r,y,x,z⟩
  have hh:=h.isLt
  have hr:=r.isLt
  have hy:=y.isLt
  have hx:=x.isLt
  have hz:=z.isLt
  simp only [budget] at hx
  simp only [yCount] at hy
  simp [exponent]
  omega

theorem card_index (D:ℕ→ℕ) (w L B s U:ℕ):
    Fintype.card (Index D w L B s U)=
      ∑ h:Fin (s+1),∑ r:Fin (B-2*h.val+1),∑ y:Fin (yCount D w U h.val r.val),
        (budget D w h.val r.val-w*y.val)*(L+1-h.val-r.val-y.val):=by
  simp [Index]

variable {K N:Type*} [Field K] [Fintype N]
theorem BQU (D:ℕ→ℕ) (w L B s U m:ℕ)
    (hsB:2*s≤B) (hw:2≤w) (x u0 u1:N→K)
    (hcard:Fintype.card N*EG.rankBound m L B s U
      (fun h=>(D h+B-1)/w)<Fintype.card (Index D w L B s U)):
    ∃P:DX.Poly (K:=K),P ≠ 0∧
      (∀d ∈ P.support,2*d 1+d 3≤B∧d 1≤s∧d 1+d 2+d 3≤U∧
        d 1+d 2+d 3+d 4≤L∧d 0+w*d 2+(w-1)*d 3+(w-2)*d 1<D (d 1))∧
      ∀n,Polynomial.X^m ∣ PX.contact (K:=K)
        (DX.flatEquiv (K:=K)
          (HZ.localize (x n) (u0 n) (u1 n) P)):=by
  obtain ⟨P,hP,hPex,hcontact⟩:=EG.FBQ
    exponent (ACD D w L B s U) m L B s U w D hw
    (fun i=>(BNO D w L B s U hsB i).1)
    (fun i=>(BNO D w L B s U hsB i).2.1)
    (fun i=>(BNO D w L B s U hsB i).2.2.1)
    (fun i=>(BNO D w L B s U hsB i).2.2.2.1)
    (fun i=>(BNO D w L B s U hsB i).2.2.2.2) x u0 u1 hcard
  refine ⟨P,hP,?_,hcontact⟩
  intro d hd
  obtain ⟨i,rfl⟩:=hPex d hd
  exact BNO D w L B s U hsB i

end
end ProximityPrize.SubmissionLower.DD

end Compact_SecondJetRelaxedGlobalIndex

section Compact_SecondJetRelaxedGlobalCounts

namespace ProximityPrize.SubmissionLower.AM
open scoped BigOperators
open DD
open CPV (weightedCell ESA)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem y_weight_le (D:ℕ→ℕ) (w U h r:ℕ) (y:Fin (yCount D w U h r)):
    w*y.val≤budget D w h r:=by
  have hy:y.val≤(budget D w h r-1)/w:=by
    have hh:=y.isLt
    unfold yCount at hh
    omega
  calc
    w*y.val≤w*((budget D w h r-1)/w):=Nat.mul_le_mul_left w hy
    _≤budget D w h r-1:=by
      simpa only [mul_comm] using Nat.div_mul_le_self (budget D w h r-1) w
    _≤budget D w h r:=Nat.sub_le _ _

def AW (D:ℕ→ℕ) (w L B s U:ℕ):ℕ:=
  ∑ h:Fin (s+1),∑ r:Fin (B-2*h.val+1),
    weightedCell (budget D w h.val r.val) w (L+1-h.val-r.val) (yCount D w U h.val r.val)

theorem JY (D:ℕ→ℕ) (w L B s U:ℕ) (hUL:U≤L):
    Fintype.card (Index D w L B s U)=AW D w L B s U:=by
  rw [card_index]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro r _
  apply ESA
  · exact y_weight_le D w U h.val r.val
  · intro y
    have hy:=y.isLt
    unfold yCount at hy
    omega

end
end ProximityPrize.SubmissionLower.AM

end Compact_SecondJetRelaxedGlobalCounts

section Compact_SecondJetRelaxedDifferentiation

namespace ProximityPrize.SubmissionLower.AQ
open MvPolynomial DX HZ IM
open KL HH
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N:Type*} [Field K]

def reserve (k n0 h:ℕ):ℕ:=if h<n0 then h else k

theorem GAR (k n0 h d:ℕ) (hdk:d≤k) (hdh:d≤h):
    d≤reserve k n0 h:=by
  unfold reserve
  split<;>assumption

theorem FVP (P:Poly (K:=K)) (m a w k n0 d:ℕ)
    (hwa:w-2≤a) (hdm:d≤m) (hdk:d≤k)
    (hP: ∀e ∈ P.support,
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+
        reserve k n0 (e 1)*(a-(w-2))<m*a)
    (e:Fin 5→₀ ℕ) (he:e ∈ ((pderiv 1)^[d] P).support):
    e 0+w*e 2+(w-1)*e 3+(w-2)*e 1<(m-d)*a:=by
  have hh:=hP _ (CAJ P d e he)
  simp [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  have hr:=GAR k n0 (e 1+d) d hdk (by omega)
  have hp:=Nat.mul_le_mul_right (a-(w-2)) hr
  have ha:a-(w-2)+(w-2)=a:=Nat.sub_add_cancel hwa
  have hm:(m-d)*a+d*a=m*a:=by
    rw [← Nat.add_mul,Nat.sub_add_cancel hdm]
  nlinarith

theorem AMU (P:Poly (K:=K)) (m a w k n0 d:ℕ)
    (ha:0<a) (hwa:w-2≤a) (hdm:d<m) (hdk:d≤k)
    (hP: ∀e ∈ P.support,
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+
        reserve k n0 (e 1)*(a-(w-2))<m*a)
    (nodes:N ↪ K) (u0 u1:N→K)
    (hcontact: ∀i,MvPolynomial.X 0^m ∣ substitute (K:=K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (f:Polynomial K) (hf:f.natDegree≤w) (z:K) (S:Finset N)
    (hS:a≤S.card) (hvalues: ∀i ∈ S,f.eval (nodes i)=u0 i+u1 i*z):
    specialize f z ((pderiv 1)^[d] P)=0:=by
  refine CAG.ALK _ f z nodes u0 u1 S (m-d) ?_ hvalues ?_
  · intro i _
    apply ADR (nodes i) (u0 i) (u1 i) P (m-d) d
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hcontact i
  · have hd:=DRK ((pderiv 1)^[d] P) f z w ((m-d)*a) hf (Nat.mul_pos (Nat.sub_pos_of_lt hdm) ha)
      (FVP P m a w k n0 d hwa (Nat.le_of_lt hdm) hdk hP)
    exact hd.trans_le (Nat.mul_le_mul_left (m-d) hS)

end
end ProximityPrize.SubmissionLower.AQ

end Compact_SecondJetRelaxedDifferentiation

section Compact_SecondJetRelaxedCoefficientsReceipt

namespace ProximityPrize.SubmissionLower.OH
open DD AM
open AQ
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end ProximityPrize.SubmissionLower.OH

end Compact_SecondJetRelaxedCoefficientsReceipt

section Compact_SecondJetRelaxedRanksReceipt

namespace ProximityPrize.SubmissionLower.DXC
open AR OH
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

end ProximityPrize.SubmissionLower.DXC

end Compact_SecondJetRelaxedRanksReceipt

section Compact_SecondJetRelaxedInterpolation

namespace ProximityPrize.SubmissionLower.WN
open MvPolynomial DX HZ HH IM
open OH AQ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N:Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.WN

end Compact_SecondJetRelaxedInterpolation

section Compact_SecondJetLeadingCoefficient

namespace ProximityPrize.SubmissionLower.EDM
open MvPolynomial DX HZ HH
open BX JQ IM
open AQ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N:Type*} [Field K]

end
end ProximityPrize.SubmissionLower.EDM

end Compact_SecondJetLeadingCoefficient

section Compact_SecondJetProperAlternatives

namespace ProximityPrize.SubmissionLower.AQE
open MvPolynomial DX BX JQ
open FR OR WN
open OH RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K N:Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.AQE

end Compact_SecondJetProperAlternatives

section Compact_SecondJetRounding

namespace ProximityPrize.SubmissionLower.FUE
set_option autoImplicit false

end ProximityPrize.SubmissionLower.FUE

end Compact_SecondJetRounding

section Compact_SecondJetCombinedCount

namespace ProximityPrize.SubmissionLower.EWI
open scoped Classical
open MvPolynomial RCN135 RCN136 RCN319 RCN327 RCN238 RCN222
open BX
open WN AQE AEF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {nodes:I ↪ K} {u0 u1:I→K}

end
end ProximityPrize.SubmissionLower.EWI

end Compact_SecondJetCombinedCount

section Compact_SecondJetNumericGeometry

namespace ProximityPrize.SubmissionLower.AIE
open RCN260 RCN095 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.AIE

end Compact_SecondJetNumericGeometry

section Compact_SecondJetOwnShape

namespace ProximityPrize.SubmissionLower.TI
open MvPolynomial RCN130 RCN234 RCN156 RCN095 RCN347 RCN135
open FA GJ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes:I ↪ K} {u0 u1:I→K}

theorem factorial_ne (d:ℕ) (hd:d<2130706433):(d.factorial:K) ≠ 0:=
  TJ 2130706433 d hd

theorem two_ne:(2:K) ≠ 0:=by
  have h:=factorial_ne (K:=K) 2 (by decide)
  simpa only [show Nat.factorial 2=2 by decide,Nat.cast_ofNat] using h

end
end ProximityPrize.SubmissionLower.TI

end Compact_SecondJetOwnShape

section Compact_SecondJetUniformReceipts

namespace ProximityPrize.SubmissionLower.DBL
open AIE RCN260 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.DBL

end Compact_SecondJetUniformReceipts

section Compact_SecondJetProperReceipts

namespace ProximityPrize.SubmissionLower.DHN
open AIE RCN260 RCN095 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.DHN

end Compact_SecondJetProperReceipts

section Compact_SecondJetProfileBounds

namespace ProximityPrize.SubmissionLower.EXI
open RCN135 TI
open AIE DBL WN
open DHN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes:I ↪ K} {u0 u1:I→K}
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433

end
end ProximityPrize.SubmissionLower.EXI

end Compact_SecondJetProfileBounds

section Compact_SecondJetAffineCeiling

namespace ProximityPrize.SubmissionLower.DOO
open RCN095
set_option autoImplicit false
set_option maxHeartbeats 2000000

end ProximityPrize.SubmissionLower.DOO

end Compact_SecondJetAffineCeiling

section Compact_SecondJetSingleCap

namespace ProximityPrize.SubmissionLower.FLN
open RCN095 DY
open TI DOO
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes:I ↪ K} {u0 u1:I→K}

end
end ProximityPrize.SubmissionLower.FLN

end Compact_SecondJetSingleCap

section Compact_SecondJetRowIntervals

namespace ProximityPrize.SubmissionLower.DSM
open FV
set_option autoImplicit false
set_option maxHeartbeats 3000000

def pickTail (z:ℕ) (a:BaseSegment):List BaseSegment→BaseSegment
  | []=>a
  | s::ss=>pickTail z (if s.start≤z then s else a) ss

def BaseCell (q:BaseRow) (lo hi:ℕ):Prop:=
  lo=hi∨(3≤lo∧match q.segments with
    | []=>True
    | a::ss=>a.start≤lo∧ ∀s ∈ ss,s.start≤lo∨hi<s.start)
instance (q:BaseRow) (lo hi:ℕ):Decidable (BaseCell q lo hi):=by
  unfold BaseCell
  cases q.segments<;>infer_instance

end ProximityPrize.SubmissionLower.DSM

end Compact_SecondJetRowIntervals
end
section
section MergedPart0
namespace ProximityPrize.SubmissionLower.Lower80850.Initial
open scoped BigOperators
open RCN095 DY
open FV (Potential rawFlag rawFlag_all AVF BTK
  sumFlag sumFlag_all AQT AXF)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end ProximityPrize.SubmissionLower.Lower80850.Initial
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.AFH
open MvPolynomial DX BX RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K:Type*} [Field K]

theorem ENG (P:Poly (K:=K)) (L j:ℕ)
    (hP: ∀e ∈ P.support,e 1+e 2+e 3+e 4≤L):
    wt AT ((asS P).coeff j)≤L-j:=by
  apply (RCN081.KN _ _ _).mpr
  intro e he
  have hh:=hP _ (AJU P j e he)
  obtain ⟨h0,h1,h2,h3,h4⟩:=_Q17 j e
  rw [h1,h2,h3,h4] at hh
  simp [AT,RCN081.weight_fin4]
  omega

theorem FHJ (P:Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (L j:ℕ) (hP: ∀e ∈ P.support,e 1+e 2+e 3+e 4≤L)
    (hF:L<wt AT F) (hC:(asS P).coeff j ≠ 0):
    ¬F ∣ (asS P).coeff j:=by
  intro hdiv
  have hh:=RCN081.IQ AT F
    ((asS P).coeff j) hdiv hC
  have hc:=ENG P L j hP
  change wt AT F≤wt AT ((asS P).coeff j) at hh
  omega

theorem CAK (P:Poly (K:=K)) (hP:P ≠ 0)
    (F:MvPolynomial (Fin 4) K) (L:ℕ)
    (hPL: ∀e ∈ P.support,e 1+e 2+e 3+e 4≤L)
    (hF:L<wt AT F):
    (asS P).leadingCoeff ≠ 0∧ ¬F ∣ (asS P).leadingCoeff:=by
  have hn:asS P ≠ 0:=by
    intro hz
    apply hP
    apply (asS (K:=K)).injective
    simpa only [map_zero] using hz
  have hc:=Polynomial.leadingCoeff_ne_zero.mpr hn
  exact ⟨hc,FHJ P F L (asS P).natDegree hPL hF hc⟩

open JQ FR OR
open WN OH AQE
variable {N:Type*} [Fintype N]

end
end ProximityPrize.SubmissionLower.AFH

namespace ProximityPrize.SubmissionLower.ZM
open RCN260 RCN052 RCN294

theorem DUQ {K:Type} [Field K]
    (P:DG) (F:MvPolynomial (Fin 4) K)
    (hY:F.degreeOf 1≤P.leftY) (hR:F.degreeOf 2≤P.leftR)
    (hZ:F.degreeOf 3≤P.leftZ) (count:ℕ) (hgap:0<P.gap)
    (hc:count*P.gap≤(P.n-P.w)*dot P.KO (OX P F)+
      (P.errors+1)*P.gap*(OX P F).z):
    count≤GB.FU P:=by
  have hv:=KI.CRA P F hY hR hZ
  have hdot:dot P.KO (OX P F)≤dot P.KO P.mixedCost:=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.KO.y hv.1)
        (Nat.mul_le_mul_left P.KO.r hv.2.1))
      (Nat.mul_le_mul_left P.KO.z hv.2.2)
  apply (Nat.le_div_iff_mul_le hgap).mpr
  exact hc.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n-P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors+1)*P.gap) hv.2.2))

end ProximityPrize.SubmissionLower.ZM

namespace ProximityPrize.SubmissionLower.CWX.Data
open MvPolynomial RCN319 RCN260 RCN327
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {nodes:I ↪ K} {u0 u1:I→K}

end
end ProximityPrize.SubmissionLower.CWX.Data

namespace ProximityPrize.SubmissionLower.FHY
open scoped Classical
open MvPolynomial RCN135 RCN136 RCN319 RCN327 RCN238 RCN222 RCN234 RCN156
open BX
open WN AQE AEF
open GB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {nodes:I ↪ K} {u0 u1:I→K}

end
end ProximityPrize.SubmissionLower.FHY

namespace ProximityPrize.SubmissionLower.TI
open MvPolynomial RCN130 RCN234 RCN156 RCN095 RCN347 RCN135
noncomputable section
set_option autoImplicit false
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes:I ↪ K} {u0 u1:I→K}

end
end ProximityPrize.SubmissionLower.TI

namespace ProximityPrize.SubmissionLower.FIJ
open DD AM AR
open OH WN
open AIE RCN260 RCN294 RCN135
open TI
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes:I ↪ K} {u0 u1:I→K}
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433

end
end ProximityPrize.SubmissionLower.FIJ

namespace ProximityPrize.SubmissionLower.DER
open RCN095 RCN260 RCN294 GB AIE
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end ProximityPrize.SubmissionLower.DER

namespace ProximityPrize.SubmissionLower.DER
open RCN130 RCN234 RCN156 RCN347 TI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes:I ↪ K} {u0 u1:I→K}

end
end ProximityPrize.SubmissionLower.DER
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.BAA
open IM
open MvPolynomial DX HZ HH
open OH AQ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
variable {K N:Type*} [Field K] [Fintype N]







end
end ProximityPrize.SubmissionLower.BAA
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.EK
set_option autoImplicit false

structure Carrier where
  c0:ℕ
  c1:ℕ
  c2:ℕ
  c3:ℕ
  c4:ℕ
  deriving DecidableEq,Repr

structure Run where
  stop:ℕ
  who:ℕ
  deriving DecidableEq,Repr

end ProximityPrize.SubmissionLower.EK

namespace ProximityPrize.SubmissionLower.Lower80899.PhaseRows
set_option autoImplicit false

structure PhaseRun where
  stop:ℕ
  witness:ℕ
  deriving DecidableEq,Repr

end ProximityPrize.SubmissionLower.Lower80899.PhaseRows

namespace ProximityPrize.SubmissionLower.Lower80899.LedgerAudit
set_option autoImplicit false

structure LedgerRun where
  stop:ℕ
  witness:ℕ
  mode:ℕ
  deriving DecidableEq,Repr

end ProximityPrize.SubmissionLower.Lower80899.LedgerAudit

namespace ProximityPrize.SubmissionLower.Lower80899.BLW
set_option autoImplicit false

structure Run where
  stop:ℕ
  code:ℕ
  deriving DecidableEq,Repr

end ProximityPrize.SubmissionLower.Lower80899.BLW

namespace ProximityPrize.SubmissionLower.EAY
open FV Lower80899.PhaseRows
set_option autoImplicit false

structure BaseRun where
  stop:Nat
  sheet:Nat
  deriving DecidableEq,Repr

structure Numbers where
  carrier:EK.Carrier
  base:BaseRow
  threshold:Array Nat
  prefixValues:Array Nat
  singletons:List EK.Run
  baseChoices:List BaseRun
  phaseRuns:Array (List PhaseRun)
  ledgerRuns:List Lower80899.LedgerAudit.LedgerRun
  thresholdRuns:Array (List Lower80899.BLW.Run)

end ProximityPrize.SubmissionLower.EAY
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.JR
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RZ IL
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
namespace A


end A
namespace B
theorem OS:AW 30085010 131071 17230 50=2420604005349470:=by
  rw [show 30085010=229*131071+69751 by decide+kernel]
  rw [GQ 229 69751 131071 17230 50
    (by decide+kernel) (by decide+kernel) (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem rank_exact:ES 166 17230 50=9233870586:=by
  rw [ClosedRank.RU _ _ _ (by decide+kernel) (by decide+kernel)]
  decide+kernel
end B
namespace TCap
theorem OS:AW 45671220 131071 11785 78=5823903988049800:=by
  rw [show 45671220=348*131071+58512 by decide+kernel]
  rw [GQ 348 58512 131071 11785 78
    (by decide+kernel) (by decide+kernel) (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem rank_exact:ES 252 11785 78=22216422107:=by
  rw [ClosedRank.RU _ _ _ (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem AJI:AW 45671220 131071 11785 78-262144*ES 252 11785 78=2231232392:=by
  norm_num only [OS,rank_exact]
theorem FGK:AW 45671220 131071 0 78=45671220:=by decide+kernel
theorem FPR:AW 45671220 131071 0 78<2231232392:=by rw [FGK];decide+kernel
end TCap
namespace Source00
theorem OS:AW 11598846163 131071 3840000 19840=30703246203056482477568417:=by
  rw [show 11598846163=88492*131071+111231 by decide+kernel]
  rw [GQ 88492 111231 131071 3840000 19840
    (by decide+kernel) (by decide+kernel) (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem rank_exact:ES 63999 3840000 19840=116780376202356671680:=by
  rw [ClosedRank.RU _ _ _ (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem AJI:AW 11598846163 131071 3840000 19840-262144*ES 63999 3840000 19840=89971263865895136686497:=by
  norm_num only [OS,rank_exact]
theorem AJG:89971263865895136686497≤AW 11598846163 131071 3840000 19840-262144*ES 63999 3840000 19840:=by rw [AJI]
theorem shape:11598846163+19840≤131071*(88497+1):=by decide+kernel
theorem finrank_gap (u0 u1:IRSProfile.Index→IRSProfile.Field):
    89971263865895136686497≤Module.finrank IRSProfile.Field (IJ (K:=IRSProfile.Field) 11598846163 131071 3840000 19840 63999 IRSProfile.domain u0 u1):=
  KJ 11598846163 3840000 19840 63999 89971263865895136686497 u0 u1 AJG
end Source00
namespace Source01
theorem OS:AW 5799520000 131071 3200000 9888=3202673490115626486546488:=by
  rw [show 5799520000=44247*131071+21463 by decide+kernel]
  rw [GQ 44247 21463 131071 3200000 9888
    (by decide+kernel) (by decide+kernel) (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem rank_exact:ES 32000 3200000 9888=12172764924613929328:=by
  rw [ClosedRank.RU _ _ _ (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem AJI:AW 5799520000 131071 3200000 9888-262144*ES 32000 3200000 9888=11656201717632596787256:=by
  norm_num only [OS,rank_exact]
theorem AJG:11656201717632596787256≤AW 5799520000 131071 3200000 9888-262144*ES 32000 3200000 9888:=by rw [AJI]
theorem shape:5799520000+9888≤131071*(44249+1):=by decide+kernel
theorem finrank_gap (u0 u1:IRSProfile.Index→IRSProfile.Field):
    11656201717632596787256≤Module.finrank IRSProfile.Field (IJ (K:=IRSProfile.Field) 5799520000 131071 3200000 9888 32000 IRSProfile.domain u0 u1):=
  KJ 5799520000 3200000 9888 32000 11656201717632596787256 u0 u1 AJG
end Source01
namespace Source02
theorem OS:AW 5799520000 131071 2880000 9888=2880617853929807211026488:=by
  rw [show 5799520000=44247*131071+21463 by decide+kernel]
  rw [GQ 44247 21463 131071 2880000 9888
    (by decide+kernel) (by decide+kernel) (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem rank_exact:ES 32000 2880000 9888=10950008283031849328:=by
  rw [ClosedRank.RU _ _ _ (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem AJI:AW 5799520000 131071 2880000 9888-262144*ES 32000 2880000 9888=10138882582706100787256:=by
  norm_num only [OS,rank_exact]
theorem AJG:10138882582706100787256≤AW 5799520000 131071 2880000 9888-262144*ES 32000 2880000 9888:=by rw [AJI]
theorem shape:5799520000+9888≤131071*(44249+1):=by decide+kernel
theorem finrank_gap (u0 u1:IRSProfile.Index→IRSProfile.Field):
    10138882582706100787256≤Module.finrank IRSProfile.Field (IJ (K:=IRSProfile.Field) 5799520000 131071 2880000 9888 32000 IRSProfile.domain u0 u1):=
  KJ 5799520000 2880000 9888 32000 10138882582706100787256 u0 u1 AJG
end Source02
namespace Source03
theorem OS:AW 2899760000 131071 1062000 4940=132420707973271972421613:=by
  rw [show 2899760000=22123*131071+76267 by decide+kernel]
  rw [GQ 22123 76267 131071 1062000 4940
    (by decide+kernel) (by decide+kernel) (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem rank_exact:ES 16000 1062000 4940=503593395806461590:=by
  rw [ClosedRank.RU _ _ _ (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem AJI:AW 2899760000 131071 1062000 4940-262144*ES 16000 1062000 4940=406720822982905372653:=by
  norm_num only [OS,rank_exact]
theorem AJG:406720822982905372653≤AW 2899760000 131071 1062000 4940-262144*ES 16000 1062000 4940:=by rw [AJI]
theorem shape:2899760000+4940≤131071*(22124+1):=by decide+kernel
theorem finrank_gap (u0 u1:IRSProfile.Index→IRSProfile.Field):
    406720822982905372653≤Module.finrank IRSProfile.Field (IJ (K:=IRSProfile.Field) 2899760000 131071 1062000 4940 16000 IRSProfile.domain u0 u1):=
  KJ 2899760000 1062000 4940 16000 406720822982905372653 u0 u1 AJG
end Source03
namespace Source04
theorem OS:AW 1449880000 131071 531000 2470=8278416685988322110125:=by
  rw [show 1449880000=11061*131071+103669 by decide+kernel]
  rw [GQ 11061 103669 131071 531000 2470
    (by decide+kernel) (by decide+kernel) (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem rank_exact:ES 8000 531000 2470=31483869872329770:=by
  rw [ClosedRank.RU _ _ _ (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem AJI:AW 1449880000 131071 531000 2470-262144*ES 8000 531000 2470=25109102176306883245:=by
  norm_num only [OS,rank_exact]
theorem AJG:25109102176306883245≤AW 1449880000 131071 531000 2470-262144*ES 8000 531000 2470:=by rw [AJI]
theorem shape:1449880000+2470≤131071*(11062+1):=by decide+kernel
theorem finrank_gap (u0 u1:IRSProfile.Index→IRSProfile.Field):
    25109102176306883245≤Module.finrank IRSProfile.Field (IJ (K:=IRSProfile.Field) 1449880000 131071 531000 2470 8000 IRSProfile.domain u0 u1):=
  KJ 1449880000 531000 2470 8000 25109102176306883245 u0 u1 AJG
end Source04
namespace Source05
theorem OS:AW 181235000 131071 88902 308=2717547762635542235:=by
  rw [show 181235000=1382*131071+94878 by decide+kernel]
  rw [GQ 1382 94878 131071 88902 308
    (by decide+kernel) (by decide+kernel) (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem rank_exact:ES 1000 88902 308=10336494078526:=by
  rw [ClosedRank.RU _ _ _ (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem AJI:AW 181235000 131071 88902 308-262144*ES 1000 88902 308=7897858914422491:=by
  norm_num only [OS,rank_exact]
theorem AJG:7897858914422491≤AW 181235000 131071 88902 308-262144*ES 1000 88902 308:=by rw [AJI]
theorem shape:181235000+308≤131071*(1382+1):=by decide+kernel
theorem finrank_gap (u0 u1:IRSProfile.Index→IRSProfile.Field):
    7897858914422491≤Module.finrank IRSProfile.Field (IJ (K:=IRSProfile.Field) 181235000 131071 88902 308 1000 IRSProfile.domain u0 u1):=
  KJ 181235000 88902 308 1000 7897858914422491 u0 u1 AJG
end Source05
namespace Source06
theorem OS:AW 2537290000 131071 3640000 4267=302982957217690639276805:=by
  rw [show 2537290000=19358*131071+17582 by decide+kernel]
  rw [GQ 19358 17582 131071 3640000 4267
    (by decide+kernel) (by decide+kernel) (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem rank_exact:ES 14000 3640000 4267=1150877542707512224:=by
  rw [ClosedRank.RU _ _ _ (by decide+kernel) (by decide+kernel)]
  decide+kernel
theorem AJI:AW 2537290000 131071 3640000 4267-262144*ES 14000 3640000 4267=1287314662172554828549:=by
  norm_num only [OS,rank_exact]
theorem AJG:1287314662172554828549≤AW 2537290000 131071 3640000 4267-262144*ES 14000 3640000 4267:=by rw [AJI]
theorem shape:2537290000+4267≤131071*(19359+1):=by decide+kernel
theorem finrank_gap (u0 u1:IRSProfile.Index→IRSProfile.Field):
    1287314662172554828549≤Module.finrank IRSProfile.Field (IJ (K:=IRSProfile.Field) 2537290000 131071 3640000 4267 14000 IRSProfile.domain u0 u1):=
  KJ 2537290000 3640000 4267 14000 1287314662172554828549 u0 u1 AJG
end Source06
end ProximityPrize.SubmissionLower.JR
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.Lower80899.FactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open KI IL

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

def helperPair (L YS S leftY leftR leftZ:ℕ):DG:=
  ⟨262144,131071,181235,leftY,leftR,leftZ,YS,S,L⟩

def LX (L YS S leftY leftR leftZ:ℕ):Prop:=
  let P:=helperPair L YS S leftY leftR leftZ
  1≤P.leftR∧P.leftY<2130706433∧P.leftR<2130706433∧
    P.leftZ<2130706433∧P.mixedCost.y<2130706433∧
    P.mixedCost.r<2130706433∧P.mixedCost.z<2130706433

private theorem AKD (Q:P4):
    Q.degreeOf (1:Fin 4)≤wt BC Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree BC hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0≤
    wt BC Q at h
  omega

private theorem BAM (Q:P4):
    Q.degreeOf (2:Fin 4)≤wt BE Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree BE hd
  rw [weight_fin4] at h
  change d 0*0+d 1*0+d 2*1+d 3*0≤
    wt BE Q at h
  omega

private theorem ADI (Q:P4):
    Q.degreeOf (3:Fin 4)≤wt AT Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree AT hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1≤
    wt AT Q at h
  omega

theorem DKV
    (D L S m YS:ℕ) (hD:0<D) (hDa:D≤m*181235)
    (hshape:D+S≤131071*(YS+1))
    {u0 u1:I→K} {H:P4}
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (F:RegularIndex H) (leftY leftR leftZ:ℕ)
    (hFY:F.1.degreeOf 1≤leftY)
    (hFR:F.1.degreeOf 2≤leftR)
    (hFZ:F.1.degreeOf 3≤leftZ)
    (hgates:LX L YS S leftY leftR leftZ):
    (∀v:IJ (K:=K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 L S v.1)∨
      (regularSeeds H selected Gamma F).card≤
        GB.FU (helperPair L YS S leftY leftR leftZ):=by
  classical
  by_cases hdiv: ∀v:IJ (K:=K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 L S v.1
  · exact Or.inl hdiv
  · right
    push Not at hdiv
    obtain ⟨v,hv⟩:=hdiv
    let Q:=reconstruct K D 131071 L S v.1
    have hF:=RCN167.KR H F.1 F.2
    have hrel:IsRelPrime F.1 Q:=
      hF.1.isRelPrime_iff_not_dvd.mpr hv
    have hQbox:Q ∈ BA K D 131071 L S:=
      LG K D 131071 L S v.1
    have hQYS:wt BC Q≤YS:=by
      apply EQT D 131071 L S YS (by decide) hshape Q hQbox
    have hweights:=(JT Q
      D 131071 L S hD).mp hQbox
    have hQY:Q.degreeOf 1≤YS:=
      (AKD Q).trans hQYS
    have hQR:Q.degreeOf 2≤S:=
      (BAM Q).trans hweights.2.1
    have hQZ:Q.degreeOf 3≤L:=
      (ADI Q).trans hweights.1
    obtain ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
      hmixedYSmall,hmixedRSmall,hmixedZSmall⟩:=hgates
    apply GB.ZF
      (helperPair L YS S leftY leftR leftZ) H Q F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall
      selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by
        change (Finset.univ:Finset I).card=262144
        rw [Finset.card_univ]
        exact Fintype.card_fin _)
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by simpa only [helperPair] using hdegree)
      (by simpa only [helperPair] using hagreement)
      (by simpa only [helperPair,DG.errors,(show (262144-181235:ℕ)=80909 by decide+kernel)] using hno)
    intro gamma hgamma
    dsimp only [Q]
    apply BIY K
      D 131071 L S m IRSProfile.domain u0 u1
      v.1 v.2 (selected gamma) gamma
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i))
    · exact hD
    · exact hdegree gamma (Finset.mem_filter.mp hgamma).1
    · exact hDa.trans (Nat.mul_le_mul_left m
        (hagreement gamma (Finset.mem_filter.mp hgamma).1))
    · intro i hi
      exact (Finset.mem_filter.mp hi).2

end

end ProximityPrize.SubmissionLower.Lower80899.FactorSwitch

namespace ProximityPrize.SubmissionLower.Lower80899.PowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open KI IL
open CS TB
open Lower80899.FactorSwitch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

structure DTX where
  tLo:ℕ
  tHi:ℕ
  yLo:ℕ
  yHi:ℕ
  rLo:ℕ
  rHi:ℕ
  deriving DecidableEq

def stagePair (L YS S:ℕ) (b:DTX) (j:ℕ):
    DG:=
  helperPair (L-j*b.tLo) (YS-j*b.yLo) (S-j*b.rLo)
    b.yHi b.rHi b.tHi

def stageCost (L YS S:ℕ) (b:DTX) (j:ℕ):ℕ:=
  GB.FU (stagePair L YS S b j)

private theorem AKD (Q:P4):
    Q.degreeOf (1:Fin 4)≤wt BC Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree BC hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0≤
    wt BC Q at h
  omega

private theorem BAM (Q:P4):
    Q.degreeOf (2:Fin 4)≤wt BE Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree BE hd
  rw [weight_fin4] at h
  change d 0*0+d 1*0+d 2*1+d 3*0≤
    wt BE Q at h
  omega

private theorem ADI (Q:P4):
    Q.degreeOf (3:Fin 4)≤wt AT Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree AT hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1≤
    wt AT Q at h
  omega

theorem DMN
    (L YS S:ℕ) (b:DTX) (j:ℕ)
    (u0 u1:I→K) (H:P4) (selected:K→Polynomial K)
    (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (F:RegularIndex H)
    (hFY:F.1.degreeOf 1≤b.yHi)
    (hFR:F.1.degreeOf 2≤b.rHi)
    (hFZ:F.1.degreeOf 3≤b.tHi)
    (Q:P4)
    (hQT:wt AT Q≤L-j*b.tLo)
    (hQY:wt BC Q≤YS-j*b.yLo)
    (hQR:wt BE Q≤S-j*b.rLo)
    (hrel:IsRelPrime F.1 Q)
    (hgates:LX (L-j*b.tLo) (YS-j*b.yLo)
      (S-j*b.rLo) b.yHi b.rHi b.tHi)
    (hQzero: ∀gamma ∈ regularSeeds H selected Gamma F,
      RCN319.BM K (selected gamma) gamma Q=0):
    (regularSeeds H selected Gamma F).card≤stageCost L YS S b j:=by
  have hQY' :Q.degreeOf 1≤(stagePair L YS S b j).rightY:=by
    simpa only [stagePair,helperPair] using (AKD Q).trans hQY
  have hQR' :Q.degreeOf 2≤(stagePair L YS S b j).rightR:=by
    simpa only [stagePair,helperPair] using (BAM Q).trans hQR
  have hQZ:Q.degreeOf 3≤(stagePair L YS S b j).rightZ:=by
    simpa only [stagePair,helperPair] using (ADI Q).trans hQT
  obtain ⟨hleftR,hleftYSmall,hleftRSmall,hleftZSmall,
    hmixedYSmall,hmixedRSmall,hmixedZSmall⟩:=hgates
  have hcount:=GB.ZF
    (stagePair L YS S b j) H Q F hrel 2130706433
    (by simpa only [stagePair,helperPair] using hFY)
    (by simpa only [stagePair,helperPair] using hFR)
    (by simpa only [stagePair,helperPair] using hFZ)
    hQY' hQR' hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
    (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ:Finset I).card=262144
      rw [Finset.card_univ]
      exact Fintype.card_fin _)
    (by norm_num [stagePair,helperPair])
    (by norm_num [stagePair,helperPair])
    (by norm_num [stagePair,helperPair])
    (by norm_num [stagePair,helperPair])
    hdegree hagreement
    (by simpa only [stagePair,helperPair,DG.errors,
      (show (262144-181235:ℕ)=80909 by decide+kernel)] using hno)
    hQzero
  simpa only [stageCost] using hcount

end

end ProximityPrize.SubmissionLower.Lower80899.PowerRoute

namespace ProximityPrize.SubmissionLower.Lower80899.AGR

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open IL KI CS TB Lower80899.FactorSwitch Lower80899.PowerRoute KZ

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

def LP {H:P4} (F:RegularIndex H):DTX where
  tLo:=wt AT F.1
  tHi:=wt AT F.1
  yLo:=wt BC F.1
  yHi:=wt BC F.1
  rLo:=wt BE F.1
  rHi:=wt BE F.1

private theorem AKD (Q:P4):
    Q.degreeOf (1:Fin 4)≤wt BC Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree BC hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0≤
    wt BC Q at h
  omega

private theorem BAM (Q:P4):
    Q.degreeOf (2:Fin 4)≤wt BE Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree BE hd
  rw [weight_fin4] at h
  change d 0*0+d 1*0+d 2*1+d 3*0≤
    wt BE Q at h
  omega

private theorem ADI (Q:P4):
    Q.degreeOf (3:Fin 4)≤wt AT Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree AT hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1≤
    wt AT Q at h
  omega

theorem CXN
    {D Dlow L S m j:ℕ} (u0 u1:I→K)
    (v:IJ (K:=K) D 131071 L S m
      IRSProfile.domain u0 u1)
    (P J:P4)
    (heq:P^j*J=reconstruct K D 131071 L S v.1)
    (hD:0<D) (hDlow:0<Dlow)
    (hcontact:wt (BV 131071) J<
      Dlow-j*wt (BV 131071) P):
    reconstruct K D 131071 L S v.1 ∈
      BA K Dlow 131071 L S:=by
  have hsource:=(JT
    (reconstruct K D 131071 L S v.1) D 131071 L S hD).mp
      (LG K D 131071 L S v.1)
  apply (JT
    (reconstruct K D 131071 L S v.1) Dlow 131071 L S hDlow).mpr
  refine ⟨hsource.1,hsource.2.1,?_⟩
  rw [← heq]
  have hmul:=wt_mul_le (BV 131071) (P^j) J
  have hp:=wt_pow_le (BV 131071) P j
  omega

theorem EOW
    (D L S m YS delta fuel:ℕ)
    (hD:0<D) (hfuelChar:fuel<2130706433)
    (hlowpos: ∀j,1≤j→j≤fuel→0<D-j*delta)
    (hcapacity: ∀j,1≤j→j≤fuel→
      D-j*delta≤(m-j)*181235+j*(131071-1))
    (u0 u1:I→K) (H:P4)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,
      (selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (A:Finset (RegularIndex H))
    (q:IJ (K:=K) D 131071 L S m
        IRSProfile.domain u0 u1→ₗ[K] P4)
    (hproduct: ∀v,
      reconstruct K D 131071 L S v.1=CK H A*q v)
    (hexit:DUW fuel
      (D-delta-wt (BV 131071) (CK H A))
      131071 delta
      (L-wt AT (CK H A))
      (YS-wt BC (CK H A))
      (S-wt BE (CK H A)) H A q)
    (hfeasible:
      fuel*wt AT (CK H A)≤L∧
      fuel*wt BC (CK H A)≤YS∧
      fuel*wt BE (CK H A)≤S)
    (hgates: ∀F ∈ A,∀j,1≤j→j≤fuel→
      LX
        (L-j*wt AT F.1)
        (YS-j*wt BC F.1)
        (S-j*wt BE F.1)
        (wt BC F.1) (wt BE F.1)
        (wt AT F.1))
    (charge:RegularIndex H→ℕ)
    (hcharge: ∀F ∈ A,∀j,1≤j→j≤fuel→
      stageCost L YS S (LP F) j≤charge F):
    ∃U,U ⊂ A∧ ∀F ∈ A \ U,
      (regularSeeds H selected Gamma F).card≤charge F:=by
  classical
  let P:=CK H A
  change DUW fuel
      (D-delta-wt (BV 131071) P) 131071 delta
      (L-wt AT P) (YS-wt BC P)
      (S-wt BE P) H A q at hexit
  obtain ⟨e,U,v,J,hUA,hv,hJ,heq,hbox,havoid⟩:=hexit
  let j:=e.val+1
  have hj:1≤j:=by simp only [j];omega
  have hjle:j≤fuel:=by simp only [j];omega
  have hjchar:j<2130706433:=hjle.trans_lt hfuelChar
  have heqOriginal:P^j*J=
      reconstruct K D 131071 L S v.1:=by
    calc
      P^j*J=P*(P^e.val*J):=by
        simp only [j,pow_succ']
        ring
      _=P*q v:=by rw [heq]
      _=reconstruct K D 131071 L S v.1:=(hproduct v).symm
  change J ∈ PQ K
      (D-delta-wt (BV 131071) P-e.val*delta-
        e.val*wt (BV 131071) P) 131071
      (L-wt AT P-e.val*wt AT P)
      (YS-wt BC P-e.val*wt BC P)
      (S-wt BE P-e.val*wt BE P) at hbox
  have hweights:=DLI hbox hJ
  have hJT:wt AT J≤
      L-j*wt AT P:=by
    simpa only [j,Nat.sub_sub,Nat.add_mul,one_mul,Nat.add_comm] using
      hweights.1
  have hJY:wt BC J≤
      YS-j*wt BC P:=by
    simpa only [j,Nat.sub_sub,Nat.add_mul,one_mul,Nat.add_comm] using
      hweights.2.1
  have hJS:wt BE J≤
      S-j*wt BE P:=by
    simpa only [j,Nat.sub_sub,Nat.add_mul,one_mul,Nat.add_comm] using
      hweights.2.2.1
  have hJcontact:wt (BV 131071) J<
      D-j*delta-j*wt (BV 131071) P:=by
    have hc:=hweights.2.2.2
    simp only [j,Nat.sub_sub,Nat.add_mul,one_mul] at hc ⊢
    omega
  have hlow:reconstruct K D 131071 L S v.1 ∈
      BA K (D-j*delta) 131071 L S:=
    CXN u0 u1 v P J heqOriginal hD
      (hlowpos j hj hjle) hJcontact
  have hPT:j*wt AT P≤L:=
    (Nat.mul_le_mul_right (wt AT P) hjle).trans hfeasible.1
  have hPY:j*wt BC P≤YS:=
    (Nat.mul_le_mul_right (wt BC P) hjle).trans hfeasible.2.1
  have hPS:j*wt BE P≤S:=
    (Nat.mul_le_mul_right (wt BE P) hjle).trans hfeasible.2.2
  refine ⟨U,hUA,?_⟩
  intro F hFU
  have hFA:F ∈ A:=(Finset.mem_sdiff.mp hFU).1
  let QF:=WR H A F^j*J
  have hQF:QF ≠ 0:=by
    exact mul_ne_zero (pow_ne_zero j (DKE H A F)) hJ
  have hrel:IsRelPrime F.1 QF:=by
    exact COG H A F hFA j J
      (havoid F hFU)
  have hQbounds:=DWV H A F hFA L YS S j J hJ
    hJT hJY hJS hPT hPY hPS
  have hQzero: ∀gamma ∈ regularSeeds H selected Gamma F,
      BM K (selected gamma) gamma QF=0:=by
    exact DFY j D (D-j*delta) 131071
      L S m 181235 2130706433
      (CharP.char_prime_of_ne_zero (R:=K) (by norm_num))
      IRSProfile.domain u0 u1 H A F hFA selected Gamma v J hj hjchar
      (by decide) hdegree hagreement (hcapacity j hj hjle) hlow
      heqOriginal
  have hstage:=DMN L YS S
    (LP F) j u0 u1 H selected Gamma hdegree hagreement hno F
    (AKD F.1) (BAM F.1)
    (ADI F.1) QF
    (by simpa only [LP] using hQbounds.1)
    (by simpa only [LP] using hQbounds.2.1)
    (by simpa only [LP] using hQbounds.2.2)
    hrel (by simpa only [LP] using hgates F hFA j hj hjle)
    hQzero
  exact hstage.trans (hcharge F hFA j hj hjle)

theorem AAA
    (D L S m YS gap delta fuel:ℕ)
    (hD:0<D) (hDa:D≤m*181235)
    (hshape:D+S≤131071*(YS+1))
    (hfuel:1≤fuel) (hfuelChar:fuel<2130706433)
    (hlowpos: ∀j,1≤j→j≤fuel→0<D-j*delta)
    (hcapacity: ∀j,1≤j→j≤fuel→
      D-j*delta≤(m-j)*181235+j*(131071-1))
    (u0 u1:I→K) (H:P4)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,
      (selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (A:Finset (RegularIndex H)) (hA:A.Nonempty)
    (hbandThin:CS.HN 131071
      (D-wt (BV 131071) (CK H A)) delta
      (wt (BV 131071) (CK H A))
      (wt AT (CK H A))
      (wt BC (CK H A))
      (wt BE (CK H A))
      (L-wt AT (CK H A))
      (YS-wt BC (CK H A))
      (S-wt BE (CK H A)) fuel<gap)
    (hterminal:
      L-fuel*wt AT (CK H A)<
          wt AT (CK H A)∨
      YS-fuel*wt BC (CK H A)<
          wt BC (CK H A)∨
      S-fuel*wt BE (CK H A)<
          wt BE (CK H A))
    (hfeasible:
      fuel*wt AT (CK H A)≤L∧
      fuel*wt BC (CK H A)≤YS∧
      fuel*wt BE (CK H A)≤S)
    (hgapLe:gap≤Module.finrank K
      (IJ (K:=K) D 131071 L S m
        IRSProfile.domain u0 u1))
    (hfield:A.card<ENat.card K)
    (hgates: ∀F ∈ A,∀j,j≤fuel→
      LX
        (L-j*wt AT F.1)
        (YS-j*wt BC F.1)
        (S-j*wt BE F.1)
        (wt BC F.1) (wt BE F.1)
        (wt AT F.1))
    (charge:RegularIndex H→ℕ)
    (hcharge: ∀F ∈ A,∀j,j≤fuel→
      stageCost L YS S (LP F) j≤charge F):
    ∃U,U ⊂ A∧ ∀F ∈ A \ U,
      (regularSeeds H selected Gamma F).card≤charge F:=by
  classical
  let source:=IJ (K:=K) D 131071 L S m
    IRSProfile.domain u0 u1
  let recon:source→ₗ[K] P4:=
    LZ (K:=K) D 131071 L S m
      IRSProfile.domain u0 u1
  let U₀:=AKV H A recon
  have hU₀sub:U₀ ⊆ A:=BTP H A recon
  by_cases hall:U₀=A
  · have hdiv: ∀v:source,CK H A ∣
        reconstruct K D 131071 L S v.1:=by
      intro v
      have hv:=BAZ H A recon v
      change CK H U₀ ∣ recon v at hv
      rw [hall] at hv
      change CK H A ∣
        LZ (K:=K) D 131071 L S m
          IRSProfile.domain u0 u1 v at hv
      rw [SE] at hv
      exact hv
    obtain ⟨q,hq,hproduct,hqbox⟩:=
      CRZ D 131071 L S m YS
        IRSProfile.domain u0 u1 (by decide) hshape H A hdiv
    cases fuel with
    | zero=>omega
    | succ steps=>
      have hDlow:
          D-delta-wt (BV 131071) (CK H A)=
            (D-wt (BV 131071) (CK H A))-delta:=by
        omega
      have hsource:CS.HN 131071
          (D-wt (BV 131071) (CK H A)) delta
          (wt (BV 131071) (CK H A))
          (wt AT (CK H A))
          (wt BC (CK H A))
          (wt BE (CK H A))
          (L-wt AT (CK H A))
          (YS-wt BC (CK H A))
          (S-wt BE (CK H A)) (steps+1)<
        Module.finrank K source:=hbandThin.trans_le hgapLe
      have hterminal' :
          (L-wt AT (CK H A))-
              steps*wt AT (CK H A)<
                wt AT (CK H A)∨
          (YS-wt BC (CK H A))-
              steps*wt BC (CK H A)<
                wt BC (CK H A)∨
          (S-wt BE (CK H A))-
              steps*wt BE (CK H A)<
                wt BE (CK H A):=by
        rcases hterminal with ht | hy | hs
        · left
          simpa only [Nat.sub_sub,Nat.succ_eq_add_one,Nat.add_mul,
            one_mul,Nat.add_comm] using ht
        · right;left
          simpa only [Nat.sub_sub,Nat.succ_eq_add_one,Nat.add_mul,
            one_mul,Nat.add_comm] using hy
        · right;right
          simpa only [Nat.sub_sub,Nat.succ_eq_add_one,Nat.add_mul,
            one_mul,Nat.add_comm] using hs
      have hexit:=BON steps
        (D-wt (BV 131071) (CK H A))
        (D-delta-wt (BV 131071) (CK H A))
        131071 delta
        (L-wt AT (CK H A))
        (YS-wt BC (CK H A))
        (S-wt BE (CK H A)) (by decide) hDlow q hq hqbox
        H A hA hsource hterminal' hfield
      exact EOW D L S m YS delta (steps+1)
        hD hfuelChar hlowpos hcapacity u0 u1 H selected Gamma hdegree
        hagreement hno A q hproduct hexit hfeasible
        (fun F hFA j _hj hjle=>hgates F hFA j hjle) charge
        (fun F hFA j _hj hjle=>hcharge F hFA j hjle)
  · have hproper:U₀ ⊂ A:=
        (_root_.ssubset_iff_subset_ne).mpr ⟨hU₀sub,hall⟩
    refine ⟨U₀,hproper,?_⟩
    intro F hFU
    have hFA:F ∈ A:=(Finset.mem_sdiff.mp hFU).1
    have hnot: ¬ ∀v:source,
        F.1 ∣ reconstruct K D 131071 L S v.1:=by
      intro hdiv
      apply (Finset.mem_sdiff.mp hFU).2
      apply (ASD H A recon F).mpr
      refine ⟨hFA,?_⟩
      intro v
      change F.1 ∣ LZ (K:=K) D 131071 L S m
        IRSProfile.domain u0 u1 v
      rw [SE]
      exact hdiv v
    rcases DKV D L S m YS hD hDa hshape selected
      Gamma hdegree hagreement hno F
      (wt BC F.1) (wt BE F.1)
      (wt AT F.1)
      (AKD F.1) (BAM F.1)
      (ADI F.1)
      (by simpa using hgates F hFA 0 (Nat.zero_le fuel)) with
      hdiv | hhelper
    · exact (hnot hdiv).elim
    · have hstage:(regularSeeds H selected Gamma F).card≤
          stageCost L YS S (LP F) 0:=by
        simpa only [stageCost,stagePair,LP,Nat.zero_mul,
          Nat.sub_zero] using hhelper
      exact hstage.trans (hcharge F hFA 0 (Nat.zero_le _))

end

end ProximityPrize.SubmissionLower.Lower80899.AGR

namespace ProximityPrize.SubmissionLower.Lower80899.Oracle
open RCN095 DY IL CS
open Lower80899.PowerRoute Lower80899.FactorSwitch
open FV (Potential rawFlag sumFlag RawBelow AVS)
set_option autoImplicit false
set_option maxRecDepth 100000

structure EA where
  totalCap:ℕ
  middleCap:ℕ
  slopeCap:ℕ
  gap:ℕ
  deriving DecidableEq,Repr

def EA.fuel (s:EA) (p:FlagDegree):ℕ:=
  min (s.totalCap/total p)
    (min (s.middleCap/middle p) (s.slopeCap/p.all))

def EA.band (s:EA) (p:FlagDegree):ℕ:=
  LH 50165 (total p) (middle p) p.all
    (s.totalCap-total p) (s.middleCap-middle p)
    (s.slopeCap-p.all) (s.fuel p)

def contactDec (p:FlagDegree):ℕ:=131071*middle p-p.all

def EA.contactCap (s:EA) (p:FlagDegree):ℕ:=
  (131071*(s.middleCap+1)-s.slopeCap)-contactDec p

def EA.bandThin (s:EA) (p:FlagDegree):ℕ:=
  HN 131071 (s.contactCap p) 50165 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap-total p) (s.middleCap-middle p)
    (s.slopeCap-p.all) (s.fuel p)

def EA.Routeable (s:EA) (p:FlagDegree):Prop:=
  1≤p.all∧total p≤s.totalCap∧middle p≤s.middleCap∧
    p.all≤s.slopeCap∧(s.band p<s.gap∨s.bandThin p<s.gap)

instance (s:EA) (p:FlagDegree):Decidable (s.Routeable p):=
  by unfold EA.Routeable;infer_instance

def LP (p:FlagDegree):DTX:=
  ⟨total p,total p,middle p,middle p,p.all,p.all⟩

structure YF where
  source:EA
  potential:Potential
  stageCost_le: ∀(p:FlagDegree) (j:ℕ),
    1≤p.all→p.all≤40→middle p≤181→total p≤11784→
    j≤source.fuel p→
    stageCost source.totalCap source.middleCap source.slopeCap
      (LP p) j≤potential.eval p
  stageGates: ∀(p:FlagDegree) (j:ℕ),
    1≤p.all→p.all≤40→middle p≤181→total p≤11784→
    j≤source.fuel p→
    LX
      (source.totalCap-j*total p)
      (source.middleCap-j*middle p)
      (source.slopeCap-j*p.all)
      (middle p) p.all (total p)

end ProximityPrize.SubmissionLower.Lower80899.Oracle

namespace ProximityPrize.SubmissionLower.Lower80899.BatchPhase

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266
open DY CS KZ Lower80899.AGR Lower80899.FactorSwitch Lower80899.Oracle

open FV (Potential sumFlag sumFlag_all AQT AXF RawBelow AVS)
open MM (BF JM
  IF KH LY
  AAN AML BCO)

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

private theorem DJI (s:EA) (p:FlagDegree)
    (hr:1≤p.all) (ht:total p≤s.totalCap)
    (hy:middle p≤s.middleCap) (hs:p.all≤s.slopeCap):
    1≤s.fuel p:=by
  have hmiddle:1≤middle p:=hr.trans (ATD p)
  have htotal:1≤total p:=hmiddle.trans (AIS p)
  unfold EA.fuel
  apply le_min
  · exact (Nat.le_div_iff_mul_le htotal).mpr (by simpa using ht)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hmiddle).mpr (by simpa using hy)
    · exact (Nat.le_div_iff_mul_le hr).mpr (by simpa using hs)

private theorem BHW (s:EA) (p:FlagDegree)
    (hr:1≤p.all):
    s.fuel p*total p≤s.totalCap∧
      s.fuel p*middle p≤s.middleCap∧
      s.fuel p*p.all≤s.slopeCap:=by
  have hmiddle:1≤middle p:=hr.trans (ATD p)
  have htotal:1≤total p:=hmiddle.trans (AIS p)
  unfold EA.fuel
  refine ⟨?_,?_,?_⟩
  · apply (Nat.le_div_iff_mul_le htotal).mp
    exact min_le_left _ _
  · apply (Nat.le_div_iff_mul_le hmiddle).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  · apply (Nat.le_div_iff_mul_le hr).mp
    exact (min_le_right _ _).trans (min_le_right _ _)

private theorem AIN (a b:ℕ) (hb:0<b):
    a-(a/b)*b<b:=by
  have hm:=Nat.mod_lt a hb
  have heq:=Nat.mod_add_div' a b
  omega

private theorem BKF (s:EA) (p:FlagDegree)
    (hr:1≤p.all):
    s.totalCap-s.fuel p*total p<total p∨
      s.middleCap-s.fuel p*middle p<middle p∨
      s.slopeCap-s.fuel p*p.all<p.all:=by
  have hall:0<p.all:=by omega
  have hmiddle:0<middle p:=hall.trans_le (ATD p)
  have htotal:0<total p:=hmiddle.trans_le (AIS p)
  unfold EA.fuel
  by_cases hT:s.totalCap/total p≤
      min (s.middleCap/middle p) (s.slopeCap/p.all)
  · left
    rw [min_eq_left hT]
    exact AIN s.totalCap (total p) htotal
  · rw [min_eq_right (Nat.le_of_not_ge hT)]
    by_cases hY:s.middleCap/middle p≤s.slopeCap/p.all
    · right;left
      rw [min_eq_left hY]
      exact AIN s.middleCap (middle p) hmiddle
    · right;right
      rw [min_eq_right (Nat.le_of_not_ge hY)]
      exact AIN s.slopeCap p.all hr

theorem CSO
    (sound:YF) (D m:ℕ)
    (hweighted:D≤m*181235∧m*50165<D)
    (hshape:D+sound.source.slopeCap≤
      131071*(sound.source.middleCap+1))
    (hslopeM:sound.source.slopeCap≤m)
    (hmChar:m<2130706433)
    (u0 u1:I→K) (H:P4)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,
      (selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (hgap:sound.source.gap≤Module.finrank K
      (IJ (K:=K) D 131071 sound.source.totalCap
        sound.source.slopeCap m IRSProfile.domain u0 u1))
    (A:Finset (RegularIndex H))
    (hroute:sound.source.Routeable (BF H A))
    (hnarrowS:(BF H A).all≤40)
    (hnarrowY:middle (BF H A)≤181)
    (hnarrowT:total (BF H A)≤11784):
    ∃U,U ⊂ A∧ ∀F ∈ A \ U,
      (regularSeeds H selected Gamma F).card≤
        sound.potential.eval (BG H F):=by
  classical
  let p:=BF H A
  have hr:1≤p.all:=hroute.1
  have hA:A.Nonempty:=by
    by_contra hzero
    have hAe:A= ∅ :=Finset.not_nonempty_iff_eq_empty.mp hzero
    subst A
    simp [p,BF,sumFlag] at hr
  have hfuel:1≤sound.source.fuel p:=
    DJI sound.source p hr hroute.2.1 hroute.2.2.1
      hroute.2.2.2.1
  have hfeasibleP:=BHW sound.source p hr
  have hterminalP:=BKF sound.source p hr
  have hfuelSlope:sound.source.fuel p≤sound.source.slopeCap:=by
    calc
      sound.source.fuel p≤sound.source.slopeCap/p.all:=
        (min_le_right _ _).trans (min_le_right _ _)
      _≤sound.source.slopeCap:=Nat.div_le_self _ _
  have hfuelM:sound.source.fuel p≤m:=hfuelSlope.trans hslopeM
  have hfuelChar:sound.source.fuel p<2130706433:=
    hfuelM.trans_lt hmChar
  have hlowpos: ∀j,1≤j→j≤sound.source.fuel p→
      0<D-j*50165:=by
    intro j hj hjfuel
    have hjm:j≤m:=hjfuel.trans hfuelM
    have hw:=hweighted.2
    omega
  have hcapacity: ∀j,1≤j→j≤sound.source.fuel p→
      D-j*50165≤
        (m-j)*181235+j*(131071-1):=by
    intro j _hj hjfuel
    have hjm:j≤m:=hjfuel.trans hfuelM
    have hw:=hweighted.1
    omega
  have hfield:A.card<ENat.card K:=by
    have hcard:A.card≤p.all:=by
      calc
        A.card= ∑ F ∈ A,1:=by simp
        _≤ ∑ F ∈ A,(BG H F).all:=
          Finset.sum_le_sum (fun F _=>Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (JH H F)))
        _=p.all:=by simp only [p,BF,sumFlag_all]
    calc
      (A.card:ENat)≤(40:ℕ):=by
        exact_mod_cast hcard.trans hnarrowS
      _<ENat.card K:=by
        rw [ENat.card_eq_coe_fintype_card,RCN183.BIS]
        norm_num
  have factor_le_aggregate (F:RegularIndex H) (hFA:F ∈ A):
      (BG H F).all≤p.all∧
      middle (BG H F)≤middle p∧
      total (BG H F)≤total p:=by
    have hsub:({F}:Finset (RegularIndex H)) ⊆ A:=
      Finset.singleton_subset_iff.mpr hFA
    simpa [p,BF,sumFlag,middle,total] using
      LY H hsub
  have factorFuel (F:RegularIndex H) (hFA:F ∈ A) (j:ℕ)
      (hj:j≤sound.source.fuel p):
      j≤sound.source.fuel (BG H F):=by
    have hle:=factor_le_aggregate F hFA
    have hFr:1≤(BG H F).all:=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (JH H F))
    have hFm:1≤middle (BG H F):=
      hFr.trans (ATD _)
    have hFt:1≤total (BG H F):=
      hFm.trans (AIS _)
    have hjT:j*total (BG H F)≤
        sound.source.totalCap:=by
      calc
        j*total (BG H F)≤j*total p:=
          Nat.mul_le_mul_left j hle.2.2
        _≤sound.source.fuel p*total p:=
          Nat.mul_le_mul_right (total p) hj
        _≤sound.source.totalCap:=hfeasibleP.1
    have hjY:j*middle (BG H F)≤
        sound.source.middleCap:=by
      calc
        j*middle (BG H F)≤j*middle p:=
          Nat.mul_le_mul_left j hle.2.1
        _≤sound.source.fuel p*middle p:=
          Nat.mul_le_mul_right (middle p) hj
        _≤sound.source.middleCap:=hfeasibleP.2.1
    have hjS:j*(BG H F).all≤
        sound.source.slopeCap:=by
      calc
        j*(BG H F).all≤j*p.all:=
          Nat.mul_le_mul_left j hle.1
        _≤sound.source.fuel p*p.all:=
          Nat.mul_le_mul_right p.all hj
        _≤sound.source.slopeCap:=hfeasibleP.2.2
    unfold EA.fuel
    apply le_min
    · exact (Nat.le_div_iff_mul_le hFt).mpr hjT
    · apply le_min
      · exact (Nat.le_div_iff_mul_le hFm).mpr hjY
      · exact (Nat.le_div_iff_mul_le hFr).mpr hjS
  have hgates: ∀F ∈ A,∀j,j≤sound.source.fuel p→
      LX
        (sound.source.totalCap-j*wt AT F.1)
        (sound.source.middleCap-j*wt BC F.1)
        (sound.source.slopeCap-j*wt BE F.1)
        (wt BC F.1) (wt BE F.1)
        (wt AT F.1):=by
    intro F hFA j hj
    have hc:=GX F.1
    have hle:=factor_le_aggregate F hFA
    have hFr:1≤(BG H F).all:=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (JH H F))
    have hs:=sound.stageGates (BG H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR:(BG H F).all=
        wt BE F.1:=hc.1
    have hY:middle (BG H F)=
        wt BC F.1:=hc.2.1
    have hT:total (BG H F)=
        wt AT F.1:=hc.2.2
    simpa only [hR,hY,hT] using hs
  have hcharge: ∀F ∈ A,∀j,j≤sound.source.fuel p→
      Lower80899.PowerRoute.stageCost sound.source.totalCap
        sound.source.middleCap sound.source.slopeCap
        (Lower80899.AGR.LP F) j≤
          sound.potential.eval (BG H F):=by
    intro F hFA j hj
    have hc:=GX F.1
    have hle:=factor_le_aggregate F hFA
    have hFr:1≤(BG H F).all:=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (JH H F))
    have hs:=sound.stageCost_le (BG H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR:(BG H F).all=
        wt BE F.1:=hc.1
    have hY:middle (BG H F)=
        wt BC F.1:=hc.2.1
    have hT:total (BG H F)=
        wt AT F.1:=hc.2.2
    simpa only [Lower80899.AGR.LP,
      Lower80899.Oracle.LP,hR,hY,hT] using hs
  have hmpos:0<m:=by omega
  have hDpos:0<D:=by
    have hw:=hweighted.2
    omega
  have hDa:D≤m*181235:=hweighted.1
  have hP:CK H A ≠ 0:=AHD H A
  have hcP:contactDec p≤wt (BV 131071) (CK H A):=by
    have h:=CS.FAK 131071 (by decide)
      (CK H A) hP
    simpa only [contactDec,p,IF,
      JM] using h
  have hDcap:D-wt (BV 131071) (CK H A)≤
      sound.source.contactCap p:=by
    unfold EA.contactCap
    omega
  have hbandThin:CS.HN 131071
      (D-wt (BV 131071) (CK H A)) 50165
      (wt (BV 131071) (CK H A))
      (wt AT (CK H A))
      (wt BC (CK H A))
      (wt BE (CK H A))
      (sound.source.totalCap-wt AT (CK H A))
      (sound.source.middleCap-wt BC (CK H A))
      (sound.source.slopeCap-wt BE (CK H A))
      (sound.source.fuel p)<sound.source.gap:=by
    rcases hroute.2.2.2.2 with hold | hthin
    · have hold' :LH 50165
          (wt AT (CK H A))
          (wt BC (CK H A))
          (wt BE (CK H A))
          (sound.source.totalCap-wt AT (CK H A))
          (sound.source.middleCap-wt BC (CK H A))
          (sound.source.slopeCap-wt BE (CK H A))
          (sound.source.fuel p)<sound.source.gap:=by
        simpa only [EA.band,p,KH,
          IF,JM] using hold
      exact (CS.CCZ
        _ _ _ _ _ _ _ _ _ _ _).trans_lt hold'
    · have hthin' :CS.HN 131071
          (sound.source.contactCap p) 50165 (contactDec p)
          (wt AT (CK H A))
          (wt BC (CK H A))
          (wt BE (CK H A))
          (sound.source.totalCap-wt AT (CK H A))
          (sound.source.middleCap-wt BC (CK H A))
          (sound.source.slopeCap-wt BE (CK H A))
          (sound.source.fuel p)<sound.source.gap:=by
        simpa only [EA.bandThin,p,KH,
          IF,JM] using hthin
      exact (CS.AZD 131071 50165
        (sound.source.fuel p) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hDcap hcP le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl).trans_lt hthin'
  apply AAA D
    sound.source.totalCap sound.source.slopeCap m sound.source.middleCap
    sound.source.gap 50165 (sound.source.fuel p)
  · exact hDpos
  · exact hDa
  · exact hshape
  · exact hfuel
  · exact hfuelChar
  · exact hlowpos
  · exact hcapacity
  · exact hdegree
  · exact hagreement
  · exact hno
  · exact hA
  · exact hbandThin
  · simpa only [p,KH,
      IF,JM] using hterminalP
  · simpa only [p,KH,
      IF,JM] using hfeasibleP
  · exact hgap
  · exact hfield
  · exact hgates
  · exact hcharge

structure WZ (sound:YF)
    (u0 u1:I→K) where
  D:ℕ
  m:ℕ
  weighted:D≤m*181235∧m*50165<D
  shape:D+sound.source.slopeCap≤
    131071*(sound.source.middleCap+1)
  slope_le_m:sound.source.slopeCap≤m
  m_lt_char:m<2130706433
  gap_le_finrank:sound.source.gap≤Module.finrank K
    (IJ (K:=K) D 131071 sound.source.totalCap
      sound.source.slopeCap m IRSProfile.domain u0 u1)

end

end ProximityPrize.SubmissionLower.Lower80899.BatchPhase
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.AFL

open RCN095
open Lower80788.FixedStage

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem GY (f:FlagDegree) (a b s:ℕ):
    131073*80910*ProximityPrize.SubmissionLower.RCN146.IY f a b s 131071≤
      50164*flagMixed f (firstTail a b s) (secondTail a b s):=by
  change 131073*80910*ProximityPrize.SubmissionLower.RCN146.IY f a b s Lower80788.FixedStage.w≤_
  rw [Lower80788.FixedStage.APP]
  norm_num [firstTail,secondTail,Lower80788.FixedStage.BRF,
    Lower80788.FixedStage.w,flagMixed]
  ring_nf
  omega

theorem FLH (p:FlagDegree)
    (h: ¬AAJ.UG p):
    Lower80788.Fixed.padSlope p=0∨Lower80788.Fixed.padB p=0:=by
  dsimp [AAJ.UG,DY.middle] at h
  dsimp [Lower80788.Fixed.padSlope,Lower80788.Fixed.padB,
    DY.padS,DY.padY,
    DY.middle]
  omega

theorem ETV (b s:ℕ) (f:FlagDegree)
    (hS:s+2≤32) (hY:b+s+3≤149)
    (hlow:s=0∨b=0)
    (hfs:f.all≤s+2) (hfy:f.yz+f.all≤b+s+3):
    (1+131072*(2*(b+s+3)-2))*f.all+
      (f.yz+f.all)*((2*(s+2)-2)*131072)<2130706433:=by
  rcases hlow with hs0 | hb0
  · have hy:2*(b+s+3)-2≤296:=by omega
    have hs:2*(s+2)-2≤2:=by omega
    have hfS:f.all≤2:=by omega
    have hfY:f.yz+f.all≤149:=by omega
    calc
      _≤(1+131072*296)*2+149*(2*131072):=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131072 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131072 hs))
      _<2130706433:=by decide
  · have hy:2*(b+s+3)-2≤64:=by omega
    have hs:2*(s+2)-2≤62:=by omega
    have hfS:f.all≤32:=by omega
    have hfY:f.yz+f.all≤33:=by omega
    calc
      _≤(1+131072*64)*32+33*(62*131072):=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131072 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131072 hs))
      _<2130706433:=by decide

theorem ETS (b s:ℕ) (f:FlagDegree)
    (hS:s+2≤32) (hY:b+s+3≤149)
    (hlow:s=0∨b=0)
    (hfs:f.all≤s+2) (hfy:f.yz+f.all≤b+s+3):
    (1+131071*(2*(b+s+3)-2))*f.all+
      (f.yz+f.all)*((2*(s+2)-1)*131071)<2130706433:=by
  rcases hlow with hs0 | hb0
  · have hy:2*(b+s+3)-2≤296:=by omega
    have hs:2*(s+2)-1≤3:=by omega
    have hfS:f.all≤2:=by omega
    have hfY:f.yz+f.all≤149:=by omega
    calc
      _≤(1+131071*296)*2+149*(3*131071):=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131071 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131071 hs))
      _<2130706433:=by decide
  · have hy:2*(b+s+3)-2≤64:=by omega
    have hs:2*(s+2)-1≤63:=by omega
    have hfS:f.all≤32:=by omega
    have hfY:f.yz+f.all≤33:=by omega
    calc
      _≤(1+131071*64)*32+33*(63*131071):=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131071 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131071 hs))
      _<2130706433:=by decide

end ProximityPrize.SubmissionLower.AFL
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.AJN
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80909
def agreements:ℕ:=181235
def gap:ℕ:=50164
def prime:ℕ:=2130706433
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,RCN223.prime] using
    RCN128.FJ
def firstTail (a b s:ℕ):FlagDegree:=
  CI (RCN198.support a b s) (w+1)
def secondTail (a b s:ℕ):FlagDegree:=
  CI (RCN198.support a b s) (w+2)
theorem BRF (a b s d:ℕ):
    CI (RCN198.support a b s) d=
      ⟨2*a*d,1+2*(b+1)*d,2*(s+1)*d⟩:=by
  have ht:a+b+s+3-(b+s+3)=a:=by omega
  have hy:b+s+3-(s+2)=b+1:=by omega
  have hs:2*(s+2)-2=2*(s+1):=by omega
  simp only [CI,UH,RCN198.support]
  rw [ht,hy,hs]
theorem tangent_gate (a b s:ℕ):
    errors+1≤(secondTail a b s).yz:=by
  rw [secondTail,BRF]
  change errors+1≤1+2*(b+1)*(w+2)
  have hb:2*(w+2)≤2*(b+1)*(w+2):=by
    have h:=Nat.mul_le_mul_right (w+2)
      (Nat.mul_le_mul_left 2 (show 1≤b+1 by omega))
    simpa only [Nat.mul_one] using h
  exact (by norm_num [errors,w]:errors+1≤1+2*(w+2)).trans
    (Nat.add_le_add_left hb 1)
theorem FIU (a b s:ℕ) (flag:FlagDegree)
    (hS:s+2≤32) (hY:b+s+3≤149) (hT:a+b+s+3≤8121)
    (hflag:flag.all≤s+2∧flag.yz+flag.all≤b+s+3∧
      flag.zOnly+flag.yz+flag.all≤a+b+s+3):
    flag.yz+flag.all<prime∧flag.all<prime∧
      flag.zOnly+flag.yz+flag.all<prime:=by
  dsimp [prime]
  omega
def GHG (D a b s:ℕ):Prop:=
  ∀{Gamma:Finset K} {flag:FlagDegree},
    (S:FH (AL K) Gamma IRSProfile.domain
      prime errors flag w (RCN198.support a b s))→
    S.nodes.card=agreements+errors→
    (∀gamma ∈ Gamma,agreements≤(S.AJW gamma).card)→
    S.F ∈ RCN174.BA K D w (a+b+s+3) (s+2)→
    (flag.all≤s+2∧flag.yz+flag.all≤b+s+3∧
      flag.zOnly+flag.yz+flag.all≤a+b+s+3)→
    Gamma.card≤flagMixed flag (firstTail a b s) (secondTail a b s)
theorem GFO (D a b s:ℕ)
    (hDlow:w+1≤D) (hDhigh:D<prime)
    (hS:s+2≤32) (hY:b+s+3≤149) (hT:a+b+s+3≤8121)
    (hlow:s=0∨b=0):
    GHG D a b s:=by
  intro Gamma flag S hnodes hagreement hbox hflag
  have hDchar:D<prime:=hDhigh
  have hflagChar:=FIU a b s flag hS hY hT hflag
  by_cases hTail:S.G ∣ _Q2 (AL K) S.F (w+1)
  · have hTailNumerator:S.G ∣ surfaceMap (AL K)
        (numerator K S.F (w+1)):=
      (AWJ (AL K)
        (DI K) S.F (w+1) S.G).mp hTail
    have hprovider:=RCN146.AAB S agreements hnodes
      hagreement (by norm_num [agreements,w]) hTailNumerator
      D (a+b+s+3) (s+2)
      (by norm_num [w]) hDlow hDchar hbox hflagChar
      (AFL.ETS b s flag hS hY hlow hflag.1 hflag.2.1)
    have hpositive:1≤ProximityPrize.SubmissionLower.RCN146.IY flag a b s w:=by
      apply Lower80788.FixedStage.CVP
      have hy:0<S.G.degreeOf 1:=S.y_dependent
      have hdeg:=AHE S.G flag S.flag_support 1
      omega
    have hinc:=AQH S agreements
      (ProximityPrize.SubmissionLower.RCN146.IY flag a b s w) hprovider hagreement
      (by norm_num [agreements,w])
      (by rw [hnodes]<;>norm_num [agreements,errors]) hpositive
    have hscaled:Gamma.card*gap≤
        gap*flagMixed flag (firstTail a b s) (secondTail a b s):=by
      calc
        Gamma.card*gap=Gamma.card*(agreements-w):=rfl
        _≤(S.nodes.card-w)*(errors+1)*
            ProximityPrize.SubmissionLower.RCN146.IY flag a b s w:=hinc
        _=(n-w)*(errors+1)*ProximityPrize.SubmissionLower.RCN146.IY flag a b s w:=by
          rw [hnodes]<;>norm_num [n,agreements,errors]
        _≤gap*flagMixed flag (firstTail a b s) (secondTail a b s):=
          AFL.GY flag a b s
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap]:0<gap)
    simpa only [Nat.mul_comm] using hscaled
  · have hprovider:=ATO
      (stageErrorCap:=errors) agreements S hTail hflagChar
      (AFL.ETV b s flag hS hY hlow hflag.1 hflag.2.1)
      D (a+b+s+3) (s+2) hnodes hagreement
      (by norm_num [RCN327.w,agreements])
      (by simpa only [RCN327.w,w] using hDlow)
      hDchar hbox (tangent_gate a b s)
    exact EUJ S hprovider.some
end

end ProximityPrize.SubmissionLower.AJN
end MergedPart7
end
section
section MergedPart0
section Compact_MovingFiberScalar6815

namespace ProximityPrize.SubmissionLower.CNZ
open scoped BigOperators
open ProximityPrize.Benchmark RCN279 RCN285
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-- `RCN319.EM _ x u 0` and `RCN279.EM _ x u`
are distinct constants with identical bodies. Bridging them here, over variables,
keeps the delta step small; doing it inside the proof below forces the check on a
huge applied term. -/
theorem DVP (x u:IRSProfile.Field):
    RCN319.EM IRSProfile.Field x u 0
      =EM IRSProfile.Field x u:=rfl

theorem EUR:AW 23923020 131071 182 39=70442639960:=by decide+kernel

theorem FEZ:ES 132 182 39=268700:=by decide+kernel

theorem FNC:
    262144*ES 132 182 39<AW 23923020 131071 182 39:=by
  norm_num only [EUR,FEZ]

theorem CXE
   (received:IRSProfile.Index→IRSProfile.Field):
   ∃Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈BA IRSProfile.Field
       23923020 131071 182 39∧
     ∀(i:IRSProfile.Index) (r:ℕ),
       RCN119.IA IRSProfile.Field^(132-r)∣
         (EM IRSProfile.Field
           (IRSProfile.domain i) (received i) Q).coeff r:=by
 obtain ⟨theta,htheta,hzero⟩:=ACY
   IRSProfile.Field 23923020 131071 182 39 132
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index=262144 by
       norm_num [IRSProfile.Index]]
     exact FNC)
 refine ⟨reconstruct IRSProfile.Field 23923020 131071 182 39 theta,
   AVT IRSProfile.Field _ _ _ _ theta htheta,
   FII IRSProfile.Field _ _ _ _ theta,?_⟩
 intro i r
 have hdiv:=DPT IRSProfile.Field
   23923020 131071 182 39 132 IRSProfile.domain received
   theta hzero i r
 rw [AMG IRSProfile.Field 23923020 131071
   182 39 (IRSProfile.domain i) (received i) theta r]
 exact hdiv

end ProximityPrize.SubmissionLower.CNZ

end Compact_MovingFiberScalar6815

section Compact_MovingFiberScalarList6815

namespace ProximityPrize.SubmissionLower.FQ
open ProximityPrize.Benchmark
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80909
def agreements:ℕ:=n-errors
def gap:ℕ:=agreements-w
def prime:ℕ:=2130706433
def multiplicity:ℕ:=132
def yTotalCap:ℕ:=182
def slopeCap:ℕ:=39
def weightedCap:ℕ:=multiplicity*agreements
def listBudget:ℕ:=9661207595
def capY:ℕ:=1+2*w*yTotalCap
def capR:ℕ:=w*(2*slopeCap-1)
def ALH:ℕ:=(n-w)*(capY*slopeCap+capR*yTotalCap)
def AMW:ℕ:=(2*slopeCap-1)*yTotalCap
def BNF:ℕ:=ALH+AMW*gap

theorem DEN:BNF<listBudget*gap:=by decide

theorem EDE (received:IRSProfile.Index→IRSProfile.Field):
   ∃Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0∧Q ∈ RCN279.BA IRSProfile.Field weightedCap w yTotalCap slopeCap∧
     ∀(i:IRSProfile.Index) (r:ℕ),
       RCN119.IA IRSProfile.Field^(multiplicity-r) ∣
         (RCN319.EM IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r:=by
  obtain ⟨Q,hQ0,hQbox,hQdvd⟩:=
    CNZ.CXE received
  refine ⟨Q,hQ0,hQbox,fun i r=> ?_⟩
  rw [CNZ.DVP]
  exact hQdvd i r
end
end ProximityPrize.SubmissionLower.FQ

namespace ProximityPrize.SubmissionLower.CVH
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN319 RCN174 RCN231 RCN081 RCN167 RCN313 RCN136 RCN135 RCN138 RCN137 RCN267 RCN238 RCN243 RCN222 RCN290 RCN293 RCN286 RCN279 RCN282 RCN283 RCN001 RCN281 RCN019 RCN018
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
private abbrev n:=FQ.n
private abbrev w:=FQ.w
private abbrev agreements:=FQ.agreements
private abbrev gap:=FQ.gap
private abbrev prime:=FQ.prime
private abbrev multiplicity:=FQ.multiplicity
private abbrev yTotalCap:=FQ.yTotalCap
private abbrev slopeCap:=FQ.slopeCap
private abbrev weightedCap:=FQ.weightedCap
private abbrev listBudget:=FQ.listBudget
private abbrev capY:=FQ.capY
private abbrev capR:=FQ.capR
private abbrev ALH:=
 FQ.ALH
private abbrev AMW:=FQ.AMW
private abbrev BNF:=FQ.BNF
private theorem DEN:BNF<listBudget*gap:=
 FQ.DEN
private theorem w_pos:0<w:=by decide
private theorem prime_pos:0<prime:=by decide
private theorem w_lt_prime:w<prime:=by decide
private theorem GGX:w<agreements:=by decide
private theorem GGA:agreements≤n:=by decide
private theorem FLP:yTotalCap<prime:=by decide
private theorem CTG:slopeCap<prime:=by decide
private theorem slopeCap_pos:0<slopeCap:=by decide
private theorem GFR:0<weightedCap:=by decide
private theorem gap_pos:0<gap:=by decide
private theorem FGB:IRSProfile.baseDimension=w+1:=by
 norm_num [IRSProfile.baseDimension,w,FQ.w]
private theorem FZR:Fintype.card IRSProfile.Index=n:=by
 norm_num [IRSProfile.Index,n,FQ.n]
section
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
private def agreementCap:Fin 3→ℕ:=![capY,capR,1]
private theorem DZS
   (Q:MvPolynomial (Fin 4) K)
   (hbox:Q ∈ RCN279.BA K
     weightedCap w yTotalCap slopeCap):
   Q.degreeOf 1≤yTotalCap∧Q.degreeOf 2≤slopeCap∧
     Q.degreeOf 3=0:=by
 refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_,
   MvPolynomial.degreeOf_le_iff.mpr ?_,?_⟩
 · intro d hd
   exact (Nat.le_add_right (d 1) (d 2)).trans (hbox hd).1
 · intro d hd
   exact (hbox hd).2.1
 · apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.2.1.le
private theorem GUR
   (phi:Polynomial K→+*GenericField K)
   (F:MvPolynomial (Fin 4) K)
   (hY:F.degreeOf 1≤yTotalCap)
   (hR:F.degreeOf 2≤slopeCap)
   (hZ:F.degreeOf 3=0) (x u:K):
   ∀j,(FK phi F w x u 0).degreeOf j≤agreementCap j:=by
 have hb:=ARB F yTotalCap slopeCap 0
   slopeCap_pos hY hR hZ.le w
     (fun j=>(j.factorial:K)⁻¹) x u 0
 intro j
 fin_cases j
 · exact (GO phi _ 0).trans
     (by simpa [agreementCap,capY,FQ.capY]
       using hb.1)
 · exact (GO phi _ 1).trans
     (by simpa [agreementCap,capR,FQ.capR]
       using hb.2.1)
 · exact (GO phi _ 2).trans
     (hb.2.2.trans (by simp [agreementCap]))
private theorem DMR
   [CharP K prime]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0<F.degreeOf 2)
   (hbox:F ∈ RCN174.BA K
     weightedCap w yTotalCap slopeCap)
   (hY:F.degreeOf 1≤yTotalCap)
   (hR:F.degreeOf 2≤slopeCap)
   (hZ:F.degreeOf 3=0)
   (Gamma:Finset (Polynomial K))
   (hdegree:∀S ∈ Gamma,S.natDegree≤w)
   (hsolutions:∀S ∈ Gamma,BM K S 0 F=0)
   (hregular:∀S ∈ Gamma,
     BM K S 0 (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0)
   {Iota:Type} [Fintype Iota] [DecidableEq Iota]
   (nodes:Finset Iota) (x received:Iota→K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hagreement:∀S ∈ Gamma,agreements≤
     (nodes.filter (fun i=>S.eval (x i)=received i)).card):
   Gamma.card*gap≤
     (n-w)*(capY*F.degreeOf 2+capR*F.degreeOf 1):=by
 classical
 letI:CharP (GenericField K) prime:=MP K prime
 have hsmall:F.degreeOf 2<prime:=hR.trans_lt CTG
 have hcount (g:RCN281.EX K F):
     (RCN281.AHL K F Gamma g).card*gap≤
       (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0):=by
   obtain ⟨hgirred,hgdiv⟩:=
     ACQ (AL K) F g.1 g.2
   have hgate:=BWF K (GenericField K) F hF
     prime hRpos hsmall g.1 hgirred
     (by simpa only [HP] using hgdiv)
   have hproper:=RCN281.DVO
     K g.1 hgate.1
   have hgY:=(AGP K F hF.ne_zero g 0).trans hY
   have hgR:=(AGP K F hF.ne_zero g 1).trans hR
   have hgZ:g.1.degreeOf 2=0:=Nat.eq_zero_of_le_zero
     ((AGP K F hF.ne_zero g 2).trans_eq hZ)
   have hGdegree:∀j:Fin 3,g.1.degreeOf j<prime:=by
     intro j
     fin_cases j
     · exact hgY.trans_lt FLP
     · exact hgR.trans_lt CTG
     · simpa [hgZ] using prime_pos
   have hcutDegree:∀j k:Fin 3,j ≠ k→
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf j*
           g.1.degreeOf k+
         g.1.degreeOf j*
           (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf k<prime:=by
     intro j k hjk
     have h0:=hGdegree 0
     have h1:=hGdegree 1
     have h2:=hGdegree 2
     fin_cases j<;>fin_cases k<;>
       simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne] at hjk ⊢ <;>
       omega
   have hsub:=RCN281.EBW K F Gamma g
   have hraw:=EKW (AL K)
     (DI K) F g.1 hgirred hgdiv hproper
     (RCN281.AHL K F Gamma g)
     nodes x received hinj prime w agreements
     w_pos w_lt_prime GGX
     (by rw [hnodes];exact GGA)
     hGdegree hcutDegree
     (fun S hS=>hdegree S (hsub hS))
     (fun S hS=>hsolutions S (hsub hS))
     (fun S hS=>VK K F
       (fun _:K=>S) 0 (hregular S (hsub hS)))
     (fun S hS=>(Finset.mem_filter.mp hS).2)
     (fun S hS=>hagreement S (hsub hS)) agreementCap
     (fun i hi=>GUR K (AL K) F hY hR hZ
       (x i) (received i))
   have hx0:
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 0=0:=by
     simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(0:Fin 3) ≠ 2)]
   have hx1:
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 1=0:=by
     simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3) ≠ 2)]
   have hx2:
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 2=1:=by
     simp [seedlessCut]
   have hm0:EB (GenericField K) g.1 seedlessCut 0=
       g.1.degreeOf 1:=by
     rw [RCN001.ASL,hx1,hx2]
     omega
   have hm1:EB (GenericField K) g.1 seedlessCut 1=
       g.1.degreeOf 0:=by
     rw [RCN001.BNH,hx0,hx2]
     omega
   have hm2:EB (GenericField K) g.1 seedlessCut 2=0:=by
     rw [RCN001.AGB,hx0,hx1]
     omega
   have hcost:
       (∑ i:Fin 3,agreementCap i*
         EB (GenericField K) g.1 seedlessCut i)=
       capY*g.1.degreeOf 1+capR*g.1.degreeOf 0:=by
     simp [Fin.sum_univ_succ,agreementCap,hm0,hm1,hm2]
   rw [hnodes,hcost] at hraw
   change (RCN281.AHL K F Gamma g).card*
       (agreements-w)≤
     (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0)
   exact hraw
 calc
   Gamma.card*gap≤
       (∑ g:RCN281.EX K F,
         (RCN281.AHL K F Gamma g).card)*gap:=
     Nat.mul_le_mul_right _
       (RCN281.DKJ
         K F hF.ne_zero Gamma hsolutions)
   _= ∑ g:RCN281.EX K F,
       (RCN281.AHL K F Gamma g).card*gap:=by
     rw [Finset.sum_mul]
   _≤ ∑ g:RCN281.EX K F,
       (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0):=
     Finset.sum_le_sum (fun g _=>hcount g)
   _=(n-w)*
       (capY*(∑ g:RCN281.EX K F,
         g.1.degreeOf 1)+
       capR*(∑ g:RCN281.EX K F,
         g.1.degreeOf 0)):=by
     rw [← Finset.mul_sum,Finset.sum_add_distrib,
       ← Finset.mul_sum,← Finset.mul_sum]
   _≤(n-w)*(capY*F.degreeOf 2+capR*F.degreeOf 1):=by
     apply Nat.mul_le_mul_left
     exact Nat.add_le_add
       (Nat.mul_le_mul_left capY (AYD K F hF.ne_zero 1))
       (Nat.mul_le_mul_left capR (AYD K F hF.ne_zero 0))
private theorem EKU
   [CharP K prime]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0)
   (hbox:Q ∈ RCN279.BA K
     weightedCap w yTotalCap slopeCap)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀S ∈ Gamma,
     BM K S 0 (IE Q)=0):
   Gamma.card≤AMW:=by
 classical
 let phi:=AL K
 let J:=IE Q
 have hcaps:=DZS K Q hbox
 have hJne:J ≠ 0:=BNM Q hQ prime
   (hcaps.2.1.trans_lt CTG)
 have hJR:J.degreeOf 2=0:=BIT Q hQ prime
   (hcaps.2.1.trans_lt CTG)
 have hQY:MvPolynomial.weightedTotalDegree
     RCN281.yWeights Q≤yTotalCap:=by
   apply (KN
     RCN281.yWeights Q yTotalCap).mpr
   intro d hd
   have hh:=(hbox hd).1
   rw [weight_fin4]
   simpa [RCN281.yWeights] using
     (Nat.le_add_right (d 1) (d 2)).trans hh
 have hQZ:MvPolynomial.weightedTotalDegree
     RCN281.zWeights Q≤0:=by
   apply (KN
     RCN281.zWeights Q 0).mpr
   intro d hd
   have hh:=(hbox hd).2.2.1
   rw [weight_fin4]
   simpa [RCN281.zWeights,hh]
 have hJYw:=ACP
   RCN281.yWeights Q hQ slopeCap
   slopeCap_pos hcaps.2.1
 have hJZw:=ACP
   RCN281.zWeights Q hQ slopeCap
   slopeCap_pos hcaps.2.1
 have hJY:J.degreeOf 1≤AMW:=
   (RCN281.FMV K J).trans
     (hJYw.trans (by
       simp only [AMW,FQ.AMW]
       exact Nat.mul_le_mul_left _ hQY))
 have hJZ:J.degreeOf 3=0:=Nat.eq_zero_of_le_zero
   ((RCN281.FOF K J).trans
     (hJZw.trans (by
       simpa only [Nat.mul_zero] using
         Nat.mul_le_mul_left (2*slopeCap-1) hQZ)))
 let A:MvPolynomial (Fin 3) (GenericField K):=surfaceMap phi J
 have hAne:A ≠ 0:=ZL phi
   (DI K) J hJne
 have hAR:A.degreeOf 1=0:=Nat.eq_zero_of_le_zero
   ((GO phi J 1).trans_eq hJR)
 have hAZ:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero
   ((GO phi J 2).trans_eq hJZ)
 let q:Polynomial (GenericField K):=
   RCN281.yProjection (GenericField K) A
 have hq:q ≠ 0:=
   RCN281.FJT A hAne hAR hAZ
 have hroots:∀z ∈ Gamma.image phi,z ∈ q.roots:=by
   intro z hz
   obtain ⟨S,hS,rfl⟩:=Finset.mem_image.mp hz
   apply (Polynomial.mem_roots hq).mpr
   change q.eval (phi S)=0
   have hv:VR phi S 0=phi S:=by
     simp [DGF]
   change (RCN281.yProjection (GenericField K) A).eval
     (phi S)=0
   rw [← hv,RCN281.GFE A hAR hAZ
     (VR phi S)]
   rw [ARD,LN,
     hsolutions S hS]
   simp
 have hcard:(Gamma.image phi).card=Gamma.card:=
   Finset.card_image_of_injective _ (DI K)
 rw [← hcard]
 calc
   (Gamma.image phi).card≤q.roots.toFinset.card:=by
     apply Finset.card_le_card
     intro z hz
     exact Multiset.mem_toFinset.mpr (hroots z hz)
   _≤q.roots.card:=Multiset.toFinset_card_le _
   _≤q.natDegree:=Polynomial.card_roots' q
   _≤A.degreeOf 0:=RCN281.EPT A
   _≤J.degreeOf 1:=GO phi J 0
   _≤AMW:=hJY
theorem FBO
   [CharP K prime]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0)
   (hbox:Q ∈ RCN279.BA K
     weightedCap w yTotalCap slopeCap)
   (hlegacy:Q ∈ RCN174.BA K
     weightedCap w yTotalCap slopeCap)
   (Gamma:Finset (Polynomial K))
   {Iota:Type} [Fintype Iota] [DecidableEq Iota]
   (nodes:Finset Iota) (x received:Iota→K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀S ∈ Gamma,S.natDegree≤w)
   (hsolutions:∀S ∈ Gamma,BM K S 0 Q=0)
   (hagreement:∀S ∈ Gamma,agreements≤
     (nodes.filter (fun i=>S.eval (x i)=received i)).card):
   Gamma.card≤listBudget:=by
 classical
 have hcaps:=DZS K Q hbox
 have hsing:(AGM K Q Gamma).card≤AMW:=
   EKU K Q hQ hbox (AGM K Q Gamma)
     (fun S hS=>(Finset.mem_filter.mp hS).2)
 have hreg (F:↥(FW Q)):
     (AFT K Q Gamma F).card*gap≤
       (n-w)*(capY*F.1.degreeOf 2+capR*F.1.degreeOf 1):=by
   have hdata:=ALY Q F.1 hQ weightedCap w yTotalCap slopeCap
     hlegacy F.2
   have hdivF:=(KR Q F.1 F.2).2.1
   have hFZ:F.1.degreeOf 3=0:=Nat.eq_zero_of_le_zero
     ((OI 3 F.1 Q hdivF hQ).trans_eq hcaps.2.2)
   have hsub:AFT K Q Gamma F ⊆ Gamma:=Finset.filter_subset _ _
   exact DMR K F.1 hdata.1 hdata.2.1 hdata.2.2
     ((OI 1 F.1 Q hdivF hQ).trans hcaps.1)
     ((OI 2 F.1 Q hdivF hQ).trans hcaps.2.1)
     hFZ (AFT K Q Gamma F)
     (fun S hS=>hdegree S (hsub hS))
     (fun S hS=>(Finset.mem_filter.mp hS).2.1)
     (fun S hS=>(Finset.mem_filter.mp hS).2.2)
     nodes x received hinj hnodes (fun S hS=>hagreement S (hsub hS))
 have hsumY:=AJJ
   (FW Q) id Q hQ (AGW Q hQ) 1
 have hsumR:=AJJ
   (FW Q) id Q hQ (AGW Q hQ) 2
 have hsumY':(∑ F:↥(FW Q),F.1.degreeOf 1)≤Q.degreeOf 1:=by
   simpa only [Finset.sum_coe_sort,id_eq] using hsumY
 have hsumR':(∑ F:↥(FW Q),F.1.degreeOf 2)≤Q.degreeOf 2:=by
   simpa only [Finset.sum_coe_sort,id_eq] using hsumR
 have hregularScaled:
     (∑ F:↥(FW Q),(AFT K Q Gamma F).card)*gap≤
       ALH:=by
   calc
     _= ∑ F:↥(FW Q),
         (AFT K Q Gamma F).card*gap:=by rw [Finset.sum_mul]
     _≤ ∑ F:↥(FW Q),
         (n-w)*(capY*F.1.degreeOf 2+capR*F.1.degreeOf 1):=
       Finset.sum_le_sum (fun F _=>hreg F)
     _=(n-w)*(capY*(∑ F:↥(FW Q),F.1.degreeOf 2)+
         capR*(∑ F:↥(FW Q),F.1.degreeOf 1)):=by
       rw [← Finset.mul_sum,Finset.sum_add_distrib,
         ← Finset.mul_sum,← Finset.mul_sum]
     _≤(n-w)*(capY*slopeCap+capR*yTotalCap):=by
       apply Nat.mul_le_mul_left
       exact Nat.add_le_add (Nat.mul_le_mul_left capY (hsumR'.trans hcaps.2.1))
         (Nat.mul_le_mul_left capR (hsumY'.trans hcaps.1))
     _=ALH:=rfl
 have hcover:=ERS K Q hQ Gamma hsolutions
 have hscaled:=Nat.mul_le_mul_right gap hcover
 have htotal:Gamma.card*gap≤BNF:=by
   calc
     Gamma.card*gap≤
         ((AGM K Q Gamma).card+
           ∑ F:↥(FW Q),(AFT K Q Gamma F).card)*gap:=
       hscaled
     _=(AGM K Q Gamma).card*gap+
         (∑ F:↥(FW Q),(AFT K Q Gamma F).card)*gap:=by
       ring
     _≤AMW*gap+ALH:=
       Nat.add_le_add (Nat.mul_le_mul_right gap hsing) hregularScaled
     _=BNF:=by
       simp only [BNF,FQ.BNF,
         ALH,AMW,gap]
       omega
 by_contra hnot
 have hlarge:listBudget<Gamma.card:=Nat.lt_of_not_ge hnot
 have hgap:0<gap:=gap_pos
 have hmul:=Nat.mul_lt_mul_of_pos_right hlarge hgap
 have hcontra:listBudget*gap<BNF:=hmul.trans_le htotal
 exact (Nat.not_lt_of_ge hcontra.le) DEN
end
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
local instance:CharP IRSProfile.Field prime:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem CNJ
   (received:IRSProfile.Index→IRSProfile.Field):
   ∃Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0∧
     Q ∈ RCN279.BA IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     Q ∈ RCN174.BA IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     ∀(P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree≤w→agreements≤support.card→
       (∀i ∈ support,P.eval (IRSProfile.domain i)=received i)→
       RCN319.BM IRSProfile.Field P 0 Q=0:=by
 classical
 obtain ⟨Q,hQ,hbox,hcontact⟩:=
   FQ.EDE received
 change Q ∈ RCN279.BA IRSProfile.Field
   weightedCap w yTotalCap slopeCap at hbox
 have hlegacy:Q ∈ RCN174.BA IRSProfile.Field
     weightedCap w yTotalCap slopeCap:=by
   intro d hd
   obtain ⟨hYR,hR,hZ,hweight⟩:=hbox hd
   exact ⟨by omega,hR,hweight⟩
 refine ⟨Q,hQ,hbox,hlegacy,?_⟩
 intro P support hdegree hcard hvalues
 apply RCN319.WH
   IRSProfile.Field Q P 0 IRSProfile.domain received (fun _=>0)
     support multiplicity
 · intro i hi r
   exact hcontact i r
 · intro i hi
   simpa only [mul_zero,add_zero] using hvalues i hi
 · have hdeg:=RCN319.AIJ
     IRSProfile.Field weightedCap w yTotalCap slopeCap Q P 0
     GFR
     hlegacy hdegree
   have hbound:weightedCap≤multiplicity*support.card:=by
     rw [weightedCap]
     exact Nat.mul_le_mul_left multiplicity hcard
   exact hdeg.trans_le hbound
theorem DQN
   (received:IRSProfile.Index→IRSProfile.Field)
   (L:Finset (IRSProfile.Index→IRSProfile.Field))
   (hcode:∀c ∈ L,c ∈ IRSProfile.baseCode)
   (hclose:∀c ∈ L,agreements≤
     (Finset.univ.filter (fun i=>c i=received i)).card):
   L.card≤listBudget:=by
 classical
 let D:=↥L
 let codeword:D→IRSProfile.baseCode:=fun c=>⟨c.1,hcode c.1 c.2⟩
 let selected:D→Polynomial IRSProfile.Field:=fun c=>ReedSolomon.toPolynomial (codeword c)
 let Gamma:Finset (Polynomial IRSProfile.Field):=Finset.univ.image selected
 have hselected:Function.Injective selected:=by
   intro c d h
   apply Subtype.ext
   funext i
   have hh:=congrArg (fun P:Polynomial IRSProfile.Field=>
     P.eval (IRSProfile.domain i)) h
   exact ReedSolomon.toPolynomial_eval_at_domain.symm.trans
     (hh.trans ReedSolomon.toPolynomial_eval_at_domain)
 have hcard:Gamma.card=L.card:=by
   rw [show Gamma=Finset.univ.image selected by rfl,
     Finset.card_image_of_injective _ hselected,Finset.card_univ,
     Fintype.card_coe]
 obtain ⟨Q,hQ,hbox,hlegacy,hvanish⟩:=
   CNJ received
 have hdegree:∀P ∈ Gamma,P.natDegree≤w:=by
   intro P hP
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
   have hp:=ReedSolomon.toPolynomial_mem_lt_deg (codeword c)
   have hdeg:(selected c).degree<((w+1:ℕ):WithBot ℕ):=by
     have hh:=Polynomial.mem_degreeLT.mp hp
     change (selected c).degree<
       ((IRSProfile.baseDimension:ℕ):WithBot ℕ) at hh
     rw [FGB] at hh
     exact hh
   by_cases hz:selected c=0
   · simp [hz]
   · rw [← Polynomial.natDegree_lt_iff_degree_lt hz] at hdeg
     omega
 have hsolution:∀P ∈ Gamma,BM IRSProfile.Field P 0 Q=0:=by
   intro P hP
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
   let A:=Finset.univ.filter (fun i=>c.1 i=received i)
   apply hvanish (selected c) A (hdegree (selected c)
     (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩))
     (hclose c.1 c.2)
   intro i hi
   have hcval:=ReedSolomon.toPolynomial_eval_at_domain (c:=codeword c) (i:=i)
   exact hcval.trans (Finset.mem_filter.mp hi).2
 have hagreement:∀P ∈ Gamma,agreements≤
     (Finset.univ.filter (fun i=>P.eval (IRSProfile.domain i)=received i)).card:=by
   intro P hP
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
   have heq:Finset.univ.filter
       (fun i=>(selected c).eval (IRSProfile.domain i)=received i)=
       Finset.univ.filter (fun i=>c.1 i=received i):=by
     apply Finset.filter_congr
     intro i hi
     rw [show (selected c).eval (IRSProfile.domain i)=c.1 i from
       ReedSolomon.toPolynomial_eval_at_domain]
   rw [heq]
   exact hclose c.1 c.2
 have hbound:=FBO IRSProfile.Field Q hQ hbox hlegacy Gamma
   (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain received
   IRSProfile.domain.injective.injOn
   (by simpa using FZR) hdegree hsolution hagreement
 rwa [hcard] at hbound
end
end ProximityPrize.SubmissionLower.CVH

end Compact_MovingFiberScalarList6815
end MergedPart0
section MergedPart1
section Compact_MovingFiberProtocol6815

namespace ProximityPrize.SubmissionLower.JC
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def errors:ℕ:=80909
def BBV:ℕ:=331407359
def ARQ:ℕ:=1073741824
def radius:ℝ≥0:=claimedRadius BBV ARQ
theorem radius_floor:
    ⌊(radius:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊ =errors:=by
  norm_num [radius,claimedRadius,BBV,ARQ,
    errors,IRSProfile.Index]
theorem FRV:
    radius ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
  constructor<;>norm_num [radius,claimedRadius,BBV,ARQ,
    IRSProfile.minRelativeDistance]
theorem FNG:(2:ℕ)^16*100000000^100≤111728714^100:=by decide
theorem FFP:
    (742334465:ℕ)^128*(2^68*111728714)≤100000000*1073741824^128:=by decide
theorem FGZ:
    (2:ℝ≥0)^((16:ℝ)/100)≤(111728714:ℝ≥0)/100000000:=by
  have hroot:((2:ℝ≥0)^(16:ℕ))^((100:ℝ)⁻¹)≤(111728714:ℝ≥0)/100000000:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ)<100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast FNG
  calc
    (2:ℝ≥0)^((16:ℝ)/100)=((2:ℝ≥0)^(16:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _≤_:=hroot
theorem FMO:
    (1-radius)^IRSProfile.repetitions≤
      ((1:ℝ≥0)/2^(68:ℕ))*(100000000/111728714):=by
  have hsub:(1-radius:ℝ≥0)=742334465/1073741824:=by
    have hr:radius≤1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,BBV,ARQ]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,BBV,ARQ]
  change (1-radius)^128≤((1:ℝ≥0)/2^(68:ℕ))*(100000000/111728714)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast FFP
theorem GIG:
    (1-radius)^IRSProfile.repetitions≤claimedError 6816:=by
  have hscale:(100000000:ℝ≥0)/111728714≤(2:ℝ≥0)^(-((16:ℝ)/100)):=by
    calc
      (100000000:ℝ≥0)/111728714=1/((111728714:ℝ≥0)/100000000):=by norm_num
      _≤1/((2:ℝ≥0)^((16:ℝ)/100)):=
        one_div_le_one_div_of_le (by positivity) FGZ
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1-radius)^IRSProfile.repetitions≤
        ((1:ℝ≥0)/2^(68:ℕ))*(100000000/111728714):=FMO
    _≤((1:ℝ≥0)/2^(68:ℕ))*(2:ℝ≥0)^(-((16:ℝ)/100)):=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6816:=by
      unfold claimedError
      rw [show-((((6816:ℕ):ℝ)/100))=
          -((68:ℕ):ℝ)+ -((16:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end ProximityPrize.SubmissionLower.JC

namespace ProximityPrize.SubmissionLower.AAZ
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem RCN018 RCN019 RCN284 RCN280
open scoped NNReal
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 5000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
def n:ℕ:=262144
def errors:ℕ:=80909
def agreements:ℕ:=n-errors
def listBudget:ℕ:=9661207595
def mcaBudget:ℕ:=274980718450187492
def radius:ℝ≥0:=JC.radius
theorem EWG:
   15*(listBudget+1).choose 2<Fintype.card IRSProfile.Field:=by
 rw [show Fintype.card IRSProfile.Field=(2130706433:ℕ)^6 by
   norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize],
   Nat.choose_eq_descFactorial_div_factorial]
 norm_num [listBudget,Nat.descFactorial_succ,Nat.factorial_succ]
theorem EOE
   (delta:ℝ)
   (hcell:(delta:ℝ)*(Fintype.card IRSProfile.Index:ℝ)<
     ((errors+1:ℕ):ℝ)):
   Code.Lambda
     (((IRSProfile.baseCode^⋈ (Fin 8))^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2→Fin 8→IRSProfile.Field)):
       Set (IRSProfile.Index→Fin 2→Fin 8→IRSProfile.Field))
     delta≤(listBudget:ℕ∞):=by
 apply RCN280.BPX
   IRSProfile.baseCode errors listBudget ?_ delta hcell
 intro received L hrows hclose
 have hclose':∀v ∈ L,agreements≤
     (Finset.univ.filter (fun i=>v i=received i)).card:=by
   intro v hv
   have hc:Fintype.card IRSProfile.Index=n:=Fintype.card_fin _
   have he:n-errors=agreements:=by decide+kernel
   have hh:=hclose v hv
   rw [hc,he] at hh
   exact hh
 classical
 letI:DecidableEq (IRSProfile.Index→Fin 16→IRSProfile.Field):=Classical.decEq _
 letI:DecidableEq (IRSProfile.Index→IRSProfile.Field):=Classical.decEq _
 by_contra hnot
 obtain ⟨D,hDL,hDcard⟩:=
   Finset.exists_subset_card_eq (show listBudget+1≤L.card by omega)
 have hsepD:15*D.card.choose 2<Fintype.card IRSProfile.Field:=by
   rw [hDcard]
   exact EWG
 obtain ⟨t,ht⟩:=CXX D hsepD
 let projected:Finset (IRSProfile.Index→IRSProfile.Field):=
   D.image (YG (ι:=IRSProfile.Index) (r:=16) t)
 have hprojcard:projected.card=D.card:=Finset.card_image_of_injOn ht
 have hcode:∀c ∈ projected,c ∈ IRSProfile.baseCode:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact EJZ IRSProfile.baseCode t v (hrows v (hDL hv))
 have hnear:∀c ∈ projected,agreements≤
     (Finset.univ.filter (fun i=>c i=YG t received i)).card:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact (hclose' v (hDL hv)).trans
     (Finset.card_le_card (CPL t v received))
 have hbound:=CVH.DQN
   (YG t received) projected hcode hnear
 change projected.card≤listBudget at hbound
 rw [hprojcard,hDcard] at hbound
 omega
theorem lambda_le:
   Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2→Fin IRSProfile.interleaving→IRSProfile.Field)):
       Set (IRSProfile.Index→Fin 2→Fin IRSProfile.interleaving→IRSProfile.Field))
     (radius:ℝ)≤(listBudget:ℕ∞):=by
 rw [EXQ]
 apply EOE (radius:ℝ)
 norm_num [radius,JC.radius,claimedRadius,
   JC.BBV,
   JC.ARQ,
   errors,IRSProfile.Index]
theorem EOJ
   (halign:ADO IRSProfile.baseCode errors mcaBudget):
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ)≤
     ENNReal.ofReal ((mcaBudget:ℝ)/Fintype.card IRSProfile.Field):=by
 apply BZM
 apply DJP IRSProfile.baseCode
   (radius:ℝ) errors mcaBudget
 · intro A hA
   have hcomp:=
     (mul_one_sub_le_card_iff_sub_card_le_floor A
       (show (0:ℝ)≤(radius:ℝ) by positivity)).mp hA
   rw [show ⌊(radius:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊ =errors by
     simpa only [radius,errors,JC.errors] using
       JC.radius_floor] at hcomp
   have hn:Fintype.card IRSProfile.Index=262144:=by
     norm_num [IRSProfile.Index]
   rw [hn]
   norm_num [errors,JC.errors] at hcomp ⊢
   omega
 · exact halign
theorem FIT
   (halign:ADO IRSProfile.baseCode errors mcaBudget):
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
       (radius:ℝ)≤
     (mcaBudget:ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
 calc
   _≤mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ):=by
     rw [RCN284.DXQ]
     exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
       IRSProfile.interleaving radius
       (by norm_num [IRSProfile.interleaving])
       (by norm_num [radius,JC.radius,
         claimedRadius,JC.BBV,
         JC.ARQ])
       (by norm_num [radius,JC.radius,
         claimedRadius,JC.BBV,
         JC.ARQ])
   _≤ENNReal.ofReal
       ((mcaBudget:ℝ)/Fintype.card IRSProfile.Field):=
     EOJ halign
   _=(mcaBudget:ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
       ENNReal.ofReal_natCast]
theorem FFY:
   2^(128:ℕ)*(mcaBudget+listBudget)≤
     Fintype.card IRSProfile.Field:=by
 rw [RCN284.BIS]
 norm_num [mcaBudget,listBudget]
theorem CWB
   (halign:ADO IRSProfile.baseCode errors mcaBudget):
   certifiedGammaError IRSProfile.code radius≤
     (1:ℝ≥0)/2^(128:ℕ):=by
 rw [← ENNReal.coe_le_coe,coe_certifiedGammaError]
 push_cast
 have hLambdaNat:=ENat.toNat_le_of_le_coe lambda_le
 have hList:
     ((Code.Lambda
       ((IRSProfile.code^⋈ (Fin 2):
         ModuleCode IRSProfile.Index IRSProfile.Field
           (Fin 2→Fin IRSProfile.interleaving→IRSProfile.Field)):
         Set (IRSProfile.Index→Fin 2→Fin IRSProfile.interleaving→
           IRSProfile.Field))
       (radius:ℝ)).toNat:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal)≤
       (listBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal):=
   ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
 calc
   _≤(mcaBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal)+
       (listBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal):=
     add_le_add (FIT halign) hList
   _=((mcaBudget+listBudget:ℕ):ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [← ENNReal.add_div,Nat.cast_add]
   _≤(1:ENNReal)/2^(128:ℕ):=by
     apply RCN284.FMW
     · norm_num [mcaBudget,listBudget]
     · simpa only [Nat.mul_comm] using FFY
theorem DPA
   (halign:ADO IRSProfile.baseCode errors mcaBudget):
   ProtocolClaim 6816 331407359 1073741824 where
 admissible:=JC.FRV
 reduction:=by
   change certifiedGammaError IRSProfile.code radius≤reductionTarget
   simpa [reductionTarget,ProximityGap.prizeThreshold] using
     CWB halign
 score:=by
   change (1-JC.radius)^
     IRSProfile.repetitions≤claimedError 6816
   exact JC.GIG
end
end ProximityPrize.SubmissionLower.AAZ

end Compact_MovingFiberProtocol6815

section Compact_Protocol80850

namespace ProximityPrize.SubmissionLower.Lower80860.Protocol
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem RCN018 RCN019 RCN284 RCN280

end ProximityPrize.SubmissionLower.Lower80860.Protocol

end Compact_Protocol80850
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.CPX
open scoped BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN095 RCN136 RCN187 RCN204 RCN207 RCN257 RCN313 RCN341
open DX BX FR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000

private theorem BIH {L:Type*} [Field L]
    (v:Valuation L (WithZero (Multiplicative ℤ))) (x:L) (b:ℤ)
    (hb:0≤b) (hx:v x≤WithZero.exp b):poleOrder v x≤b:=by
  unfold poleOrder
  apply max_le hb
  by_cases hz:v x=0
  · simpa only [hz,WithZero.log_zero] using hb
  · simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hz WithZero.exp_ne_zero).mpr hx

theorem EIF {E L:Type*} [Field E] [Field L]
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (coeff:E→+*L) (hc: ∀c,v (coeff c)≤1)
    (x:Fin 3→L) (sigma:L) (Q U:MvPolynomial (Fin 3) E) (target:E)
    (hQ:BI (2 • unitAllFlag) Q)
    (hU:BI unitYZFlag U):
    poleOrder v (coeff target-MvPolynomial.eval₂Hom coeff x Q-
      MvPolynomial.eval₂Hom coeff x U*sigma)≤
      max (2*flagPole v x unitAllFlag)
        (flagPole v x unitYZFlag+poleOrder v sigma):=by
  let theta:=max (2*flagPole v x unitAllFlag)
    (flagPole v x unitYZFlag+poleOrder v sigma)
  have htheta:0≤theta:=
    (mul_nonneg (by norm_num) (ALZ _ _ _)).trans (le_max_left _ _)
  apply BIH v _ theta htheta
  apply v.map_sub_le
  · have hv:=ADJ v coeff hc x (2 • unitAllFlag)
      (MvPolynomial.C target-Q) (BBP (inFlag_const _ _) hQ)
    have he:flagPole v x (2 • unitAllFlag)=2*flagPole v x unitAllFlag:=by
      simp only [flagPole,nsmul_zOnly,nsmul_yz,nsmul_all,unitAllFlag]
      norm_num
    simp only [map_sub,MvPolynomial.eval₂Hom_C,he] at hv
    exact hv.trans (WithZero.exp_le_exp.mpr (le_max_left _ _))
  · have hu:=ADJ v coeff hc x unitYZFlag U hU
    have hs:v sigma≤WithZero.exp (poleOrder v sigma):=
      WithZero.le_exp_of_log_le (le_max_right _ _)
    rw [map_mul]
    exact (mul_le_mul' hu hs).trans (by
      rw [← WithZero.exp_add]
      exact WithZero.exp_le_exp.mpr (le_max_right _ _))

variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]

theorem EPX
    (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base:BP C)
    (P:Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(asS P).natDegree)
    (hF:surfaceMap phi F ∈ C)
    (hH:surfaceMap phi (polyH K F) ∉ C)
    (hlead:surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv: ∀j≤k,F ∣ helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (Q A:MvPolynomial (Fin 3) E) (target:E)
    (hQ:BI (2 • unitAllFlag) Q)
    (hA:BI unitYZFlag A)
    (CV:ℕ)
    (hbudget: ∀W:Finset (Place E (AJ E C)),
      (∑ nu ∈ W,flagPole nu.val (coordinate E C)
        (EJ.budgetFlag B U T (k+1) n0))≤(CV:ℤ))
    (W:Finset (Place E (AJ E C))):
    ((k+1:ℕ):ℤ)*(∑ nu ∈ W,poleOrder nu.val
      (algebraMap E (AJ E C) target-BR E C Q-
        BR E C A*RCN064.movingRatio C
          (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F))))≤(CV:ℤ):=by
  letI:=IP E C base.index
  letI:=DT E C base.index base.transcendental
  letI:=IU E C base.index
  letI:=_Q5 E C base.index base.transcendental
  letI:=IS E C base.index base.transcendental
  letI:FiniteDimensional (RatFunc E) (AJ E C):=base.finite
  letI:Algebra.IsSeparable (RatFunc E) (AJ E C):=base.separable
  have hdeg:=CT.ELO phi C P hlead
  have hroot:=CT.FKC phi C P F s k hS
    hF hH hlead hdiv h2 hfact
  have hdegree:n0≤(CT.AGC phi C P).natDegree:=by
    rw [hdeg.2]
    exact hn
  have hs:=EJ.moving_bound
    (MvPolynomial.map (phi.comp Polynomial.C) P) (phi Polynomial.X)
    B U T (k+1) n0 hBU hUT hdn hB
    (BZJ.DVE _ P B U T hP)
    (coordinate E C) (CT.AGC phi C P)
    (CT.coefficients phi C P) hdeg.1 hdegree
    (RCN064.movingRatio C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F))/2) hroot (CV:ℤ) hbudget W
  simp only [CWV.pole_half _ h2] at hs
  apply le_trans _ hs
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
  apply Finset.sum_le_sum
  intro nu _
  have hh:=EIF nu.val (algebraMap E (AJ E C))
    (RCN344.NP E (AJ E C) nu) (coordinate E C)
    (RCN064.movingRatio C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
    Q A target hQ hA
  simpa only [HJ,MvPolynomial.aeval_eq_eval₂Hom] using hh

theorem DVQ
    (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base:BP C)
    (P:Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(asS P).natDegree)
    (hF:surfaceMap phi F ∈ C)
    (hH:surfaceMap phi (polyH K F) ∉ C)
    (hlead:surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv: ∀j≤k,F ∣ helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (Q A:MvPolynomial (Fin 3) E) (target:E)
    (hQ:BI (2 • unitAllFlag) Q)
    (hA:BI unitYZFlag A)
    (hproper:JF (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) Q A target ∉ C)
    (CV:ℕ)
    (hbudget: ∀W:Finset (Place E (AJ E C)),
      (∑ nu ∈ W,flagPole nu.val (coordinate E C)
        (EJ.budgetFlag B U T (k+1) n0))≤(CV:ℤ)):
    RCN271.ABY C (surfaceMap phi (polyH K F))
      (JF (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) (CV/(k+1)):=by
  let H:=surfaceMap phi (polyH K F)
  let G:=surfaceMap phi (polyG K F)
  have hHne:BR E C H ≠ 0:=by
    intro hz
    exact hH ((CT.AAE C _).mp hz)
  have hnorm:MvPolynomial.aeval (coordinate E C) (JF H G Q A target)/
      MvPolynomial.aeval (coordinate E C) H=
      algebraMap E (AJ E C) target-BR E C Q-
        BR E C A*RCN064.movingRatio C H G:=by
    simp only [JF,map_sub,map_mul,MvPolynomial.aeval_C,
      RCN064.movingRatio,HJ] at*
    field_simp
  apply AIR E C base H _ 1 (CV/(k+1)) hproper hH
  intro W
  have hsource:=EPX phi F C base P B U T s k n0
    hS hP hBU hUT hdn hB hn hF hH hlead hdiv h2 hfact Q A target hQ hA CV hbudget W
  simp only [pow_one]
  change (∑ nu ∈ W,poleOrder nu.val
    (MvPolynomial.aeval (coordinate E C) (JF H G Q A target)/
      MvPolynomial.aeval (coordinate E C) H))≤((CV/(k+1):ℕ):ℤ)
  simp_rw [hnorm]
  rw [Int.natCast_ediv]
  apply (Int.le_ediv_iff_mul_le (by positivity:(0:ℤ)<((k+1:ℕ):ℤ))).mpr
  simpa only [H,G,mul_comm] using hsource

end
end ProximityPrize.SubmissionLower.CPX
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.CBU
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN039 RCN046 RCN084 RCN095
open RCN114 RCN136 RCN187 RCN204 RCN207 RCN237 RCN257 RCN264 RCN271 RCN313 RCN340 RCN341
open DX BX FR
open CPX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
local instance:DecidableEq E:=Classical.decEq E
local notation "Poly3" =>MvPolynomial (Fin 3) E

private theorem GHB
    {G N R:Poly3} {p q:FlagDegree}
    {base: ∀C:AU E G N R,BP C.1}
    (U:QZ base p q) (C:AU E G N R)
    (V:FlagDegree) (W:Finset (Place E (AJ E C.1))):
    (∑ nu ∈ W,flagPole nu.val (coordinate E C.1) V)≤
      (U.toFE.weightedCost V C:ℤ):=by
  have hz:=U.zPole C W
  have hy:=U.yzPole C W
  have ha:=U.allPole C W
  simp only [UC] at hz
  simp only [QD] at hy
  simp only [SF] at ha
  have h:=add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg V.zOnly))
    (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg V.yz)))
    (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg V.all))
  simpa only [flagPole,Finset.sum_add_distrib,← Finset.mul_sum,
    FE.weightedCost,QZ.toFE,
    Nat.cast_add,Nat.cast_mul] using h

theorem DSR
    (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (carrier N:Poly3) (p q:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:BI p carrier) (hNflag:BI q N)
    (c:ℕ) [CharP E c]
    (hdeg:p.zOnly+p.yz+p.all<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c)
    (P:Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(asS P).natDegree)
    (hdiv: ∀j≤k,F ∣ helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (Q A:Poly3) (target:E)
    (hQ:BI (2 • unitAllFlag) Q)
    (hA:BI unitYZFlag A)
    (points:Finset (Fin 3→E))
    (hpoints: ∀x ∈ points,
      MvPolynomial.eval x carrier=0∧MvPolynomial.eval x N=0∧
      MvPolynomial.eval x (JF (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target)=0∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)) ≠ 0∧
      MvPolynomial.eval x (surfaceMap phi (asS P).leadingCoeff) ≠ 0∧
      MvPolynomial.eval x (MvPolynomial.pderiv (1:Fin 3) carrier) ≠ 0)
    (hisolated: ∀x ∈ points,UK carrier N
      (JF (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) x):
    (k+1)*points.card≤
      flagMixed p q (EJ.budgetFlag B U T (k+1) n0):=by
  classical
  let H:=surfaceMap phi (polyH K F)
  let L:=surfaceMap phi (asS P).leadingCoeff
  let R:=H*L
  let M:=JF H (surfaceMap phi (polyG K F)) Q A target
  let V:=EJ.budgetFlag B U T (k+1) n0
  have hR: ∀x ∈ points,MvPolynomial.eval x R ≠ 0:=by
    intro x hx
    simpa only [R,map_mul] using mul_ne_zero (hpoints x hx).2.2.2.1 (hpoints x hx).2.2.2.2.1
  have hcover: ∀x ∈ points,∃g: ↥(HR carrier N),MvPolynomial.eval x g.1=0:=by
    intro x hx
    exact AAU carrier N M R hcarrier x
      (hpoints x hx).1 (hpoints x hx).2.2.1 (hR x hx)
      (hpoints x hx).2.2.2.2.2 (hisolated x hx)
  obtain ⟨base,hY,hZ⟩:=AOE carrier N R hcarrier p q hflag hNflag c hdeg hmix
  let S (g: ↥(HR carrier N)):Finset (Fin 3→E):=
    points.filter (fun (x:Fin 3→E)=>MvPolynomial.eval x g.1=(0:E))
  have hcoverage:points ⊆ Finset.univ.biUnion S:=by
    intro x hx
    obtain ⟨g,hg⟩:=hcover x hx
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hg⟩⟩
  have hcount (g: ↥(HR carrier N)):
      (k+1)*(S g).card≤flagMixed (exactFlag g.1) q V:=by
    have hg:=OJ carrier N g
    obtain ⟨unit⟩:=ACA (exactFlag g.1) q
      (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
      ((EI _ _).mpr (ATU g.1))
      ((EI _ _).mpr hNflag)
    let budget:=unit.toFE
    have hcard:=WX E g.1 N R (S g) id
      (fun x hx=>(Finset.mem_filter.mp hx).2)
      (fun x hx=>(hpoints x (Finset.mem_filter.mp hx).1).2.1)
      (fun x hx=>hR x (Finset.mem_filter.mp hx).1)
    have hlocal (C:AU E g.1 N R):
        (k+1)*(HF E g.1 N R (S g) id C).card≤budget.weightedCost V C:=by
      by_cases he:(HF E g.1 N R (S g) id C).Nonempty
      · obtain ⟨x,hx⟩:=he
        have hxS:=LU E g.1 N R (S g) id C hx
        have hxpoints:=(Finset.mem_filter.mp hxS).1
        have hxC:=MC E g.1 N R (S g) id C x hx
        have hcar:carrier ∈ C.1:=C.1.mem_of_dvd hg.2.1 (EN E g.1 N R C)
        have hF:surfaceMap phi F ∈ C.1:=C.1.mem_of_dvd hcarrierF hcar
        have hH:H ∉ C.1:=by
          intro hh
          exact _Q6 E g.1 N R C (C.1.mul_mem_right L hh)
        have hL:L ∉ C.1:=by
          intro hl
          exact _Q6 E g.1 N R C (C.1.mul_mem_left H hl)
        have hproper:M ∉ C.1:=hisolated x hxpoints C.1 inferInstance
          (PU E g.1 N R C) hxC hcar (GV E g.1 N R C)
        have hb:=DVQ phi F C.1 (base g C) P B U T s k n0
          hS hP hBU hUT hdn hB hn hF hH hL hdiv h2 hfact Q A target hQ hA hproper
          (budget.weightedCost V C) (fun W=>GHB unit.toQZ C V W)
        have hc:=hb (HF E g.1 N R (S g) id C)
          (fun y hy=>MC E g.1 N R (S g) id C y hy)
          (fun y hy=>(hpoints y (Finset.mem_filter.mp
            (LU E g.1 N R (S g) id C hy)).1).2.2.2.1)
          (fun y hy=>(hpoints y (Finset.mem_filter.mp
            (LU E g.1 N R (S g) id C hy)).1).2.2.1)
        exact (Nat.mul_le_mul_left (k+1) hc).trans (by
          simpa only [Nat.mul_comm] using Nat.div_mul_le_self (budget.weightedCost V C) (k+1))
      · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.mul_zero,Nat.zero_le]
    calc
      (k+1)*(S g).card≤(k+1)*∑ C:AU E g.1 N R,
          (HF E g.1 N R (S g) id C).card:=Nat.mul_le_mul_left _ hcard
      _= ∑ C:AU E g.1 N R,
          (k+1)*(HF E g.1 N R (S g) id C).card:=Finset.mul_sum _ _ _
      _≤ ∑ C:AU E g.1 N R,budget.weightedCost V C:=Finset.sum_le_sum (fun C _=>hlocal C)
      _≤_:=budget.DGB V
  have hc:=(Finset.card_le_card hcoverage).trans Finset.card_biUnion_le
  calc
    (k+1)*points.card≤(k+1)*∑ g: ↥(HR carrier N),(S g).card:=Nat.mul_le_mul_left _ hc
    _= ∑ g: ↥(HR carrier N),(k+1)*(S g).card:=Finset.mul_sum _ _ _
    _≤ ∑ g: ↥(HR carrier N),flagMixed (exactFlag g.1) q V:=Finset.sum_le_sum (fun g _=>hcount g)
    _≤_:=ASF carrier N hcarrier p q V hflag

end
end ProximityPrize.SubmissionLower.CBU
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.AUK
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN072 RCN076 RCN084 RCN095 RCN134 RCN136
open RCN207 RCN208 RCN237 RCN264 RCN313 RCN341 RCN344
open DX BX FR
open CBU
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

variable {K Ω E:Type} [Field K] [Field Ω] [Field E] [IsAlgClosed Ω] [IsAlgClosed E]
  [Algebra Ω E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E]
local instance:DecidableEq Ω:=Classical.decEq Ω
local instance:DecidableEq E:=Classical.decEq E

omit [IsAlgClosed Ω] [IsAlgClosed E] [Algebra (RatFunc Ω) E]
  [IsScalarTower Ω (RatFunc Ω) E] in
private theorem US (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K):
    CD Ω E (surfaceMap phi F)=
      surfaceMap ((algebraMap Ω E).comp phi) F:=by
  simp only [CD,surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]

private theorem FSO {R:Type*} [CommRing R] (F H G:R):
    filteredCut 0 (fun _:Fin 1=>F) H G=F:=by
  simp [filteredCut]

omit [IsAlgClosed Ω] in
theorem DLA {ι:Type} [Fintype ι]
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (carrier:MvPolynomial (Fin 3) Ω) (p q:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:BI p carrier)
    (ell:MvPolynomial (Fin 3) Ω) (hell:BI q ell)
    (c:ℕ) [CharP E c]
    (hdeg:p.zOnly+p.yz+p.all<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c)
    (P:Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(asS P).natDegree)
    (hdiv: ∀j≤k,F ∣ helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (Q A:MvPolynomial (Fin 3) Ω) (target:Ω)
    (hQ:BI (2 • unitAllFlag) Q)
    (hA:BI unitYZFlag A)
    (old:ι→AU Ω carrier
      (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff))
    (hold:Function.Injective old)
    (projection: ∀i,DB Ω (AJ Ω (old i).1))
    (hvalue: ∀i,DB.value Ω (AJ Ω (old i).1) (projection i)=
      BR Ω (old i).1 ell):
    (k+1)*(∑ i,DB.degree Ω (AJ Ω (old i).1) (projection i))≤
      flagMixed p q (EJ.budgetFlag B U T (k+1) n0):=by
  classical
  let H:=surfaceMap phi (polyH K F)
  let G:=surfaceMap phi (polyG K F)
  let L:=surfaceMap phi (asS P).leadingCoeff
  let R:=H*L
  let M:=JF H G Q A target
  have hderiv:H ∈ Ideal.span
      ({carrier,MvPolynomial.pderiv (1:Fin 3) carrier}:Set (MvPolynomial (Fin 3) Ω)):=by
    let carrierIdeal:=Ideal.span
      ({carrier,MvPolynomial.pderiv (1:Fin 3) carrier}:Set (MvPolynomial (Fin 3) Ω))
    have hcar:carrier ∈ carrierIdeal:=Ideal.subset_span (by simp)
    have hdc:MvPolynomial.pderiv (1:Fin 3) carrier ∈ carrierIdeal:=Ideal.subset_span (by simp)
    obtain ⟨b,hb⟩:=hcarrierF
    change surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F) ∈ carrierIdeal
    rw [← RCN267.ZO,hb,MvPolynomial.pderiv_mul]
    exact carrierIdeal.add_mem (carrierIdeal.mul_mem_right b hdc)
      (carrierIdeal.mul_mem_right (MvPolynomial.pderiv (1:Fin 3) b) hcar)
  let mu:=CD Ω E
  let phiE:=(algebraMap Ω E).comp phi
  let prime:=fun i=>(old i).1
  letI: ∀i,Algebra (RatFunc Ω) (AJ Ω (prime i)):=
    fun i=>(projection i).embedding.toRingHom.toAlgebra
  letI: ∀i,IsScalarTower Ω (RatFunc Ω) (AJ Ω (prime i)):=
    fun i=>IsScalarTower.of_algebraMap_eq (fun a=>((projection i).embedding.commutes a).symm)
  letI: ∀i,FiniteDimensional (RatFunc Ω) (AJ Ω (prime i)):=fun i=>(projection i).finite
  letI: ∀i,Algebra.IsSeparable (RatFunc Ω) (AJ Ω (prime i)):=fun i=>(projection i).separable
  let points:=BAN (B:=RatFunc Ω) (L:=E) prime
  let t:=algebraMap (RatFunc Ω) E (RCN202.PF Ω)
  let N:=MvPolynomial.C t-mu ell
  have hprime:Function.Injective prime:=by
    intro i j hij
    exact hold (Subtype.ext hij)
  have hNflag:BI q N:=
    BBP (inFlag_const _ _) (inFlag_map _ hell)
  have hmuM:mu M=JF (surfaceMap phiE (polyH K F))
      (surfaceMap phiE (polyG K F)) (mu Q) (mu A) (algebraMap Ω E target):=by
    simp only [M,JF,map_sub,map_mul]
    rw [show mu H=surfaceMap phiE (polyH K F) from US phi _,
      show mu G=surfaceMap phiE (polyG K F) from US phi _]
    simp only [mu,CD,MvPolynomial.map_C]
  have certificate (i:ι) (f:AJ Ω (prime i)→ₐ[RatFunc Ω] E):
      let x:=GM (prime i) (f.restrictScalars Ω)
      MvPolynomial.eval x (mu carrier)=0∧MvPolynomial.eval x N=0∧
      MvPolynomial.eval x (mu M)=0∧MvPolynomial.eval x (mu R) ≠ 0∧
      UK (mu carrier) N (mu M) x:=by
    let C0:AU Ω carrier (filteredCut 0 (fun _:Fin 1=>M) R 0) R:=
      ⟨(old i).1,by simpa only [FSO] using (old i).2⟩
    letI:Algebra (RatFunc Ω) (AJ Ω C0.1):=
      (projection i).embedding.toRingHom.toAlgebra
    have hj:algebraMap (RatFunc Ω) (AJ Ω C0.1) (RCN202.PF Ω)=
        movingValue C0.1 R 0 ell 1:=by
      change DB.value Ω (AJ Ω (old i).1) (projection i)=_
      simpa only [movingValue,map_one,map_zero,mul_zero,zero_div,add_zero] using hvalue i
    have hone:(1:MvPolynomial (Fin 3) Ω) ∉ C0.1:=by
      intro h
      have hz:=(CT.AAE C0.1 1).mpr h
      exact one_ne_zero (by simpa only [map_one] using hz)
    have hc:=RCN202.VX carrier R 0 ell 1 0
      (fun _:Fin 1=>M) C0 hj hone f
    have hc' :
        let x:=GM (prime i) (f.restrictScalars Ω)
        MvPolynomial.eval x (mu carrier)=0∧MvPolynomial.eval x (mu R*N)=0∧
        MvPolynomial.eval x (mu M)=0∧MvPolynomial.eval x (mu R) ≠ 0∧
        UK (mu carrier) (mu R*N) (mu M) x:=by
      simpa only [map_zero,map_one,JF,AEY,FSO,
        mul_zero,sub_zero,mul_one,MvPolynomial.aeval_eq_eval] using hc
    dsimp only at hc' ⊢
    have hn:MvPolynomial.eval (GM (prime i) (f.restrictScalars Ω)) N=0:=
      (mul_eq_zero.mp (by simpa only [map_mul] using hc'.2.1)).resolve_left hc'.2.2.2.1
    refine ⟨hc'.1,hn,hc'.2.2.1,hc'.2.2.2.1,?_⟩
    intro D hD hnot hp hF hN
    exact hc'.2.2.2.2 D hD hnot hp hF (D.mul_mem_left (mu R) hN)
  have hpoints: ∀x ∈ points,
      MvPolynomial.eval x (mu carrier)=0∧MvPolynomial.eval x N=0∧
      MvPolynomial.eval x (mu M)=0∧
      MvPolynomial.eval x (surfaceMap phiE (polyH K F)) ≠ 0∧
      MvPolynomial.eval x (surfaceMap phiE (asS P).leadingCoeff) ≠ 0∧
      MvPolynomial.eval x (MvPolynomial.pderiv (1:Fin 3) (mu carrier)) ≠ 0:=by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩:=Finset.mem_image.mp hx
    have hc:=certificate i f
    have hRne:=hc.2.2.2.1
    have hHL:MvPolynomial.eval (GM (prime i) (f.restrictScalars Ω)) (mu H) ≠ 0∧
        MvPolynomial.eval (GM (prime i) (f.restrictScalars Ω)) (mu L) ≠ 0:=by
      simpa only [R,map_mul,mul_ne_zero_iff] using hRne
    have hHne:MvPolynomial.eval (GM (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (polyH K F)) ≠ 0:=by simpa only [H,mu,US,phiE] using hHL.1
    have hLne:MvPolynomial.eval (GM (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (asS P).leadingCoeff) ≠ 0:=by simpa only [L,mu,US,phiE] using hHL.2
    have hd:=AUO (MvPolynomial.eval (GM (prime i) (f.restrictScalars Ω)))
      (mu carrier) (mu H) (DOV carrier H hderiv) hc.1 hHL.1
    exact ⟨hc.1,hc.2.1,hc.2.2.1,hHne,hLne,hd⟩
  have hiso: ∀x ∈ points,UK (mu carrier) N (mu M) x:=by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩:=Finset.mem_image.mp hx
    exact (certificate i f).2.2.2.2
  have hcar:mu carrier ∣ surfaceMap phiE F:=by
    simpa only [mu,US,phiE] using map_dvd mu hcarrierF
  have hmu:Function.Injective mu:=MvPolynomial.map_injective (algebraMap Ω E) (algebraMap Ω E).injective
  have hne:mu carrier ≠ 0:=fun hz=>hcarrier (hmu (by simpa only [map_zero] using hz))
  rw [hmuM] at hpoints hiso
  have hc:=DSR phiE F (mu carrier) N p q hne hcar
    (inFlag_map _ hflag) hNflag c hdeg hmix P B U T s k n0 hS hP hBU hUT hdn hB hn hdiv h2 hfact
    (mu Q) (mu A) (algebraMap Ω E target) (inFlag_map _ hQ) (inFlag_map _ hA) points hpoints hiso
  have hcard:=BAW (B:=RatFunc Ω) (L:=E) prime hprime
  simpa only [points,hcard,DB.degree,prime] using hc

omit [IsAlgClosed Ω] in
theorem BIQ {ι:Type} [Fintype ι]
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (carrier:MvPolynomial (Fin 3) Ω) (p q:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:BI p carrier)
    (ell:MvPolynomial (Fin 3) Ω) (hell:BI q ell)
    (c:ℕ) [CharP E c]
    (hdeg:p.zOnly+p.yz+p.all<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c)
    (P:Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(asS P).natDegree)
    (hdiv: ∀j≤k,F ∣ helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (Q A:MvPolynomial (Fin 3) Ω) (target:Ω)
    (hQ:BI (2 • unitAllFlag) Q)
    (hA:BI unitYZFlag A)
    (old:ι→AU Ω carrier
      (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff))
    (hold:Function.Injective old)
    (projection: ∀i,Coordinate Ω (AJ Ω (old i).1))
    (hvalue: ∀i,FT Ω (AJ Ω (old i).1) (projection i)=
      BR Ω (old i).1 ell):
    (k+1)*(∑ i,DQ Ω (AJ Ω (old i).1) (projection i))≤
      flagMixed p q (EJ.budgetFlag B U T (k+1) n0):=by
  classical
  let Alive:Set ι:={i | ∃C,projection i=Sum.inr C}
  let sep:=fun i:Alive=>Classical.choose i.2
  have hsep (i:Alive):projection i.1=Sum.inr (sep i):=Classical.choose_spec i.2
  let old0:=fun i:Alive=>old i.1
  have hi0:Function.Injective old0:=by
    intro i j h
    exact Subtype.ext (hold h)
  have hv0 (i:Alive):
      DB.value Ω (AJ Ω (old0 i).1) (sep i)=
        BR Ω (old0 i).1 ell:=by
    have h:=hvalue i.1
    rw [hsep i] at h
    exact h
  have hsum:(∑ i,DQ Ω (AJ Ω (old i).1) (projection i))=
      ∑ i:Alive,DB.degree Ω (AJ Ω (old0 i).1) (sep i):=by
    apply Finset.sum_congr_set Alive
      (fun i=>DQ Ω (AJ Ω (old i).1) (projection i))
      (fun i=>DB.degree Ω (AJ Ω (old0 i).1) (sep i))
    · intro i hi
      simp only [hsep ⟨i,hi⟩,DQ,Sum.elim_inr,old0]
    · intro i hi
      cases hp:projection i with
      | inl C=>simp only [DQ,Sum.elim_inl]
      | inr C=>exact (hi ⟨C,hp⟩).elim
  rw [hsum]
  exact DLA (E:=E) phi F carrier p q hcarrier hcarrierF hflag ell hell
    c hdeg hmix P B U T s k n0 hS hP hBU hUT hdn hB hn hdiv h2 hfact Q A target hQ hA
    old0 hi0 sep hv0

end
end ProximityPrize.SubmissionLower.AUK
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.BFL
open scoped Classical BigOperators
open RCN002 RCN022 RCN037 RCN039 RCN042 RCN046 RCN071 RCN076 RCN084 RCN093 RCN095 RCN135 RCN136 RCN207
open RCN237 RCN264 RCN313 RCN340 RCN341 RCN344
open DX BX FR
open AUK
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 40000
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq Ω:=Classical.decEq Ω
local notation "Poly3" =>MvPolynomial (Fin 3) Ω

def linearZ:Poly3:=MvPolynomial.X 2
def linearU (a:Ω):Poly3:=MvPolynomial.X 0+MvPolynomial.C a*MvPolynomial.X 2
def linearA (b a:Ω):Poly3:=MvPolynomial.X 1+MvPolynomial.C b*MvPolynomial.X 0+
  MvPolynomial.C (b*a)*MvPolynomial.X 2

omit [IsAlgClosed Ω] in
private theorem flag_X (i:Fin 3) (p:FlagDegree)
    (hi:InFlag p (Finsupp.single i 1)):BI p (MvPolynomial.X i:Poly3):=by
  intro e he
  have:e=Finsupp.single i 1:=by simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  subst e
  exact hi
omit [IsAlgClosed Ω] in
private theorem flag_add {p:FlagDegree} {A B:Poly3}
    (hA:BI p A) (hB:BI p B):BI p (A+B):=by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hA e h
  · exact hB e h
omit [IsAlgClosed Ω] in
private theorem flag_scale {p:FlagDegree} {A:Poly3} (c:Ω)
    (hA:BI p A):BI p (MvPolynomial.C c*A):=by
  intro e he
  rw [← MvPolynomial.smul_eq_C_mul] at he
  exact hA e (MvPolynomial.support_smul he)

theorem linearZ_flag:BI unitZFlag (linearZ:Poly3):=
  flag_X 2 unitZFlag (by simp [InFlag,unitZFlag,Finsupp.single_apply])
theorem linearU_flag (a:Ω):BI unitYZFlag (linearU a):=
  flag_add (flag_X 0 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply]))
    (flag_scale a (flag_X 2 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply])))
theorem linearA_flag (b a:Ω):BI unitAllFlag (linearA b a):=
  flag_add (flag_add (flag_X 1 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))
    (flag_scale b (flag_X 0 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))))
    (flag_scale (b*a) (flag_X 2 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply])))

theorem EHY {G N R:Poly3} (p q:FlagDegree)
    (base: ∀C:AU Ω G N R,BP C.1)
    (hY: ∀C:AU Ω G N R,GR C 0)
    (hZ: ∀C:AU Ω G N R,GR C 2)
    (hderiv:MvPolynomial.pderiv (1:Fin 3) G ≠ 0)
    (hG:Irreducible G) (hproper: ¬G ∣ N)
    (hGflag:BI p G) (hNflag:BI q N):
    ∃(unit:EE base p q) (a b:Ω),
      (∀C:AU Ω G N R,FT Ω (AJ Ω C.1) (unit.zProjection C)=
        BR Ω C.1 linearZ)∧
      (∀C:AU Ω G N R,FT Ω (AJ Ω C.1) (unit.yzProjection C)=
        BR Ω C.1 (linearU a))∧
      (∀C:AU Ω G N R,FT Ω (AJ Ω C.1) (unit.NV C)=
        BR Ω C.1 (linearA b a)):=by
  obtain ⟨D⟩:=ALD base hY hZ hderiv
  let unit:=AUZ p q base hY hZ hderiv D hG hproper
    ((EI _ _).mpr hGflag) ((EI _ _).mpr hNflag)
  refine ⟨unit,D.lam,D.mu,?_,?_,?_⟩
  · intro C
    exact unit.zValue C
  · intro C
    have hv:FT Ω (AJ Ω C.1) (unit.yzProjection C)=affineU Ω C.1 D.lam:=by
      change FT Ω (AJ Ω C.1)
        (JV (affineU Ω C.1 D.lam) (D.uGate C))=_
      exact MT _ _
    rw [hv,HJ]
    simp only [linearU,affineU,map_add,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.smul_def]
  · intro C
    have hv:FT Ω (AJ Ω C.1) (unit.NV C)=
        affineV Ω C.1 D.mu (D.mu*D.lam):=by
      change (BO Ω (AJ Ω C.1)
        (affineV Ω C.1 D.mu (D.mu*D.lam)) (D.GN C))
        (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)=_
      exact KA Ω (AJ Ω C.1) _ _
    rw [hv,HJ]
    simp only [linearA,affineV,map_add,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.smul_def]

end
end ProximityPrize.SubmissionLower.BFL
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.BD
open scoped Classical BigOperators
open RCN002 RCN037 RCN039 RCN042 RCN046 RCN071 RCN076 RCN084 RCN095 RCN136 RCN207 RCN237 RCN264 RCN313 RCN340 RCN341 RCN344
open DX BX FR
open BFL AUK
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 60000
set_option maxRecDepth 50000
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq Ω:=Classical.decEq Ω
local notation "Poly3" =>MvPolynomial (Fin 3) Ω

structure Source (F:MvPolynomial (Fin 4) K) where
  P:Poly (K:=K)
  B:ℕ
  U:ℕ
  T:ℕ
  s:ℕ
  k:ℕ
  n0:ℕ
  hS: ∀e ∈ P.support,e 1≤s
  hshape: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧e 1+e 2+e 3+e 4≤T
  hBU:B≤U
  hUT:U≤T
  hdn:k+1≤n0
  hB:2*(n0-(k+1))≤B
  hn:n0≤(asS P).natDegree
  hdiv: ∀j≤k,F ∣ helper P F (s-j) j

def Source.d {F:MvPolynomial (Fin 4) K} (S:Source F):ℕ:=S.k+1
def Source.flag {F:MvPolynomial (Fin 4) K} (S:Source F):FlagDegree:=
  EJ.budgetFlag S.B S.U S.T S.d S.n0
def Source.leading {F:MvPolynomial (Fin 4) K} (S:Source F) (phi:Polynomial K→+*Ω):Poly3:=
  surfaceMap phi (asS S.P).leadingCoeff
def direction:Fin 3→FlagDegree:= ![unitZFlag,unitYZFlag,unitAllFlag]
def weight (W:FlagDegree):Fin 3→ℕ:= ![W.zOnly,W.yz,W.all]

theorem EXX
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (source:Fin 3→Source F) (D:ℕ) (hD: ∀j,(source j).d ∣ D)
    (carrier:Poly3) (p q W:FlagDegree)
    (hcarrier:Irreducible carrier) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:BI p carrier)
    (c:ℕ) [CharP Ω c] (hunit:2*(p.zOnly+p.yz+p.all)<c)
    (h2:(2:Ω) ≠ 0) (hfact: ∀j,((source j).k.factorial:Ω) ≠ 0)
    (Q A:Poly3) (target:Ω)
    (hQ:BI (2 • unitAllFlag) Q) (hA:BI unitYZFlag A)
    (hderiv:MvPolynomial.pderiv (1:Fin 3) carrier ≠ 0)
    (hproper: ¬carrier ∣ JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
    (hNflag:BI q (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target))
    (base: ∀C:AU Ω carrier
      (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j,(source j).leading phi),BP C.1)
    (hY: ∀C:AU Ω carrier
      (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j,(source j).leading phi),GR C 0)
    (hZ: ∀C:AU Ω carrier
      (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j,(source j).leading phi),GR C 2)
    (cut:Poly3) (hcut:BI W cut) (points:Finset (Fin 3→Ω))
    (hpoints: ∀x ∈ points,MvPolynomial.eval x carrier=0∧
      MvPolynomial.eval x (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)=0∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*∏ j,(source j).leading phi) ≠ 0∧
      MvPolynomial.aeval x cut=0)
    (hisolated: ∀x ∈ points,UK carrier
      (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) cut x):
    D*points.card≤ ∑ j:Fin 3,weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag:=by
  classical
  let H:=surfaceMap phi (polyH K F)
  let N:=JF H (surfaceMap phi (polyG K F)) Q A target
  let R:=H*∏ j,(source j).leading phi
  let Family:=AU Ω carrier N R
  obtain ⟨unit,a,b,hzv,hyv,hav⟩:=EHY p q base hY hZ hderiv hcarrier hproper hflag hNflag
  let ell:Fin 3→Poly3:= ![linearZ,linearU a,linearA b a]
  let projection:(j:Fin 3)→(C:Family)→Coordinate Ω (AJ Ω C.1):=
    ![unit.zProjection,unit.yzProjection,unit.NV]
  have hell (j:Fin 3):BI (direction j) (ell j):=by
    fin_cases j
    · exact linearZ_flag
    · exact linearU_flag a
    · exact linearA_flag b a
  have hvalue (j:Fin 3) (C:Family):
      FT Ω (AJ Ω C.1) (projection j C)=BR Ω C.1 (ell j):=by
    fin_cases j
    · exact hzv C
    · exact hyv C
    · exact hav C
  have hH (C:Family):H ∉ C.1:=by
    intro h
    exact _Q6 Ω carrier N R C
      (C.1.mul_mem_right (∏ j,(source j).leading phi) h)
  have hL (j:Fin 3) (C:Family):(source j).leading phi ∉ C.1:=by
    intro h
    have hd:(source j).leading phi ∣ R:=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun j=>(source j).leading phi) (Finset.mem_univ j)) H
    exact _Q6 Ω carrier N R C (C.1.mem_of_dvd hd h)
  let forget (j:Fin 3) (C:Family):AU Ω carrier N (H*(source j).leading phi):=
    ⟨C.1,(AJF Ω).mpr ⟨AAS Ω carrier N R C,by
      intro h
      exact ((inferInstance:C.1.IsPrime).mem_or_mem h).elim (hH C) (hL j C)⟩⟩
  have hinj (j:Fin 3):Function.Injective (forget j):=by
    intro C C' h
    have hh:=congrArg (fun C0:AU Ω carrier N (H*(source j).leading phi)=>C0.1) h
    exact Subtype.ext hh
  let Ext:=AlgebraicClosure (RatFunc Ω)
  letI:Algebra Ω Ext:=((algebraMap (RatFunc Ω) Ext).comp (algebraMap Ω (RatFunc Ω))).toAlgebra
  letI:SMul (RatFunc Ω) Ext:=(inferInstance:Algebra (RatFunc Ω) Ext).toSMul
  letI:SMul Ω Ext:=(inferInstance:Algebra Ω Ext).toSMul
  letI:IsScalarTower Ω (RatFunc Ω) Ext:=by
    constructor
    intro a b x
    simp only [Algebra.smul_def,map_mul]
    exact mul_assoc _ _ _
  letI:CharP Ext c:=by infer_instance
  have h2e:(2:Ext) ≠ 0:=by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hproj (j:Fin 3):
      (source j).d*(∑ C:Family,DQ Ω (AJ Ω C.1) (projection j C))≤
        flagMixed p (direction j) (source j).flag:=by
    have hfe:((source j).k.factorial:Ext) ≠ 0:=by
      simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne (hfact j)
    have hdirection:(direction j).zOnly+(direction j).yz+(direction j).all=1:=by fin_cases j<;>rfl
    exact BIQ (E:=Ext) phi F carrier p (direction j) hcarrier.ne_zero hcarrierF hflag
      (ell j) (hell j) c (by omega) (by rw [hdirection,mul_one];exact hunit)
      (source j).P (source j).B (source j).U (source j).T (source j).s (source j).k (source j).n0
      (source j).hS (source j).hshape (source j).hBU (source j).hUT (source j).hdn (source j).hB
      (source j).hn (source j).hdiv h2e hfe Q A target hQ hA (forget j) (hinj j) (projection j) (hvalue j)
  have hscaled (j:Fin 3):
      D*(∑ C:Family,DQ Ω (AJ Ω C.1) (projection j C))≤
        (D/(source j).d)*flagMixed p (direction j) (source j).flag:=by
    have h:=Nat.mul_le_mul_left (D/(source j).d) (hproj j)
    simpa only [← Nat.mul_assoc,Nat.div_mul_cancel (hD j)] using h
  let budget:=unit.toFE
  have hcard:points.card≤ ∑ C:Family,budget.weightedCost W C:=by
    apply (WX Ω carrier N R points id
      (fun x hx=>(hpoints x hx).1) (fun x hx=>(hpoints x hx).2.1)
      (fun x hx=>(hpoints x hx).2.2.1)).trans
    apply Finset.sum_le_sum
    intro C _
    by_cases he:(HF Ω carrier N R points id C).Nonempty
    · obtain ⟨x,hx⟩:=he
      have hxS:=LU Ω carrier N R points id C hx
      have hxC:=MC Ω carrier N R points id C x hx
      apply (budget.primeBudget C).zero_le W cut hcut
        (hisolated x hxS C.1 inferInstance (PU Ω carrier N R C)
          hxC (EN Ω carrier N R C) (GV Ω carrier N R C))
      · intro y hy
        exact MC Ω carrier N R points id C y hy
      · intro y hy
        exact (hpoints y (LU Ω carrier N R points id C hy)).2.2.2
    · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]
  have hs:=Finset.sum_le_sum (fun j (_:j ∈ (Finset.univ:Finset (Fin 3)))=>
    Nat.mul_le_mul_left (weight W j) (hscaled j))
  have hb:D*(∑ C:Family,budget.weightedCost W C)≤
      ∑ j:Fin 3,weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag:=by
    have hl:D*(∑ C:Family,budget.weightedCost W C)=
        ∑ j:Fin 3,weight W j*(D*∑ C:Family,DQ Ω (AJ Ω C.1) (projection j C)):=by
      simp only [Fin.sum_univ_three,projection,weight,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
        budget,FE.weightedCost,EE.toFE,
        QZ.toFE,EE.toQZ,
        Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    have hr:(∑ j:Fin 3,weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag)=
        ∑ j:Fin 3,weight W j*((D/(source j).d)*flagMixed p (direction j) (source j).flag):=by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hl,hr]
    exact hs
  exact (Nat.mul_le_mul_left D hcard).trans hb

theorem DMO
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (source:Fin 3→Source F) (D:ℕ) (hD: ∀j,(source j).d ∣ D)
    (carrier:Poly3) (p q W:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:BI p carrier)
    (c:ℕ) [CharP Ω c] (hunit:2*(p.zOnly+p.yz+p.all)<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c)
    (h2:(2:Ω) ≠ 0) (hfact: ∀j,((source j).k.factorial:Ω) ≠ 0)
    (Q A:Poly3) (target:Ω)
    (hQ:BI (2 • unitAllFlag) Q) (hA:BI unitYZFlag A)
    (hNflag:BI q (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target))
    (cut:Poly3) (hcut:BI W cut) (points:Finset (Fin 3→Ω))
    (hpoints: ∀x ∈ points,MvPolynomial.eval x carrier=0∧
      MvPolynomial.eval x (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)=0∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*∏ j,(source j).leading phi) ≠ 0∧
      MvPolynomial.aeval x cut=0)
    (hisolated: ∀x ∈ points,UK carrier
      (JF (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) cut x):
    D*points.card≤ ∑ j:Fin 3,weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag:=by
  classical
  let H:=surfaceMap phi (polyH K F)
  let N:=JF H (surfaceMap phi (polyG K F)) Q A target
  let R:=H*∏ j,(source j).leading phi
  have hdeg:p.zOnly+p.yz+p.all<c:=by omega
  have hderiv:H ∈ Ideal.span ({carrier,MvPolynomial.pderiv (1:Fin 3) carrier}:Set Poly3):=by
    let I:=Ideal.span ({carrier,MvPolynomial.pderiv (1:Fin 3) carrier}:Set Poly3)
    have hc:carrier ∈ I:=Ideal.subset_span (by simp)
    have hd:MvPolynomial.pderiv (1:Fin 3) carrier ∈ I:=Ideal.subset_span (by simp)
    obtain ⟨b,hb⟩:=hcarrierF
    change surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F) ∈ I
    rw [← RCN267.ZO,hb,MvPolynomial.pderiv_mul]
    exact I.add_mem (I.mul_mem_right b hd) (I.mul_mem_right (MvPolynomial.pderiv (1:Fin 3) b) hc)
  have hcover: ∀x ∈ points,∃g: ↥(HR carrier N),MvPolynomial.eval x g.1=0:=by
    intro x hx
    have hp:=hpoints x hx
    have hh:MvPolynomial.eval x H ≠ 0:=by
      have hr:MvPolynomial.eval x H*MvPolynomial.eval x (∏ j,(source j).leading phi) ≠ 0:=by
        simpa only [map_mul] using hp.2.2.1
      exact (mul_ne_zero_iff.mp hr).1
    exact AAU carrier N cut R hcarrier x hp.1 hp.2.2.2 hp.2.2.1
      (AUO (MvPolynomial.eval x) carrier H hderiv hp.1 hh) (hisolated x hx)
  obtain ⟨base,hY,hZ⟩:=AOE carrier N R hcarrier p q hflag hNflag c hdeg hmix
  let S (g: ↥(HR carrier N)):Finset (Fin 3→Ω):=
    points.filter (fun x=>MvPolynomial.eval x g.1=(0:Ω))
  have hcoverage:points ⊆ Finset.univ.biUnion S:=by
    intro x hx
    obtain ⟨g,hg⟩:=hcover x hx
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hg⟩⟩
  have hcount (g: ↥(HR carrier N)):
      D*(S g).card≤ ∑ j:Fin 3,weight W j*(D/(source j).d)*flagMixed (exactFlag g.1) (direction j) (source j).flag:=by
    have hg:=OJ carrier N g
    have hgtotal:(exactFlag g.1).zOnly+(exactFlag g.1).yz+(exactFlag g.1).all≤
        p.zOnly+p.yz+p.all:=by
      rw [(AHN g.1).2.2]
      exact (AOB AAR g.1 carrier hg.2.1 hcarrier).trans
        (_Q21 carrier p hflag).2.2
    apply EXX phi F source D hD g.1 (exactFlag g.1) q W hg.1
      (dvd_trans hg.2.1 hcarrierF) (ATU g.1) c (by omega) h2 hfact
      Q A target hQ hA hg.2.2.2 hg.2.2.1 hNflag (base g) (hY g) (hZ g) cut hcut (S g)
    · intro x hx
      have hs:=Finset.mem_filter.mp hx
      have hp:=hpoints x hs.1
      exact ⟨hs.2,hp.2.1,hp.2.2.1,hp.2.2.2⟩
    · intro x hx J hj hnot hpoint hG hN
      exact hisolated x (Finset.mem_filter.mp hx).1 J hj hnot hpoint (J.mem_of_dvd hg.2.1 hG) hN
  calc
    D*points.card≤D*∑ g: ↥(HR carrier N),(S g).card:=
      Nat.mul_le_mul_left _ ((Finset.card_le_card hcoverage).trans Finset.card_biUnion_le)
    _= ∑ g: ↥(HR carrier N),D*(S g).card:=Finset.mul_sum _ _ _
    _≤ ∑ g: ↥(HR carrier N),∑ j:Fin 3,
        weight W j*(D/(source j).d)*flagMixed (exactFlag g.1) (direction j) (source j).flag:=
      Finset.sum_le_sum (fun g _=>hcount g)
    _= ∑ j:Fin 3,weight W j*(D/(source j).d)*
        ∑ g: ↥(HR carrier N),flagMixed (exactFlag g.1) (direction j) (source j).flag:=by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _≤_:=Finset.sum_le_sum (fun j _=>Nat.mul_le_mul_left _
      (ASF carrier N hcarrier p (direction j) (source j).flag hflag))

end
end ProximityPrize.SubmissionLower.BD
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.DDE
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN046 RCN072 RCN084 RCN095 RCN134 RCN136 RCN202
open RCN199 RCN200 RCN207 RCN208 RCN209 RCN237 RCN264 RCN313 RCN341 RCN344
open BX BD
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 50000
variable {K Ω E:Type} [Field K] [Field Ω] [Field E] [IsAlgClosed Ω] [IsAlgClosed E]
  [Algebra Ω E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E]
local instance:DecidableEq Ω:=Classical.decEq Ω
local instance:DecidableEq E:=Classical.decEq E

omit [IsAlgClosed Ω] [IsAlgClosed E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E] in
private theorem VL (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K):
    CD Ω E (surfaceMap phi F)=surfaceMap ((algebraMap Ω E).comp phi) F:=by
  simp only [CD,surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]

omit [IsAlgClosed Ω] [IsAlgClosed E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E] in
private theorem GSB (C:Ideal (MvPolynomial (Fin 3) Ω)) [C.IsPrime]
    (f:AJ Ω C→ₐ[Ω] E) (F:MvPolynomial (Fin 3) Ω):
    MvPolynomial.eval (GM C f) (CD Ω E F)=f (BR Ω C F):=by
  have h:=AlgHom.congr_fun (ALG C f) F
  change MvPolynomial.eval (GM C f) (MvPolynomial.map (algebraMap Ω E) F)=_
  rw [MvPolynomial.eval_map]
  exact h

theorem DKQ {ι:Type} [Fintype ι]
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (source:Fin 3→Source F) (D:ℕ) (hD: ∀j,(source j).d ∣ D)
    (carrier:MvPolynomial (Fin 3) Ω) (p:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:BI p carrier)
    (a b s n:ℕ) (center:FlagDegree)
    (coeff:Fin (n+1)→MvPolynomial (Fin 3) Ω) (coeffFlag:Fin (n+1)→FlagDegree)
    (hHflag:BI (⟨a,b+1,s+1⟩:FlagDegree) (surfaceMap phi (polyH K F)))
    (hGflag:BI (⟨a,b,s+3⟩:FlagDegree) (surfaceMap phi (polyG K F)))
    (hcoeff: ∀j,BI (coeffFlag j) (coeff j))
    (hcoeffEq: ∀j,coeffFlag j+(n-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
      j.val • (⟨a,b,s+3⟩:FlagDegree)=center+n • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
    (c:ℕ) [CharP E c] (hunit:2*(p.zOnly+p.yz+p.all)<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3))<c)
    (h2:(2:E) ≠ 0) (hfact: ∀j,((source j).k.factorial:E) ≠ 0)
    (Q A:MvPolynomial (Fin 3) Ω)
    (hQ:BI (2 • unitAllFlag) Q) (hA:BI unitYZFlag A)
    (old:ι→AU Ω carrier
      (filteredCut n coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
      (surfaceMap phi (polyH K F)))
    (hold:Function.Injective old)
    (hleading: ∀i j,(source j).leading phi ∉ (old i).1)
    (hAnonzero: ∀i,A ∉ (old i).1)
    (projection: ∀i,DB Ω (AJ Ω (old i).1))
    (hvalue: ∀i,DB.value Ω (AJ Ω (old i).1) (projection i)=
      movingValue (old i).1 (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A):
    D*(∑ i,DB.degree Ω (AJ Ω (old i).1) (projection i))≤
      ∑ j:Fin 3,weight (center+n • (⟨a,b+1,s+2⟩:FlagDegree)) j*(D/(source j).d)*
        flagMixed p (direction j) (source j).flag:=by
  classical
  let H:=surfaceMap phi (polyH K F)
  let G:=surfaceMap phi (polyG K F)
  let mu:=CD Ω E
  let phiE:=(algebraMap Ω E).comp phi
  let prime:=fun i=>(old i).1
  letI: ∀i,Algebra (RatFunc Ω) (AJ Ω (prime i)):=
    fun i=>(projection i).embedding.toRingHom.toAlgebra
  letI: ∀i,IsScalarTower Ω (RatFunc Ω) (AJ Ω (prime i)):=
    fun i=>IsScalarTower.of_algebraMap_eq (fun a=>((projection i).embedding.commutes a).symm)
  letI: ∀i,FiniteDimensional (RatFunc Ω) (AJ Ω (prime i)):=fun i=>(projection i).finite
  letI: ∀i,Algebra.IsSeparable (RatFunc Ω) (AJ Ω (prime i)):=fun i=>(projection i).separable
  let points:=BAN (B:=RatFunc Ω) (L:=E) prime
  let target:=algebraMap (RatFunc Ω) E (PF Ω)
  let N:=DUO (E:=E) H G Q A
  let cut:=fiberCut (E:=E) n coeff Q A
  let W:=center+n • (⟨a,b+1,s+2⟩:FlagDegree)
  have hi:Function.Injective prime:=by
    intro i j h
    exact hold (Subtype.ext h)
  have certificate (i:ι) (f:AJ Ω (prime i)→ₐ[RatFunc Ω] E):
      let x:=GM (prime i) (f.restrictScalars Ω)
      MvPolynomial.eval x (mu carrier)=0∧MvPolynomial.eval x N=0∧
      MvPolynomial.aeval x cut=0∧MvPolynomial.eval x (mu H*mu A) ≠ 0∧
      UK (mu carrier) N cut x:=by
    letI:Algebra (RatFunc Ω) (AJ Ω (old i).1):=
      (projection i).embedding.toRingHom.toAlgebra
    have hj:algebraMap (RatFunc Ω) (AJ Ω (old i).1) (PF Ω)=
        movingValue (old i).1 H G Q A:=hvalue i
    exact RCN202.VX carrier H G Q A n coeff (old i) hj (hAnonzero i) f
  have hpoints: ∀x ∈ points,
      MvPolynomial.eval x (mu carrier)=0∧MvPolynomial.eval x N=0∧
      MvPolynomial.eval x (surfaceMap phiE (polyH K F)*∏ j,(source j).leading phiE) ≠ 0∧
      MvPolynomial.aeval x cut=0:=by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩:=Finset.mem_image.mp hx
    have hc:=certificate i f
    have hHne:MvPolynomial.eval (GM (prime i) (f.restrictScalars Ω)) (mu H) ≠ 0:=by
      have hh:=hc.2.2.2.1
      rw [map_mul] at hh
      exact (mul_ne_zero_iff.mp hh).1
    have hLne (j:Fin 3):MvPolynomial.eval (GM (prime i) (f.restrictScalars Ω))
        ((source j).leading phiE) ≠ 0:=by
      have he:(source j).leading phiE=mu ((source j).leading phi):=by
        exact (VL phi (asS (source j).P).leadingCoeff).symm
      rw [he,GSB]
      intro hz
      exact hleading i j ((CT.AAE (prime i) _).mp
        ((map_eq_zero_iff f f.injective).mp hz))
    have hprod:(∏ j:Fin 3,MvPolynomial.eval (GM (prime i) (f.restrictScalars Ω))
        ((source j).leading phiE)) ≠ 0:=Finset.prod_ne_zero_iff.mpr (fun j _=>hLne j)
    have hgate:MvPolynomial.eval (GM (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (polyH K F)*∏ j,(source j).leading phiE) ≠ 0:=by
      rw [map_mul,map_prod]
      apply mul_ne_zero _ hprod
      simpa only [H,mu,VL,phiE] using hHne
    exact ⟨hc.1,hc.2.1,hgate,hc.2.2.1⟩
  have hiso: ∀x ∈ points,UK (mu carrier) N cut x:=by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩:=Finset.mem_image.mp hx
    exact (certificate i f).2.2.2.2
  obtain ⟨hNflag,hcutflag⟩:=RCN202.DSK (E:=E) a b s n center H G Q A coeff coeffFlag
    hHflag hGflag hQ hA hcoeff hcoeffEq
  have hN:N=JF (surfaceMap phiE (polyH K F)) (surfaceMap phiE (polyG K F))
      (mu Q) (mu A) target:=by
    dsimp only [N,DUO]
    rw [show CD Ω E H=surfaceMap phiE (polyH K F) from VL phi _,
      show CD Ω E G=surfaceMap phiE (polyG K F) from VL phi _]
  have hcar:mu carrier ∣ surfaceMap phiE F:=by
    simpa only [mu,VL,phiE] using map_dvd mu hcarrierF
  have hmu:Function.Injective mu:=MvPolynomial.map_injective (algebraMap Ω E) (algebraMap Ω E).injective
  have hne:mu carrier ≠ 0:=fun hz=>hcarrier (hmu (by simpa only [map_zero] using hz))
  have hNflag' :BI (⟨a,b+1,s+3⟩:FlagDegree)
      (JF (surfaceMap phiE (polyH K F)) (surfaceMap phiE (polyG K F)) (mu Q) (mu A) target):=by
    change BI (⟨a,b+1,s+3⟩:FlagDegree) N at hNflag
    rwa [hN] at hNflag
  rw [hN] at hpoints hiso
  have hc:=DMO phiE F source D hD (mu carrier) p (⟨a,b+1,s+3⟩:FlagDegree) W
    hne hcar (inFlag_map _ hflag) c hunit hmix h2 hfact (mu Q) (mu A) target
    (inFlag_map _ hQ) (inFlag_map _ hA) hNflag' cut hcutflag points hpoints hiso
  have hcard:=BAW (B:=RatFunc Ω) (L:=E) prime hi
  simpa only [points,hcard,DB.degree,prime,W] using hc

theorem DLF {ι:Type} [Fintype ι]
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (source:Fin 3→Source F) (D:ℕ) (hD: ∀j,(source j).d ∣ D)
    (carrier:MvPolynomial (Fin 3) Ω) (p:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:BI p carrier)
    (a b s w:ℕ) (hw:1≤w)
    (hR:F.degreeOf 2≤s+2)
    (hYR:RCN234.wt ![0,1,1,0] F≤b+s+3)
    (hAll:RCN234.wt ![0,1,1,1] F≤a+b+s+3)
    (c:ℕ) [CharP E c] (hunit:2*(p.zOnly+p.yz+p.all)<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3))<c)
    (h2:(2:E) ≠ 0) (hfact: ∀j,((source j).k.factorial:E) ≠ 0)
    (Q A:MvPolynomial (Fin 3) Ω)
    (hQ:BI (2 • unitAllFlag) Q) (hA:BI unitYZFlag A)
    (old:ι→AU Ω carrier (RCN086._Q2 phi F (w+1)) (surfaceMap phi (polyH K F)))
    (hold:Function.Injective old)
    (hleading: ∀i j,(source j).leading phi ∉ (old i).1)
    (hAnonzero: ∀i,A ∉ (old i).1)
    (projection: ∀i,DB Ω (AJ Ω (old i).1))
    (hvalue: ∀i,DB.value Ω (AJ Ω (old i).1) (projection i)=
      movingValue (old i).1 (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A):
    D*(∑ i,DB.degree Ω (AJ Ω (old i).1) (projection i))≤
      ∑ j:Fin 3,weight (RCN198.center a b s+w • (⟨a,b+1,s+2⟩:FlagDegree)) j*(D/(source j).d)*
        flagMixed p (direction j) (source j).flag:=by
  classical
  obtain ⟨coeff,flags,heq,hcoeff,hrel⟩:=RCN086.BDL phi a b s F hR hYR hAll
    (w+1) (by omega) (RCN086.tailSelector (w+1)) 0 0 0
  have heq' :RCN086._Q2 phi F (w+1)=
      filteredCut w coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)):=heq
  let old' :ι→AU Ω carrier
      (filteredCut w coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
      (surfaceMap phi (polyH K F)):=fun i=>⟨(old i).1,by rw [← heq'];exact (old i).2⟩
  have hi:Function.Injective old' :=by
    intro i j h
    have hh:=congrArg (fun C:AU Ω carrier
      (filteredCut w coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
      (surfaceMap phi (polyH K F))=>C.1) h
    exact hold (Subtype.ext hh)
  obtain ⟨hHflag,hGflag⟩:=RCN201.DGW phi a b s F hR hYR hAll
  exact DKQ (E:=E) phi F source D hD carrier p hcarrier hcarrierF hflag
    a b s w (RCN198.center a b s) coeff flags hHflag hGflag hcoeff hrel c hunit hmix h2 hfact
    Q A hQ hA old' hi hleading hAnonzero projection hvalue

theorem EOV
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (source:Fin 3→Source F) (D:ℕ) (hDpos:0<D) (hD: ∀j,(source j).d ∣ D)
    (carrier:MvPolynomial (Fin 3) Ω) (p tailFlag:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:BI p carrier)
    (a b s w:ℕ) (hw:1≤w)
    (hR:F.degreeOf 2≤s+2)
    (hYR:RCN234.wt ![0,1,1,0] F≤b+s+3)
    (hAll:RCN234.wt ![0,1,1,1] F≤a+b+s+3)
    (c:ℕ) [CharP E c] (hunit:2*(p.zOnly+p.yz+p.all)<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3))<c)
    (h2:(2:E) ≠ 0) (hfact: ∀j,((source j).k.factorial:E) ≠ 0)
    (base: ∀C:AU Ω carrier (RCN086._Q2 phi F (w+1))
      (surfaceMap phi (polyH K F)),BP C.1)
    (unit:EE base p tailFlag)
    (active:Finset (AU Ω carrier (RCN086._Q2 phi F (w+1)) (surfaceMap phi (polyH K F))))
    (hleading: ∀C ∈ active,∀j,(source j).leading phi ∉ C.1):
    ∃budget: ∀C:AU Ω carrier (RCN086._Q2 phi F (w+1)) (surfaceMap phi (polyH K F)),
        RD C.1 (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)),
      (∀C:AU Ω carrier (RCN086._Q2 phi F (w+1)) (surfaceMap phi (polyH K F)),
        (budget C).zCost=unit.toFE.zCost C∧
        (budget C).yzCost=unit.toFE.yzCost C∧
        (budget C).allCost=unit.toFE.allCost C)∧
      (∑ C ∈ active,(budget C).movingCost)≤
        (∑ j:Fin 3,weight (RCN198.center a b s+w • (⟨a,b+1,s+2⟩:FlagDegree)) j*(D/(source j).d)*
          flagMixed p (direction j) (source j).flag)/D:=by
  classical
  let H:=surfaceMap phi (polyH K F)
  let G:=surfaceMap phi (polyG K F)
  let T:=RCN086._Q2 phi F (w+1)
  obtain ⟨Q,A,J,hQ,hA,hJ⟩:=BCF carrier T H G base
  let budget:=EFZ carrier T H G unit J (fun C v=>(hJ C).2.2.1 v)
  refine ⟨budget,(fun _=>⟨rfl,rfl,rfl⟩),?_⟩
  have hb:=DLF (E:=E) phi F source D hD carrier p hcarrier hcarrierF hflag
    a b s w hw hR hYR hAll c hunit hmix h2 hfact Q A hQ hA
    (fun C:active=>C.val) Subtype.val_injective
    (fun C j=>hleading C.val C.property j)
    (fun C=>(hJ C.val).1) (fun C=>J C.val) (fun C=>(hJ C.val).2.1)
  have hsum:(∑ C ∈ active,(budget C).movingCost)=
      ∑ C:active,DB.degree Ω (AJ Ω C.val.1) (J C.val):=by
    exact (Finset.sum_coe_sort active (fun C=>(budget C).movingCost)).symm
  apply (Nat.le_div_iff_mul_le hDpos).mpr
  rw [hsum]
  simpa only [Nat.mul_comm] using hb

end
end ProximityPrize.SubmissionLower.DDE
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.PI
open RCN260 GB
set_option autoImplicit false
set_option maxHeartbeats 1000000

def pair (capT capY capR r y t:ℕ):DG:=
  ⟨262144,131071,181235,y,r,t,capY,capR,capT⟩

def numerator (capT capY capR r y t:ℤ):ℤ:=
  4*131073*131071*(capT*r*y+capR*t*y+capY*t*r)+
  131073*(capR-131071*capY)*t+
  (131073*(capR-131071*capT)+80910*50164*capR)*y+
  (131073*(capT+capY)+80910*50164*capY)*r

theorem numerator_eq (capT capY capR r y t:ℕ) (hr:1≤r):
    (KP (pair capT capY capR r y t):ℤ)=
      numerator capT capY capR r y t:=by
  have hsub:((2*r-1:ℕ):ℤ)=2*(r:ℤ)-1:=by
    rw [Nat.cast_sub (by omega:1≤2*r)]
    push_cast
    ring
  simp only [KP,pair,DG.errors,DG.gap,
    DG.KO,DG.mixedCost,RCN294.dot]
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [hsub]
  norm_num [numerator]
  ring

private theorem box_product (x y capX capY:ℤ)
    (hx:0≤x) (hy:0≤y) (hX:x≤capX) (hY:y≤capY):
    2*x*y≤capX*y+capY*x:=by
  nlinarith [mul_nonneg (sub_nonneg.mpr hX) hy,mul_nonneg (sub_nonneg.mpr hY) hx]

theorem GII (r y t:ℤ)
    (hr:0≤r) (hy:0≤y) (ht:0≤t)
    (hR:r≤40) (hY:y≤181) (hT:t≤11784):
    numerator 531000 11062 2470 r y t≤
      50164*(452397292056*t+44271288457346*y+155118092834147*r):=by
  have hry:=box_product r y 40 181 hr hy hR hY
  have hrt:=box_product r t 40 11784 hr ht hR hT
  have hty:4*t*y≤181*t+3*11784*y:=by
    nlinarith [mul_nonneg (sub_nonneg.mpr hY) ht,mul_nonneg (sub_nonneg.mpr hT) hy]
  dsimp [numerator]
  nlinarith

theorem GQA (r y t:ℤ)
    (hr:0≤r) (hy:0≤y) (ht:0≤t)
    (hY:y≤181) (hT:t≤11784):
    numerator 88902 1382 308 r y t≤
      50164*(4941578463932*y+44352901270546*r):=by
  have hry:r*y≤181*r:=by nlinarith [mul_nonneg (sub_nonneg.mpr hY) hr]
  have hty:t*y≤11784*y:=by nlinarith [mul_nonneg (sub_nonneg.mpr hT) hy]
  have htr:t*r≤11784*r:=by nlinarith [mul_nonneg (sub_nonneg.mpr hT) hr]
  dsimp [numerator]
  nlinarith

set_option maxRecDepth 1000000 in
theorem FUG (r y t:ℕ) (hr:1≤r)
    (hR:r≤40) (hY:y≤181) (hT:t≤11784):
    FU (pair 531000 11062 2470 r y t)≤
      452397292056*t+44271288457346*y+155118092834147*r:=by
  have hz:=GII (r:ℤ) y t (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hR) (by exact_mod_cast hY) (by exact_mod_cast hT)
  have he:=numerator_eq 531000 11062 2470 r y t hr
  norm_num only [Nat.cast_ofNat] at he
  rw [← he] at hz
  have hn:KP (pair 531000 11062 2470 r y t)≤
      50164*(452397292056*t+44271288457346*y+155118092834147*r):=by exact_mod_cast hz
  have hd:=Nat.div_le_div_right (c:=50164) hn
  simpa [FU,pair,DG.gap] using hd

set_option maxRecDepth 1000000 in
theorem EZQ (r y t:ℕ) (hr:1≤r)
    (hY:y≤181) (hT:t≤11784):
    FU (pair 88902 1382 308 r y t)≤
      4941578463932*y+44352901270546*r:=by
  have hz:=GQA (r:ℤ) y t (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hY) (by exact_mod_cast hT)
  have he:=numerator_eq 88902 1382 308 r y t hr
  norm_num only [Nat.cast_ofNat] at he
  rw [← he] at hz
  have hn:KP (pair 88902 1382 308 r y t)≤
      50164*(4941578463932*y+44352901270546*r):=by exact_mod_cast hz
  have hd:=Nat.div_le_div_right (c:=50164) hn
  simpa [FU,pair,DG.gap] using hd

theorem GEK (loT loY loR hiT hiY hiR r y t:ℕ)
    (hT:loT≤hiT) (hY:loY≤hiY) (hR:loR≤hiR):
    FU (pair loT loY loR r y t)≤
      FU (pair hiT hiY hiR r y t):=by
  unfold FU
  apply Nat.div_le_div_right
  simp only [KP,pair,DG.errors,DG.gap,
    DG.KO,DG.mixedCost,RCN294.dot]
  gcongr

end ProximityPrize.SubmissionLower.PI
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.MZ
open RCN260 GB PI
set_option autoImplicit false
set_option maxHeartbeats 1400000

def EIX (L U S Rcap Ycap Tcap qt qy qr:ℕ):Prop:=
  2*131073*131071*((S:ℤ)*Ycap+(U:ℤ)*Rcap)+131073*((S:ℤ)-131071*U)≤50164*(qt:ℤ)∧
  2*131073*131071*((L:ℤ)*Rcap+(S:ℤ)*Tcap)+131073*((S:ℤ)-131071*L)+80910*50164*S≤50164*(qy:ℤ)∧
  2*131073*131071*((L:ℤ)*Ycap+(U:ℤ)*Tcap)+131073*((L:ℤ)+U)+80910*50164*U≤50164*(qr:ℤ)
instance (L U S Rcap Ycap Tcap qt qy qr:ℕ):Decidable (EIX L U S Rcap Ycap Tcap qt qy qr):=by
  unfold EIX;infer_instance

theorem box_product (x y capX capY:ℤ) (hx:0≤x) (hy:0≤y) (hX:x≤capX) (hY:y≤capY):
    2*x*y≤capX*y+capY*x:=by
  nlinarith [mul_nonneg (sub_nonneg.mpr hX) hy,mul_nonneg (sub_nonneg.mpr hY) hx]

set_option maxRecDepth 1000000 in
theorem count_le (L U S Rcap Ycap Tcap qt qy qr r y t:ℕ)
    (hf:EIX L U S Rcap Ycap Tcap qt qy qr)
    (hr:1≤r) (hR:r≤Rcap) (hY:y≤Ycap) (hT:t≤Tcap):
    FU (pair L U S r y t)≤qt*t+qy*y+qr*r:=by
  have hry:=box_product r y Rcap Ycap (by positivity) (by positivity)
    (by exact_mod_cast hR) (by exact_mod_cast hY)
  have hrt:=box_product r t Rcap Tcap (by positivity) (by positivity)
    (by exact_mod_cast hR) (by exact_mod_cast hT)
  have hty:=box_product t y Tcap Ycap (by positivity) (by positivity)
    (by exact_mod_cast hT) (by exact_mod_cast hY)
  have h1:=mul_le_mul_of_nonneg_left hry (show (0:ℤ)≤2*131073*131071*L by positivity)
  have h2:=mul_le_mul_of_nonneg_left hrt (show (0:ℤ)≤2*131073*131071*U by positivity)
  have h3:=mul_le_mul_of_nonneg_left hty (show (0:ℤ)≤2*131073*131071*S by positivity)
  have h4:=mul_le_mul_of_nonneg_right hf.1 (show (0:ℤ)≤t by positivity)
  have h5:=mul_le_mul_of_nonneg_right hf.2.1 (show (0:ℤ)≤y by positivity)
  have h6:=mul_le_mul_of_nonneg_right hf.2.2 (show (0:ℤ)≤r by positivity)
  have hz:numerator L U S r y t≤50164*((qt:ℤ)*t+(qy:ℤ)*y+(qr:ℤ)*r):=by
    unfold numerator
    nlinarith only [h1,h2,h3,h4,h5,h6]
  rw [←numerator_eq L U S r y t hr] at hz
  have hn:KP (pair L U S r y t)≤50164*(qt*t+qy*y+qr*r):=by exact_mod_cast hz
  have hd:=Nat.div_le_div_right (c:=50164) hn
  simpa [FU,pair,DG.gap] using hd

end ProximityPrize.SubmissionLower.MZ
end MergedPart9
section MergedPart10

namespace ProximityPrize.SubmissionLower.Lower80899.SourceSound

open RCN095 RCN223 RCN260 RCN294 DY
open Lower80899.FactorSwitch Lower80899.PowerRoute
open Lower80899.Oracle
open FV (Potential)

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem COH
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ:ℕ)
    (hL:L₁≤L₂) (hY:Y₁≤Y₂) (hS:S₁≤S₂):
    GB.FU (helperPair L₁ Y₁ S₁ leftY leftR leftZ)≤
      GB.FU (helperPair L₂ Y₂ S₂ leftY leftR leftZ):=by
  let P₁:=helperPair L₁ Y₁ S₁ leftY leftR leftZ
  let P₂:=helperPair L₂ Y₂ S₂ leftY leftR leftZ
  have ha:vectorLE P₁.KO P₂.KO:=by
    exact ⟨le_rfl,le_rfl,le_rfl⟩
  have hm:vectorLE P₁.mixedCost P₂.mixedCost:=by
    refine ⟨?_,?_,?_⟩
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
        (Nat.mul_le_mul_left leftZ hS)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
        (Nat.mul_le_mul_left leftZ hY)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
        (Nat.mul_le_mul_left leftR hY)
  have hdot:dot P₁.KO P₁.mixedCost≤
      dot P₂.KO P₂.mixedCost:=by
    unfold dot
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul ha.1 hm.1)
        (Nat.mul_le_mul ha.2.1 hm.2.1))
      (Nat.mul_le_mul ha.2.2 hm.2.2)
  have hnum:GB.KP P₁≤GB.KP P₂:=by
    unfold GB.KP
    exact Nat.add_le_add (Nat.mul_le_mul_left (P₁.n-P₁.w) hdot)
      (Nat.mul_le_mul_left ((P₁.errors+1)*P₁.gap) hm.2.2)
  exact Nat.div_le_div_right hnum

theorem ZB (L YS S:ℕ) (p:FlagDegree) (j:ℕ):
    stageCost L YS S (LP p) j≤
      stageCost L YS S (LP p) 0:=by
  apply COH
  · simpa only [LP,Nat.zero_mul,Nat.sub_zero] using
      Nat.sub_le L (j*total p)
  · simpa only [LP,Nat.zero_mul,Nat.sub_zero] using
      Nat.sub_le YS (j*middle p)
  · simpa only [LP,Nat.zero_mul,Nat.sub_zero] using
      Nat.sub_le S (j*p.all)

theorem DZC
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ:ℕ)
    (hL:L₁≤L₂) (hY:Y₁≤Y₂) (hS:S₁≤S₂)
    (hgate:LX L₂ Y₂ S₂ leftY leftR leftZ):
    LX L₁ Y₁ S₁ leftY leftR leftZ:=by
  rcases hgate with ⟨hr,hy,hs,hz,hmy,hmr,hmz⟩
  refine ⟨hr,hy,hs,hz,?_,?_,?_⟩
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
      (Nat.mul_le_mul_left leftZ hS)).trans_lt hmy
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
      (Nat.mul_le_mul_left leftZ hY)).trans_lt hmr
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
      (Nat.mul_le_mul_left leftR hY)).trans_lt hmz

theorem VW (L YS S:ℕ) (p:FlagDegree) (j:ℕ)
    (hgate:LX L YS S (middle p) p.all (total p)):
    LX (L-j*total p) (YS-j*middle p)
      (S-j*p.all) (middle p) p.all (total p):=by
  apply DZC
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact hgate

namespace Phase00
def source:EA:=⟨3840000,88497,19840,89971263865895136686497⟩
def potential:Potential:=⟨4854002496338,264031687204593,1193000963911735⟩
theorem stageZero_le (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    stageCost 3840000 88497 19840 (LP p) 0≤potential.eval p:=by
  have h:=MZ.count_le 3840000 88497 19840 40 181 11784 4854002496338 264031687204593 1193000963911735
    p.all (middle p) (total p) (by decide+kernel) hr hs hy ht
  simpa only [stageCost,stagePair,LP,helperPair,PI.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem ABV (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    LX 3840000 88497 19840 (middle p) p.all (total p):=by
  unfold LX helperPair DG.mixedCost
  norm_num
  omega
def sound:YF where
  source:=source
  potential:=potential
  stageCost_le:=by
    intro p j hr hs hy ht _hj
    exact (ZB _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates:=by
    intro p j hr hs hy ht _hj
    exact VW _ _ _ p j (ABV p hr hs hy ht)
noncomputable def kernel (u0 u1:ProximityPrize.Benchmark.IRSProfile.Index→ProximityPrize.Benchmark.IRSProfile.Field):
    Lower80899.BatchPhase.WZ sound u0 u1 where
  D:=11598846163
  m:=63999
  weighted:=by decide
  shape:=JR.Source00.shape
  slope_le_m:=by decide
  m_lt_char:=by decide
  gap_le_finrank:=JR.Source00.finrank_gap u0 u1
end Phase00
namespace Phase01
def source:EA:=⟨3200000,44249,9888,11656201717632596787256⟩
def potential:Potential:=⟨2423047556199,166388533118268,756070039150762⟩
theorem stageZero_le (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    stageCost 3200000 44249 9888 (LP p) 0≤potential.eval p:=by
  have h:=MZ.count_le 3200000 44249 9888 40 181 11784 2423047556199 166388533118268 756070039150762
    p.all (middle p) (total p) (by decide+kernel) hr hs hy ht
  simpa only [stageCost,stagePair,LP,helperPair,PI.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem ABV (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    LX 3200000 44249 9888 (middle p) p.all (total p):=by
  unfold LX helperPair DG.mixedCost
  norm_num
  omega
def sound:YF where
  source:=source
  potential:=potential
  stageCost_le:=by
    intro p j hr hs hy ht _hj
    exact (ZB _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates:=by
    intro p j hr hs hy ht _hj
    exact VW _ _ _ p j (ABV p hr hs hy ht)
noncomputable def kernel (u0 u1:ProximityPrize.Benchmark.IRSProfile.Index→ProximityPrize.Benchmark.IRSProfile.Field):
    Lower80899.BatchPhase.WZ sound u0 u1 where
  D:=5799520000
  m:=32000
  weighted:=by decide
  shape:=JR.Source01.shape
  slope_le_m:=by decide
  m_lt_char:=by decide
  gap_le_finrank:=JR.Source01.finrank_gap u0 u1
end Phase01
namespace Phase02
def source:EA:=⟨2880000,44249,9888,10138882582706100787256⟩
def potential:Potential:=⟨2423047556199,157730788661163,716178658790759⟩
theorem stageZero_le (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    stageCost 2880000 44249 9888 (LP p) 0≤potential.eval p:=by
  have h:=MZ.count_le 2880000 44249 9888 40 181 11784 2423047556199 157730788661163 716178658790759
    p.all (middle p) (total p) (by decide+kernel) hr hs hy ht
  simpa only [stageCost,stagePair,LP,helperPair,PI.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem ABV (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    LX 2880000 44249 9888 (middle p) p.all (total p):=by
  unfold LX helperPair DG.mixedCost
  norm_num
  omega
def sound:YF where
  source:=source
  potential:=potential
  stageCost_le:=by
    intro p j hr hs hy ht _hj
    exact (ZB _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates:=by
    intro p j hr hs hy ht _hj
    exact VW _ _ _ p j (ABV p hr hs hy ht)
noncomputable def kernel (u0 u1:ProximityPrize.Benchmark.IRSProfile.Index→ProximityPrize.Benchmark.IRSProfile.Field):
    Lower80899.BatchPhase.WZ sound u0 u1 where
  D:=5799520000
  m:=32000
  weighted:=by decide
  shape:=JR.Source02.shape
  slope_le_m:=by decide
  m_lt_char:=by decide
  gap_le_finrank:=JR.Source02.finrank_gap u0 u1
end Phase02
namespace Phase03
def source:EA:=⟨1062000,22124,4940,406720822982905372653⟩
def potential:Potential:=⟨1211014347912,68606147651569,310963600590244⟩
theorem stageZero_le (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    stageCost 1062000 22124 4940 (LP p) 0≤potential.eval p:=by
  have h:=MZ.count_le 1062000 22124 4940 40 181 11784 1211014347912 68606147651569 310963600590244
    p.all (middle p) (total p) (by decide+kernel) hr hs hy ht
  simpa only [stageCost,stagePair,LP,helperPair,PI.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem ABV (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    LX 1062000 22124 4940 (middle p) p.all (total p):=by
  unfold LX helperPair DG.mixedCost
  norm_num
  omega
def sound:YF where
  source:=source
  potential:=potential
  stageCost_le:=by
    intro p j hr hs hy ht _hj
    exact (ZB _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates:=by
    intro p j hr hs hy ht _hj
    exact VW _ _ _ p j (ABV p hr hs hy ht)
noncomputable def kernel (u0 u1:ProximityPrize.Benchmark.IRSProfile.Index→ProximityPrize.Benchmark.IRSProfile.Field):
    Lower80899.BatchPhase.WZ sound u0 u1 where
  D:=2899760000
  m:=16000
  weighted:=by decide
  shape:=JR.Source03.shape
  slope_le_m:=by decide
  m_lt_char:=by decide
  gap_le_finrank:=JR.Source03.finrank_gap u0 u1
end Phase03
namespace Phase04
def source:EA:=⟨531000,11062,2470,25109102176306883245⟩
def potential:Potential:=⟨452397292056,44271288457346,155118092834147⟩
theorem stageZero_le (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    stageCost 531000 11062 2470 (LP p) 0≤potential.eval p:=by
  have h:=PI.FUG p.all (middle p) (total p) hr hs hy ht
  simpa only [stageCost,stagePair,LP,helperPair,PI.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem ABV (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    LX 531000 11062 2470 (middle p) p.all (total p):=by
  unfold LX helperPair DG.mixedCost
  norm_num
  omega
def sound:YF where
  source:=source
  potential:=potential
  stageCost_le:=by
    intro p j hr hs hy ht _hj
    exact (ZB _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates:=by
    intro p j hr hs hy ht _hj
    exact VW _ _ _ p j (ABV p hr hs hy ht)
noncomputable def kernel (u0 u1:ProximityPrize.Benchmark.IRSProfile.Index→ProximityPrize.Benchmark.IRSProfile.Field):
    Lower80899.BatchPhase.WZ sound u0 u1 where
  D:=1449880000
  m:=8000
  weighted:=by decide
  shape:=JR.Source04.shape
  slope_le_m:=by decide
  m_lt_char:=by decide
  gap_le_finrank:=JR.Source04.finrank_gap u0 u1
end Phase04
namespace Phase05
def source:EA:=⟨88902,1382,308,7897858914422491⟩
def potential:Potential:=⟨75575123445,4891308750229,22237399921348⟩
theorem stageZero_le (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    stageCost 88902 1382 308 (LP p) 0≤potential.eval p:=by
  have h:=MZ.count_le 88902 1382 308 40 181 11784 75575123445 4891308750229 22237399921348
    p.all (middle p) (total p) (by decide+kernel) hr hs hy ht
  simpa only [stageCost,stagePair,LP,helperPair,PI.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem ABV (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    LX 88902 1382 308 (middle p) p.all (total p):=by
  unfold LX helperPair DG.mixedCost
  norm_num
  omega
def sound:YF where
  source:=source
  potential:=potential
  stageCost_le:=by
    intro p j hr hs hy ht _hj
    exact (ZB _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates:=by
    intro p j hr hs hy ht _hj
    exact VW _ _ _ p j (ABV p hr hs hy ht)
noncomputable def kernel (u0 u1:ProximityPrize.Benchmark.IRSProfile.Index→ProximityPrize.Benchmark.IRSProfile.Field):
    Lower80899.BatchPhase.WZ sound u0 u1 where
  D:=181235000
  m:=1000
  weighted:=by decide
  shape:=JR.Source05.shape
  slope_le_m:=by decide
  m_lt_char:=by decide
  gap_le_finrank:=JR.Source05.finrank_gap u0 u1
end Phase05
namespace Phase06
def source:EA:=⟨3640000,19359,4267,1287314662172554828549⟩
def potential:Potential:=⟨1052770435489,132922975362900,610020809117841⟩
theorem stageZero_le (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    stageCost 3640000 19359 4267 (LP p) 0≤potential.eval p:=by
  have h:=MZ.count_le 3640000 19359 4267 40 181 11784 1052770435489 132922975362900 610020809117841
    p.all (middle p) (total p) (by decide+kernel) hr hs hy ht
  simpa only [stageCost,stagePair,LP,helperPair,PI.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem ABV (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    LX 3640000 19359 4267 (middle p) p.all (total p):=by
  unfold LX helperPair DG.mixedCost
  norm_num
  omega
def sound:YF where
  source:=source
  potential:=potential
  stageCost_le:=by
    intro p j hr hs hy ht _hj
    exact (ZB _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates:=by
    intro p j hr hs hy ht _hj
    exact VW _ _ _ p j (ABV p hr hs hy ht)
noncomputable def kernel (u0 u1:ProximityPrize.Benchmark.IRSProfile.Index→ProximityPrize.Benchmark.IRSProfile.Field):
    Lower80899.BatchPhase.WZ sound u0 u1 where
  D:=2537290000
  m:=14000
  weighted:=by decide
  shape:=JR.Source06.shape
  slope_le_m:=by decide
  m_lt_char:=by decide
  gap_le_finrank:=JR.Source06.finrank_gap u0 u1
end Phase06
namespace PhaseFinal
def source:EA:=⟨88902,1382,308,7897858914422491⟩
def potential:Potential:=⟨0,4941578463932,44352901270546⟩
theorem stageZero_le (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    stageCost 88902 1382 308 (LP p) 0≤potential.eval p:=by
  have h:=PI.EZQ p.all (middle p) (total p) hr hy ht
  simpa only [stageCost,stagePair,LP,helperPair,PI.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem ABV (p:FlagDegree) (hr:1≤p.all) (hs:p.all≤40)
    (hy:middle p≤181) (ht:total p≤11784):
    LX 88902 1382 308 (middle p) p.all (total p):=by
  unfold LX helperPair DG.mixedCost
  norm_num
  omega
def sound:YF where
  source:=source
  potential:=potential
  stageCost_le:=by
    intro p j hr hs hy ht _hj
    exact (ZB _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates:=by
    intro p j hr hs hy ht _hj
    exact VW _ _ _ p j (ABV p hr hs hy ht)
noncomputable def kernel (u0 u1:ProximityPrize.Benchmark.IRSProfile.Index→ProximityPrize.Benchmark.IRSProfile.Field):
    Lower80899.BatchPhase.WZ sound u0 u1 where
  D:=181235000
  m:=1000
  weighted:=by decide
  shape:=JR.Source05.shape
  slope_le_m:=by decide
  m_lt_char:=by decide
  gap_le_finrank:=JR.Source05.finrank_gap u0 u1
end PhaseFinal
end ProximityPrize.SubmissionLower.Lower80899.SourceSound
end MergedPart10
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace BB
open IM
open MvPolynomial DX HZ HH
open OH AQ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
variable {K N:Type*} [Field K] [Fintype N]

def cutoff (m k n0 h:ℕ):ℕ:=m*181235-AQ.reserve k n0 h*50166

def Interpolant (m B s U L k n0:ℕ) (nodes:N ↪ K) (u0 u1:N→K)
    (P:Poly (K:=K)):Prop:=
  P ≠ 0∧
  (∀e ∈ P.support,2*e 1+e 3≤B∧e 1≤s∧e 1+e 2+e 3≤U∧
    e 1+e 2+e 3+e 4≤L∧
    e 0+131071*e 2+131070*e 3+131069*e 1<cutoff m k n0 (e 1))∧
  (∀i,MvPolynomial.X 0^m ∣ substitute (K:=K)
    (localize (nodes i) (u0 i) (u1 i) P))∧
  ∀d≤k,∀f:Polynomial K,f.natDegree≤131071→ ∀z:K,∀S:Finset N,
    181235≤S.card→(∀i ∈ S,f.eval (nodes i)=u0 i+u1 i*z)→
      specialize f z ((pderiv 1)^[d] P)=0

theorem JD (m B s U L k n0:ℕ) (hsB:2*s≤B) (hkm:k<m)
    (hN:Fintype.card N=262144) (nodes:N ↪ K) (u0 u1:N→K)
    (hcard:262144*EG.rankBound m L B s U
        (fun h=>(cutoff m k n0 h+B-1)/131071)<
      Fintype.card (DD.Index (cutoff m k n0) 131071 L B s U)):
    ∃P,Interpolant m B s U L k n0 nodes u0 u1 P:=by
  obtain ⟨P,hP,hbounds,hcontact⟩:=DD.BQU
    (cutoff m k n0) 131071 L B s U m hsB (by decide) nodes u0 u1 (by simpa only [hN] using hcard)
  have hc: ∀i,MvPolynomial.X 0^m ∣ substitute (K:=K)
      (localize (nodes i) (u0 i) (u1 i) P):=fun i=>
    KL.CGJ _ m (hcontact i)
  refine ⟨P,hP,hbounds,hc,?_⟩
  intro d hd f hf z S hS hvalues
  apply AMU P m 181235 131071 k n0 d (by decide) (by decide)
    (by omega) hd ?_ nodes u0 u1 hc f hf z S hS hvalues
  intro e he
  have hb:=(hbounds e he).2.2.2.2
  dsimp [cutoff] at hb
  norm_num
  omega

end
end BB
end MergedPart0
section MergedPart1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace CH.P0
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=132
def B:ℕ:=54
def s:ℕ:=25
def U:ℕ:=180
def L:ℕ:=1935
def k:ℕ:=5
def n0:ℕ:=7

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      2280074396081297:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=8697765996:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=2280074396081297:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=8697765996:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*8697765996<2280074396081297:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P0

namespace CH.P1
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=133
def B:ℕ:=56
def s:ℕ:=25
def U:ℕ:=180
def L:ℕ:=3119
def k:ℕ:=6
def n0:ℕ:=8

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      3987943710128528:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=15212787534:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=3987943710128528:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=15212787534:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*15212787534<3987943710128528:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P1

namespace CH.P2
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=136
def B:ℕ:=56
def s:ℕ:=25
def U:ℕ:=185
def L:ℕ:=2911
def k:ℕ:=6
def n0:ℕ:=8

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      3914500176105135:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=14932623447:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=3914500176105135:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=14932623447:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*14932623447<3914500176105135:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P2

namespace CH.P3
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=116
def B:ℕ:=46
def s:ℕ:=21
def U:ℕ:=158
def L:ℕ:=3225
def k:ℕ:=5
def n0:ℕ:=7

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      2214704218741999:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=8448417816:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=2214704218741999:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=8448417816:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*8448417816<2214704218741999:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P3

namespace CH.P4
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=114
def B:ℕ:=45
def s:ℕ:=20
def U:ℕ:=155
def L:ℕ:=3642
def k:ℕ:=5
def n0:ℕ:=7

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      2315333205668819:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=8832294900:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=2315333205668819:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=8832294900:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*8832294900<2315333205668819:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P4

namespace CH.P5
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=158
def B:ℕ:=63
def s:ℕ:=28
def U:ℕ:=215
def L:ℕ:=3383
def k:ℕ:=7
def n0:ℕ:=10

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      7779460537890279:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=29676286694:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=7779460537890279:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=29676286694:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*29676286694<7779460537890279:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P5
end MergedPart1
section MergedPart2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace CH.P6
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=167
def B:ℕ:=73
def s:ℕ:=33
def U:ℕ:=226
def L:ℕ:=3496
def k:ℕ:=8
def n0:ℕ:=9

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      11581591205013754:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=44180233512:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=11581591205013754:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=44180233512:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*44180233512<11581591205013754:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P6

namespace CH.P7
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=114
def B:ℕ:=47
def s:ℕ:=21
def U:ℕ:=154
def L:ℕ:=3257
def k:ℕ:=5
def n0:ℕ:=7

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      2214333322059217:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=8447004300:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=2214333322059217:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=8447004300:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*8447004300<2214333322059217:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P7

namespace CH.P8
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=142
def B:ℕ:=56
def s:ℕ:=25
def U:ℕ:=193
def L:ℕ:=3083
def k:ℕ:=6
def n0:ℕ:=9

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      4588592483165103:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=17504075871:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=4588592483165103:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=17504075871:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*17504075871<4588592483165103:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P8

namespace CH.P9
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=174
def B:ℕ:=76
def s:ℕ:=34
def U:ℕ:=236
def L:ℕ:=3018
def k:ℕ:=8
def n0:ℕ:=9

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      11658378769660847:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=44473138791:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=11658378769660847:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=44473138791:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*44473138791<11658378769660847:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P9

namespace CH.P10
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=170
def B:ℕ:=71
def s:ℕ:=32
def U:ℕ:=231
def L:ℕ:=3484
def k:ℕ:=8
def n0:ℕ:=10

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      11511104209049142:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=43911336522:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=11511104209049142:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=43911336522:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*43911336522<11511104209049142:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P10

namespace CH.P11
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=97
def B:ℕ:=41
def s:ℕ:=19
def U:ℕ:=132
def L:ℕ:=2775
def k:ℕ:=4
def n0:ℕ:=6

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      1051214702203687:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=4010065389:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=1051214702203687:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=4010065389:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*4010065389<1051214702203687:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P11
end MergedPart2
section MergedPart3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace CH.P12
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=142
def B:ℕ:=59
def s:ℕ:=27
def U:ℕ:=193
def L:ℕ:=2685
def k:ℕ:=6
def n0:ℕ:=9

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      4341316715620411:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=16560776891:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=4341316715620411:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=16560776891:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*16560776891<4341316715620411:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P12

namespace CH.P13
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=158
def B:ℕ:=69
def s:ℕ:=31
def U:ℕ:=214
def L:ℕ:=2660
def k:ℕ:=7
def n0:ℕ:=8

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      7027679135100320:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=26808466660:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=7027679135100320:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=26808466660:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*26808466660<7027679135100320:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P13

namespace CH.P14
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=146
def B:ℕ:=58
def s:ℕ:=26
def U:ℕ:=198
def L:ℕ:=2766
def k:ℕ:=6
def n0:ℕ:=9

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      4631863281470244:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=17669150784:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=4631863281470244:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=17669150784:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*17669150784<4631863281470244:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P14

namespace CH.P15
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=98
def B:ℕ:=41
def s:ℕ:=19
def U:ℕ:=133
def L:ℕ:=2667
def k:ℕ:=4
def n0:ℕ:=6

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      1033971174325207:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=3944286890:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=1033971174325207:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=3944286890:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*3944286890<1033971174325207:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P15

namespace CH.P16
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=150
def B:ℕ:=60
def s:ℕ:=27
def U:ℕ:=204
def L:ℕ:=2504
def k:ℕ:=6
def n0:ℕ:=9

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      4699620378673493:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=17927586760:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=4699620378673493:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=17927586760:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*17927586760<4699620378673493:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P16

namespace CH.P17
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=161
def B:ℕ:=71
def s:ℕ:=32
def U:ℕ:=218
def L:ℕ:=2524
def k:ℕ:=7
def n0:ℕ:=8

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      7278386120216350:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=27764830737:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=7278386120216350:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=27764830737:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*27764830737<7278386120216350:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P17
end MergedPart3
section MergedPart4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace CH.P18
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=114
def B:ℕ:=47
def s:ℕ:=21
def U:ℕ:=155
def L:ℕ:=3155
def k:ℕ:=5
def n0:ℕ:=7

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      2143831092366876:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=8178058899:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=2143831092366876:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=8178058899:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*8178058899<2143831092366876:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P18

namespace CH.P19
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=166
def B:ℕ:=66
def s:ℕ:=30
def U:ℕ:=226
def L:ℕ:=2932
def k:ℕ:=7
def n0:ℕ:=10

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      8140863652995707:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=31054880752:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=8140863652995707:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=31054880752:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*31054880752<8140863652995707:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P19

namespace CH.P20
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=175
def B:ℕ:=76
def s:ℕ:=34
def U:ℕ:=237
def L:ℕ:=2990
def k:ℕ:=8
def n0:ℕ:=9

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      11702791690016735:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=44642601346:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=11702791690016735:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=44642601346:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*44642601346<11702791690016735:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P20

namespace CH.P21
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=111
def B:ℕ:=46
def s:ℕ:=21
def U:ℕ:=151
def L:ℕ:=3695
def k:ℕ:=5
def n0:ℕ:=7

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      2295616262780031:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=8757079531:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=2295616262780031:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=8757079531:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*8757079531<2295616262780031:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P21

namespace CH.P22
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=189
def B:ℕ:=83
def s:ℕ:=37
def U:ℕ:=256
def L:ℕ:=3453
def k:ℕ:=9
def n0:ℕ:=10

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      18649122800334149:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=71140745720:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=18649122800334149:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=71140745720:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*71140745720<18649122800334149:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P22

namespace CH.P23
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=114
def B:ℕ:=45
def s:ℕ:=20
def U:ℕ:=155
def L:ℕ:=3642
def k:ℕ:=5
def n0:ℕ:=7

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      2315333205668819:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=8832294900:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=2315333205668819:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=8832294900:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*8832294900<2315333205668819:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P23
end MergedPart4

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace ETH
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN302
open RZ IL
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000










open KZ
noncomputable section

end



end ETH

section MergedPart0
namespace BIM
open MvPolynomial DX HZ HH
open BX JQ IM
open AQ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N:Type*} [Field K]

theorem BFX (f:Polynomial K) (z:K) (w:ℕ)
    (hf:f.natDegree≤w) (e:Fin 4→₀ ℕ) (c:K):
    (FL f z (MvPolynomial.monomial e c)).natDegree≤
      e 0+w*e 1+(w-1)*e 2:=by
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,map_mul,map_pow]
    have hc:(FL f z (MvPolynomial.C c)).natDegree≤0:=by
      simp [FL]
    have h0:(FL f z (MvPolynomial.X 0)^e 0).natDegree≤e 0:=by
      simp [FL]
    have h1:(FL f z (MvPolynomial.X 1)^e 1).natDegree≤e 1*w:=by
      simpa [FL] using Polynomial.natDegree_pow_le_of_le (e 1) hf
    have h2:(FL f z (MvPolynomial.X 2)^e 2).natDegree≤e 2*(w-1):=by
      simpa [FL] using Polynomial.natDegree_pow_le_of_le (e 2)
        ((Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1))
    have h3:(FL f z (MvPolynomial.X 3)^e 3).natDegree≤0:=by
      simp [FL]
    have hh:=Polynomial.natDegree_mul_le_of_le hc (Polynomial.natDegree_mul_le_of_le h0
      (Polynomial.natDegree_mul_le_of_le h1 (Polynomial.natDegree_mul_le_of_le h2 h3)))
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Nat.mul_comm] using hh
  · intro i
    simp

theorem BOT (P:MvPolynomial (Fin 4) K) (f:Polynomial K)
    (z:K) (w D:ℕ) (hf:f.natDegree≤w) (hD:0<D)
    (hP: ∀e ∈ P.support,e 0+w*e 1+(w-1)*e 2<D):
    (FL f z P).natDegree<D:=by
  classical
  have ht: ∀e ∈ P.support,
      (FL f z (MvPolynomial.monomial e (AddMonoidAlgebra.coeff P e))).natDegree≤D-1:=by
    intro e he
    have hh:=BFX f z w hf e (AddMonoidAlgebra.coeff P e)
    have hb:=hP e he
    omega
  rw [MvPolynomial.as_sum P,map_sum]
  have hh:=Polynomial.natDegree_sum_le_of_forall_le P.support
    (fun e=>FL f z (MvPolynomial.monomial e (AddMonoidAlgebra.coeff P e))) ht
  omega

theorem CHD {R:Type*} [CommRing R] (P:Polynomial R) (d:ℕ)
    (hh: ∀j,d<j→P.coeff j=0):
    (Polynomial.derivative)^[d] P=Polynomial.C (d.factorial • P.coeff d):=by
  ext j
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hj:j=0
  · subst j
    simp [Nat.descFactorial_self]
  · rw [hh (j+d) (by omega)]
    simp [hj]

theorem DIO (P:Poly (K:=K)) (f:Polynomial K) (z:K) (d:ℕ)
    (hh: ∀j,d<j→FL f z ((asS P).coeff j)=0):
    specialize f z ((pderiv 1)^[d] P)=
      d.factorial • FL f z ((asS P).coeff d):=by
  rw [FAP,asS_iterate,← Polynomial.eval_map,← Polynomial.iterate_derivative_map]
  rw [CHD _ d (by intro j hj;simpa using hh j hj)]
  simp

theorem ATR (P:Poly (K:=K)) (m k n0 d:ℕ)
    (hdm:d<m) (hdn:d<n0) (hfact:(d.factorial:K) ≠ 0)
    (hP: ∀e ∈ P.support,
      e 0+131071*e 2+131070*e 3+131069*e 1+
        reserve k n0 (e 1)*50166<m*181235)
    (nodes:N ↪ K) (u0 u1:N→K)
    (hcontact: ∀i,MvPolynomial.X 0^m ∣ substitute (K:=K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (f:Polynomial K) (hf:f.natDegree≤131071) (z:K) (S:Finset N)
    (hS:181235≤S.card) (hvalues: ∀i ∈ S,f.eval (nodes i)=u0 i+u1 i*z)
    (hh: ∀j,d<j→FL f z ((asS P).coeff j)=0):
    FL f z ((asS P).coeff d)=0:=by
  have hweight: ∀e ∈ ((asS P).coeff d).support,
      e 0+131071*e 1+131070*e 2<(m-d)*181235:=by
    intro e he
    have hb:=hP _ (AJU P d e he)
    obtain ⟨h0,h1,h2,h3,h4⟩:=_Q17 d e
    rw [h0,h1,h2,h3] at hb
    simp only [reserve,if_pos hdn] at hb
    omega
  have hdeg:=BOT ((asS P).coeff d) f z 131071 ((m-d)*181235)
    hf (by omega) hweight
  have htop:=DIO P f z d hh
  have hv:specialize f z ((pderiv 1)^[d] P)=0:=by
    refine CAG.ALK _ f z nodes u0 u1 S (m-d) ?_ hvalues ?_
    · intro i _
      apply KL.ADR
      simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hcontact i
    · rw [htop]
      have hs:=Polynomial.natDegree_smul_le d.factorial
        (FL f z ((asS P).coeff d))
      exact (hs.trans_lt hdeg).trans_le (Nat.mul_le_mul_left (m-d) hS)
  rw [htop,nsmul_eq_mul] at hv
  apply (mul_eq_zero.mp hv).resolve_left
  simpa only [map_natCast] using (Polynomial.C_ne_zero.mpr hfact)

end
end BIM
end MergedPart0
section MergedPart1
namespace AXB
open MvPolynomial DX BX JQ
open FR OR BB
open OH RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option maxRecDepth 100000
variable {K N:Type*} [Field K] [Fintype N]

def ProperHelper (F Q:MvPolynomial (Fin 4) K) (B U L s capR capY capT:ℕ)
    (nodes:N ↪ K) (u0 u1:N→K):Prop:=
  IsRelPrime F Q∧
  (wt BE Q≤B+s*(capR-1)∧
    wt BC Q≤U+s*(capY-1)∧
    wt AT Q≤L+s*(capT-1))∧
  ∀f:Polynomial K,f.natDegree≤131071→ ∀z:K,∀S:Finset N,
    181235≤S.card→(∀i ∈ S,f.eval (nodes i)=u0 i+u1 i*z)→
    RCN319.BM K f z F=0→RCN319.BM K f z Q=0

theorem EXD (P:Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (m B s U L k n0 capR capY capT:ℕ)
    (nodes:N ↪ K) (u0 u1:N→K)
    (hP:Interpolant m B s U L k n0 nodes u0 u1 P)
    (hFi:Irreducible F) (hFT:L<wt AT F)
    (hsB:2*s≤B) (hsU:s≤U) (hsL:s≤L) (hks:k≤s) (hsm:s<m)
    (hR:1≤capR) (hY:1≤capY) (hT:1≤capT)
    (hF:wt BE F≤capR∧wt BC F≤capY∧
      wt AT F≤capT)
    (hfact: ∀d≤s,(d.factorial:K) ≠ 0):
    (∃Q,ProperHelper F Q B U L s capR capY capT nodes u0 u1)∨
      (n0≤(asS P).natDegree∧ ∀d≤k,F ∣ helper P F (s-d) d):=by
  classical
  have hflags: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤L:=by
    intro e he
    have h:=hP.2.1 e he
    exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
  have hS: ∀e ∈ P.support,e 1≤s:=fun e he=>(hP.2.1 e he).2.1
  have hdegree:(asS P).natDegree≤s:=by
    simpa using AFG P s 0 hS
  by_cases hn:(asS P).natDegree<n0
  · left
    let n:=(asS P).natDegree
    let Q:=(asS P).leadingCoeff
    have hQ:=AFH.CAK P hP.1 F L
      (fun e he=>(hflags e he).2.2) hFT
    refine ⟨Q,hFi.isRelPrime_iff_not_dvd.mpr hQ.2,?_,?_⟩
    · have hw:=OE P B U L 0 n hflags
      simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
      change wt BE ((asS P).coeff n)≤B+s*(capR-1)∧
        wt BC ((asS P).coeff n)≤U+s*(capY-1)∧
        wt AT ((asS P).coeff n)≤L+s*(capT-1)
      omega
    · intro f hf z S hSc hvalues _hFzero
      have hweight: ∀e ∈ P.support,
          e 0+131071*e 2+131070*e 3+131069*e 1+
            AQ.reserve k n0 (e 1)*50166<m*181235:=by
        intro e he
        have hw:=(hP.2.1 e he).2.2.2.2
        dsimp [BB.cutoff] at hw
        omega
      apply BIM.ATR P m k n0 n
        (by dsimp [n];omega) hn (hfact n hdegree) hweight nodes u0 u1 hP.2.2.1
        f hf z S hSc hvalues
      intro j hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj,map_zero]
  · by_cases hdiv: ∀d≤k,F ∣ helper P F (s-d) d
    · exact Or.inr ⟨Nat.le_of_not_gt hn,hdiv⟩
    · left
      push_neg at hdiv
      obtain ⟨d,hd,hproper⟩:=hdiv
      refine ⟨helper P F (s-d) d,hFi.isRelPrime_iff_not_dvd.mpr hproper,?_,?_⟩
      · have hw:=EUI P F B U L s d capT capY capR hsB hsU hsL
          (hd.trans hks) hR hY hT hflags hF
        have hr:=Nat.mul_le_mul_right (capR-1) (Nat.sub_le s d)
        have hy:=Nat.mul_le_mul_right (capY-1) (Nat.sub_le s d)
        have ht:=Nat.mul_le_mul_right (capT-1) (Nat.sub_le s d)
        omega
      · intro f hf z S hSc hvalues hFzero
        exact FAI P F (s-d) d (AFG P s d hS) f z hFzero
          (hP.2.2.2 d hd f hf z S hSc hvalues)

end
end AXB
end MergedPart1
section MergedPart2
namespace Lower80899.Selection
open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN183
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:StrongNormalizationMonoid P4:=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid P4:=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid P4
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
abbrev TCapKernel (u0 u1:I→K):=
  IJ (K:=K) 45671220 131071 11785 78 252 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I→K):=
  IJ (K:=K) 30085010 131071 17230 50 166 IRSProfile.domain u0 u1
theorem gateTCap:Fintype.card I*ES 252 11785 78<AW 45671220 131071 11785 78:=by
  rw [JR.TCap.rank_exact,JR.TCap.OS]
  norm_num [I,IRSProfile.Index]
theorem gateB:Fintype.card I*ES 166 17230 50<AW 30085010 131071 17230 50:=by
  rw [JR.B.rank_exact,JR.B.OS]
  norm_num [I,IRSProfile.Index]
private theorem DPK
    (P H q:P4) (hc:IsRelPrime q P):
    Associated (gcd P (H*q)) (gcd P H):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd P (H*q) ∣ P:=gcd_dvd_left P (H*q)
    have hright:gcd P (H*q) ∣ H*q:=gcd_dvd_right P (H*q)
    have hcop:IsRelPrime (gcd P (H*q)) q:=hc.symm.of_dvd_left hleft
    exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
  · exact dvd_gcd (gcd_dvd_left P H)
      ((gcd_dvd_right P H).trans (dvd_mul_right H q))
private theorem DTF
    (H q P:P4) (hc:IsRelPrime q P):
    Associated (gcd (H*q) P) (gcd H P):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd (H*q) P ∣ H*q:=gcd_dvd_left (H*q) P
    have hright:gcd (H*q) P ∣ P:=gcd_dvd_right (H*q) P
    have hcop:IsRelPrime (gcd (H*q) P) q:=hc.symm.of_dvd_left hright
    exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
  · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
      (gcd_dvd_right H P)
structure SelectedPair (u0 u1:I→K) where
  QA:P4
  QB:P4
  QA_ne:QA ≠ 0
  QB_ne:QB ≠ 0
  QA_flag:QA ∈ BA K 45671220 131071 11785 78
  QB_flag:QB ∈ BA K 30085010 131071 17230 50
  common_divides_TCap:∀v:TCapKernel u0 u1,
    gcd QA QB ∣ reconstruct K 45671220 131071 11785 78 v.1
  common_divides_B:∀v:BKernel u0 u1,
    gcd QA QB ∣ reconstruct K 30085010 131071 17230 50 v.1
  EEM:
    ∀(gamma:K) (P:Polynomial K) (points:Finset I),
      P.natDegree≤131071→181235≤points.card→
      (∀i ∈ points,P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i)→
      RCN319.BM K P gamma QA=0∧
        RCN319.BM K P gamma QB=0
theorem FFX (u0 u1:I→K):Nonempty (SelectedPair u0 u1):=by
  classical
  obtain ⟨thetaT,htT,hkT⟩:=ACY (I:=I)
    K 45671220 131071 11785 78 252 IRSProfile.domain u0 u1 gateTCap
  obtain ⟨thetaB,htB,hkB⟩:=ACY (I:=I)
    K 30085010 131071 17230 50 166 IRSProfile.domain u0 u1 gateB
  let vT0:TCapKernel u0 u1:=⟨thetaT,LinearMap.mem_ker.mpr hkT⟩
  let vB0:BKernel u0 u1:=⟨thetaB,LinearMap.mem_ker.mpr hkB⟩
  letI:Nontrivial (TCapKernel u0 u1):=⟨⟨vT0,0,by
    intro h
    exact htT (congrArg Subtype.val h)⟩⟩
  letI:Nontrivial (BKernel u0 u1):=⟨⟨vB0,0,by
    intro h
    exact htB (congrArg Subtype.val h)⟩⟩
  let bT:=Module.Free.chooseBasis K (TCapKernel u0 u1)
  let bB:=Module.Free.chooseBasis K (BKernel u0 u1)
  letI:Finite (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=
    Module.Finite.finite_basis bT
  letI:Finite (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=
    Module.Finite.finite_basis bB
  letI:Fintype (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=Fintype.ofFinite _
  letI:Fintype (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=Fintype.ofFinite _
  letI:Nonempty (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=bT.index_nonempty
  letI:Nonempty (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=bB.index_nonempty
  let HT:=commonGCD (TCapKernel u0 u1) bT
  let HB:=commonGCD (BKernel u0 u1) bB
  have hHT:HT ≠ 0:=EUK (TCapKernel u0 u1) bT
  have hHB:HB ≠ 0:=EUK (BKernel u0 u1) bB
  have hHBbox:HB ∈ BA K 30085010 131071 17230 50:=
    FBX (BKernel u0 u1) bB
  have hcardHB:(IW HB).card<ENat.card K:=
    AIZ HB 30085010 17230 50
      hHB hHBbox (by norm_num)
  obtain ⟨vA,hvA,hcopA⟩:=BKG
    (TCapKernel u0 u1) bT hHT HB hHB hcardHB
  let qA:=ADU (TCapKernel u0 u1) bT hHT vA
  let QA:=SY (TCapKernel u0 u1) vA
  have hQAeq:QA=HT*qA:=LR
    (SY (TCapKernel u0 u1)) HT
    (CMM (TCapKernel u0 u1) bT) vA
  have hQA:QA ≠ 0:=by
    intro hz
    apply hvA
    apply AZP (TCapKernel u0 u1)
    simpa only [map_zero,QA] using hz
  have hQAbox:QA ∈ BA K 45671220 131071 11785 78:=by
    dsimp only [QA]
    rw [AHO]
    exact LG K 45671220 131071 11785 78 vA.1
  have hcardQA:(IW QA).card<ENat.card K:=
    AIZ QA 45671220 11785 78
      hQA hQAbox (by norm_num)
  obtain ⟨vB,hvB,hcopB⟩:=BKG
    (BKernel u0 u1) bB hHB QA hQA hcardQA
  let qB:=ADU (BKernel u0 u1) bB hHB vB
  let QB:=SY (BKernel u0 u1) vB
  have hQBeq:QB=HB*qB:=LR
    (SY (BKernel u0 u1)) HB
    (CMM (BKernel u0 u1) bB) vB
  have hQB:QB ≠ 0:=by
    intro hz
    apply hvB
    apply AZP (BKernel u0 u1)
    simpa only [map_zero,QB] using hz
  have hQBbox:QB ∈ BA K 30085010 131071 17230 50:=by
    dsimp only [QB]
    rw [AHO]
    exact LG K 30085010 131071 17230 50 vB.1
  have hAssocA:Associated (gcd QA HB) (gcd HT HB):=by
    rw [hQAeq]
    exact DTF HT qA HB hcopA
  have hAssocB:Associated (gcd QA QB) (gcd QA HB):=by
    rw [hQBeq]
    exact DPK QA HB qB hcopB
  have hAssoc:=hAssocB.trans hAssocA
  have hHHT:gcd QA QB ∣ HT:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_left HT HB)
  have hHHB:gcd QA QB ∣ HB:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_right HT HB)
  refine ⟨{
    QA:=QA,QB:=QB,QA_ne:=hQA,QB_ne:=hQB
    QA_flag:=hQAbox,QB_flag:=hQBbox
    common_divides_TCap:=?_,common_divides_B:=?_
    EEM:=?_}⟩
  · intro v
    exact hHHT.trans (EJX (TCapKernel u0 u1) bT v)
  · intro v
    exact hHHB.trans (EJX (BKernel u0 u1) bB v)
  · intro gamma P points hP hcard hvalues
    constructor
    · dsimp only [QA]
      rw [AHO]
      exact AZK K
        45671220 131071 11785 78 252 181235 IRSProfile.domain u0 u1
        vA.1 vA.2 (by decide+kernel) (by decide+kernel) P gamma points hP hcard hvalues
    · dsimp only [QB]
      rw [AHO]
      exact AZK K
        30085010 131071 17230 50 166 181235 IRSProfile.domain u0 u1
        vB.1 vB.2 (by decide+kernel) (by decide+kernel) P gamma points hP hcard hvalues
end
end Lower80899.Selection

namespace Lower80899.Caps
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev AKernel (u0 u1:I→K):=
  IJ (K:=K) 24285490 131071 104142 40 134 IRSProfile.domain u0 u1
abbrev TCapKernel (u0 u1:I→K):=
  IJ (K:=K) 45671220 131071 11785 78 252 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I→K):=
  IJ (K:=K) 30085010 131071 17230 50 166 IRSProfile.domain u0 u1

theorem gateB:Fintype.card I*ES 166 17230 50<AW 30085010 131071 17230 50:=by
  rw [JR.B.rank_exact,JR.B.OS]
  norm_num [I,IRSProfile.Index]
theorem EAM (D w L s m:ℕ)
    (gate:Fintype.card I*ES m L s<AW D w L s)
    (u0 u1:I→K) (F:P4)
    (hdiv:∀v:IJ (K:=K) D w L s m IRSProfile.domain u0 u1,
      F ∣ reconstruct K D w L s v.1):
    F ∈ BA K D w L s:=by
  classical
  obtain ⟨a,ha,hk⟩:=ACY (I:=I)
    K D w L s m IRSProfile.domain u0 u1 gate
  let v:IJ (K:=K) D w L s m IRSProfile.domain u0 u1:=
    ⟨a,LinearMap.mem_ker.mpr hk⟩
  have hQ:reconstruct K D w L s a ≠ 0:=AVT K D w L s a ha
  exact AMA F (reconstruct K D w L s a)
    D w L s hQ (hdiv v) (LG K D w L s a)

theorem DOM (u0 u1:I→K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀v:BKernel u0 u1,F ∣ reconstruct K 30085010 131071 17230 50 v.1):
    F ∈ BA K 30085010 131071 17230 50:=
  EAM 30085010 131071 17230 50 166 gateB u0 u1 F hdiv


theorem FYU (u0 u1:I→K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀v:BKernel u0 u1,F ∣ reconstruct K 30085010 131071 17230 50 v.1):
    wt BE F≤50:=
  ((JT F 30085010 131071 17230 50 (by decide+kernel)).mp
    (DOM u0 u1 F hF hdiv)).2.1
theorem GLT (u0 u1:I→K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀v:BKernel u0 u1,F ∣ reconstruct K 30085010 131071 17230 50 v.1):
    wt BC F≤229:=by
  have hcaps:=(JT F
    30085010 131071 17230 50 (by decide+kernel)).mp
    (DOM u0 u1 F hF hdiv)
  have hr:wt BE F≤50:=hcaps.2.1
  have hc:wt (BV 131071) F≤30085010-1:=hcaps.2.2
  have hw:=XV F 131071 (by decide+kernel)
  omega
theorem FDN (u0 u1:I→K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀v:TCapKernel u0 u1,F ∣ reconstruct K 45671220 131071 11785 78 v.1):
    wt AT F≤11784:=by
  by_contra hnot
  have ht:11785≤wt AT F:=by omega
  have hdivK:∀v:TCapKernel u0 u1,
      F ∣ LZ (K:=K)
        45671220 131071 11785 78 252 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [SE] using hdiv v
  have hq:∀v:TCapKernel u0 u1,
      ZK
        (LZ (K:=K) (I:=I)
          45671220 131071 11785 78 252 IRSProfile.domain u0 u1)
        F hdivK v ∈ BA K 45671220 131071 0 78:=by
    have h:=IL.CBL (K:=K) (I:=I)
      45671220 131071 11785 78 252 0 11785 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 11785-11785=0 by decide] using h v
  have hobs:=AZT (K:=K) (I:=I)
    45671220 131071 11785 78 252 45671220 0 78
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  rw [JR.TCap.AJI] at hobs
  exact (not_lt_of_ge hobs) JR.TCap.FPR
end
end Caps
end Lower80899

namespace Lower80899.Selection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem GHS {u0 u1:I→K} (S:SelectedPair u0 u1):
    wt AT (gcd S.QA S.QB)≤11784:=
  Caps.FDN u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_TCap
theorem common_ys_le {u0 u1:I→K} (S:SelectedPair u0 u1):
    wt BC (gcd S.QA S.QB)≤229:=
  Caps.GLT u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
theorem GGF {u0 u1:I→K} (S:SelectedPair u0 u1):
    wt BE (gcd S.QA S.QB)≤50:=
  Caps.FYU u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
end
end Lower80899.Selection.SelectedPair
end MergedPart2

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace JE

open RCN055 RCN056 RCN313
variable {K:Type*} [CommRing K]
noncomputable section
local notation "Poly4" =>MvPolynomial (Fin 4) K

def sExponent (m i:ℕ):ℕ:=max (m-2*i) 0
def boundaryJ (F:Poly4):Poly4:=MvPolynomial.pderiv (2:Fin 4) (polyH K F)

def QT (F:Poly4) (m i:ℕ) (C:Poly4):Poly4:=
  polyH K F^i*polyG K F^(m+1-i)*boundaryJ F^sExponent m i*C

def dZero (P:Poly4):Poly4:=
  TR P

def COD (F:Poly4) (m i:ℕ) (C:Poly4):Poly4:=
  ((i:Poly4)-(2*m+1:ℕ))*
    boundaryJ F^(sExponent m i+1-sExponent (m+1) i)*C

def DEL (F:Poly4) (m i:ℕ) (C:Poly4):Poly4:=
  boundaryJ F^(sExponent m i-sExponent (m+1) (i+1))*
    (((i:Poly4)-(2*m+1:ℕ))*dZero (polyH K F)+
      (m+1-i:Poly4)*MvPolynomial.pderiv (2:Fin 4) (polyG K F))*C
      +polyG K F*boundaryJ F^(sExponent m i-sExponent (m+1) (i+1))*
        MvPolynomial.pderiv (2:Fin 4) C

def DEI (F:Poly4) (m i:ℕ) (C:Poly4):Poly4:=
  if 0<sExponent m i then
    (sExponent m i:Poly4)*polyG K F*
      MvPolynomial.pderiv (2:Fin 4) (boundaryJ F)*
      boundaryJ F^(sExponent m i-1-sExponent (m+1) (i+1))*C
  else 0

def DTR (F:Poly4) (m i:ℕ) (C:Poly4):Poly4:=
    boundaryJ F^(sExponent m i-sExponent (m+1) (i+2))*
    ((m+1-i:Poly4)*dZero (polyG K F))*C+
      polyG K F*boundaryJ F^(sExponent m i-sExponent (m+1) (i+2))*
        dZero C

def DSP (F:Poly4) (m i:ℕ) (C:Poly4):Poly4:=
  if 0<sExponent m i then
    (sExponent m i:Poly4)*polyG K F*dZero (boundaryJ F)*
      boundaryJ F^(sExponent m i-1-sExponent (m+1) (i+2))*C
  else 0

def DRR (F:Poly4) (C:Poly4):Poly4:=polyH K F*dZero C

def ATP (F:Poly4) (m:ℕ) (C:ℕ→Poly4) (q:ℕ):Poly4:=
  ∑ i ∈ Finset.range (m+2),
    (if q=i then COD F m i (C i)
     else if q=i+1 then
       DEL F m i (C i)+DEI F m i (C i)+
         if i=m+1 then DRR F (C i) else 0
     else if q=i+2∧i≤m then
       DTR F m i (C i)+DSP F m i (C i)
     else 0)

def RE (F:Poly4):ℕ→ℕ→Poly4
  | 0,i=>if i=0 then 1 else 0
  | m+1,i=>ATP F m (RE F m) i

theorem EVT (F C:Poly4) (i b s lambda:ℕ):
    polyH K F*OB F
        (polyH K F^i*polyG K F^b*boundaryJ F^s*C)-
      (lambda:Poly4)*(polyH K F^i*polyG K F^b*boundaryJ F^s*C)*
        OB F (polyH K F)=
      ((i:Poly4)-(lambda:ℕ))*polyH K F^i*polyG K F^(b+1)*
          boundaryJ F^(s+1)*C+
      polyH K F^(i+1)*polyG K F^b*boundaryJ F^s*
        (((i:Poly4)-(lambda:ℕ))*dZero (polyH K F)+
          (b:Poly4)*MvPolynomial.pderiv (2:Fin 4) (polyG K F))*C+
      polyH K F^(i+1)*polyG K F^(b+1)*boundaryJ F^s*
        MvPolynomial.pderiv (2:Fin 4) C+
      (s:Poly4)*polyH K F^(i+1)*polyG K F^(b+1)*
        boundaryJ F^(s-1)*MvPolynomial.pderiv (2:Fin 4) (boundaryJ F)*C+
      (b:Poly4)*polyH K F^(i+2)*polyG K F^(b-1)*
        boundaryJ F^s*dZero (polyG K F)*C+
      polyH K F^(i+2)*polyG K F^b*boundaryJ F^s*dZero C+
      (s:Poly4)*polyH K F^(i+2)*polyG K F^b*
        boundaryJ F^(s-1)*dZero (boundaryJ F)*C:=by
  simp only [AEH,dZero,TR,
    Derivation.add_apply,Derivation.smul_apply,smul_eq_mul,
    MvPolynomial.pderiv_mul,Derivation.leibniz_pow,nsmul_eq_mul]
  cases i<;>cases b<;>cases s<;>
    simp only [Nat.cast_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_one,
    Nat.add_sub_cancel,Nat.succ_sub_one,pow_succ,pow_zero,
      zero_mul,mul_zero,one_mul,mul_one,boundaryJ]<;>ring

theorem FIQ (m i:ℕ):
    sExponent m i+1≥sExponent (m+1) i:=by
  unfold sExponent
  omega

theorem FSK (m i:ℕ):
    sExponent m i≥sExponent (m+1) (i+1):=by
  unfold sExponent
  omega

theorem FDC (m i:ℕ):
    sExponent m i≥sExponent (m+1) (i+2):=by
  unfold sExponent
  omega

theorem EHV (m i:ℕ) (hs:0<sExponent m i):
    sExponent m i-1≥sExponent (m+1) (i+1):=by
  unfold sExponent at*
  omega

theorem DUZ (m i:ℕ) (hs:0<sExponent m i):
    sExponent m i-1≥sExponent (m+1) (i+2):=by
  unfold sExponent at*
  omega

end
end JE
end MergedPart0
section MergedPart1
namespace JE

open RCN055 RCN056 RCN057 RCN313
open scoped BigOperators

noncomputable section
variable {K:Type*} [Field K]
local notation "Poly4" =>MvPolynomial (Fin 4) K

theorem ALV {w:Fin 4→ℕ} {P:Poly4} {a:ℤ}
    (hP:WeightBound w P a) (n:ℕ):WeightBound w (P^n) ((n:ℤ)*a):=by
  induction n with
  | zero=>simpa using (WeightBound.natCast (w:=w) (K:=K) 1)
  | succ n ih=>
    rw [pow_succ]
    convert ih.mul hP using 1<;>push_cast<;>ring

theorem ELJ {w:Fin 4→ℕ} {ι:Type*} [DecidableEq ι] (S:Finset ι)
    (P:ι→Poly4) (a:ℤ) (hP: ∀i ∈ S,WeightBound w (P i) a):
    WeightBound w (∑ i ∈ S,P i) a:=by
  classical
  induction S using Finset.induction_on with
  | empty=>exact Or.inl (by simp)
  | @insert i S hi ih=>
    rw [Finset.sum_insert hi]
    exact (hP i (Finset.mem_insert_self i S)).add
      (ih (fun j hj=>hP j (Finset.mem_insert_of_mem hj)))

def QJ (m i:ℕ) (f t:ℤ):ℤ:=
  (i:ℤ)*(2-t)+((min (2*i) m:ℕ):ℤ)*(f-2)

theorem APN (m i:ℕ) (f t:ℤ):
    QJ m i f t=
      (i:ℤ)*(2-t)+((m:ℤ)-sExponent m i)*(f-2):=by
  have he:((min (2*i) m:ℕ):ℤ)=(m:ℤ)-sExponent m i:=by
    unfold sExponent
    omega
  simp only [QJ,he]

theorem EDL (m i:ℕ) (f t:ℤ):
    QJ (m+1) i f t=QJ m i f t+
      ((sExponent m i+1-sExponent (m+1) i:ℕ):ℤ)*(f-2):=by
  have h:=FIQ m i
  rw [APN,APN]
  have he:((sExponent m i+1-sExponent (m+1) i:ℕ):ℤ)=
      (sExponent m i:ℤ)+1-sExponent (m+1) i:=by omega
  rw [he]
  push_cast
  ring

theorem BMG (m i:ℕ) (f t:ℤ):
    QJ (m+1) (i+1) f t=QJ m i f t+
      (f-t)+((sExponent m i-sExponent (m+1) (i+1):ℕ):ℤ)*(f-2):=by
  have h:=FSK m i
  rw [APN,APN]
  have he:((sExponent m i-sExponent (m+1) (i+1):ℕ):ℤ)=
      (sExponent m i:ℤ)-sExponent (m+1) (i+1):=by omega
  rw [he]
  push_cast
  ring

theorem BWI (m i:ℕ) (f t:ℤ):
    QJ (m+1) (i+2) f t=QJ m i f t+
      (f+2-2*t)+
      ((sExponent m i-sExponent (m+1) (i+2):ℕ):ℤ)*(f-2):=by
  have h:=FDC m i
  rw [APN,APN]
  have he:((sExponent m i-sExponent (m+1) (i+2):ℕ):ℤ)=
      (sExponent m i:ℤ)-sExponent (m+1) (i+2):=by omega
  rw [he]
  push_cast
  ring

theorem ASM (w:Fin 4→ℕ) (t:ℕ)
    (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t≤1)
    (F:Poly4) (f:ℤ) (hF:WeightBound w F f):
    WeightBound w (polyH K F) (f-1)∧
    WeightBound w (polyG K F) (f+1-t)∧
    WeightBound w (boundaryJ F) (f-2):=by
  have hH:WeightBound w (polyH K F) (f-1):=by
    simpa only [polyH,hR,Nat.cast_one] using hF.pderiv (2:Fin 4)
  refine ⟨hH,?_,?_⟩
  · simpa only [polyG,TR,Derivation.add_apply,
      Derivation.smul_apply,smul_eq_mul] using (hF.horizontal t hX hY hR ht).neg
  · have:=hH.pderiv (2:Fin 4)
    simpa only [boundaryJ,hR,Nat.cast_one,sub_sub,Int.reduceAdd] using this

theorem EBZ (w:Fin 4→ℕ) (t:ℕ)
    (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t≤1)
    (F P:Poly4) (f:ℤ) (hF:WeightBound w F f)
    (m i:ℕ) (hi:i≤m+1)
    (hP:WeightBound w P (QJ m i f t)):
    WeightBound w (COD F m i P) (QJ (m+1) i f t)∧
    WeightBound w (DEL F m i P) (QJ (m+1) (i+1) f t)∧
    WeightBound w (DEI F m i P) (QJ (m+1) (i+1) f t)∧
    WeightBound w (DTR F m i P) (QJ (m+1) (i+2) f t)∧
    WeightBound w (DSP F m i P) (QJ (m+1) (i+2) f t)∧
    (i=m+1→WeightBound w (DRR F P)
      (QJ (m+1) (i+1) f t)):=by
  obtain ⟨hH,hG,hJ⟩:=ASM w t hX hY hR ht F f hF
  have hDH:=hH.horizontal t hX hY hR ht
  have hDG:=hG.horizontal t hX hY hR ht
  have hDJ:=hJ.horizontal t hX hY hR ht
  have hDP:=hP.horizontal t hX hY hR ht
  have hGR:=hG.pderiv (2:Fin 4)
  have hJR:=hJ.pderiv (2:Fin 4)
  have hPR:=hP.pderiv (2:Fin 4)
  simp only [hR,Nat.cast_one] at hGR hJR hPR
  have hscalar:WeightBound w ((i:Poly4)-((2*m+1:ℕ):Poly4)) 0:=
    (WeightBound.natCast i).sub (WeightBound.natCast (2*m+1))
  have hb:WeightBound w (m+1-i:Poly4) 0:=by
    convert (WeightBound.natCast (w:=w) (K:=K) (m+1)).sub
      (WeightBound.natCast i) using 1<;>push_cast<;>ring
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · unfold COD
    rw [EDL]
    convert (hscalar.mul (ALV hJ _)).mul hP using 1<;>ring
  · unfold DEL
    rw [BMG]
    apply WeightBound.add
    · have hmid:WeightBound w
          (((i:Poly4)-((2*m+1:ℕ):Poly4))*dZero (polyH K F)+
            (m+1-i:Poly4)*MvPolynomial.pderiv (2:Fin 4) (polyG K F))
          (f-t):=by
        apply WeightBound.add
        · convert hscalar.mul hDH using 1<;>(try dsimp only [dZero])<;>ring
        · convert hb.mul hGR using 1<;>ring
      convert ((ALV hJ _).mul hmid).mul hP using 1<;>ring
    · convert (hG.mul (ALV hJ _)).mul hPR using 1<;>ring
  · unfold DEI
    split_ifs with hs
    · have he:((sExponent m i-1-sExponent (m+1) (i+1):ℕ):ℤ)+1=
          ((sExponent m i-sExponent (m+1) (i+1):ℕ):ℤ):=by
        have:=EHV m i hs
        omega
      rw [BMG]
      convert ((((WeightBound.natCast (w:=w) (K:=K) (sExponent m i)).mul hG).mul hJR).mul
        (ALV hJ _)).mul hP using 1
      nlinarith [congrArg (fun x:ℤ=>x*(f-2)) he]
    · exact Or.inl rfl
  · unfold DTR
    rw [BWI]
    apply WeightBound.add
    · convert ((ALV hJ (sExponent m i-sExponent (m+1) (i+2))).mul (hb.mul hDG)).mul hP using 1
        <;>(try dsimp only [dZero])<;>ring
    · convert (hG.mul (ALV hJ (sExponent m i-sExponent (m+1) (i+2)))).mul hDP using 1
        <;>(try dsimp only [dZero])<;>ring
  · unfold DSP
    split_ifs with hs
    · have he:((sExponent m i-1-sExponent (m+1) (i+2):ℕ):ℤ)+1=
          ((sExponent m i-sExponent (m+1) (i+2):ℕ):ℤ):=by
        have:=DUZ m i hs
        omega
      rw [BWI]
      convert ((((WeightBound.natCast (w:=w) (K:=K) (sExponent m i)).mul hG).mul hDJ).mul
        (ALV hJ _)).mul hP using 1
      · rfl
      · nlinarith [congrArg (fun x:ℤ=>x*(f-2)) he]
    · exact Or.inl rfl
  · intro htop
    have he:sExponent m i-sExponent (m+1) (i+1)=0:=by
      unfold sExponent
      omega
    rw [BMG,he]
    unfold DRR
    convert hH.mul hDP using 1<;>(try dsimp only [dZero])<;>push_cast<;>ring

theorem ASX (w:Fin 4→ℕ) (t:ℕ)
    (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t≤1)
    (F:Poly4) (f:ℤ) (hF:WeightBound w F f) (m i:ℕ):
    WeightBound w (RE F m i) (QJ m i f t):=by
  induction m generalizing i with
  | zero=>
    by_cases hi:i=0
    · subst i
      simpa only [RE,↓reduceIte,QJ,
        Nat.mul_zero,min_self,Nat.cast_zero,Nat.cast_one,zero_mul,zero_add] using
        (WeightBound.natCast (w:=w) (K:=K) 1)
    · exact Or.inl (by simp only [RE,if_neg hi])
  | succ m ih=>
    simp only [RE,ATP]
    apply ELJ
    intro j hj
    have hjm:j≤m+1:=by have:=Finset.mem_range.mp hj;omega
    obtain ⟨hA,hB,hC,hD,hE,htop⟩:=EBZ
      w t hX hY hR ht F (RE F m j) f hF m j hjm (ih j)
    by_cases hi0:i=j
    · simp only [if_pos hi0]
      simpa only [hi0] using hA
    · rw [if_neg hi0]
      by_cases hi1:i=j+1
      · rw [if_pos hi1,hi1]
        apply (hB.add hC).add
        split_ifs with he
        · exact htop he
        · exact Or.inl rfl
      · rw [if_neg hi1]
        split_ifs with he
        · rw [he.1]
          exact hD.add hE
        · exact Or.inl rfl

end
end JE
end MergedPart1

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace BoundaryTail

theorem FIA {n j a b c:ℤ}
    (hn:2≤n) (hj0:0≤j) (hjn:j≤n-1)
    (ha:0≤a) (hb:0≤b) (hc:0≤c) (hab:a-b≤2*c):
    2*(j*a+(n-1-j)*b+max (n-2-2*j) 0*c)≥
      2*(n-1)*a-n*max (a-b) 0:=by
  by_cases hpos:0≤n-2-2*j
  · rw [max_eq_left hpos]
    by_cases hd:0≤a-b
    · rw [max_eq_left hd]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hd)]
      nlinarith
  · rw [max_eq_right (le_of_not_ge hpos)]
    by_cases hd:0≤a-b
    · rw [max_eq_left hd]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hd)]
      nlinarith

theorem FLE {n j a b c:ℤ}
    (hn:2≤n) (hj0:1≤j) (hjn:j≤n-1)
    (hc:0≤c) (hgap:2*c<a-b):
    j*a+(n-1-j)*b+max (n-2-2*j) 0*c>
      (n-1)*b+(n-2)*c:=by
  by_cases hpos:0≤n-2-2*j
  · rw [max_eq_left hpos]
    nlinarith
  · rw [max_eq_right (le_of_not_ge hpos)]
    nlinarith

theorem FNL {u v p:ℤ}
    (hv:0≤v) (hvu:v≤u):
    max (max (2*u) (v+max p 0)-2*u) 0=
      max (p-(2*u-v)) 0:=by
  simp [max_def]
  omega

end BoundaryTail

end ProximityPrize.SubmissionLower
end
section
section MergedPart0
namespace ProximityPrize.SubmissionLower.BoundaryTail

open scoped BigOperators

noncomputable section

variable {L:Type*} [Field L]

local instance:DecidableEq L:=Classical.decEq L

def QT (n j:ℕ) (H G J C:L):L:=
  H^j*G^(n-1-j)*J^(n-2-2*j)*C

def DGC (n j:ℕ) (a b c:ℤ):ℤ:=
  (j:ℤ)*a+((n-1-j:ℕ):ℤ)*b+
    ((n-2-2*j:ℕ):ℤ)*c

theorem EYT {n j:ℕ} (hn:2≤n) (hj:j<n)
    (a b c:ℤ):
    DGC n j a b c=
      (j:ℤ)*a+((n:ℤ)-1-j)*b+
        max ((n:ℤ)-2-2*j) 0*c:=by
  have hsub:((n-1-j:ℕ):ℤ)=(n:ℤ)-1-j:=by omega
  have htail:((n-2-2*j:ℕ):ℤ)=
      max ((n:ℤ)-2-2*j) 0:=by omega
  simp only [DGC,hsub,htail]

theorem BVP
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    {n j:ℕ} (hn:2≤n) (hj:j<n)
    (H G J C:L) (h g q A B D:ℤ)
    (hH:v H≤WithZero.exp h) (hG:v G≤WithZero.exp g)
    (hJ:v J≤WithZero.exp q)
    (hC:v C≤WithZero.exp
      ((j:ℤ)*(B-A)+((min (2*j) (n-2):ℕ):ℤ)*D)):
    v (QT n j H G J C)≤WithZero.exp
      (((n-1:ℕ):ℤ)*B+((n-2:ℕ):ℤ)*D-
        DGC n j (A-h) (B-g) (D-q)):=by
  have hpow (x:L) (e:ℤ) (hx:v x≤WithZero.exp e) (k:ℕ):
      v x^k≤WithZero.exp ((k:ℤ)*e):=by
    rw [← nsmul_eq_mul,WithZero.exp_nsmul]
    exact pow_le_pow_left₀ zero_le hx k
  have hsub:((n-1-j:ℕ):ℤ)+j=((n-1:ℕ):ℤ):=by omega
  have hmin:((n-2-2*j:ℕ):ℤ)+
      ((min (2*j) (n-2):ℕ):ℤ)=((n-2:ℕ):ℤ):=by omega
  unfold QT
  simp only [map_mul,map_pow]
  calc
    _≤WithZero.exp ((j:ℤ)*h)*
        WithZero.exp (((n-1-j:ℕ):ℤ)*g)*
        WithZero.exp (((n-2-2*j:ℕ):ℤ)*q)*
        WithZero.exp ((j:ℤ)*(B-A)+
          ((min (2*j) (n-2):ℕ):ℤ)*D):=
      mul_le_mul' (mul_le_mul' (mul_le_mul' (hpow H h hH j)
        (hpow G g hG (n-1-j))) (hpow J q hJ (n-2-2*j))) hC
    _=_:=by
      rw [← WithZero.exp_add,← WithZero.exp_add,← WithZero.exp_add]
      congr 1
      unfold DGC
      nlinarith [congrArg (fun t:ℤ=>t*B) hsub,
        congrArg (fun t:ℤ=>t*D) hmin]

theorem EIK
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    {n j:ℕ} (hn:2≤n) (hj:j<n)
    (H G J C:L) (hH:H ≠ 0) (hG:G ≠ 0) (hJ:J ≠ 0)
    (A B D:ℤ)
    (hC:v C≤WithZero.exp
      ((j:ℤ)*(B-A)+((min (2*j) (n-2):ℕ):ℤ)*D)):
    v (QT n j H G J C)≤WithZero.exp
      (((n-1:ℕ):ℤ)*B+((n-2:ℕ):ℤ)*D-
        DGC n j (A-(v H).log) (B-(v G).log) (D-(v J).log)):=
  BVP v hn hj H G J C _ _ _ A B D
    (WithZero.le_exp_of_log_le (le_refl _))
    (WithZero.le_exp_of_log_le (le_refl _))
    (WithZero.le_exp_of_log_le (le_refl _)) hC

theorem CKP
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    {ι:Type*} [Fintype ι] [DecidableEq ι] (T:ι→L) (i:ι)
    (hi:T i ≠ 0) (hsum: ∑ j,T j=0):
    ¬(∀j,j ≠ i→v (T j)<v (T i)):=by
  intro hlt
  have hsmall:v (∑ j ∈ Finset.univ.erase i,T j)<v (T i):=by
    apply v.map_sum_lt (by simpa using hi)
    intro j hj
    exact hlt j (Finset.mem_erase.mp hj).1
  have hsplit:(∑ j ∈ Finset.univ.erase i,T j)+T i=0:=by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact hsum
  have hneg:(∑ j ∈ Finset.univ.erase i,T j)= -T i:=
    eq_neg_of_add_eq_zero_left hsplit
  rw [hneg,v.map_neg] at hsmall
  exact lt_irrefl _ hsmall

theorem DUC
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    {n:ℕ} (hn:2≤n) (H G J:L)
    (hH:H ≠ 0) (hG:G ≠ 0) (hJ:J ≠ 0)
    (C:Fin n→L) (A B D:ℤ)
    (hD:(v J).log≤D)
    (hC: ∀j,v (C j)≤WithZero.exp
      ((j.val:ℤ)*(B-A)+((min (2*j.val) (n-2):ℕ):ℤ)*D))
    (hlead:v (C ⟨0,by omega⟩)=1)
    (hzero: ∑ j,QT n j.val H G J (C j)=0):
    (A-(v H).log)-(B-(v G).log)≤2*(D-(v J).log):=by
  classical
  by_contra hgap
  let i:Fin n:=⟨0,by omega⟩
  let T:Fin n→L:=fun j=>QT n j.val H G J (C j)
  let P:ℤ:=((n-1:ℕ):ℤ)*B+((n-2:ℕ):ℤ)*D
  let a:=A-(v H).log
  let b:=B-(v G).log
  let c:=D-(v J).log
  have hleadval:v (T i)=WithZero.exp
      (P-(((n-1:ℕ):ℤ)*b+((n-2:ℕ):ℤ)*c)):=by
    have hGv:v G ≠ 0:=(Valuation.ne_zero_iff v).mpr hG
    have hJv:v J ≠ 0:=(Valuation.ne_zero_iff v).mpr hJ
    simp only [T,i,QT,pow_zero,one_mul,Nat.sub_zero,
      Nat.mul_zero,map_mul,map_pow,hlead,mul_one]
    rw [← WithZero.exp_log (pow_ne_zero (n-1) hGv),
      ← WithZero.exp_log (pow_ne_zero (n-2) hJv),← WithZero.exp_add]
    congr 1
    simp only [WithZero.log_pow,nsmul_eq_mul,P,b,c]
    ring
  have hi:T i ≠ 0:=by
    intro hz
    have:=hleadval
    rw [hz,map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  apply CKP v T i hi hzero
  intro j hji
  have hjpos:1≤(j.val:ℤ):=by
    have:j.val ≠ 0:=by
      intro hz
      apply hji
      exact Fin.ext hz
    omega
  have hsep:=FLE
    (n:=(n:ℤ)) (j:=(j.val:ℤ)) (a:=a) (b:=b) (c:=c)
    (by omega) hjpos (by omega) (by dsimp [c];omega) (by exact lt_of_not_ge hgap)
  have hvalue:=EIK v hn j.isLt H G J (C j)
    hH hG hJ A B D (hC j)
  change v (T j)≤WithZero.exp (P-DGC n j.val a b c) at hvalue
  apply lt_of_le_of_lt hvalue
  rw [hleadval]
  apply WithZero.exp_lt_exp.mpr
  rw [EYT hn j.isLt]
  have hsub1:((n-1:ℕ):ℤ)=(n:ℤ)-1:=by omega
  have hsub2:((n-2:ℕ):ℤ)=(n:ℤ)-2:=by omega
  rw [hsub1,hsub2]
  linarith

theorem ERV
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    {n:ℕ} (hn:2≤n) (H G J:L)
    (C:Fin n→L) (h g q A B D:ℤ)
    (hH:v H≤WithZero.exp h) (hG:v G≤WithZero.exp g)
    (hJ:v J≤WithZero.exp q)
    (hA:h≤A) (hB:g≤B) (hD:q≤D)
    (hgap:(A-h)-(B-g)≤2*(D-q))
    (hC: ∀j,v (C j)≤WithZero.exp
      ((j.val:ℤ)*(B-A)+((min (2*j.val) (n-2):ℕ):ℤ)*D)):
    v (∑ j,QT n j.val H G J (C j))≤WithZero.exp
      ((2*(((n-1:ℕ):ℤ)*B+((n-2:ℕ):ℤ)*D)-
          2*((n-1:ℕ):ℤ)*(A-h)+
          (n:ℤ)*max ((A-h)-(B-g)) 0)/2):=by
  apply v.map_sum_le
  intro j _
  apply le_trans (BVP v hn j.isLt H G J (C j)
    h g q A B D hH hG hJ (hC j))
  apply WithZero.exp_le_exp.mpr
  apply (Int.le_ediv_iff_mul_le (by decide:(0:ℤ)<2)).mpr
  have hweight:=FIA
    (n:=(n:ℤ)) (j:=(j.val:ℤ))
    (a:=A-h) (b:=B-g) (c:=D-q)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hgap
  rw [EYT hn j.isLt]
  have hsub:((n-1:ℕ):ℤ)=(n:ℤ)-1:=by omega
  rw [hsub]
  nlinarith

theorem ECH
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (H G J:L) (A B D:ℤ) (hH:H ≠ 0) (hAB:A≤B)
    (hA:(v H).log≤A)
    (hB:G ≠ 0→(v G).log≤B) (hD:J ≠ 0→(v J).log≤D)
    (hfirst:G ≠ 0→J ≠ 0→
      (A-(v H).log)-(B-(v G).log)≤2*(D-(v J).log)):
    ∃g q:ℤ,
      v G≤WithZero.exp g∧v J≤WithZero.exp q∧
      g≤B∧q≤D∧
      (A-(v H).log)-(B-g)≤2*(D-q)∧
      max ((A-(v H).log)-(B-g)) 0=
        max (max (v (G/H)).log 0-(B-A)) 0:=by
  have hHv:v H ≠ 0:=(Valuation.ne_zero_iff v).mpr hH
  have hJchoice (g:ℤ)
      (hg:J ≠ 0→(A-(v H).log)-(B-g)≤2*(D-(v J).log)):
      ∃q:ℤ,v J≤WithZero.exp q∧q≤D∧
        (A-(v H).log)-(B-g)≤2*(D-q):=by
    by_cases hz:J=0
    · refine ⟨D-max ((A-(v H).log)-(B-g)) 0,?_,?_,?_⟩
      · simp only [hz,map_zero];exact zero_le
      · omega
      · omega
    · exact ⟨(v J).log,WithZero.le_exp_of_log_le (le_refl _),hD hz,hg hz⟩
  by_cases hG:G=0
  · obtain ⟨q,hqv,hqD,hq⟩:=hJchoice ((v H).log+B-A) (by
      intro hJ
      have:=hD hJ
      omega)
    refine ⟨(v H).log+B-A,q,?_,hqv,?_,hqD,hq,?_⟩
    · simp only [hG,map_zero];exact zero_le
    · omega
    · simp only [hG,zero_div,map_zero,WithZero.log_zero]
      omega
  · obtain ⟨q,hqv,hqD,hq⟩:=hJchoice (v G).log (hfirst hG)
    refine ⟨(v G).log,q,WithZero.le_exp_of_log_le (le_refl _),
      hqv,hB hG,hqD,hq,?_⟩
    have hGv:v G ≠ 0:=(Valuation.ne_zero_iff v).mpr hG
    rw [map_div₀,WithZero.log_div hGv hHv]
    omega

theorem ETA
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    {n:ℕ} (hn:2≤n) (H G J:L) (hH:H ≠ 0)
    (C:Fin n→L) (A u t:ℤ) (ht:0≤t) (htu:t≤u) (huA:u≤A)
    (hA:(v H).log≤A)
    (hB:G ≠ 0→(v G).log≤A+2*u-t)
    (hD:J ≠ 0→(v J).log≤A-u)
    (hfirst:G ≠ 0→J ≠ 0→
      (A-(v H).log)-(A+2*u-t-(v G).log)≤
        2*(A-u-(v J).log))
    (hC: ∀j,v (C j)≤WithZero.exp
      ((j.val:ℤ)*(2*u-t)+
        ((min (2*j.val) (n-2):ℕ):ℤ)*(A-u))):
    2*max (v (H^3*(∑ j,QT n j.val H G J (C j))/
      H^(n-1))).log 0≤
      2*(((n:ℤ)+1)*A-((n:ℤ)-1)*t)+
        (n:ℤ)*max (2*u) (t+max (v (G/H)).log 0):=by
  let T:= ∑ j,QT n j.val H G J (C j)
  let theta:=max (2*u) (t+max (v (G/H)).log 0)
  have htheta0:0≤theta:=by dsimp [theta];omega
  have hnormal0:0≤((n:ℤ)+1)*A-((n:ℤ)-1)*t:=by
    have hprod:=mul_nonneg (show 0≤(n:ℤ)-1 by omega)
      (show 0≤A-t by omega)
    nlinarith
  have hright0:0≤2*(((n:ℤ)+1)*A-((n:ℤ)-1)*t)+
      (n:ℤ)*theta:=by positivity
  change 2*max (v (H^3*T/H^(n-1))).log 0≤_
  by_cases hT:T=0
  · simpa only [hT,mul_zero,zero_div,map_zero,WithZero.log_zero,
      max_self,mul_zero] using hright0
  obtain ⟨g,q,hg,hq,hgB,hqD,hgap,hr⟩:=ECH
    v H G J A (A+2*u-t) (A-u) hH (by omega) hA hB hD hfirst
  have hc' : ∀j,v (C j)≤WithZero.exp
      ((j.val:ℤ)*((A+2*u-t)-A)+
        ((min (2*j.val) (n-2):ℕ):ℤ)*(A-u)):=by
    convert hC using 1<;>ring
  have hvalue:=ERV v hn H G J C (v H).log g q
    A (A+2*u-t) (A-u)
    (WithZero.le_exp_of_log_le (le_refl _)) hg hq hA hgB hqD hgap hc'
  let Q:ℤ:=2*(((n-1:ℕ):ℤ)*(A+2*u-t)+
      ((n-2:ℕ):ℤ)*(A-u))-
      2*((n-1:ℕ):ℤ)*(A-(v H).log)+
      (n:ℤ)*max ((A-(v H).log)-(A+2*u-t-g)) 0
  change v T≤WithZero.exp (Q/2) at hvalue
  have hTv:v T ≠ 0:=(Valuation.ne_zero_iff v).mpr hT
  have hlog:(v T).log≤Q/2:=by
    simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hTv WithZero.exp_ne_zero).mpr hvalue
  have htwolog:2*(v T).log≤Q:=by omega
  have htheta:=FNL (u:=u) (v:=t) (p:=(v (G/H)).log) ht htu
  have htheta_ge:0≤theta-2*u:=by dsimp [theta];omega
  change max (theta-2*u) 0=_ at htheta
  rw [max_eq_left htheta_ge] at htheta
  have hdelta:max ((A-(v H).log)-(A+2*u-t-g)) 0=theta-2*u:=by
    rw [hr,htheta]
    omega
  have hHv:v H ≠ 0:=(Valuation.ne_zero_iff v).mpr hH
  have hlogcut:(v (H^3*T/H^(n-1))).log=
      (4-(n:ℤ))*(v H).log+(v T).log:=by
    rw [map_div₀,map_mul,map_pow,map_pow,
      WithZero.log_div (mul_ne_zero (pow_ne_zero 3 hHv) hTv) (pow_ne_zero _ hHv),
      WithZero.log_mul (pow_ne_zero 3 hHv) hTv]
    simp only [WithZero.log_pow,nsmul_eq_mul,Nat.cast_ofNat]
    have hsub:((n-1:ℕ):ℤ)=(n:ℤ)-1:=by omega
    rw [hsub]
    ring
  rw [hlogcut]
  by_cases hnonneg:0≤(4-(n:ℤ))*(v H).log+(v T).log
  · rw [max_eq_left hnonneg]
    dsimp [Q] at htwolog
    rw [hdelta] at htwolog
    have hsub1:((n-1:ℕ):ℤ)=(n:ℤ)-1:=by omega
    have hsub2:((n-2:ℕ):ℤ)=(n:ℤ)-2:=by omega
    rw [hsub1,hsub2] at htwolog
    nlinarith
  · rw [max_eq_right (by omega),mul_zero]
    exact hright0

end

end ProximityPrize.SubmissionLower.BoundaryTail
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.JE

open RCN055 RCN057 RCN095 RCN136 RCN156 RCN234 RCN313

noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]

def LJ (m i r v z:ℕ):FlagDegree:=
  ⟨min (2*i) m*z,min (2*i) m*v-i,
    2*i+min (2*i) m*(r-2)⟩

theorem CYZ {m i v:ℕ}
    (hm:1≤m) (hi:i≤m+1) (hv:2≤v):i≤min (2*i) m*v:=by
  have h:i≤2*min (2*i) m:=by
    by_cases hh:2*i≤m
    · rw [min_eq_left hh];omega
    · rw [min_eq_right (by omega)];omega
  have:=Nat.mul_le_mul_left (min (2*i) m) hv
  omega

theorem BJH {m i r v:ℕ} (z:ℕ)
    (hm:1≤m) (hi:i≤m+1) (hr:2≤r) (hv:2≤v):
    ((LJ m i r v z).all:ℤ)=QJ m i r 0∧
    (((LJ m i r v z).yz+(LJ m i r v z).all:ℕ):ℤ)=
      QJ m i (r+v) 1∧
    (((LJ m i r v z).zOnly+(LJ m i r v z).yz+
      (LJ m i r v z).all:ℕ):ℤ)=QJ m i (r+v+z) 1:=by
  have hsafe:=CYZ hm hi hv
  simp only [LJ,QJ,Nat.cast_add,Nat.cast_mul,
    Nat.cast_sub hr,Nat.cast_sub hsafe,Nat.cast_ofNat]
  constructor
  · ring
  constructor<;>ring

theorem EKC {w:Fin 4→ℕ} {P:MvPolynomial (Fin 4) K} {a:ℕ}
    (h:WeightBound w P (a:ℤ)):wt w P≤a:=by
  rcases h with rfl | h
  · simp [wt,MvPolynomial.weightedTotalDegree]
  · exact_mod_cast h

theorem AOL (φ:Polynomial K→+*Ω)
    (P:MvPolynomial (Fin 4) K) (p:FlagDegree)
    (hR:WeightBound BE P (p.all:ℤ))
    (hYR:WeightBound BC P ((p.yz+p.all:ℕ):ℤ))
    (hAll:WeightBound AT P ((p.zOnly+p.yz+p.all:ℕ):ℤ)):
    BI p (surfaceMap φ P):=by
  intro e he
  obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (VO φ P he)
  have hr:=(MvPolynomial.le_weightedTotalDegree BE hd).trans (EKC hR)
  have hm:=(MvPolynomial.le_weightedTotalDegree BC hd).trans (EKC hYR)
  have ht:=(MvPolynomial.le_weightedTotalDegree AT hd).trans (EKC hAll)
  simp [RCN081.weight_fin4,BE] at hr
  simp [RCN081.weight_fin4,BC] at hm
  simp [RCN081.weight_fin4,AT] at ht
  exact ⟨hr,hm,ht⟩

theorem CUX (φ:Polynomial K→+*Ω)
    (F:MvPolynomial (Fin 4) K) (m i r v z:ℕ)
    (hm:1≤m) (hi:i≤m+1) (hr:2≤r) (hv:2≤v)
    (hR:WeightBound BE F (r:ℤ))
    (hYR:WeightBound BC F ((r+v:ℕ):ℤ))
    (hAll:WeightBound AT F ((r+v+z:ℕ):ℤ)):
    BI (LJ m i r v z) (surfaceMap φ (RE F m i)):=by
  obtain ⟨hcR,hcYR,hcAll⟩:=BJH z hm hi hr hv
  apply AOL
  · rw [hcR]
    exact ASX BE 0 rfl rfl rfl (by omega) F _ hR m i
  · rw [hcYR]
    convert ASX BC 1 rfl rfl rfl (by omega)
      F _ hYR m i using 1<;>push_cast<;>rfl
  · rw [hcAll]
    convert ASX AT 1 rfl rfl rfl (by omega)
      F _ hAll m i using 1<;>push_cast<;>rfl

theorem BNS (φ:Polynomial K→+*Ω)
    (F:MvPolynomial (Fin 4) K) (r v z:ℕ) (hr:2≤r) (hv:1≤v)
    (hR:WeightBound BE F (r:ℤ))
    (hYR:WeightBound BC F ((r+v:ℕ):ℤ))
    (hAll:WeightBound AT F ((r+v+z:ℕ):ℤ)):
    BI ⟨z,v,r-1⟩ (surfaceMap φ (polyH K F))∧
    BI ⟨z,v-1,r+1⟩ (surfaceMap φ (polyG K F))∧
    BI ⟨z,v,r-2⟩ (surfaceMap φ (boundaryJ F)):=by
  have hR' :=ASM BE 0 rfl rfl rfl (by omega) F _ hR
  have hYR' :=ASM BC 1 rfl rfl rfl (by omega) F _ hYR
  have hAll' :=ASM AT 1 rfl rfl rfl (by omega) F _ hAll
  have hr1:1≤r:=by omega
  refine ⟨?_,?_,?_⟩
  · apply AOL
    · convert hR'.1 using 1<;>simp only [Nat.cast_sub hr1,Nat.cast_one]
    · convert hYR'.1 using 1<;>simp only [Nat.cast_add,Nat.cast_sub hr1,Nat.cast_one]<;>ring
    · convert hAll'.1 using 1<;>simp only [Nat.cast_add,Nat.cast_sub hr1,Nat.cast_one]<;>ring
  · apply AOL
    · convert hR'.2.1 using 1<;>simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,sub_zero]
    · convert hYR'.2.1 using 1<;>simp only [Nat.cast_add,Nat.cast_sub hv,Nat.cast_one]<;>ring
    · convert hAll'.2.1 using 1<;>simp only [Nat.cast_add,Nat.cast_sub hv,Nat.cast_one]<;>ring
  · apply AOL
    · convert hR'.2.2 using 1<;>simp only [Nat.cast_sub hr,Nat.cast_ofNat]
    · convert hYR'.2.2 using 1<;>simp only [Nat.cast_add,Nat.cast_sub hr,Nat.cast_ofNat]<;>ring
    · convert hAll'.2.2 using 1<;>simp only [Nat.cast_add,Nat.cast_sub hr,Nat.cast_ofNat]<;>ring

theorem FDK {L:Type*} [Field L]
    (V:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3→L)
    (m i r v z:ℕ) (hm:1≤m) (hi:i≤m+1) (hv:2≤v):
    RCN204.flagPole V x (LJ m i r v z)=
      (i:ℤ)*(2*RCN204.flagPole V x unitAllFlag-RCN204.flagPole V x unitYZFlag)+
      ((min (2*i) m:ℕ):ℤ)*RCN204.flagPole V x (⟨z,v,r-2⟩:FlagDegree):=by
  have hsafe:=CYZ hm hi hv
  simp only [RCN204.flagPole,LJ,unitAllFlag,unitYZFlag,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,Nat.cast_sub hsafe]
  ring

theorem DWT {L:Type*} [Field L]
    (V:Valuation L (WithZero (Multiplicative ℤ)))
    (coeff:Ω→+*L) (hcoeff: ∀a,V (coeff a)≤1) (x:Fin 3→L)
    (φ:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K) (m i r v z:ℕ)
    (hm:1≤m) (hi:i≤m+1) (hr:2≤r) (hv:2≤v)
    (hR:WeightBound BE F (r:ℤ))
    (hYR:WeightBound BC F ((r+v:ℕ):ℤ))
    (hAll:WeightBound AT F ((r+v+z:ℕ):ℤ)):
    V (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (RE F m i)))≤
      WithZero.exp ((i:ℤ)*(2*RCN204.flagPole V x unitAllFlag-
        RCN204.flagPole V x unitYZFlag)+((min (2*i) m:ℕ):ℤ)*
        RCN204.flagPole V x (⟨z,v,r-2⟩:FlagDegree)):=by
  rw [← FDK V x m i r v z hm hi hv]
  exact RCN204.ADJ V coeff hcoeff x _ _
    (CUX φ F m i r v z hm hi hr hv hR hYR hAll)

end
end ProximityPrize.SubmissionLower.JE
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.JE

open RCN055 RCN056 RCN313
open scoped BigOperators

noncomputable section
variable {K:Type*} [CommRing K]
local notation "Poly4" =>MvPolynomial (Fin 4) K

theorem EZZ (F P:Poly4) (m i:ℕ) (hi:i≤m+1):
    baseStep F m (QT F m i P)=
      QT F (m+1) i (COD F m i P)+
      QT F (m+1) (i+1)
        (DEL F m i P+DEI F m i P+
          if i=m+1 then DRR F P else 0)+
      if i≤m then QT F (m+1) (i+2)
        (DTR F m i P+DSP F m i P) else 0:=by
  simp only [baseStep,QT]
  rw [EVT]
  by_cases htop:i=m+1
  · subst i
    have hs0:sExponent m (m+1)=0:=by unfold sExponent;omega
    have hs1:sExponent (m+1) (m+1)=0:=by unfold sExponent;omega
    have hs2:sExponent (m+1) (m+1+1)=0:=by unfold sExponent;omega
    have hGexp:m+1+1-(m+1)=1:=by omega
    simp only [COD,DEL,DEI,DRR,
      hs0,hs1,hs2,hGexp,Nat.lt_irrefl,if_false,Nat.le_add_left,if_true,
      show¬m+1≤m by omega,↓reduceIte]
    simp only [Nat.add_sub_cancel,Nat.sub_self,Nat.zero_sub,Nat.zero_add,
      Nat.sub_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
      Nat.cast_zero,pow_zero,pow_succ,zero_mul,mul_zero,one_mul,mul_one,
      dZero]
    ring
  · have him:i≤m:=by omega
    have hb0:m+1+1-i=(m+1-i)+1:=by omega
    have hb1:m+1+1-(i+1)=m+1-i:=by omega
    have hb2:m+1+1-(i+2)=m-i:=by omega
    have hb3:m+1-i=(m-i)+1:=by omega
    have hcast:(m+1-i:Poly4)=((m+1-i:ℕ):Poly4):=by
      rw [Nat.cast_sub hi,Nat.cast_add,Nat.cast_one]
    simp only [if_neg htop,if_pos him,COD,DEL,
      DEI,DTR,DSP,hb0,hb1,hb2,hb3,hcast]
    by_cases hs:2*i≤m
    · obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hs
      have he0:sExponent (2*i+d) i=d:=by unfold sExponent;omega
      have he1:sExponent (2*i+d+1) i=d+1:=by unfold sExponent;omega
      have he2:sExponent (2*i+d+1) (i+1)=d-1:=by unfold sExponent;omega
      have he3:sExponent (2*i+d+1) (i+2)=d-3:=by unfold sExponent;omega
      have he4:2*i+d-i=i+d:=by omega
      simp only [he0,he1,he2,he3,he4]
      by_cases hd:d<3
      · interval_cases d<;>
          norm_num [pow_add,pow_succ,dZero]<;>ring
      · obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le (show 3≤d by omega)
        have h1:3+s-1=s+2:=by omega
        have h3:3+s-3=s:=by omega
        have h4:3+s-(s+2)=1:=by omega
        have h5:3+s-1-(s+2)=0:=by omega
        have h6:3+s-1-s=2:=by omega
        simp only [h1,h3,h4,h5,h6,show 0<3+s by omega,if_true]
        norm_num [pow_add,pow_succ,dZero]<;>ring
    · have he0:sExponent m i=0:=by unfold sExponent;omega
      have he1:sExponent (m+1) i=0:=by unfold sExponent;omega
      have he2:sExponent (m+1) (i+1)=0:=by unfold sExponent;omega
      have he3:sExponent (m+1) (i+2)=0:=by unfold sExponent;omega
      simp only [he0,he1,he2,he3]
      norm_num [pow_add,pow_succ,dZero]<;>ring

end
end ProximityPrize.SubmissionLower.JE
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.JE

open RCN055 RCN056 RCN313
open scoped BigOperators

noncomputable section
variable {K:Type*} [CommRing K]
local notation "Poly4" =>MvPolynomial (Fin 4) K

theorem EQY (m i q:ℕ) (A B D:Poly4):
    (if q=i then A else if q=i+1 then B else if q=i+2∧i≤m then D else 0)=
      (if q=i then A else 0)+(if q=i+1 then B else 0)+
        (if q=i+2∧i≤m then D else 0):=by
  split_ifs<;>simp_all<;>omega

theorem DFV (F:Poly4) (m:ℕ) (C:ℕ→Poly4):
    baseStep F m (∑ i ∈ Finset.range (m+2),QT F m i (C i))=
      ∑ q ∈ Finset.range (m+3),
        QT F (m+1) q (ATP F m C q):=by
  rw [baseStep_sum]
  conv_rhs=>
    simp only [ATP,EQY,
      QT,Finset.mul_sum,mul_add,mul_ite,mul_zero,
      Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have him:i≤m+1:=by have:=Finset.mem_range.mp hi;omega
  rw [EZZ F (C i) m i him]
  have hi0:i ∈ Finset.range (m+3):=by simp only [Finset.mem_range];omega
  have hi1:i+1 ∈ Finset.range (m+3):=by simp only [Finset.mem_range];omega
  simp only [Finset.sum_add_distrib]
  by_cases hi2:i≤m
  · have hi2mem:i+2 ∈ Finset.range (m+3):=by simp only [Finset.mem_range];omega
    simp [hi2,hi0,hi1,hi2mem,QT,mul_add]
  · simp [hi2,hi0,hi1,QT,mul_add]

theorem ELV (F:Poly4) (m:ℕ):
    MN F m=
      ∑ i ∈ Finset.range (m+2),QT F m i (RE F m i):=by
  induction m with
  | zero=>simp [MN,QT,RE,sExponent]
  | succ m ih=>
    change baseStep F m (MN F m)=_
    rw [ih,DFV]
    rfl

end
end ProximityPrize.SubmissionLower.JE
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.CBN

open JE RCN055 RCN313
variable {K:Type*} [Field K]
local notation "Poly4" =>MvPolynomial (Fin 4) K
noncomputable section

def BBU:ℕ→K
  | 0=>1
  | m+1=> -(2*m+1:K)*BBU m

@[simp] theorem signedOddScalar_zero:BBU (K:=K) 0=1:=rfl

@[simp] theorem FHD (m:ℕ):
    BBU (K:=K) (m+1)= -(2*m+1:K)*BBU m:=by
  rfl

theorem ETY {p:ℕ} [CharP K p] (m:ℕ)
    (hm:2*m<p):BBU (K:=K) m ≠ 0:=by
  induction m with
  | zero=>simp [BBU]
  | succ m ih=>
      rw [FHD]
      apply mul_ne_zero
      · apply neg_ne_zero.mpr
        intro hz
        have hdvd:p ∣ 2*m+1:=
          (CharP.cast_eq_zero_iff K p (2*m+1)).mp (by
            simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
              Nat.cast_one] using hz)
        exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
      · apply ih
        omega

theorem EOK (F:Poly4) (m:ℕ):
    RE F m 0=MvPolynomial.C (BBU (K:=K) m):=by
  induction m with
  | zero=>simp [RE]
  | succ m ih=>
      have hC2:MvPolynomial.C (2:K)=(2:Poly4):=
        map_natCast (MvPolynomial.C:K→+*Poly4) 2
      simp [RE,ATP,ih,BBU,
        COD,sExponent,Nat.cast_add,Nat.cast_mul,hC2]

end
end ProximityPrize.SubmissionLower.CBN
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.JE

open RCN055 RCN057 RCN095 RCN136 RCN156 RCN204 RCN234 RCN313
open CBN
open scoped BigOperators

noncomputable section
variable {K Ω L:Type} [Field K] [Field Ω] [Field L]

theorem CTZ (ev:MvPolynomial (Fin 4) K→+*L)
    (F:MvPolynomial (Fin 4) K) (m:ℕ):
    ev (MN F m)=
      ∑ i:Fin (m+2),BoundaryTail.QT (m+2) i.val
        (ev (polyH K F)) (ev (polyG K F)) (ev (boundaryJ F))
        (ev (RE F m i.val)):=by
  rw [ELV,map_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [QT,map_mul,map_pow,BoundaryTail.QT,
    sExponent,Nat.max_zero,show m+2-1=m+1 by omega,
    show m+2-2=m by omega]

theorem FIR (V:Valuation L (WithZero (Multiplicative ℤ)))
    (x:Fin 3→L) (r v z:ℕ) (hr:3≤r) (hv:1≤v):
    let A:=flagPole V x (⟨z,v,r-1⟩:FlagDegree)
    let u:=flagPole V x unitAllFlag
    let t:=flagPole V x unitYZFlag
    0≤t∧t≤u∧u≤A∧
      flagPole V x (⟨z,v,r-2⟩:FlagDegree)=A-u∧
      flagPole V x (⟨z,v-1,r+1⟩:FlagDegree)=A+2*u-t:=by
  dsimp
  have hr1:1≤r:=by omega
  have hr2:2≤r:=by omega
  have hu0:=ALZ V x unitAllFlag
  have ht0:=ALZ V x unitYZFlag
  have hz0:0≤RCN187.poleOrder V (x 2):=le_max_left _ _
  simp only [flagPole,unitAllFlag,unitYZFlag,Nat.cast_add,Nat.cast_sub hr1,
    Nat.cast_sub hr2,Nat.cast_sub hv,Nat.cast_one,Nat.cast_zero,Nat.cast_ofNat,
    zero_mul,one_mul,zero_add,add_zero] at*
  refine ⟨ht0,le_max_right _ _,?_,?_,?_⟩
  · have:=mul_nonneg (show 0≤(r:ℤ)-2 by omega) hu0
    have:=mul_nonneg (show 0≤(v:ℤ) by omega) ht0
    have:=mul_nonneg (show 0≤(z:ℤ) by omega) hz0
    nlinarith
  · ring
  · ring

theorem DPJ
    (V:Valuation L (WithZero (Multiplicative ℤ)))
    (coeff:Ω→+*L) (hcoeff: ∀a:Ω,a ≠ 0→V (coeff a)=1)
    (x:Fin 3→L) (φ:Polynomial K→+*Ω)
    (F:MvPolynomial (Fin 4) K) (m₀ m r v z p:ℕ) [CharP K p]
    (hm₀:1≤m₀) (hm:1≤m) (hchar:2*m₀<p)
    (hr:3≤r) (hv:2≤v)
    (hR:WeightBound BE F (r:ℤ))
    (hYR:WeightBound BC F ((r+v:ℕ):ℤ))
    (hAll:WeightBound AT F ((r+v+z:ℕ):ℤ))
    (hH:MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)) ≠ 0)
    (hfirst:MvPolynomial.eval₂Hom coeff x (surfaceMap φ (MN F m₀))=0):
    let ev:=(MvPolynomial.eval₂Hom coeff x).comp (surfaceMap φ)
    let A:=flagPole V x (⟨z,v,r-1⟩:FlagDegree)
    let t:=flagPole V x unitYZFlag
    let u:=flagPole V x unitAllFlag
    2*max (V (ev (polyH K F)^3*ev (MN F m)/
      ev (polyH K F)^(m+1))).log 0≤
      2*(((m:ℤ)+3)*A-((m:ℤ)+1)*t)+
        ((m:ℤ)+2)*max (2*u) (t+max (V (ev (polyG K F)/ev (polyH K F))).log 0):=by
  classical
  let ev:=(MvPolynomial.eval₂Hom coeff x).comp (surfaceMap φ)
  let H:=ev (polyH K F)
  let G:=ev (polyG K F)
  let J:=ev (boundaryJ F)
  let A:=flagPole V x (⟨z,v,r-1⟩:FlagDegree)
  let u:=flagPole V x unitAllFlag
  let t:=flagPole V x unitYZFlag
  have hc: ∀a:Ω,V (coeff a)≤1:=by
    intro a
    letI:Decidable (a=0):=Classical.propDecidable _
    by_cases ha:a=0
    · simp [ha]
    · rw [hcoeff a ha]
  obtain ⟨ht0,htu,huA,hJcap,hGcap⟩:=FIR V x r v z hr (by omega)
  obtain ⟨hHF,hGF,hJF⟩:=BNS φ F r v z (by omega) (by omega) hR hYR hAll
  have log_cap (P:MvPolynomial (Fin 3) Ω) (cap:FlagDegree)
      (hP:BI cap P) (hne:MvPolynomial.eval₂Hom coeff x P ≠ 0):
      (V (MvPolynomial.eval₂Hom coeff x P)).log≤flagPole V x cap:=by
    have hh:=ADJ V coeff hc x cap P hP
    simpa only [WithZero.log_exp] using
      (WithZero.log_le_log ((Valuation.ne_zero_iff V).mpr hne) WithZero.exp_ne_zero).mpr hh
  have hA:(V H).log≤A:=log_cap _ _ hHF hH
  have hB:G ≠ 0→(V G).log≤A+2*u-t:=by
    intro hn
    rw [← hGcap]
    exact log_cap _ _ hGF hn
  have hD:J ≠ 0→(V J).log≤A-u:=by
    intro hn
    rw [← hJcap]
    exact log_cap _ _ hJF hn
  have hcoeffs (k:ℕ) (hk:1≤k) (i:Fin (k+2)):
      V (ev (RE F k i.val))≤WithZero.exp
        ((i.val:ℤ)*(2*u-t)+
          ((min (2*i.val) k:ℕ):ℤ)*(A-u)):=by
    rw [← hJcap]
    exact DWT V coeff hc x φ F k i.val r v z hk
      (by omega) (by omega) hv hR hYR hAll
  have hconstraint:G ≠ 0→J ≠ 0→
      (A-(V H).log)-(A+2*u-t-(V G).log)≤2*(A-u-(V J).log):=by
    intro hG hJ
    apply BoundaryTail.DUC V (n:=m₀+2) (by omega)
      H G J hH hG hJ (fun i=>ev (RE F m₀ i.val)) A (A+2*u-t) (A-u) (hD hJ)
    · intro i
      simpa only [show m₀+2-2=m₀ by omega,
        show A+2*u-t-A=2*u-t by ring] using hcoeffs m₀ hm₀ i
    · simp only [ev,RingHom.comp_apply,EOK,
        surfaceMap_C,MvPolynomial.eval₂Hom_C]
      apply hcoeff
      have hn:=ETY (K:=K) m₀ hchar
      intro hz
      apply hn
      apply (φ.comp Polynomial.C).injective
      simpa using hz
    · rw [← CTZ ev F m₀]
      exact hfirst
  have hresult:=BoundaryTail.ETA V (n:=m+2) (by omega) H G J hH
    (fun i=>ev (RE F m i.val)) A u t ht0 htu huA hA hB hD hconstraint
    (by intro i;simpa only [Nat.add_sub_cancel] using hcoeffs m hm i)
  rw [← CTZ ev F m] at hresult
  simp only [show m+2-1=m+1 by omega] at hresult
  convert hresult using 1<;>push_cast<;>ring

def normalFlag (m r v z:ℕ):FlagDegree:=
  ⟨(m+3)*z,(m+3)*v-(m+1),(m+3)*(r-1)⟩

theorem GHH (V:Valuation L (WithZero (Multiplicative ℤ)))
    (x:Fin 3→L) (m r v z:ℕ) (hv:1≤v):
    flagPole V x (normalFlag m r v z)=
      ((m:ℤ)+3)*flagPole V x (⟨z,v,r-1⟩:FlagDegree)-
        ((m:ℤ)+1)*flagPole V x unitYZFlag:=by
  have hsub:m+1≤(m+3)*v:=by nlinarith
  simp only [normalFlag,flagPole,unitYZFlag,Nat.cast_sub hsub,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero]
  ring

theorem FPJ (V:Valuation L (WithZero (Multiplicative ℤ)))
    (coeff:Ω→+*L) (hcoeff: ∀a:Ω,a ≠ 0→V (coeff a)=1)
    (x:Fin 3→L) (φ:Polynomial K→+*Ω) (hφ:Function.Injective φ)
    (F:MvPolynomial (Fin 4) K) (m:ℕ):
    V (MvPolynomial.eval₂Hom coeff x (RCN086._Q2 φ F (m+2))/
      (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)))^(m+1))=
    V ((MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)))^3*
      MvPolynomial.eval₂Hom coeff x (surfaceMap φ (MN F m))/
      (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)))^(m+1)):=by
  have hunit:=hcoeff _ (RCN086.AVR φ hφ (m+2))
  simp only [map_pow] at hunit
  rw [RCN086.ALA,CAN]
  simp only [map_mul,map_pow,MvPolynomial.eval₂Hom_C,map_div₀,hunit,mul_one]

theorem DQQ
    (V:Valuation L (WithZero (Multiplicative ℤ)))
    (coeff:Ω→+*L) (hcoeff: ∀a:Ω,a ≠ 0→V (coeff a)=1)
    (x:Fin 3→L) (φ:Polynomial K→+*Ω) (hφ:Function.Injective φ)
    (F:MvPolynomial (Fin 4) K) (m₀ m r v z p:ℕ) [CharP K p]
    (hm₀:1≤m₀) (hm:1≤m) (hchar:2*m₀<p)
    (hr:3≤r) (hv:2≤v)
    (hR:WeightBound BE F (r:ℤ))
    (hYR:WeightBound BC F ((r+v:ℕ):ℤ))
    (hAll:WeightBound AT F ((r+v+z:ℕ):ℤ))
    (hH:MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)) ≠ 0)
    (hfirst:MvPolynomial.eval₂Hom coeff x (RCN086._Q2 φ F (m₀+2))=0):
    2*RCN187.poleOrder V
      (MvPolynomial.eval₂Hom coeff x (RCN086._Q2 φ F (m+2))/
        (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)))^(m+1))≤
      2*flagPole V x (normalFlag m r v z)+((m:ℤ)+2)*
        max (2*flagPole V x unitAllFlag) (flagPole V x unitYZFlag+
          RCN187.poleOrder V (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyG K F))/
            MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)))):=by
  have hscalar:coeff ((-φ Polynomial.X)^(m₀+2)) ≠ 0:=by
    intro hz
    have hh:=hcoeff _ (RCN086.AVR φ hφ (m₀+2))
    rw [hz,map_zero] at hh
    exact zero_ne_one hh
  simp only [map_pow] at hscalar
  have hbase:MvPolynomial.eval₂Hom coeff x (surfaceMap φ (MN F m₀))=0:=by
    rw [RCN086.ALA,CAN] at hfirst
    simp only [map_mul,map_pow,MvPolynomial.eval₂Hom_C] at hfirst
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hfirst).resolve_right hscalar)).resolve_left
      (pow_ne_zero 3 hH)
  have h:=DPJ V coeff hcoeff x φ F m₀ m r v z p
    hm₀ hm hchar hr hv hR hYR hAll hH hbase
  rw [GHH V x m r v z (by omega)]
  simp only [RCN187.poleOrder,FPJ V coeff hcoeff x φ hφ F m,max_comm]
  simpa only [max_comm,RingHom.comp_apply] using h

end
end ProximityPrize.SubmissionLower.JE
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.RCN199
open scoped Classical BigOperators WithZero
open RCN002 RCN344 RCN341 RCN095 RCN114 RCN295 RCN187 RCN207 RCN064 RCN204 RCN271 RCN257
noncomputable section
set_option autoImplicit false
variable {K:Type} [Field K]
variable {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
variable {H G:MvPolynomial (Fin 3) K}

namespace RD

theorem EQK [IsAlgClosed K]
    (budget:RD P H G)
    (base:BP P)
    (T:MvPolynomial (Fin 3) K) (denom factor:ℕ) (q:FlagDegree)
    (hH:H ∉ P) (hT:T ∉ P)
    (hpole: ∀v:Place K (AJ K P),
      2*poleOrder v.val
          (BR K P T/
            (BR K P H)^denom)≤
        2*flagPole v.val (coordinate K P) q+
          (2*factor:ℕ)*KS P H G v):
    ABY P H T
      (budget.weightedCost q+factor*budget.movingCost):=by
  apply AIR K P base H T denom _ hT hH
  intro W
  have hlocal: ∀v ∈ W,
      (2*poleOrder v.val
          (BR K P T/
            (BR K P H)^denom):ℤ)≤
        2*flagPole v.val (coordinate K P) q+
          (2*factor:ℤ)*KS P H G v:=by
    intro v hv
    exact hpole v
  have hsum:=Finset.sum_le_sum hlocal
  have hflag:=budget.CUE q W
  have hmove:=budget.movingPole W
  have hbound:
      (2:ℤ)*(∑ v ∈ W,poleOrder v.val
        (BR K P T/
          (BR K P H)^denom))≤
      (2:ℤ)*(budget.weightedCost q+factor*budget.movingCost):=by
    calc
      _= ∑ v ∈ W,(2*poleOrder v.val
          (BR K P T/
            (BR K P H)^denom):ℤ):=by
            simp only [Finset.mul_sum]
      _≤ ∑ v ∈ W,(2*flagPole v.val (coordinate K P) q+
          (2*factor:ℤ)*KS P H G v):=hsum
      _=(2:ℤ)*((∑ v ∈ W,flagPole v.val (coordinate K P) q)+
          (factor:ℤ)* ∑ v ∈ W,KS P H G v):=by
            simp only [Finset.sum_add_distrib,← Finset.mul_sum]
            push_cast
            ring
      _≤(2:ℤ)*(budget.weightedCost q+factor*budget.movingCost):=by
            gcongr
  have hfinal:
      (∑ v ∈ W,poleOrder v.val
        (BR K P T/
          (BR K P H)^denom):ℤ)≤
        (budget.weightedCost q+factor*budget.movingCost:ℤ):=by
    linarith
  simpa only [RCN346.poleOrder,HJ,
    Nat.cast_add,Nat.cast_mul] using hfinal

end RD
end
end ProximityPrize.SubmissionLower.RCN199
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.JE

open RCN002 RCN055 RCN057 RCN064 RCN086 RCN095 RCN114 RCN136 RCN156
open RCN187 RCN199 RCN204 RCN234 RCN257 RCN271 RCN295 RCN313 RCN341 RCN344

noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]

theorem coordinate_eval₂ (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (Q:MvPolynomial (Fin 3) Ω):
    MvPolynomial.eval₂Hom (algebraMap Ω (AJ Ω P)) (coordinate Ω P) Q=
      BR Ω P Q:=by
  rw [HJ]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm

theorem DQR
    (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (V:Place Ω (AJ Ω P))
    (φ:Polynomial K→+*Ω) (hφ:Function.Injective φ)
    (F:MvPolynomial (Fin 4) K) (m₀ m r v z p:ℕ) [CharP K p]
    (hm₀:1≤m₀) (hm:1≤m) (hchar:2*m₀<p)
    (hr:3≤r) (hv:2≤v)
    (hR:WeightBound BE F (r:ℤ))
    (hYR:WeightBound BC F ((r+v:ℕ):ℤ))
    (hAll:WeightBound AT F ((r+v+z:ℕ):ℤ))
    (hH:surfaceMap φ (polyH K F) ∉ P)
    (hfirst:_Q2 φ F (m₀+2) ∈ P):
    2*poleOrder V.val (BR Ω P (_Q2 φ F (m+2))/
      BR Ω P (surfaceMap φ (polyH K F))^(m+1))≤
      2*flagPole V.val (coordinate Ω P) (normalFlag m r v z)+
        ((m:ℤ)+2)*KS P
          (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F)) V:=by
  have hHne:BR Ω P (surfaceMap φ (polyH K F)) ≠ 0:=by
    intro hz
    apply hH
    rw [← FB Ω P]
    exact hz
  have hfirstzero:BR Ω P (_Q2 φ F (m₀+2))=0:=by
    change _Q2 φ F (m₀+2) ∈ RingHom.ker (BR Ω P).toRingHom
    rw [FB]
    exact hfirst
  have hcoeff: ∀a:Ω,a ≠ 0→V.val (algebraMap Ω (AJ Ω P) a)=1:=by
    letI:V.val.IsTrivialOn Ω:=V.property.2
    exact Valuation.IsTrivialOn.eq_one
  have h:=DQQ V.val (algebraMap Ω (AJ Ω P))
    hcoeff (coordinate Ω P) φ hφ F m₀ m r v z p hm₀ hm hchar hr hv hR hYR hAll
    (by rwa [coordinate_eval₂]) (by rwa [coordinate_eval₂])
  simpa only [coordinate_eval₂,KS,movingRatio,BPD,
    CWP] using h

theorem EXE [IsAlgClosed Ω]
    (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (φ:Polynomial K→+*Ω) (hφ:Function.Injective φ)
    (F:MvPolynomial (Fin 4) K) (m₀ m r v z p factor:ℕ) [CharP K p]
    (hm₀:1≤m₀) (hm:1≤m) (hchar:2*m₀<p)
    (hr:3≤r) (hv:2≤v) (hfactor:m+2≤2*factor)
    (hR:WeightBound BE F (r:ℤ))
    (hYR:WeightBound BC F ((r+v:ℕ):ℤ))
    (hAll:WeightBound AT F ((r+v+z:ℕ):ℤ))
    (budget:RD P (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F)))
    (base:BP P)
    (hH:surfaceMap φ (polyH K F) ∉ P)
    (hfirst:_Q2 φ F (m₀+2) ∈ P)
    (hlater:_Q2 φ F (m+2) ∉ P):
    ABY P (surfaceMap φ (polyH K F)) (_Q2 φ F (m+2))
      (budget.weightedCost (normalFlag m r v z)+factor*budget.movingCost):=by
  apply budget.EQK base _ (m+1) factor _ hH hlater
  intro V
  apply (DQR P V φ hφ F m₀ m r v z p hm₀ hm hchar
    hr hv hR hYR hAll hH hfirst).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast hfactor)
  simp only [KS,poleOrder]
  positivity

end
end ProximityPrize.SubmissionLower.JE
end MergedPart7
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace CNQ
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA GJ IB
open JE RCN057
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable [CharP K p]
variable {stageErrorCap:ℕ}

set_option maxHeartbeats 1000000 in
theorem BRG
    (t y r:Nat) (hr3:3≤r) (hb:r+2≤y) (hyt:y≤t)
    (hchar:2*(w-1)<p)
    (S:FH (AL K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (C:CM S)
    (budget:RD C.1
      (CR (AL K) S.F)
      (surfaceMap (AL K) (polyG K S.F)))
    (base:BP C.1)
    (delay:ℕ) (hdelay:1≤delay) (factor:ℕ)
    (hfactor:w+1+delay≤2*factor)
    (htail:_Q2 (AL K) S.F
      (w+1+delay) ∉ C.1):
    (HF (GenericField K) S.G
        (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card≤
      budget.weightedCost (JE.normalFlag (w-1+delay) r (y-r) (t-y))+
        factor*budget.movingCost:=by
  classical
  have Hsupport:KW (cellSupport t y r) S.F:=
    ⟨S.AFS,S.ACG,S.UT⟩
  have hs:cellS r+2=r:=by dsimp [cellS];omega
  have hys:cellB y r+cellS r+3=r+(y-r):=by
    dsimp [cellB,cellS];omega
  have htot:cellA t y+cellB y r+cellS r+3=r+(y-r)+(t-y):=by
    dsimp [cellA,cellB,cellS];omega
  have hR:WeightBound BE S.F (r:ℤ):=by
    apply Or.inr
    exact_mod_cast (show wt BE S.F≤r by
      simpa only [cellSupport,RCN198.support,hs] using Hsupport.s_weight)
  have hYR:WeightBound BC S.F ((r+(y-r):ℕ):ℤ):=by
    apply Or.inr
    exact_mod_cast (show wt BC S.F≤r+(y-r) by
      simpa only [cellSupport,RCN198.support,hys] using Hsupport.ys_weight)
  have hAll:WeightBound AT S.F ((r+(y-r)+(t-y):ℕ):ℤ):=by
    apply Or.inr
    exact_mod_cast (show wt AT S.F≤r+(y-r)+(t-y) by
      simpa only [cellSupport,RCN198.support,htot] using Hsupport.total_weight)
  have hHnot:CR (AL K) S.F ∉ C.1:=
    _Q6 (GenericField K) S.G _ _ C
  have hfirst:_Q2 (AL K) S.F (w+1) ∈ C.1:=
    GV (GenericField K) S.G _ _ C
  have hzero:ABY C.1
      (CR (AL K) S.F)
      (_Q2 (AL K) S.F (w+1+delay))
      (budget.weightedCost (JE.normalFlag (w-1+delay) r (y-r) (t-y))+
        factor*budget.movingCost):=by
    have hlevel:w-1+delay+2=w+1+delay:=by norm_num [w];omega
    have hfirstlevel:w-1+2=w+1:=by norm_num [w]
    have hf:w-1+delay+2≤2*factor:=by omega
    have hfirst0:_Q2 (AL K) S.F (w-1+2) ∈ C.1:=by
      rw [hfirstlevel]
      exact hfirst
    have hlater0:_Q2 (AL K) S.F (w-1+delay+2) ∉ C.1:=by
      rw [hlevel]
      exact htail
    have hz:=JE.EXE C.1
      (AL K) (DI K) S.F
      (w-1) (w-1+delay) r (y-r) (t-y) p factor
      (by norm_num [w]) (by norm_num [w];omega) hchar hr3 (by omega)
      hf hR hYR hAll budget base hHnot hfirst0 hlater0
    rwa [hlevel] at hz
  let seeds:=HF (GenericField K) S.G
    (_Q2 (AL K) S.F (w+1))
    (CR (AL K) S.F) Gamma
    (DK (AL K) S.selected) C
  let pts:Finset (Fin 3→GenericField K):=
    seeds.image (DK (AL K) S.selected)
  have hprime: ∀v ∈ pts,
      C.1≤RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
    exact MC (GenericField K) S.G
      (_Q2 (AL K) S.F (w+1))
      (CR (AL K) S.F) Gamma
      (DK (AL K) S.selected) C gamma hgamma
  have hHne: ∀v ∈ pts,MvPolynomial.aeval v
      (CR (AL K) S.F) ≠ 0:=by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
    have hGamma:gamma ∈ Gamma:=LU (GenericField K) S.G
      (_Q2 (AL K) S.F (w+1))
      (CR (AL K) S.F) Gamma
      (DK (AL K) S.selected) C hgamma
    show MvPolynomial.eval
        (DK (AL K) S.selected gamma)
        (CR (AL K) S.F) ≠ 0
    exact (WQ (AL K) S.selected gamma
      (MvPolynomial.pderiv (2:Fin 4) S.F)).symm ▸ S.regular gamma hGamma
  have hAzero: ∀v ∈ pts,MvPolynomial.aeval v
      (_Q2 (AL K) S.F (w+1+delay))=0:=by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
    have hGamma:gamma ∈ Gamma:=LU (GenericField K) S.G
      (_Q2 (AL K) S.F (w+1))
      (CR (AL K) S.F) Gamma
      (DK (AL K) S.selected) C hgamma
    have hz:MvPolynomial.aeval
        (DK (AL K) S.selected gamma)
        (_Q2 (AL K) S.F
          (w+1+delay))=0:=
      VZ (AL K) S.F
        S.selected gamma w (w+1+delay)
        (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
    exact hz
  have hbound:pts.card≤
      budget.weightedCost (JE.normalFlag (w-1+delay) r (y-r) (t-y))+
        factor*budget.movingCost:=
    hzero pts hprime hHne hAzero
  have hcard:pts.card=seeds.card:=
    Finset.card_image_of_injective seeds
      (ABD (AL K) S.selected)
  show seeds.card≤_
  omega

end
end CNQ
end MergedPart0
section MergedPart1
namespace JE
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open RCN095 RCN237 RCN206 RCN327 FA GJ

theorem EZR (m v:ℕ) (hv:1≤v):
    (m+3)*v-(m+1)=(m+3)*(v-1)+2:=by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hv
  simp only [Nat.add_sub_cancel_left,Nat.mul_add,Nat.mul_one]
  omega

theorem CML (t y r:ℕ) (hr:3≤r)
    (hy:r+2≤y):
    normalFlag w r (y-r) (t-y)=
      MK t y r+w • unitAllFlag:=by
  unfold normalFlag MK cellRational
  apply congrArg₃ (f:=FlagDegree.mk)
  all_goals simp only [normalFlag,MK,cellRational,
    BGD,ZR,cellA,cellB,cellS,add_zOnly,add_yz,
    add_all,nsmul_zOnly,nsmul_yz,nsmul_all,unitAllFlag,w]
  all_goals omega

theorem DBT (w m d r v z:ℕ)
    (hw:1≤w) (hm:1≤m) (hd:d≤m) (hv:1≤v):
    (normalFlag (w-1+d) r v z).zOnly≤(m • normalFlag w r v z).zOnly∧
    (normalFlag (w-1+d) r v z).yz≤(m • normalFlag w r v z).yz∧
    (normalFlag (w-1+d) r v z).all≤(m • normalFlag w r v z).all:=by
  have hwsub:w-1+1=w:=Nat.sub_add_cancel hw
  have hscale:w-1+d+3≤m*(w+3):=by nlinarith [Nat.mul_le_mul_right w hm]
  simp only [normalFlag,nsmul_zOnly,nsmul_yz,nsmul_all]
  refine ⟨?_,?_,?_⟩
  · nlinarith [Nat.mul_le_mul_right z hscale]
  · rw [EZR _ _ hv,EZR _ _ hv]
    nlinarith [Nat.mul_le_mul_right (v-1) hscale]
  · nlinarith [Nat.mul_le_mul_right (r-1) hscale]

theorem EZO (d m:ℕ) (hd:d≤m) (hm:m≤5):
    w+1+d≤2*65539:=by
  simp only [w]
  omega

end JE
end MergedPart1
section MergedPart2
namespace ID
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA GJ IB
open ND JN
open JE
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap:ℕ}

def cellNormal (t y r:ℕ):FlagDegree:=
  JE.normalFlag w r (y-r) (t-y)

theorem CRN
    (t y r:Nat) (hr3:3≤r) (hb:r+2≤y) (hyt:y≤t)
    (hchar:2*(w-1)<p)
    (S:FH (AL K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper: ¬S.G ∣ _Q2 (AL K) S.F
      (w+1))
    (tail1:FlagDegree)
    (B:FE
      (G:=S.G) (T:=_Q2 (AL K) S.F
        (w+1))
      (H:=CR (AL K) S.F) flag tail1)
    (base: ∀C:CM S,BP C.1)
    (budget: ∀C:CM S,
      RD C.1
        (CR (AL K) S.F)
        (surfaceMap (AL K) (polyG K S.F)))
    (hcost: ∀C:CM S,
      (budget C).zCost=B.zCost C∧(budget C).yzCost=B.yzCost C∧
        (budget C).allCost=B.allCost C)
    (active:Finset (CM S)) (movingTotal:ℕ)
    (hinactive: ∀C:CM S,C ∉ active→
      (HF (GenericField K) S.G
        (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card=0)
    (hmovingSum:(∑ C ∈ active,(budget C).movingCost)≤movingTotal)
    (hgate:stageErrorCap+1≤(cellNormal t y r).yz)
    (htangent: ∀C:CM S,
      (∀delay,_Q2 (AL K) S.F
        (w+1+delay) ∈ C.1)→
      (HF (GenericField K) S.G
        (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card≤
          (stageErrorCap+1)*B.yzCost C)
    (hresultants:EY B
      (fun C=>FO (MU S)
        (DN (MU S) hfirstProper) C)):
    Nonempty (AKI
      (tailFlag1:=tail1)
      (tailFlag2:=cellNormal t y r) S
      (flagMixed flag tail1 (cellNormal t y r)+
        65539*movingTotal)):=by
  classical
  have hry:r<y:=by omega
  have hr2:2≤r:=by omega
  let S0:=MU S
  let multiplicity:CM S→ℕ:=fun C=>
    FO S0 (DN S0 hfirstProper) C
  have hone: ∀C,1≤multiplicity C:=
    ADP S hfirstProper
  have hwcEq: ∀(C:CM S) (f:FlagDegree),
      (budget C).weightedCost f=B.weightedCost f C:=by
    intro C f
    obtain ⟨hz,hy',ha⟩:=hcost C
    simp only [RD.weightedCost,
      FE.weightedCost,hz,hy',ha]
  have hscale: ∀(m:ℕ) (f:FlagDegree) (C:CM S),
      B.weightedCost (m • f) C=m*B.weightedCost f C:=by
    intro m f C
    simp only [FE.weightedCost,nsmul_zOnly,nsmul_yz,
      nsmul_all]
    ring
  have hnormal: ∀C:CM S,
      B.weightedCost (MK t y r) C≤
        B.weightedCost (cellNormal t y r) C:=by
    intro C
    unfold cellNormal
    rw [CML t y r hr3 hb]
    apply CUY B C
    all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,
      nsmul_yz,nsmul_all,unitAllFlag]
    all_goals omega
  let cost:CM S→ℕ:=fun C=>
    multiplicity C*B.weightedCost (cellNormal t y r) C+
      65539*(budget C).movingCost
  have hcost_pointwise: ∀C,cost C≤
      multiplicity C*B.weightedCost (cellNormal t y r) C+
        65539*(budget C).movingCost:=fun _=>le_rfl
  have hbound: ∀C,
      (HF (GenericField K) S.G
        (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card≤cost C:=by
    intro C
    have dichotomy:=AEM S0
      (DN S0 hfirstProper) C hfirstProper
    rcases dichotomy.2 with hproper | htangentBranch
    · obtain ⟨delay,hdelay,hdelayMu,htail⟩:=hproper
      by_cases hm:6≤multiplicity C
      · have hzero: ∀gamma ∈ HF (GenericField K) S.G
            (_Q2 (AL K) S.F (w+1))
            (CR (AL K) S.F) Gamma
            (DK (AL K) S.selected) C,
            MvPolynomial.aeval
              (DK (AL K) S.selected gamma)
              (_Q2 (AL K) S.F (w+1+delay))=0:=by
          intro gamma hgamma
          have hGamma:=LU (GenericField K) S.G
            (_Q2 (AL K) S.F (w+1))
            (CR (AL K) S.F) Gamma
            (DK (AL K) S.selected) C hgamma
          exact VZ (AL K)
            S.F S.selected gamma w (w+1+delay)
            (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
        have hflagMod:BIU C.1
            (multiplicity C • MK t y r)
            (_Q2 (AL K) S.F (w+1+delay)):=by
          refine ⟨_Q2 (AL K) S.F (w+1+delay),
            CUW t y r hr3 hry S delay
              (multiplicity C) hdelay hdelayMu hm,?_⟩
          simp
        have hcount:=AQR (Seed:=K) B C Gamma
          (DK (AL K) S.selected)
          (ABD (AL K) S.selected)
          hflagMod htail hzero
        rw [hscale] at hcount
        exact hcount.trans ((Nat.mul_le_mul_left _ (hnormal C)).trans
          (Nat.le_add_right _ _))
      · have hdm:delay≤multiplicity C:=hdelayMu
        have hcount:=CNQ.BRG
          t y r hr3 hb hyt hchar S C (budget C) (base C) delay hdelay
          65539 (EZO delay (multiplicity C) hdm (by omega)) htail
        simp only [hwcEq] at hcount
        have hmono:=DBT w (multiplicity C) delay r
          (y-r) (t-y) (by norm_num [w]) (hone C) hdm (by omega)
        have hcostle:=CUY B C hmono.1 hmono.2.1 hmono.2.2
        rw [hscale] at hcostle
        exact hcount.trans (Nat.add_le_add_right hcostle _)
    · have hcount:=htangent C htangentBranch
      calc _≤(stageErrorCap+1)*B.yzCost C:=hcount
        _≤B.weightedCost (cellNormal t y r) C:=
          BIB B (cellNormal t y r) C
            (stageErrorCap+1) hgate
        _≤multiplicity C*B.weightedCost (cellNormal t y r) C:=by
          simpa only [one_mul] using Nat.mul_le_mul_right
            (B.weightedCost (cellNormal t y r) C) (hone C)
        _≤cost C:=Nat.le_add_right _ _
  let activeCost:CM S→ℕ:=fun C=>if C ∈ active then cost C else 0
  have hactiveBound: ∀C,
      (HF (GenericField K) S.G
        (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card≤activeCost C:=by
    intro C
    by_cases hC:C ∈ active
    · simpa only [activeCost,if_pos hC] using hbound C
    · simp only [activeCost,if_neg hC,hinactive C hC,le_refl]
  have hsum:(∑ C,activeCost C)≤
      flagMixed flag tail1 (cellNormal t y r)+65539*movingTotal:=by
    have ha:(∑ C,activeCost C)= ∑ C ∈ active,cost C:=by simp only [activeCost,Finset.sum_ite_mem,Finset.univ_inter]
    rw [ha]
    calc
      (∑ C ∈ active,cost C)≤
          ∑ C ∈ active,(multiplicity C*
            B.weightedCost (cellNormal t y r) C+
            65539*(budget C).movingCost):=
        Finset.sum_le_sum (fun C _=>hcost_pointwise C)
      _=(∑ C ∈ active,multiplicity C*
            B.weightedCost (cellNormal t y r) C)+
          65539*(∑ C ∈ active,(budget C).movingCost):=by
        rw [Finset.sum_add_distrib,Finset.mul_sum]
      _≤(∑ C,multiplicity C*
            B.weightedCost (cellNormal t y r) C)+
          65539*movingTotal:=
        Nat.add_le_add (Finset.sum_le_sum_of_subset (Finset.subset_univ active))
          (Nat.mul_le_mul_left _ hmovingSum)
      _≤_:=Nat.add_le_add (hresultants.divisor_le B multiplicity) (le_refl _)
  have providerDichotomy:=AFC S
    hfirstProper B htangent
  exact ⟨{
    budgetFamily:=B
    multiplicity:=multiplicity
    cost:=activeCost
    one_le_multiplicity:=hone
    EHX:=hgate
    cost_sum_le:=hsum
    CRK:=hactiveBound
    dichotomy:=providerDichotomy}⟩

end
end ID
end MergedPart2
section MergedPart3
namespace _Q19
set_option maxHeartbeats 1000000
open RCN002 RCN004 RCN005 RCN095 RCN125 RCN371
open scoped BigOperators

theorem BOC {Omega:Type} [Field Omega]
    (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (hZ:Transcendental Omega (coordinate Omega P 2))
    (prime:Nat) [CharP Omega prime]
    (G T:MvPolynomial (Fin 3) Omega)
    (hG:Irreducible G) (hGmem:G ∈ P) (hTmem:T ∈ P)
    (hproper: ¬G ∣ T)
    (hR:MvPolynomial.pderiv (1:Fin 3) G ≠ 0)
    (pG pT:FlagDegree)
    (hGflag:RCN095.BI pG G)
    (hTflag:RCN095.BI pT T)
    (hsmall:flagMixed pG pT unitZFlag<prime):
    letI:=DT Omega P 2 hZ
    FiniteDimensional (RatFunc Omega) (AJ Omega P)∧
      Algebra.IsSeparable (RatFunc Omega) (AJ Omega P):=by
  let Q:Unit→Ideal (MvPolynomial (Fin 3) Omega):=fun _=>P
  have hinj:Function.Injective Q:=by
    intro i j _
    exact Subsingleton.elim i j
  letI:Algebra (RatFunc Omega) (AJ Omega P):=
    DT Omega P 2 hZ
  have htZ: ∀i:Unit,Transcendental Omega
      (RCN093.BQ Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0))):=by
    intro i
    simpa [Q,zOrder,Equiv.swap_apply_def] using hZ
  have hembZ (i:Unit):
      RCN022.BO Omega (AJ Omega (Q i))
        (RCN093.BQ Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0))) (htZ i)=
      RCN022.BO Omega (AJ Omega P) (coordinate Omega P 2) hZ:=
    by
      have hx:RCN093.BQ Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0))=
          coordinate Omega P 2:=by simp [Q,zOrder]
      simp only [hx]
      rfl
  have hgenZ: ∀i:Unit,
      letI:Algebra (RatFunc Omega) (AJ Omega (Q i)):=
        (RCN022.BO Omega (AJ Omega (Q i))
          (RCN093.BQ Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0)))
          (htZ i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc Omega)
        ({RCN093.BQ Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 2)),
          RCN093.BQ Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 1))}:
            Set (AJ Omega (Q i)))= ⊤ :=by
    intro i
    rw [hembZ i]
    simpa [Q,zOrder,Equiv.swap_apply_def] using RCN093.BKE Omega P 0 0 0 hZ
  have hfamily:=RCN093.RG
    (K:=Omega) (Q:=Q) hinj 0 0 0 zOrder htZ hgenZ
      G T hG (fun _=>hGmem) (fun _=>hTmem) hproper
      (by simpa using (RCN117.MV 0 0 G hR).2)
      pG.all pT.all (pG.yz+pG.all) (pT.yz+pT.all)
      (flagMixed pG pT unitZFlag) (by
        intro hzero
        apply hproper
        rw [hzero]
        exact dvd_zero G)
      (by
        simpa using (RCN123.LQ pG G 0 0 0
          ((EI pG G).2 hGflag)).zOuter)
      (by
        simpa using (RCN123.LQ pT T 0 0 0
          ((EI pT T).2 hTflag)).zOuter)
      (by
        simpa using (RCN123.LQ pG G 0 0 0
          ((EI pG G).2 hGflag)).zTotal)
      (by
        simpa using (RCN123.LQ pT T 0 0 0
          ((EI pT T).2 hTflag)).zTotal)
      (RCN121.BDA pG pT)
  have hfd:FiniteDimensional (RatFunc Omega) (AJ Omega P):=by
    convert hfamily.1 () using 1
    congr 1
    exact congrArg (fun e:RatFunc Omega→ₐ[Omega] AJ Omega P=>e.toRingHom.toAlgebra) (hembZ ()).symm
  have hrank:Module.finrank (RatFunc Omega) (AJ Omega P)≤
      flagMixed pG pT unitZFlag:=by
    have hs:=hfamily.2
    simp only [Fintype.sum_unique] at hs
    convert hs using 1
    congr 2
    exact congrArg (fun e:RatFunc Omega→ₐ[Omega] AJ Omega P=>e.toRingHom.toAlgebra) (hembZ ()).symm
  letI:=hfd
  refine ⟨hfd,⟨fun x=> ?_⟩⟩
  have hint:IsIntegral (RatFunc Omega) x:=Algebra.IsIntegral.isIntegral x
  exact (RCN364.WS prime
    (minpoly (RatFunc Omega) x) x (minpoly.ne_zero hint) (minpoly.aeval _ _)
    ((minpoly.natDegree_le (A:=RatFunc Omega) x).trans_lt (hrank.trans_lt hsmall))).2
end _Q19
end MergedPart3
section MergedPart4
namespace AGZ
open scoped Classical BigOperators
open _Q19
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN040 RCN041 RCN265 RCN274 RCN198 RCN086 RCN263 RCN089
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K→+*Omega} {Gamma:Finset K} {x:Iota→K}
 {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem UI
   (S:FH phi Gamma x pchar e flag w (support a b s))
   (hproper:¬S.G ∣ _Q2 phi S.F (w+1))
   (hflagChar:flag.yz+flag.all<pchar∧flag.all<pchar∧
     flag.zOnly+flag.yz+flag.all<pchar)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<pchar):
   ∃(base:∀C:AU Omega S.G
       (RA phi (support a b s) S.F (w+1))
       (CR phi S.F),BP C.1),
     ∃(hactive:∀C:AU Omega S.G
         (RA phi (support a b s) S.F (w+1))
         (CR phi S.F),
         KaehlerDifferential.D Omega (AJ Omega C.1)
             (coordinate Omega C.1 0) ≠ 0∨
           KaehlerDifferential.D Omega (AJ Omega C.1)
             (coordinate Omega C.1 2) ≠ 0),
       ∃(hZ:∀C:AU Omega S.G
           (RA phi (support a b s) S.F (w+1))
           (CR phi S.F),GR C 2),
         Nonempty (JO base hactive
           (RCN315.EH S)):=by
 classical
 let supp:=support a b s
 let T:=_Q2 phi S.F (w+1)
 let Tred:=RA phi supp S.F (w+1)
 let H:=CR phi S.F
 have hd:S.G ∣ T-Tred:=
   S.RR.trans (AMZ phi supp S.F (w+1))
 have hproperRed:¬S.G ∣ Tred:=by
   intro hr
   apply hproper
   have:=hd.add hr
   simpa only [T,Tred,sub_add_cancel] using this
 have hGflag:BI flag S.G:=S.flag_support
 let Hsupport:KW supp S.F:=
   ⟨S.AFS,S.ACG,S.UT⟩
 have hTflag:BI
     (CI supp (w+1)) Tred:=
   AOF phi supp Hsupport (w+1)
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.WD
     hGflag
 have hGdegree:∀j:Fin 3,S.G.degreeOf j<pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hR:=RCN315.EH S
 let hZ:∀C:AU Omega S.G Tred H,GR C 2:=by
   intro C htr
   exact BOC C.1 htr pchar S.G Tred
     S.MW (EN Omega S.G Tred H C)
     (GV Omega S.G Tred H C) hproperRed hR
     flag (CI supp (w+1)) hGflag hTflag hmixed
 let choiceData:∀C:AU Omega S.G Tred H,
     ∃B:BP C.1,B.index=0∨B.index=2:=by
   intro C
   by_cases hz:Transcendental Omega (coordinate Omega C.1 2)
   · exact ⟨⟨2,hz,(hZ C hz).1,(hZ C hz).2⟩,Or.inr rfl⟩
   · have hy:=(AAO phi S.F S.G Tred
       S.RR C).resolve_right hz
     have hsep:=AKM C.1 pchar S.G
       S.MW (EN Omega S.G Tred H C)
       S.y_dependent hGdegree hy (not_not.mp hz)
     exact ⟨⟨0,hy,hsep.1,hsep.2⟩,Or.inl rfl⟩
 let base:∀C:AU Omega S.G Tred H,
     BP C.1:=fun C↦(choiceData C).choose
 have hbaseIndex:∀C:AU Omega S.G Tred H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀C:AU Omega S.G Tred H,
     KaehlerDifferential.D Omega (AJ Omega C.1)
         (coordinate Omega C.1 0) ≠ 0∨
       KaehlerDifferential.D Omega (AJ Omega C.1)
         (coordinate Omega C.1 2) ≠ 0:=by
   intro C
   have hb:=ACB (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 exact ⟨base,hactive,hZ,
   AFF base hactive
     (RCN315.EH S)⟩
end
end AGZ

namespace AGZ
open scoped Classical BigOperators
open _Q19
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN039 RCN040 RCN041 RCN265 RCN274 RCN198
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K→+*Ω} {Γ:Finset K} {x:I→K}
 {p e w a b s:ℕ} [CharP Ω p] {flag:FlagDegree}
theorem AMV
   (S:FH φ Γ x p e flag w (support a b s))
   (x0 u0 u1:K)
   (hproper:¬S.G∣FK φ S.F w x0 u0 u1)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (DL (support a b s) w) unitZFlag<p):
   ∃base:∀C:AU Ω S.G
       (FK φ S.F w x0 u0 u1) (CR φ S.F),
       BP C.1,
     Nonempty (YQ base flag
       (DL (support a b s) w)):=by
 classical
 let T:=FK φ S.F w x0 u0 u1
 let H:=CR φ S.F
 have hsy:s+2<b+s+3:=by omega
 have hTflag:BI (DL (support a b s) w) T:=
   ANZ hsy (phi:=φ)
     ⟨S.AFS,S.ACG,S.UT⟩
     w (fun j:ℕ=>(j.factorial:K)⁻¹) x0 u0 u1
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.WD S.flag_support
 have hGdegree:∀j:Fin 3,S.G.degreeOf j<p:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hR:=RCN315.EH S
 let hZ:∀C:AU Ω S.G T H,GR C 2:=by
   intro C htr
   exact BOC C.1 htr p S.G T
     S.MW (EN Ω S.G T H C)
     (GV Ω S.G T H C) hproper hR
     flag (DL (support a b s) w) S.flag_support hTflag hmixed
 let choiceData:∀C:AU Ω S.G T H,
     ∃B:BP C.1,B.index=0∨B.index=2:=by
   intro C
   by_cases hz:Transcendental Ω (coordinate Ω C.1 2)
   · exact ⟨⟨2,hz,(hZ C hz).1,(hZ C hz).2⟩,Or.inr rfl⟩
   · have hy:=(AAO φ S.F S.G T
       S.RR C).resolve_right hz
     have hsep:=AKM C.1 p S.G
       S.MW (EN Ω S.G T H C)
       S.y_dependent hGdegree hy (not_not.mp hz)
     exact ⟨⟨0,hy,hsep.1,hsep.2⟩,Or.inl rfl⟩
 let base:∀C:AU Ω S.G T H,
     BP C.1:=fun C=>(choiceData C).choose
 have hbaseIndex:∀C:AU Ω S.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀C:AU Ω S.G T H,
     D Ω (AJ Ω C.1) (coordinate Ω C.1 0)≠0∨
       D Ω (AJ Ω C.1) (coordinate Ω C.1 2)≠0:=by
   intro C
   have hb:=ACB (base C)
   rcases hbaseIndex C with hidx | hidx
   · left;simpa only [hidx] using hb
   · right;simpa only [hidx] using hb
 obtain ⟨P⟩:=AEJ
   flag (DL (support a b s) w) base hactive hZ
   (RCN315.EH S)
   S.MW hproper
   ((EI flag S.G).2 S.flag_support)
   ((EI
     (DL (support a b s) w) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
end
end AGZ
end MergedPart4
section MergedPart5
namespace KF
open scoped Classical BigOperators
open RCN332 AGZ
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN334 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN042 RCN341 RCN002 RCN344 RCN340
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
theorem AZZ
   {a b s:ℕ}
   (S:FH (AL K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ _Q2 (AL K) S.F (w+1))
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):
   Nonempty (ABN S):=by
 obtain ⟨base,hactive,hZ,-⟩:=
   AGZ.UI S hfirstProper hflagChar hmixed
 obtain ⟨D,hlam,hmu⟩:=RCN038.ACK base hactive
   (RCN315.EH S) (Set.range (AL K))
   (Set.infinite_range_of_injective (DI K))
 exact ⟨⟨base,hactive,hZ,D,hlam,hmu⟩⟩
noncomputable def LI
   {a b s:ℕ}
   (S:FH (AL K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ _Q2 (AL K) S.F (w+1))
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):
   ABN S:=
 Classical.choice (AZZ S hfirstProper hflagChar hmixed)
noncomputable def QK
   {a b s:ℕ}
   (S:FH (AL K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ _Q2 (AL K) S.F (w+1))
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):=
 let A:=LI S hfirstProper hflagChar hmixed
 NJ A.base A.hactive A.hZ
   (RCN315.EH S) A.data
   S.MW (AHF S hfirstProper)
   ((EI flag S.G).2 S.flag_support)
   ((EI
     (CI (support a b s) (w+1))
     (VQ S)).2 (AFM S))
noncomputable def MQ
   {a b s:ℕ}
   (S:FH (AL K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ _Q2 (AL K) S.F (w+1))
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):=
 FE.AQQ (EW S)
   (QK S hfirstProper hflagChar hmixed).toFE
noncomputable def AHP
   {a b s:ℕ}
   (S:FH (AL K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ _Q2 (AL K) S.F (w+1))
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p)
   (C:CM S):BP C.1:=by
 let C':AU (GenericField K) S.G (VQ S)
     (CR (AL K) S.F):=
   ⟨C.1,by
     rw [← VB (EW S)]
     exact C.2⟩
 exact (LI S hfirstProper hflagChar hmixed).base C'
theorem ADY
   {a b s:ℕ}
   (S:FH (AL K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ _Q2 (AL K) S.F (w+1))
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p)
   (C:CM S):
   1≤(MQ S hfirstProper hflagChar hmixed).yzCost C:=by
 let hd:=EW S
 let C':=JA hd C
 let A:=LI S hfirstProper hflagChar hmixed
 let U:=QK S hfirstProper hflagChar hmixed
 change 1≤U.toFE.yzCost C'
 change 1≤DQ (GenericField K)
   (AJ (GenericField K) C'.1) (U.yzProjection C')
 apply RO
 have hproj:U.yzProjection C' =JV
     (RCN093.affineU
       (GenericField K) C'.1 A.data.lam) (A.data.uGate C'):=rfl
 rw [hproj,MT]
 exact A.data.ZG C'
theorem AJM
   {a b s:ℕ}
   (S:FH (AL K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ _Q2 (AL K) S.F (w+1))
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p)
   (C:CM S):
   UJ
     (AHP S hfirstProper hflagChar hmixed C)
     (flagSupport unitYZFlag)
     ((MQ S hfirstProper hflagChar hmixed).yzCost C):=by
 let C':AU (GenericField K) S.G (VQ S)
     (CR (AL K) S.F):=
   ⟨C.1,by
     rw [← VB (EW S)]
     exact C.2⟩
 have heq:JA (EW S) C=C':=by
   apply Subtype.ext
   rfl
 rw [show (MQ S hfirstProper hflagChar hmixed).yzCost C=
     (QK S hfirstProper hflagChar hmixed).toFE.yzCost C' by
   simp only [MQ,FE.AQQ,heq]]
 change UJ
   ((LI S hfirstProper hflagChar hmixed).base C')
   (flagSupport unitYZFlag)
   ((QK S hfirstProper hflagChar hmixed).toFE.yzCost C')
 exact (QK S hfirstProper hflagChar hmixed).toQZ.yzPole C'
theorem BMI
   {a b s:ℕ}
   (S:FH (AL K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ _Q2 (AL K) S.F (w+1))
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):
   let A:=LI S hfirstProper hflagChar hmixed
   ARH A.base A.hactive A.hZ
     (RCN315.EH S) A.data
     (OA (EW S)
       (RK S hfirstProper)):=by
 dsimp only
 exact BRD (MU S)
   hfirstProper (VQ S) (EW S)
   (LI S hfirstProper hflagChar hmixed).base
   (LI S hfirstProper hflagChar hmixed).hactive
   (LI S hfirstProper hflagChar hmixed).hZ
   (RCN315.EH S)
   (LI S hfirstProper hflagChar hmixed).data
theorem ARC
   {a b s:ℕ}
   (S:FH (AL K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ _Q2 (AL K) S.F (w+1))
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):
   EY
     (QK S hfirstProper hflagChar hmixed).toFE
     (OA (EW S)
       (RK S hfirstProper)):=by
 let A:=LI S hfirstProper hflagChar hmixed
 exact BOD A.base A.hactive A.hZ
   (RCN315.EH S) A.data
   S.MW (AHF S hfirstProper)
   ((EI flag S.G).2 S.flag_support)
   ((EI
     (CI (support a b s) (w+1))
     (VQ S)).2 (AFM S))
   (OA (EW S)
     (RK S hfirstProper))
   (BMI S hfirstProper hflagChar hmixed)
theorem AKO
   {a b s:ℕ}
   (S:FH (AL K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ _Q2 (AL K) S.F (w+1))
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):
   EY
     (MQ S hfirstProper hflagChar hmixed)
     (RK S hfirstProper):=by
 exact BBC (EW S)
   (QK S hfirstProper hflagChar hmixed).toFE
   (RK S hfirstProper)
   (ARC S hfirstProper hflagChar hmixed)
end
end KF
end MergedPart5
section MergedPart6
namespace DHS
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open FA GJ IB
open ND JN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 800000

variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap:ℕ}
variable {t y r:Nat}

theorem GHP
    (hr3:3≤r) (hb:r+2≤y) (hyt:y≤t) (hchar:2*(w-1)<p)
    (S:FH (AL K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper: ¬S.G ∣ _Q2 (AL K) S.F
      (w+1))
    (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
      flag.zOnly+flag.yz+flag.all<p)
    (hmixedRed:flagMixed flag (TX t y r) unitZFlag<p)
    (hmix:2*(flag.zOnly+flag.yz+flag.all)*
      (cellA t y+cellB y r+cellS r+4)<p)
    (hrationalGate:stageErrorCap+1≤(ID.cellNormal t y r).yz)
    (htangent: ∀C:CM S,
      (∀delay,_Q2 (AL K) S.F
        (w+1+delay) ∈ C.1)→
      (HF (GenericField K) S.G
        (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card≤
          (stageErrorCap+1)*
            (KF.MQ S hfirstProper hflagChar hmixedRed).yzCost C):
    Nonempty (AKI
      (tailFlag1:=TX t y r)
      (tailFlag2:=ID.cellNormal t y r) S
      (flagMixed flag (TX t y r) (ID.cellNormal t y r)+
        65539*
          flagMixed flag (BZO t y r) (BUV t y r))):=by
  classical
  haveI:CharP (AlgebraicClosure (RatFunc (GenericField K))) p:=
    charP_of_injective_algebraMap
      (algebraMap (GenericField K)
        (AlgebraicClosure (RatFunc (GenericField K)))).injective p
  obtain ⟨budget,hcost,hmov⟩:=
    DNR
      (E:=AlgebraicClosure (RatFunc (GenericField K)))
      (AL K) S.F S.G
      (_Q2 (AL K) S.F (w+1))
      (cellA t y) (cellB y r) (cellS r) w (by norm_num [RCN327.w])
      rfl
      ⟨S.AFS,S.ACG,S.UT⟩
      flag S.MW.ne_zero S.RR S.flag_support
      (KF.AHP S hfirstProper hflagChar hmixedRed)
      (TX t y r)
      (YV (EW S)
        (KF.QK S hfirstProper hflagChar hmixedRed)
        (KF.AHP S hfirstProper hflagChar hmixedRed))
      p hmix
  have hmovingSum:(∑ C:CM S,(budget C).movingCost)≤
      flagMixed flag (BZO t y r) (BUV t y r):=by
    have hcut:=ECN t y r
    have hfib:BZO t y r=
        RCN206.fiberFlag (cellA t y) (cellB y r) (cellS r):=rfl
    rw [hfib,hcut]
    exact hmov

  have hcost' : ∀C:CM S,
      (budget C).zCost=
        (KF.MQ S hfirstProper hflagChar hmixedRed).zCost C∧
      (budget C).yzCost=
        (KF.MQ S hfirstProper hflagChar hmixedRed).yzCost C∧
      (budget C).allCost=
        (KF.MQ S hfirstProper hflagChar hmixedRed).allCost C:=by
    intro C
    obtain ⟨hz,hy,ha⟩:=hcost C
    obtain ⟨ez,ey,ea⟩:=AUD
      (EW S)
      (KF.QK S hfirstProper hflagChar hmixedRed)
      (KF.AHP S hfirstProper hflagChar hmixedRed) C
    refine ⟨hz.trans ez,hy.trans ey,ha.trans ea⟩
  exact ID.CRN
    t y r hr3 hb hyt hchar S hfirstProper (TX t y r)
    (KF.MQ S hfirstProper hflagChar hmixedRed)
    (KF.AHP S hfirstProper hflagChar hmixedRed)
    budget hcost' Finset.univ
    (flagMixed flag (BZO t y r) (BUV t y r))
    (by intro C hC;exact False.elim (hC (Finset.mem_univ C)))
    (by simpa using hmovingSum)
    hrationalGate htangent
    (KF.AKO S hfirstProper hflagChar hmixedRed)

end
end DHS
end MergedPart6
section MergedPart7
namespace ABO
open RCN095 RCN198 RCN263 RCN287 RCN327 FA
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def Safe (r y:ℕ):Prop:=
  r*(TX y y r).yz+y*(TX y y r).all<2130706433∧
  r*(DL (cellSupport y y r) w).yz+
    y*(DL (cellSupport y y r) w).all<2130706433
instance (r y:ℕ):Decidable (Safe r y):=by unfold Safe;infer_instance

theorem DVW (f q:FlagDegree) (r y:ℕ)
    (hr:f.all≤r) (hy:f.yz+f.all≤y):
    flagMixed f q unitZFlag≤r*q.yz+y*q.all:=by
  have h1:=Nat.mul_le_mul_right q.yz hr
  have h2:=Nat.mul_le_mul_right q.all hy
  simp only [flagMixed,unitZFlag]
  nlinarith

theorem reduced_gate (f:FlagDegree) (t y r:ℕ)
    (hsafe:Safe r y) (hfa:f.all≤r) (hfy:f.yz+f.all≤y):
    flagMixed f (TX t y r) unitZFlag<2130706433:=by
  have hy:(TX t y r).yz=(TX y y r).yz:=rfl
  have hr:(TX t y r).all=(TX y y r).all:=rfl
  exact (DVW f _ r y hfa hfy).trans_lt (by rw [hy,hr];exact hsafe.1)

theorem EJG (f:FlagDegree) (t y r:ℕ)
    (hsafe:Safe r y) (hfa:f.all≤r) (hfy:f.yz+f.all≤y):
    flagMixed f (DL (cellSupport t y r) w) unitZFlag<2130706433:=by
  have hy:(DL (cellSupport t y r) w).yz=
      (DL (cellSupport y y r) w).yz:=rfl
  have hr:(DL (cellSupport t y r) w).all=
      (DL (cellSupport y y r) w).all:=rfl
  exact (DVW f _ r y hfa hfy).trans_lt (by rw [hy,hr];exact hsafe.2)
end ABO
end MergedPart7
section MergedPart8
namespace BRK
open scoped Classical BigOperators
open RCN146
open RCN135 RCN136 RCN231 RCN319 RCN313 RCN174 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275 RCN198 RCN203 RCN287 RCN049 RCN144 RCN063 RCN145 RCN087 RCN046 RCN265 RCN295 RCN344 RCN002
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 45000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Γ:Finset K} {x:I→K} {p e a b s:ℕ} [CharP (GenericField K) p]
 {flag:FlagDegree} {w:ℕ}
theorem AAB
   (S:FH (AL K) Γ x p e flag w (support a b s))
   (agreements:ℕ) (hnodes:S.nodes.card=agreements+e)
   (hagreement:∀γ∈Γ,agreements≤(S.AJW γ).card)
   (hwa:w<agreements)
   (hTail:S.G∣surfaceMap (AL K) (numerator K S.F (w+1)))
   (bound seedCap slopeCap:ℕ) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈BA K bound w seedCap slopeCap)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (DL (support a b s) w) unitZFlag<p):
   AEO S (IY flag a b s w):=by
 classical
 unfold AEO
 intro i hi
 dsimp only
 intro hproper
 let T:=FK (AL K) S.F w
   (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
 obtain ⟨base,⟨U⟩⟩:=AGZ.AMV S
   (x i) (S.u0 i) (S.u1 i) hproper hflagChar hmixed
 let cost:AU (GenericField K) S.G T (CR (AL K) S.F)→ℕ:=
   fun C=>U.family.toFE.zCost C+
     U.family.toFE.yzCost C
 refine ⟨cost,?_,?_⟩
 · intro C
   let Gc:=HF (GenericField K) S.G T
     (CR (AL K) S.F) Gi
     (DK (AL K) S.selected) C
   have hGcGi:Gc⊆Gi:=LU (GenericField K) S.G T _ Gi _ C
   have hGiΓ:Gi⊆Γ:=Finset.filter_subset _ _
   have hGcΓ:Gc⊆Γ:=hGcGi.trans hGiΓ
   have hyzC:∀W:Finset (RCN346.Place (GenericField K)
       (AJ (GenericField K) C.1)),
       (∑ v∈W,CE v.val (coordinate (GenericField K) C.1)
         (flagSupport unitYZFlag))≤
         (U.family.toFE.yzCost C:ℤ):=by
     intro W
     change (∑ v∈W,CE v.val (coordinate (GenericField K) C.1)
       (flagSupport unitYZFlag))≤
       (DQ (GenericField K) (AJ (GenericField K) C.1)
         (U.family.yzProjection C):ℤ)
     calc
       _=∑ v∈W,RCN346.poleOrder (GenericField K)
           (AJ (GenericField K) C.1) v
           (FT (GenericField K) (AJ (GenericField K) C.1)
             (U.family.yzProjection C)):=by
         apply Finset.sum_congr rfl
         intro v _
         exact U.family.yzPole_eq C v
       _≤_:=PY (GenericField K)
         (AJ (GenericField K) C.1) (U.family.yzProjection C) W
   have hprofileYZ:=AIK
     S hTail (x i) (S.u0 i) (S.u1 i) hproper C
     bound seedCap slopeCap (U.family.toFE.yzCost C)
     hw hshort hchar hbox hyzC
   have hprofile:AHG (AL K) C.1 S.F
       (BJT S (x i) (S.u0 i) (S.u1 i) C)
       (AIC S (x i) (S.u0 i) (S.u1 i) C) w (cost C):=by
     intro W
     exact (hprofileYZ W).trans (by
       change (U.family.toFE.yzCost C:ℤ)≤
         ((U.family.toFE.zCost C+
           U.family.toFE.yzCost C:ℕ):ℤ)
       exact_mod_cast Nat.le_add_left _ _)
   have hcost:1≤cost C:=
     U.one_le_zCost_add_yzCost (AL K) S.F rfl S.RR C
   apply VP
     (AL K) C.1 S.F
     (BJT S (x i) (S.u0 i) (S.u1 i) C)
     (AIC S (x i) (S.u0 i) (S.u1 i) C)
     (base C) p w agreements e (cost C) S.WG hwa hcost hprofile
     S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
   · intro γ hγ
     exact S.degree_le γ (hGcΓ hγ)
   · intro γ hγ
     exact S.solution γ (hGcΓ hγ)
   · intro γ hγ
     exact S.regular γ (hGcΓ hγ)
   · intro γ hγ
     exact MC (GenericField K) S.G T
       (CR (AL K) S.F) Gi
       (DK (AL K) S.selected) C γ hγ
   · intro γ hγ
     have hΓ:=hGcΓ hγ
     exact hagreement γ hΓ
   · exact KX S.selected Γ Gc w e hGcΓ S.BNN
 · have hz:=U.family.ARJ
   have hyz:=U.family.ALE
   change (∑ C,U.family.toFE.zCost C)≤
     flagMixed flag (DL (support a b s) w) unitZFlag at hz
   change (∑ C,U.family.toFE.yzCost C)≤
     flagMixed flag (DL (support a b s) w) unitYZFlag at hyz
   have hz':=hz.trans (BLY a b s w flag unitZFlag)
   have hyz':=hyz.trans (BLY a b s w flag unitYZFlag)
   have hz'':=hz'.trans (BRQ flag a b s w unitZFlag)
   have hyz'':=hyz'.trans (BRQ flag a b s w unitYZFlag)
   change (∑ C,(U.family.toFE.zCost C+
     U.family.toFE.yzCost C))≤IY flag a b s w
   rw [Finset.sum_add_distrib]
   exact Nat.add_le_add hz'' hyz''
end
end BRK
end MergedPart8
section MergedPart9
namespace VN

open RCN095 RCN146
open Lower80788.FixedStage
open Lower80788.YM

def newNormal (f:FlagDegree) (a b s:ℕ):ℕ:=
  flagMixed f (reducedABS a b s)
    (rationalABS a b s+131071 • unitAllFlag)

def newCost (f:FlagDegree) (a b s:ℕ):ℕ:=
  newNormal f a b s+65539*flagMixed f (mfibABS a b s) (mcutABS a b s)

end VN
end MergedPart9
section MergedPart10
namespace BHY
open RCN095 RCN146 Lower80788.YM
open VN (newCost newNormal)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem FMP (f:FlagDegree) (a b s:ℕ) (_ha:0≤a)
    (hb:1≤b) (hs:1≤s):
    131073*80910*ProximityPrize.SubmissionLower.RCN146.IY f a b s 131071≤
      50164*newCost f a b s:=by
  obtain ⟨b',rfl⟩: ∃b',b=b'+1:=⟨b-1,by omega⟩
  obtain ⟨s',rfl⟩: ∃s',s=s'+1:=⟨s-1,by omega⟩
  change 131073*80910*ProximityPrize.SubmissionLower.RCN146.IY f a (b'+1) (s'+1)
    Lower80788.YM.w≤_
  rw [Lower80788.YM.APP]
  simp [newCost,newNormal,reducedABS,rationalABS,mfibABS,mcutABS,
    flagMixed,unitAllFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all]
  ring_nf
  omega

end BHY
end MergedPart10
section MergedPart11
namespace UF

open scoped Classical BigOperators
open RCN135 RCN136 RCN139 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095
open RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312
open RCN339 RCN330 RCN174 RCN319 RCN206 RCN287 RCN066 RCN338 RCN199 RCN207
open RCN271 RCN313 RCN234 RCN156 RCN341 RCN085 RCN087 RCN203 RCN084 RCN335
open FA GJ IB
open ND JN

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def bound (flag:FlagDegree) (t y r:ℕ):ℕ:=
  flagMixed flag (TX t y r) (ID.cellNormal t y r)+
    65539*flagMixed flag (BZO t y r) (BUV t y r)

theorem bound_eq_abs (flag:FlagDegree) (t y r:ℕ)
    (hr3:3≤r) (hb:r+2≤y):
    bound flag t y r=VN.newCost flag
      (cellA t y) (cellB y r) (cellS r):=by
  have hfirst:=CWF.GTP t y r
  have hnormal:ID.cellNormal t y r=
      Lower80788.YM.rationalABS (cellA t y) (cellB y r) (cellS r)+
        131071 • unitAllFlag:=by
    unfold ID.cellNormal
    rw [JE.CML t y r hr3 hb,
      CWF.FKK]
    rfl
  have hfiber:BZO t y r=
      Lower80788.YM.mfibABS (cellA t y) (cellB y r) (cellS r):=rfl
  have hrat:cellRational t y r=
      Lower80788.YM.rationalABS (cellA t y) (cellB y r) (cellS r):=
    CWF.FKK t y r
  have hcut:BUV t y r=
      Lower80788.YM.mcutABS (cellA t y) (cellB y r) (cellS r):=by
    simp only [BUV,Lower80788.YM.mcutABS,hrat,
      RCN327.w,Nat.reduceAdd,Nat.reduceMul]
  unfold bound VN.newCost VN.newNormal
  rw [hfirst,hnormal,hfiber,hcut]

variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433
variable {Gamma:Finset K} {x:I→K} {flag:FlagDegree}

theorem GTE (D t y r:ℕ)
    (hDlow:131072≤D) (hDchar:D<2130706433)
    (hr3:3≤r) (hb:r+2≤y) (hyt:y≤t)
    (hRcap:r≤32) (hYcap:y≤149) (hTcap:t≤8121)
    (hSafe:ABO.Safe r y)
    (S:FH (AL K) Gamma x 2130706433 80909 flag
      w (cellSupport t y r))
    (hnodes:S.nodes.card=181235+80909)
    (hagreement: ∀gamma ∈ Gamma,181235≤(S.AJW gamma).card)
    (hbox:S.F ∈ BA K D w t r)
    (hflag:flag.all≤r∧flag.yz+flag.all≤y∧
      flag.zOnly+flag.yz+flag.all≤t):
    Gamma.card≤bound flag t y r:=by
  have hflagChar:flag.yz+flag.all<2130706433∧flag.all<2130706433∧
      flag.zOnly+flag.yz+flag.all<2130706433:=by omega
  have hshort:w+1≤D:=by simpa only [RCN327.w] using hDlow
  have hb1:1≤cellB y r:=by dsimp [cellB];omega
  have hs1:1≤cellS r:=by dsimp [cellS];omega
  by_cases hTail:S.G ∣ _Q2 (AL K) S.F (w+1)
  · have hTailNumerator:S.G ∣ surfaceMap (AL K)
        (numerator K S.F (w+1)):=
      (AWJ (AL K)
        (DI K) S.F (w+1) S.G).mp hTail
    have hidentityGate:=ABO.EJG flag t y r hSafe hflag.1 hflag.2.1
    have hprovider:=BRK.AAB
      (a:=cellA t y) (b:=cellB y r) (s:=cellS r) S 181235 hnodes hagreement
      (by norm_num [RCN327.w]) hTailNumerator D t r
      (by norm_num [RCN327.w]) hshort hDchar hbox hflagChar hidentityGate
    have hpositive:1≤ProximityPrize.SubmissionLower.RCN146.IY flag (cellA t y) (cellB y r)
        (cellS r) w:=by
      apply Lower80788.FixedStage.CVP
      have hy:0<S.G.degreeOf 1:=S.y_dependent
      have hdeg:=AHE S.G flag S.flag_support 1
      omega
    have hinc:=AQH S 181235
      (ProximityPrize.SubmissionLower.RCN146.IY flag (cellA t y) (cellB y r) (cellS r) w)
      hprovider hagreement (by norm_num [RCN327.w])
      (by rw [hnodes];norm_num [RCN327.w]) hpositive
    have habsorb:=BHY.FMP flag
      (cellA t y) (cellB y r) (cellS r) (Nat.zero_le _) hb1 hs1
    have hscaled:Gamma.card*50164≤50164*bound flag t y r:=by
      calc
        Gamma.card*50164=Gamma.card*(181235-w):=by norm_num [RCN327.w]
        _≤(S.nodes.card-w)*(80909+1)*
            ProximityPrize.SubmissionLower.RCN146.IY flag (cellA t y) (cellB y r) (cellS r) w:=hinc
        _=131073*80910*
            ProximityPrize.SubmissionLower.RCN146.IY flag (cellA t y) (cellB y r) (cellS r) 131071:=by
          rw [hnodes]
          norm_num [RCN327.w]
        _≤50164*VN.newCost flag
            (cellA t y) (cellB y r) (cellS r):=habsorb
        _=50164*bound flag t y r:=by rw [bound_eq_abs flag t y r hr3 hb]
    apply Nat.le_of_mul_le_mul_right ?_ (by decide:0<50164)
    simpa only [Nat.mul_comm] using hscaled
  · have hmixedRed:=ABO.reduced_gate flag t y r hSafe hflag.1 hflag.2.1
    have hmix:2*(flag.zOnly+flag.yz+flag.all)*
        (cellA t y+cellB y r+cellS r+4)<2130706433:=by
      have hf:flag.zOnly+flag.yz+flag.all≤8121:=hflag.2.2.trans hTcap
      have ht:cellA t y+cellB y r+cellS r+4≤8122:=by
        dsimp [cellA,cellB,cellS]
        omega
      exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hf) ht).trans_lt (by decide)
    have hrationalGate:80909+1≤(ID.cellNormal t y r).yz:=by
      have hv:2≤y-r:=by omega
      simp only [ID.cellNormal,JE.normalFlag,RCN327.w]
      omega
    have htangent: ∀C:CM S,
        (∀delay,_Q2 (AL K) S.F (w+1+delay) ∈ C.1)→
        (HF (GenericField K) S.G
          (_Q2 (AL K) S.F (w+1))
          (CR (AL K) S.F) Gamma
          (DK (AL K) S.selected) C).card≤
            (80909+1)*
              (KF.MQ S hTail hflagChar hmixedRed).yzCost C:=by
      intro C hall
      exact ALX S C hTail
        (KF.AHP S hTail hflagChar hmixedRed C)
        181235 D t r hnodes hagreement
        (by norm_num [RCN327.w]) (by norm_num [RCN327.w]) hshort hDchar hbox
        (KF.MQ S hTail hflagChar hmixedRed)
        (KF.ADY S hTail hflagChar hmixedRed C)
        hall
        (KF.AJM S hTail hflagChar hmixedRed C)
    obtain ⟨provider⟩:=DHS.GHP hr3 hb hyt
      (by norm_num [RCN327.w]) S hTail hflagChar hmixedRed hmix hrationalGate htangent
    exact BIF S provider

end
end UF
end MergedPart11

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace QH
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 DY
open AAJ FA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.FJ
def padA (p:FlagDegree):ℕ:=padT p-padY p
def padB (p:FlagDegree):ℕ:=padY p-padS p-1
def padSlope (p:FlagDegree):ℕ:=padS p-2
theorem pad_sums (p:FlagDegree):
    padSlope p+2=padS p∧
    padB p+padSlope p+3=padY p∧
    padA p+padB p+padSlope p+3=padT p:=by
  have hs:2≤padS p:=le_max_right _ _
  have hy:padS p+1≤padY p:=le_max_right _ _
  have ht:padY p≤padT p:=le_max_right _ _
  dsimp [padA,padB,padSlope]
  omega
theorem GKV (p:FlagDegree) (d:ℕ):
    CI (RCN198.support (padA p) (padB p) (padSlope p)) d=
      paddedTail p d:=by
  have hc:=pad_sums p
  have hs:2≤padS p:=le_max_right _ _
  simp only [CI,UH,
    RCN198.support,hc.1,hc.2.1,hc.2.2,paddedTail]
  have he:2*padS p-2=2*(padS p-1):=by omega
  rw [he]
theorem own_support (F:P4):
    KW
      (RCN198.support (padA (FX F))
        (padB (FX F)) (padSlope (FX F))) F:=by
  have hc:=GX F
  have hp:=pad_sums (FX F)
  refine ⟨?_,?_,?_⟩
  · change wt BE F≤padSlope (FX F)+2
    rw [hp.1,← hc.1]
    exact le_max_left _ _
  · change wt BC F≤
      padB (FX F)+padSlope (FX F)+3
    rw [hp.2.1,← hc.2.1]
    exact le_max_left _ _
  · change wt AT F≤padA (FX F)+
      padB (FX F)+padSlope (FX F)+3
    rw [hp.2.2,← hc.2.2]
    exact le_max_left _ _
theorem own_box (F:P4) (D w L s:ℕ)
    (hbox:F ∈ RCN174.BA K D w L s):
    F ∈ RCN174.BA K D w
      (padA (FX F)+padB (FX F)+
        padSlope (FX F)+3)
      (padSlope (FX F)+2):=by
  have hs:=(own_support F).s_weight
  have ht:=(own_support F).total_weight
  intro d hd
  have hds:=(MvPolynomial.le_weightedTotalDegree BE hd).trans hs
  have hdt:=(MvPolynomial.le_weightedTotalDegree AT hd).trans ht
  rw [weight_fin4] at hds hdt
  simp only [BE,AT,RCN198.support,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero] at hds hdt
  exact ⟨by omega,hds,(hbox hd).2.2⟩
theorem EQE {P:BT} (Q:P4) (hQ:Q ≠ 0)
    (HQ:KW P Q) (R:RegularIndex Q):
    KW P R.1:=by
  have hd:=(RCN167.KR Q R.1 R.2).2.1
  exact ⟨(IQ BE R.1 Q hd hQ).trans HQ.s_weight,
    (IQ BC R.1 Q hd hQ).trans HQ.ys_weight,
    (IQ AT R.1 Q hd hQ).trans HQ.total_weight⟩
theorem EMS (p:FlagDegree)
    (hs:p.all≤32) (hy:middle p≤149) (ht:total p≤8121):
    padSlope p+2≤32∧padB p+padSlope p+3≤149∧
      padA p+padB p+padSlope p+3≤8121:=by
  have hp:=pad_sums p
  have hps:padS p≤32:=max_le hs (by decide)
  have hpy:padY p≤149:=max_le hy (by omega)
  have hpt:padT p≤8121:=max_le ht (by omega)
  rw [hp.1,hp.2.1,hp.2.2]
  exact ⟨hps,hpy,hpt⟩
theorem FGP
    (D:ℕ) (P:BT)
    (hDlow:131072≤D) (hDhigh:D<2130706433)
    (hS:P.s≤32) (hY:P.ys≤149) (hT:P.total≤8121)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.BA K D 131071 P.total P.s)
    (HQ:KW P Q)
    (selected:K→Polynomial K) (Gamma:Finset K) (u0 u1:I→K)
    (hdegree:∀gamma ∈ Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (R:RegularIndex Q)
    (hhyb: ¬UG (BG Q R)):
    (regularSeeds Q selected Gamma R).card≤
      paddedCost 131072 131073 (BG Q R):=by
  letI:CharP (GenericField K) 2130706433:=MP K 2130706433
  let p:=BG Q R
  let a:=padA p
  let b:=padB p
  let s:=padSlope p
  have hlow:=AFL.FLH p hhyb
  have hRdata:=ALY Q R.1 hQ D 131071 P.total P.s hbox R.2
  have hRsmall:R.1.degreeOf (2:Fin 4)<2130706433:=
    (UY _ _ _ _ _ hRdata.2.2).trans_lt
      (hS.trans_lt (by decide))
  have hRbox:=own_box R.1 D 131071 P.total P.s hRdata.2.2
  have hRsupport:=own_support R.1
  have hRwhole:=EQE Q hQ HQ R
  have hc:=GX R.1
  have hparam:s+2≤32∧b+s+3≤149∧a+b+s+3≤8121:=by
    apply EMS p
    · exact hRwhole.s_weight.trans hS
    · simpa only [p,middle,BG,hc.2.1] using
        hRwhole.ys_weight.trans hY
    · simpa only [p,total,BG,hc.2.2] using
        hRwhole.total_weight.trans hT
  have hsolutions:∀gamma ∈ regularSeeds Q selected Gamma R,
      BM K (selected gamma) gamma R.1=0:=by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover:=AAD K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage (g:EX K R.1):
      (KK K R.1 selected (regularSeeds Q selected Gamma R) g).card≤
        flagMixed (CO K g) (paddedTail p 131072)
          (paddedTail p 131073):=by
    let S0:=AVD (RCN198.support a b s) Q selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn hdegree hno R
      hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
    let S:=BJP S0 (AES g.1)
    have hsub:KK K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma:=
      (WK K R.1 selected _ g).trans (ACS Q selected Gamma R)
    have hnodes:S.nodes.card=181235+80909:=by
      change (Finset.univ:Finset I).card=_
      norm_num [I,IRSProfile.Index]
    have hag:∀gamma ∈ KK K R.1 selected
        (regularSeeds Q selected Gamma R) g,181235≤(S.AJW gamma).card:=by
      intro gamma hgamma
      exact hagreement gamma (hsub hgamma)
    have hf:=AER R.1 hRdata.1.ne_zero hRsupport g
    have hcount:=AJN.GFO D a b s
      hDlow hDhigh hparam.1 hparam.2.1 hparam.2.2 hlow S hnodes hag hRbox hf
    simpa only [AJN.firstTail,AJN.secondTail,
      AJN.w,Nat.reduceAdd,CO,
      a,b,s,GKV] using hcount
  calc
    (regularSeeds Q selected Gamma R).card≤
        ∑ g:EX K R.1,
          (KK K R.1 selected (regularSeeds Q selected Gamma R) g).card:=hcover
    _≤ ∑ g:EX K R.1,
        flagMixed (CO K g) (paddedTail p 131072)
          (paddedTail p 131073):=Finset.sum_le_sum (fun g _=>hstage g)
    _≤paddedCost 131072 131073 p:=by
      have hb:=VD R.1 hRdata.1.ne_zero
      exact DY.sum_mixed_le (CO K) p _ _
        hb.1 hb.2.1 hb.2.2

theorem EIR
    (D:ℕ) (P:BT)
    (hDlow:131072≤D) (hDhigh:D<2130706433)
    (hS:P.s≤32) (hY:P.ys≤149) (hT:P.total≤8121)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.BA K D 131071 P.total P.s)
    (HQ:KW P Q)
    (selected:K→Polynomial K) (Gamma:Finset K) (u0 u1:I→K)
    (hdegree: ∀gamma ∈ Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (R:RegularIndex Q)
    (hSafe:ABO.Safe (BG Q R).all (middle (BG Q R)))
    (hhyb:UG (BG Q R)):
    (regularSeeds Q selected Gamma R).card≤
      UF.bound (BG Q R)
        (total (BG Q R)) (middle (BG Q R))
        (BG Q R).all:=by
  letI:CharP (GenericField K) 2130706433:=MP K 2130706433
  set p:=BG Q R with hp
  have hRdata:=ALY Q R.1 hQ D 131071 P.total P.s hbox R.2
  have hRsmall:R.1.degreeOf (2:Fin 4)<2130706433:=
    (UY _ _ _ _ _ hRdata.2.2).trans_lt
      (hS.trans_lt (by decide))
  have hRbox0:R.1 ∈ RCN174.BA K D 131071
      (padA p+padB p+padSlope p+3) (padSlope p+2):=
    own_box R.1 D 131071 P.total P.s hRdata.2.2
  have hRsupport:KW
      (RCN198.support (padA p) (padB p) (padSlope p)) R.1:=own_support R.1
  have hRwhole:=EQE Q hQ HQ R
  have hc:=GX R.1
  have hps:=pad_sums p
  have hRbox:R.1 ∈ RCN174.BA K D 131071 (padT p) (padS p):=by
    rw [← hps.2.2,← hps.1]
    exact hRbox0
  have h1:p.all≤32:=hRwhole.s_weight.trans hS
  have h2:middle p≤149:=by
    simpa only [hp,middle,BG,hc.2.1] using
      hRwhole.ys_weight.trans hY
  have h3:total p≤8121:=by
    simpa only [hp,total,BG,hc.2.2] using
      hRwhole.total_weight.trans hT
  have hpS:padS p≤32:=max_le h1 (by decide)
  have hpY:padY p≤149:=max_le h2 (by omega)
  have hpT:padT p≤8121:=max_le h3 (by omega)
  have hp3:3≤p.all:=hhyb.1
  have hpSeq:padS p=p.all:=max_eq_left (by omega:2≤p.all)
  have hpYeq:padY p=middle p:=
    max_eq_left (by rw [hpSeq];exact hhyb.2.trans' (by omega))
  have hpTeq:padT p=total p:=by
    unfold padT
    rw [hpYeq]
    exact max_eq_left (by dsimp [total,middle];omega)
  have hpS3:3≤padS p:=by rw [hpSeq];exact hhyb.1
  have hhyb' :padS p+2≤padY p:=by rw [hpSeq,hpYeq];exact hhyb.2
  have hpyt:padY p≤padT p:=le_max_right _ _
  have hsolutions: ∀gamma ∈ regularSeeds Q selected Gamma R,
      BM K (selected gamma) gamma R.1=0:=by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover:=AAD K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage (g:EX K R.1):
      (KK K R.1 selected (regularSeeds Q selected Gamma R) g).card≤
        UF.bound (CO K g)
          (padT p) (padY p) (padS p):=by
    let S0:=AVD
      (RCN198.support (padA p) (padB p) (padSlope p)) Q selected Gamma
      (Finset.univ:Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn hdegree hno R
      hRdata.1 hRdata.2.1 hRsmall hRsupport (by decide) g
    let S:=BJP S0 (AES g.1)
    have hsub:KK K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma:=
      (WK K R.1 selected _ g).trans
        (ACS Q selected Gamma R)
    have hnodes:S.nodes.card=181235+80909:=by
      change (Finset.univ:Finset I).card=_
      norm_num [I,IRSProfile.Index]
    have hag: ∀gamma ∈ KK K R.1 selected
        (regularSeeds Q selected Gamma R) g,
        181235≤(S.AJW gamma).card:=by
      intro gamma hgamma
      exact hagreement gamma (hsub hgamma)
    have hf:=AER R.1 hRdata.1.ne_zero hRsupport g
    have hf1:(CO K g).all≤padSlope p+2:=hf.1
    have hf2:(CO K g).yz+
        (CO K g).all≤padB p+padSlope p+3:=hf.2.1
    have hf3:(CO K g).zOnly+
        (CO K g).yz+(CO K g).all≤
          padA p+padB p+padSlope p+3:=hf.2.2
    have hf' :(CO K g).all≤padS p∧
        (CO K g).yz+(CO K g).all≤padY p∧
        (CO K g).zOnly+(CO K g).yz+
          (CO K g).all≤padT p:=by
      refine ⟨?_,?_,?_⟩<;>omega
    have hcount:=UF.GTE D (padT p) (padY p) (padS p)
      hDlow hDhigh hpS3 hhyb' hpyt hpS hpY hpT (by rw [hpSeq,hpYeq];exact hSafe) S hnodes hag hRbox hf'
    simpa only [CO] using hcount
  have hsum:
      (∑ g:EX K R.1,
        UF.bound (CO K g)
          (padT p) (padY p) (padS p))≤
        UF.bound p (padT p) (padY p) (padS p):=by
    have hb:=VD R.1 hRdata.1.ne_zero
    unfold UF.bound
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    exact Nat.add_le_add
      (DY.sum_mixed_le (CO K) p _ _
        hb.1 hb.2.1 hb.2.2)
      (Nat.mul_le_mul_left 65539
        (DY.sum_mixed_le (CO K) p _ _
          hb.1 hb.2.1 hb.2.2))
  have hcount:=hcover.trans ((Finset.sum_le_sum (fun g _=>hstage g)).trans hsum)
  rwa [hpTeq,hpYeq,hpSeq] at hcount

def rawCost (p:FlagDegree):ℕ:=
  if UG p then
    UF.bound p (total p) (middle p) p.all
  else paddedCost 131072 131073 p

theorem EOZ
    (D:ℕ) (P:BT)
    (hDlow:131072≤D) (hDhigh:D<2130706433)
    (hS:P.s≤32) (hY:P.ys≤149) (hT:P.total≤8121)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.BA K D 131071 P.total P.s)
    (HQ:KW P Q)
    (selected:K→Polynomial K) (Gamma:Finset K) (u0 u1:I→K)
    (hdegree: ∀gamma ∈ Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (R:RegularIndex Q)
    (hSafe:ABO.Safe (BG Q R).all (middle (BG Q R))):
    (regularSeeds Q selected Gamma R).card≤rawCost (BG Q R):=by
  unfold rawCost
  split_ifs with hhyb
  · exact EIR D P hDlow hDhigh hS hY hT Q hQ hbox HQ
      selected Gamma u0 u1 hdegree hagreement hno R hSafe hhyb
  · exact FGP D P hDlow hDhigh hS hY hT Q hQ hbox HQ
      selected Gamma u0 u1 hdegree hagreement hno R hhyb

end

end QH
end MergedPart0
section MergedPart1
namespace AMT
open RCN095 RCN146 DY FV
open AAJ FA
open VN Lower80788.YM
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section

def cost (r v z:ℕ):ℕ:=QH.rawCost (rawFlag r v z)

def high (r v z:ℕ):ℕ:=newCost ⟨z,v,r⟩ z (v-1) (r-2)

theorem high_mono (r v:ℕ):Monotone (high r v):=by
  intro a b hab
  simp only [high,newCost,newNormal,reducedABS,rationalABS,mfibABS,mcutABS,
    flagMixed,unitAllFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all]
  gcongr

theorem high_affine (r v z:ℕ):
    2*high r v (z+1)=high r v z+high r v (z+2):=by
  simp only [high,newCost,newNormal,reducedABS,rationalABS,mfibABS,mcutABS,
    flagMixed,unitAllFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all]
  ring

theorem hybrid_iff (r v z:ℕ):
    UG (rawFlag r v z) ↔ 3≤r∧2≤v:=by
  unfold UG rawFlag middle
  dsimp
  omega

theorem cost_eq_high (r v z:ℕ) (hr:3≤r) (hv:2≤v):
    cost r v z=high r v z:=by
  have ha:=(hybrid_iff r v z).mpr ⟨hr,hv⟩
  unfold cost QH.rawCost
  rw [if_pos ha]
  simp only [rawFlag_all,AVF,BTK]
  rw [UF.bound_eq_abs _ _ _ _ hr (by omega)]
  unfold high
  congr 1<;>simp only [rawFlag,total,middle,cellA,cellB,cellS]<;>omega

theorem cost_eq_old (r v z:ℕ) (h: ¬(3≤r∧2≤v)):
    cost r v z=UB.rawCost r v z:=by
  have ha: ¬UG (rawFlag r v z):=by
    simpa only [hybrid_iff] using h
  change QH.rawCost (rawFlag r v z)=
    AFI.ANG (rawFlag r v z)
  simp only [QH.rawCost,AFI.ANG,if_neg ha]

theorem cost_mono (r v:ℕ):Monotone (cost r v):=by
  intro a b hab
  by_cases h:3≤r∧2≤v
  · rw [cost_eq_high r v a h.1 h.2,cost_eq_high r v b h.1 h.2]
    exact high_mono r v hab
  · rw [cost_eq_old r v a h,cost_eq_old r v b h]
    exact UB.GML r v hab

end
theorem raw_affine (r v z:ℕ) (hr:1≤r) (hz:3≤z):
    cost r v z=cost r v 3+(cost r v 4-cost r v 3)*(z-3):=by
  apply UB.EIG _ (cost_mono r v) _ z hz
  intro n hn
  by_cases h:3≤r∧2≤v
  · rw [cost_eq_high r v (n+1) h.1 h.2,cost_eq_high r v n h.1 h.2,
      cost_eq_high r v (n+2) h.1 h.2]
    exact high_affine r v n
  · rw [cost_eq_old r v (n+1) h,cost_eq_old r v n h,cost_eq_old r v (n+2) h]
    exact UB.DWS r v n hr hn

end AMT
end MergedPart1

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace PS
open MvPolynomial BY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type*) [Field K]

def xWeights:Fin 4→ℕ:= ![1,0,0,0]

theorem FDT (d:Fin 4→₀ ℕ):
    Finsupp.weight xWeights (UL d)=
      Finsupp.weight AQO d:=by
  rw [RCN081.weight_fin4,RCN081.weight_fin4]
  simp [xWeights,AQO,UL]

theorem GBJ (m:ℕ) (P:Poly4 K):
    AtLeast xWeights m (AEV K P) ↔ AtLeast AQO m P:=by
  classical
  constructor
  · intro h d hd
    have hm:UL d ∈ (AEV K P).support:=by
      rw [AWQ]
      exact Finset.mem_image.mpr ⟨d,hd,rfl⟩
    simpa only [FDT] using h _ hm
  · intro h d hd
    rw [AWQ] at hd
    obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hd
    simpa only [FDT] using h e he

theorem FVB (m:ℕ) (P:Poly4 K):
    AtLeast xWeights m P ↔
      Polynomial.X^m ∣ MvPolynomial.finSuccEquiv K 3 P:=by
  classical
  rw [Polynomial.X_pow_dvd_iff]
  constructor
  · intro h n hn
    ext d
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    by_contra hc
    have hw:=h (Finsupp.cons n d) (MvPolynomial.mem_support_iff.mpr hc)
    rw [RCN081.weight_fin4] at hw
    simp [xWeights] at hw
    omega
  · intro h d hd
    by_contra hm
    have hm' :d 0<m:=by
      rw [RCN081.weight_fin4] at hm
      simpa [xWeights] using hm
    have hc:=congrArg (AddMonoidAlgebra.coeff · d.tail) (h (d 0) hm')
    rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hc
    have he:Finsupp.cons (d 0) d.tail=d:=by
      ext i
      fin_cases i<;>simp
    rw [he,MvPolynomial.coeff_zero] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc

def DRF (x u0 u1:K):
    Poly4 K→+*Polynomial (MvPolynomial (Fin 3) K):=
  (MvPolynomial.finSuccEquiv K 3).toRingHom.comp
    ((AEV K).comp ((AEV K).comp
      (localize K x u0 u1).toRingHom))

theorem EUV (x u0 u1:K) (m:ℕ) (P:Poly4 K):
    VE K x u0 u1 m P ↔
      Polynomial.X^m ∣ DRF K x u0 u1 P:=by
  change AtLeast localWeights m (localize K x u0 u1 P) ↔ _
  rw [← CWL K m,← GBJ K m,
    FVB K m]
  rfl

theorem FKY {P:Poly4 K} (hP:P ≠ 0):AEV K P ≠ 0:=by
  intro h
  have hs:=congrArg MvPolynomial.support h
  rw [AWQ] at hs
  simp only [MvPolynomial.support_zero,Finset.image_eq_empty] at hs
  exact hP (MvPolynomial.support_eq_empty.mp hs)

def delocalize (x u0 u1:K):Poly4 K→ₐ[K] Poly4 K:=
  MvPolynomial.aeval ![MvPolynomial.X 0-MvPolynomial.C x,
    MvPolynomial.X 1-MvPolynomial.C u0-MvPolynomial.X 3*MvPolynomial.C u1-
      MvPolynomial.X 2*(MvPolynomial.X 0-MvPolynomial.C x),
    MvPolynomial.X 2,MvPolynomial.X 3]

theorem FHU (x u0 u1:K) (P:Poly4 K):
    delocalize K x u0 u1 (localize K x u0 u1 P)=P:=by
  have he:(delocalize K x u0 u1).comp (localize K x u0 u1)=
      AlgHom.id K (Poly4 K):=by
    ext i
    fin_cases i<;>simp [delocalize,localize,DII]
  exact DFunLike.congr_fun he P

theorem BMT (x u0 u1:K) {P:Poly4 K} (hP:P ≠ 0):
    DRF K x u0 u1 P ≠ 0:=by
  have hl:localize K x u0 u1 P ≠ 0:=by
    intro h
    have:=congrArg (delocalize K x u0 u1) h
    rw [FHU,map_zero] at this
    exact hP this
  exact (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv K 3).injective).mpr
    (FKY K (FKY K hl))

def contactOrder (x u0 u1:K) (P:Poly4 K):ℕ:=
  (DRF K x u0 u1 P).natTrailingDegree

theorem AFE (x u0 u1:K) (m:ℕ) (P:Poly4 K) (hP:P ≠ 0):
    VE K x u0 u1 m P ↔ m≤contactOrder K x u0 u1 P:=by
  rw [EUV,Polynomial.X_pow_dvd_iff]
  constructor
  · intro h
    by_contra hm
    have hz:=h (contactOrder K x u0 u1 P) (by omega)
    exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr
      (BMT K x u0 u1 hP)) hz
  · intro h n hn
    apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
    exact lt_of_lt_of_le hn h

theorem GDO (x u0 u1:K) (P Q:Poly4 K) (hP:P ≠ 0) (hQ:Q ≠ 0):
    contactOrder K x u0 u1 (P*Q)=
      contactOrder K x u0 u1 P+contactOrder K x u0 u1 Q:=by
  unfold contactOrder
  rw [map_mul,Polynomial.natTrailingDegree_mul
    (BMT K x u0 u1 hP)
    (BMT K x u0 u1 hQ)]

theorem GGJ (x u0 u1:K) (m:ℕ) (P Q:Poly4 K) (hP:P ≠ 0):
    VE K x u0 u1 m (P*Q) ↔
      VE K x u0 u1 (m-contactOrder K x u0 u1 P) Q:=by
  by_cases hQ:Q=0
  · subst Q
    simp [VE,AtLeast]
  rw [AFE K x u0 u1 m _ (mul_ne_zero hP hQ),
    AFE K x u0 u1 _ Q hQ,GDO K x u0 u1 P Q hP hQ]
  omega

end
end PS
end MergedPart0
section MergedPart1
namespace PS
open MvPolynomial BY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type*) [Field K]

def VU (x u0 u1:K) (m:ℕ):Submodule K (Poly4 K):=
  (MvPolynomial.restrictSupport K {d | m≤Finsupp.weight localWeights d}).comap
    (localize K x u0 u1).toLinearMap

theorem FFQ (x u0 u1:K) (m:ℕ) (Q:Poly4 K):
    Q ∈ VU K x u0 u1 m ↔ VE K x u0 u1 m Q:=by
  rfl

def DZM (F:Poly4 K):Poly4 K→ₗ[K] Poly4 K where
  toFun Q:=F*Q
  map_add' Q R:=mul_add F Q R
  map_smul' a Q:=by simp [MvPolynomial.smul_eq_C_mul,mul_left_comm]

theorem DCA (x u0 u1:K) (m:ℕ) (F:Poly4 K) (hF:F ≠ 0):
    LinearMap.ker ((VU K x u0 u1 m).mkQ.comp
      (DZM K F))=
        VU K x u0 u1 (m-contactOrder K x u0 u1 F):=by
  ext Q
  simp only [LinearMap.mem_ker,LinearMap.comp_apply,Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change VE K x u0 u1 m (F*Q) ↔
    VE K x u0 u1 (m-contactOrder K x u0 u1 F) Q
  exact GGJ K x u0 u1 m F Q hF

def factorJetMap (x u0 u1:K) (m:ℕ) (F:Poly4 K) (hF:F ≠ 0):
    (Poly4 K ⧸ VU K x u0 u1 (m-contactOrder K x u0 u1 F))→ₗ[K]
      (Poly4 K ⧸ VU K x u0 u1 m):=
  (VU K x u0 u1 (m-contactOrder K x u0 u1 F)).liftQ
    ((VU K x u0 u1 m).mkQ.comp (DZM K F))
    (by rw [DCA K x u0 u1 m F hF])

theorem EXL (x u0 u1:K) (m:ℕ) (F:Poly4 K) (hF:F ≠ 0):
    Function.Injective (factorJetMap K x u0 u1 m F hF):=by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  rw [DCA K x u0 u1 m F hF]

end
end PS
end MergedPart1
section MergedPart2
namespace PS
open scoped BigOperators
open MvPolynomial BY RCN122
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type*) [Field K]

def ADM (x u0 u1:K) (m:ℕ) (F Q:Poly4 K):Prop:=
  ∃B:Poly4 K,VE K x u0 u1 m (Q-F*B)

theorem DQU
    (x u0 u1:K) (m:ℕ) (F Q:Poly4 K) (hF:F ≠ 0):
    ADM K x u0 u1 m F Q ↔
      (VU K x u0 u1 m).mkQ Q ∈
        LinearMap.range (factorJetMap K x u0 u1 m F hF):=by
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨Submodule.Quotient.mk B,?_⟩
    change (Submodule.Quotient.mk (F*B):Poly4 K ⧸ VU K x u0 u1 m)=
      Submodule.Quotient.mk Q
    symm
    exact (Submodule.Quotient.eq _).mpr hB
  · rintro ⟨q,hq⟩
    obtain ⟨B,rfl⟩:=Submodule.Quotient.mk_surjective _ q
    refine ⟨B,?_⟩
    apply (Submodule.Quotient.eq (VU K x u0 u1 m)).mp
    exact hq.symm

theorem CVC
    (F Q:Poly4 K) (f:Polynomial K) (x u0 u1 gamma:K) (m:ℕ)
    (hF:BM K f gamma F=0)
    (hagrees:f.eval x=u0+gamma*u1)
    (hcontact:ADM K x u0 u1 m F Q):
    (Polynomial.X-Polynomial.C x)^m ∣ BM K f gamma Q:=by
  obtain ⟨B,hB⟩:=hcontact
  have ht:=ACJ K (Q-F*B) f x u0 u1 gamma m hagrees
    ((QW K x u0 u1 m (Q-F*B)).mp hB)
  simp only [map_sub,map_mul,hF,zero_mul,sub_zero] at ht
  exact (RCN185.ZJ
    (BM K f gamma Q) x m).mpr (Polynomial.X_pow_dvd_iff.mp ht)

theorem CII
    {I:Type*} (F Q:Poly4 K) (f:Polynomial K) (gamma:K)
    (nodes:I ↪ K) (u0 u1:I→K) (support:Finset I) (m:I→ℕ)
    (hF:BM K f gamma F=0)
    (hagrees: ∀i ∈ support,f.eval (nodes i)=u0 i+gamma*u1 i)
    (hcontact: ∀i ∈ support,
      ADM K (nodes i) (u0 i) (u1 i) (m i) F Q)
    (hdegree:(BM K f gamma Q).natDegree< ∑ i ∈ support,m i):
    BM K f gamma Q=0:=by
  classical
  by_contra hne
  have hmult: ∀i ∈ support,m i≤
      (BM K f gamma Q).rootMultiplicity (nodes i):=by
    intro i hi
    apply (Polynomial.le_rootMultiplicity_iff hne).mpr
    exact CVC K F Q f
      (nodes i) (u0 i) (u1 i) gamma (m i) hF (hagrees i hi) (hcontact i hi)
  have hsum:(∑ i ∈ support,m i)≤(BM K f gamma Q).natDegree:=by
    calc
      _≤ ∑ i ∈ support,(BM K f gamma Q).rootMultiplicity (nodes i):=
        Finset.sum_le_sum hmult
      _= ∑ a ∈ support.map nodes,(BM K f gamma Q).rootMultiplicity a:=
        (Finset.sum_map support nodes
          (fun a:K=>(BM K f gamma Q).rootMultiplicity a)).symm
      _≤_:= @RCN355._Q14 K inferInstance (Classical.decEq K)
        (BM K f gamma Q) (support.map nodes)
  omega

end
end PS
end MergedPart2
section MergedPart3
namespace BCB
open scoped BigOperators
open MvPolynomial RCN119
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

variable (K:Type*) [Field K]

def totalWeights:Fin 3→ℕ:=fun _=>1

theorem AXZ (M L s:ℕ) (p:RCN119.Poly K):
    p ∈ IN K M L s ↔
      p.degreeOf 0≤M∧weightedTotalDegree totalWeights p≤L∧p.degreeOf 1≤s:=by
  classical
  rw [IN,MvPolynomial.mem_restrictSupport_iff K]
  constructor
  · intro hp
    refine ⟨MvPolynomial.degreeOf_le_iff.mpr (fun d hd=>(hp hd).1),?_,
      MvPolynomial.degreeOf_le_iff.mpr (fun d hd=>(hp hd).2.2)⟩
    change p.support.sup (Finsupp.weight totalWeights)≤L
    apply Finset.sup_le
    intro d hd
    simpa [totalWeights,RCN372.weight_fin3] using (hp hd).2.1
  · rintro ⟨h0,ht,h1⟩ d hd
    have htot:Finsupp.weight totalWeights d≤L:=
      (Finset.le_sup (f:=Finsupp.weight totalWeights) hd).trans ht
    exact ⟨MvPolynomial.degreeOf_le_iff.mp h0 d hd,
      by simpa [totalWeights,RCN372.weight_fin3] using htot,
      MvPolynomial.degreeOf_le_iff.mp h1 d hd⟩

theorem GSZ:
    (IA K).degreeOf 0=1∧
      weightedTotalDegree totalWeights (IA K)=1∧
      (IA K).degreeOf 1=1:=by
  classical
  have hb:=(AXZ K 1 1 1 _).mp (BHI K)
  have h0:Finsupp.single (0:Fin 3) 1 ∈ (IA K).support:=by
    simp [MvPolynomial.mem_support_iff,IA]
  have h1:Finsupp.single (1:Fin 3) 1 ∈ (IA K).support:=by
    simp [MvPolynomial.mem_support_iff,IA]
  have hlo0:=MvPolynomial.degreeOf_le_iff.mp (le_refl ((IA K).degreeOf 0)) _ h0
  have hlo1:=MvPolynomial.degreeOf_le_iff.mp (le_refl ((IA K).degreeOf 1)) _ h1
  have hlot:=Finset.le_sup (f:=Finsupp.weight totalWeights) h0
  change Finsupp.weight totalWeights (Finsupp.single 0 1)≤
    weightedTotalDegree totalWeights (IA K) at hlot
  simp only [Finsupp.single_eq_same] at hlo0 hlo1
  have hlot' :1≤weightedTotalDegree totalWeights (IA K):=by
    simpa [totalWeights,RCN372.weight_fin3] using hlot
  exact ⟨Nat.le_antisymm hb.1 hlo0,Nat.le_antisymm hb.2.1 hlot',
    Nat.le_antisymm hb.2.2 hlo1⟩

theorem DEK (h:ℕ):
    (IA K^h).degreeOf 0=h∧
      weightedTotalDegree totalWeights (IA K^h)=h∧
      (IA K^h).degreeOf 1=h:=by
  have hd:=GSZ K
  have ht:weightedTotalDegree totalWeights (IA K^h)=h:=by
    induction h with
    | zero=>simp [MvPolynomial.weightedTotalDegree]
    | succ h ih=>
        rw [pow_succ,RCN071.AOD _ _ _
          (pow_ne_zero h (AAW K)) (AAW K),ih,hd.2.1]
  refine ⟨?_,ht,?_⟩
  · rw [MvPolynomial.degreeOf_pow_eq _ _ _ (AAW K),hd.1,mul_one]
  · rw [MvPolynomial.degreeOf_pow_eq _ _ _ (AAW K),hd.2.2,mul_one]

theorem ECA {M L s h:ℕ} (q:RCN119.Poly K)
    (hq:IA K^h*q ∈ IN K M L s):
    q ∈ IN K (M-h) (L-h) (s-h):=by
  by_cases hz:q=0
  · rw [hz];exact Submodule.zero_mem _
  have hn:=pow_ne_zero h (AAW K)
  have hb:=(AXZ K M L s _).mp hq
  have hd:=DEK K h
  have h0:=hb.1
  have ht:=hb.2.1
  have h1:=hb.2.2
  rw [MvPolynomial.degreeOf_mul_eq hn hz,hd.1] at h0
  rw [RCN071.AOD _ _ _ hn hz,hd.2.1] at ht
  rw [MvPolynomial.degreeOf_mul_eq hn hz,hd.2.2] at h1
  exact (AXZ K _ _ _ q).mpr ⟨by omega,by omega,by omega⟩

theorem EGD {M L s h:ℕ}
    (hM:h≤M) (hL:h≤L) (hs:h≤s):
    Function.Surjective (EII K hM hL hs):=by
  intro p
  have hp:contactJet K h p.val.val=0:=p.property
  obtain ⟨q,hq⟩:=(XA K h p.val.val).mp hp
  have hmem:q ∈ IN K (M-h) (L-h) (s-h):=by
    apply ECA K q
    rw [← hq]
    exact p.val.property
  refine ⟨⟨q,hmem⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hq.symm

theorem CPD {M L s h:ℕ}
    (hM:h≤M) (hL:h≤L) (hs:h≤s):
    Module.finrank K (LinearMap.range (blockJet K M L s h))+
      Module.finrank K (IN K (M-h) (L-h) (s-h))=
      Module.finrank K (IN K M L s):=by
  have he:=(LinearEquiv.ofBijective (EII K hM hL hs)
    ⟨CTX K hM hL hs,EGD K hM hL hs⟩).finrank_eq
  have hr:=(blockJet K M L s h).finrank_range_add_finrank_ker
  omega

theorem ATB (M L s h:ℕ) (hh:M<h∨s<h):
    LinearMap.ker (blockJet K M L s h)= ⊥ :=by
  apply le_antisymm ?_ bot_le
  intro p hp
  rw [Submodule.mem_bot]
  apply Subtype.ext
  change p.val=0
  by_contra hne
  have hz:contactJet K h p.val=0:=hp
  obtain ⟨q,hq⟩:=(XA K h p.val).mp hz
  have hqne:q ≠ 0:=by
    intro h
    apply hne
    rw [hq,h,mul_zero]
  have hn:=pow_ne_zero h (AAW K)
  have hb:=(AXZ K M L s p.val).mp p.property
  have h0:=hb.1
  have h1:=hb.2.2
  rw [hq,MvPolynomial.degreeOf_mul_eq hn hqne,(DEK K h).1] at h0
  rw [hq,MvPolynomial.degreeOf_mul_eq hn hqne,(DEK K h).2.2] at h1
  omega

theorem DEF (M L s h:ℕ) (hML:M≤L):
    Module.finrank K (LinearMap.range (blockJet K M L s h))=
      AAT M L s h:=by
  by_cases hM:h≤M
  · by_cases hs:h≤s
    · have hL:=hM.trans hML
      have he:=CPD K hM hL hs
      rw [ABG K M L s hML,
        ABG K (M-h) (L-h) (s-h) (Nat.sub_le_sub_right hML h)] at he
      have hm:M-h+1=M+1-h:=by omega
      have hl:L-h+1=L+1-h:=by omega
      have hs' :s-h+1=s+1-h:=by omega
      simp only [hm,hl,hs'] at he
      unfold AAT ALC TS
      omega
    · have hk:=ATB K M L s h (Or.inr (by omega))
      have he:=(blockJet K M L s h).finrank_range_add_finrank_ker
      rw [hk,finrank_bot,Nat.add_zero] at he
      rw [ABG K M L s hML] at he
      have hz:s+1-h=0:=by omega
      simpa [AAT,ALC,TS,hz] using he
  · have hk:=ATB K M L s h (Or.inl (by omega))
    have he:=(blockJet K M L s h).finrank_range_add_finrank_ker
    rw [hk,finrank_bot,Nat.add_zero] at he
    rw [ABG K M L s hML] at he
    have hz:M+1-h=0:=by omega
    simpa [AAT,ALC,TS,hz] using he

theorem EVA (m L s:ℕ):
    Module.finrank K (RCN100.LocalTarget K m L s)=ES m L s:=by
  change Module.finrank K ((r:Fin m)→LinearMap.range
    (blockJet K (min r.val L) L s (m-r.val)))=_
  rw [Module.finrank_pi_fintype]
  unfold ES
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro r _
  rw [DEF K _ _ _ _ (min_le_right _ _),
    RCN100.CYX]

end
end BCB
end MergedPart3
section MergedPart4
namespace MA
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 BY
open PS BCB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable (K:Type*) [Field K]

def unpackExponent (r:ℕ) (d:Fin 3→₀ ℕ):Fin 4→₀ ℕ:=
  Finsupp.cons (r-d 0) d

theorem monomial3_eq (d:Fin 3→₀ ℕ) (a:K):
    MvPolynomial.monomial d a=
      MvPolynomial.C a*MvPolynomial.X 0^d 0*
        MvPolynomial.X 1^d 1*MvPolynomial.X 2^d 2:=by
  have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
      Finsupp.single 2 (d 2):=by
    ext i;fin_cases i<;>simp
  conv_lhs=>rw [hd]
  rw [MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem EHC (r:ℕ) (d:Fin 3→₀ ℕ) (a:K)
    (hd:d 0≤r):
    EM K 0 0 0 (MvPolynomial.monomial (unpackExponent r d) a)=
      Polynomial.monomial r (MvPolynomial.monomial d a):=by
  rw [RCN122.monomial_eq K,monomial3_eq K,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul,map_pow]
  simp [unpackExponent,EM,AAP,seedAffine,
    Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq,mul_pow]
  simp only [show (Finsupp.cons (r-d 0) d) (1:Fin 4)=d 0 from rfl,
    show (Finsupp.cons (r-d 0) d) (2:Fin 4)=d 1 from rfl,
    show (Finsupp.cons (r-d 0) d) (3:Fin 4)=d 2 from rfl]
  conv_rhs=>rw [show r=(r-d 0)+d 0 by omega,pow_add]
  ring

def unpackBlock (r:ℕ):RCN119.Poly K→ₗ[K] Poly4 K:=
  (MvPolynomial.basisMonomials (Fin 3) K).constr K
    (fun d=>MvPolynomial.monomial (unpackExponent r d) 1)

theorem ETK (r:ℕ) (p:RCN119.Poly K):
    unpackBlock K r p= ∑ d ∈ p.support,
      p.coeff d • MvPolynomial.monomial (unpackExponent r d) (1:K):=by
  rw [unpackBlock,Module.Basis.constr_apply]
  rfl

theorem EXU (r:ℕ) (p:RCN119.Poly K)
    (hp:p.degreeOf 0≤r):
    EM K 0 0 0 (unpackBlock K r p)=Polynomial.monomial r p:=by
  classical
  rw [ETK,map_sum]
  have he: ∀d ∈ p.support,
      EM K 0 0 0
          (p.coeff d • MvPolynomial.monomial (unpackExponent r d) (1:K))=
        Polynomial.monomial r (MvPolynomial.monomial d (p.coeff d)):=by
    intro d hd
    simp only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
    exact EHC K r d (p.coeff d)
      (MvPolynomial.degreeOf_le_iff.mp hp d hd)
  rw [Finset.sum_congr rfl he]
  conv_rhs=>rw [MvPolynomial.as_sum p]
  simp only [map_sum]

theorem GHF (m L s:ℕ) (r:Fin m)
    (p:IN K (min r.val L) L s):
    unpackBlock K r.val p.val ∈ BA K m 1 L s:=by
  classical
  rw [ETK]
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
  left
  have hb:=p.property hd
  change d 0≤min r.val L∧d 0+d 1+d 2≤L∧d 1≤s at hb
  change d 0+d 1+d 2≤L∧d 1≤s∧(r.val-d 0)+1*d 0+(1-1)*d 1<m
  have hr:=r.isLt
  omega

abbrev LocalSource (m L s:ℕ):=
  (r:Fin m)→IN K (min r.val L) L s

def unpack (m L s:ℕ):LocalSource K m L s→ₗ[K] Poly4 K where
  toFun p:= ∑ r:Fin m,unpackBlock K r.val (p r).val
  map_add' p q:=by simp [map_add,Finset.sum_add_distrib]
  map_smul' a p:=by simp [map_smul,Finset.smul_sum]

theorem unpack_mem (m L s:ℕ) (p:LocalSource K m L s):
    unpack K m L s p ∈ BA K m 1 L s:=by
  change (∑ r:Fin m,unpackBlock K r.val (p r).val) ∈ _
  apply Submodule.sum_mem
  intro r _
  exact GHF K m L s r (p r)

theorem FPO (m L s:ℕ) (p:LocalSource K m L s):
    EM K 0 0 0 (unpack K m L s p)=
      ∑ r:Fin m,Polynomial.monomial r.val (p r).val:=by
  change EM K 0 0 0 (∑ r:Fin m,_)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply EXU
  exact ((AXZ K _ _ _ _).mp (p r).property).1.trans (min_le_left _ _)

theorem BVE (m L s:ℕ) (p:LocalSource K m L s) (r:Fin m):
    (EM K 0 0 0 (unpack K m L s p)).coeff r.val=(p r).val:=by
  classical
  rw [FPO,Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial,Fin.val_inj]
  simp

def sourceJet (m L s:ℕ):LocalSource K m L s→ₗ[K] LocalTarget K m L s:=
  LinearMap.pi fun r=>
    (blockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp (LinearMap.proj r)

theorem FFZ (m L s:ℕ):
    Function.Surjective (sourceJet K m L s):=by
  classical
  intro v
  choose p hp using fun r=>(v r).property
  refine ⟨p,?_⟩
  funext r
  apply Subtype.ext
  exact hp r

theorem FCM (m L s:ℕ) (p:LocalSource K m L s):
    sourceJet K m L s p=0 ↔ VE K 0 0 0 m (unpack K m L s p):=by
  rw [QW]
  constructor
  · intro h n
    by_cases hn:n<m
    · have hr:=congrArg (fun v:LocalTarget K m L s=>(v ⟨n,hn⟩).val) h
      have hz:contactJet K (m-n) (p ⟨n,hn⟩).val=0:=hr
      rw [BVE K m L s p ⟨n,hn⟩]
      exact (XA K (m-n) _).mp hz
    · simp [show m-n=0 by omega]
  · intro h
    funext r
    apply Subtype.ext
    change contactJet K (m-r.val) (p r).val=0
    apply (XA K (m-r.val) _).mpr
    have hr:=h r.val
    rw [BVE] at hr
    exact hr

def AXP (m L s:ℕ):LocalSource K m L s→ₗ[K]
    (Poly4 K ⧸ VU K 0 0 0 m):=
  (VU K 0 0 0 m).mkQ.comp (unpack K m L s)

theorem FRE (m L s:ℕ):
    LinearMap.ker (AXP K m L s)=LinearMap.ker (sourceJet K m L s):=by
  ext p
  simp only [LinearMap.mem_ker]
  change ((VU K 0 0 0 m).mkQ (unpack K m L s p)=0) ↔ _
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,FFQ,
    ← FCM]

theorem DVB (m L s:ℕ):
    Module.finrank K (LinearMap.range (AXP K m L s))=ES m L s:=by
  have hfull:=LinearMap.range_eq_top.mpr (FFZ K m L s)
  have hs:=(sourceJet K m L s).finrank_range_add_finrank_ker
  rw [hfull,finrank_top,EVA] at hs
  have hb:=(AXP K m L s).finrank_range_add_finrank_ker
  rw [FRE] at hb
  omega

end
end MA
end MergedPart4
section MergedPart5
namespace MA
open scoped BigOperators Pointwise
open MvPolynomial RCN119 RCN100 RCN122 BY
open RCN180 (encodeBox COX)
open PS BCB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable (K:Type*) [Field K]

def blocksOf {D w L s:ℕ} (m:ℕ) (Q:BA K D w L s):
    LocalSource K m L s:=
  fun r=>extractBlock K D w L s 0 0 0 r.val (encodeBox Q)

theorem EUQ {D w L s:ℕ} (m:ℕ)
    (Q:BA K D w L s) (r:Fin m):
    (blocksOf K m Q r).val=(EM K 0 0 0 Q.val).coeff r.val:=by
  rw [← COX Q,AMG]
  rfl

theorem ETB {D w L s:ℕ} (m:ℕ)
    (Q:BA K D w L s):
    VE K 0 0 0 m (Q.val-unpack K m L s (blocksOf K m Q)):=by
  rw [QW]
  intro r
  by_cases hr:r<m
  · rw [map_sub,Polynomial.coeff_sub,BVE K m L s _ ⟨r,hr⟩,
      EUQ,sub_self]
    exact dvd_zero _
  · simp [show m-r=0 by omega]

theorem CQZ {D w L s:ℕ} (m:ℕ)
    (Q:BA K D w L s):
    (VU K 0 0 0 m).mkQ Q.val ∈ LinearMap.range (AXP K m L s):=by
  refine ⟨blocksOf K m Q,?_⟩
  change (Submodule.Quotient.mk (unpack K m L s (blocksOf K m Q)):
      Poly4 K ⧸ VU K 0 0 0 m)=Submodule.Quotient.mk Q.val
  symm
  exact (Submodule.Quotient.eq _).mpr (ETB K m Q)

theorem GVF {D L s D' L' s' :ℕ} {F Q:Poly4 K}
    (hF:F ∈ BA K D 1 L s)
    (hQ:Q ∈ BA K D' 1 L' s'):
    F*Q ∈ BA K (D+D') 1 (L+L') (s+s'):=by
  have hset:AEC D 1 L s+AEC D' 1 L' s' ⊆
      AEC (D+D') 1 (L+L') (s+s'):=by
    rintro _ ⟨a,ha,b,hb,rfl⟩
    simp only [AEC,Set.mem_setOf_eq,Finsupp.add_apply,
      Nat.one_mul,Nat.sub_self,Nat.zero_mul,Nat.add_zero] at ha hb ⊢
    omega
  change F*Q ∈ MvPolynomial.restrictSupport K _
  apply MvPolynomial.restrictSupport_mono (R:=K) hset
  rw [MvPolynomial.restrictSupport_add]
  exact Submodule.mul_mem_mul hF hQ

theorem EGO {D L s L' s' :ℕ}
    (hL:L≤L') (hs:s≤s'):
    BA K D 1 L s≤BA K D 1 L' s' :=by
  apply MvPolynomial.restrictSupport_mono
  intro d hd
  exact ⟨hd.1.trans hL,hd.2.1.trans hs,hd.2.2⟩

theorem EOY
    {DF TF RF m L s:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF)
    (hT:TF≤L) (hR:RF≤s)
    (v:LinearMap.range (AXP K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF))):
    factorJetMap K 0 0 0 m F hF v.val ∈ LinearMap.range (AXP K m L s):=by
  obtain ⟨q,hq⟩:=v.property
  rw [← hq]
  change (VU K 0 0 0 m).mkQ
    (F*unpack K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF) q) ∈ _
  apply CQZ K (D:=DF+(m-contactOrder K 0 0 0 F))
    (w:=1) (L:=L) (s:=s) m
    ⟨F*unpack K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF) q,?_⟩
  exact EGO K (L':=L) (s':=s) (by omega) (by omega)
    (GVF K hbox (unpack_mem K _ _ _ q))

def CKR {DF TF RF m L s:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s):
    LinearMap.range (AXP K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF))→ₗ[K]
      LinearMap.range (AXP K m L s):=
  LinearMap.codRestrict _
    ((factorJetMap K 0 0 0 m F hF).comp
      (LinearMap.range (AXP K (m-contactOrder K 0 0 0 F) (L-TF) (s-RF))).subtype)
    (EOY K F hF hbox hT hR)

theorem EHB {DF TF RF m L s:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s):
    Function.Injective (CKR K (m:=m) F hF hbox hT hR):=by
  intro a b hab
  apply Subtype.ext
  apply EXL K 0 0 0 m F hF
  exact congrArg Subtype.val hab

abbrev AYQ {DF TF RF m L s:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s):=
  LinearMap.range (AXP K m L s) ⧸
    LinearMap.range (CKR K (m:=m) F hF hbox hT hR)

theorem EIU {DF TF RF m L s:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s):
    Module.finrank K (AYQ K (m:=m) F hF hbox hT hR)=
      ES m L s-
        ES (m-contactOrder K 0 0 0 F) (L-TF) (s-RF):=by
  have hi:=LinearMap.finrank_range_of_inj
    (EHB K (m:=m) F hF hbox hT hR)
  rw [DVB] at hi
  have hq:=(LinearMap.range
    (CKR K (m:=m) F hF hbox hT hR)).finrank_quotient_add_finrank
  rw [hi,DVB] at hq
  change Module.finrank K (AYQ K (m:=m) F hF hbox hT hR)+_=_ at hq
  omega

end
end MA
end MergedPart5
section MergedPart6
namespace MA
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 BY
open PS
open RCN234 (wt wt_C wt_X wt_add_le wt_mul_le wt_pow_le)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type*) [Field K]

def center (x u0 u1:K):Poly4 K→ₐ[K] Poly4 K:=
  MvPolynomial.aeval ![MvPolynomial.X 0+MvPolynomial.C x,
    MvPolynomial.X 1+MvPolynomial.C u0+MvPolynomial.X 3*MvPolynomial.C u1,
    MvPolynomial.X 2,MvPolynomial.X 3]

theorem DIB (x u0 u1:K) (Q:Poly4 K):
    center K (-x) (-u0) (-u1) (center K x u0 u1 Q)=Q:=by
  have he:(center K (-x) (-u0) (-u1)).comp (center K x u0 u1)=
      AlgHom.id K (Poly4 K):=by
    ext i
    fin_cases i<;>simp [center]<;>ring
  exact DFunLike.congr_fun he Q

theorem ARO (x u0 u1:K) {Q:Poly4 K} (hQ:Q ≠ 0):
    center K x u0 u1 Q ≠ 0:=by
  intro h
  have hc:=congrArg (center K (-x) (-u0) (-u1)) h
  rw [DIB,map_zero] at hc
  exact hQ hc

theorem EAA (x u0 u1:K) (m:ℕ) (Q:Poly4 K):
    VE K 0 0 0 m (center K x u0 u1 Q) ↔
      VE K x u0 u1 m Q:=by
  have he:(localize K 0 0 0).comp (center K x u0 u1)=localize K x u0 u1:=by
    ext i
    fin_cases i<;>simp [center,localize,DII]<;>ring
  unfold VE
  rw [show localize K 0 0 0 (center K x u0 u1 Q)=localize K x u0 u1 Q from
    DFunLike.congr_fun he Q]

theorem EES (x u0 u1:K) (Q:Poly4 K) (hQ:Q ≠ 0):
    contactOrder K 0 0 0 (center K x u0 u1 Q)=contactOrder K x u0 u1 Q:=by
  apply Nat.le_antisymm
  · apply (AFE K x u0 u1 _ Q hQ).mp
    apply (EAA K x u0 u1 _ Q).mp
    exact (AFE K 0 0 0 _ _ (ARO K x u0 u1 hQ)).mpr le_rfl
  · apply (AFE K 0 0 0 _ _ (ARO K x u0 u1 hQ)).mp
    apply (EAA K x u0 u1 _ Q).mpr
    exact (AFE K x u0 u1 _ Q hQ).mpr le_rfl

theorem FZD (phi:Poly4 K→ₐ[K] Poly4 K) (w:Fin 4→ℕ)
    (hvar: ∀i,wt w (phi (MvPolynomial.X i))≤w i) (Q:Poly4 K):
    wt w (phi Q)≤wt w Q:=by
  classical
  conv_lhs=>rw [MvPolynomial.as_sum Q,map_sum]
  apply RCN235.CLG
  intro d hd
  have hp (i:Fin 4):wt w (phi (MvPolynomial.X i)^d i)≤d i*w i:=
    (wt_pow_le w _ _).trans (Nat.mul_le_mul_left _ (hvar i))
  have hm:=wt_mul_le w (MvPolynomial.C (Q.coeff d)) (phi (MvPolynomial.X 0)^d 0)
  have hm1:=wt_mul_le w (MvPolynomial.C (Q.coeff d)*phi (MvPolynomial.X 0)^d 0)
    (phi (MvPolynomial.X 1)^d 1)
  have hm2:=wt_mul_le w
    (MvPolynomial.C (Q.coeff d)*phi (MvPolynomial.X 0)^d 0*phi (MvPolynomial.X 1)^d 1)
    (phi (MvPolynomial.X 2)^d 2)
  have hm3:=wt_mul_le w
    (MvPolynomial.C (Q.coeff d)*phi (MvPolynomial.X 0)^d 0*phi (MvPolynomial.X 1)^d 1*
      phi (MvPolynomial.X 2)^d 2) (phi (MvPolynomial.X 3)^d 3)
  have hc:phi (MvPolynomial.C (Q.coeff d))=MvPolynomial.C (Q.coeff d):=phi.commutes _
  rw [RCN122.monomial_eq K,map_mul,map_mul,map_mul,map_mul,hc]
  simp only [map_pow]
  have h0:=hp 0
  have h1:=hp 1
  have h2:=hp 2
  have h3:=hp 3
  rw [wt_C] at hm
  have hbound:=MvPolynomial.le_weightedTotalDegree w hd
  rw [RCN081.weight_fin4] at hbound
  change _≤wt w Q at hbound
  omega

theorem DHB (x u0 u1:K) (w:Fin 4→ℕ) (hw:w 3≤w 1) (Q:Poly4 K):
    wt w (center K x u0 u1 Q)≤wt w Q:=by
  apply FZD
  intro i
  simp only [center,MvPolynomial.aeval_X]
  fin_cases i
  · change wt w (MvPolynomial.X 0+MvPolynomial.C x)≤w 0
    exact (wt_add_le w _ _).trans (by simp [wt_X,wt_C])
  · change wt w (MvPolynomial.X 1+MvPolynomial.C u0+MvPolynomial.X 3*MvPolynomial.C u1)≤w 1
    apply (wt_add_le w _ _).trans
    apply max_le
    · exact (wt_add_le w _ _).trans (by simp [wt_X,wt_C])
    · exact (wt_mul_le w _ _).trans (by simpa [wt_X,wt_C] using hw)
  · change wt w (MvPolynomial.X 2:Poly4 K)≤w 2
    rw [wt_X]
  · change wt w (MvPolynomial.X 3:Poly4 K)≤w 3
    rw [wt_X]

theorem APS {D w L s:ℕ} (x u0 u1:K)
    (Q:BA K D w L s):
    center K x u0 u1 Q.val ∈ BA K D w L s:=by
  by_cases hz:Q.val=0
  · rw [hz,map_zero];exact Submodule.zero_mem _
  obtain ⟨d,hd⟩:=MvPolynomial.support_nonempty.mpr hz
  have hD:0<D:=lt_of_le_of_lt (Nat.zero_le _) (Q.property hd).2.2
  have hb:=(RCN180.JT Q.val D w L s hD).mp Q.property
  apply (RCN180.JT _ D w L s hD).mpr
  refine ⟨(DHB K x u0 u1 _ ?_ Q.val).trans hb.1,
    (DHB K x u0 u1 _ ?_ Q.val).trans hb.2.1,
    (DHB K x u0 u1 _ ?_ Q.val).trans hb.2.2⟩
  all_goals simp [RCN156.AT,RCN156.BE,RCN081.BV]

theorem EUT (x u0 u1:K) (m:ℕ) (F Q:Poly4 K):
    ADM K 0 0 0 m (center K x u0 u1 F) (center K x u0 u1 Q) ↔
      ADM K x u0 u1 m F Q:=by
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨center K (-x) (-u0) (-u1) B,?_⟩
    apply (EAA K x u0 u1 m _).mp
    rw [map_sub,map_mul]
    have he:center K x u0 u1 (center K (-x) (-u0) (-u1) B)=B:=by
      simpa using DIB K (-x) (-u0) (-u1) B
    rw [he]
    exact hB
  · rintro ⟨B,hB⟩
    refine ⟨center K x u0 u1 B,?_⟩
    rw [← map_mul,← map_sub]
    exact (EAA K x u0 u1 m _).mpr hB

end
end MA
end MergedPart6
section MergedPart7
namespace MA
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 BY
open PS
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable (K:Type*) [Field K]

def NodeTarget {DF TF RF m L s:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s)
    (x u0 u1:K):=
  AYQ K (m:=m) (center K x u0 u1 F) (ARO K x u0 u1 hF)
    (APS K x u0 u1 ⟨F,hbox⟩) hT hR

local instance nodeTargetAddCommGroup {DF TF RF m L s:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s)
    (x u0 u1:K):AddCommGroup (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1):=
  inferInstanceAs (AddCommGroup (AYQ K (m:=m) (center K x u0 u1 F)
    (ARO K x u0 u1 hF) (APS K x u0 u1 ⟨F,hbox⟩) hT hR))

local instance nodeTargetModule {DF TF RF m L s:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s)
    (x u0 u1:K):Module K (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1):=
  inferInstanceAs (Module K (AYQ K (m:=m) (center K x u0 u1 F)
    (ARO K x u0 u1 hF) (APS K x u0 u1 ⟨F,hbox⟩) hT hR))

local instance nodeTargetFinite {DF TF RF m L s:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s)
    (x u0 u1:K):Module.Finite K (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1):=
  inferInstanceAs (Module.Finite K (AYQ K (m:=m) (center K x u0 u1 F)
    (ARO K x u0 u1 hF) (APS K x u0 u1 ⟨F,hbox⟩) hT hR))

theorem FLG {DF TF RF m L s:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s)
    (x u0 u1:K):
    Module.finrank K (NodeTarget K (m:=m) F hF hbox hT hR x u0 u1)=
      ES m L s-ES (m-contactOrder K x u0 u1 F) (L-TF) (s-RF):=by
  change Module.finrank K (AYQ K (m:=m) (center K x u0 u1 F)
    (ARO K x u0 u1 hF) (APS K x u0 u1 ⟨F,hbox⟩) hT hR)=_
  rw [EIU,EES K x u0 u1 F hF]

def nodeJet (D w L s m:ℕ) (x u0 u1:K):
    BA K D w L s→ₗ[K] LinearMap.range (AXP K m L s):=
  LinearMap.codRestrict _
    ((VU K 0 0 0 m).mkQ.comp
      ((center K x u0 u1).toLinearMap.comp (BA K D w L s).subtype))
    (fun Q=>CQZ K m ⟨center K x u0 u1 Q.val,
      APS K x u0 u1 Q⟩)

def FKJ {DF TF RF m L s:ℕ} (D w:ℕ) (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s)
    (x u0 u1:K):
    BA K D w L s→ₗ[K] NodeTarget K (m:=m) F hF hbox hT hR x u0 u1:=
  (LinearMap.range (CKR K (m:=m) (center K x u0 u1 F)
    (ARO K x u0 u1 hF) (APS K x u0 u1 ⟨F,hbox⟩) hT hR)).mkQ.comp
      (nodeJet K D w L s m x u0 u1)

theorem EDW {DF TF RF m L s D w:ℕ}
    (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s)
    (x u0 u1:K) (Q:BA K D w L s)
    (hQ:FKJ K (m:=m) D w F hF hbox hT hR x u0 u1 Q=0):
    ADM K x u0 u1 m F Q.val:=by
  apply (EUT K x u0 u1 m F Q.val).mp
  apply (DQU K 0 0 0 m _ _
    (ARO K x u0 u1 hF)).mpr
  change (LinearMap.range (CKR K (m:=m) (center K x u0 u1 F)
    (ARO K x u0 u1 hF) (APS K x u0 u1 ⟨F,hbox⟩) hT hR)).mkQ
      (nodeJet K D w L s m x u0 u1 Q)=0 at hQ
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at hQ
  obtain ⟨v,hv⟩:=hQ
  exact ⟨v.val,congrArg Subtype.val hv⟩

def EFW {I:Type*} [Fintype I] {DF TF RF L s:ℕ}
    (D w:ℕ) (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s)
    (nodes u0 u1:I→K) (m:I→ℕ):
    BA K D w L s→ₗ[K]
      ((i:I)→NodeTarget K (m:=m i) F hF hbox hT hR (nodes i) (u0 i) (u1 i)):=
  LinearMap.pi fun i=>FKJ K (m:=m i) D w F hF hbox hT hR (nodes i) (u0 i) (u1 i)

theorem DKT {I:Type*} [Fintype I] {DF TF RF L s D w:ℕ}
    (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s)
    (nodes u0 u1:I→K) (m:I→ℕ) (Q:BA K D w L s)
    (hQ:EFW K D w F hF hbox hT hR nodes u0 u1 m Q=0):
    ∀i,ADM K (nodes i) (u0 i) (u1 i) (m i) F Q.val:=by
  intro i
  exact EDW K F hF hbox hT hR (nodes i) (u0 i) (u1 i) Q
    (congrFun hQ i)

set_option maxHeartbeats 300000 in
private theorem FBN
    {W:Type*} [AddCommGroup W] [Module K W] [Module.Finite K W]
    {TF RF D w L s nu:ℕ}
    (A:BA K D w L s→ₗ[K] W)
    (F:Poly4 K) (hF:F ≠ 0)
    (hcode:nu≤wt (RCN081.BV w) F)
    (htotal:TF≤wt RCN156.AT F)
    (hslope:RF≤wt RCN156.BE F)
    (hdim:AW (D-nu) w (L-TF) (s-RF)+
      Module.finrank K W<AW D w L s):
    ∃Q:BA K D w L s,¬F ∣ Q.val∧A Q=0:=by
  classical
  let V:=LinearMap.ker A
  let recon:V→ₗ[K] Poly4 K:=(BA K D w L s).subtype.comp V.subtype
  have hrecon:Function.Injective recon:=by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  by_contra hnone
  have hdiv: ∀v:V,F ∣ recon v:=by
    intro v
    by_contra hv
    apply hnone
    exact ⟨v.val,hv,v.property⟩
  have hquot (v:V):RCN180.ZK recon F hdiv v ∈
      BA K (D-nu) w (L-TF) (s-RF):=by
    let R:=RCN180.ZK recon F hdiv v
    have he:recon v=F*R:=RCN180.LR recon F hdiv v
    by_cases hz:R=0
    · change R ∈ _
      rw [hz]
      exact Submodule.zero_mem _
    have hn:recon v ≠ 0:=by rw [he];exact mul_ne_zero hF hz
    exact RCN180.ZP
      (recon v) F R D w L s nu TF RF hn hF hz v.val.property he hcode htotal hslope
  letI:Module.Finite K (BA K (D-nu) w (L-TF) (s-RF)):=
    RCN180.EGE (K:=K) (D-nu) w (L-TF) (s-RF)
  let divMap:V→ₗ[K] BA K (D-nu) w (L-TF) (s-RF):=
    LinearMap.codRestrict _ (RCN180.ARF (K:=K) (V:=V) recon F hF hdiv)
      (fun v=>by
        change RCN180.ZK recon F hdiv v ∈ _
        exact hquot v)
  have hdivMap:Function.Injective divMap:=by
    intro a b hab
    apply RCN180.BPR recon hrecon F hF hdiv
    exact congrArg Subtype.val hab
  have hupper:Module.finrank K V≤
      Module.finrank K (BA K (D-nu) w (L-TF) (s-RF)):=
    LinearMap.finrank_le_finrank_of_injective (f:=divMap) hdivMap
  have hupperCount:Module.finrank K V≤AW (D-nu) w (L-TF) (s-RF):=
    hupper.trans_eq (RCN180.BAD (K:=K) (D-nu) w (L-TF) (s-RF))
  have hnull:Module.finrank K A.range+Module.finrank K A.ker=AW D w L s:=
    A.finrank_range_add_finrank_ker.trans (RCN180.BAD (K:=K) D w L s)
  have hrange:=A.range.finrank_le
  change Module.finrank K A.ker≤_ at hupperCount
  have hcount:AW D w L s≤
      AW (D-nu) w (L-TF) (s-RF)+Module.finrank K W:=by
    rw [← hnull]
    exact (Nat.add_le_add hrange hupperCount).trans_eq (Nat.add_comm _ _)
  exact (Nat.not_le_of_gt hdim) hcount

theorem DSW
    {I:Type*} [Fintype I] {DF TF RF D w L s nu:ℕ}
    (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 TF RF) (hT:TF≤L) (hR:RF≤s)
    (hcode:nu≤wt (RCN081.BV w) F)
    (htotal:TF≤wt RCN156.AT F)
    (hslope:RF≤wt RCN156.BE F)
    (nodes u0 u1:I→K) (m:I→ℕ)
    (hdim:AW (D-nu) w (L-TF) (s-RF)+
      (∑ i:I,(ES (m i) L s-
        ES (m i-contactOrder K (nodes i) (u0 i) (u1 i) F) (L-TF) (s-RF)))<
      AW D w L s):
    ∃Q:Poly4 K,Q ∈ BA K D w L s∧ ¬F ∣ Q∧
      ∀i,ADM K (nodes i) (u0 i) (u1 i) (m i) F Q:=by
  classical
  let W:=(i:I)→NodeTarget K (m:=m i) F hF hbox hT hR (nodes i) (u0 i) (u1 i)
  have htarget:Module.finrank K W=
      ∑ i:I,(ES (m i) L s-
        ES (m i-contactOrder K (nodes i) (u0 i) (u1 i) F) (L-TF) (s-RF)):=by
    change Module.finrank K ((i:I)→NodeTarget K (m:=m i) F hF hbox hT hR
      (nodes i) (u0 i) (u1 i))=_
    rw [Module.finrank_pi_fintype]
    apply Finset.sum_congr rfl
    intro i _
    exact FLG K F hF hbox hT hR (nodes i) (u0 i) (u1 i)
  have hd:AW (D-nu) w (L-TF) (s-RF)+Module.finrank K W<
      AW D w L s:=by rw [htarget];exact hdim
  obtain ⟨Q,hproper,hQ⟩:=FBN K
    (EFW K D w F hF hbox hT hR nodes u0 u1 m) F hF hcode htotal hslope hd
  exact ⟨Q.val,Q.property,hproper,
    DKT K F hF hbox hT hR nodes u0 u1 m Q hQ⟩

end
end MA
end MergedPart7

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace DXV
open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243 UA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq _
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
  UniqueFactorizationMonoid.strongNormalizationMonoid
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq _

end
end DXV

namespace NG
open scoped Classical BigOperators
open RCN238 RCN081 RCN071 RCN167 RCN174 RCN319 RCN052 RCN260 RCN313 UA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq _

theorem FND {A B:Type*} [DecidableEq A] [DecidableEq B]
    (fs us:Finset A) (bs:Finset B) (hus:us ⊆ fs)
    (f:A→MvPolynomial (Fin 4) K) (g:B→MvPolynomial (Fin 4) K)
    (H Q:MvPolynomial (Fin 4) K) (hH:H ≠ 0) (hQ:Q ≠ 0)
    (hf:(∏ a ∈ fs,f a) ∣ H) (hg:(∏ b ∈ bs,g b) ∣ Q)
    (cap unitU unitRest:ℕ) (hcap:(H*Q).degreeOf 2≤cap)
    (costA:A→ℕ) (costB:B→ℕ)
    (hu: ∀a ∈ us,costA a≤(f a).degreeOf 2*unitU)
    (ha: ∀a ∈ fs \ us,costA a≤(f a).degreeOf 2*unitRest)
    (hb: ∀b ∈ bs,costB b≤(g b).degreeOf 2*unitRest):
    (∑ a ∈ fs,costA a)+(∑ b ∈ bs,costB b)≤
      (∑ a ∈ us,(f a).degreeOf 2)*unitU+
        (cap- ∑ a ∈ us,(f a).degreeOf 2)*unitRest:=by
  have hdA:=VS fs f H hH hf (2:Fin 4)
  have hdB:=VS bs g Q hQ hg (2:Fin 4)
  have heq:=MvPolynomial.degreeOf_mul_eq (n:=(2:Fin 4)) hH hQ
  have hs:=Finset.sum_sdiff hus (f:=fun a=>(f a).degreeOf 2)
  have hd:(∑ a ∈ fs \ us,(f a).degreeOf 2)+(∑ b ∈ bs,(g b).degreeOf 2)≤
      cap- ∑ a ∈ us,(f a).degreeOf 2:=by omega
  have hcu:=Finset.sum_le_sum hu
  have hca:=Finset.sum_le_sum ha
  have hcb:=Finset.sum_le_sum hb
  rw [← Finset.sum_mul] at hcu hca hcb
  have hrest:=Nat.add_le_add hca hcb
  rw [← Nat.add_mul] at hrest
  have hrest' :=hrest.trans (Nat.mul_le_mul_right unitRest hd)
  have hcs:=Finset.sum_sdiff hus (f:=costA)
  omega

theorem DYI
    (P:DG) (Q:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0)
    (hY:Q.degreeOf 1≤P.leftY) (hR:Q.degreeOf 2≤P.leftR)
    (hZ:Q.degreeOf 3≤P.leftZ):
    (∑ F:RegularIndex Q,(OX P F.1).y)≤P.mixedCost.y∧
    (∑ F:RegularIndex Q,(OX P F.1).r)≤P.mixedCost.r∧
    (∑ F:RegularIndex Q,(OX P F.1).z)≤P.mixedCost.z:=by
  have hi (i:Fin 4):(∑ F:RegularIndex Q,F.1.degreeOf i)≤Q.degreeOf i:=by
    rw [← Finset.sum_subtype (FW Q) (fun _=>Iff.rfl)]
    exact VS (FW Q) id Q hQ
      (AGW Q hQ) i
  have hy:=(hi 1).trans hY
  have hr:=(hi 2).trans hR
  have hz:=(hi 3).trans hZ
  simp only [OX,Finset.sum_add_distrib]
  constructor
  · rw [← Finset.sum_mul,← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hr) (Nat.mul_le_mul_right P.rightR hz)
  constructor
  · rw [← Finset.sum_mul,← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hy) (Nat.mul_le_mul_right P.rightY hz)
  · rw [← Finset.sum_mul,← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right P.rightR hy) (Nat.mul_le_mul_right P.rightY hr)

theorem dR_degree_le (j:ℕ) (F:MvPolynomial (Fin 4) K) (i:Fin 4):
    (dR j F).degreeOf i≤F.degreeOf i:=by
  induction j with
  | zero=>simp
  | succ j ih=>
    rw [dR_succ]
    exact KQ 2 i (dR j F) (F.degreeOf i) ih

variable {I:Type}
local instance:DecidableEq I:=Classical.decEq _

end
end NG

namespace ABE
open GB
open scoped Classical BigOperators
open RCN238 RCN081 RCN071 RCN167 RCN174 RCN319 RCN052 RCN260 RCN313 RCN294 UA NG
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _

theorem DVN
   (P:DG) (Q T:MvPolynomial (Fin 4) K)
   (selected:K→Polynomial K) (Gamma:Finset K)
   (hcost:
     (∑ F:RegularIndex Q,(OX P F.1).y)≤P.mixedCost.y∧
     (∑ F:RegularIndex Q,(OX P F.1).r)≤P.mixedCost.r∧
     (∑ F:RegularIndex Q,(OX P F.1).z)≤P.mixedCost.z)
   (hcount:∀F:RegularIndex Q,
     (NQ Q T selected Gamma F).card*P.gap≤
       (P.n-P.w)*dot P.KO (OX P F.1)+
         (P.errors+1)*P.gap*(OX P F.1).z):
   (∑ F:RegularIndex Q,(NQ Q T selected Gamma F).card)*
       P.gap≤KP P:=by
 calc
   _=∑ F:RegularIndex Q,
       (NQ Q T selected Gamma F).card*P.gap:=by
     rw [Finset.sum_mul]
   _≤ ∑ F:RegularIndex Q,
       ((P.n-P.w)*dot P.KO (OX P F.1)+
         (P.errors+1)*P.gap*(OX P F.1).z):=
     Finset.sum_le_sum fun F _↦hcount F
   _=(P.n-P.w)*dot P.KO
         (RCN294.sumVector fun F:RegularIndex Q↦
           OX P F.1)+
       (P.errors+1)*P.gap*
         (RCN294.sumVector fun F:RegularIndex Q↦
           OX P F.1).z:=by
     rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,
       ←GYC]
     simp only [RCN294.sumVector]
   _≤(P.n-P.w)*dot P.KO P.mixedCost+
       (P.errors+1)*P.gap*P.mixedCost.z:=by
     apply Nat.add_le_add
     · exact Nat.mul_le_mul_left _ (Nat.add_le_add
         (Nat.add_le_add
           (Nat.mul_le_mul_left P.KO.y hcost.1)
           (Nat.mul_le_mul_left P.KO.r hcost.2.1))
         (Nat.mul_le_mul_left P.KO.z hcost.2.2))
     · exact Nat.mul_le_mul_left _ hcost.2.2
   _=KP P:=rfl

end
end ABE

namespace AUT
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 ABE GB
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end AUT

namespace Lower80811.Counting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open UA NG AUT ABE GB
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ
local instance:StrongNormalizationMonoid P4:=UniqueFactorizationMonoid.strongNormalizationMonoid

variable {u0 u1:I→K} {selected:K→Polynomial K} {Gamma:Finset K}

end
end Lower80811.Counting

namespace Lower80811.Budgets
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN319
open RCN286 RCN267 RCN180 KZ
open DY MM FV Counting NG AUT
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _

end
end Lower80811.Budgets
end MergedPart0
section MergedPart1
namespace FAD
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174 RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001 RCN052 RCN264 RCN007 RCN004 RCN072 UA NG GB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K:Type} [Field K] {ι:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι

def foldSeeds (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K)
    (Gamma:Finset K):Finset K:=
  Gamma.filter fun γ=>BM K (selected γ) γ F=0∧
    BM K (selected γ) γ (dR 1 F)=0∧
    BM K (selected γ) γ (dR (chainLength F) F) ≠ 0

theorem GDW (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K)
    (Gamma:Finset K):foldSeeds F selected Gamma ⊆ Gamma:=Finset.filter_subset _ _

theorem dR_one (F:MvPolynomial (Fin 4) K):
    dR 1 F=MvPolynomial.pderiv (2:Fin 4) F:=dR_succ 0 F

theorem GAP (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K)
    (Gamma:Finset K) (γ:K) (hγ:γ ∈ Gamma)
    (h0:BM K (selected γ) γ F=0)
    (h1:BM K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) F)=0):
    γ ∈ foldSeeds F selected Gamma ∪ tailSeeds F selected Gamma:=by
  by_cases hL:BM K (selected γ) γ (dR (chainLength F) F)=0
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ,hL⟩)
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hγ,h0,by rw [dR_one];exact h1,hL⟩)

theorem DKY (F:MvPolynomial (Fin 4) K)
    (hF:F.degreeOf 2=1) (selected:K→Polynomial K) (Gamma:Finset K):
    foldSeeds F selected Gamma= ∅ :=by
  have hL:chainLength F=1:=by
    have h1:=FEE F (by omega)
    have h2:=GJV F
    omega
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro γ hγ
  obtain ⟨_,_,h1,hne⟩:=Finset.mem_filter.mp hγ
  rw [hL] at hne
  exact hne h1

theorem cover_fold (Q T:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hQsolution: ∀γ ∈ Gamma,BM K (selected γ) γ Q=0)
    (hTsolution: ∀γ ∈ Gamma,BM K (selected γ) γ T=0):
    Gamma ⊆
      (Finset.univ.biUnion fun F:RegularIndex Q=>
          NQ Q T selected Gamma F) ∪
        ((FW Q).biUnion fun F=>foldSeeds F selected Gamma) ∪
        ((FW Q).biUnion fun F=>tailSeeds F selected Gamma) ∪
        rfreeSeeds Q selected Gamma:=by
  intro γ hγ
  obtain ⟨F,hFactive,hFzero⟩:=
    DIF Q hQ (selected γ) γ (hQsolution γ hγ)
  by_cases hRfree:F.degreeOf 2=0
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr ⟨hγ,?_⟩
    have hdiv:F ∣ rfreeProduct Q:=by
      unfold rfreeProduct
      exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hFactive,hRfree⟩)
    obtain ⟨c,hc⟩:=hdiv
    rw [hc,map_mul,hFzero,zero_mul]
  · have hFpos:F ∈ FW Q:=by
      unfold FW
      exact Finset.mem_filter.mpr ⟨hFactive,Nat.pos_of_ne_zero hRfree⟩
    by_cases hreg:BM K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) F)=0
    · rcases Finset.mem_union.mp (GAP F selected Gamma γ hγ hFzero hreg) with
        hfold | htail
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨F,hFpos,hfold⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨F,hFpos,htail⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr ⟨⟨F,hFpos⟩,Finset.mem_univ _,?_⟩
      exact Finset.mem_filter.mpr ⟨hγ,⟨hFzero,hreg⟩,hTsolution γ hγ⟩

section Components

variable (K)

theorem BKY
    (C:Ideal (MvPolynomial (Fin 3) (GenericField K))) (selected:K→Polynomial K) (γ:K)
    (hC:C≤RingHom.ker
      (MvPolynomial.aeval (DK (AL K) selected γ)).toRingHom)
    (Q:MvPolynomial (Fin 4) K) (hQ:surfaceMap (AL K) Q ∈ C):
    BM K (selected γ) γ Q=0:=by
  have h:=RingHom.mem_ker.mp (hC hQ)
  change MvPolynomial.eval (DK (AL K) selected γ)
    (surfaceMap (AL K) Q)=0 at h
  rw [UM] at h
  exact (ATH K _).mp h

theorem FEC
    (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) (GenericField K))
    (hG:Irreducible G) (hdiv:G ∣ surfaceMap (AL K) F)
    (hproper: ¬G ∣ surfaceMap (AL K) (dR 1 F))
    (C:AU (GenericField K) G (surfaceMap (AL K) (dR 1 F)) 1)
    (p:ℕ) [CharP K p]
    (hGdegree: ∀j:Fin 3,G.degreeOf j<p)
    (hcutDegree: ∀j k:Fin 3,j ≠ k→
      (surfaceMap (AL K) (dR 1 F)).degreeOf j*G.degreeOf k+
        G.degreeOf j*(surfaceMap (AL K) (dR 1 F)).degreeOf k<p)
    (y r z:ℕ) (hr:1≤r) (hY:F.degreeOf 1≤y) (hR:F.degreeOf 2-1≤r)
    (hZ:F.degreeOf 3≤z)
    (selected:K→Polynomial K) (Γ:Finset K)
    (nodes:Finset ι) (x u₀ u₁:ι→K) (hinj:Set.InjOn x nodes)
    (w a e:ℕ) (hw:1≤w) (hchar:w<p) (hwa:w<a) (han:a≤nodes.card)
    (hdegree: ∀γ ∈ Γ,(selected γ).natDegree≤w)
    (htail: ∀γ ∈ Γ,BM K (selected γ) γ (dR (chainLength F) F) ≠ 0)
    (hagreement: ∀γ ∈ Γ,
      a≤(nodes.filter (fun i=>(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
    (hnoPencil:BL selected Γ w e):
    (HF (GenericField K) G (surfaceMap (AL K) (dR 1 F)) 1 Γ
        (DK (AL K) selected) C).card*(a-w)≤
      (nodes.card-w)*(∑ i,capAt (AMS y r z w) i*
          II (GenericField K) C.1 i)+
        (e+1)*(a-w)*II (GenericField K) C.1 2+
        (a-w)*(∑ i,capAt ⟨y,r,z⟩ i*II (GenericField K) C.1 i):=by
  classical
  letI:CharP (GenericField K) p:=MP K p
  let phi:=AL K
  let T:=surfaceMap phi (dR 1 F)
  let S:=HF (GenericField K) G T 1 Γ (DK phi selected) C
  show S.card*(a-w)≤_
  have hsub:S ⊆ Γ:=LU _ G T 1 Γ _ C
  have hon: ∀γ ∈ S,C.1≤RingHom.ker
      (MvPolynomial.aeval (DK phi selected γ)).toRingHom:=
    fun γ hγ=>MC _ G T 1 Γ _ C γ hγ
  have hgmem:=EN _ G T 1 C
  have htmem:=GV _ G T 1 C
  have hFmem:surfaceMap phi (dR 0 F) ∈ C.1:=
    ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
      (Ideal.mem_span_singleton.mpr hdiv)
  by_cases hex: ∃m,surfaceMap phi (dR m F) ∉ C.1
  · obtain ⟨m,hmout,hmin⟩: ∃m,surfaceMap phi (dR m F) ∉ C.1∧
        ∀k<m,surfaceMap phi (dR k F) ∈ C.1:=
      ⟨Nat.find hex,Nat.find_spec hex,fun k hk=>not_not.mp (Nat.find_min hex hk)⟩
    have hm2:2≤m:=by
      by_contra hlt
      interval_cases m
      · exact hmout hFmem
      · exact hmout htmem
    have hcarrier:surfaceMap phi (dR (m-1) F) ∈ C.1:=hmin (m-1) (by omega)
    have hderiv:MvPolynomial.pderiv (2:Fin 4) (dR (m-1) F)=dR m F:=by
      rw [← dR_succ,Nat.sub_add_cancel (by omega:1≤m)]
    have hproj:GK (GenericField K) C.1:=
      AAC _ C.1 p G T hG hgmem htmem
        hproper hGdegree hcutDegree
    have hnonpoint:=PU _ G T 1 C
    let S₁:=S.filter fun γ=>BM K (selected γ) γ (dR m F) ≠ 0
    let S₂:=S.filter fun γ=> ¬BM K (selected γ) γ (dR m F) ≠ 0
    have hsplit:S₁.card+S₂.card=S.card:=
      Finset.card_filter_add_card_filter_not _
    have hS₁:S₁ ⊆ S:=Finset.filter_subset _ _
    have hS₂:S₂ ⊆ S:=Finset.filter_subset _ _

    have hcap: ∀i ∈ nodes,∀j,
        (FK phi (dR (m-1) F) w (x i) (u₀ i) (u₁ i)).degreeOf j≤
          capAt (AMS y r z w) j:=by
      intro i _ j
      have h:=BHT phi (dR (m-1) F) y r z hr
        ((dR_degree_le (m-1) F 1).trans hY)
        ((BLP (m-1) F).trans (by omega))
        ((dR_degree_le (m-1) F 3).trans hZ) w (fun j=>(j.factorial:K)⁻¹)
        (x i) (u₀ i) (u₁ i)
      simpa [FK] using h j
    have hreg:=CQV phi C.1 hproj hnonpoint (dR (m-1) F) hcarrier
      (by rw [hderiv];exact hmout) selected S₁ nodes x u₀ u₁ hinj p w a e hw hchar hwa han
      (fun γ hγ=>hdegree γ (hsub (hS₁ hγ)))
      (fun γ hγ=>BKY K C.1 selected γ (hon γ (hS₁ hγ)) _
        hcarrier)
      (fun γ hγ=>VK K (dR (m-1) F) selected γ
        (by rw [hderiv];exact (Finset.mem_filter.mp hγ).2))
      (fun γ hγ=>hon γ (hS₁ hγ))
      (fun γ hγ=>hagreement γ (hsub (hS₁ hγ)))
      (KX selected Γ S₁ w e (hS₁.trans hsub) hnoPencil)
      (capAt (AMS y r z w)) hcap

    let points:=S₂.image (DK phi selected)
    have hjcap: ∀i,(surfaceMap phi (dR m F)).degreeOf i≤capAt ⟨y,r,z⟩ i:=by
      intro i
      have h:=GO phi (dR m F) i
      fin_cases i
      · exact h.trans ((dR_degree_le m F 1).trans hY)
      · exact h.trans ((BLP m F).trans (by change F.degreeOf 2-m≤r;omega))
      · exact h.trans ((dR_degree_le m F 3).trans hZ)
    have hjump:=BMF (GenericField K) C.1 hproj hnonpoint
      (surfaceMap phi (dR m F)) hmout (capAt ⟨y,r,z⟩) hjcap points
      (by
        intro v hv
        obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
        exact hon γ (hS₂ hγ))
      (by
        intro v hv
        obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
        have hz:BM K (selected γ) γ (dR m F)=0:=
          not_not.mp (Finset.mem_filter.mp hγ).2
        change MvPolynomial.eval (DK phi selected γ) (surfaceMap phi (dR m F))=0
        rw [UM,hz,map_zero])
    have hpoints:points.card=S₂.card:=
      Finset.card_image_of_injective _ (ABD phi selected)
    rw [hpoints] at hjump
    have hjump' :S₂.card≤ ∑ i,capAt ⟨y,r,z⟩ i*
        II (GenericField K) C.1 i:=by
      exact_mod_cast hjump
    have hreg' :S₁.card*(a-w)≤(nodes.card-w)*(∑ i,capAt (AMS y r z w) i*
          II (GenericField K) C.1 i)+
        (e+1)*(a-w)*II (GenericField K) C.1 2:=hreg
    calc
      S.card*(a-w)=S₁.card*(a-w)+S₂.card*(a-w):=by
        rw [← hsplit,Nat.add_mul]
      _≤_:=by
        have:=Nat.mul_le_mul_left (a-w) hjump'
        nlinarith
  · have hempty:S= ∅ :=by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      apply htail γ (hsub hγ)
      exact BKY K C.1 selected γ (hon γ hγ) _
        (not_not.mp (fun h=>hex ⟨chainLength F,h⟩))
    rw [hempty,Finset.card_empty,Nat.zero_mul]
    exact Nat.zero_le _

theorem FPG
    (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) (GenericField K))
    (hG:Irreducible G) (hdiv:G ∣ surfaceMap (AL K) F)
    (hproper: ¬G ∣ surfaceMap (AL K) (dR 1 F))
    (p:ℕ) [CharP K p]
    (hGdegree: ∀j:Fin 3,G.degreeOf j<p)
    (hcutDegree: ∀j k:Fin 3,j ≠ k→
      (surfaceMap (AL K) (dR 1 F)).degreeOf j*G.degreeOf k+
        G.degreeOf j*(surfaceMap (AL K) (dR 1 F)).degreeOf k<p)
    (y r z:ℕ) (hr:1≤r) (hY:F.degreeOf 1≤y) (hR:F.degreeOf 2-1≤r)
    (hZ:F.degreeOf 3≤z)
    (selected:K→Polynomial K) (Γ:Finset K)
    (nodes:Finset ι) (x u₀ u₁:ι→K) (hinj:Set.InjOn x nodes)
    (w a e:ℕ) (hw:1≤w) (hchar:w<p) (hwa:w<a) (han:a≤nodes.card)
    (hdegree: ∀γ ∈ Γ,(selected γ).natDegree≤w)
    (hGpoint: ∀γ ∈ Γ,
      MvPolynomial.eval (DK (AL K) selected γ) G=0)
    (hfold: ∀γ ∈ Γ,BM K (selected γ) γ (dR 1 F)=0)
    (htail: ∀γ ∈ Γ,BM K (selected γ) γ (dR (chainLength F) F) ≠ 0)
    (hagreement: ∀γ ∈ Γ,
      a≤(nodes.filter (fun i=>(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
    (hnoPencil:BL selected Γ w e):
    Γ.card*(a-w)≤
      1*(∑ i,((nodes.card-w)*capAt (AMS y r z w) i+
          (a-w)*capAt ⟨y,r,z⟩ i)*
        EB (GenericField K) G (surfaceMap (AL K) (dR 1 F)) i)+
      (e+1)*(a-w)*
        EB (GenericField K) G (surfaceMap (AL K) (dR 1 F)) 2:=by
  classical
  letI:CharP (GenericField K) p:=MP K p
  let T:=surfaceMap (AL K) (dR 1 F)
  letI: ∀C:AU (GenericField K) G T 1,C.1.IsPrime:=
    fun C=>CYY (GenericField K) G T 1 C
  have hTpoint: ∀γ ∈ Γ,
      MvPolynomial.eval (DK (AL K) selected γ) T=0:=by
    intro γ hγ
    change MvPolynomial.eval (DK (AL K) selected γ)
      (surfaceMap (AL K) (dR 1 F))=0
    rw [UM,hfold γ hγ,map_zero]
  have hbudget: ∀i,(∑ C:AU (GenericField K) G T 1,
      II (GenericField K) C.1 i)≤
        EB (GenericField K) G T i:=by
    intro i
    have hneq:(Equiv.swap (0:Fin 3) i) 1 ≠ (Equiv.swap (0:Fin 3) i) 2:=
      (Equiv.swap (0:Fin 3) i).injective.ne (by decide)
    exact BLR (GenericField K)
      (fun C:AU (GenericField K) G T 1=>C.1)
      Subtype.val_injective i p G T hG
      (EN (GenericField K) G T 1)
      (GV (GenericField K) G T 1)
      hproper hGdegree (hcutDegree _ _ hneq)
  apply AXW (GenericField K) G T 1 Γ
    (DK (AL K) selected) hGpoint hTpoint (fun _ _=>by simp)
    (a-w) 1 (e+1) _ (EB (GenericField K) G T)
    (fun C i=>II (GenericField K) C.1 i) _ hbudget
  intro C
  have h:=FEC K F G hG hdiv hproper C p hGdegree hcutDegree y r z hr hY hR hZ
    selected Γ nodes x u₀ u₁ hinj w a e hw hchar hwa han hdegree htail hagreement hnoPencil
  have heq:(∑ i,((nodes.card-w)*capAt (AMS y r z w) i+
      (a-w)*capAt ⟨y,r,z⟩ i)*II (GenericField K) C.1 i)=
      (nodes.card-w)*(∑ i,capAt (AMS y r z w) i*
        II (GenericField K) C.1 i)+
      (a-w)*(∑ i,capAt ⟨y,r,z⟩ i*II (GenericField K) C.1 i):=by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  show _≤1*(∑ i,((nodes.card-w)*capAt (AMS y r z w) i+
      (a-w)*capAt ⟨y,r,z⟩ i)*II (GenericField K) C.1 i)+
    (e+1)*(a-w)*II (GenericField K) C.1 2
  rw [Nat.one_mul,heq]
  exact h.trans (le_of_eq (by ring))

end Components

theorem EVR
    (P:DG) (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
    (p:ℕ) [CharP K p] (hpos:0<F.degreeOf 2) (hsmall:F.degreeOf 2<p)
    (hY:F.degreeOf 1≤P.leftY) (hR:F.degreeOf 2-1≤P.leftR)
    (hZ:F.degreeOf 3≤P.leftZ)
    (hY' :F.degreeOf 1≤P.rightY) (hR' :F.degreeOf 2≤P.rightR)
    (hZ' :F.degreeOf 3≤P.rightZ)
    (hleftR:1≤P.leftR)
    (hrightYSmall:P.rightY<p) (hrightRSmall:P.rightR<p) (hrightZSmall:P.rightZ<p)
    (hmixedYSmall:P.mixedCost.y<p) (hmixedRSmall:P.mixedCost.r<p)
    (hmixedZSmall:P.mixedCost.z<p)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (nodes:Finset ι) (x u₀ u₁:ι→K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card=P.n) (hw:1≤P.w) (hchar:P.w<p)
    (hwa:P.w<P.a) (han:P.a≤P.n)
    (hdegree: ∀γ ∈ Gamma,(selected γ).natDegree≤P.w)
    (hagreement: ∀γ ∈ Gamma,P.a≤(nodes.filter (fun i=>
      (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
    (hno:BL selected Gamma P.w P.errors):
    (foldSeeds F selected Gamma).card*P.gap≤
      KP P+P.gap*dot ⟨P.leftY,P.leftR,P.leftZ⟩ P.mixedCost:=by
  classical
  letI:CharP (GenericField K) p:=MP K p
  let phi:=AL K
  let Δ:=foldSeeds F selected Gamma
  have hFne:F ≠ 0:=hF.ne_zero
  have hΔ:Δ ⊆ Gamma:=GDW F selected Gamma
  have hΔdata: ∀γ ∈ Δ,BM K (selected γ) γ F=0∧
      BM K (selected γ) γ (dR 1 F)=0∧
      BM K (selected γ) γ (dR (chainLength F) F) ≠ 0:=
    fun γ hγ=>(Finset.mem_filter.mp hγ).2
  have hnotdvd: ¬F ∣ dR 1 F:=
    EVN F hF p hpos hsmall 1 le_rfl (FEE F hpos)
  have hcover:=AAD K F hFne selected Δ (fun γ hγ=>(hΔdata γ hγ).1)
  let rightCap:RCN051.DegreeVector:=⟨P.rightY,P.rightR,P.rightZ⟩
  let leftCap:RCN051.DegreeVector:=⟨P.leftY,P.leftR,P.leftZ⟩
  let capF:Fin 3→ℕ:=fun i=>
    (P.n-P.w)*capAt (AMS P.leftY P.leftR P.leftZ P.w) i+
      (P.a-P.w)*capAt ⟨P.leftY,P.leftR,P.leftZ⟩ i
  have hsingle (g:EX K F):
      (KK K F selected Δ g).card*P.gap≤
        (∑ i,capF i*EB (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i)+
          (P.errors+1)*P.gap*
            EB (GenericField K) g.1 (surfaceMap phi (dR 1 F)) 2:=by
    have hgSpec:=ACQ phi F g.1 g.2
    have hsub:=WK K F selected Δ g
    have hproper: ¬g.1 ∣ surfaceMap phi (dR 1 F):=by
      intro hgT
      apply hnotdvd
      have hpos' :0<F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by omega
      have hgeo:g.1 ∣ NB K (GenericField K) F:=by
        simpa only [HP] using hgSpec.2
      exact (AIB K (GenericField K) F (dR 1 F) hF hpos'
        g.1 hgSpec.1 hgeo).mp (by simpa only [HP] using hgT)
    have hgCaps:HasCaps g.1 rightCap:=by
      intro i
      have hi:=AGP K F hFne g i
      fin_cases i
      · exact hi.trans hY'
      · exact hi.trans hR'
      · exact hi.trans hZ'
    have hTCaps:HasCaps (surfaceMap phi (dR 1 F)) leftCap:=by
      intro i
      fin_cases i
      · exact (GO phi (dR 1 F) 0).trans ((dR_degree_le 1 F 1).trans hY)
      · exact (GO phi (dR 1 F) 1).trans ((BLP 1 F).trans hR)
      · exact (GO phi (dR 1 F) 2).trans ((dR_degree_le 1 F 3).trans hZ)
    have hrightSmall: ∀i,capAt rightCap i<p:=by
      intro i
      fin_cases i
      · exact hrightYSmall
      · exact hrightRSmall
      · exact hrightZSmall
    have hgates:=APW g.1 (surfaceMap phi (dR 1 F))
      rightCap leftCap p hgCaps hTCaps hrightSmall
      (by
        have h:RCN051.mixed rightCap leftCap RCN051.unitY=P.mixedCost.y:=by
          simp only [rightCap,leftCap,RCN051.mixed,RCN051.unitY,
            DG.mixedCost]
          ring
        rw [h]
        exact hmixedYSmall)
      (by
        have h:RCN051.mixed rightCap leftCap RCN051.unitR=P.mixedCost.r:=by
          simp only [rightCap,leftCap,RCN051.mixed,RCN051.unitR,
            DG.mixedCost]
          ring
        rw [h]
        exact hmixedRSmall)
      (by
        have h:RCN051.mixed rightCap leftCap RCN051.unitZ=P.mixedCost.z:=by
          simp only [rightCap,leftCap,RCN051.mixed,RCN051.unitZ,
            DG.mixedCost]
          ring
        rw [h]
        exact hmixedZSmall)
    have h:=FPG K F g.1 hgSpec.1 hgSpec.2 hproper p hgates.1 hgates.2
      P.leftY P.leftR P.leftZ hleftR hY hR hZ selected (KK K F selected Δ g)
      nodes x u₀ u₁ hinj P.w P.a P.errors hw hchar hwa (by rw [hnodes];exact han)
      (fun γ hγ=>hdegree γ (hΔ (hsub hγ)))
      (fun γ hγ=>(Finset.mem_filter.mp hγ).2)
      (fun γ hγ=>(hΔdata γ (hsub hγ)).2.1)
      (fun γ hγ=>(hΔdata γ (hsub hγ)).2.2)
      (fun γ hγ=>hagreement γ (hΔ (hsub hγ)))
      (KX selected Gamma _ P.w P.errors
        (fun _ hγ=>hΔ (hsub hγ)) hno)
    rw [hnodes,Nat.one_mul] at h
    exact h
  let P' :DG:=
    ⟨P.n,P.w,P.a,P.rightY,P.rightR,P.rightZ,P.leftY,P.leftR,P.leftZ⟩
  have hbudget (i:Fin 3):
      (∑ g:EX K F,
        EB (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i)≤
        regularCapAt P.mixedCost i:=by
    have h:=ABX P' F (dR 1 F) hFne
      ((dR_degree_le 1 F 1).trans hY) ((BLP 1 F).trans hR)
      ((dR_degree_le 1 F 3).trans hZ) i
    refine h.trans ?_
    have h1:=Nat.mul_le_mul_right P.leftZ hR'
    have h2:=Nat.mul_le_mul_right P.leftR hZ'
    have h3:=Nat.mul_le_mul_right P.leftZ hY'
    have h4:=Nat.mul_le_mul_right P.leftY hZ'
    have h5:=Nat.mul_le_mul_right P.leftR hY'
    have h6:=Nat.mul_le_mul_right P.leftY hR'
    fin_cases i<;>
      simp only [regularCapAt,OX,P',DG.mixedCost,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.head_cons,Matrix.tail_cons,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk]<;>
      nlinarith
  have hfubini:(∑ g:EX K F,∑ i:Fin 3,
      capF i*EB (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i)=
      ∑ i:Fin 3,capF i*(∑ g:EX K F,
        EB (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i):=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    Δ.card*P.gap≤(∑ g:EX K F,
        (KK K F selected Δ g).card)*P.gap:=
      Nat.mul_le_mul_right P.gap hcover
    _= ∑ g:EX K F,(KK K F selected Δ g).card*P.gap:=by
      rw [Finset.sum_mul]
    _≤ ∑ g:EX K F,
        ((∑ i,capF i*EB (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i)+
          (P.errors+1)*P.gap*
            EB (GenericField K) g.1 (surfaceMap phi (dR 1 F)) 2):=
      Finset.sum_le_sum fun g _=>hsingle g
    _=(∑ i:Fin 3,capF i*(∑ g:EX K F,
          EB (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i))+
        (P.errors+1)*P.gap*(∑ g:EX K F,
          EB (GenericField K) g.1 (surfaceMap phi (dR 1 F)) 2):=by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,hfubini]
    _≤(∑ i:Fin 3,capF i*regularCapAt P.mixedCost i)+
        (P.errors+1)*P.gap*regularCapAt P.mixedCost 2:=
      Nat.add_le_add
        (Finset.sum_le_sum fun i _=>Nat.mul_le_mul_left _ (hbudget i))
        (Nat.mul_le_mul_left _ (hbudget 2))
    _=_:=by
      simp only [capF,Fin.sum_univ_three,capAt,regularCapAt,AMS,
        KP,DG.KO,dot,DG.gap,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.head_cons,Matrix.tail_cons]
      ring

end
end FAD
end MergedPart1

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace Lower80899.PhaseRows
open RCN095 DY CS
open FV (Potential BaseRow BaseSegment EZD rawFlag BTK AVF rawFlag_all)
open Lower80899.Oracle
open DSA (CVK)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem DZI
    (s:EA) {r v z₁ z₂:ℕ}
    (hz:z₁≤z₂) (hcap:r+v+z₂≤s.totalCap)
    (hroute:s.Routeable (rawFlag r v z₁)):
    s.Routeable (rawFlag r v z₂):=by
  rcases hroute with ⟨hr,ht,hy,hs,hband⟩
  have hr' :1≤r:=by simpa only [rawFlag_all] using hr
  have htotal:r+v+z₁≤r+v+z₂:=by omega
  have hpos:0<r+v+z₁:=by omega
  have hdiv:s.totalCap/(r+v+z₂)≤
      s.totalCap/(r+v+z₁):=
    Nat.div_le_div_left htotal hpos
  have hfuel:s.fuel (rawFlag r v z₂)≤
      s.fuel (rawFlag r v z₁):=by
    unfold EA.fuel
    simp only [BTK,AVF,rawFlag_all]
    exact min_le_min hdiv (le_refl _)
  have hbox:s.totalCap-(r+v+z₂)≤
      s.totalCap-(r+v+z₁):=Nat.sub_le_sub_left htotal _
  have hsameFuel:
      LH 50165 (r+v+z₂) (r+v) r
          (s.totalCap-(r+v+z₂)) (s.middleCap-(r+v))
          (s.slopeCap-r) (s.fuel (rawFlag r v z₂))≤
        LH 50165 (r+v+z₁) (r+v) r
          (s.totalCap-(r+v+z₁)) (s.middleCap-(r+v))
          (s.slopeCap-r) (s.fuel (rawFlag r v z₂)):=by
    exact BRL 50165
      (r+v+z₂) (r+v) r
      (s.totalCap-(r+v+z₂)) (s.middleCap-(r+v))
      (s.slopeCap-r)
      (r+v+z₁) (r+v) r
      (s.totalCap-(r+v+z₁)) (s.middleCap-(r+v))
      (s.slopeCap-r) (s.fuel (rawFlag r v z₂))
      hbox (le_refl _) (le_refl _) htotal (le_refl _) (le_refl _)
  have hmoreFuel:
      LH 50165 (r+v+z₁) (r+v) r
          (s.totalCap-(r+v+z₁)) (s.middleCap-(r+v))
          (s.slopeCap-r) (s.fuel (rawFlag r v z₂))≤
        LH 50165 (r+v+z₁) (r+v) r
          (s.totalCap-(r+v+z₁)) (s.middleCap-(r+v))
          (s.slopeCap-r) (s.fuel (rawFlag r v z₁)):=
    CVK 50165 (r+v+z₁) (r+v) r
      (s.totalCap-(r+v+z₁)) (s.middleCap-(r+v))
      (s.slopeCap-r) hfuel
  refine ⟨hr,?_,?_,?_,?_⟩
  · simpa only [BTK] using hcap
  · simpa only [AVF] using hy
  · simpa only [rawFlag_all] using hs
  · rcases hband with hband | hthin
    · left
      unfold EA.band at hband ⊢
      simp only [BTK,AVF,rawFlag_all] at hband ⊢
      exact (hsameFuel.trans hmoreFuel).trans_lt hband
    · right
      have hsameFuelT:
          HN 131071 (s.contactCap (rawFlag r v z₂)) 50165
              (contactDec (rawFlag r v z₂)) (r+v+z₂) (r+v) r
              (s.totalCap-(r+v+z₂)) (s.middleCap-(r+v))
              (s.slopeCap-r) (s.fuel (rawFlag r v z₂))≤
            HN 131071 (s.contactCap (rawFlag r v z₁)) 50165
              (contactDec (rawFlag r v z₁)) (r+v+z₁) (r+v) r
              (s.totalCap-(r+v+z₁)) (s.middleCap-(r+v))
              (s.slopeCap-r) (s.fuel (rawFlag r v z₂)):=by
        have hcap:s.contactCap (rawFlag r v z₂)=s.contactCap (rawFlag r v z₁):=by
          simp only [EA.contactCap,contactDec,AVF,rawFlag_all]
        have hdec:contactDec (rawFlag r v z₂)=contactDec (rawFlag r v z₁):=by
          simp only [contactDec,AVF,rawFlag_all]
        rw [hcap,hdec]
        exact AZD 131071 50165 (s.fuel (rawFlag r v z₂))
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r+v+z₂) (r+v) r
          (s.totalCap-(r+v+z₂)) (s.middleCap-(r+v)) (s.slopeCap-r)
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r+v+z₁) (r+v) r
          (s.totalCap-(r+v+z₁)) (s.middleCap-(r+v)) (s.slopeCap-r)
          le_rfl le_rfl hbox le_rfl le_rfl htotal le_rfl le_rfl
      have hmoreFuelT:
          HN 131071 (s.contactCap (rawFlag r v z₁)) 50165
              (contactDec (rawFlag r v z₁)) (r+v+z₁) (r+v) r
              (s.totalCap-(r+v+z₁)) (s.middleCap-(r+v))
              (s.slopeCap-r) (s.fuel (rawFlag r v z₂))≤
            HN 131071 (s.contactCap (rawFlag r v z₁)) 50165
              (contactDec (rawFlag r v z₁)) (r+v+z₁) (r+v) r
              (s.totalCap-(r+v+z₁)) (s.middleCap-(r+v))
              (s.slopeCap-r) (s.fuel (rawFlag r v z₁)):=
        DUI 131071 (s.contactCap (rawFlag r v z₁)) 50165
          (contactDec (rawFlag r v z₁)) (r+v+z₁) (r+v) r
          (s.totalCap-(r+v+z₁)) (s.middleCap-(r+v)) (s.slopeCap-r) hfuel
      unfold EA.bandThin at hthin ⊢
      simp only [BTK,AVF,rawFlag_all] at hthin ⊢
      exact (hsameFuelT.trans hmoreFuelT).trans_lt hthin

def BSY:ℕ→Potential
  | 0=>Lower80899.SourceSound.Phase00.potential
  | 1=>Lower80899.SourceSound.Phase01.potential
  | 2=>Lower80899.SourceSound.Phase02.potential
  | 3=>Lower80899.SourceSound.Phase03.potential
  | 4=>Lower80899.SourceSound.Phase04.potential
  | 5=>Lower80899.SourceSound.Phase05.potential
  | 6=>Lower80899.SourceSound.Phase06.potential
  | 7=>Lower80899.SourceSound.Phase03.potential
  | 8=>Lower80899.SourceSound.Phase04.potential
  | _=>Lower80899.SourceSound.PhaseFinal.potential

def thresholdAt (q:Array ℕ) (j:ℕ):ℕ:=(q[j]?).getD 11193
def FKT (q:Array ℕ) (j:ℕ):ℕ:=(q[j]?).getD 0
structure ABS where
  R:ℕ
  V:ℕ
  base:BaseRow
  threshold:Array ℕ
  here:Array ℕ
  parent:Array ℕ

def baseAt (c:ABS) (z:ℕ):ℕ:=c.base.evalAt z

def parentCharge (c:ABS) (phase z:ℕ):ℕ:=
  (BSY phase).eval (rawFlag c.R c.V z)+FKT c.parent phase

def hereCharge (c:ABS) (phase z:ℕ):ℕ:=
  (BSY phase).eval (rawFlag c.R c.V z)+FKT c.here phase

def sourceLine (c:ABS):ℕ→ℕ→ℕ
  | 0,z=>baseAt c z
  | j+1,z=>parentCharge c j z

def SourceActive (c:ABS):ℕ→ℕ→Prop
  | 0,_=>True
  | j+1,z=>thresholdAt c.threshold j≤z

instance (c:ABS) (w z:ℕ):Decidable (SourceActive c w z):=by
  cases w<;>simp only [SourceActive]<;>infer_instance

open DSM

def SourceCell (c:ABS):ℕ→ℕ→ℕ→Prop
  | 0,lo,hi=>BaseCell c.base lo hi
  | _+1,_,_=>True
instance (c:ABS) (w lo hi:ℕ):Decidable (SourceCell c w lo hi):=by
  cases w<;>simp only [SourceCell]<;>infer_instance

def RunValid (c:ABS) (phase start:ℕ) (run:PhaseRun):Prop:=
  let hi:=run.stop-1
  start<run.stop∧run.witness≤phase∧
    SourceActive c run.witness start∧
    SourceCell c run.witness start hi∧
    sourceLine c run.witness start≤hereCharge c phase start∧
    sourceLine c run.witness hi≤hereCharge c phase hi

instance (c:ABS) (phase start:ℕ) (run:PhaseRun):
    Decidable (RunValid c phase start run):=by
  unfold RunValid
  infer_instance

def RunsValid (c:ABS) (phase finish:ℕ):
    ℕ→List PhaseRun→Prop
  | start,[]=>start=finish
  | start,run::runs=>
      run.stop≤finish∧RunValid c phase start run∧
        RunsValid c phase finish run.stop runs

instance (c:ABS) (phase finish start:ℕ)
    (runs:List PhaseRun):Decidable (RunsValid c phase finish start runs):=by
  induction runs generalizing start with
  | nil=>simp only [RunsValid];infer_instance
  | cons run runs ih=>simp only [RunsValid];infer_instance

def phaseFinish (c:ABS) (phase:ℕ):ℕ:=
  min (thresholdAt c.threshold phase) (11193-(c.R+c.V))

def RowRunsValid (c:ABS) (runs:Array (List PhaseRun)):Prop:=
  ∀j ∈ List.range 10,RunsValid c j (phaseFinish c j) 0 ((runs[j]?).getD [])

instance (c:ABS) (runs:Array (List PhaseRun)):
    Decidable (RowRunsValid c runs):=by
  unfold RowRunsValid
  infer_instance

end Lower80899.PhaseRows

namespace Lower80899.AMY

open scoped BigOperators
open IL

set_option autoImplicit false
set_option maxRecDepth 100000

theorem term_eq (B x:ℕ):
    (x+1)*(B+x)-(x+1)*x/2=
      (x+1)*B+(x+1).choose 2:=by
  rw [Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  have hdvd:2 ∣ (x+1)*x:=by
    simpa [Nat.mul_comm,Nat.add_comm] using
      (even_iff_two_dvd.mp (Nat.even_mul_succ_self x))
  have hhalf:=Nat.div_mul_cancel hdvd
  rw [Nat.mul_add]
  omega

theorem DIM: ∀n:ℕ,
    ADH (fun x=>x+1) n=(n+1).choose 2
  | 0=>by decide
  | n+1=>by
      rw [IL.BKB,DIM]
      simpa [Nat.choose_one_right,Nat.add_comm,Nat.add_left_comm,
        Nat.add_assoc] using (Nat.choose_succ_succ (n+1) 1).symm

theorem BKB (U:ℕ):
    ADH (fun x=>x+1) (U+1)=(U+2).choose 2:=by
  simpa only [Nat.add_assoc] using DIM (U+1)

theorem BVB: ∀n:ℕ,
    ADH (fun x=>(x+1).choose 2) n=(n+1).choose 3
  | 0=>by decide
  | n+1=>by
      rw [IL.BKB,BVB]
      simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
        (Nat.choose_succ_succ (n+1) 2).symm

theorem ELG (U:ℕ):
    ADH (fun x=>(x+1).choose 2) (U+1)=
      (U+2).choose 3:=by
  simpa only [Nat.add_assoc] using BVB (U+1)

theorem ETL (B U:ℕ):
    ADH (fun x=>
      (x+1)*(B+x)-(x+1)*x/2) (U+1)=
      B*(U+2).choose 2+(U+2).choose 3:=by
  rw [VJ]
  simp_rw [term_eq]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  rw [← VJ,BKB]
  rw [← VJ,ELG]
  simp only [Nat.mul_comm]

def cappedTerm (B S x:ℕ):ℕ:=
  let M:=min S x
  (M+1)*(B+x)-(M+1)*M/2

theorem GNN (T YS x:ℕ) (hx:x≤min T YS):
    min (T-(min T YS-x)) (YS-(min T YS-x))=x:=by
  rcases le_total T YS with h | h
  · simp only [Nat.min_eq_left h] at hx ⊢
    omega
  · simp only [Nat.min_eq_right h] at hx ⊢
    omega

theorem BAJ (T YS S:ℕ):
    channelCount T YS S=
      ADH
        (cappedTerm (T+1-min T YS) S) (min T YS+1):=by
  unfold channelCount
  rw [VJ,← Finset.sum_range_reflect]
  rw [VJ]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hx' :x≤min T YS:=by
    have:=Finset.mem_range.mp hx
    omega
  have hU:min T YS≤T:=Nat.min_le_left _ _
  simp only [Nat.add_sub_cancel,cappedTerm]
  rw [GNN T YS x hx']
  have harg:T+1-(min T YS-x)=
      (T+1-min T YS)+x:=by omega
  rw [harg]

def DHA (T YS S:ℕ):ℕ:=
  let U:=min T YS
  let B:=T+1-U
  let k:=min S U
  let n:=U-k
  let C:=(S+1)*(B+S+1)-(S+1)*S/2
  B*(k+2).choose 2+(k+2).choose 3+
    n*C+(S+1)*(n*(n-1)/2)

theorem tail_term_eq (B S t:ℕ):
    cappedTerm B S (S+1+t)=
      ((S+1)*(B+S+1)-(S+1)*S/2)+
        (S+1)*t:=by
  unfold cappedTerm
  rw [Nat.min_eq_left (by omega)]
  change (S+1)*(B+(S+1+t))-(S+1)*S/2=
    ((S+1)*(B+S+1)-(S+1)*S/2)+(S+1)*t
  rw [show B+(S+1+t)=(B+S+1)+t by omega,
    Nat.mul_add]
  have hS:S≤B+S+1:=by omega
  have hq:(S+1)*S/2≤(S+1)*(B+S+1):=
    (Nat.div_le_self ((S+1)*S) 2).trans
      (Nat.mul_le_mul_left (S+1) hS)
  exact Nat.sub_add_comm
    (n:=(S+1)*(B+S+1)) (m:=(S+1)*t)
    (k:=(S+1)*S/2) hq

theorem CBF (B S k:ℕ) (hk:k≤S):
    ADH (cappedTerm B S) (k+1)=
      B*(k+2).choose 2+(k+2).choose 3:=by
  calc
    ADH (cappedTerm B S) (k+1)=
        ADH (fun x=>
          (x+1)*(B+x)-(x+1)*x/2) (k+1):=by
      rw [VJ,VJ]
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxk:x≤k:=by
        have:=Finset.mem_range.mp hx
        omega
      simp only [cappedTerm,Nat.min_eq_right (hxk.trans hk)]
    _=B*(k+2).choose 2+(k+2).choose 3:=
      ETL B k

theorem FID (B S U:ℕ) (hSU:S<U):
    (∑ x ∈ Finset.Ico (S+1) (U+1),cappedTerm B S x)=
      (U-S)*
          ((S+1)*(B+S+1)-(S+1)*S/2)+
        (S+1)*((U-S)*(U-S-1)/2):=by
  rw [Finset.sum_Ico_eq_sum_range]
  have hsub:U+1-(S+1)=U-S:=by omega
  rw [hsub]
  simp_rw [tail_term_eq]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_range,Nat.nsmul_eq_mul,
    Finset.sum_range_id]

theorem DYZ (B S U:ℕ):
    ADH (cappedTerm B S) (U+1)=
      let k:=min S U
      let n:=U-k
      B*(k+2).choose 2+(k+2).choose 3+
        n*((S+1)*(B+S+1)-(S+1)*S/2)+
          (S+1)*(n*(n-1)/2):=by
  by_cases hSU:S<U
  · simp only [Nat.min_eq_left hSU.le]
    rw [VJ]
    rw [← Finset.sum_range_add_sum_Ico (cappedTerm B S)
      (show S+1≤U+1 by omega)]
    rw [← VJ,CBF B S S le_rfl,
      FID B S U hSU]
    simp only [Nat.add_assoc]
  · have hUS:U≤S:=Nat.le_of_not_gt hSU
    simp only [Nat.min_eq_right hUS,Nat.sub_self,zero_mul,
      Nat.zero_sub,Nat.add_zero]
    exact CBF B S U hUS

theorem EAC (T YS S:ℕ):
    channelCount T YS S=DHA T YS S:=by
  rw [BAJ]
  rw [DYZ]
  rfl

theorem FMF (n:ℕ):
    n.choose 3=n*(n-1)*(n-2)/6:=by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp [Nat.descFactorial,Nat.factorial]
  congr 1
  ring

def FCL (n:ℕ):ℕ:=n*(n-1)/2
def EIP (n:ℕ):ℕ:=n*(n-1)*(n-2)/6

def AQJ (T YS S:ℕ):ℕ:=
  let U:=min T YS
  let B:=T+1-U
  let k:=min S U
  let n:=U-k
  let C:=(S+1)*(B+S+1)-(S+1)*S/2
  B*FCL (k+2)+EIP (k+2)+
    n*C+(S+1)*(n*(n-1)/2)

theorem ENK (T YS S:ℕ):
    DHA T YS S=AQJ T YS S:=by
  simp only [DHA,AQJ,FCL,
    EIP,Nat.choose_two_right,FMF]

theorem CVN (T YS S:ℕ):
    channelCount T YS S=AQJ T YS S:=
  (EAC T YS S).trans (ENK T YS S)

open CS Lower80899.Oracle
open FV (rawFlag)
open RCN095 DY

def BZP
    (delta dT dY dS T YS S:ℕ):ℕ→ℕ
  | 0=>0
  | fuel+1=>
      delta*AQJ T YS S+
        BZP delta dT dY dS
          (T-dT) (YS-dY) (S-dS) fuel

theorem EWC
    (delta dT dY dS T YS S fuel:ℕ):
    BZP delta dT dY dS T YS S fuel=
      LH delta dT dY dS T YS S fuel:=by
  induction fuel generalizing T YS S with
  | zero=>rfl
  | succ fuel ih=>
      simp only [BZP,LH]
      rw [← CVN,ih]

def evalBand (s:EA) (p:FlagDegree):ℕ:=
  BZP 50165 (total p) (middle p) p.all
    (s.totalCap-total p) (s.middleCap-middle p)
    (s.slopeCap-p.all) (s.fuel p)

theorem evalBand_eq (s:EA) (p:FlagDegree):
    evalBand s p=s.band p:=by
  unfold evalBand EA.band
  exact EWC _ _ _ _ _ _ _ _

def ABC
    (w Dh delta dc dT dY dS T YS S:ℕ):ℕ→ℕ
  | 0=>0
  | fuel+1=>
      delta*AQJ T (min YS (thinTop w Dh S)) S+
        ABC w (Dh-delta-dc) delta dc dT dY dS
          (T-dT) (YS-dY) (S-dS) fuel

theorem EHP
    (w Dh delta dc dT dY dS T YS S fuel:ℕ):
    ABC w Dh delta dc dT dY dS T YS S fuel=
      HN w Dh delta dc dT dY dS T YS S fuel:=by
  induction fuel generalizing Dh T YS S with
  | zero=>rfl
  | succ fuel ih=>
      simp only [ABC,HN]
      rw [← CVN,ih]

def evalBandThin (s:EA) (p:FlagDegree):ℕ:=
  ABC 131071 (s.contactCap p) 50165 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap-total p) (s.middleCap-middle p)
    (s.slopeCap-p.all) (s.fuel p)

theorem GGQ (s:EA) (p:FlagDegree):
    evalBandThin s p=s.bandThin p:=by
  unfold evalBandThin EA.bandThin
  exact EHP _ _ _ _ _ _ _ _ _ _ _

def DDX (s:EA) (p:FlagDegree):Prop:=
  1≤p.all∧total p≤s.totalCap∧middle p≤s.middleCap∧
    p.all≤s.slopeCap∧(evalBandThin s p<s.gap∨evalBand s p<s.gap)

instance (s:EA) (p:FlagDegree):
    Decidable (DDX s p):=by
  unfold DDX
  infer_instance

theorem EUB (s:EA) (p:FlagDegree):
    DDX s p ↔ s.Routeable p:=by
  unfold DDX EA.Routeable
  rw [evalBand_eq,GGQ,or_comm]

def QM
    (s:EA) (r v threshold:ℕ):Prop:=
  11192-(r+v)<threshold∨DDX s (rawFlag r v threshold)

instance (s:EA) (r v threshold:ℕ):
    Decidable (QM s r v threshold):=by
  unfold QM
  infer_instance

theorem DHC (s:EA) (r v threshold z:ℕ)
    (hs:11192≤s.totalCap) (hz:r+v+z≤11192) (ht:threshold≤z)
    (hc:QM s r v threshold):
    s.Routeable (rawFlag r v z):=by
  rcases hc with hbad | hroute
  · omega
  · exact Lower80899.PhaseRows.DZI s ht (hz.trans hs)
      ((EUB _ _).mp hroute)
end Lower80899.AMY
end MergedPart0
section MergedPart1
set_option Elab.async true
namespace Lower80899.EZE
open RCN095 DY CS
open FV (rawFlag)
open Lower80899.Oracle Lower80899.AMY
open Lower80899.PhaseRows
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def indexedThin (w Dh delta dc dT dY dS T YS S:ℕ):ℕ→ℕ
  | 0=>0
  | n+1=>indexedThin w Dh delta dc dT dY dS T YS S n+
      delta*AQJ (T-n*dT)
        (min (YS-n*dY) (thinTop w (Dh-n*(delta+dc)) (S-n*dS))) (S-n*dS)

theorem FWA (w Dh delta dc dT dY dS T YS S n:ℕ):
    indexedThin w Dh delta dc dT dY dS T YS S (n+1)=
      delta*AQJ T (min YS (thinTop w Dh S)) S+
        indexedThin w (Dh-delta-dc) delta dc dT dY dS (T-dT) (YS-dY) (S-dS) n:=by
  induction n with
  | zero=>simp [indexedThin]
  | succ n ih=>
      rw [indexedThin,ih,indexedThin]
      have shift (x d:ℕ):x-(n+1)*d=(x-d)-n*d:=by
        rw [Nat.add_mul,Nat.one_mul,Nat.sub_sub]
        omega
      rw [shift T dT,shift YS dY,shift S dS,shift Dh (delta+dc)]
      rw [Nat.sub_sub]
      omega

theorem GLU (w Dh delta dc dT dY dS T YS S fuel:ℕ):
    indexedThin w Dh delta dc dT dY dS T YS S fuel=
      ABC w Dh delta dc dT dY dS T YS S fuel:=by
  induction fuel generalizing Dh T YS S with
  | zero=>rfl
  | succ fuel ih=>
      rw [FWA,ABC,ih]

def indexedBand (s:EA) (p:FlagDegree):ℕ:=
  indexedThin 131071 (s.contactCap p) 50165 (contactDec p)
    (total p) (middle p) p.all (s.totalCap-total p)
    (s.middleCap-middle p) (s.slopeCap-p.all) (s.fuel p)

theorem GRA (s:EA) (p:FlagDegree):
    indexedBand s p=evalBandThin s p:=GLU _ _ _ _ _ _ _ _ _ _ _

def DVX (s:EA) (r v threshold:ℕ):Prop:=
  11192-(r+v)<threshold∨
    let p:=rawFlag r v threshold
    1≤p.all∧total p≤s.totalCap∧middle p≤s.middleCap∧
      p.all≤s.slopeCap∧indexedBand s p<s.gap
instance (s:EA) (r v threshold:ℕ):
    Decidable (DVX s r v threshold):=by
  unfold DVX;infer_instance

theorem FDE (s:EA) (r v threshold:ℕ)
    (h:DVX s r v threshold):
    QM s r v threshold:=by
  rcases h with h | ⟨hr,ht,hy,hs,hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨hr,ht,hy,hs,Or.inl ((GRA _ _) ▸ hb)⟩

end Lower80899.EZE

namespace Lower80899.EUA
open scoped BigOperators
open IL Lower80899.AMY
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def boxPoly (w A B C:ℤ):ℤ:=
  (C+w)*(3*(A+w)*(C+2*w)+C*(C+2*w)+6*A*B+9*w*B+3*B*C+3*B*B)

theorem FWD (c:ℕ):
    2*(c+2).choose 2=(c+2)*(c+1):=by
  have h:=Nat.descFactorial_eq_factorial_mul_choose (c+2) 2
  simpa [Nat.descFactorial,Nat.factorial,Nat.mul_comm] using h.symm

theorem FIM (c:ℕ):
    6*(c+2).choose 3=(c+2)*(c+1)*c:=by
  have h:=Nat.descFactorial_eq_factorial_mul_choose (c+2) 3
  simpa [Nat.descFactorial,Nat.factorial,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h.symm

theorem half_succ (c:ℕ):2*((c+1)*c/2)=(c+1)*c:=by
  have h:2 ∣ (c+1)*c:=by
    simpa [Nat.mul_comm,Nat.add_comm] using
      (even_iff_two_dvd.mp (Nat.even_mul_succ_self c))
  simpa [Nat.mul_comm] using Nat.div_mul_cancel h

theorem half_pred (b:ℕ):2*(b*(b-1)/2)+b=b*b:=by
  cases b with
  | zero=>decide
  | succ b=>
      simp only [Nat.add_sub_cancel]
      rw [half_succ]
      ring

theorem channel_raw (a b c:ℕ):
    6*(channelCount (a+b+c) (b+c) c:ℤ)=boxPoly 1 a b c:=by
  rw [EAC]
  have hm:min (a+b+c) (b+c)=b+c:=min_eq_right (by omega)
  have hk:min c (b+c)=c:=min_eq_left (by omega)
  simp only [DHA,hm,hk]
  have hA:a+b+c+1-(b+c)=a+1:=by omega
  have hB:b+c-c=b:=by omega
  rw [hA,hB]
  have hsub:(c+1)*c/2≤(c+1)*(a+1+c+1):=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (by omega))
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_sub hsub]
  have h2:(2:ℤ)*((c+2).choose 2:ℤ)=(c+2)*(c+1):=by
    exact_mod_cast FWD c
  have h3:(6:ℤ)*((c+2).choose 3:ℤ)=(c+2)*(c+1)*c:=by
    exact_mod_cast FIM c
  have hc:(2:ℤ)*(((c+1)*c/2:ℕ):ℤ)=(c+1)*c:=by
    exact_mod_cast half_succ c
  have hb:(2:ℤ)*((b*(b-1)/2:ℕ):ℤ)+b=b*b:=by
    exact_mod_cast half_pred b
  unfold boxPoly
  nlinarith only [h3,congrArg (fun x:ℤ=>3*(a+1)*x) h2,
    congrArg (fun x:ℤ=>3*(b:ℤ)*x) hc,
    congrArg (fun x:ℤ=>3*(c+1)*x) hb]

theorem FLV (T YS S:ℕ):
    channelCount T YS S=
      channelCount (T-min T YS+(min T YS-min S (min T YS))+min S (min T YS))
        (min T YS-min S (min T YS)+min S (min T YS)) (min S (min T YS)):=by
  have hU:=Nat.min_le_left T YS
  have hk:=Nat.min_le_right S (min T YS)
  have hT:T-min T YS+(min T YS-min S (min T YS))+min S (min T YS)=T:=by omega
  have hY:min T YS-min S (min T YS)+min S (min T YS)=min T YS:=by omega
  rw [hT,hY]
  rw [BAJ,BAJ]
  rw [min_eq_right hU]
  rw [VJ,VJ]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' :x≤min T YS:=by have:=Finset.mem_range.mp hx;omega
  unfold cappedTerm
  rw [min_assoc,min_eq_right hx']

theorem channel_poly (T YS S:ℕ):
    6*(channelCount T YS S:ℤ)=
      boxPoly 1 ((T-min T YS:ℕ):ℤ) ((min T YS-min S (min T YS):ℕ):ℤ) (min S (min T YS):ℕ):=by
  rw [FLV T YS S]
  exact channel_raw _ _ _

theorem GNF (w a b c:ℤ):
    boxPoly w (w*a) (w*b) (w*c)=w^3*boxPoly 1 a b c:=by
  unfold boxPoly
  ring

theorem boxPoly_mono (w a b c A B C:ℤ)
    (hw:0≤w) (ha:0≤a) (hb:0≤b) (hc:0≤c)
    (hA:a≤A) (hB:b≤B) (hC:c≤C):
    boxPoly w a b c≤boxPoly w A B C:=by
  have hA0:=ha.trans hA
  have hB0:=hb.trans hB
  have hC0:=hc.trans hC
  unfold boxPoly
  gcongr<;>positivity

theorem FMT (T YS S Dh:ℕ):
    6*131071^3*(channelCount T (min YS ((Dh+S-1)/131071)) S:ℤ)≤
      boxPoly 131071
        (131071*T-min (131071*T) (min (131071*YS) (Dh+S))+131071)
        (min (131071*T) (min (131071*YS) (Dh+S))-
          min (131071*S) (min (131071*T) (min (131071*YS) (Dh+S))))
        (min (131071*S) (min (131071*T) (min (131071*YS) (Dh+S)))):=by
  let U:=min T (min YS ((Dh+S-1)/131071))
  let C:=min S U
  let V:ℤ:=min (131071*T) (min (131071*YS) (Dh+S))
  let K:ℤ:=min (131071*S) V
  have hU:U≤T:=Nat.min_le_left _ _
  have hC:C≤U:=Nat.min_le_right _ _
  have hround:131071*(U:ℤ)≤V∧V≤131071*(U:ℤ)+131071:=by
    dsimp [U,V]
    omega
  have hK:131071*(C:ℤ)≤K:=by dsimp [C,K];omega
  have hB:131071*((U-C:ℕ):ℤ)≤V-K:=by
    dsimp [C,K]
    omega
  have hA:131071*((T-U:ℕ):ℤ)≤131071*T-V+131071:=by omega
  have hm:=boxPoly_mono 131071
    (131071*((T-U:ℕ):ℤ)) (131071*((U-C:ℕ):ℤ)) (131071*C)
    (131071*T-V+131071) (V-K) K (by norm_num) (by positivity)
    (by positivity) (by positivity) hA hB hK
  rw [GNF,← channel_poly] at hm
  convert hm using 1<;>push_cast<;>ring

structure Affine where
  constant:ℤ
  slope:ℤ
  deriving DecidableEq,Repr

def Affine.eval (a:Affine) (i:ℕ):ℤ:=a.constant+a.slope*i

def triplePrefix (a b c:Affine) (n:ℕ):ℤ:=
  let x:ℤ:=n
  12*x*(a.constant*b.constant*c.constant)+
  6*x*(x-1)*(a.slope*b.constant*c.constant+a.constant*b.slope*c.constant+a.constant*b.constant*c.slope)+
  2*x*(x-1)*(2*x-1)*(a.slope*b.slope*c.constant+a.slope*b.constant*c.slope+a.constant*b.slope*c.slope)+
  3*x*x*(x-1)*(x-1)*(a.slope*b.slope*c.slope)

theorem GIF (a b c:Affine) (n:ℕ):
    triplePrefix a b c n=12*∑ i ∈ Finset.range n,a.eval i*b.eval i*c.eval i:=by
  induction n with
  | zero=>simp [triplePrefix]
  | succ n ih=>
      rw [Finset.sum_range_succ,mul_add,← ih]
      simp only [triplePrefix,Affine.eval,Nat.cast_add,Nat.cast_one]
      ring

def Affine.add (a b:Affine):Affine:=⟨a.constant+b.constant,a.slope+b.slope⟩
def Affine.sub (a b:Affine):Affine:=⟨a.constant-b.constant,a.slope-b.slope⟩
def Affine.scale (a:Affine) (k:ℤ):Affine:=⟨k*a.constant,k*a.slope⟩
def Affine.plus (a:Affine) (k:ℤ):Affine:=⟨a.constant+k,a.slope⟩

@[simp] theorem Affine.eval_add (a b:Affine) (i:ℕ):
    (a.add b).eval i=a.eval i+b.eval i:=by simp [Affine.add,Affine.eval];ring
@[simp] theorem Affine.eval_sub (a b:Affine) (i:ℕ):
    (a.sub b).eval i=a.eval i-b.eval i:=by simp [Affine.sub,Affine.eval];ring
@[simp] theorem Affine.eval_scale (a:Affine) (k:ℤ) (i:ℕ):
    (a.scale k).eval i=k*a.eval i:=by simp [Affine.scale,Affine.eval];ring
@[simp] theorem Affine.eval_plus (a:Affine) (k:ℤ) (i:ℕ):
    (a.plus k).eval i=a.eval i+k:=by simp [Affine.plus,Affine.eval];ring

def boxPrefix (a b c:Affine) (n:ℕ):ℤ:=
  3*triplePrefix (c.plus 131071) (a.plus 131071) (c.plus (2*131071)) n+
  triplePrefix (c.plus 131071) c (c.plus (2*131071)) n+
  6*triplePrefix (c.plus 131071) a b n+
  9*131071*triplePrefix (c.plus 131071) b ⟨1,0⟩ n+
  3*triplePrefix (c.plus 131071) b c n+
  3*triplePrefix (c.plus 131071) b b n

def BID (a b c:Affine) (n:ℕ):ℤ:=
  if n=0 then 0 else
  let x:ℤ:=n
  let w:ℤ:=131071
  let A:=a.constant
  let B:=b.constant
  let C:=c.constant
  let α:=a.slope
  let β:=b.slope
  let γ:=c.slope
  let q0:=3*(A+w)*(C+2*w)+C*(C+2*w)+6*A*B+9*w*B+3*B*C+3*B*B
  let q1:=3*((A+w)*γ+α*(C+2*w))+γ*(2*C+2*w)+
    6*(A*β+α*B)+9*w*β+3*(B*γ+β*C)+6*B*β
  let q2:=3*α*γ+γ*γ+6*α*β+3*β*γ+3*β*β
  let s0:=12*x
  let s1:=6*x*(x-1)
  let s2:=2*x*(x-1)*(2*x-1)
  let s3:=3*x*x*(x-1)*(x-1)
  q0*(s0*(C+w)+s1*γ)+q1*(s1*(C+w)+s2*γ)+q2*(s2*(C+w)+s3*γ)

theorem DZQ (a b c:Affine) (n:ℕ):
    BID a b c n=boxPrefix a b c n:=by
  unfold BID
  split_ifs with hn
  · subst n
    simp [boxPrefix,triplePrefix]
  · simp only [boxPrefix,triplePrefix,Affine.plus]
    ring

theorem boxPrefix_eq (a b c:Affine) (n:ℕ):
    boxPrefix a b c n=
      12*∑ i ∈ Finset.range n,boxPoly 131071 (a.eval i) (b.eval i) (c.eval i):=by
  simp only [boxPrefix,GIF,Affine.eval_plus]
  apply Eq.symm
  calc
    _= ∑ i ∈ Finset.range n,12*boxPoly 131071 (a.eval i) (b.eval i) (c.eval i):=by rw [Finset.mul_sum]
    _= ∑ i ∈ Finset.range n,
        ((3*(12*((c.eval i+131071)*(a.eval i+131071)*(c.eval i+2*131071))))+
        (12*((c.eval i+131071)*c.eval i*(c.eval i+2*131071)))+
        (6*(12*((c.eval i+131071)*a.eval i*b.eval i)))+
        (9*131071*(12*((c.eval i+131071)*b.eval i*(Affine.eval ⟨1,0⟩ i))))+
        (3*(12*((c.eval i+131071)*b.eval i*c.eval i)))+
        (3*(12*((c.eval i+131071)*b.eval i*b.eval i)))):=by
      apply Finset.sum_congr rfl
      intro i _
      simp only [boxPoly,Affine.eval]
      ring
    _=_:=by simp only [Finset.sum_add_distrib,← Finset.mul_sum]

theorem FNE (a b c:Affine) (lo hi:ℕ) (h:lo≤hi):
    boxPrefix a b c hi-boxPrefix a b c lo=
      12*∑ i ∈ Finset.Ico lo hi,boxPoly 131071 (a.eval i) (b.eval i) (c.eval i):=by
  rw [boxPrefix_eq,boxPrefix_eq]
  rw [← Finset.sum_range_add_sum_Ico _ h]
  ring

theorem Affine.GJF (a:Affine) (lo hi i:ℕ)
    (hlo:lo≤ i) (hhi:i≤hi) (h0:0≤a.eval lo) (h1:0≤a.eval hi):
    0≤a.eval i:=by
  unfold Affine.eval at*
  rcases le_total 0 a.slope with hs | hs
  · have hh:=mul_le_mul_of_nonneg_left (show (lo:ℤ)≤ i by omega) hs
    omega
  · have hh:=mul_le_mul_of_nonpos_left (show (i:ℤ)≤hi by omega) hs
    omega

end Lower80899.EUA

namespace Lower80899.BLW
open scoped BigOperators
open Lower80899.EUA Lower80899.EZE
open Lower80899.AMY IL
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

structure Input where
  T:ℕ
  YS:ℕ
  S:ℕ
  Dh:ℕ
  dT:ℕ
  dY:ℕ
  dS:ℕ
  dDh:ℕ
  fuel:ℕ
  deriving DecidableEq,Repr

def Input.atT (p:Input):Affine:=⟨p.T,-(p.dT:ℤ)⟩
def Input.atY (p:Input):Affine:=⟨p.YS,-(p.dY:ℤ)⟩
def Input.atS (p:Input):Affine:=⟨p.S,-(p.dS:ℤ)⟩
def Input.atDh (p:Input):Affine:=⟨p.Dh,-(p.dDh:ℤ)⟩
def Input.count (p:Input) (i:ℕ):ℕ:=
  channelCount (p.T-i*p.dT)
    (min (p.YS-i*p.dY) ((p.Dh-i*p.dDh+(p.S-i*p.dS)-1)/131071)) (p.S-i*p.dS)

def Input.dh (p:Input) (code:ℕ):Affine:=if 6≤code then p.atDh else ⟨0,0⟩
def Input.u (p:Input) (code:ℕ):Affine:=
  if code/2%3=0 then p.atT.scale 131071
  else if code/2%3=1 then p.atY.scale 131071
  else (p.dh code).add p.atS
def Input.c (p:Input) (code:ℕ):Affine:=
  if code%2=0 then p.atS.scale 131071 else p.u code
def Input.a (p:Input) (code:ℕ):Affine:=((p.atT.scale 131071).sub (p.u code)).plus 131071
def Input.b (p:Input) (code:ℕ):Affine:=(p.u code).sub (p.c code)

def conditions (p:Input) (code:ℕ):List Affine:=
  [p.atT,p.atY,p.atS,if 6≤code then p.atDh else p.atDh.scale (-1),
    (p.atT.scale 131071).sub (p.u code),
    (p.atY.scale 131071).sub (p.u code),
    ((p.dh code).add p.atS).sub (p.u code),
    (p.atS.scale 131071).sub (p.c code),
    (p.u code).sub (p.c code)]

def ValidAt (p:Input) (code i:ℕ):Prop:=
  ∀a ∈ conditions p code,0≤a.eval i
def FastValidAt (p:Input) (code i:ℕ):Prop:=
  let t:=p.atT.eval i
  let y:=p.atY.eval i
  let s:=p.atS.eval i
  let u:=(p.u code).eval i
  let c:=(p.c code).eval i
  0≤t∧0≤y∧0≤s∧
    0≤(if 6≤code then p.atDh else p.atDh.scale (-1)).eval i∧
    u≤131071*t∧u≤131071*y∧u≤(p.dh code).eval i+s∧
    c≤131071*s∧c≤u
instance (p:Input) (code i:ℕ):Decidable (FastValidAt p code i):=by
  unfold FastValidAt
  infer_instance

theorem EZH (p:Input) (code i:ℕ):
    ValidAt p code i ↔ FastValidAt p code i:=by
  simp only [ValidAt,FastValidAt,conditions,List.mem_cons,
    List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    Affine.eval_sub,Affine.eval_scale,Affine.eval_add,sub_nonneg]

instance (p:Input) (code i:ℕ):Decidable (ValidAt p code i):=
  decidable_of_iff (FastValidAt p code i) (EZH p code i).symm

theorem GGU (p:Input) (code lo hi i:ℕ)
    (hlo:lo≤ i) (hhi:i≤hi) (h0:ValidAt p code lo) (h1:ValidAt p code hi):
    ValidAt p code i:=by
  intro a ha
  exact a.GJF lo hi i hlo hhi (h0 a ha) (h1 a ha)

theorem linear_cast (t d i:ℕ) (h:0≤Affine.eval ⟨t,-(d:ℤ)⟩ i):
    ((t-i*d:ℕ):ℤ)=Affine.eval ⟨t,-(d:ℤ)⟩ i:=by
  simp only [Affine.eval,neg_mul] at*
  have hc:((i*d:ℕ):ℤ)=(d:ℤ)*i:=by push_cast;ring
  omega

theorem GWJ (p:Input) (code i:ℕ) (h:ValidAt p code i):
    6*131071^3*(p.count i:ℤ)≤
      boxPoly 131071 ((p.a code).eval i) ((p.b code).eval i) ((p.c code).eval i):=by
  simp only [ValidAt,conditions,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq] at h
  rcases h with ⟨hT,hY,hS,hD,hU0,hU1,hU2,hC0,hC1⟩
  have htc:=linear_cast p.T p.dT i hT
  have hyc:=linear_cast p.YS p.dY i hY
  have hsc:=linear_cast p.S p.dS i hS
  change ((p.T-i*p.dT:ℕ):ℤ)=p.atT.eval i at htc
  change ((p.YS-i*p.dY:ℕ):ℤ)=p.atY.eval i at hyc
  change ((p.S-i*p.dS:ℕ):ℤ)=p.atS.eval i at hsc
  have hdc:((p.Dh-i*p.dDh:ℕ):ℤ)=(p.dh code).eval i:=by
    unfold Input.dh
    split_ifs with hd
    · simp only [hd,↓reduceIte] at hD
      exact linear_cast p.Dh p.dDh i hD
    · simp only [hd,↓reduceIte,Affine.eval_scale] at hD
      simp only [Input.atDh,Affine.eval,neg_mul] at hD ⊢
      have hc:((i*p.dDh:ℕ):ℤ)=(p.dDh:ℤ)*i:=by push_cast;ring
      omega
  simp only [Affine.eval_sub,Affine.eval_scale,Affine.eval_add] at hU0 hU1 hU2 hC0 hC1
  have hue:(p.u code).eval i=
      min (131071*p.atT.eval i) (min (131071*p.atY.eval i) ((p.dh code).eval i+p.atS.eval i)):=by
    by_cases h0:code/2%3=0
    · simp only [Input.u,h0,↓reduceIte,Affine.eval_scale] at hU0 hU1 hU2 ⊢
      omega
    · by_cases h1:code/2%3=1
      · simp only [Input.u,h0,h1,Nat.one_ne_zero,↓reduceIte,Affine.eval_scale] at hU0 hU1 hU2 ⊢
        omega
      · simp only [Input.u,h0,h1,Nat.one_ne_zero,↓reduceIte,Affine.eval_add] at hU0 hU1 hU2 ⊢
        omega
  have hce:(p.c code).eval i=min (131071*p.atS.eval i) ((p.u code).eval i):=by
    by_cases h0:code%2=0<;>
      simp only [Input.c,h0,↓reduceIte,Affine.eval_scale] at hC0 hC1 ⊢ <;>omega
  have hb:=FMT (p.T-i*p.dT) (p.YS-i*p.dY) (p.S-i*p.dS) (p.Dh-i*p.dDh)
  push_cast at hb
  rw [htc,hyc,hsc,hdc,← hue,← hce] at hb
  norm_num only [Int.reducePow,Int.reduceMul]
  simpa only [Input.count,Input.a,Input.b,Affine.eval_plus,Affine.eval_sub,Affine.eval_scale] using hb

def RunValid (p:Input) (start:ℕ) (run:Run):Prop:=
  start<run.stop∧run.stop≤p.fuel∧
    ValidAt p run.code start∧ValidAt p run.code (run.stop-1)
instance (p:Input) (start:ℕ) (run:Run):Decidable (RunValid p start run):=by
  unfold RunValid;infer_instance

def runUpper (p:Input) (start:ℕ) (run:Run):ℤ:=
  BID (p.a run.code) (p.b run.code) (p.c run.code) run.stop-
  BID (p.a run.code) (p.b run.code) (p.c run.code) start

theorem GPM (p:Input) (start:ℕ) (run:Run)
    (h:RunValid p start run):
    72*131071^3*(∑ i ∈ Finset.Ico start run.stop,(p.count i:ℤ))≤runUpper p start run:=by
  rw [runUpper,DZQ,DZQ,FNE _ _ _ _ _ h.1.le]
  have hs:(∑ i ∈ Finset.Ico start run.stop,6*131071^3*(p.count i:ℤ))≤
      ∑ i ∈ Finset.Ico start run.stop,
        boxPoly 131071 ((p.a run.code).eval i) ((p.b run.code).eval i) ((p.c run.code).eval i):=by
    apply Finset.sum_le_sum
    intro i hi
    exact GWJ p run.code i (GGU p run.code start (run.stop-1) i
      (Finset.mem_Ico.mp hi).1 (by have:=(Finset.mem_Ico.mp hi).2;omega) h.2.2.1 h.2.2.2)
  rw [← Finset.mul_sum] at hs
  linarith

def RunsValid (p:Input):ℕ→List Run→Prop
  | start,[]=>start=p.fuel
  | start,run::runs=>RunValid p start run∧RunsValid p run.stop runs
instance (p:Input) (start:ℕ) (runs:List Run):Decidable (RunsValid p start runs):=by
  induction runs generalizing start with
  | nil=>unfold RunsValid;infer_instance
  | cons run runs ih=>unfold RunsValid;infer_instance

def runsUpper (p:Input):ℕ→List Run→ℤ
  | _,[]=>0
  | start,run::runs=>runUpper p start run+runsUpper p run.stop runs

theorem GIX (p:Input) (start:ℕ) (runs:List Run)
    (h:RunsValid p start runs):
    72*131071^3*(∑ i ∈ Finset.Ico start p.fuel,(p.count i:ℤ))≤runsUpper p start runs:=by
  induction runs generalizing start with
  | nil=>simp only [RunsValid] at h;simp [h,runsUpper]
  | cons run runs ih=>
      have h0:=GPM p start run h.1
      have h1:=ih run.stop h.2
      rw [← Finset.sum_Ico_consecutive _ h.1.1.le h.1.2.1]
      simp only [runsUpper]
      linarith

open Lower80899.Oracle CS
open RCN095 DY
open FV (rawFlag)

def ofSource (s:EA) (p:FlagDegree):Input:=
  ⟨s.totalCap-total p,s.middleCap-middle p,s.slopeCap-p.all,s.contactCap p,
    total p,middle p,p.all,50165+contactDec p,s.fuel p⟩

theorem indexed_sum (p:Input) (dc n:ℕ) (hd:p.dDh=50165+dc):
    (indexedThin 131071 p.Dh 50165 dc p.dT p.dY p.dS p.T p.YS p.S n:ℤ)=
      50165*∑ i ∈ Finset.range n,(p.count i:ℤ):=by
  induction n with
  | zero=>simp [indexedThin]
  | succ n ih=>
      rw [indexedThin,Nat.cast_add,Nat.cast_mul,ih,Finset.sum_range_succ]
      simp only [Input.count,CVN,thinTop,hd]
      push_cast
      ring

theorem source_sum (s:EA) (p:FlagDegree):
    (indexedBand s p:ℤ)=
      50165*∑ i ∈ Finset.range (ofSource s p).fuel,((ofSource s p).count i:ℤ):=
  indexed_sum (ofSource s p) (contactDec p) (s.fuel p) rfl

def Sufficient (s:EA) (r v threshold:ℕ) (runs:List Run):Prop:=
  11192-(r+v)<threshold∨
    let p:=rawFlag r v threshold
    1≤p.all∧total p≤s.totalCap∧middle p≤s.middleCap∧p.all≤s.slopeCap∧
      RunsValid (ofSource s p) 0 runs∧
      50165*runsUpper (ofSource s p) 0 runs<(s.gap:ℤ)*(72*131071^3)
instance (s:EA) (r v threshold:ℕ) (runs:List Run):
    Decidable (Sufficient s r v threshold runs):=by
  unfold Sufficient;infer_instance

theorem GDF (s:EA) (r v threshold:ℕ) (runs:List Run)
    (h:Sufficient s r v threshold runs):QM s r v threshold:=by
  rcases h with h | ⟨hr,ht,hy,hs,hvalid,hgap⟩
  · exact Or.inl h
  apply FDE
  refine Or.inr ⟨hr,ht,hy,hs,?_⟩
  have hb:=GIX (ofSource s (rawFlag r v threshold)) 0 runs hvalid
  rw [Nat.Ico_zero_eq_range] at hb
  have he:=source_sum s (rawFlag r v threshold)
  have hi:(indexedBand s (rawFlag r v threshold):ℤ)<s.gap:=by
    nlinarith only [hgap,congrArg (fun x:ℤ=>(72*131071^3)*x) he,
      mul_le_mul_of_nonneg_left hb (show (0:ℤ)≤50165 by norm_num)]
  exact_mod_cast hi

end Lower80899.BLW
end MergedPart1
section MergedPart2
namespace EMO
open Lower80899.BLW Lower80899.EUA Lower80899.Oracle Lower80899.AMY
open FV (rawFlag)
open RCN095 DY CS IL
set_option autoImplicit false
set_option maxRecDepth 100000

def minK (a b:ℕ):ℕ:=cond (Nat.ble a b) a b

theorem minK_eq (a b:ℕ):minK a b=min a b:=by
  unfold minK
  by_cases h:a≤b
  · rw [Nat.ble_eq_true_of_le h,min_eq_left h];rfl
  · rw [show Nat.ble a b=false from Bool.eq_false_iff.mpr (fun hb=>h (Nat.le_of_ble_eq_true hb)),
      min_eq_right (by omega)];rfl

def channelK (T YS S:ℕ):ℕ:=
  let U:=minK T YS
  let B:=Nat.sub (Nat.add T 1) U
  let k:=minK S U
  let n:=Nat.sub U k
  let S1:=Nat.add S 1
  let C:=Nat.sub (Nat.mul S1 (Nat.add (Nat.add B S) 1)) (Nat.div (Nat.mul S1 S) 2)
  let k2:=Nat.add k 2
  Nat.add (Nat.add (Nat.add (Nat.mul B (Nat.div (Nat.mul k2 (Nat.sub k2 1)) 2))
    (Nat.div (Nat.mul (Nat.mul k2 (Nat.sub k2 1)) (Nat.sub k2 2)) 6))
    (Nat.mul n C)) (Nat.mul S1 (Nat.div (Nat.mul n (Nat.sub n 1)) 2))

theorem channelK_eq (T YS S:ℕ):channelK T YS S=AQJ T YS S:=by
  simp only [channelK,AQJ,FCL,EIP,minK_eq]
  rfl

def thinLoopK (w delta dc dT dY dS fuel:ℕ):ℕ→ℕ→ℕ→ℕ→ℕ:=
  Nat.rec (motive:=fun _=>ℕ→ℕ→ℕ→ℕ→ℕ) (fun _ _ _ _=>0)
    (fun _ ih Dh T YS S=>Nat.add
      (Nat.mul delta (channelK T (minK YS (Nat.div (Nat.sub (Nat.add Dh S) 1) w)) S))
      (ih (Nat.sub (Nat.sub Dh delta) dc) (Nat.sub T dT) (Nat.sub YS dY) (Nat.sub S dS))) fuel

theorem thinLoopK_eq (w delta dc dT dY dS fuel Dh T YS S:ℕ):
    thinLoopK w delta dc dT dY dS fuel Dh T YS S=
      ABC w Dh delta dc dT dY dS T YS S fuel:=by
  induction fuel generalizing Dh T YS S with
  | zero=>rfl
  | succ fuel ih=>
    show Nat.add _ (thinLoopK w delta dc dT dY dS fuel _ _ _ _)=_
    rw [ih,ABC,channelK_eq,minK_eq]
    rfl

def bandThinK (s:EA) (p:FlagDegree):ℕ:=
  thinLoopK 131071 50165 (contactDec p) (total p) (middle p) p.all (s.fuel p)
    (s.contactCap p) (s.totalCap-total p) (s.middleCap-middle p) (s.slopeCap-p.all)

theorem bandThinK_eq (s:EA) (p:FlagDegree):bandThinK s p=evalBandThin s p:=
  thinLoopK_eq _ _ _ _ _ _ _ _ _ _ _

def fastK (s:EA) (r v threshold:ℕ):Bool:=
  Nat.blt (11192-(r+v)) threshold ||
    (let p:=rawFlag r v threshold
     Nat.ble 1 p.all && Nat.ble (total p) s.totalCap && Nat.ble (middle p) s.middleCap &&
       Nat.ble p.all s.slopeCap && Nat.blt (bandThinK s p) s.gap)

theorem fastK_sound (s:EA) (r v threshold:ℕ) (h:fastK s r v threshold=true):
    QM s r v threshold:=by
  simp only [fastK,Bool.or_eq_true,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq,bandThinK_eq] at h
  rcases h with h | ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1,h2,h3,h4,Or.inl h5⟩

def validN (p:Input) (code i:ℕ):Bool:=
  let t:=p.T-i*p.dT
  let y:=p.YS-i*p.dY
  let s:=p.S-i*p.dS
  let hasD:=Nat.ble 6 code
  let dh:=cond hasD (p.Dh-i*p.dDh) 0
  let m:=code/2%3
  let u:=cond (Nat.beq m 0) (131071*t) (cond (Nat.beq m 1) (131071*y) (dh+s))
  let c:=cond (Nat.beq (code%2) 0) (131071*s) u
  Nat.ble (i*p.dT) p.T && Nat.ble (i*p.dY) p.YS && Nat.ble (i*p.dS) p.S &&
    cond hasD (Nat.ble (i*p.dDh) p.Dh) (Nat.ble p.Dh (i*p.dDh)) &&
    Nat.ble u (131071*t) && Nat.ble u (131071*y) && Nat.ble u (dh+s) &&
    Nat.ble c (131071*s) && Nat.ble c u

theorem affine_cast (t d i:ℕ) (h:i*d≤t):
    Affine.eval ⟨t,-(d:ℤ)⟩ i=((t-i*d:ℕ):ℤ):=by
  simp only [Affine.eval]
  push_cast [Nat.cast_sub h]
  ring

theorem validN_sound (p:Input) (code i:ℕ) (h:validN p code i=true):ValidAt p code i:=by
  rw [EZH]
  unfold validN at h
  simp only [Bool.and_eq_true,Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hT,hY⟩,hS⟩,hD⟩,h1⟩,h2⟩,h3⟩,h4⟩,h5⟩:=h
  have et:p.atT.eval i=((p.T-i*p.dT:ℕ):ℤ):=affine_cast _ _ _ hT
  have ey:p.atY.eval i=((p.YS-i*p.dY:ℕ):ℤ):=affine_cast _ _ _ hY
  have es:p.atS.eval i=((p.S-i*p.dS:ℕ):ℤ):=affine_cast _ _ _ hS
  generalize p.T-i*p.dT=t at et h1 h2 h3 h4 h5
  generalize p.YS-i*p.dY=y at ey h1 h2 h3 h4 h5
  generalize p.S-i*p.dS=s at es h1 h2 h3 h4 h5
  have key:0≤(if 6≤code then p.atDh else p.atDh.scale (-1)).eval i∧
      (p.dh code).eval i=((cond (Nat.ble 6 code) (p.Dh-i*p.dDh) 0:ℕ):ℤ):=by
    by_cases hc:6≤code
    · have hb:Nat.ble 6 code=true:=Nat.ble_eq_true_of_le hc
      rw [hb] at hD
      have hD' :i*p.dDh≤p.Dh:=by simpa only [cond,Nat.ble_eq] using hD
      have e:=affine_cast p.Dh p.dDh i hD'
      rw [hb]
      simp only [Input.dh,if_pos hc,Input.atDh,cond,e]
      exact ⟨Int.natCast_nonneg _,trivial⟩
    · have hb:Nat.ble 6 code=false:=Bool.eq_false_iff.mpr (fun hb=>hc (Nat.le_of_ble_eq_true hb))
      rw [hb] at hD
      have hD' :p.Dh≤ i*p.dDh:=by simpa only [cond,Nat.ble_eq] using hD
      rw [hb]
      simp only [Input.dh,if_neg hc,Input.atDh,Affine.scale,Affine.eval,cond]
      refine ⟨?_,by simp⟩
      have hc' :((p.Dh:ℕ):ℤ)≤(i:ℤ)*(p.dDh:ℤ):=by exact_mod_cast hD'
      linarith
  obtain ⟨hDz,edh⟩:=key
  generalize cond (Nat.ble 6 code) (p.Dh-i*p.dDh) 0=dh at edh h1 h2 h3 h4 h5
  have eu:(p.u code).eval i=
      ((cond (Nat.beq (code/2%3) 0) (131071*t) (cond (Nat.beq (code/2%3) 1) (131071*y) (dh+s)):ℕ):ℤ):=by
    rcases (show code/2%3=0∨code/2%3=1∨code/2%3=2 by omega) with hm | hm | hm<;>
      simp only [Input.u,hm,Affine.eval_scale,Affine.eval_add,et,ey,es,edh,cond,Nat.beq,
        if_true,if_false,one_ne_zero,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one]<;>push_cast<;>ring
  generalize cond (Nat.beq (code/2%3) 0) (131071*t) (cond (Nat.beq (code/2%3) 1) (131071*y) (dh+s))=u
    at eu h1 h2 h3 h4 h5
  have ec:(p.c code).eval i=((cond (Nat.beq (code%2) 0) (131071*s) u:ℕ):ℤ):=by
    rcases (show code%2=0∨code%2=1 by omega) with hm | hm<;>
      simp only [Input.c,hm,Affine.eval_scale,es,eu,cond,Nat.beq,if_true,if_false,
        one_ne_zero]<;>push_cast<;>ring
  generalize cond (Nat.beq (code%2) 0) (131071*s) u=c at ec h4 h5
  simp only [FastValidAt]
  rw [et,ey,es,eu,ec,edh]
  exact ⟨Int.natCast_nonneg _,Int.natCast_nonneg _,Int.natCast_nonneg _,hDz,
    by exact_mod_cast h1,by exact_mod_cast h2,by exact_mod_cast h3,by exact_mod_cast h4,
    by exact_mod_cast h5⟩

def runsValidK (p:Input) (runs:List Run):ℕ→Bool:=
  List.rec (motive:=fun _=>ℕ→Bool) (fun start=>Nat.beq start p.fuel)
    (fun run _ ih start=>Bool.rec false (ih run.stop)
      (Nat.blt start run.stop && Nat.ble run.stop p.fuel &&
        validN p run.code start && validN p run.code (run.stop-1))) runs

theorem GAT (p:Input) (runs:List Run) (start:ℕ)
    (h:runsValidK p runs start=true):RunsValid p start runs:=by
  induction runs generalizing start with
  | nil=>exact Nat.eq_of_beq_eq_true h
  | cons run runs ih=>
    change Bool.rec false (runsValidK p runs run.stop) (Nat.blt start run.stop &&
      Nat.ble run.stop p.fuel && validN p run.code start && validN p run.code (run.stop-1))=true at h
    cases hb:(Nat.blt start run.stop && Nat.ble run.stop p.fuel &&
        validN p run.code start && validN p run.code (run.stop-1)) with
    | false=>rw [hb] at h;exact absurd h Bool.false_ne_true
    | true=>
      rw [hb] at h
      simp only [Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at hb
      exact ⟨⟨hb.1.1.1,hb.1.1.2,validN_sound _ _ _ hb.1.2,validN_sound _ _ _ hb.2⟩,ih _ h⟩

def sPow (x:ℕ):ℕ × ℕ × ℕ × ℕ:=
  let xx1:=x*(x-1)
  (12*x,6*xx1,2*xx1*(2*x-1),3*(xx1*xx1))

theorem sPow_mono {lo hi:ℕ} (h:lo≤hi):
    (sPow lo).1≤(sPow hi).1∧(sPow lo).2.1≤(sPow hi).2.1∧
      (sPow lo).2.2.1≤(sPow hi).2.2.1∧(sPow lo).2.2.2≤(sPow hi).2.2.2:=by
  have h1:lo*(lo-1)≤hi*(hi-1):=Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)
  have h2:2*lo-1≤2*hi-1:=Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 h) 1
  simp only [sPow]
  refine ⟨Nat.mul_le_mul_left 12 h,Nat.mul_le_mul_left 6 h1,Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2,
    Nat.mul_le_mul_left 3 (Nat.mul_le_mul h1 h1)⟩

theorem DNY (a b c:Affine) (n:ℕ):
    BID a b c n=
      let w:ℤ:=131071
      let A:=a.constant
      let B:=b.constant
      let C:=c.constant
      let α:=a.slope
      let β:=b.slope
      let γ:=c.slope
      let q0:=(C+2*w)*(3*A+3*w+C)+B*(6*A+9*w+3*C+3*B)
      let q1:=γ*(3*A+5*w+2*C+3*B)+α*(3*C+6*w+6*B)+β*(6*A+9*w+3*C+6*B)
      let q2:=γ*(3*α+γ+3*β)+β*(6*α+3*β)
      (C+w)*(q0*(sPow n).1+q1*(sPow n).2.1+q2*(sPow n).2.2.1)+
        γ*(q0*(sPow n).2.1+q1*(sPow n).2.2.1+q2*(sPow n).2.2.2):=by
  unfold BID sPow
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg (by omega)]
    have h1:((n-1:ℕ):ℤ)=(n:ℤ)-1:=by push_cast [Nat.cast_sub hn];ring
    have h2:((2*n-1:ℕ):ℤ)=2*(n:ℤ)-1:=by push_cast [Nat.cast_sub (by omega:1≤2*n)];ring
    simp only [Nat.cast_mul,Nat.cast_ofNat,h1,h2]
    ring

def runUpperK (p:Input) (start:ℕ) (run:Run):ℤ:=
  let a:=p.a run.code
  let b:=p.b run.code
  let c:=p.c run.code
  let w:ℤ:=131071
  let A:=a.constant
  let B:=b.constant
  let C:=c.constant
  let α:=a.slope
  let β:=b.slope
  let γ:=c.slope
  let q0:=(C+2*w)*(3*A+3*w+C)+B*(6*A+9*w+3*C+3*B)
  let q1:=γ*(3*A+5*w+2*C+3*B)+α*(3*C+6*w+6*B)+β*(6*A+9*w+3*C+6*B)
  let q2:=γ*(3*α+γ+3*β)+β*(6*α+3*β)
  let hi:=sPow run.stop
  let lo:=sPow start
  let d0:ℤ:=((hi.1-lo.1:ℕ):ℤ)
  let d1:ℤ:=((hi.2.1-lo.2.1:ℕ):ℤ)
  let d2:ℤ:=((hi.2.2.1-lo.2.2.1:ℕ):ℤ)
  let d3:ℤ:=((hi.2.2.2-lo.2.2.2:ℕ):ℤ)
  (C+w)*(q0*d0+q1*d1+q2*d2)+γ*(q0*d1+q1*d2+q2*d3)

theorem runUpperK_eq (p:Input) (start:ℕ) (run:Run) (h:start≤run.stop):
    runUpperK p start run=runUpper p start run:=by
  obtain ⟨m0,m1,m2,m3⟩:=sPow_mono h
  unfold runUpperK runUpper
  rw [DNY,DNY]
  simp only [Nat.cast_sub m0,Nat.cast_sub m1,Nat.cast_sub m2,Nat.cast_sub m3]
  ring

def runsUpperK (p:Input) (runs:List Run):ℕ→ℤ:=
  List.rec (motive:=fun _=>ℕ→ℤ) (fun _=>0)
    (fun run _ ih start=>runUpperK p start run+ih run.stop) runs

theorem GVW (p:Input) (runs:List Run) (start:ℕ) (h:RunsValid p start runs):
    runsUpperK p runs start=runsUpper p start runs:=by
  induction runs generalizing start with
  | nil=>rfl
  | cons run runs ih=>
    change runUpperK p start run+runsUpperK p runs run.stop=runUpper p start run+runsUpper p run.stop runs
    rw [runUpperK_eq p start run h.1.1.le,ih run.stop h.2]

def zlt (a b:ℤ):Bool:=Int.casesOn (motive:=fun _=>Bool) (b-a) (fun k=>Nat.ble 1 k) (fun _=>false)

theorem zlt_sound (a b:ℤ) (h:zlt a b=true):a<b:=by
  unfold zlt at h
  rcases hb:b-a with k | k<;>rw [hb] at h
  · have hk:1≤k:=Nat.le_of_ble_eq_true h
    rw [Int.ofNat_eq_natCast] at hb
    omega
  · exact absurd h Bool.false_ne_true

def sufficientK (s:EA) (r v threshold:ℕ) (runs:List Run):Bool:=
  Nat.blt (11192-(r+v)) threshold ||
    (let p:=rawFlag r v threshold
     Nat.ble 1 p.all && Nat.ble (total p) s.totalCap && Nat.ble (middle p) s.middleCap &&
       Nat.ble p.all s.slopeCap && runsValidK (ofSource s p) runs 0 &&
       zlt (50165*runsUpperK (ofSource s p) runs 0) ((s.gap*162125875761905592:ℕ):ℤ))

theorem FPX (s:EA) (r v threshold:ℕ) (runs:List Run)
    (h:sufficientK s r v threshold runs=true):Sufficient s r v threshold runs:=by
  simp only [sufficientK,Bool.or_eq_true,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at h
  rcases h with h | ⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩
  · exact Or.inl h
  · have hv:=GAT _ _ _ h5
    refine Or.inr ⟨h1,h2,h3,h4,hv,?_⟩
    have hz:=zlt_sound _ _ h6
    rw [GVW _ _ _ hv] at hz
    push_cast at hz
    norm_num
    linarith

def thresholdK (s:EA) (r v threshold:ℕ) (runs:List Run):Bool:=
  sufficientK s r v threshold runs || fastK s r v threshold

theorem GCF (s:EA) (r v threshold:ℕ) (runs:List Run)
    (h:thresholdK s r v threshold runs=true):
    QM s r v threshold:=by
  simp only [thresholdK,Bool.or_eq_true] at h
  rcases h with h | h
  · exact Lower80899.BLW.GDF s r v threshold runs (FPX _ _ _ _ _ h)
  · exact fastK_sound _ _ _ _ h

end EMO
end MergedPart2
section MergedPart3
namespace MA
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 BY
open PS
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type*) [Field K]

theorem FGA
    {I:Type*} (F:Poly4 K) (hF:F ≠ 0) (f:Polynomial K) (gamma:K)
    (nodes:I ↪ K) (u0 u1:I→K) (support:Finset I) (w nu:ℕ)
    (hdegree:f.natDegree≤w)
    (hweight:MvPolynomial.weightedTotalDegree (RCN081.BV w) F≤nu)
    (hregular:BM K f gamma (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0)
    (hagrees: ∀i ∈ support,f.eval (nodes i)=u0 i+gamma*u1 i):
    (∑ i ∈ support,(contactOrder K (nodes i) (u0 i) (u1 i) F-1))+w≤nu+1:=by
  classical
  let H:=MvPolynomial.pderiv (2:Fin 4) F
  let P:=BM K f gamma H
  have hmult: ∀i ∈ support,
      contactOrder K (nodes i) (u0 i) (u1 i) F-1≤P.rootMultiplicity (nodes i):=by
    intro i hi
    have hc:VE K (nodes i) (u0 i) (u1 i)
        (contactOrder K (nodes i) (u0 i) (u1 i) F) F:=
      (AFE K _ _ _ _ F hF).mpr le_rfl
    have hd:=DKX K (nodes i) (u0 i) (u1 i) _ F hc
    have ht:=ACJ K H f (nodes i) (u0 i) (u1 i) gamma _
      (hagrees i hi) ((QW K _ _ _ _ H).mp hd)
    apply (Polynomial.le_rootMultiplicity_iff hregular).mpr
    exact (RCN185.ZJ P (nodes i) _).mpr
      (Polynomial.X_pow_dvd_iff.mp ht)
  have hs:(∑ i ∈ support,(contactOrder K (nodes i) (u0 i) (u1 i) F-1))≤P.natDegree:=by
    calc
      _≤ ∑ i ∈ support,P.rootMultiplicity (nodes i):=Finset.sum_le_sum hmult
      _= ∑ a ∈ support.map nodes,P.rootMultiplicity a:=
        (Finset.sum_map support nodes (fun a:K=>P.rootMultiplicity a)).symm
      _≤_:= @RCN355._Q14 K inferInstance (Classical.decEq K)
        P (support.map nodes)
  have hd:=BOO K F f gamma w nu hdegree hweight hregular
  change P.natDegree+w≤nu+1 at hd
  omega

theorem FYI {I:Type*} (support:Finset I) (d:I→ℕ)
    (alpha beta A H:ℕ) (hcard:A≤support.card) (hmass:(∑ i ∈ support,d i)≤H):
    alpha*A-beta*H≤ ∑ i ∈ support,(alpha-beta*d i):=by
  classical
  have hsum:alpha*support.card≤
      (∑ i ∈ support,(alpha-beta*d i))+beta*(∑ i ∈ support,d i):=by
    calc
      _= ∑ _i ∈ support,alpha:=by simp [Nat.mul_comm]
      _≤ ∑ i ∈ support,((alpha-beta*d i)+beta*d i):=
        Finset.sum_le_sum fun i _=>by omega
      _=_:=by rw [Finset.sum_add_distrib,Finset.mul_sum]
  have hc:=Nat.mul_le_mul_left alpha hcard
  have hm:=Nat.mul_le_mul_left beta hmass
  omega

end
end MA
end MergedPart3
section MergedPart4
namespace MA
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 BY
open PS
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type*) [Field K]
local instance:DecidableEq K:=Classical.decEq K

end
end MA
end MergedPart4
section MergedPart5
namespace MA
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 BY
open PS BCB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable (K:Type*) [Field K]

theorem FJW (F:Poly4 K):
    EM K 0 0 0 F=
      MvPolynomial.finSuccEquiv K 3 (AEV K F):=by
  have hX1:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (1:Fin 4))=
      Polynomial.C (MvPolynomial.X (0:Fin 3)):=MvPolynomial.finSuccEquiv_X_succ (j:=(0:Fin 3))
  have hX2:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (2:Fin 4))=
      Polynomial.C (MvPolynomial.X (1:Fin 3)):=MvPolynomial.finSuccEquiv_X_succ (j:=(1:Fin 3))
  have hX3:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (3:Fin 4))=
      Polynomial.C (MvPolynomial.X (2:Fin 3)):=MvPolynomial.finSuccEquiv_X_succ (j:=(2:Fin 3))
  have hgen (i:Fin 4):
      EM K 0 0 0 (MvPolynomial.X i)=
        MvPolynomial.finSuccEquiv K 3 (AEV K (MvPolynomial.X i)):=by
    rw [GIK]
    fin_cases i<;>simp [EM,AAP,seedAffine,
      MvPolynomial.finSuccEquiv_X_zero,hX1,hX2,hX3]
  induction F using MvPolynomial.induction_on with
  | C a=>simp [EM,MvPolynomial.finSuccEquiv_apply,
      Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
  | add F G hF hG=>simp only [map_add,hF,hG]
  | mul_X F i hF=>simpa only [map_mul] using congrArg₂ (· * ·) hF (hgen i)

theorem FCG (F:Poly4 K) (d:Fin 4→₀ ℕ):
    AddMonoidAlgebra.coeff ((EM K 0 0 0 F).coeff (d 0+d 1)) d.tail=AddMonoidAlgebra.coeff F d:=by
  rw [FJW,MvPolynomial.finSuccEquiv_coeff_coeff]
  have he:Finsupp.cons (d 0+d 1) d.tail=UL d:=by
    ext i
    fin_cases i<;>simp [UL]<;>rfl
  rw [he]
  change Finsupp.mapDomain UL (AddMonoidAlgebra.coeff F) (UL d)=_
  exact Finsupp.mapDomain_apply_of_injective DCR _ _

theorem EVO {DF T R B:ℕ} (F:Poly4 K)
    (hbox:F ∈ BA K DF 1 T R) (hY:F.degreeOf 1≤B)
    (hcontact:VE K 0 0 0 (B+R+1) F):
    MvPolynomial.X (0:Fin 4) ∣ F:=by
  classical
  let m:=B+R+1
  have hz (n:ℕ) (hn:n≤B):(EM K 0 0 0 F).coeff n=0:=by
    have hnm:n<m:=by dsimp [m];omega
    let p:=blocksOf K m (⟨F,hbox⟩:BA K DF 1 T R) ⟨n,hnm⟩
    have hp:(blockJet K (min n T) T R (m-n)) p=0:=by
      change contactJet K (m-n) p.val=0
      apply (XA K (m-n) _).mpr
      rw [EUQ]
      exact (QW K 0 0 0 m F).mp hcontact n
    have hker:p ∈ LinearMap.ker (blockJet K (min n T) T R (m-n)):=hp
    rw [ATB K (min n T) T R (m-n)
      (Or.inr (by dsimp [m];omega))] at hker
    have hp0:p=0:=by simpa using hker
    have he:=congrArg Subtype.val hp0
    rw [EUQ] at he
    exact he
  have hc (d:Fin 4→₀ ℕ) (hd:d 0=0):AddMonoidAlgebra.coeff F d=0:=by
    by_contra hne
    have hd1:=MvPolynomial.degreeOf_le_iff.mp hY d (MvPolynomial.mem_support_iff.mpr hne)
    have he:=FCG K F d
    rw [hd,zero_add,hz (d 1) hd1,MvPolynomial.coeff_zero] at he
    exact hne he.symm
  have hdiv:Polynomial.X ∣ MvPolynomial.finSuccEquiv K 3 F:=by
    apply Polynomial.X_dvd_iff.mpr
    ext d
    rw [MvPolynomial.finSuccEquiv_coeff_coeff,MvPolynomial.coeff_zero]
    exact hc (Finsupp.cons 0 d) rfl
  obtain ⟨Q,hQ⟩:=hdiv
  refine ⟨(MvPolynomial.finSuccEquiv K 3).symm Q,?_⟩
  apply (MvPolynomial.finSuccEquiv K 3).injective
  simpa only [map_mul,MvPolynomial.finSuccEquiv_X_zero,AlgEquiv.apply_symm_apply] using hQ

theorem DYK {DF T R B:ℕ} (F:Poly4 K) (hF:F ≠ 0)
    (hbox:F ∈ BA K DF 1 T R) (hY:F.degreeOf 1≤B)
    (hX: ¬MvPolynomial.X (0:Fin 4) ∣ F):contactOrder K 0 0 0 F≤B+R:=by
  by_contra h
  apply hX
  apply EVO K F hbox hY
  exact (AFE K 0 0 0 (B+R+1) F hF).mpr (by omega)

def centerEquiv (x u0 u1:K):Poly4 K ≃ₐ[K] Poly4 K:=
  AlgEquiv.ofAlgHom (center K x u0 u1) (center K (-x) (-u0) (-u1))
    (by
      apply DFunLike.ext
      intro Q
      change center K x u0 u1 (center K (-x) (-u0) (-u1) Q)=Q
      simpa using DIB K (-x) (-u0) (-u1) Q)
    (by
      apply DFunLike.ext
      intro Q
      exact DIB K x u0 u1 Q)

theorem DME (F:Poly4 K) (hF:Irreducible F)
    (hR:0<F.degreeOf 2) (x u0 u1:K):
    ¬MvPolynomial.X (0:Fin 4) ∣ center K x u0 u1 F:=by
  intro hdiv
  let E:=centerEquiv K (-x) (-u0) (-u1)
  have hp:Irreducible (E (MvPolynomial.X (0:Fin 4))):=
    (MulEquiv.irreducible_iff (f:=E.toMulEquiv)).mpr (MvPolynomial.X_prime.irreducible)
  have hd:E (MvPolynomial.X (0:Fin 4)) ∣ F:=by
    have hm:=map_dvd E.toRingHom hdiv
    change center K (-x) (-u0) (-u1) (MvPolynomial.X (0:Fin 4)) ∣
      center K (-x) (-u0) (-u1) (center K x u0 u1 F) at hm
    rw [DIB] at hm
    exact hm
  have hd' :=(hp.associated_of_dvd hF hd).symm.dvd
  have hle:=RCN081.OI (2:Fin 4) F _ hd' hp.ne_zero
  have he:E (MvPolynomial.X (0:Fin 4))=MvPolynomial.X 0+MvPolynomial.C (-x):=by
    simp [E,centerEquiv,center]
  rw [he] at hle
  have hh:=MvPolynomial.degreeOf_add_le (2:Fin 4)
    (MvPolynomial.X 0:Poly4 K) (MvPolynomial.C (-x))
  have hh0:(MvPolynomial.X 0+MvPolynomial.C (-x):Poly4 K).degreeOf 2≤0:=by
    simpa [MvPolynomial.degreeOf_X] using hh
  omega

theorem BLV {DF T R B:ℕ} (F:Poly4 K)
    (hF:Irreducible F) (hR:0<F.degreeOf 2)
    (hbox:F ∈ BA K DF 1 T R)
    (hB:RCN234.wt RCN156.BC F≤B) (x u0 u1:K):
    contactOrder K x u0 u1 F≤B+R:=by
  rw [← EES K x u0 u1 F hF.ne_zero]
  apply DYK K (center K x u0 u1 F)
    (ARO K x u0 u1 hF.ne_zero) (APS K x u0 u1 ⟨F,hbox⟩)
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have hw:=(MvPolynomial.le_weightedTotalDegree RCN156.BC hd).trans
      ((DHB K x u0 u1 RCN156.BC (by decide) F).trans hB)
    rw [RCN081.weight_fin4] at hw
    simp only [RCN156.BC] at hw
    simp at hw
    omega
  · exact DME K F hF hR x u0 u1

end
end MA
end MergedPart5
section MergedPart6
namespace MA
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 BY
open PS
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type*) [Field K]

theorem EIA {I:Type*} (support:Finset I) (d:I→ℕ)
    (alpha beta A H cap:ℕ) (hcard:A≤support.card)
    (hmass:(∑ i ∈ support,d i)≤H) (hcap: ∀i ∈ support,d i≤cap):
    alpha*A-beta*min H (cap*A)≤ ∑ i ∈ support,(alpha-beta*d i):=by
  classical
  by_cases hh:H≤cap*A
  · rw [Nat.min_eq_left hh]
    exact FYI support d alpha beta A H hcard hmass
  · rw [Nat.min_eq_right (by omega:cap*A≤H)]
    calc
      alpha*A-beta*(cap*A)=(alpha-beta*cap)*A:=by rw [Nat.sub_mul,Nat.mul_assoc]
      _≤(alpha-beta*cap)*support.card:=Nat.mul_le_mul_left _ hcard
      _= ∑ _i ∈ support,(alpha-beta*cap):=by simp [Nat.mul_comm]
      _≤_:=Finset.sum_le_sum fun i hi=>
        Nat.sub_le_sub_left (Nat.mul_le_mul_left beta (hcap i hi)) alpha

theorem EGA
    {I:Type*} {DF T R B:ℕ} (F:Poly4 K) (hF:Irreducible F)
    (hR:0<F.degreeOf 2) (hbox:F ∈ BA K DF 1 T R)
    (hB:RCN234.wt RCN156.BC F≤B)
    (f:Polynomial K) (gamma:K) (nodes:I ↪ K) (u0 u1:I→K)
    (support:Finset I) (w nu alpha beta A:ℕ)
    (hnu:w≤nu) (hdegree:f.natDegree≤w)
    (hweight:MvPolynomial.weightedTotalDegree (RCN081.BV w) F≤nu)
    (hregular:BM K f gamma (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0)
    (hagrees: ∀i ∈ support,f.eval (nodes i)=u0 i+gamma*u1 i)
    (hcard:A≤support.card):
    alpha*A-beta*min (nu-w+1) ((B+R-1)*A)≤
      ∑ i ∈ support,(alpha-beta*(contactOrder K (nodes i) (u0 i) (u1 i) F-1)):=by
  have hm:=FGA K F hF.ne_zero f gamma nodes u0 u1 support w nu
    hdegree hweight hregular hagrees
  apply EIA support _ alpha beta A (nu-w+1) (B+R-1) hcard
  · omega
  · intro i _
    exact Nat.sub_le_sub_right
      (BLV K F hF hR hbox hB (nodes i) (u0 i) (u1 i)) 1

end
end MA
end MergedPart6
section MergedPart7
namespace MA
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 BY
open PS
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type*) [Field K]
local instance:DecidableEq K:=Classical.decEq K

def AHJ (alpha beta L s T R mu:ℕ):ℕ:=
  ES (alpha-beta*(mu-1)) L s-
    ES (alpha-beta*(mu-1)-mu) (L-T) (s-R)

theorem EXO
    {I:Type*} [Fintype I] {DF T R B D w L s nu:ℕ}
    (F:Poly4 K) (hF:Irreducible F) (hR:0<F.degreeOf 2)
    (hbox:F ∈ BA K DF 1 T R)
    (hB:wt RCN156.BC F≤B)
    (nodes u0 u1:I→K) (alpha beta:ℕ)
    (hrows: ∀mu≤B+R,AW (D-nu) w (L-T) (s-R)+
      Fintype.card I*AHJ alpha beta L s T R mu<AW D w L s):
    AW (D-nu) w (L-T) (s-R)+
      (∑ i:I,AHJ alpha beta L s T R
        (contactOrder K (nodes i) (u0 i) (u1 i) F))<AW D w L s:=by
  classical
  let rows:=Finset.range (B+R+1)
  have hn:rows.Nonempty:=⟨0,by simp [rows]⟩
  obtain ⟨mu,hmu,heq⟩:=Finset.exists_mem_eq_sup rows hn (AHJ alpha beta L s T R)
  have hbound (i:I):AHJ alpha beta L s T R
      (contactOrder K (nodes i) (u0 i) (u1 i) F)≤
        rows.sup (AHJ alpha beta L s T R):=by
    apply Finset.le_sup
    have hc:=BLV K F hF hR hbox hB (nodes i) (u0 i) (u1 i)
    simpa [rows] using (show contactOrder K (nodes i) (u0 i) (u1 i) F<B+R+1 by omega)
  have hs:(∑ i:I,AHJ alpha beta L s T R
      (contactOrder K (nodes i) (u0 i) (u1 i) F))≤
        Fintype.card I*rows.sup (AHJ alpha beta L s T R):=by
    calc
      _≤ ∑ _i:I,rows.sup (AHJ alpha beta L s T R):=
        Finset.sum_le_sum fun i _=>hbound i
      _=_:=by simp
  have hc:=hrows mu (by have:=Finset.mem_range.mp hmu;omega)
  rw [heq] at hs
  exact (Nat.add_le_add_left hs _).trans_lt hc

theorem DTT
    {I:Type*} [Fintype I] [DecidableEq I] {DF T R B D w L s nu:ℕ}
    (F:Poly4 K) (hF:Irreducible F) (hRpos:0<F.degreeOf 2)
    (hbox:F ∈ BA K DF 1 T R) (hT:T≤L) (hR:R≤s)
    (hcode:wt (RCN081.BV w) F=nu)
    (htotal:T≤wt RCN156.AT F)
    (hslope:R≤wt RCN156.BE F)
    (hB:wt RCN156.BC F≤B)
    (nodes:I ↪ K) (u0 u1:I→K) (alpha beta A:ℕ) (hnu:w≤nu)
    (hDpos:0<D) (hD:D≤alpha*A-beta*min (nu-w+1) ((B+R-1)*A))
    (hrows: ∀mu≤B+R,AW (D-nu) w (L-T) (s-R)+
      Fintype.card I*AHJ alpha beta L s T R mu<AW D w L s)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,(selected gamma).natDegree≤w)
    (hsolution: ∀gamma ∈ Gamma,BM K (selected gamma) gamma F=0)
    (hregular: ∀gamma ∈ Gamma,
      BM K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0)
    (hagreement: ∀gamma ∈ Gamma,A≤
      ((Finset.univ:Finset I).filter
        (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card):
    ∃Q:Poly4 K,Q ∈ BA K D w L s∧IsRelPrime F Q∧
      ∀gamma ∈ Gamma,BM K (selected gamma) gamma Q=0:=by
  classical
  let m:I→ℕ:=fun i=>alpha-beta*(contactOrder K (nodes i) (u0 i) (u1 i) F-1)
  have hd:=EXO K F hF hRpos hbox hB nodes u0 u1 alpha beta hrows
  obtain ⟨Q,hQ,hproper,hcontact⟩:=DSW K F hF.ne_zero hbox hT hR
    hcode.symm.le htotal hslope nodes u0 u1 m hd
  refine ⟨Q,hQ,hF.isRelPrime_iff_not_dvd.mpr hproper,?_⟩
  intro gamma hgamma
  let support:=(Finset.univ:Finset I).filter
    (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)
  have hv: ∀i ∈ support,(selected gamma).eval (nodes i)=u0 i+gamma*u1 i:=by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hmass:=EGA K F hF hRpos hbox hB (selected gamma) gamma
    nodes u0 u1 support w nu alpha beta A hnu (hdegree gamma hgamma) hcode.le
    (hregular gamma hgamma) hv (hagreement gamma hgamma)
  apply CII K F Q (selected gamma) gamma nodes u0 u1 support m
    (hsolution gamma hgamma) hv (fun i _=>hcontact i)
  exact (AIJ K D w L s Q (selected gamma) gamma hDpos hQ
    (hdegree gamma hgamma)).trans_le (hD.trans hmass)

end
end MA
end MergedPart7
section MergedPart8
namespace MA
open scoped BigOperators
open RCN100
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem CBJ (w L s:ℕ):
    Monotone (fun D=>AW D w L s):=by
  intro D1 D2 hD
  unfold AW
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Nat.mul_le_mul_left
  exact Nat.sub_le_sub_right (Nat.sub_le_sub_right hD _) _

theorem CYP {D w L s T R B N alpha beta lo nu:ℕ}
    (hnu:lo≤nu)
    (hrows: ∀mu≤B+R,AW (D-lo) w (L-T) (s-R)+
      N*AHJ alpha beta L s T R mu<AW D w L s):
    ∀mu≤B+R,AW (D-nu) w (L-T) (s-R)+
      N*AHJ alpha beta L s T R mu<AW D w L s:=by
  intro mu hmu
  have hcoef:=CBJ w (L-T) (s-R)
    (Nat.sub_le_sub_left hnu D)
  exact (Nat.add_le_add_right hcoef _).trans_lt (hrows mu hmu)

theorem EUG (alpha beta w B R A:ℕ):
    Antitone (fun nu=>alpha*A-beta*min (nu-w+1) ((B+R-1)*A)):=by
  intro lo hi h
  apply Nat.sub_le_sub_left
  apply Nat.mul_le_mul_left
  exact min_le_min (Nat.add_le_add_right (Nat.sub_le_sub_right h w) 1) le_rfl

end MA
end MergedPart8
section MergedPart9
namespace MA
open scoped BigOperators
open RCN100
set_option autoImplicit false

theorem GYM (D x c:ℕ) (h:D≤x):
    (D-c)+((D+1-c)-(D-c))*(x-D)≤x-c:=by
  by_cases hc:c≤D
  · have h1:(D+1-c)-(D-c)=1:=by omega
    rw [h1,one_mul]
    omega
  · have h1:(D+1-c)-(D-c)=0:=by omega
    rw [h1,zero_mul]
    omega

theorem hinge_chord (a x b c:ℕ) (hax:a≤x) (hxb:x≤b):
    (b-a)*(x-c)≤(b-x)*(a-c)+(x-a)*(b-c):=by
  rcases Nat.lt_or_ge a c with hac | hca
  swap
  ·
    have hba:b-a=(b-x)+(x-a):=by omega
    have hx:x-c=(x-a)+(a-c):=by omega
    have hb:b-c=(b-x)+(x-a)+(a-c):=by omega
    rw [hba,hx,hb]
    apply le_of_eq
    ring
  rcases Nat.lt_or_ge x c with hxc | hcx
  swap
  ·
    have ha:a-c=0:=by omega
    rw [ha,Nat.mul_zero,Nat.zero_add]
    have hb:b-c=(b-x)+(x-c):=by omega
    have hxa:x-a=(x-c)+(c-a):=by omega
    have hba:b-a=(b-x)+(x-c)+(c-a):=by omega
    rw [hb,hxa,hba]
    nlinarith [Nat.zero_le ((b-x)*(c-a))]
  · have hx:x-c=0:=by omega
    rw [hx,Nat.mul_zero]
    exact Nat.zero_le _

theorem AAH (D w L s:ℕ):
    AW D w L s=
      ∑ i ∈ Finset.range (L+1),∑ j ∈ Finset.range (s+1),
        (L+1-i-j)*(D-(w*i+(w-1)*j)):=by
  unfold AW
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.sub_sub,Nat.sub_sub]

def countSlopeAt (D w L s:ℕ):ℕ:=
  ∑ i ∈ Finset.range (L+1),∑ j ∈ Finset.range (s+1),
    (L+1-i-j)*((D+1-(w*i+(w-1)*j))-(D-(w*i+(w-1)*j)))

theorem EOX (D x w L s:ℕ) (h:D≤x):
    AW D w L s+countSlopeAt D w L s*(x-D)≤AW x w L s:=by
  rw [AAH,AAH,countSlopeAt,
    Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have ht:=GYM D x (w*i+(w-1)*j) h
  calc (L+1-i-j)*(D-(w*i+(w-1)*j))+
        (L+1-i-j)*((D+1-(w*i+(w-1)*j))-(D-(w*i+(w-1)*j)))*(x-D)
      =(L+1-i-j)*((D-(w*i+(w-1)*j))+
          ((D+1-(w*i+(w-1)*j))-(D-(w*i+(w-1)*j)))*(x-D)):=by ring
    _≤(L+1-i-j)*(x-(w*i+(w-1)*j)):=Nat.mul_le_mul_left _ ht

theorem EVB (a x b w L s:ℕ) (hax:a≤x) (hxb:x≤b):
    (b-a)*AW x w L s≤
      (b-x)*AW a w L s+(x-a)*AW b w L s:=by
  rw [AAH,AAH,AAH,
    Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hc:=hinge_chord a x b (w*i+(w-1)*j) hax hxb
  calc (b-a)*((L+1-i-j)*(x-(w*i+(w-1)*j)))
      =(L+1-i-j)*((b-a)*(x-(w*i+(w-1)*j))):=by ring
    _≤(L+1-i-j)*((b-x)*(a-(w*i+(w-1)*j))+(x-a)*(b-(w*i+(w-1)*j))):=
        Nat.mul_le_mul_left _ hc
    _=(b-x)*((L+1-i-j)*(a-(w*i+(w-1)*j)))+(x-a)*((L+1-i-j)*(b-(w*i+(w-1)*j))):=by ring

theorem GOT (w L s T R K beta Dhi Ehi H t:ℕ) (ht:t≤H)
    (hHi:AW Ehi w (L-T) (s-R)+K<AW Dhi w L s)
    (hLo:AW (Ehi+(beta+1)*H) w (L-T) (s-R)+K<
      AW Dhi w L s+countSlopeAt Dhi w L s*(beta*H)):
    AW (Ehi+(beta+1)*t) w (L-T) (s-R)+K<AW (Dhi+beta*t) w L s:=by
  set G2:=fun E=>AW E w (L-T) (s-R) with hG2
  set g1:=AW Dhi w L s
  set m:=countSlopeAt Dhi w L s
  have htan:=EOX Dhi (Dhi+beta*t) w L s (Nat.le_add_right _ _)
  rw [Nat.add_sub_cancel_left] at htan
  rcases Nat.eq_zero_or_pos H with hH | hH
  · have:t=0:=by omega
    subst this
    simpa using hHi

  have hch:=EVB Ehi (Ehi+(beta+1)*t) (Ehi+(beta+1)*H) w (L-T) (s-R)
    (Nat.le_add_right _ _) (by have:=Nat.mul_le_mul_left (beta+1) ht;omega)
  have e1:Ehi+(beta+1)*H-Ehi=(beta+1)*H:=by omega
  have e2:Ehi+(beta+1)*H-(Ehi+(beta+1)*t)=(beta+1)*(H-t):=by
    rw [Nat.mul_sub];omega
  have e3:Ehi+(beta+1)*t-Ehi=(beta+1)*t:=by omega
  rw [e1,e2,e3] at hch
  have hch' :H*G2 (Ehi+(beta+1)*t)≤(H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H):=by
    have hpos:0<beta+1:=Nat.succ_pos _
    have:(beta+1)*(H*G2 (Ehi+(beta+1)*t))≤(beta+1)*((H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H)):=by
      calc (beta+1)*(H*G2 (Ehi+(beta+1)*t))=(beta+1)*H*G2 (Ehi+(beta+1)*t):=by ring
        _≤(beta+1)*(H-t)*G2 Ehi+(beta+1)*t*G2 (Ehi+(beta+1)*H):=hch
        _=(beta+1)*((H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H)):=by ring
    exact Nat.le_of_mul_le_mul_left this hpos

  have hsum:H*(G2 (Ehi+(beta+1)*t)+K)<H*(g1+m*(beta*t)):=by
    have hsplit:H=(H-t)+t:=by omega
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      simp only [Nat.mul_zero,Nat.add_zero,Nat.sub_zero] at hch' ⊢
      have:=Nat.mul_lt_mul_of_pos_left hHi hH
      nlinarith [hch']
    · have hA:(H-t)*(G2 Ehi+K)≤(H-t)*g1:=Nat.mul_le_mul_left _ hHi.le
      have hB:t*(G2 (Ehi+(beta+1)*H)+K)<t*(g1+m*(beta*H)):=Nat.mul_lt_mul_of_pos_left hLo h0
      have hC:t*(m*(beta*H))=H*(m*(beta*t)):=by ring
      calc H*(G2 (Ehi+(beta+1)*t)+K)=H*G2 (Ehi+(beta+1)*t)+H*K:=by ring
        _≤(H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H)+((H-t)+t)*K:=by
            rw [← hsplit];exact Nat.add_le_add_right hch' _
        _=(H-t)*(G2 Ehi+K)+t*(G2 (Ehi+(beta+1)*H)+K):=by ring
        _<(H-t)*g1+t*(g1+m*(beta*H)):=Nat.add_lt_add_of_le_of_lt hA hB
        _=((H-t)+t)*g1+t*(m*(beta*H)):=by ring
        _=H*(g1+m*(beta*t)):=by rw [← hsplit,hC];ring
  have hfin:G2 (Ehi+(beta+1)*t)+K<g1+m*(beta*t):=Nat.lt_of_mul_lt_mul_left hsum
  exact lt_of_lt_of_le hfin htan

end MA
end MergedPart9
section MergedPart10
namespace ADZ
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 ABE GB
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def stage (y z d j:ℕ):DG:=
  ⟨262144,131071,181235,y,d-j,z,y,d,z⟩

def kTerm (y z:ℕ):ℕ:=
  131073*(z+y+524284*y*z)+50164*80910*y
def mTerm (y z:ℕ):ℕ:=131073*131071*y*z

theorem FLB (y z d j:ℕ) (hj:j≤d):
    KP (stage y z d j)=
      (2*d-j)*kTerm y z+(2*(d-j)-1)*2*mTerm y z:=by
  simp only [stage,KP,DG.gap,
    DG.errors,DG.KO,
    DG.mixedCost,dot]
  norm_num only
  have hsub:(d-j)+d=2*d-j:=by omega
  dsimp [kTerm,mTerm]
  calc
    _=((d-j)+d)*(131073*(z+y+524284*y*z)+50164*80910*y)+
        (2*(d-j)-1)*2*(131073*131071*y*z):=by ring
    _=_:=by rw [hsub]







end ADZ
end MergedPart10
section MergedPart11
namespace AFK
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 ABE GB ADZ
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem stageDot (y z d:ℕ) (hd:1≤d):
    dot ⟨y,d-1,z⟩ (stage y z d 1).mixedCost=y*z*(6*d-4):=by
  obtain ⟨e,rfl⟩: ∃e,d=e+1:=⟨d-1,by omega⟩
  simp only [stage,dot,DG.mixedCost,Nat.add_sub_cancel]
  rw [show 6*(e+1)-4=6*e+2 by omega]
  ring

def AAF (y z d:ℕ):ℕ:=
  KP (stage y z d 1)+50164*(y*z*(6*d-4))+50164*8110000000000

theorem DRU (y z d:ℕ) (hd:2≤d):
    (AAF y z d:ℤ)=
      (2*(kTerm y z:ℤ)+4*(mTerm y z:ℤ)+6*50164*(y:ℤ)*z)*d+
        (50164*8110000000000-(kTerm y z:ℤ)-6*(mTerm y z:ℤ)-4*50164*(y:ℤ)*z):=by
  unfold AAF
  rw [FLB y z d 1 (by omega)]
  have e1:((2*d-1:ℕ):ℤ)=2*(d:ℤ)-1:=by omega
  have e2:((2*(d-1)-1:ℕ):ℤ)=2*(d:ℤ)-3:=by omega
  have e3:((6*d-4:ℕ):ℤ)=6*(d:ℤ)-4:=by omega
  push_cast [e1,e2,e3]
  ring

theorem EZU (y z d r u:ℕ) (hd:2≤d) (hdr:d≤r)
    (h2:AAF y z 2≤2*50164*u) (hr:AAF y z r≤r*50164*u):
    AAF y z d≤d*50164*u:=by
  by_cases hr2:r=2
  · have hd2:d=2:=by omega
    subst hd2
    exact h2
  have hk2:=DRU y z 2 le_rfl
  have hkr:=DRU y z r (by omega)
  have hkd:=DRU y z d hd
  have h2' :(AAF y z 2:ℤ)≤2*50164*(u:ℤ):=by exact_mod_cast h2
  have hr' :(AAF y z r:ℤ)≤(r:ℤ)*50164*(u:ℤ):=by exact_mod_cast hr
  have hid:((r:ℤ)-2)*((AAF y z d:ℤ)-(d:ℤ)*50164*u)=
      ((r:ℤ)-d)*((AAF y z 2:ℤ)-2*50164*u)+
        ((d:ℤ)-2)*((AAF y z r:ℤ)-(r:ℤ)*50164*u):=by
    rw [hk2,hkr,hkd]
    push_cast
    ring
  have hA:=mul_nonpos_of_nonneg_of_nonpos (show (0:ℤ)≤(r:ℤ)-d by omega)
    (show (AAF y z 2:ℤ)-2*50164*u≤0 by linarith)
  have hB:=mul_nonpos_of_nonneg_of_nonpos (show (0:ℤ)≤(d:ℤ)-2 by omega)
    (show (AAF y z r:ℤ)-(r:ℤ)*50164*u≤0 by linarith)
  have hprod:((r:ℤ)-2)*((AAF y z d:ℤ)-(d:ℤ)*50164*u)≤0:=by
    rw [hid]
    linarith
  have hpos:(0:ℤ)<(r:ℤ)-2:=by omega
  have hle:(AAF y z d:ℤ)-(d:ℤ)*50164*u≤0:=by
    by_contra hc
    have:=mul_pos hpos (lt_of_not_ge hc)
    linarith
  have hfin:(AAF y z d:ℤ)≤(d:ℤ)*50164*u:=by linarith
  exact_mod_cast hfin

def foldZCoeff (y d:ℕ):ℕ:=
  (2*d-1)*131073*(1+524284*y)+(2*d-3)*2*131073*131071*y+50164*y*(6*d-4)
def foldConstant (y d:ℕ):ℕ:=
  (2*d-1)*(131073+50164*80910)*y+50164*8110000000000

theorem FEP (y z d:ℕ) (hd:1≤d):
    AAF y z d=foldZCoeff y d*z+foldConstant y d:=by
  unfold AAF
  rw [FLB y z d 1 hd,show 2*(d-1)-1=2*d-3 by omega]
  unfold kTerm mTerm foldZCoeff foldConstant
  ring

def foldSlope (y d:ℕ):ℕ:=foldZCoeff y d/(50164*d)+1
def foldConst (y d:ℕ):ℕ:=foldConstant y d/(50164*d)+1
def foldPiece (y z d:ℕ):ℕ:=foldSlope y d*z+foldConst y d

def foldUnit (y z r:ℕ):ℕ:=
  if r<2 then 8110000000000 else
    max 8110000000000 (max (foldPiece y z 2) (foldPiece y z r))

private theorem AUX (a b:ℕ) (hb:0<b):a≤(a/b+1)*b:=by
  have hm:=Nat.mod_lt a hb
  have he:=Nat.mod_add_div a b
  nlinarith

theorem FSH (y z d:ℕ) (hd:1≤d):
    AAF y z d≤d*50164*foldPiece y z d:=by
  have hb:0<50164*d:=by omega
  have ha:=AUX (foldZCoeff y d) (50164*d) hb
  have hc:=AUX (foldConstant y d) (50164*d) hb
  have ham:=Nat.mul_le_mul_right z ha
  rw [FEP y z d hd]
  unfold foldPiece foldSlope foldConst
  nlinarith

theorem GEI (y z r:ℕ):8110000000000≤foldUnit y z r:=by
  unfold foldUnit
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem FAS (y z d r:ℕ) (hd:2≤d) (hdr:d≤r):
    AAF y z d≤d*50164*foldUnit y z r:=by
  have hr: ¬r<2:=by omega
  have h2:foldPiece y z 2≤foldUnit y z r:=by
    unfold foldUnit
    rw [if_neg hr]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hrr:foldPiece y z r≤foldUnit y z r:=by
    unfold foldUnit
    rw [if_neg hr]
    exact (le_max_right _ _).trans (le_max_right _ _)
  apply EZU y z d r (foldUnit y z r) hd hdr
  · exact (FSH y z 2 (by decide)).trans (Nat.mul_le_mul_left _ h2)
  · exact (FSH y z r (by omega)).trans (Nat.mul_le_mul_left _ hrr)

end AFK
end MergedPart11
section MergedPart12
namespace PairCell6815
open RCN260 RCN294 GB
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def parameters (r y t:ℕ):DG:=
  ⟨262144,131071,181235,229-y,50-r,17230-t,348-y,78-r,11785-t⟩

def cap (r y t:ℕ):ℕ:=FU (parameters r y t)

def constant (r y:ℕ):ℕ:=KP (parameters r y 0)

def slope (r y:ℕ):ℕ:=
  131073*((1+2*131071*(229-y))*((50-r)+(78-r))+
    131071*(2*(50-r)-1)*((229-y)+(348-y))+
    2*131071*((229-y)*(78-r)+(50-r)*(348-y)))

theorem GFC (r y t:ℕ) (ht:t≤11785):
    KP (parameters r y t)+slope r y*t=constant r y:=by
  have ht' :t≤17230:=by omega
  simp only [constant,slope,parameters,KP,DG.errors,
    DG.gap,DG.KO,DG.mixedCost,
    dot,Nat.sub_zero]
  zify [ht,ht']
  ring

def line (r y t:ℕ):ℤ:=
  ((constant r y/50164:ℕ):ℤ)-((slope r y/50164:ℕ):ℤ)*(t:ℤ)

theorem cap_le_line (r y t:ℕ) (ht:t≤11785):(cap r y t:ℤ)≤line r y t:=by
  have he:=GFC r y t ht
  have h1:=Nat.div_mul_le_self (KP (parameters r y t)) 50164
  have h2:=Nat.div_add_mod (constant r y) 50164
  have h3:=Nat.mod_lt (constant r y) (show 0<50164 by norm_num)
  have h4:=Nat.mul_le_mul_right t (Nat.div_mul_le_self (slope r y) 50164)
  have hn:cap r y t+slope r y/50164*t≤constant r y/50164:=by
    have hc:cap r y t=KP (parameters r y t)/50164:=by
      simp only [cap,FU,parameters,DG.gap]
    have h5:slope r y/50164*50164*t=50164*(slope r y/50164*t):=by ring
    rw [h5] at h4
    rw [hc]
    generalize slope r y/50164*t=P at*
    generalize slope r y*t=S at*
    omega
  unfold line
  have hn' :=(Nat.cast_le (α:=ℤ)).mpr hn
  rw [Nat.cast_add,Nat.cast_mul] at hn'
  linarith

end PairCell6815
end MergedPart12

end ProximityPrize.SubmissionLower
end
