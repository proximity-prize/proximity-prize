import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFactoredFlagCount6676Research

/-! .
 -/
namespace ProximityPrize.SubmissionLower.ContactMovingPositiveLedger6719Research
open scoped Classical BigOperators
open ContactFlagBezout6543Research ContactFactoredFlagCount6676Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def surfaceFlag (a b s : ℕ) : FlagDegree := ⟨a,b+1,s+2⟩
def denominatorFlag (a b s : ℕ) : FlagDegree := ⟨a,b+1,s+1⟩
def numeratorFlag (a b s : ℕ) : FlagDegree := ⟨a,b,s+3⟩
def fiberFlag (a b s : ℕ) : FlagDegree := ⟨a,b+1,s+3⟩
def normalFlag (a b s : ℕ) : FlagDegree := ⟨a,b,s⟩
def directionFlag (a b s : ℕ) : FlagDegree := ⟨2*a,2*b+1,2*s+3⟩
def centreFlag (a b s : ℕ) : FlagDegree := unitYZFlag+directionFlag a b s

def qeff (a b s : ℕ) (p : FlagDegree) : ℕ :=
  flagMixed p (directionFlag a b s) (normalFlag a b s)+
    flagMixed p (fiberFlag a b s) (surfaceFlag a b s)
def quad (a b s : ℕ) (p : FlagDegree) : ℕ := flagMixed p (directionFlag a b s) (directionFlag a b s)
def ell (a b s : ℕ) (p : FlagDegree) : ℕ := flagMixed p (directionFlag a b s) unitYZFlag
def unitBase (p : FlagDegree) : ℕ := flagMixed p unitYZFlag unitYZFlag
def lin (a b s : ℕ) (p : FlagDegree) : ℕ := flagMixed p (centreFlag a b s) (directionFlag a b s)
def unit (a b s : ℕ) (p : FlagDegree) : ℕ := flagMixed p (centreFlag a b s) (centreFlag a b s)
def zSlope (a b s : ℕ) (p : FlagDegree) : ℕ := flagMixed p (directionFlag a b s) unitZFlag
def zBase (a b s : ℕ) (p : FlagDegree) : ℕ := flagMixed p (centreFlag a b s) unitZFlag
def yzSlope (a b s : ℕ) (p : FlagDegree) : ℕ := flagMixed p (directionFlag a b s) unitYZFlag
def yzBase (a b s : ℕ) (p : FlagDegree) : ℕ := flagMixed p (centreFlag a b s) unitYZFlag
def weightedMixed (p q r : FlagDegree) : ℕ :=
  r.zOnly*flagMixed p q unitZFlag+r.yz*flagMixed p q unitYZFlag+r.all*flagMixed p q unitAllFlag

theorem weightedMixed_eq (p q r : FlagDegree) : weightedMixed p q r=flagMixed p q r := by
  simp only [weightedMixed,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
  ring

/-- .
 -/
theorem qeff_add_base (a b s : ℕ) (p : FlagDegree) :
    qeff a b s p+flagMixed p (denominatorFlag a b s) (numeratorFlag a b s)=
      quad a b s p+2*flagMixed p unitAllFlag unitYZFlag := by
  simp only [qeff,quad,directionFlag,normalFlag,fiberFlag,surfaceFlag,
    denominatorFlag,numeratorFlag,flagMixed,unitAllFlag,unitYZFlag]
  ring

theorem lin_eq (a b s : ℕ) (p : FlagDegree) : lin a b s p=quad a b s p+ell a b s p := by
  simp only [lin,quad,ell,centreFlag,flagMixed,add_zOnly,add_yz,add_all,unitYZFlag]
  ring
theorem unit_eq (a b s : ℕ) (p : FlagDegree) :
    unit a b s p=quad a b s p+2*ell a b s p+unitBase p := by
  simp only [unit,quad,ell,unitBase,centreFlag,flagMixed,add_zOnly,add_yz,add_all,unitYZFlag]
  ring

theorem envelope_identity (a b s d : ℕ) (p : FlagDegree) :
    weightedMixed p (centreFlag a b s+d • directionFlag a b s) (normalFlag a b s)+
      flagMixed p (fiberFlag a b s) (centreFlag a b s+d • surfaceFlag a b s)=
        d*qeff a b s p+lin a b s p := by
  simp only [weightedMixed,qeff,lin,centreFlag,directionFlag,normalFlag,fiberFlag,surfaceFlag,
    flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all,unitZFlag,unitYZFlag,unitAllFlag]
  ring

theorem centre_identity (a b s d : ℕ) (p : FlagDegree) :
    weightedMixed p (centreFlag a b s+d • directionFlag a b s) (centreFlag a b s)=
      d*lin a b s p+unit a b s p := by
  simp only [weightedMixed,lin,unit,flagMixed,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all,unitZFlag,unitYZFlag,unitAllFlag]
  ring

theorem z_affine (a b s d : ℕ) (p : FlagDegree) :
    flagMixed p (centreFlag a b s+d • directionFlag a b s) unitZFlag=
      d*zSlope a b s p+zBase a b s p := by
  simp only [zSlope,zBase,flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
  ring
theorem yz_affine (a b s d : ℕ) (p : FlagDegree) :
    flagMixed p (centreFlag a b s+d • directionFlag a b s) unitYZFlag=
      d*yzSlope a b s p+yzBase a b s p := by
  simp only [yzSlope,yzBase,flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
  ring

section Cumulative
variable {I : Type*} [Fintype I] (flags : I → FlagDegree) (p : FlagDegree)
variable (hs : (∑ i,(flags i).all) ≤ p.all)
variable (hm : (∑ i,((flags i).yz+(flags i).all)) ≤ p.yz+p.all)
variable (ht : (∑ i,((flags i).zOnly+(flags i).yz+(flags i).all)) ≤ p.zOnly+p.yz+p.all)
include hs hm ht

/-- . -/
theorem sum_qeff_le (a b s : ℕ) : (∑ i,qeff a b s (flags i)) ≤ qeff a b s p := by
  simp only [qeff,Finset.sum_add_distrib]
  exact add_le_add
    (sum_flagMixed_le_of_cumulative flags p (directionFlag a b s) (normalFlag a b s) hs hm ht)
    (sum_flagMixed_le_of_cumulative flags p (fiberFlag a b s) (surfaceFlag a b s) hs hm ht)
theorem sum_lin_le (a b s : ℕ) : (∑ i,lin a b s (flags i)) ≤ lin a b s p :=
  sum_flagMixed_le_of_cumulative flags p (centreFlag a b s) (directionFlag a b s) hs hm ht
theorem sum_unit_le (a b s : ℕ) : (∑ i,unit a b s (flags i)) ≤ unit a b s p :=
  sum_flagMixed_le_of_cumulative flags p (centreFlag a b s) (centreFlag a b s) hs hm ht
theorem sum_zSlope_le (a b s : ℕ) : (∑ i,zSlope a b s (flags i)) ≤ zSlope a b s p :=
  sum_flagMixed_le_of_cumulative flags p (directionFlag a b s) unitZFlag hs hm ht
theorem sum_zBase_le (a b s : ℕ) : (∑ i,zBase a b s (flags i)) ≤ zBase a b s p :=
  sum_flagMixed_le_of_cumulative flags p (centreFlag a b s) unitZFlag hs hm ht
theorem sum_yzSlope_le (a b s : ℕ) : (∑ i,yzSlope a b s (flags i)) ≤ yzSlope a b s p :=
  sum_flagMixed_le_of_cumulative flags p (directionFlag a b s) unitYZFlag hs hm ht
theorem sum_yzBase_le (a b s : ℕ) : (∑ i,yzBase a b s (flags i)) ≤ yzBase a b s p :=
  sum_flagMixed_le_of_cumulative flags p (centreFlag a b s) unitYZFlag hs hm ht

theorem sum_envelope_le (a b s d : ℕ) :
    (∑ i,(weightedMixed (flags i) (centreFlag a b s+d • directionFlag a b s) (normalFlag a b s)+
      flagMixed (flags i) (fiberFlag a b s) (centreFlag a b s+d • surfaceFlag a b s))) ≤
        d*qeff a b s p+lin a b s p := by
  simp_rw [envelope_identity]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  exact add_le_add (Nat.mul_le_mul_left d (sum_qeff_le flags p hs hm ht a b s))
    (sum_lin_le flags p hs hm ht a b s)

theorem sum_centre_le (a b s d : ℕ) :
    (∑ i,weightedMixed (flags i) (centreFlag a b s+d • directionFlag a b s) (centreFlag a b s)) ≤
      d*lin a b s p+unit a b s p := by
  simp_rw [centre_identity]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  exact add_le_add (Nat.mul_le_mul_left d (sum_lin_le flags p hs hm ht a b s))
    (sum_unit_le flags p hs hm ht a b s)

theorem sum_z_tail_le (a b s d : ℕ) :
    (∑ i,flagMixed (flags i) (centreFlag a b s+d • directionFlag a b s) unitZFlag) ≤
      d*zSlope a b s p+zBase a b s p := by
  rw [← z_affine]
  exact sum_flagMixed_le_of_cumulative flags p _ _ hs hm ht
theorem sum_yz_tail_le (a b s d : ℕ) :
    (∑ i,flagMixed (flags i) (centreFlag a b s+d • directionFlag a b s) unitYZFlag) ≤
      d*yzSlope a b s p+yzBase a b s p := by
  rw [← yz_affine]
  exact sum_flagMixed_le_of_cumulative flags p _ _ hs hm ht
end Cumulative

/-- . -/
theorem qeff_row : qeff 955 40 8 (surfaceFlag 955 40 8)=7643526 := by
  norm_num [qeff,surfaceFlag,directionFlag,normalFlag,fiberFlag,flagMixed]
theorem correction_row : 2*flagMixed (surfaceFlag 955 40 8) unitAllFlag unitYZFlag=2012 := by
  norm_num [surfaceFlag,flagMixed,unitAllFlag,unitYZFlag]

end
end ProximityPrize.SubmissionLower.ContactMovingPositiveLedger6719Research
