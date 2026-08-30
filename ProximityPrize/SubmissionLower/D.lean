import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AH
namespace ProximityPrize.SubmissionLower.RCN095
open scoped BigOperators
open ProximityPrize.SubmissionLower.RCN295
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
structure FlagDegree where
 zOnly:ℕ
 yz:ℕ
 all:ℕ
 deriving DecidableEq,Repr
instance:Add FlagDegree:=⟨fun p q↦
 ⟨p.zOnly+q.zOnly,p.yz+q.yz,p.all+q.all⟩⟩
instance:SMul ℕ FlagDegree:=⟨fun n p↦
 ⟨n*p.zOnly,n*p.yz,n*p.all⟩⟩
@[simp] theorem add_zOnly (p q:FlagDegree):
   (p+q).zOnly=p.zOnly+q.zOnly:=rfl
@[simp] theorem add_yz (p q:FlagDegree):
   (p+q).yz=p.yz+q.yz:=rfl
@[simp] theorem add_all (p q:FlagDegree):
   (p+q).all=p.all+q.all:=rfl
@[simp] theorem nsmul_zOnly (n:ℕ) (p:FlagDegree):
   (n • p).zOnly=n*p.zOnly:=rfl
@[simp] theorem nsmul_yz (n:ℕ) (p:FlagDegree):
   (n • p).yz=n*p.yz:=rfl
@[simp] theorem nsmul_all (n:ℕ) (p:FlagDegree):
   (n • p).all=n*p.all:=rfl
def InFlag (p:FlagDegree) (d:Fin 3 →₀ ℕ):Prop:=
 d 1 ≤ p.all∧
   d 0+d 1 ≤ p.yz+p.all∧
   d 0+d 1+d 2 ≤ p.zOnly+p.yz+p.all
theorem inFlag_zero (p:FlagDegree):InFlag p 0:=by
 simp [InFlag]
theorem inFlag_add {p q:FlagDegree} {d e:Fin 3 →₀ ℕ}
   (hd:InFlag p d) (he:InFlag q e):InFlag (p+q) (d+e):=by
 rcases hd with ⟨hdS,hdYS,hdTot⟩
 rcases he with ⟨heS,heYS,heTot⟩
 simp only [InFlag,Finsupp.add_apply,add_zOnly,add_yz,add_all]
 omega
noncomputable def exponentOfTriple (t:ℕ × ℕ × ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 t.1+Finsupp.single 1 t.2.1+
   Finsupp.single 2 t.2.2
noncomputable def flagSupport (p:FlagDegree):Finset (Fin 3 →₀ ℕ):=
 by
   classical
   exact (((((Finset.range (p.zOnly+p.yz+p.all+1)).product
       (Finset.range (p.all+1))).product
       (Finset.range (p.zOnly+p.yz+p.all+1))).image
         (fun t↦exponentOfTriple (t.1.1,t.1.2,t.2))).filter (InFlag p))
theorem exponentOfTriple_coordinates (y s z:ℕ):
   exponentOfTriple (y,s,z) 0=y∧
     exponentOfTriple (y,s,z) 1=s∧
     exponentOfTriple (y,s,z) 2=z:=by
 simp [exponentOfTriple]
theorem mem_flagSupport_iff (p:FlagDegree) (d:Fin 3 →₀ ℕ):
   d∈flagSupport p ↔ InFlag p d:=by
 classical
 constructor
 · intro hd
   unfold flagSupport at hd
   exact (Finset.mem_filter.mp hd).2
 · intro hd
   unfold flagSupport
   rw [Finset.mem_filter]
   refine ⟨?_,hd⟩
   apply Finset.mem_image.mpr
   rcases hd with ⟨hS,hYS,htotal⟩
   refine ⟨((d 0,d 1),d 2),?_,?_⟩
   · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
       ⟨Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega),
         Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega)⟩,
       Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega)⟩
   · ext i
     fin_cases i <;> simp [exponentOfTriple]
theorem zero_mem_flagSupport (p:FlagDegree):
   (0:Fin 3 →₀ ℕ)∈flagSupport p:=by
 rw [mem_flagSupport_iff]
 exact inFlag_zero p
theorem flagSupport_downwardClosed (p:FlagDegree):
   ExponentSetDownwardClosed (flagSupport p):=by
 intro d hd e he
 rw [mem_flagSupport_iff] at hd ⊢
 rcases hd with ⟨hdS,hdYS,hdtotal⟩
 have h0:=he 0
 have h1:=he 1
 have h2:=he 2
 exact ⟨h1.trans hdS,by omega,by omega⟩
def PolynomialInFlag {K:Type*} [Field K]
   (p:FlagDegree) (A:MvPolynomial (Fin 3) K):Prop:=
 ∀ d∈A.support,InFlag p d
theorem support_subset_flagSupport_iff {K:Type*} [Field K]
   (p:FlagDegree) (A:MvPolynomial (Fin 3) K):
   A.support ⊆ flagSupport p ↔ PolynomialInFlag p A:=by
 simp only [PolynomialInFlag,Finset.subset_iff,mem_flagSupport_iff]
def flagSWeights:Fin 3 → ℕ:=![0,1,0]
def flagYSWeights:Fin 3 → ℕ:=![1,1,0]
def flagTotalWeights:Fin 3 → ℕ:=![1,1,1]
theorem flag_weight_fin3 (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i <;> simp
 rw [hd,map_add,map_add]
 simp [Finsupp.weight_single,Nat.mul_comm]
theorem support_subset_flagSupport_of_weighted_degrees
   {K:Type*} [Field K] (p:FlagDegree)
   (A:MvPolynomial (Fin 3) K)
   (hS:MvPolynomial.weightedTotalDegree flagSWeights A ≤ p.all)
   (hYS:MvPolynomial.weightedTotalDegree flagYSWeights A ≤ p.yz+p.all)
   (hTotal:MvPolynomial.weightedTotalDegree flagTotalWeights A ≤
     p.zOnly+p.yz+p.all):
   A.support ⊆ flagSupport p:=by
 rw [support_subset_flagSupport_iff]
 intro d hd
 have hs:=(MvPolynomial.le_weightedTotalDegree flagSWeights hd).trans hS
 have hys:=(MvPolynomial.le_weightedTotalDegree flagYSWeights hd).trans hYS
 have htotal:=
   (MvPolynomial.le_weightedTotalDegree flagTotalWeights hd).trans hTotal
 rw [flag_weight_fin3] at hs hys htotal
 change d 0*0+d 1*1+d 2*0 ≤ p.all at hs
 change d 0*1+d 1*1+d 2*0 ≤ p.yz+p.all at hys
 change d 0*1+d 1*1+d 2*1 ≤
   p.zOnly+p.yz+p.all at htotal
 simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.zero_add] at hs hys htotal
 exact ⟨hs,hys,htotal⟩
def flagMixed (p q r:FlagDegree):ℕ:=
 p.all*q.all*r.all+
 (p.zOnly*q.all*r.all+q.zOnly*p.all*r.all+
   r.zOnly*p.all*q.all)+
 (p.yz*q.all*r.all+q.yz*p.all*r.all+
   r.yz*p.all*q.all)+
 (p.all*q.yz*r.yz+q.all*p.yz*r.yz+
   r.all*p.yz*q.yz)+
 (p.zOnly*q.yz*r.all+p.zOnly*r.yz*q.all+
   q.zOnly*p.yz*r.all+q.zOnly*r.yz*p.all+
   r.zOnly*p.yz*q.all+r.zOnly*q.yz*p.all)
def unitZFlag:FlagDegree:=⟨1,0,0⟩
def unitYZFlag:FlagDegree:=⟨0,1,0⟩
def unitAllFlag:FlagDegree:=⟨0,0,1⟩
def seedFlag:FlagDegree:=unitYZFlag
private def legacyN:ℕ:=262144
private def legacyW:ℕ:=131071
private def legacyErrors:ℕ:=78210
private def legacyAgreements:ℕ:=legacyN-legacyErrors
private def legacyGap:ℕ:=legacyAgreements-legacyW
private def legacyAlignmentBudget:ℕ:=100000000000000000
private def legacyShearedWholeMixedCap:ℕ:=16230040480658160
private def legacySingularNumerator:ℕ:=8043405963321174171
private def legacyGapSquared:ℕ:=legacyGap^2
def shearedSurfaceFlag:FlagDegree:=⟨350,21,5⟩
def shearedDerivativeFlag:FlagDegree:=⟨350,21,4⟩
def shearedAgreementFlag:FlagDegree:=
 seedFlag+legacyW • (shearedSurfaceFlag+shearedDerivativeFlag)
theorem shearedAgreementFlag_value:
   shearedAgreementFlag=⟨91749700,5504983,1179639⟩:=by
 change (⟨0+131071*(350+350),
     1+131071*(21+21),
     0+131071*(5+4)⟩:FlagDegree)=_
 norm_num
def flagWholeMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag shearedAgreementFlag
def flagZMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitZFlag
def flagYZMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitYZFlag
def flagAllMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitAllFlag
theorem flag_mixed_values:
   flagWholeMixedCap=16236998221509765∧
     flagZMixedCap=58195529∧
     flagYZMixedCap=929817679∧
     flagAllMixedCap=4898910072:=by
 norm_num [flagWholeMixedCap,flagZMixedCap,flagMixed,
   flagYZMixedCap,flagAllMixedCap,
   shearedSurfaceFlag,shearedAgreementFlag,shearedDerivativeFlag,
   seedFlag,unitZFlag,unitYZFlag,unitAllFlag,legacyW]
theorem flag_projection_decomposition:
   flagWholeMixedCap=
     shearedAgreementFlag.zOnly*flagZMixedCap+
     shearedAgreementFlag.yz*flagYZMixedCap+
     shearedAgreementFlag.all*flagAllMixedCap:=by
 norm_num [flagWholeMixedCap,flagZMixedCap,flagYZMixedCap,
   flagAllMixedCap,flagMixed,shearedSurfaceFlag,
   shearedAgreementFlag,shearedDerivativeFlag,seedFlag,
   unitZFlag,unitYZFlag,unitAllFlag,legacyW]
theorem flag_excess_exact:
   flagWholeMixedCap-legacyShearedWholeMixedCap=6957740851605:=by
 rw [flag_mixed_values.1]
 norm_num [legacyShearedWholeMixedCap]
def flagWholeNumerator:ℕ:=
 (legacyN-legacyW)^2*flagWholeMixedCap+
   (legacyErrors+1)*(legacyN-legacyW)*legacyGap*flagZMixedCap
def flagTotalNumerator:ℕ:=
 flagWholeNumerator+legacyGap*legacySingularNumerator
def flagLedgerCeiling:ℕ:=
 (flagTotalNumerator+legacyGapSquared-1)/legacyGapSquared
theorem flag_whole_numerator_exact:
   flagWholeNumerator=278985298988701469237937066:=by
 norm_num [flagWholeNumerator,flag_mixed_values.1,flag_mixed_values.2.1,
   legacyN,legacyW,legacyErrors,legacyGap,legacyAgreements]
theorem flag_total_numerator_exact:
   flagTotalNumerator=279410497558140516468138639:=by
 rw [show flagTotalNumerator=
     flagWholeNumerator+legacyGap*legacySingularNumerator by rfl,
   flag_whole_numerator_exact]
 norm_num [legacySingularNumerator,legacyGap,legacyAgreements,
   legacyN,legacyErrors,legacyW]
theorem flag_ledger_ceiling_exact:
   flagLedgerCeiling=99985979822093871:=by
 norm_num [flagLedgerCeiling,flag_total_numerator_exact,
   legacyGapSquared,legacyGap,legacyAgreements,legacyN,legacyErrors,
   legacyW]
theorem flag_budget_slack:
   legacyAlignmentBudget-flagLedgerCeiling=14020177906129:=by
 rw [flag_ledger_ceiling_exact]
 norm_num [legacyAlignmentBudget]
theorem flag_strict_budget:
   flagTotalNumerator < legacyAlignmentBudget*legacyGapSquared:=by
 rw [flag_total_numerator_exact]
 norm_num [legacyAlignmentBudget,legacyGapSquared,legacyGap,
   legacyAgreements,legacyN,legacyErrors,legacyW]
end ProximityPrize.SubmissionLower.RCN095
