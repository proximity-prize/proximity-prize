import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingSeedless6750Research

 







namespace ProximityPrize.SubmissionLower.ContactTwoTailParameters6750Research

open ProximityPrize.Benchmark

noncomputable section

set_option autoImplicit false

def n : Nat := 262144
def w : Nat := 131071
def prime : Nat := 2130706433
def score : Nat := 6750
def errors : Nat := 80260
def agreements : Nat := n - errors
def gap : Nat := agreements - w
def radiusNumerator : Nat := 10273407
def radiusDenominator : Nat := 33554432
def listBudget : Nat := ContactMovingSeedless6750Research.listBudget
def mcaBudget : Nat := ContactMovingSeedless6750Research.mcaBudget

structure Profile where
  multiplicity : Nat
  totalCap : Nat
  slopeCap : Nat
  middleCap : Nat
  deriving DecidableEq

namespace Profile

def weightedCap (P : Profile) : Nat := P.multiplicity * agreements

end Profile

 
def profileA : Profile := ⟨47, 645635, 14, 65⟩
def profileB : Profile := ⟨94, 1668, 29, 130⟩
def profileC : Profile := profileA

theorem frozen_values :
    agreements = 181884 ∧ gap = 50813 ∧
      profileA.weightedCap = 8548548 ∧
      profileB.weightedCap = 17097096 ∧
      profileC.weightedCap = 8548548 ∧
      profileA = profileC ∧
      listBudget = 1208708861 ∧
      mcaBudget = 274980726902686226 := by
  decide

theorem radius_numerator_exact :
    radiusNumerator = 128 * errors + 127 := by
  decide

end


end ProximityPrize.SubmissionLower.ContactTwoTailParameters6750Research
