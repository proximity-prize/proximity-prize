import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingSeedless6750Research

 







namespace ProximityPrize.SubmissionLower.ContactTwoTailParameters6750Research

open ProximityPrize.Benchmark

noncomputable section

set_option autoImplicit false

def n : Nat := 262144
def w : Nat := 131071
def prime : Nat := 2130706433
def score : Nat := 6751
def errors : Nat := 80270
def agreements : Nat := n - errors
def gap : Nat := agreements - w
def radiusNumerator : Nat := 321083
def radiusDenominator : Nat := 1048576
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

 
def profileA : Profile := ⟨48, 40500, 14, 65⟩
def profileB : Profile := ⟨94, 1700, 29, 130⟩
def profileC : Profile := profileA

theorem frozen_values :
    agreements = 181874 ∧ gap = 50803 ∧
      profileA.weightedCap = 8729952 ∧
      profileB.weightedCap = 17096156 ∧
      profileC.weightedCap = 8729952 ∧
      profileA = profileC ∧
      listBudget = 1227545962 ∧
      mcaBudget = 274980726883849125 := by
  decide

theorem radius_numerator_exact :
    radiusNumerator = 4 * errors + 3 := by
  decide

end


end ProximityPrize.SubmissionLower.ContactTwoTailParameters6750Research
