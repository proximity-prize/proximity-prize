
namespace ProximityPrize.SubmissionUpper

def crownAgreement : ℕ := 139775

def nextCentibitAgreement : ℕ := 139782

def crownBlocks : ℕ := 272

def fibreSize : ℕ := 512

def coreRoots : ℕ := 511

theorem crownAgreement_fibre :
    crownAgreement = coreRoots + crownBlocks * fibreSize := by
  decide

theorem nextCentibitAgreement_eq :
    nextCentibitAgreement = crownAgreement + 7 := by
  decide

theorem rowDegree_strict : 131071 < 131072 := by
  decide

theorem crown_numerator_degree :
    coreRoots + 255 * fibreSize = 131071 := by
  decide

theorem crown_numerator_one_below_row :
    coreRoots + 255 * fibreSize + 1 = 131072 := by
  decide

theorem crown_unsafeIndex :
    2 ^ 18 - crownAgreement = 122369 := by
  decide

theorem next_unsafeIndex :
    2 ^ 18 - nextCentibitAgreement = 122362 := by
  decide

end ProximityPrize.SubmissionUpper
