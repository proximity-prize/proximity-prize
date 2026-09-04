import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.CyclicFourFibre

open ProximityPrize.Benchmark

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The size of one fibre of the fourth-power quotient of the challenge domain. -/
def quarterSize : ℕ := 2 ^ 16

/-- A sparse representation of `X ^ quarterSize` that remains cheap to elaborate. -/
def cutoffPolynomial {F : Type*} [Field F] : Polynomial F :=
  Polynomial.monomial quarterSize 1

theorem cutoffPolynomial_eq_X_pow {F : Type*} [Field F] :
    (cutoffPolynomial : Polynomial F) = Polynomial.X ^ quarterSize := by
  exact Polynomial.monomial_one_right_eq_X_pow quarterSize

theorem cutoffPolynomial_monic {F : Type*} [Field F] :
    (cutoffPolynomial : Polynomial F).Monic := by
  rw [cutoffPolynomial_eq_X_pow]
  exact Polynomial.monic_X_pow quarterSize

theorem cutoffPolynomial_natDegree {F : Type*} [Field F] :
    (cutoffPolynomial : Polynomial F).natDegree = quarterSize := by
  rw [cutoffPolynomial_eq_X_pow, Polynomial.natDegree_X_pow]

/-- The part of a polynomial supported in degrees below `quarterSize`. -/
def lowPart {F : Type*} [Field F] (P : Polynomial F) : Polynomial F :=
  P %ₘ cutoffPolynomial

/-- The coefficient block above degree `quarterSize`. -/
def highPart {F : Type*} [Field F] (P : Polynomial F) : Polynomial F :=
  P /ₘ cutoffPolynomial

theorem lowPart_add_X_pow_mul_highPart {F : Type*} [Field F]
    (P : Polynomial F) :
    lowPart P + Polynomial.X ^ quarterSize * highPart P = P := by
  rw [← cutoffPolynomial_eq_X_pow]
  unfold lowPart highPart
  apply Polynomial.modByMonic_add_div

set_option maxRecDepth 20000 in
theorem lowPart_natDegree_lt {F : Type*} [Field F]
    (P : Polynomial F) : (lowPart P).natDegree < quarterSize := by
  unfold lowPart
  have hne : (cutoffPolynomial : Polynomial F) ≠ 1 := by
    intro h
    have hdegree := congrArg Polynomial.natDegree h
    rw [cutoffPolynomial_natDegree, Polynomial.natDegree_one] at hdegree
    norm_num [quarterSize] at hdegree
  have h := Polynomial.natDegree_modByMonic_lt P
    cutoffPolynomial_monic hne
  simpa only [cutoffPolynomial_natDegree] using h

set_option maxRecDepth 20000 in
theorem highPart_natDegree_lt {F : Type*} [Field F]
    (P : Polynomial F) (hP : P.natDegree ≤ 131071) :
    (highPart P).natDegree < quarterSize := by
  rw [highPart, Polynomial.natDegree_divByMonic P
    cutoffPolynomial_monic, cutoffPolynomial_natDegree]
  norm_num [quarterSize] at *
  omega

theorem eval_eq_lowPart_add_pow_mul_highPart {F : Type*} [Field F]
    (P : Polynomial F) (x : F) :
    P.eval x = (lowPart P).eval x + x ^ quarterSize * (highPart P).eval x := by
  conv_lhs => rw [← lowPart_add_X_pow_mul_highPart P]
  simp

theorem baseNode_pow_domainSize (i : IRSProfile.Index) :
    IRSProfile.baseNttDomain.node i ^ (2 ^ 18) = 1 := by
  change (IRSProfile.baseNttDomain.omega ^ (i : ℕ)) ^ (2 ^ 18) = 1
  have hroot := IRSProfile.baseNttDomain.primitive.pow_eq_one
  change IRSProfile.baseNttDomain.omega ^ (2 ^ 18) = 1 at hroot
  rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]

theorem domain_pow_domainSize (i : IRSProfile.Index) :
    IRSProfile.domain i ^ (2 ^ 18) = 1 := by
  change ((CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params)
    (IRSProfile.baseNttDomain.node i)) ^ (2 ^ 18) = 1
  rw [← map_pow, baseNode_pow_domainSize]
  exact map_one _

/-- The four-fibre quotient coordinate `T = X^(2^16)` on the challenge domain. -/
def outerValue (i : IRSProfile.Index) : IRSProfile.Field :=
  IRSProfile.domain i ^ quarterSize

theorem outerValue_pow_four (i : IRSProfile.Index) : outerValue i ^ 4 = 1 := by
  rw [outerValue, ← pow_mul]
  norm_num [quarterSize]
  exact domain_pow_domainSize i

theorem eval_domain_eq_two_block (P : Polynomial IRSProfile.Field)
    (i : IRSProfile.Index) :
    P.eval (IRSProfile.domain i) =
      (lowPart P).eval (IRSProfile.domain i) +
        outerValue i * (highPart P).eval (IRSProfile.domain i) := by
  exact eval_eq_lowPart_add_pow_mul_highPart P (IRSProfile.domain i)

/-- Enumerate the `r`-th quotient fibre by its offset inside that fibre. -/
def fibreIndex (r : Fin 4) (j : Fin quarterSize) : IRSProfile.Index :=
  ⟨r + 4 * j, by
    have hr := r.isLt
    have hj := j.isLt
    norm_num [quarterSize] at hr hj ⊢
    omega⟩

def zeroOffset : Fin quarterSize :=
  ⟨0, by norm_num [quarterSize]⟩

theorem fibreIndex_injective (r : Fin 4) : Function.Injective (fibreIndex r) := by
  intro j k h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [fibreIndex] at hval
  omega

/-- Recover the quotient-fibre label of a domain index. -/
def fibreOf (i : IRSProfile.Index) : Fin 4 :=
  ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Recover the offset within a quotient fibre. -/
def offsetOf (i : IRSProfile.Index) : Fin quarterSize :=
  ⟨i / 4, by
    have hi := i.isLt
    norm_num [quarterSize] at hi ⊢
    omega⟩

theorem fibreIndex_fibreOf_offsetOf (i : IRSProfile.Index) :
    fibreIndex (fibreOf i) (offsetOf i) = i := by
  apply Fin.ext
  simp only [fibreIndex, fibreOf, offsetOf]
  omega

theorem fibreOf_fibreIndex (r : Fin 4) (j : Fin quarterSize) :
    fibreOf (fibreIndex r j) = r := by
  apply Fin.ext
  simp only [fibreOf, fibreIndex]
  have hr := r.isLt
  omega

theorem offsetOf_fibreIndex (r : Fin 4) (j : Fin quarterSize) :
    offsetOf (fibreIndex r j) = j := by
  apply Fin.ext
  simp only [offsetOf, fibreIndex]
  have hr := r.isLt
  omega

/-- The challenge domain is exactly four fibres of size `2^16`. -/
def fibreEquiv : (Fin 4 × Fin quarterSize) ≃ IRSProfile.Index where
  toFun p := fibreIndex p.1 p.2
  invFun i := (fibreOf i, offsetOf i)
  left_inv p := by
    rcases p with ⟨r, j⟩
    simp only [fibreOf_fibreIndex, offsetOf_fibreIndex]
  right_inv := fibreIndex_fibreOf_offsetOf

/-- The base-field value of the quotient coordinate. -/
def baseOuterValue (i : IRSProfile.Index) : KoalaBear.Field :=
  IRSProfile.baseNttDomain.node i ^ quarterSize

theorem outerValue_eq_map_baseOuterValue (i : IRSProfile.Index) :
    outerValue i =
      (CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params) (baseOuterValue i) := by
  rw [outerValue, baseOuterValue]
  change ((CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params)
    (IRSProfile.baseNttDomain.node i)) ^ quarterSize = _
  rw [map_pow]

theorem baseOuterValue_fibreIndex (r : Fin 4) (j : Fin quarterSize) :
    baseOuterValue (fibreIndex r j) =
      baseOuterValue (fibreIndex r zeroOffset) := by
  have hroot : IRSProfile.baseNttDomain.omega ^ (2 ^ 18) = 1 := by
    have h := IRSProfile.baseNttDomain.primitive.pow_eq_one
    change IRSProfile.baseNttDomain.omega ^ (2 ^ 18) = 1 at h
    exact h
  change
    (IRSProfile.baseNttDomain.omega ^ (r + 4 * j : ℕ)) ^ quarterSize =
      (IRSProfile.baseNttDomain.omega ^ (r : ℕ)) ^ quarterSize
  rw [← pow_mul, ← pow_mul]
  have hexp : (r + 4 * j : ℕ) * quarterSize =
      r * quarterSize + (2 ^ 18) * j := by
    norm_num [quarterSize]
    omega
  rw [hexp, pow_add]
  have hjroot : IRSProfile.baseNttDomain.omega ^ ((2 ^ 18) * (j : ℕ)) = 1 := by
    rw [pow_mul, hroot, one_pow]
  rw [hjroot, mul_one]

theorem outerValue_fibreIndex (r : Fin 4) (j : Fin quarterSize) :
    outerValue (fibreIndex r j) = outerValue (fibreIndex r zeroOffset) := by
  rw [outerValue_eq_map_baseOuterValue, outerValue_eq_map_baseOuterValue,
    baseOuterValue_fibreIndex]

/-- The quotient coordinate attached to a fibre label. -/
def outerRepresentative (r : Fin 4) : IRSProfile.Field :=
  outerValue (fibreIndex r zeroOffset)

theorem outerRepresentative_injective : Function.Injective outerRepresentative := by
  intro r s h
  simp only [outerRepresentative, outerValue_eq_map_baseOuterValue] at h
  have hbase := (CompPoly.Extension.Ext.ofBaseRingHom
    KoalaBear.ext6Params).injective h
  change
    (IRSProfile.baseNttDomain.omega ^ (r : ℕ)) ^ quarterSize =
      (IRSProfile.baseNttDomain.omega ^ (s : ℕ)) ^ quarterSize at hbase
  rw [← pow_mul, ← pow_mul] at hbase
  have hr : (r : ℕ) * quarterSize < 2 ^ 18 := by
    have := r.isLt
    norm_num [quarterSize] at this ⊢
    omega
  have hs : (s : ℕ) * quarterSize < 2 ^ 18 := by
    have := s.isLt
    norm_num [quarterSize] at this ⊢
    omega
  have hrs := IRSProfile.baseNttDomain.primitive.pow_inj hr hs hbase
  apply Fin.ext
  norm_num [quarterSize] at hrs
  omega

/-- The degree-`< 2^16` polynomial obtained by restricting `P` to one fibre. -/
def fibrePolynomial (P : Polynomial IRSProfile.Field) (r : Fin 4) :
    Polynomial IRSProfile.Field :=
  lowPart P + Polynomial.C (outerRepresentative r) * highPart P

theorem fibrePolynomial_natDegree_lt (P : Polynomial IRSProfile.Field)
    (hP : P.natDegree ≤ 131071) (r : Fin 4) :
    (fibrePolynomial P r).natDegree < quarterSize := by
  refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
  apply max_lt
  · exact lowPart_natDegree_lt P
  · exact (Polynomial.natDegree_C_mul_le _ _).trans_lt
      (highPart_natDegree_lt P hP)

theorem eval_fibrePolynomial (P : Polynomial IRSProfile.Field) (r : Fin 4)
    (j : Fin quarterSize) :
    (fibrePolynomial P r).eval (IRSProfile.domain (fibreIndex r j)) =
      P.eval (IRSProfile.domain (fibreIndex r j)) := by
  rw [fibrePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    outerRepresentative, ← outerValue_fibreIndex r j]
  exact (eval_domain_eq_two_block P (fibreIndex r j)).symm

/-- Enumerate the four roots above one point of the `x ↦ x^4` folding. -/
def rootIndex (j : Fin quarterSize) (t : Fin 4) : IRSProfile.Index :=
  ⟨j + quarterSize * t, by
    have hj := j.isLt
    have ht := t.isLt
    norm_num [quarterSize] at hj ht ⊢
    omega⟩

theorem rootIndex_injective (j : Fin quarterSize) :
    Function.Injective (rootIndex j) := by
  intro t u h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [rootIndex] at hval
  norm_num [quarterSize] at hval
  omega

/-- Recover the base point of the four-root folding. -/
def rootBase (i : IRSProfile.Index) : Fin quarterSize :=
  ⟨i % quarterSize, Nat.mod_lt _ (by norm_num [quarterSize])⟩

/-- Recover the branch of the four-root folding. -/
def rootBranch (i : IRSProfile.Index) : Fin 4 :=
  ⟨i / quarterSize, by
    have hi := i.isLt
    norm_num [quarterSize] at hi ⊢
    omega⟩

theorem rootIndex_rootBase_rootBranch (i : IRSProfile.Index) :
    rootIndex (rootBase i) (rootBranch i) = i := by
  apply Fin.ext
  simp only [rootIndex, rootBase, rootBranch]
  exact Nat.mod_add_div (i : ℕ) quarterSize

theorem rootBase_rootIndex (j : Fin quarterSize) (t : Fin 4) :
    rootBase (rootIndex j t) = j := by
  apply Fin.ext
  simp only [rootBase, rootIndex]
  have hj := j.isLt
  norm_num [quarterSize] at hj ⊢
  omega

theorem rootBranch_rootIndex (j : Fin quarterSize) (t : Fin 4) :
    rootBranch (rootIndex j t) = t := by
  apply Fin.ext
  simp only [rootBranch, rootIndex]
  have hj := j.isLt
  norm_num [quarterSize] at hj ⊢
  omega

/-- The full NTT domain is also exactly `2^16` bundles of four fourth roots. -/
def rootFibreEquiv : (Fin quarterSize × Fin 4) ≃ IRSProfile.Index where
  toFun p := rootIndex p.1 p.2
  invFun i := (rootBase i, rootBranch i)
  left_inv p := by
    rcases p with ⟨j, t⟩
    simp only [rootBase_rootIndex, rootBranch_rootIndex]
  right_inv := rootIndex_rootBase_rootBranch

/-- The coordinate on the folded size-`2^16` domain. -/
def foldValue (i : IRSProfile.Index) : IRSProfile.Field :=
  IRSProfile.domain i ^ 4

theorem foldValue_rootIndex (j : Fin quarterSize) (t : Fin 4) :
    foldValue (rootIndex j t) = foldValue (rootIndex j (0 : Fin 4)) := by
  have hroot : IRSProfile.baseNttDomain.omega ^ (2 ^ 18) = 1 := by
    have h := IRSProfile.baseNttDomain.primitive.pow_eq_one
    change IRSProfile.baseNttDomain.omega ^ (2 ^ 18) = 1 at h
    exact h
  change
    ((CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params)
      (IRSProfile.baseNttDomain.omega ^ (j + quarterSize * t : ℕ))) ^ 4 =
    ((CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params)
      (IRSProfile.baseNttDomain.omega ^ (j : ℕ))) ^ 4
  rw [← map_pow, ← map_pow]
  apply congrArg (CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params)
  rw [← pow_mul, ← pow_mul]
  have hexp : (j + quarterSize * t : ℕ) * 4 =
      j * 4 + (2 ^ 18) * t := by
    norm_num [quarterSize]
    omega
  rw [hexp, pow_add]
  have htroot : IRSProfile.baseNttDomain.omega ^ ((2 ^ 18) * (t : ℕ)) = 1 := by
    rw [pow_mul, hroot, one_pow]
  rw [htroot, mul_one]

theorem rootValue_injective (j : Fin quarterSize) :
    Function.Injective (fun t : Fin 4 => IRSProfile.domain (rootIndex j t)) :=
  IRSProfile.domain.injective.comp (rootIndex_injective j)

end

end ProximityPrize.SubmissionLower.CyclicFourFibre
