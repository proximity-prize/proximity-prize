import ProximityPrize.Benchmark.TargetLower

 













namespace ProximityPrize.SubmissionLower.ContactNestedFiveCapCoefficientBox6750Research

open scoped Classical BigOperators Pointwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

universe u

variable (F : Type u) [Field F]

 
def nestedFiveCapExponents (D w T YS S : Nat) : Set (Fin 4 →₀ Nat) :=
  {d | d 1 + d 2 + d 3 ≤ T ∧ d 1 + d 2 ≤ YS ∧ d 2 ≤ S ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D}

 
def nestedFiveCapCoefficientBox (D w T YS S : Nat) :
    Submodule F (MvPolynomial (Fin 4) F) :=
  MvPolynomial.restrictSupport F (nestedFiveCapExponents D w T YS S)

 
abbrev NestedFiveCapCoefficientIndex (D w T YS S : Nat) :=
  (y : Fin (min T YS + 1)) ×
    (r : Fin (min S (min (T - y.val) (YS - y.val)) + 1)) ×
      (Fin (T + 1 - y.val - r.val) ×
        Fin (D - w * y.val - (w - 1) * r.val))

 
def nestedFiveCapCoefficientCount (D w T YS S : Nat) : Nat :=
  ∑ y ∈ Finset.range (min T YS + 1),
    ∑ r ∈ Finset.range (min S (min (T - y) (YS - y)) + 1),
      (T + 1 - y - r) * (D - w * y - (w - 1) * r)

 
def nestedFiveCapChannelCount (T YS S : Nat) : Nat :=
  ∑ y ∈ Finset.range (min T YS + 1),
    ∑ r ∈ Finset.range (min S (min (T - y) (YS - y)) + 1),
      (T + 1 - y - r)

 
def nestedFiveCapColumnExponent {D w T YS S : Nat}
    (c : NestedFiveCapCoefficientIndex D w T YS S) : Fin 4 →₀ Nat :=
  Finsupp.single 0 c.2.2.2.val + Finsupp.single 1 c.1.val +
    Finsupp.single 2 c.2.1.val + Finsupp.single 3 c.2.2.1.val

@[simp] theorem nestedFiveCapColumnExponent_x {D w T YS S : Nat}
    (c : NestedFiveCapCoefficientIndex D w T YS S) :
    nestedFiveCapColumnExponent c 0 = c.2.2.2.val := by
  simp [nestedFiveCapColumnExponent]

@[simp] theorem nestedFiveCapColumnExponent_y {D w T YS S : Nat}
    (c : NestedFiveCapCoefficientIndex D w T YS S) :
    nestedFiveCapColumnExponent c 1 = c.1.val := by
  simp [nestedFiveCapColumnExponent]

@[simp] theorem nestedFiveCapColumnExponent_r {D w T YS S : Nat}
    (c : NestedFiveCapCoefficientIndex D w T YS S) :
    nestedFiveCapColumnExponent c 2 = c.2.1.val := by
  simp [nestedFiveCapColumnExponent]

@[simp] theorem nestedFiveCapColumnExponent_z {D w T YS S : Nat}
    (c : NestedFiveCapCoefficientIndex D w T YS S) :
    nestedFiveCapColumnExponent c 3 = c.2.2.1.val := by
  simp [nestedFiveCapColumnExponent]

 
theorem nestedFiveCapColumnExponent_injective (D w T YS S : Nat) :
    Function.Injective
      (nestedFiveCapColumnExponent
        (D := D) (w := w) (T := T) (YS := YS) (S := S)) := by
  intro c d h
  have hx := congrArg (fun e : Fin 4 →₀ Nat => e 0) h
  have hy := congrArg (fun e : Fin 4 →₀ Nat => e 1) h
  have hr := congrArg (fun e : Fin 4 →₀ Nat => e 2) h
  have hz := congrArg (fun e : Fin 4 →₀ Nat => e 3) h
  rcases c with ⟨⟨cy, hcy⟩, ⟨⟨cr, hcr⟩, ⟨⟨cz, hcz⟩, ⟨cx, hcx⟩⟩⟩⟩
  rcases d with ⟨⟨dy, hdy⟩, ⟨⟨dr, hdr⟩, ⟨⟨dz, hdz⟩, ⟨dx, hdx⟩⟩⟩⟩
  simp only [nestedFiveCapColumnExponent_x] at hx
  simp only [nestedFiveCapColumnExponent_y] at hy
  simp only [nestedFiveCapColumnExponent_r] at hr
  simp only [nestedFiveCapColumnExponent_z] at hz
  subst dy
  subst dr
  subst dz
  subst dx
  rfl

 
def nestedFiveCapColumnExponentInSet (D w T YS S : Nat)
    (c : NestedFiveCapCoefficientIndex D w T YS S) :
    nestedFiveCapExponents D w T YS S := by
  refine ⟨nestedFiveCapColumnExponent c, ?_⟩
  simp only [nestedFiveCapExponents, Set.mem_setOf_eq,
    nestedFiveCapColumnExponent_x, nestedFiveCapColumnExponent_y,
    nestedFiveCapColumnExponent_r, nestedFiveCapColumnExponent_z]
  have hy := c.1.isLt
  have hr := c.2.1.isLt
  have hz := c.2.2.1.isLt
  have hx := c.2.2.2.isLt
  omega

 
theorem exists_nestedFiveCapColumnExponent_eq_of_mem
    (D w T YS S : Nat) (d : Fin 4 →₀ Nat)
    (hd : d ∈ nestedFiveCapExponents D w T YS S) :
    ∃ c : NestedFiveCapCoefficientIndex D w T YS S,
      nestedFiveCapColumnExponent c = d := by
  have htotal : d 1 + d 2 + d 3 ≤ T := hd.1
  have hys : d 1 + d 2 ≤ YS := hd.2.1
  have hs : d 2 ≤ S := hd.2.2.1
  have hw : d 0 + w * d 1 + (w - 1) * d 2 < D := hd.2.2.2
  let cy : Fin (min T YS + 1) := ⟨d 1, by omega⟩
  let cr : Fin (min S (min (T - cy.val) (YS - cy.val)) + 1) :=
    ⟨d 2, by dsimp [cy]; omega⟩
  let cz : Fin (T + 1 - cy.val - cr.val) :=
    ⟨d 3, by dsimp [cy, cr]; omega⟩
  let cx : Fin (D - w * cy.val - (w - 1) * cr.val) :=
    ⟨d 0, by dsimp [cy, cr]; omega⟩
  refine ⟨⟨cy, cr, cz, cx⟩, ?_⟩
  ext i
  fin_cases i <;>
    simp [nestedFiveCapColumnExponent, cy, cr, cz, cx]

 
def nestedFiveCapCoefficientIndexEquivExponents (D w T YS S : Nat) :
    NestedFiveCapCoefficientIndex D w T YS S ≃
      nestedFiveCapExponents D w T YS S :=
  Equiv.ofBijective (nestedFiveCapColumnExponentInSet D w T YS S) <| by
    constructor
    · intro c d h
      apply nestedFiveCapColumnExponent_injective D w T YS S
      exact congrArg Subtype.val h
    · intro d
      obtain ⟨c, hc⟩ := exists_nestedFiveCapColumnExponent_eq_of_mem
        D w T YS S d.1 d.2
      exact ⟨c, Subtype.ext hc⟩

@[reducible] def nestedFiveCapExponentsFintype (D w T YS S : Nat) :
    Fintype (nestedFiveCapExponents D w T YS S) :=
  Fintype.ofEquiv (NestedFiveCapCoefficientIndex D w T YS S)
    (nestedFiveCapCoefficientIndexEquivExponents D w T YS S)

 
theorem nestedFiveCapCoefficientIndex_card (D w T YS S : Nat) :
    Fintype.card (NestedFiveCapCoefficientIndex D w T YS S) =
      nestedFiveCapCoefficientCount D w T YS S := by
  simp [NestedFiveCapCoefficientIndex, nestedFiveCapCoefficientCount,
    Fintype.card_sigma, Finset.sum_range]

 
theorem nestedFiveCapCoefficientBox_finiteDimensional (D w T YS S : Nat) :
    FiniteDimensional F (nestedFiveCapCoefficientBox F D w T YS S) := by
  letI : Fintype (nestedFiveCapExponents D w T YS S) :=
    nestedFiveCapExponentsFintype D w T YS S
  exact (MvPolynomial.basisRestrictSupport
    (R := F) (nestedFiveCapExponents D w T YS S)).finiteDimensional_of_finite

 
theorem nestedFiveCapCoefficientBox_finrank_eq_count (D w T YS S : Nat) :
    Module.finrank F (nestedFiveCapCoefficientBox F D w T YS S) =
      nestedFiveCapCoefficientCount D w T YS S := by
  letI : Fintype (nestedFiveCapExponents D w T YS S) :=
    nestedFiveCapExponentsFintype D w T YS S
  calc
    Module.finrank F (nestedFiveCapCoefficientBox F D w T YS S) =
        Fintype.card (nestedFiveCapExponents D w T YS S) :=
      Module.finrank_eq_card_basis
        (MvPolynomial.basisRestrictSupport
          (R := F) (nestedFiveCapExponents D w T YS S))
    _ = Fintype.card (NestedFiveCapCoefficientIndex D w T YS S) :=
      Fintype.card_congr
        (nestedFiveCapCoefficientIndexEquivExponents D w T YS S).symm
    _ = nestedFiveCapCoefficientCount D w T YS S :=
      nestedFiveCapCoefficientIndex_card D w T YS S

 
theorem nestedFiveCapCoefficientBox_mono_D
    {Dlow Dhigh w T YS S : Nat} (hD : Dlow ≤ Dhigh) :
    nestedFiveCapCoefficientBox F Dlow w T YS S ≤
      nestedFiveCapCoefficientBox F Dhigh w T YS S := by
  apply MvPolynomial.restrictSupport_mono
  intro d hd
  exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.trans_le hD⟩

 

theorem nestedFiveCapCoefficientBox_mul
    {D₁ D₂ w T₁ T₂ YS₁ YS₂ S₁ S₂ : Nat}
    {P Q : MvPolynomial (Fin 4) F}
    (hP : P ∈ nestedFiveCapCoefficientBox F D₁ w T₁ YS₁ S₁)
    (hQ : Q ∈ nestedFiveCapCoefficientBox F D₂ w T₂ YS₂ S₂) :
    P * Q ∈ nestedFiveCapCoefficientBox F (D₁ + D₂ - 1) w
      (T₁ + T₂) (YS₁ + YS₂) (S₁ + S₂) := by
  have hset : nestedFiveCapExponents D₁ w T₁ YS₁ S₁ +
      nestedFiveCapExponents D₂ w T₂ YS₂ S₂ ⊆
      nestedFiveCapExponents (D₁ + D₂ - 1) w
        (T₁ + T₂) (YS₁ + YS₂) (S₁ + S₂) := by
    rintro _ ⟨d, hd, e, he, rfl⟩
    simp only [nestedFiveCapExponents, Set.mem_setOf_eq,
      Finsupp.add_apply] at hd he ⊢
    simp only [Nat.mul_add]
    omega
  apply MvPolynomial.restrictSupport_mono (R := F) hset
  rw [MvPolynomial.restrictSupport_add]
  exact Submodule.mul_mem_mul hP hQ

 
theorem nestedFiveCapChannelCount_3884_8_2 :
    nestedFiveCapChannelCount 3884 8 2 = 93133 := by
  norm_num [nestedFiveCapChannelCount, Finset.sum_range_succ]

end


end ProximityPrize.SubmissionLower.ContactNestedFiveCapCoefficientBox6750Research

#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapCoefficientBox6750Research.nestedFiveCapCoefficientIndex_card
#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapCoefficientBox6750Research.nestedFiveCapCoefficientBox_finrank_eq_count
#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapCoefficientBox6750Research.nestedFiveCapChannelCount_3884_8_2
