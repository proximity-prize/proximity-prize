import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSeedlessRankResearch
import ProximityPrize.SubmissionLower.ContactFlagTranslation6641Research
import ProximityPrize.SubmissionLower.ContactTranslation

/-!
# Contact interpolation for one fixed received word

This is the seed-free analogue of the affine-line interpolant.  Global
variables are still `(X,Y,R,Z)` so the existing factor and specialization
machinery can consume the result, but every reconstructed monomial has
`Z`-degree zero.  Locally the constraint map therefore lands in the
two-dimensional contact blocks proved in `ContactSeedlessRankResearch`.
-/

namespace ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch

open scoped BigOperators
open ProximityPrize.Benchmark
open ContactSeedlessRankResearch
open ContactFlagRankKernel6641Research

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable (K : Type*) [Field K]

abbrev LocalPoly := MvPolynomial (Fin 3) K
abbrev Poly4 := MvPolynomial (Fin 4) K

/-- The dummy `Fin (min 1 ...)` records the triangular `Y+R` support
without adding a seed exponent. -/
abbrev CoefficientIndex (D w L s : ℕ) :=
  (i : Fin (L + 1)) × (j : Fin (s + 1)) ×
    (Fin (min 1 (L + 1 - i.val - j.val)) ×
      Fin (D - w * i.val - (w - 1) * j.val))

def columnExponent {D w L s : ℕ}
    (c : CoefficientIndex D w L s) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 c.2.2.2.val + Finsupp.single 1 c.1.val +
    Finsupp.single 2 c.2.1.val

@[simp] theorem columnExponent_x {D w L s : ℕ}
    (c : CoefficientIndex D w L s) : columnExponent c 0 = c.2.2.2.val := by
  simp [columnExponent]

@[simp] theorem columnExponent_y {D w L s : ℕ}
    (c : CoefficientIndex D w L s) : columnExponent c 1 = c.1.val := by
  simp [columnExponent]

@[simp] theorem columnExponent_r {D w L s : ℕ}
    (c : CoefficientIndex D w L s) : columnExponent c 2 = c.2.1.val := by
  simp [columnExponent]

@[simp] theorem columnExponent_z {D w L s : ℕ}
    (c : CoefficientIndex D w L s) : columnExponent c 3 = 0 := by
  simp [columnExponent]

theorem columnExponent_injective (D w L s : ℕ) :
    Function.Injective
      (columnExponent (D := D) (w := w) (L := L) (s := s)) := by
  intro c d h
  have hx := congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
  have hy := congrArg (fun e : Fin 4 →₀ ℕ => e 1) h
  have hr := congrArg (fun e : Fin 4 →₀ ℕ => e 2) h
  rcases c with ⟨⟨ci, hci⟩, ⟨⟨cj, hcj⟩, ⟨⟨cz, hcz⟩, ⟨ce, hce⟩⟩⟩⟩
  rcases d with ⟨⟨di, hdi⟩, ⟨⟨dj, hdj⟩, ⟨⟨dz, hdz⟩, ⟨de, hde⟩⟩⟩⟩
  simp only [columnExponent_x] at hx
  simp only [columnExponent_y] at hy
  simp only [columnExponent_r] at hr
  subst di
  subst dj
  subst de
  have hcz0 : cz = 0 := by omega
  have hdz0 : dz = 0 := by omega
  subst cz
  subst dz
  rfl

def globalExponents (D w L s : ℕ) : Set (Fin 4 →₀ ℕ) :=
  {d | d 1 + d 2 ≤ L ∧ d 2 ≤ s ∧ d 3 = 0 ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D}

def globalCoefficientBox (D w L s : ℕ) : Submodule K (Poly4 K) :=
  MvPolynomial.restrictSupport K (globalExponents D w L s)

theorem columnMonomial_mem (D w L s : ℕ)
    (c : CoefficientIndex D w L s) (a : K) :
    MvPolynomial.monomial (columnExponent c) a ∈
      globalCoefficientBox K D w L s := by
  apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
  left
  have hi := c.1.isLt
  have hj := c.2.1.isLt
  have ht := c.2.2.1.isLt
  have he := c.2.2.2.isLt
  have htri : c.1.val + c.2.1.val ≤ L := by
    have hminpos : 0 < min 1 (L + 1 - c.1.val - c.2.1.val) := by
      omega
    have hpos : 0 < L + 1 - c.1.val - c.2.1.val :=
      hminpos.trans_le (min_le_right _ _)
    omega
  unfold globalExponents
  simp only [Set.mem_setOf_eq, columnExponent_x, columnExponent_y,
    columnExponent_r, columnExponent_z]
  exact ⟨htri, by omega, by simp, by omega⟩

def reconstruct (D w L s : ℕ) (theta : CoefficientIndex D w L s → K) :
    Poly4 K :=
  ∑ c : CoefficientIndex D w L s,
    MvPolynomial.monomial (columnExponent c) (theta c)

theorem reconstruct_coeff (D w L s : ℕ)
    (theta : CoefficientIndex D w L s → K) (c : CoefficientIndex D w L s) :
    MvPolynomial.coeff (columnExponent c) (reconstruct K D w L s theta) =
      theta c := by
  classical
  simp [reconstruct, MvPolynomial.coeff_sum,
    columnExponent_injective D w L s]

theorem reconstruct_mem_box (D w L s : ℕ)
    (theta : CoefficientIndex D w L s → K) :
    reconstruct K D w L s theta ∈ globalCoefficientBox K D w L s := by
  unfold reconstruct
  apply Submodule.sum_mem
  intro c hc
  exact columnMonomial_mem K D w L s c (theta c)

theorem reconstruct_ne_zero (D w L s : ℕ)
    (theta : CoefficientIndex D w L s → K) (htheta : theta ≠ 0) :
    reconstruct K D w L s theta ≠ 0 := by
  intro hrec
  have hall : ∀ c, theta c = 0 := by
    intro c
    rw [← reconstruct_coeff K D w L s theta c, hrec]
    simp
  exact htheta (funext hall)

def coefficientCount (D w L s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (L + 1),
    ∑ j ∈ Finset.range (s + 1),
      min 1 (L + 1 - i - j) * (D - w * i - (w - 1) * j)

theorem coefficient_index_card (D w L s : ℕ) :
    Fintype.card (CoefficientIndex D w L s) = coefficientCount D w L s := by
  simp [CoefficientIndex, coefficientCount, Fintype.card_sigma,
    Finset.sum_range]

def localMonomial (f j : ℕ) : LocalPoly K :=
  MvPolynomial.monomial (Finsupp.single 0 f + Finsupp.single 1 j) 1

theorem localMonomial_mem (f j : ℕ) :
    localMonomial K f j ∈ seedlessBox K f (f + j) j := by
  apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
  left
  simp [seedlessExponents]

/-- Single block entry at local index `r`, with `Z=0` hard-coded. -/
def blockEntry (D w L s : ℕ) (x u : K)
    (c : CoefficientIndex D w L s) (r : ℕ) : LocalPoly K :=
  if r ≤ c.1.val then
    (((c.1.val.choose r : ℕ) : K) *
      ((c.1.val - r).factorial : K)⁻¹ *
      (x ^ (c.1.val - r))) •
        localMonomial K r c.2.1.val
  else 0

theorem blockEntry_mem (D w L s : ℕ) (x u : K)
    (c : CoefficientIndex D w L s) (r : ℕ) :
    blockEntry K D w L s x u c r ∈ seedlessBox K (min r L) L s := by
  classical
  unfold blockEntry
  split_ifs with hr
  · have hf : localMonomial K r c.2.1.val ∈
        seedlessBox K r (r + c.2.1.val) c.2.1.val :=
      localMonomial_mem K r c.2.1.val
    have hmin : r = min r L := by
      have ht : c.1.val ≤ L := c.1.isLt.le
      omega
    have hL : r + c.2.1.val ≤ L := by
      have hminpos : 0 < min 1 (L + 1 - c.1.val - c.2.1.val) := c.2.2.1.isLt
      have hpos : 0 < L + 1 - c.1.val - c.2.1.val :=
        hminpos.trans_le (min_le_right _ _)
      omega
    have hs : c.2.1.val ≤ s := c.2.1.isLt.le
    have hsub : seedlessBox K r (r + c.2.1.val) c.2.1.val ≤
        seedlessBox K (min r L) L s := by
      apply MvPolynomial.restrictSupport_mono
      intro d hd
      rcases hd with ⟨hd0, hd01, hd1, hd2⟩
      exact ⟨by rw [← hmin]; exact hd0, hd01.trans hL, hd1.trans hs, hd2⟩
    exact hsub ((seedlessBox K r (r + c.2.1.val) c.2.1.val).smul_mem _ hf)
  · exact (seedlessBox K (min r L) L s).zero_mem

def blockEntryMap (D w L s : ℕ) (x u : K) (r : ℕ) :
    (CoefficientIndex D w L s → K) →ₗ[K] Poly K :=
  ∑ c : CoefficientIndex D w L s,
    (LinearMap.proj c).smulRight (blockEntry K D w L s x u c r)

theorem blockEntryMap_mem (D w L s : ℕ) (x u : K) (r : ℕ)
    (theta : CoefficientIndex D w L s → K) :
    blockEntryMap K D w L s x u r theta ∈ seedlessBox K (min r L) L s := by
  unfold blockEntryMap
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]
  apply Submodule.sum_mem
  intro c hc
  exact Submodule.smul_mem _ _ (blockEntry_mem K D w L s x u c r)

def nodeBlockTarget (m L s : ℕ) : Type _ :=
  (r : Fin m) → seedlessTarget K (min r.val L) L s (min (r.val + 1) (m - r.val))

def nodeTargetMap (D w L s m : ℕ) (x u : K) :
    (CoefficientIndex D w L s → K) →ₗ[K] nodeBlockTarget K m L s where
  toFun theta r :=
    seedlessBlockJet K (min r.val L) L s (min (r.val + 1) (m - r.val))
      ⟨blockEntryMap K D w L s x u r.val theta,
        blockEntryMap_mem K D w L s x u r.val theta⟩
  map_add' theta1 theta2 := by
    ext r
    simp only [map_add, Submodule.coe_add]
  map_smul' c theta := by
    ext r
    simp only [map_smul, Submodule.coe_smul, RingHom.id_apply]

theorem nodeTarget_finrank_le (m L s : ℕ) :
    Module.finrank K (nodeBlockTarget K m L s) ≤
      localRankBound m L s := by
  have hprod := Module.finrank_pi (ι := Fin m)
    (M := fun r => seedlessTarget K (min r.val L) L s
      (min (r.val + 1) (m - r.val)))
  rw [hprod]
  unfold localRankBound
  rw [← Finset.sum_fin_eq_sum_range]
  apply Finset.sum_le_sum
  intro r hr
  exact seedlessBlockJet_rank_le_contactRankBound K (min r.val L) L s
    (min (r.val + 1) (m - r.val)) (min_le_right _ _)

def totalTargetMap (D w L s m : ℕ)
    (domain : IRSProfile.Index → K) (received : IRSProfile.Index → K) :
    (CoefficientIndex D w L s → K) →ₗ[K]
      (IRSProfile.Index → nodeBlockTarget K m L s) :=
  LinearMap.pi (fun i => nodeTargetMap K D w L s m (domain i) (received i))

theorem totalTarget_finrank_le (D w L s m : ℕ)
    (domain received : IRSProfile.Index → K) :
    Module.finrank K (LinearMap.range
      (totalTargetMap K D w L s m domain received)) ≤
      Fintype.card IRSProfile.Index * localRankBound m L s := by
  have hpi : Module.finrank K
      (IRSProfile.Index → nodeBlockTarget K m L s) =
      Fintype.card IRSProfile.Index *
        Module.finrank K (nodeBlockTarget K m L s) := by
      exact Module.finrank_pi (M := fun _ => nodeBlockTarget K m L s)
    have hle := Submodule.finrank_le
      (LinearMap.range (totalTargetMap K D w L s m domain received))
    rw [hpi] at hle
    exact hle.trans (Nat.mul_le_mul_left _ (nodeTarget_finrank_le K m L s))

theorem exists_nonzero_kernel_array (D w L s m : ℕ)
    (domain received : IRSProfile.Index → K)
    (hgate : Fintype.card IRSProfile.Index * localRankBound m L s <
      coefficientCount D w L s) :
    ∃ theta : CoefficientIndex D w L s → K,
      theta ≠ 0 ∧
      totalTargetMap K D w L s m domain received theta = 0 := by
  have hdim : Module.finrank K (LinearMap.range
      (totalTargetMap K D w L s m domain received)) <
      Module.finrank K (CoefficientIndex D w L s → K) := by
    rw [Module.finrank_fintype_fun, coefficient_index_card]
    exact (totalTarget_finrank_le K D w L s m domain received).trans_lt hgate
  have hker := LinearMap.finrank_ker_pos_of_finrank_range_lt
    (totalTargetMap K D w L s m domain received) hdim
  have hpos : 0 < Module.finrank K
      (LinearMap.ker (totalTargetMap K D w L s m domain received)) := by
    exact Submodule.bot_lt_iff_ne_bot.mp (by
      intro hbot
      rw [hbot, Module.finrank_bot] at hker
      exact Nat.lt_irrefl 0 hker)
  obtain ⟨⟨theta, htheta⟩, hne⟩ :=
    Module.exists_ne_zero_of_finrank_pos hpos
  refine ⟨theta, ?_, LinearMap.mem_ker.mp htheta⟩
  intro hzero
  subst hzero
  exact hne rfl

theorem translation_reconstruct_coeff (D w L s : ℕ) (x u : K)
    (theta : CoefficientIndex D w L s → K) (r : ℕ) :
    (ContactTranslation.homogenizedTranslation K x u 0
      (reconstruct K D w L s theta)).coeff r =
      blockEntryMap K D w L s x u r theta := by
  ext d
  simp [reconstruct, ContactTranslation.homogenizedTranslation,
    blockEntryMap, blockEntry, localMonomial, seedlessExponents]

theorem all_blocks_divisible_of_kernel (D w L s m : ℕ)
    (domain received : IRSProfile.Index → K)
    (theta : CoefficientIndex D w L s → K)
    (hzero : totalTargetMap K D w L s m domain received theta = 0)
    (i : IRSProfile.Index) (r : ℕ) :
    slopeDifference K ^ (m - r) ∣
      (blockEntryMap K D w L s (domain i) (received i) r theta) := by
  by_cases hr : r < m
  · have hnode := congrFun (congrFun hzero i) ⟨r, hr⟩
    exact seedlessBlockJet_eq_zero_iff.mp hnode
  · have hpow : m - r = 0 := by omega
    rw [hpow, pow_zero]
    exact one_dvd _

def n : ℕ := 262144
def errors : ℕ := 80066
def agreements : ℕ := n - errors
def w : ℕ := 131071
def multiplicity : ℕ := 50
def yTotalCap : ℕ := 68
def slopeCap : ℕ := 14
def weightedCap : ℕ := multiplicity * agreements

theorem parameter_values :
    agreements = 182078 ∧ weightedCap = 9103900 := by
  norm_num [agreements, weightedCap, multiplicity, n, errors]

theorem coefficient_count_exact :
    coefficientCount weightedCap w yTotalCap slopeCap = 3913882045 := by
  decide

theorem local_rank_exact :
    localRankBound multiplicity yTotalCap slopeCap = 14890 := by
  decide

theorem nullity_exact :
    coefficientCount weightedCap w yTotalCap slopeCap -
      n * localRankBound multiplicity yTotalCap slopeCap = 3913882045 - n * 14890 := by
  rw [coefficient_count_exact, local_rank_exact]

theorem interpolation_gate :
    n * localRankBound multiplicity yTotalCap slopeCap <
      coefficientCount weightedCap w yTotalCap slopeCap := by
  rw [coefficient_count_exact, local_rank_exact]
  decide

theorem exists_frozen_seedless_interpolant
    (received : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w yTotalCap slopeCap ∧
      ∀ (i : IRSProfile.Index) (r : ℕ),
        slopeDifference IRSProfile.Field ^ (multiplicity - r) ∣
          (ContactTranslation.homogenizedTranslation IRSProfile.Field
            (IRSProfile.domain i) (received i) 0 Q).coeff r := by
  obtain ⟨theta, htheta, hzero⟩ := exists_nonzero_kernel_array
    IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
    IRSProfile.domain received (by
      rw [show Fintype.card IRSProfile.Index = n by
        norm_num [IRSProfile.Index, n]]
      exact interpolation_gate)
  refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
    reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
    reconstruct_mem_box IRSProfile.Field _ _ _ _ theta, ?_⟩
  intro i r
  have hdiv := all_blocks_divisible_of_kernel IRSProfile.Field
    weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received
    theta hzero i r
  rw [← translation_reconstruct_coeff IRSProfile.Field weightedCap w
    yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
  exact hdiv

theorem seedlessBox_le_legacy :
    globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ≤
      ContactInterpolation.globalCoefficientBox IRSProfile.Field
        weightedCap w yTotalCap slopeCap := by
  apply MvPolynomial.restrictSupport_mono
  intro d hd
  rcases hd with ⟨hYR, hR, hZ, hweighted⟩
  exact ⟨by omega, hR, hweighted⟩

/-- Every degree-`w` polynomial agreeing with the fixed received word on
`agreements` coordinates is a genuine root of the seedless interpolant. -/
theorem exists_frozen_seedless_vanishing_interpolant
    (received : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w yTotalCap slopeCap ∧
      Q ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        weightedCap w yTotalCap slopeCap ∧
      ∀ (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support, P.eval (IRSProfile.domain i) = received i) →
        ContactTranslation.specialization IRSProfile.Field P 0 Q = 0 := by
  classical
  obtain ⟨Q, hQ, hbox, hcontact⟩ :=
    exists_frozen_seedless_interpolant received
  have hlegacy := seedlessBox_le_legacy hbox
  refine ⟨Q, hQ, hbox, hlegacy, ?_⟩
  intro P support hdegree hcard hvalues
  apply ContactTranslation.specialization_eq_zero_of_contact_and_degree
    IRSProfile.Field Q P 0 IRSProfile.domain received (fun _ => 0)
      support multiplicity
  · intro i hi r
    exact hcontact i r
  · intro i hi
    simpa only [mul_zero, add_zero] using hvalues i hi
  · have hdeg := ContactTranslation.specialization_natDegree_lt
      IRSProfile.Field weightedCap w yTotalCap slopeCap Q P 0
      (by norm_num [weightedCap, multiplicity, agreements, n, errors])
      hlegacy hdegree
    have hbound : weightedCap ≤ multiplicity * support.card := by
      rw [weightedCap]
      exact Nat.mul_le_mul_left multiplicity hcard
    exact hdeg.trans_le hbound

end

end ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch
