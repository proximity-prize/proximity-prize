import ProximityPrize.SubmissionLower.Fast054

set_option Elab.async false

/-!
Two-flag kernel bound for the K1_13_1_1 blocks (69.29 anchor, c13).

Status: standalone module, NOT imported by the Solution closure (P10 build unaffected), not built.
* O1 (flag image inside the block kernel, with the certified dimension) — proved here.
* Combination (rank + k₁ + k₂ ≤ bandCount + dim(U₁ ⊓ U₂)) — proved here.
* Intersection ≤ lcm-band image — proved here *from* two named open statements
  `LcmDivisibility` (O2) and `CofactorBand` (O3), taken as explicit hypotheses; no placeholder proofs.
-/

section PackSource_K1_13_1_1TwoFlag
set_option autoImplicit true
namespace K1_13_1_1

open K1_13 MvPolynomial
open private smallContact smallContact_order from ProximityPrize.SubmissionLower.Fast054
noncomputable section

set_option maxHeartbeats 1800000

/-- Componentwise maximum of factor powers: the lcm of two flag factors. -/
def FactorPowers.sup (v w : FactorPowers) : FactorPowers :=
  ⟨max v.value w.value, max v.jetTwo w.jetTwo, max v.quad w.quad, max v.cubic w.cubic⟩

/-- The kernel of one block, viewed inside the forms. -/
def blockKernel (s : ℕ) (g : ℤ) : Submodule Geom Form :=
  (LinearMap.ker (blockMap s g)).map (bandSpace (residualDegree s) (-g) 48 10).subtype

/-- Multiples by `flagFactor v` of the kernel of the shifted small contact map. -/
def flagImage (s : ℕ) (g : ℤ) (v : FactorPowers) : Submodule Geom Form :=
  Submodule.map (LinearMap.mulLeft Geom (flagFactor v))
    (Submodule.map
      (bandSpace (residualDegree s - v.degree) (-g - (v.minIndex : ℤ)) (48 - (v.maxIndex : ℤ))
        (10 - v.maxTop)).subtype
      (LinearMap.ker (smallContact (residualDegree s - v.degree) (-g - (v.minIndex : ℤ))
        (48 - (v.maxIndex : ℤ)) (10 - v.maxTop) (orderCutoff s g - (v.minOrder : ℤ)))))

/-- The kernel dimension certified by one flag (the quantity subtracted in `flagBound`). -/
def flagKernel (s : ℕ) (g : ℤ) (v : FactorPowers) : ℕ :=
  if v.degree ≤ residualDegree s ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10 then
    bandCount (residualDegree s - v.degree) (-g - (v.minIndex : ℤ)) (48 - (v.maxIndex : ℤ))
        (10 - v.maxTop) -
      targetCount (residualDegree s - v.degree) (-g - (v.minIndex : ℤ))
        (orderCutoff s g - (v.minOrder : ℤ))
  else 0

/-- Dimension of the band of cofactors of the lcm flag. -/
def lcmBand (s : ℕ) (g : ℤ) (v w : FactorPowers) : ℕ :=
  bandCount (residualDegree s - (v.sup w).degree) (-g - ((v.sup w).minIndex : ℤ))
    (48 - ((v.sup w).maxIndex : ℤ)) (10 - (v.sup w).maxTop)

/-- O2 (open). The four factors x₀, x₂, quad, cubic are pairwise non-associate primes, so a form
divisible by two flag factors is divisible by their lcm. -/
def LcmDivisibility : Prop :=
  ∀ (v w : FactorPowers) (P : Form),
    flagFactor v ∣ P → flagFactor w ∣ P → flagFactor (v.sup w) ∣ P

/-- O3 (open). Lowest/highest index parts and the top x₃ degree of a product are the sums of those
of the factors (no cancellation in a domain), and degrees add for homogeneous forms; hence the
cofactor of a band element by a flag factor lies in the shifted band (it is 0 when nothing fits). -/
def CofactorBand : Prop :=
  ∀ (u : FactorPowers) (h : Form) (d : ℕ) (lo hi : ℤ) (top : ℕ),
    flagFactor u * h ∈ bandSpace d lo hi top →
      h ∈ bandSpace (d - u.degree) (lo - (u.minIndex : ℤ)) (hi - (u.maxIndex : ℤ)) (top - u.maxTop)

private theorem finrank_map_injective {M N : Type*} [AddCommGroup M] [Module Geom M]
    [AddCommGroup N] [Module Geom N] (f : M →ₗ[Geom] N) (hf : Function.Injective f)
    (p : Submodule Geom M) :
    Module.finrank Geom (p.map f) = Module.finrank Geom p :=
  (Submodule.equivMapOfInjective f hf p).finrank_eq.symm

theorem finrank_blockKernel (s : ℕ) (g : ℤ) :
    Module.finrank Geom (blockKernel s g) = Module.finrank Geom (LinearMap.ker (blockMap s g)) :=
  finrank_map_injective (bandSpace (residualDegree s) (-g) 48 10).subtype
    (fun _ _ h => Subtype.ext h) (LinearMap.ker (blockMap s g))

theorem rank_add_finrank_blockKernel (s : ℕ) (g : ℤ) :
    Module.finrank Geom (LinearMap.range (blockMap s g)) + Module.finrank Geom (blockKernel s g) =
      bandCount (residualDegree s) (-g) 48 10 := by
  have hB : Module.Finite Geom (bandSpace (residualDegree s) (-g) 48 10) :=
    bandSpace_finite _ _ _ _
  rw [finrank_blockKernel, (blockMap s g).finrank_range_add_finrank_ker, finrank_bandSpace]

theorem blockKernel_finite (s : ℕ) (g : ℤ) : FiniteDimensional Geom (blockKernel s g) := by
  have hB : Module.Finite Geom (bandSpace (residualDegree s) (-g) 48 10) :=
    bandSpace_finite _ _ _ _
  unfold blockKernel
  infer_instance

private theorem small_kernel_lb (d : ℕ) (lo hi : ℤ) (top : ℕ) (order : ℤ) :
    bandCount d lo hi top - targetCount d lo order ≤
      Module.finrank Geom (LinearMap.ker (smallContact d lo hi top order)) := by
  have hW : Module.Finite Geom (bandSpace d lo hi top) := bandSpace_finite _ _ _ _
  have hT : Module.Finite Geom (targetSpace d lo order) := targetSpace_finite _ _ _
  have hsum := (smallContact d lo hi top order).finrank_range_add_finrank_ker
  have hr : Module.finrank Geom (LinearMap.range (smallContact d lo hi top order)) ≤
      targetCount d lo order :=
    (Submodule.finrank_le _).trans_eq (finrank_targetSpace _ _ _)
  rw [finrank_bandSpace] at hsum
  omega

/-- O1, dimension part. -/
theorem flagKernel_le_finrank (s : ℕ) (g : ℤ) (v : FactorPowers) :
    flagKernel s g v ≤ Module.finrank Geom (flagImage s g v) := by
  unfold flagKernel
  split_ifs with h
  · unfold flagImage
    rw [finrank_map_injective (LinearMap.mulLeft Geom (flagFactor v))
        (mul_right_injective₀ (flagFactor_ne_zero v)),
      finrank_map_injective (bandSpace (residualDegree s - v.degree) (-g - (v.minIndex : ℤ))
        (48 - (v.maxIndex : ℤ)) (10 - v.maxTop)).subtype (fun _ _ h => Subtype.ext h)]
    exact small_kernel_lb _ _ _ _ _
  · exact Nat.zero_le _

/-- O1, inclusion part: the flag image lies in the block kernel. -/
theorem flagImage_le (s : ℕ) (g : ℤ) (v : FactorPowers)
    (hv : v.degree ≤ residualDegree s ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10) :
    flagImage s g v ≤ blockKernel s g := by
  obtain ⟨h1, h2, h3⟩ := hv
  intro y hy
  unfold flagImage at hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  obtain ⟨Q, hQ, rfl⟩ := Submodule.mem_map.mp hz
  have hd : v.degree + (residualDegree s - v.degree) = residualDegree s := by omega
  have hl : (v.minIndex : ℤ) + (-g - (v.minIndex : ℤ)) = -g := by ring
  have hh : (v.maxIndex : ℤ) + (48 - (v.maxIndex : ℤ)) = 48 := by ring
  have ht : v.maxTop + (10 - v.maxTop) = 10 := by omega
  have hmem : flagFactor v * (Q : Form) ∈ bandSpace (residualDegree s) (-g) 48 10 := by
    have hm := bandSpace_mul (flagFactor_mem_band v) Q.property
    simpa only [hd, hl, hh, ht] using hm
  have hker : blockMap s g ⟨flagFactor v * (Q : Form), hmem⟩ = 0 := by
    change weightedTruncation targetOrder (orderCutoff s g).toNat
      (backShift (flagFactor v * (Q : Form))) = 0
    rw [map_mul]
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    have hcut : (orderCutoff s g).toNat ≤
        v.minOrder + (orderCutoff s g - (v.minOrder : ℤ)).toNat := by
      omega
    exact restrictWeightedOrder_anti _ hcut
      (mul_mem_restrictWeightedOrder (flagFactor_target_order v)
        (smallContact_order (d := residualDegree s - v.degree) (lo := -g - (v.minIndex : ℤ))
          (hi := 48 - (v.maxIndex : ℤ)) (top := 10 - v.maxTop)
          (order := orderCutoff s g - (v.minOrder : ℤ)) ⟨Q, hQ⟩))
  unfold blockKernel
  exact Submodule.mem_map.mpr ⟨⟨flagFactor v * (Q : Form), hmem⟩, LinearMap.mem_ker.mpr hker, rfl⟩

theorem flagImage_dvd (s : ℕ) (g : ℤ) (v : FactorPowers) {y : Form}
    (hy : y ∈ flagImage s g v) : flagFactor v ∣ y := by
  unfold flagImage at hy
  obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hy
  exact ⟨z, rfl⟩

/-- Combination of two kernel subspaces through `dim(U ⊔ V) + dim(U ⊓ V) = dim U + dim V`. -/
theorem rank_block_le_twoFlag_of_inter (s : ℕ) (g : ℤ) (v w : FactorPowers)
    (hv : v.degree ≤ residualDegree s ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10)
    (hw : w.degree ≤ residualDegree s ∧ w.maxIndex ≤ 48 ∧ w.maxTop ≤ 10) {c : ℕ}
    (hinter : Module.finrank Geom ↥(flagImage s g v ⊓ flagImage s g w) ≤ c) :
    Module.finrank Geom (LinearMap.range (blockMap s g)) + (flagKernel s g v + flagKernel s g w) ≤
      bandCount (residualDegree s) (-g) 48 10 + c := by
  have hK := blockKernel_finite s g
  have hU := flagImage_le s g v hv
  have hV := flagImage_le s g w hw
  have hUf : FiniteDimensional Geom (flagImage s g v) := Submodule.finiteDimensional_of_le hU
  have hVf : FiniteDimensional Geom (flagImage s g w) := Submodule.finiteDimensional_of_le hV
  have hsi := Submodule.finrank_sup_add_finrank_inf_eq (flagImage s g v) (flagImage s g w)
  have hsup : Module.finrank Geom ↥(flagImage s g v ⊔ flagImage s g w) ≤
      Module.finrank Geom (blockKernel s g) :=
    Submodule.finrank_le_finrank_of_le (sup_le hU hV)
  have h1 := flagKernel_le_finrank s g v
  have h2 := flagKernel_le_finrank s g w
  have hr := rank_add_finrank_blockKernel s g
  omega

/-- The intersection of two flag images consists of lcm multiples of the cofactor band. -/
theorem flagInter_le_lcm (hD : LcmDivisibility) (hC : CofactorBand) (s : ℕ) (g : ℤ)
    (v w : FactorPowers) (hv : v.degree ≤ residualDegree s ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10) :
    flagImage s g v ⊓ flagImage s g w ≤
      Submodule.map (LinearMap.mulLeft Geom (flagFactor (v.sup w)))
        (bandSpace (residualDegree s - (v.sup w).degree) (-g - ((v.sup w).minIndex : ℤ))
          (48 - ((v.sup w).maxIndex : ℤ)) (10 - (v.sup w).maxTop)) := by
  intro y hy
  obtain ⟨hyv, hyw⟩ := Submodule.mem_inf.mp hy
  have hyK : y ∈ blockKernel s g := flagImage_le s g v hv hyv
  unfold blockKernel at hyK
  obtain ⟨z, -, hz⟩ := Submodule.mem_map.mp hyK
  have hyB : y ∈ bandSpace (residualDegree s) (-g) 48 10 := by
    rw [← hz]
    exact z.property
  obtain ⟨h, rfl⟩ := hD v w y (flagImage_dvd s g v hyv) (flagImage_dvd s g w hyw)
  exact Submodule.mem_map.mpr ⟨h, hC (v.sup w) h (residualDegree s) (-g) 48 10 hyB, rfl⟩

/-- Two-flag block bound, conditional only on the named statements O2 and O3. -/
theorem rank_block_le_twoFlag (hD : LcmDivisibility) (hC : CofactorBand) (s : ℕ) (g : ℤ)
    (v w : FactorPowers)
    (hv : v.degree ≤ residualDegree s ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10)
    (hw : w.degree ≤ residualDegree s ∧ w.maxIndex ≤ 48 ∧ w.maxTop ≤ 10) :
    Module.finrank Geom (LinearMap.range (blockMap s g)) + (flagKernel s g v + flagKernel s g w) ≤
      bandCount (residualDegree s) (-g) 48 10 + lcmBand s g v w := by
  apply rank_block_le_twoFlag_of_inter s g v w hv hw
  have hL : Module.Finite Geom
      (bandSpace (residualDegree s - (v.sup w).degree) (-g - ((v.sup w).minIndex : ℤ))
        (48 - ((v.sup w).maxIndex : ℤ)) (10 - (v.sup w).maxTop)) :=
    bandSpace_finite _ _ _ _
  calc
    _ ≤ Module.finrank Geom ↥(Submodule.map (LinearMap.mulLeft Geom (flagFactor (v.sup w)))
          (bandSpace (residualDegree s - (v.sup w).degree) (-g - ((v.sup w).minIndex : ℤ))
            (48 - ((v.sup w).maxIndex : ℤ)) (10 - (v.sup w).maxTop))) :=
      Submodule.finrank_le_finrank_of_le (flagInter_le_lcm hD hC s g v w hv)
    _ ≤ Module.finrank Geom ↥(bandSpace (residualDegree s - (v.sup w).degree)
          (-g - ((v.sup w).minIndex : ℤ)) (48 - ((v.sup w).maxIndex : ℤ)) (10 - (v.sup w).maxTop)) :=
      Submodule.finrank_map_le _ _
    _ = lcmBand s g v w := finrank_bandSpace _ _ _ _

end
end K1_13_1_1
end PackSource_K1_13_1_1TwoFlag
