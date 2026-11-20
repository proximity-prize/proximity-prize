import ProximityPrize.SubmissionLower.Koala6844VirtualHighMappedSource
import ProximityPrize.SubmissionLower.Koala6844VirtualHighSurfaceSource
import Mathlib.FieldTheory.AlgebraicClosure


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial ProximityPrize.Benchmark Koala6844Normalization Koala6844BivariateSeeds RCN132
open scoped Classical

noncomputable section

set_option autoImplicit false

abbrev BenchmarkVirtualField := AlgebraicClosure IRSProfile.Field
abbrev BenchmarkVirtualCarrier := MvPolynomial (Fin 4) BenchmarkVirtualField
abbrev BenchmarkVirtualFraction := RationalCoefficients BenchmarkVirtualField

def benchmarkVirtualEmbedding : IRSProfile.Field →+* BenchmarkVirtualField :=
  algebraMap _ _

def benchmarkVirtualSeed : IRSProfile.Field →+* BenchmarkVirtualFraction :=
  (algebraMap (Polynomial BenchmarkVirtualField) BenchmarkVirtualFraction).comp
    (Polynomial.C.comp benchmarkVirtualEmbedding)

theorem benchmarkVirtualCharacteristic : CharP BenchmarkVirtualField 2130706433 := by
  letI := Koala6844BenchmarkField.characteristic
  exact charP_of_injective_ringHom benchmarkVirtualEmbedding.injective 2130706433


abbrev BenchmarkVirtualFamily (nodes : Finset IRSProfile.Index) (excess : ℕ) :=
  CenteredVirtualData IRSProfile.domain nodes Koala6844BenchmarkField.frobenius 131071 180959 81185 excess

variable {nodes : Finset IRSProfile.Index} {excess : ℕ}

def benchmarkSurfaceValue (D : BenchmarkVirtualFamily nodes excess) (g : IRSProfile.Field) :
    BenchmarkVirtualFraction :=
  fractionValue ((D.normalized g).map benchmarkVirtualEmbedding)

def benchmarkSurfacePoint (D : BenchmarkVirtualFamily nodes excess) (g : IRSProfile.Field) :
    Fin 3 → BenchmarkVirtualFraction :=
  Fin.cases (benchmarkSurfaceValue D g)
    (coordinates (benchmarkVirtualSeed g) ((benchmarkVirtualSeed g)^2130706433))

theorem benchmarkSurfaceValue_injOn (D : BenchmarkVirtualFamily nodes excess) :
    Set.InjOn (benchmarkSurfaceValue D) (↑D.seeds : Set IRSProfile.Field) :=
  mapped_normalized_fraction_injOn D benchmarkVirtualEmbedding

def benchmarkSeedDerivative (second : Bool) (k : ℕ) (F : BenchmarkVirtualCarrier) :
    BenchmarkVirtualCarrier :=
  ((MvPolynomial.pderiv (if second then 3 else 2) :
    BenchmarkVirtualCarrier → BenchmarkVirtualCarrier)^[k]) F

def benchmarkVirtualBox (D : BenchmarkVirtualFamily nodes excess) (shape : SourceShape) :
    Submodule BenchmarkVirtualField BenchmarkVirtualCarrier :=
  globalBox BenchmarkVirtualField (mappedSourceCutoff shape D.d0.natDegree)
    (mappedSourceDegree D.d0.natDegree (affineDegree D.A0))
    shape.valueCap shape.seedCap shape.seedCap

def benchmarkAdaptiveBoxAt (D : BenchmarkVirtualFamily nodes excess) (j : ℕ) :
    Submodule BenchmarkVirtualField BenchmarkVirtualCarrier :=
  globalBox BenchmarkVirtualField (mappedSourceCutoff adaptive D.d0.natDegree - j * D.d0.natDegree)
    (mappedSourceDegree D.d0.natDegree (affineDegree D.A0)) 6975 133094 133094

def benchmarkSourceVanishes (D : BenchmarkVirtualFamily nodes excess) (F : BenchmarkVirtualCarrier) :
    Prop :=
  ∀ g ∈ D.seeds, MvPolynomial.eval (benchmarkSurfacePoint D g)
    (rationalSurfaceMap BenchmarkVirtualField F) = 0

private theorem benchmarkFrobenius_map (g : IRSProfile.Field) :
    benchmarkVirtualEmbedding (Koala6844BenchmarkField.frobenius g) =
      (benchmarkVirtualEmbedding g)^2130706433 := by
  rw [Koala6844BenchmarkField.frobenius_apply, map_pow]

private theorem benchmarkVanishes_of_specialize (D : BenchmarkVirtualFamily nodes excess)
    (F : BenchmarkVirtualCarrier)
    (h : ∀ g ∈ D.seeds, specializeGerm ((D.normalized g).map benchmarkVirtualEmbedding)
      (benchmarkVirtualEmbedding g) (benchmarkVirtualEmbedding (Koala6844BenchmarkField.frobenius g))
      (MvPolynomial.finSuccEquiv BenchmarkVirtualField 3 F) = 0) :
    benchmarkSourceVanishes D F :=
  eval_mapped_centered_surface_eq_zero D benchmarkVirtualEmbedding 2130706433
    (fun g _ => benchmarkFrobenius_map g) F h

private theorem benchmarkContent_pos (D : BenchmarkVirtualFamily nodes excess) :
    0 < D.d0.natDegree := by
  by_contra! h
  have hdeg : D.d1.degree = 0 := by
    rw [Polynomial.degree_eq_natDegree D.d1_ne, D.degree_content, Nat.eq_zero_of_le_zero h]
    rfl
  exact D.active ((Polynomial.isUnit_iff_degree_eq_zero.mpr hdeg).dvd)

private theorem adaptive_cutoff_sub (d j : ℕ) (hj : j ≤ 6975) :
    mappedSourceCutoff adaptive d - j*d = 180959*4800+(6912+6912-j)*d := by
  change 4800*180959+ (2*6912-0)*d - j*d = _
  have h : j*d ≤ (2*6912-0)*d := Nat.mul_le_mul_right d (by omega)
  rw [Nat.add_sub_assoc h, ← Nat.sub_mul]

structure BenchmarkVirtualSources (D : BenchmarkVirtualFamily nodes excess) where
  content_pos : 0 < D.d0.natDegree
  support_le : D.d0.natDegree + affineDegree D.A0 ≤ 10000
  primarySource : benchmarkVirtualBox D primary
  primary_ne : primarySource ≠ 0
  primary_vanishes : benchmarkSourceVanishes D primarySource.val
  roomSource : benchmarkVirtualBox D Koala6844VirtualHigh.roomSource
  room_ne : roomSource ≠ 0
  room_vanishes : ∀ (second : Bool) (k : ℕ), k ≤ 31 →
    benchmarkSourceVanishes D (benchmarkSeedDerivative second k roomSource.val)
  adaptiveSpace : Submodule BenchmarkVirtualField (benchmarkVirtualBox D adaptive)
  adaptive_dim : D.d0.natDegree * adaptiveGap ≤ Module.finrank BenchmarkVirtualField adaptiveSpace
  adaptive_vanishes : ∀ (v : adaptiveSpace) (j : ℕ), j ≤ 6975 →
    v.val.val ∈ benchmarkAdaptiveBoxAt D j →
    ∀ (second : Bool) (k : ℕ), k ≤ j →
      benchmarkSourceVanishes D (benchmarkSeedDerivative second k v.val.val)

def BenchmarkVirtualSources.adaptiveMap {D : BenchmarkVirtualFamily nodes excess}
    (source : BenchmarkVirtualSources D) : source.adaptiveSpace →ₗ[BenchmarkVirtualField] BenchmarkVirtualCarrier :=
  (benchmarkVirtualBox D adaptive).subtype.comp source.adaptiveSpace.subtype

theorem BenchmarkVirtualSources.adaptiveMap_injective {D : BenchmarkVirtualFamily nodes excess}
    (source : BenchmarkVirtualSources D) :
    Function.Injective source.adaptiveMap :=
  (benchmarkVirtualBox D adaptive).subtype_injective.comp source.adaptiveSpace.subtype_injective

theorem BenchmarkVirtualSources.adaptiveMap_mem {D : BenchmarkVirtualFamily nodes excess}
    (source : BenchmarkVirtualSources D) (v : source.adaptiveSpace) :
    source.adaptiveMap v ∈ benchmarkVirtualBox D adaptive :=
  v.val.property

theorem exists_benchmark_virtual_sources
    (D : BenchmarkVirtualFamily nodes excess) (hexcess : excess ≤ 9799)
    (hstart : 6678 ≤ D.d0.natDegree + affineDegree D.A0) :
    Nonempty (BenchmarkVirtualSources D) := by
  have hend : D.d0.natDegree + affineDegree D.A0 ≤ 10000 :=
    D.support_le.trans (hexcess.trans (by decide))
  have hcard : nodes.card ≤ 262144 := by
    have h := Finset.card_le_univ nodes
    rwa [IRSProfile.card_index] at h
  obtain ⟨P, hP, _, _, _, hPV⟩ :=
    exists_mapped_source_and_seed_vanishing D benchmarkVirtualEmbedding primary
      (Or.inl rfl) hcard hstart hend
  obtain ⟨R, hR, _, _, _, hRV⟩ :=
    exists_mapped_source_and_seed_vanishing D benchmarkVirtualEmbedding Koala6844VirtualHigh.roomSource
      (Or.inr (Or.inl rfl)) hcard hstart hend
  let d := D.d0.natDegree
  have hstart' : (6678 : ℤ) ≤ (d : ℤ) + affineDegree D.A0 := by exact_mod_cast hstart
  have hend' : (d : ℤ) + affineDegree D.A0 ≤ 10000 := by exact_mod_cast hend
  have hpasses := adaptive_passes (d := (d : ℤ)) (a := (affineDegree D.A0 : ℤ))
    (by positivity) (by positivity) hstart' hend'
  obtain ⟨S, hS, hcontact⟩ := exists_mapped_sourceSpace_and_seed_vanishing
    D benchmarkVirtualEmbedding adaptive (Or.inr (Or.inr rfl)) hcard hend (adaptiveGap : ℤ) hpasses
  have hRank : D.d0.natDegree * adaptiveGap ≤ Module.finrank BenchmarkVirtualField S := by
    have h : (D.d0.natDegree : ℤ) * (adaptiveGap : ℤ) ≤ Module.finrank BenchmarkVirtualField S := by
      simpa only [mul_comm] using hS
    exact_mod_cast h
  refine ⟨{
    content_pos := benchmarkContent_pos D
    support_le := hend
    primarySource := P
    primary_ne := hP
    primary_vanishes := benchmarkVanishes_of_specialize D P.val (hPV false 0 (by decide))
    roomSource := R
    room_ne := hR
    room_vanishes := fun second k hk =>
      benchmarkVanishes_of_specialize D _ (hRV second k hk)
    adaptiveSpace := S
    adaptive_dim := hRank
    adaptive_vanishes := ?_ }⟩
  intro v j hj hjBox second k hk
  obtain ⟨ho, h0, h1, _⟩ := hcontact v.val v.property
  let cut := mappedSourceCutoff adaptive d - j*d
  let Q : benchmarkAdaptiveBoxAt D j := ⟨v.val.val, hjBox⟩
  have he := adaptive_cutoff_sub d j hj
  have hpos : 0 < cut := by
    change 0 < mappedSourceCutoff adaptive d - j*d
    rw [he]
    positivity
  have hroom : cut ≤ 180959*4800+(6912+6912-k)*d := by
    change mappedSourceCutoff adaptive d - j*d ≤ _
    rw [he]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hk _)) _
  apply benchmarkVanishes_of_specialize D
  exact iterated_seed_derivative_vanishes_at_cutoff D benchmarkVirtualEmbedding
    cut (mappedSourceDegree d (affineDegree D.A0)) 6975 133094 133094
    4800 6912 6912 k second hpos le_rfl hroom Q ho h0 h1

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
