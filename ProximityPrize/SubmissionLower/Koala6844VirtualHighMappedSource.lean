import ProximityPrize.SubmissionLower.Koala6844VirtualHighSourceGate
import ProximityPrize.SubmissionLower.Koala6844VirtualHighSeedDerivatives
import Mathlib.FieldTheory.IsAlgClosed.Basic


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial Koala6844Normalization
open scoped BigOperators Classical

noncomputable section

set_option autoImplicit false

variable {K E I : Type} [Field K] [Field E] [IsAlgClosed E]
variable [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {excess : ℕ}

def mappedSourceDegree (d a : ℕ) : ℕ := 131071 + d - a

def mappedSourceCutoff (shape : SourceShape) (d : ℕ) : ℕ :=
  shape.ordinaryOrder * 180959 + (2 * shape.virtualOrder - shape.room) * d

private theorem sourceShape_room_le_order (shape : SourceShape)
    (hshape : shape = primary ∨ shape = roomSource ∨ shape = adaptive) :
    shape.room ≤ shape.virtualOrder := by
  rcases hshape with rfl | rfl | rfl <;> decide

private theorem cast_mappedSourceCutoff (shape : SourceShape)
    (hshape : shape = primary ∨ shape = roomSource ∨ shape = adaptive) (d : ℕ) :
    (mappedSourceCutoff shape d : ℤ) = cutoff shape d := by
  have hroom := sourceShape_room_le_order shape hshape
  unfold mappedSourceCutoff cutoff
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]
  push_cast
  rfl

private theorem centered_shape_passes (shape : SourceShape)
    (hshape : shape = primary ∨ shape = roomSource ∨ shape = adaptive) (d a : ℕ)
    (hstart : 6678 ≤ d+a) (hend : d+a ≤ 10000) :
    ∃ perContent, Passes shape d a perContent := by
  have hstart' : (6678 : ℤ) ≤ (d : ℤ)+a := by exact_mod_cast hstart
  have hend' : (d : ℤ)+a ≤ (10000 : ℤ) := by exact_mod_cast hend
  rcases hshape with rfl | rfl | rfl
  · exact ⟨377230, primary_passes (by positivity) (by positivity) hstart' hend'⟩
  · exact ⟨539504259, room_passes (by positivity) (by positivity) hstart' hend'⟩
  · exact ⟨adaptiveGap, adaptive_passes (by positivity) (by positivity) hstart' hend'⟩

theorem exists_mapped_source_and_seed_vanishing
    (D : CenteredVirtualData x nodes σ 131071 180959 81185 excess)
    (embed : K →+* E) (shape : SourceShape)
    (hshape : shape = primary ∨ shape = roomSource ∨ shape = adaptive)
    (hcard : nodes.card ≤ 262144)
    (hstart : 6678 ≤ D.d0.natDegree + affineDegree D.A0)
    (hend : D.d0.natDegree + affineDegree D.A0 ≤ 10000) :
    let cut := mappedSourceCutoff shape D.d0.natDegree
    let w' := mappedSourceDegree D.d0.natDegree (affineDegree D.A0)
    ∃ F : globalBox E cut w' shape.valueCap shape.seedCap shape.seedCap, F ≠ 0 ∧
      (∀ i ∈ nodes, MvPolynomial.finSuccEquiv E 3 F.val ∈
        ordinaryIdeal (embed (x i)) (embed (D.fixedWord i)) ^ shape.ordinaryOrder) ∧
      (MvPolynomial.finSuccEquiv E 3 F.val ∈ divisorIdeal (D.d0.map embed)
        (virtualEquation (fun j => (D.A0 j).map embed) (D.C1.map embed) 1) ^ shape.virtualOrder) ∧
      (MvPolynomial.finSuccEquiv E 3 F.val ∈ divisorIdeal (D.d1.map embed)
        (virtualEquation (fun j => ((D.A0 j).map σ.toRingHom).map embed)
          (D.D1.map embed) 2) ^ shape.virtualOrder) ∧
      ∀ (second : Bool) (r : ℕ), r ≤ shape.room → ∀ g ∈ D.seeds,
        specializeGerm ((D.normalized g).map embed) (embed g) (embed (σ g))
          (MvPolynomial.finSuccEquiv E 3
            (((MvPolynomial.pderiv (if second then 3 else 2) :
              MvPolynomial (Fin 4) E → MvPolynomial (Fin 4) E)^[r]) F.val)) = 0 := by
  let d := D.d0.natDegree
  let a := affineDegree D.A0
  let cut := mappedSourceCutoff shape d
  let w' := mappedSourceDegree d a
  let A0 (j : Fin 2) := (D.A0 j).map embed
  let A1 (j : Fin 2) := ((D.A0 j).map σ.toRingHom).map embed
  have hw : (w' : ℤ) = normalizedDegree d a := by
    have ha : a ≤ 131071 + d := by change d + a ≤ 10000 at hend; omega
    simp [w', mappedSourceDegree, Nat.cast_sub ha, normalizedDegree]
  have hcut : (cut : ℤ) = cutoff shape d := cast_mappedSourceCutoff shape hshape d
  obtain ⟨perContent, passes⟩ := centered_shape_passes shape hshape d a hstart hend
  have hcutPos : 0 < cut := by
    have ht := passes.1
    rw [← hw, ← hcut] at ht
    exact_mod_cast ((by positivity : (0 : ℤ) ≤ shape.valueCap * (w' : ℤ)).trans_lt ht)
  have e0 : specializeAffine D.A0 0 = D.A0 0 := by simp [specializeAffine]
  have hc0 := (D.coprime_denominator0 0 D.zero_mem).map (Polynomial.mapRingHom embed)
  have hc1 := (D.coprime_denominator1 0 D.zero_mem).map (Polynomial.mapRingHom embed)
  rw [e0] at hc0 hc1
  have hd0 : (D.d0.map embed).natDegree = d := Polynomial.natDegree_map _
  have hd1 : (D.d1.map embed).natDegree = d :=
    (Polynomial.natDegree_map _).trans D.degree_content
  have ep : Passes shape (D.d0.map embed).natDegree a perContent := by rwa [hd0]
  obtain ⟨F, hF, ho, hv0, hv1⟩ :=
    exists_centered_source_of_arithmetic nodes (fun i => embed (x i))
      (fun i => embed (D.fixedWord i)) (D.d0.map embed) (D.d1.map embed) A0 A1
      (D.C1.map embed) (D.D1.map embed) (IsAlgClosed.splits _) (IsAlgClosed.splits _)
      (Polynomial.map_ne_zero D.d0_ne) (Polynomial.map_ne_zero D.d1_ne) hc0 hc1
      (hd1.trans hd0.symm) hcard shape hshape cut w' a perContent
      (by rwa [hd0]) (by rwa [hd0]) ep
  refine ⟨F, hF, ho, hv0, hv1, ?_⟩
  intro second r hr
  have hrM := hr.trans (sourceShape_room_le_order shape hshape)
  have hs : 2 * shape.virtualOrder - shape.room ≤
      shape.virtualOrder + shape.virtualOrder - r := by omega
  have room : cut ≤ 180959 * shape.ordinaryOrder +
      (shape.virtualOrder + shape.virtualOrder - r) * d := by
    unfold cut mappedSourceCutoff
    rw [Nat.mul_comm shape.ordinaryOrder]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right d hs) _
  exact iterated_seed_derivative_vanishes D embed cut w' _ _ _ _ _ _ r second hcutPos
    le_rfl (by cases second <;> exact hrM) room F ho hv0 hv1

theorem exists_mapped_sourceSpace_and_seed_vanishing
    (D : CenteredVirtualData x nodes σ 131071 180959 81185 excess)
    (embed : K →+* E) (shape : SourceShape)
    (hshape : shape = primary ∨ shape = roomSource ∨ shape = adaptive)
    (hcard : nodes.card ≤ 262144)
    (hend : D.d0.natDegree + affineDegree D.A0 ≤ 10000)
    (perContent : ℤ) (passes : Passes shape D.d0.natDegree (affineDegree D.A0) perContent) :
    let cut := mappedSourceCutoff shape D.d0.natDegree
    let w' := mappedSourceDegree D.d0.natDegree (affineDegree D.A0)
    ∃ S : Submodule E (globalBox E cut w' shape.valueCap shape.seedCap shape.seedCap),
      perContent * D.d0.natDegree ≤ (Module.finrank E S : ℤ) ∧
      ∀ F ∈ S,
      (∀ i ∈ nodes, MvPolynomial.finSuccEquiv E 3 F.val ∈
        ordinaryIdeal (embed (x i)) (embed (D.fixedWord i)) ^ shape.ordinaryOrder) ∧
      (MvPolynomial.finSuccEquiv E 3 F.val ∈ divisorIdeal (D.d0.map embed)
        (virtualEquation (fun j => (D.A0 j).map embed) (D.C1.map embed) 1) ^ shape.virtualOrder) ∧
      (MvPolynomial.finSuccEquiv E 3 F.val ∈ divisorIdeal (D.d1.map embed)
        (virtualEquation (fun j => ((D.A0 j).map σ.toRingHom).map embed)
          (D.D1.map embed) 2) ^ shape.virtualOrder) ∧
      ∀ (second : Bool) (r : ℕ), r ≤ shape.room → ∀ g ∈ D.seeds,
        specializeGerm ((D.normalized g).map embed) (embed g) (embed (σ g))
          (MvPolynomial.finSuccEquiv E 3
            (((MvPolynomial.pderiv (if second then 3 else 2) :
              MvPolynomial (Fin 4) E → MvPolynomial (Fin 4) E)^[r]) F.val)) = 0 := by
  let d := D.d0.natDegree
  let a := affineDegree D.A0
  let cut := mappedSourceCutoff shape d
  let w' := mappedSourceDegree d a
  let A0 (j : Fin 2) := (D.A0 j).map embed
  let A1 (j : Fin 2) := ((D.A0 j).map σ.toRingHom).map embed
  have hw : (w' : ℤ) = normalizedDegree d a := by
    have ha : a ≤ 131071 + d := by change d + a ≤ 10000 at hend; omega
    simp [w', mappedSourceDegree, Nat.cast_sub ha, normalizedDegree]
  have hcut : (cut : ℤ) = cutoff shape d := cast_mappedSourceCutoff shape hshape d
  have hcutPos : 0 < cut := by
    have ht := passes.1
    rw [← hw, ← hcut] at ht
    exact_mod_cast ((by positivity : (0 : ℤ) ≤ shape.valueCap * (w' : ℤ)).trans_lt ht)
  have e0 : specializeAffine D.A0 0 = D.A0 0 := by simp [specializeAffine]
  have hc0 := (D.coprime_denominator0 0 D.zero_mem).map (Polynomial.mapRingHom embed)
  have hc1 := (D.coprime_denominator1 0 D.zero_mem).map (Polynomial.mapRingHom embed)
  rw [e0] at hc0 hc1
  have hd0 : (D.d0.map embed).natDegree = d := Polynomial.natDegree_map _
  have hd1 : (D.d1.map embed).natDegree = d :=
    (Polynomial.natDegree_map _).trans D.degree_content
  have ep : Passes shape (D.d0.map embed).natDegree a perContent := by rwa [hd0]
  obtain ⟨S, hRank, hContacts⟩ :=
    exists_centered_sourceSpace_of_arithmetic nodes (fun i => embed (x i))
      (fun i => embed (D.fixedWord i)) (D.d0.map embed) (D.d1.map embed) A0 A1
      (D.C1.map embed) (D.D1.map embed) (IsAlgClosed.splits _) (IsAlgClosed.splits _)
      (Polynomial.map_ne_zero D.d0_ne) (Polynomial.map_ne_zero D.d1_ne) hc0 hc1
      (hd1.trans hd0.symm) hcard shape hshape cut w' a perContent
      (by rwa [hd0]) (by rwa [hd0]) ep
  rw [hd0] at hRank
  refine ⟨S, hRank, ?_⟩
  intro F hF
  obtain ⟨ho, hv0, hv1⟩ := hContacts F hF
  refine ⟨ho, hv0, hv1, ?_⟩
  intro second r hr
  have hrM := hr.trans (sourceShape_room_le_order shape hshape)
  have hs : 2 * shape.virtualOrder - shape.room ≤
      shape.virtualOrder + shape.virtualOrder - r := by omega
  have room : cut ≤ 180959 * shape.ordinaryOrder +
      (shape.virtualOrder + shape.virtualOrder - r) * d := by
    unfold cut mappedSourceCutoff
    rw [Nat.mul_comm shape.ordinaryOrder]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right d hs) _
  exact iterated_seed_derivative_vanishes D embed cut w' _ _ _ _ _ _ r second hcutPos
    le_rfl (by cases second <;> exact hrM) room F ho hv0 hv1

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
