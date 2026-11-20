import ProximityPrize.SubmissionLower.Koala6844VirtualShortSeedlessRank


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetRelaxedRank

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2500000

abbrev SeedlessRectangle (width height total : ℕ) :=
  {ij : Fin width × Fin height // ij.1.val + ij.2.val ≤ total}

private abbrev SourceCell (B U t h : ℕ) :=
  {ij : Fin (t + 1) × Fin (B - 2*h + 1) // h + ij.1.val + ij.2.val ≤ U}

private def sourceCellEquiv (B U t h : ℕ) (hh : h ≤ U) :
    SourceCell B U t h ≃ SeedlessRectangle (t+1) (B-2*h+1) (U-h) where
  toFun ij := ⟨ij.val,by have := ij.property; omega⟩
  invFun ij := ⟨ij.val,by have := ij.property; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def toCells (m B s U : ℕ) (i : SeedlessIndex m B s U) :
    Σ t : Fin m, Σ h : Fin (s+1), SourceCell B U t.val h.val := by
  let d := SecondJetRelaxedSpace.exponent i.val
  have hm := (SecondJetRelaxedSpace.mem_range_exponent m U B s U (fun _ => U) d).mp ⟨i.val,rfl⟩
  have ht : d 0 < m := hm.1.1
  have hi : d 2 < d 0 + 1 := Nat.lt_succ_of_le hm.1.2.1
  have hh : d 1 < s + 1 := Nat.lt_succ_of_le hm.1.2.2.2.1
  have hB : 2*d 1+d 3 ≤ B := hm.2.1
  have hj : d 3 < B-2*d 1+1 := by omega
  exact ⟨⟨d 0,ht⟩,⟨d 1,hh⟩,⟨⟨⟨d 2,hi⟩,⟨d 3,hj⟩⟩,hm.2.2.1⟩⟩

private theorem toCells_injective (m B s U : ℕ) :
    Function.Injective (toCells m B s U) := by
  intro i j hij
  apply Subtype.ext
  apply SecondJetRelaxedSpace.exponent_injective m U B s U (fun _ => U)
  ext k
  fin_cases k
  · change SecondJetRelaxedSpace.exponent i.val 0 = SecondJetRelaxedSpace.exponent j.val 0
    simpa only [toCells] using congrArg (fun c : Σ t : Fin m, Σ h : Fin (s+1), SourceCell B U t.val h.val => c.1.val) hij
  · change SecondJetRelaxedSpace.exponent i.val 1 = SecondJetRelaxedSpace.exponent j.val 1
    simpa only [toCells] using congrArg (fun c : Σ t : Fin m, Σ h : Fin (s+1), SourceCell B U t.val h.val => c.2.1.val) hij
  · change SecondJetRelaxedSpace.exponent i.val 2 = SecondJetRelaxedSpace.exponent j.val 2
    simpa only [toCells] using congrArg (fun c : Σ t : Fin m, Σ h : Fin (s+1), SourceCell B U t.val h.val => c.2.2.val.1.val) hij
  · change SecondJetRelaxedSpace.exponent i.val 3 = SecondJetRelaxedSpace.exponent j.val 3
    simpa only [toCells] using congrArg (fun c : Σ t : Fin m, Σ h : Fin (s+1), SourceCell B U t.val h.val => c.2.2.val.2.val) hij
  · exact i.property.trans j.property.symm

private theorem cells_ext {m B s U : ℕ}
    (u v : Σ t : Fin m, Σ h : Fin (s+1), SourceCell B U t.val h.val)
    (ht : u.1.val = v.1.val) (hh : u.2.1.val = v.2.1.val)
    (h₁ : u.2.2.val.1.val = v.2.2.val.1.val)
    (h₂ : u.2.2.val.2.val = v.2.2.val.2.val) : u = v := by
  rcases u with ⟨t,h,⟨⟨i,j⟩,p⟩⟩
  rcases v with ⟨t',h',⟨⟨i',j'⟩,p'⟩⟩
  have ht' : t = t' := Fin.ext ht
  subst t'
  have hh' : h = h' := Fin.ext hh
  subst h'
  have hi' : i = i' := Fin.ext h₁
  have hj' : j = j' := Fin.ext h₂
  subst i'
  subst j'
  rfl

private theorem toCells_surjective (m B s U : ℕ) (hsB : 2*s ≤ B) :
    Function.Surjective (toCells m B s U) := by
  rintro ⟨t,h,ij⟩
  let d : Fin 5 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![t.val,h.val,ij.val.1.val,ij.val.2.val,0]
  have hi := ij.val.1.isLt
  have hj := ij.val.2.isLt
  have hh := h.isLt
  have heq := ij.property
  have hd : Allowed m U B s d ∧ 2*d 1+d 3 ≤ B ∧ d 1+d 2+d 3 ≤ U ∧ d 1+d 2+d 3 ≤ U := by
    dsimp only [Allowed]
    simp [d] <;> omega
  obtain ⟨e,he⟩ := (SecondJetRelaxedSpace.mem_range_exponent m U B s U (fun _ => U) d).mpr hd
  have hzero : SecondJetRelaxedSpace.exponent e 4 = 0 := by simp [he,d]
  let i : SeedlessIndex m B s U := ⟨e,hzero⟩
  refine ⟨i,?_⟩
  apply cells_ext <;> simp [toCells, i, he, d]

theorem card_seedlessIndex (m B s U : ℕ) (hsB : 2*s ≤ B) :
    Fintype.card (SeedlessIndex m B s U) =
      ∑ t : Fin m, ∑ h : Fin (s+1),
        if h.val ≤ U then Fintype.card (SeedlessRectangle (t.val+1) (B-2*h.val+1) (U-h.val)) else 0 := by
  rw [Fintype.card_congr (Equiv.ofBijective _ ⟨toCells_injective _ _ _ _, toCells_surjective _ _ _ _ hsB⟩)]
  simp only [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro h _
  split_ifs with hh
  · exact Fintype.card_congr (sourceCellEquiv B U t.val h.val hh)
  · have : IsEmpty (SourceCell B U t.val h.val) := ⟨fun ij => hh (by have := ij.property; omega)⟩
    exact Fintype.card_eq_zero

theorem card_seedlessKernelBlock (m B s U t h : ℕ) (ht : t ≤ m) (hh : h ≤ s) :
    let k := q m s t h
    Fintype.card (SeedlessKernelBlock m B s U t h) =
      if k ≤ t ∧ m-t+2*h ≤ B ∧ h+k ≤ U then
        Fintype.card (SeedlessRectangle (t-k+1) (B-2*h-k+1) (U-h-k))
      else 0 := by
  let k := q m s t h
  change _ = if k ≤ t ∧ m-t+2*h ≤ B ∧ h+k ≤ U then _ else 0
  split_ifs with hb
  · have hkm : k ≤ m-t := by dsimp [k,q]; omega
    have equiv : SeedlessKernelBlock m B s U t h ≃
        SeedlessRectangle (t-k+1) (B-2*h-k+1) (U-h-k) :=
      { toFun := fun d => by
          have hd := d.val.property
          change (d.val.val 0).val+k ≤ t ∧ (d.val.val 1).val+k+2*h ≤ B ∧
            m-t+2*h ≤ B ∧ (d.val.val 0).val+(d.val.val 1).val+h+k ≤ U ∧ _ at hd
          have hi : (d.val.val 0).val < t-k+1 := by omega
          have hj : (d.val.val 1).val < B-2*h-k+1 := by omega
          have hc : (d.val.val 0).val+(d.val.val 1).val ≤ U-h-k := by omega
          exact ⟨⟨⟨(d.val.val 0).val,hi⟩,⟨(d.val.val 1).val,hj⟩⟩,hc⟩
        invFun := fun ij => by
          have hi := ij.val.1.isLt
          have hj := ij.val.2.isLt
          have hsum := ij.property
          let i := (⟨ij.val.1.val,by omega⟩ : Fin (U+1))
          let j := (⟨ij.val.2.val,by omega⟩ : Fin (U+1))
          let v : Fin 3 → Fin (U+1) := ![i,j,0]
          refine ⟨⟨v,?_,?_,hb.2.1,?_,?_,?_⟩,?_⟩
          all_goals try (simp [v,i,j,k] <;> omega)
        left_inv := fun d => by
          apply Subtype.ext
          apply Subtype.ext
          funext i
          apply Fin.ext
          fin_cases i
          · rfl
          · rfl
          · exact d.property.symm
        right_inv := fun ij => by
          apply Subtype.ext
          apply Prod.ext <;> apply Fin.ext <;> rfl }
    exact Fintype.card_congr equiv
  · have : IsEmpty (SeedlessKernelBlock m B s U t h) := ⟨fun d => by
      have hd := d.val.property
      change (d.val.val 0).val+k ≤ t ∧ _ ∧
        m-t+2*h ≤ B ∧ (d.val.val 0).val+(d.val.val 1).val+h+k ≤ U ∧ _ at hd
      exact hb ⟨by omega,hd.2.2.1,by omega⟩⟩
    exact Fintype.card_eq_zero

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
