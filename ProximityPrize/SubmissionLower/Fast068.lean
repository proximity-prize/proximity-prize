import ProximityPrize.SubmissionLower.Fast064
import ProximityPrize.SubmissionLower.Fast065
import ProximityPrize.SubmissionLower.Fast067
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace K1_3
noncomputable section
open Polynomial Matrix Finset FrobeniusLocator
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
theorem residual_error_count [DecidableEq F] (D : Finset ι) (G : Finset F) (q : ι → F[X]) (d : ℕ)
    (hd : 0 < d) (hne : ∀ i ∈ D, q i ≠ 0) (hdeg : ∀ i ∈ D, (q i).natDegree ≤ d)
    (hroots : ∀ γ ∈ G, d ≤ (D.filter (fun i => (q i).eval γ = 0)).card) :
    G.card ≤ D.card := by
  classical
  have hi (i : ι) (hi : i ∈ D) : (G.filter (fun γ => (q i).eval γ = 0)).card ≤ d := by
    apply (le_trans ?_ (hdeg i hi))
    apply Polynomial.card_le_degree_of_subset_roots
    intro γ hγ
    exact (Polynomial.mem_roots (hne i hi)).mpr (Finset.mem_filter.mp hγ).2
  have hswap : (∑ γ ∈ G, (D.filter (fun i => (q i).eval γ = 0)).card) =
      ∑ i ∈ D, (G.filter (fun γ => (q i).eval γ = 0)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hc : G.card * d ≤ D.card * d := calc
    G.card * d = ∑ _γ ∈ G, d := by simp [Nat.mul_comm]
    _ ≤ ∑ γ ∈ G, (D.filter (fun i => (q i).eval γ = 0)).card := Finset.sum_le_sum hroots
    _ = ∑ i ∈ D, (G.filter (fun γ => (q i).eval γ = 0)).card := hswap
    _ ≤ ∑ _i ∈ D, d := Finset.sum_le_sum hi
    _ = D.card * d := by simp [Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_right hc hd
omit [Fintype ι] [DecidableEq ι] in
theorem fixed_error_count (x u v : ι → F) (k : ℕ) (G : Finset F)
    (E : Finset ι) (P : F → F[X]) (S : F → Finset ι)
    (hP : ∀ γ ∈ G, (P γ).degree < k)
    (hout : ∀ γ ∈ G, ∀ i, i ∉ E → u i + γ * v i = (P γ).eval (x i))
    (havoid : ∀ γ ∈ G, ∀ i ∈ S γ, i ∉ E)
    (hbad : ∀ γ ∈ G, ¬ (ExtendsOn x u k (S γ) ∧ ExtendsOn x v k (S γ))) :
    G.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro γ hγ ζ hζ
  by_contra hne
  have hz : ζ - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let V := (ζ - γ)⁻¹ • (P ζ - P γ)
  let U := P γ - γ • V
  have hV : V.degree < k :=
    Principal.degree_smul_lt _ (Principal.degree_sub_lt (hP ζ hζ) (hP γ hγ))
  have hU : U.degree < k :=
    Principal.degree_sub_lt (hP γ hγ) (Principal.degree_smul_lt _ hV)
  have hVe (i : ι) (hi : i ∉ E) : V.eval (x i) = v i := by
    simp only [V, eval_smul, eval_sub, smul_eq_mul, ← hout ζ hζ i hi, ← hout γ hγ i hi]
    field_simp [hz]
    ring
  have hUe (i : ι) (hi : i ∉ E) : U.eval (x i) = u i := by
    simp only [U, eval_sub, eval_smul, smul_eq_mul, hVe i hi, ← hout γ hγ i hi]
    ring
  exact hbad γ hγ
    ⟨⟨U, hU, fun i hi => hUe i (havoid γ hγ i hi)⟩,
      ⟨V, hV, fun i hi => hVe i (havoid γ hγ i hi)⟩⟩
theorem deficient_hankel_count (x u v : ι → F) (hx : Function.Injective x)
    (k l t α : ℕ) (hsize : k + l + t = Fintype.card ι) (hα : α < l)
    (hrank : GenericLayer.genericRank (hankel x u v l t) = α)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Principal.BadSlope x u v k (k + l) γ) :
    Γ.card ≤ Fintype.card ι + α := by
  classical
  let M := hankel x u v l t
  let φ := algebraMap F[X] (GenericLayer.GenericField F)
  have hφ := IsFractionRing.injective F[X] (GenericLayer.GenericField F)
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ M α hrank
  let Δ := (NormalFiber.pivot B).det
  have hΔdeg : Δ.natDegree ≤ α := by
    simpa [Δ] using NormalFiber.minor_degree_le φ M α B (fun _ => 1)
      (hankel_entry_natDegree x u v l t)
  let G := Γ.filter (fun γ => Δ.eval γ ≠ 0)
  let exceptional := Γ.filter (fun γ => Δ.eval γ = 0)
  have hExceptional : exceptional.card ≤ α := by
    apply (le_trans ?_ hΔdeg)
    apply Polynomial.card_le_degree_of_subset_roots
    intro γ hγ
    exact (Polynomial.mem_roots B.minor_ne).mpr (Finset.mem_filter.mp hγ).2
  have hsplit : exceptional.card + G.card = Γ.card :=
    Finset.card_filter_add_card_filter_not (s := Γ) (p := fun γ => Δ.eval γ = 0)
  suffices hG : G.card ≤ Fintype.card ι by omega
  by_cases hG0 : G.Nonempty
  · have hdata : ∀ γ : F, ∃ (P : F[X]) (S : Finset ι), γ ∈ G →
        k + l ≤ S.card ∧ P.degree < k ∧
          (∀ i ∈ S, P.eval (x i) = u i + γ * v i) ∧
          ¬ (ExtendsOn x u k S ∧ ExtendsOn x v k S) := by
      intro γ
      by_cases hg : γ ∈ G
      · obtain ⟨S, hS, ⟨P, hP, hp⟩, hb⟩ := hΓ γ (Finset.mem_filter.mp hg).1
        exact ⟨P, S, fun _ => ⟨hS, hP, hp, hb⟩⟩
      · exact ⟨0, ∅, fun h => (hg h).elim⟩
    choose P S hPS using hdata
    let E : F → Finset ι :=
      fun γ => univ.filter (fun i => u i + γ * v i ≠ (P γ).eval (x i))
    have her (γ : F) (i : ι) : i ∈ E γ ↔ u i + γ * v i ≠ (P γ).eval (x i) := by
      simp [E]
    have hsizeE (γ : F) (hg : γ ∈ G) : (E γ).card ≤ t := by
      have hsub : E γ ⊆ univ \ S γ := by
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨mem_univ _, fun his => (her γ i).mp hi
          (((hPS γ hg).2.2.1 i his).symm)⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at hle
      have := (hPS γ hg).1
      omega
    have hactual (γ : F) (hg : γ ∈ G) : (E γ).card = α := by
      have hr := NormalFiber.rank_specializes φ hφ M α B γ (Finset.mem_filter.mp hg).2
      change ((hankel x u v l t).map (evalRingHom γ)).rank = α at hr
      rw [evaluated_hankel_rank x u v hx γ (P γ) k l t (hPS γ hg).2.1 hsize.le (E γ)
        (by have := hsizeE γ hg; omega)
        (fun i hi => by simpa only [her, not_not] using hi)
        (fun i hi => (her γ i).mp hi)] at hr
      omega
    let H : Finset ι := univ.filter (fun i => ∀ γ ∈ G, i ∈ E γ)
    have hH (i : ι) : i ∈ H ↔ ∀ γ ∈ G, i ∈ E γ := by simp [H]
    have hsub (γ : F) (hg : γ ∈ G) : H ⊆ E γ :=
      fun i hi => (hH i).mp hi γ hg
    obtain ⟨γ₀, hγ₀⟩ := hG0
    have hHle : H.card ≤ α := by
      rw [← hactual γ₀ hγ₀]
      exact Finset.card_le_card (hsub γ₀ hγ₀)
    have hat : α ≤ t := (hactual γ₀ hγ₀) ▸ hsizeE γ₀ hγ₀
    let d := α - H.card
    have hcard (γ : F) (hg : γ ∈ G) : (E γ \ H).card = d := by
      rw [Finset.card_sdiff_of_subset (hsub γ hg), hactual γ hg]
    by_cases hd : 0 < d
    · let f := locator x H
      let u' := fun i => f.eval (x i) * u i
      let v' := fun i => f.eval (x i) * v i
      let M' := hankel x u' v' d d
      let A := M'.submatrix id Fin.castSucc
      let b := fun i => M' i (Fin.last d)
      let q := fun i : ι => ∑ j : Option (Fin d),
        C (x i ^ (j.elim d Fin.val)) * CofactorLine.vector A b j
      have hq (γ : F) (hg : γ ∈ G) (i : ι) :
          (q i).eval γ = A.det.eval γ * (locator x (E γ \ H)).eval (x i) ∧
            A.det.eval γ ≠ 0 := by
        have hdeg : (f * P γ).degree < (k + H.card : ℕ) := by
          have hfdeg : f.degree = (H.card : ℕ) := by
            rw [degree_eq_natDegree (locator_monic x H).ne_zero, locator_natDegree]
          have h := (hPS γ hg).2.1
          exact (degree_mul_le _ _).trans_lt (by
            rw [hfdeg, Nat.cast_add, add_comm (k : WithBot ℕ)]
            exact WithBot.add_lt_add_left WithBot.coe_ne_bot h)
        have hval (a : ι) : u' a + γ * v' a - (f * P γ).eval (x a) =
            f.eval (x a) * (u a + γ * v a - (P γ).eval (x a)) := by
          simp only [u', v', eval_mul]
          ring
        apply cofactor_at_nodes x u' v' hx γ (f * P γ) (k + H.card) d hdeg
          (by dsimp [d]; omega) (E γ \ H) (hcard γ hg) _ _ i
        · intro a ha
          apply sub_eq_zero.mp
          rw [hval]
          by_cases hh : a ∈ H
          · simp [f, locator_eval_zero x H a hh]
          · have hno : a ∉ E γ := fun he => ha (Finset.mem_sdiff.mpr ⟨he, hh⟩)
            have heq : u a + γ * v a = (P γ).eval (x a) := by
              simpa only [her, not_not] using hno
            simp [heq]
        · intro a ha
          obtain ⟨he, hh⟩ := Finset.mem_sdiff.mp ha
          apply sub_ne_zero.mp
          rw [hval]
          exact mul_ne_zero (fun hz => hh ((Principal.locator_eval_zero_iff x hx H a).mp hz))
            (sub_ne_zero.mpr ((her γ a).mp he))
      let D := (univ : Finset ι) \ H
      refine (residual_error_count D G q d hd ?_ ?_ ?_).trans (Finset.card_le_univ D)
      · intro i hi
        have hni := (Finset.mem_sdiff.mp hi).2
        obtain ⟨γ, hg, he⟩ : ∃ γ ∈ G, i ∉ E γ := by
          by_contra hnone
          apply hni
          apply (hH i).mpr
          intro γ hg
          by_contra he
          exact hnone ⟨γ, hg, he⟩
        intro hz
        obtain ⟨heval, hdet⟩ := hq γ hg i
        rw [hz, eval_zero] at heval
        have hr := (mul_eq_zero.mp heval.symm).resolve_left hdet
        exact he (Finset.mem_sdiff.mp ((Principal.locator_eval_zero_iff x hx _ i).mp hr)).1
      · intro i _
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro j _
        refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        calc
          _ ≤ ∑ _r : Fin d, 1 := CofactorLine.vector_natDegree_le A b (fun _ => 1)
              (fun r c => hankel_entry_natDegree x u' v' d d r (Fin.castSucc c))
              (fun r => hankel_entry_natDegree x u' v' d d r (Fin.last d)) j
          _ = d := by simp
      · intro γ hg
        rw [← hcard γ hg]
        apply Finset.card_le_card
        intro i hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨mem_univ _, (Finset.mem_sdiff.mp hi).2⟩, ?_⟩
        rw [(hq γ hg i).1, locator_eval_zero x _ i hi, mul_zero]
    · have heq (γ : F) (hg : γ ∈ G) : E γ = H := by
        apply (Finset.eq_of_subset_of_card_le (hsub γ hg) ?_).symm
        rw [hactual γ hg]
        dsimp [d] at hd
        omega
      have hf := fixed_error_count x u v k G H P S
        (fun γ hg => (hPS γ hg).2.1)
        (fun γ hg i hi => by
          rw [← heq γ hg, her, not_not] at hi
          exact hi)
        (fun γ hg i hi hs => (her γ i).mp (heq γ hg ▸ hs) (((hPS γ hg).2.2.1 i hi).symm))
        (fun γ hg => (hPS γ hg).2.2.2)
      omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hG0]
end
end K1_3
end
section
namespace K1_13_2_3_7
open K1_13_2 K1_13_2_3
open scoped BigOperators
private theorem natDen_eq (u : ℤ) : (natDen (u + 1).toNat : ℤ) = fastDen u := by
  by_cases hu : u < 0
  · simp [natDen, fastDen, hu, show (u + 1).toNat = 0 by omega]
  lift u to ℕ using (by omega)
  rw [show ((u : ℤ) + 1).toNat = u + 1 by omega]
  simp only [natDen, fastDen, not_lt.mpr (Int.natCast_nonneg _), ite_false, Nat.cast_succ]
  change ((↑(u * (u * (2 * u + 21) + 66) / 72 : ℕ) : ℤ) + 1) = _
  simp only [Int.natCast_ediv, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
private def partValue (ab : ℕ × ℕ) : ℤ := (ab.1 : ℤ) - ab.2
private theorem countParts_eq (d : ℕ) (u : ℤ) :
    partValue (countParts d (u + 1).toNat) = fastCum (d : ℤ) u := by
  by_cases hu : u < 0
  · simp [countParts, partValue, natDen, fastCum, hu, show (u + 1).toNat = 0 by omega]
  let v := min u (3 * (d : ℤ))
  have hvDef : min u (3 * (d : ℤ)) = v := rfl
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hm : Nat.min (u + 1).toNat (3 * d + 1) = (v + 1).toNat := by
    change min (u + 1).toNat (3 * d + 1) = (v + 1).toNat
    dsimp [v]
    omega
  have ha (k : ℕ) : (v + 1).toNat - d - k = (v - (d : ℤ) - k + 1).toNat := by omega
  have hb (k : ℕ) : (v + 1).toNat - 2 * d - k = (v - 2 * (d : ℤ) - k + 1).toNat := by omega
  have h₁ : ((v + 1).toNat ≤ d + 1) ↔ v ≤ (d : ℤ) := by omega
  have h₂ : ((v + 1).toNat ≤ 2 * d + 3) ↔ v ≤ 2 * (d : ℤ) + 2 := by omega
  simp only [countParts, fastCum, not_lt.mpr (Int.natCast_nonneg d), hu, decide_false,
    Bool.false_or, Bool.false_eq_true, ite_false, hm, hvDef, h₁, h₂]
  change partValue (if v ≤ (d : ℤ) then _ else _) = (if v ≤ (d : ℤ) then _ else _)
  by_cases hsmall : v ≤ (d : ℤ)
  · simp only [ite_eq_left hsmall, partValue, Nat.cast_zero, sub_zero, natDen_eq]
  · rw [ite_eq_right hsmall, ite_eq_right hsmall]
    by_cases hlarge : v ≤ 2 * (d : ℤ) + 2
    · simp only [ite_eq_left hlarge, partValue, ha, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, natDen_eq]
      ring
    · simp only [ite_eq_right hlarge, partValue, ha, hb, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, natDen_eq]
      ring
private theorem natKernel_eq (d j h r : ℕ) (hr : r ≤ d) :
    natKernel d j h r =
      (if r = 0 then fastCum d 1650 - fastCum d (1649 - (j : ℤ)) else
        fastCum d 1650 - fastCum d ((h : ℤ) - 1) +
          fastCum ((d : ℤ) - r) ((h : ℤ) - 1 - 3 * r) -
          fastCum ((d : ℤ) - r) (1649 - (j : ℤ))).toNat := by
  have hA := countParts_eq d 1650
  change partValue (countParts d 1651) = _ at hA
  rcases eA : countParts d 1651 with ⟨a, b⟩
  rw [eA] at hA
  by_cases hz : r = 0
  · have hC := countParts_eq d (1649 - (j : ℤ))
    rw [show (1649 - (j : ℤ) + 1).toNat = 1650 - j by omega] at hC
    rcases eC : countParts d (1650 - j) with ⟨c, e⟩
    rw [eC] at hC
    simp only [natKernel, eA, hz, ite_true, eC]
    simp only [partValue] at hA hC
    omega
  · have hC := countParts_eq d ((h : ℤ) - 1)
    have hF := countParts_eq (d - r) ((h : ℤ) - 1 - 3 * r)
    have hK := countParts_eq (d - r) (1649 - (j : ℤ))
    rw [show ((h : ℤ) - 1 + 1).toNat = h by omega] at hC
    rw [show ((h : ℤ) - 1 - 3 * r + 1).toNat = h - 3 * r by omega] at hF
    rw [show (1649 - (j : ℤ) + 1).toNat = 1650 - j by omega] at hK
    rcases eC : countParts d h with ⟨c, e⟩
    rcases eF : countParts (d - r) (h - 3 * r) with ⟨f, g⟩
    rcases eK : countParts (d - r) (1650 - j) with ⟨k, l⟩
    rw [eC] at hC
    rw [eF, Nat.cast_sub hr] at hF
    rw [eK, Nat.cast_sub hr] at hK
    simp only [natKernel, eA, hz, ite_false, eC, eF, eK]
    simp only [partValue] at hA hC hF hK
    omega
private theorem natKernel_signed (d j h r : ℕ) (hr : r ≤ d)
    (hz : ((h : ℤ) - 1 - (1650 - (j : ℤ)) + d < 0) ↔ r = 0)
    (hc : r ≠ 0 → min (d : ℤ) (((h : ℤ) - 1 - (1650 - (j : ℤ)) + d) / 4) + 1 = r) :
    natKernel d j h r = (signedKernel d j ((h : ℤ) - 1)).toNat := by
  rw [natKernel_eq _ _ _ _ hr]
  unfold signedKernel
  by_cases hzero : r = 0
  · rw [ite_eq_left hzero, ite_eq_left (hz.mpr hzero)]
  · rw [ite_eq_right hzero, ite_eq_right (fun h => hzero (hz.mp h)), hc hzero]
private theorem clipped_savings (old original chosen : ℤ) :
    (old - max 0 original).toNat - (old - max (max 0 original) chosen).toNat =
      Nat.min old.toNat chosen.toNat - original.toNat := by
  change _ = min old.toNat chosen.toNat - original.toNat
  omega
theorem natEntry_eq (t j : ℕ) (ht : t < 499) (hj : j < 283) : natEntry t j = entry t j := by
  unfold natEntry entry
  by_cases hdiag : 23 ≤ t + j ∧ t + j ≤ 656
  · simp only [ite_eq_left hdiag]
    let b := 1136 - t
    let h := b - j
    let v := b - 4 * j
    have he : valuePower (3514 + t) j = v := by unfold valuePower v b; omega
    rw [he]
    change (if 4 * j < b then _ else _) = (if v = 0 then _ else _)
    by_cases hp : 4 * j < b
    · have hp' : v ≠ 0 := by dsimp [v]; omega
      rw [ite_eq_left hp, ite_eq_right hp', clipped_savings]
      have hB : b + t = 1136 := by dsimp [b]; omega
      have hh : (h : ℤ) - 1 = 1135 - (t : ℤ) - j := by dsimp [h]; omega
      have h₀ : (h : ℤ) - 1 - (1650 - (j : ℤ)) + 1650 = (b : ℤ) - 1 := by
        dsimp [h]; omega
      have h₁ : (h : ℤ) - 1 - (1650 - (j : ℤ)) + (↑(1650 - v : ℕ) : ℤ) = 4 * (j : ℤ) - 1 := by
        dsimp [h, v]; omega
      have hzero₀ : (↑h - 1 - (1650 - (j : ℤ)) + 1650 < 0) ↔ (b + 3) / 4 = 0 := by
        rw [h₀]; omega
      have hcut₀ : (b + 3) / 4 ≠ 0 →
          min (1650 : ℤ) ((↑h - 1 - (1650 - (j : ℤ)) + 1650) / 4) + 1 = ↑((b + 3) / 4) := by
        rw [h₀]; omega
      have hn₀ : natKernel 1650 j h ((b + 3) / 4) =
          (signedKernel 1650 j (1135 - (t : ℤ) - j)).toNat := by
        simpa only [hh, Nat.cast_ofNat] using
          natKernel_signed 1650 j h ((b + 3) / 4) (by omega) hzero₀ hcut₀
      have hzero₁ : (↑h - 1 - (1650 - (j : ℤ)) + (↑(1650 - v : ℕ) : ℤ) < 0) ↔ j = 0 := by
        rw [h₁]; omega
      have hcut₁ : j ≠ 0 → min (↑(1650 - v : ℕ) : ℤ)
          ((↑h - 1 - (1650 - (j : ℤ)) + (↑(1650 - v : ℕ) : ℤ)) / 4) + 1 = j := by
        rw [h₁]; dsimp [v]; omega
      have hd₁ : (↑(1650 - v : ℕ) : ℤ) = 1650 - (v : ℤ) := by dsimp [v]; omega
      have hn₁ : natKernel (1650 - v) j h j =
          (signedKernel (1650 - (v : ℤ)) j (1135 - (t : ℤ) - j)).toNat := by
        simpa only [hh, hd₁] using
          natKernel_signed (1650 - v) j h j (by dsimp [v]; omega) hzero₁ hcut₁
      have hd := natDen_eq 1650
      change (natDen 1651 : ℤ) = _ at hd
      have hl := natDen_eq (1649 - (j : ℤ))
      rw [show (1649 - (j : ℤ) + 1).toNat = 1650 - j by omega] at hl
      have ho : natDen 1651 - natDen (1650 - j) =
          (fastDen 1650 - fastDen (1649 - (j : ℤ))).toNat := by omega
      change Nat.min (natDen 1651 - natDen (1650 - j)) (natKernel (1650 - v) j h j) -
        natKernel 1650 j h ((b + 3) / 4) = _
      rw [ho, hn₀, hn₁]
    · have hz : v = 0 := by dsimp [v]; omega
      rw [ite_eq_right hp, ite_eq_left hz]
  · simp only [ite_eq_right hdiag]
private def windowEmbed : Fin 499 × Fin 283 ↪ BlockIndex where
  toFun x := (⟨3514 + x.1.val, by have := x.1.isLt; omega⟩, x.2.castLE (by decide))
  inj' := by
    intro x y h
    apply Prod.ext <;> apply Fin.ext
    · have e := congrArg (fun i : BlockIndex => i.1.val) h
      change 3514 + x.1.val = 3514 + y.1.val at e
      omega
    · exact congrArg (fun i : BlockIndex => i.2.val) h
private theorem rangeSum_eq (f : ℕ → ℕ) (n : ℕ) :
    rangeSum f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [rangeSum]
  | succ n ih => rw [rangeSum, Finset.sum_range_succ, ih]
private theorem rangeSum_fin (f : ℕ → ℕ) (n : ℕ) :
    rangeSum f n = ∑ k : Fin n, f k.val := by
  rw [rangeSum_eq, Fin.sum_univ_eq_sum_range]
private theorem sum_embed_le {α β : Type*} [Fintype α] [Fintype β] (e : α ↪ β) (f : β → ℕ) :
    (∑ i : α, f (e i)) ≤ ∑ i : β, f i := calc
  _ = ∑ i ∈ Finset.univ.map e, f i := by rw [Finset.sum_map]
  _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
theorem numeric_le_savings : natChunk 0 499 ≤ savingsSum w4 witness := by
  unfold natChunk
  simp only [zero_add, rangeSum_fin, natGrade]
  rw [← Finset.sum_product Finset.univ Finset.univ
    (fun x : Fin 499 × Fin 283 => natEntry x.1.val x.2.val), Finset.univ_product_univ]
  calc
    _ = ∑ x : Fin 499 × Fin 283,
        if w4.Contains (windowEmbed x) then savings (windowEmbed x) (witness (windowEmbed x)) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [natEntry_eq _ _ x.1.isLt x.2.isLt]
      exact entry_eq x.1 x.2 (windowEmbed x) rfl rfl
    _ ≤ _ := sum_embed_le windowEmbed (fun i => if w4.Contains i then savings i (witness i) else 0)
end K1_13_2_3_7
end
section
namespace K1_13_2_3_7
theorem proof : K1_13_2_3.c7 := by
  refine ⟨witness, ?_⟩
  calc
    174062508216 ≤ 177382348097 := by decide
    _ = natChunk 0 499 := numeric_total.symm
    _ ≤ _ := numeric_le_savings
end K1_13_2_3_7
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_13_6_1_4_1_1
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem genericSlice {k σ τ : Type*} [Field k] [Finite σ]
    (J : Ideal (MvPolynomial σ k)) (hJ : J.IsPrime)
    (s : Finset τ) (c : τ) (hc : c ∈ s)
    (u : τ → MvPolynomial σ k) (hu : u c = 1) :
    let F := FractionRing (MvPolynomial τ k)
    let ι : MvPolynomial σ k →+* MvPolynomial σ F := MvPolynomial.map (algebraMap k F)
    let g : MvPolynomial σ F :=
      ∑ m ∈ s, MvPolynomial.C (algebraMap (MvPolynomial τ k) F (MvPolynomial.X m)) * ι (u m)
    let L := J.map ι ⊔ Ideal.span {g}
    (affineHilbertPolynomial L).natDegree ≤ (affineHilbertPolynomial J).natDegree - 1 ∧
      (L = ⊤ ∨ L.IsPrime ∧ L.comap ι = J) := by
  classical
  let _ : J.IsPrime := hJ
  let R := MvPolynomial σ k
  let A := R ⧸ J
  let q : R →+* A := Ideal.Quotient.mk J
  let D := MvPolynomial τ k
  let F := FractionRing D
  let T := MvPolynomial σ D
  let V := MvPolynomial σ F
  let ι₀ : R →+* T := MvPolynomial.map MvPolynomial.C
  let localize : T →+* V := algebraMap T V
  let ι : R →+* V := MvPolynomial.map (algebraMap k F)
  let G : T := ∑ m ∈ s, MvPolynomial.C (MvPolynomial.X m) * ι₀ (u m)
  let P := J.map ι₀
  let H := P ⊔ Ideal.span {G}
  let M : Submonoid T := (nonZeroDivisors D).map MvPolynomial.C
  have hloc : IsLocalization M V := MvPolynomial.isLocalization (nonZeroDivisors D) F
  have hι : localize.comp ι₀ = ι := by
    apply MvPolynomial.ringHom_ext <;> intro x
    · change MvPolynomial.map (algebraMap D F) (MvPolynomial.map MvPolynomial.C (MvPolynomial.C x)) =
        MvPolynomial.map (algebraMap k F) (MvPolynomial.C x)
      simp only [MvPolynomial.map_C] <;> rfl
    · change MvPolynomial.map (algebraMap D F) (MvPolynomial.map MvPolynomial.C (MvPolynomial.X x)) =
        MvPolynomial.map (algebraMap k F) (MvPolynomial.X x)
      simp only [MvPolynomial.map_X]
  have hG : localize G = ∑ m ∈ s, MvPolynomial.C (algebraMap D F (MvPolynomial.X m)) * ι (u m) := by
    simp only [G, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro m _
    have hm : localize (ι₀ (u m)) = ι (u m) := RingHom.congr_fun hι (u m)
    rw [show localize (MvPolynomial.C (MvPolynomial.X m)) = MvPolynomial.C (algebraMap D F (MvPolynomial.X m)) from MvPolynomial.map_C _ _, hm]
  have hP : P.map localize = J.map ι := by
    rw [show P = J.map ι₀ from rfl, Ideal.map_map, hι]
  dsimp only
  rw [← hG]
  let e := (commAlgEquiv k σ τ).toRingEquiv
  let move : T →+* MvPolynomial τ A := (MvPolynomial.map q).comp e.toRingHom
  have he : e.toRingHom.comp ι₀ = MvPolynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro x
      change commAlgEquiv k σ τ (MvPolynomial.map MvPolynomial.C (MvPolynomial.C x)) = _
      rw [MvPolynomial.map_C, commAlgEquiv_C, MvPolynomial.map_C]
    · intro i
      change commAlgEquiv k σ τ (MvPolynomial.map MvPolynomial.C (MvPolynomial.X i)) = _
      rw [MvPolynomial.map_X, commAlgEquiv_X]
  have hmι (x : R) : move (ι₀ x) = MvPolynomial.C (q x) := by
    change MvPolynomial.map q (e (ι₀ x)) = _
    rw [show e (ι₀ x) = MvPolynomial.C x from RingHom.congr_fun he x, MvPolynomial.map_C]
  have hmC (d : D) : move (MvPolynomial.C d) = MvPolynomial.map (q.comp MvPolynomial.C) d := by
    change MvPolynomial.map q (commAlgEquiv k σ τ (MvPolynomial.C d)) = _
    rw [commAlgEquiv_C, MvPolynomial.map_map]
  have hsurj : Function.Surjective move :=
    (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp e.surjective
  have hker : RingHom.ker move = P := by
    change RingHom.ker ((MvPolynomial.map q).comp e.toRingHom) = J.map ι₀
    rw [← RingHom.comap_ker, MvPolynomial.ker_map, show RingHom.ker q = J from Ideal.mk_ker,
      ← he, ← Ideal.map_map, Ideal.comap_map_of_bijective e.toRingHom e.bijective]
  have hmoveG : move G = ∑ m ∈ s, MvPolynomial.X m * MvPolynomial.C (q (u m)) := by
    simp only [G, map_sum, map_mul, hmC, hmι, MvPolynomial.map_X]
  obtain ⟨hne, f, hf, hfC⟩ :=
    eliminateConstantParameter s c hc (fun m => q (u m)) (by simp [hu])
  rw [← hmoveG] at hne hf
  have hPprime : P.IsPrime := by
    rw [← hker, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_isPrime move _
  have hPdisj : Disjoint (M : Set T) (P : Set T) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨d, hd, rfl⟩ hm
    have hn : move (MvPolynomial.C d) ≠ 0 := by
      rw [hmC]
      simpa only [map_zero] using
        (MvPolynomial.map_injective _ (q.comp MvPolynomial.C).injective).ne (nonZeroDivisors.ne_zero hd)
    exact hn (RingHom.mem_ker.mp (hker.symm ▸ hm))
  have hPext : (J.map ι).IsPrime :=
    hP ▸ IsLocalization.isPrime_of_isPrime_disjoint M V P hPprime hPdisj
  have hproper : localize G ∉ J.map ι := by
    rw [← hP]
    change G ∉ (P.map (algebraMap T V)).under T
    rw [IsLocalization.under_map_of_isPrime_disjoint M V hPprime hPdisj, ← hker]
    exact hne
  have hdegree := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hPext hproper le_rfl).1
  rw [K1_13_5_5_2.hilbertPolynomial_map J] at hdegree
  refine ⟨hdegree, ?_⟩
  have hH : H.map localize = J.map ι ⊔ Ideal.span {localize G} := by
    simp only [H, Ideal.map_sup, hP, Ideal.map_span, Set.image_singleton]
  rw [← hH]
  by_cases htop : H.map localize = ⊤
  · exact Or.inl htop
  have hHdisj := (IsLocalization.map_algebraMap_ne_top_iff_disjoint M V H).mp htop
  have hkerH : RingHom.ker (f.comp move) = H := by
    rw [← RingHom.comap_ker, hf, ← Set.image_singleton (f := move) (a := G),
      ← Ideal.map_span, Ideal.comap_map_of_surjective _ hsurj,
      ← RingHom.ker_eq_comap_bot, hker, sup_comm]
  have hHprime : H.IsPrime := by
    rw [← hkerH, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_isPrime (f.comp move) _
  refine Or.inr ⟨IsLocalization.isPrime_of_isPrime_disjoint M V H hHprime hHdisj, ?_⟩
  change (H.map localize).comap ι = J
  rw [← hι, ← Ideal.comap_comap]
  change ((H.map (algebraMap T V)).under T).comap ι₀ = J
  rw [IsLocalization.under_map_of_isPrime_disjoint M V hHprime hHdisj, ← hkerH]
  ext x
  change f (move (ι₀ x)) = 0 ↔ x ∈ J
  rw [hmι, show f (MvPolynomial.C (q x)) = MvPolynomial.C (q x) from RingHom.congr_fun hfC (q x)]
  constructor
  · intro hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (MvPolynomial.C_injective _ _ (hz.trans (map_zero MvPolynomial.C).symm))
  · intro hx
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_1
theorem proof : K1_13_6_1_4_1.c1 := by
  intro J h hJ _
  let c : SectionIndex h := fun _ => 0
  have hc : c ∈ boxMonomials h := by simp [c, boxMonomials]
  let u : SectionIndex h → GeoJets := fun m => ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
  have hu : u c = 1 := by simp [u, c]
  have hg : (∑ m ∈ boxMonomials h,
      MvPolynomial.C (algebraMap (MvPolynomial (SectionIndex h) GeoField) (SectionField h) (MvPolynomial.X m)) *
        sliceMap h (u m)) = genericSection h := by
    simp [u, sliceMap, genericSection]
  have hs := genericSlice J hJ (boxMonomials h) c hc u hu
  dsimp only at hs
  simp only [sliceMap] at hg
  rw [hg] at hs
  exact hs
end
end K1_13_6_1_4_1_1
end
section
namespace K1_12
noncomputable section
open Polynomial K1
structure Direction (u : Words) (deleted : Finset I) where
  den : K[X]
  U : K[X]
  V : K[X]
  A : Fin 2 → K[X]
  out : Fin 2 → Fin 2 → K[X]
  den_nodes : ∀ i, den.eval (node i) ≠ 0
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ den
  coprime : IsCoprime U V
  phase : U * den.map twist = V * den
  degrees_eq : V.natDegree = U.natDegree
  primitive : IsCoprime (A 0) (A 1)
  height : U.natDegree + amplitudeDegree (A 0) (A 1) + deleted.card ≤ 32680
  out_degree : ∀ i j, (out i j).degree <
    (131072 + U.natDegree + amplitudeDegree (A 0) (A 1) : ℕ)
  nodes : ∀ x ∉ deleted, ∀ i j, (out i j).eval (node x) =
    U.eval (node x) * ((A i).map twist).eval (node x) * u j x -
    V.eval (node x) * (A j).eval (node x) * twist (u i x)
variable {u : Words} {deleted : Finset I}
def Direction.s (F : Direction u deleted) := amplitudeDegree (F.A 0) (F.A 1)
def Direction.amp (F : Direction u deleted) (γ : K) := F.A 0 + C γ * F.A 1
structure Regular (F : Direction u deleted) (γ : K) : Prop where
  amp_ne : F.amp γ ≠ 0
  degree_eq : (F.amp γ).natDegree = F.s
  adjacent : IsCoprime (F.amp γ) ((F.amp γ).map twist)
  content_unit : IsCoprime (F.amp γ) F.U
  node_unit : ∀ i ∉ deleted, (F.amp γ).eval (node i) ≠ 0
structure CrossLift (F : Direction u deleted) where
  G : K[X]
  L : K[X]
  monic : G.Monic
  left : G ∣ F.U
  right : G.map twist ∣ F.V
  degree_lt : L.degree < (131072 + F.s + G.natDegree : ℕ)
  nodes : ∀ i ∉ deleted, L.eval (node i) = G.eval (node i) *
    ((F.A 0).eval (node i) * u 1 i - (F.A 1).eval (node i) * u 0 i)
structure Offset (F : Direction u deleted) {η : K} (anchor : BadMark u η) where
  pencil : K[X]
  pencil_degree : pencil.degree < 131072
  E : K[X]
  Q : K[X]
  E_monic : E.Monic
  left : E ∣ F.U
  right : E.map twist ∣ F.V
  proper : Q.degree < E.degree
  reduced : IsCoprime Q E
  raw : I → K
  raw_fixed : ∀ i ∉ deleted, twist (raw i) = raw i
  first : ∀ i ∉ deleted, u 0 i + η * u 1 i - anchor.decoder.eval (node i) =
    (F.amp η).eval (node i) * raw i / F.den.eval (node i)
  second : ∀ i ∉ deleted, u 1 i - pencil.eval (node i) =
    Q.eval (node i) / E.eval (node i) + (F.A 1).eval (node i) * raw i / F.den.eval (node i)
end
end K1_12
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace K1_12
noncomputable section
open Polynomial K1 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
theorem eval_unit_of_dvd {P Q : K[X]} (h : P ∣ Q) {a : K}
    (hu : Q.eval a ≠ 0) : P.eval a ≠ 0 := by
  obtain ⟨L, rfl⟩ := h
  rw [eval_mul] at hu
  exact left_ne_zero_of_mul hu
private def conjugate : ℕ → K[X] → K[X]
  | 0, P => P
  | n+1, P => (conjugate n P).map twist
private theorem conjugate_six (P : K[X]) : conjugate 6 P = P := by
  have iter (n : ℕ) : conjugate n P = P.map (iterateFrobenius K p n) := by
    induction n with
    | zero => simp [conjugate]
    | succ n ih =>
      rw [conjugate, ih, map_map, add_comm n 1,
        iterateFrobenius_add K p 1 n, iterateFrobenius_one, twist]
  have card : Fintype.card K = p^6 := KoalaBear.card_ext6
  have hs : iterateFrobenius K p 6 = RingHom.id K := by
    apply RingHom.ext
    intro x
    change x ^ p ^ 6 = x
    rw [← card]
    exact FiniteField.pow_card x
  rw [iter, hs, map_id]
theorem twist_node (i : I) : twist (node i) = node i := Native.native_domain_fixed i
theorem eval_twist (P : K[X]) (i : I) : (P.map twist).eval (node i) = twist (P.eval (node i)) :=
  Strata.eval_coefficient_map twist P (node i) (twist_node i)
private theorem conjugate_nodes {W : K[X]} (hu : ∀ i, W.eval (node i) ≠ 0)
    (n : ℕ) (i : I) : (conjugate n W).eval (node i) ≠ 0 := by
  induction n with
  | zero => exact hu i
  | succ n ih => rw [conjugate, eval_twist]; exact (map_ne_zero twist).mpr ih
private theorem conjugate_dvd {W T : K[X]} (h : W ∣ T) (ht : T.map twist = T)
    (n : ℕ) : conjugate n W ∣ T := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [conjugate, ← ht]
    exact map_dvd (Polynomial.mapRingHom twist) ih
theorem invariant_multiple (W : K[X]) (hu : ∀ i, W.eval (node i) ≠ 0) :
    ∃ L C₀ : K[X], L = W * C₀ ∧ L.map twist = L ∧ (∀ i, L.eval (node i) ≠ 0) ∧
      ∀ N : K[X], (W*N).map twist = W*N → ∃ S : K[X], S.map twist = S ∧ N = C₀*S := by
  classical
  let f := fun j : Fin 6 => conjugate j.val W
  let rawL := Finset.univ.lcm f
  let L := normalize rawL
  have hdiv (j : Fin 6) : f j ∣ L :=
    dvd_normalize_iff.mpr (Finset.dvd_lcm (Finset.mem_univ j))
  have hnode (i : I) : L.eval (node i) ≠ 0 := by
    apply eval_unit_of_dvd (normalize_dvd_iff.mpr (Finset.lcm_dvd_prod Finset.univ f))
    rw [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => conjugate_nodes hu j.val i)
  have hne : L ≠ 0 := fun h => hnode 0 (by rw [h, eval_zero])
  have hm : L.Monic := monic_normalize (by simpa [L] using hne)
  have hcross : L ∣ L.map twist := by
    apply normalize_dvd_iff.mpr
    apply Finset.lcm_dvd
    intro j _
    have step (i : Fin 6) : conjugate (i.val+1) W ∣ L.map twist :=
      map_dvd (Polynomial.mapRingHom twist) (hdiv i)
    by_cases hz : j.val = 0
    · change conjugate j.val W ∣ _
      rw [hz]
      change W ∣ _
      simpa only [show (5 : Fin 6).val+1 = 6 by decide, conjugate_six] using step 5
    · let i : Fin 6 := ⟨j.val-1, by omega⟩
      have hi : i.val+1 = j.val := by dsimp [i]; omega
      simpa only [hi, f] using step i
  have hfix : L.map twist = L := (eq_of_dvd_of_natDegree_le_of_leadingCoeff hcross
    natDegree_map_le (hm.trans (hm.map twist).symm)).symm
  obtain ⟨C₀, hc⟩ := hdiv 0
  change L = W * C₀ at hc
  refine ⟨L, C₀, hc, hfix, hnode, ?_⟩
  intro N ht
  have hL : L ∣ W*N := normalize_dvd_iff.mpr (Finset.lcm_dvd (fun j _ =>
    conjugate_dvd (dvd_mul_right W N) ht j.val))
  obtain ⟨S, hs⟩ := hL
  refine ⟨S, ?_, ?_⟩
  · apply mul_left_cancel₀ hne
    rw [hs, Polynomial.map_mul, hfix] at ht
    exact ht
  · have hW : W ≠ 0 := fun h => hu 0 (by rw [h, eval_zero])
    apply mul_left_cancel₀ hW
    simpa only [hc, mul_assoc] using hs
variable {u : Words} {deleted : Finset I} {F : Direction u deleted} {η γ : K}
  {anchor : BadMark u η}
end
end K1_12
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace K1_12
noncomputable section
open Polynomial K1 FrobeniusLocator ProximityPrize.Benchmark
theorem eq_on_puncture {deleted : Finset I} {P Q : K[X]} {d : ℕ}
    (hroom : d + deleted.card ≤ 262144) (hP : P.natDegree < d) (hQ : Q.natDegree < d)
    (hn : ∀ i ∉ deleted, P.eval (node i) = Q.eval (node i)) : P = Q := by
  classical
  apply sub_eq_zero.mp
  by_contra hne
  have hcount := Strata.root_nodes_card_le node IRSProfile.domain.injective (P-Q) hne
    (Finset.univ \ deleted) (by
      intro i hi
      rw [eval_sub, hn i (Finset.mem_sdiff.mp hi).2, sub_self])
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    IRSProfile.card_index] at hcount
  have h := natDegree_sub_le P Q
  omega
theorem natDegree_lt_of_degree_lt_pos {P : K[X]} {n : ℕ} (hn : 0 < n) (hd : P.degree < n) :
    P.natDegree < n := by
  by_cases h : P = 0
  · simpa [h] using hn
  exact (natDegree_lt_iff_degree_lt h).mpr hd
private theorem top_amplitude {A : Fin 2 → K[X]} (hp : IsCoprime (A 0) (A 1)) :
    ∃ j, A j ≠ 0 ∧ (A j).natDegree = max (A 0).natDegree (A 1).natDegree := by
  by_cases h0 : A 0 = 0
  · exact ⟨1,hp.ne_zero_or_ne_zero.resolve_left (not_not.mpr h0),by simp [h0]⟩
  by_cases h1 : A 1 = 0
  · exact ⟨0,h0,by simp [h1]⟩
  rcases le_total (A 0).natDegree (A 1).natDegree with h|h
  · exact ⟨1,h1,(max_eq_right h).symm⟩
  · exact ⟨0,h0,(max_eq_left h).symm⟩
private theorem cancel_pair (deleted : Finset I) (w : I → K) (A P : Fin 2 → K[X]) (d s : ℕ)
    (hs : max (A 0).natDegree (A 1).natDegree = s) (hcop : IsCoprime (A 0) (A 1))
    (hpos : 0 < d) (hroom : d+2*s+deleted.card ≤ 262144)
    (hP : ∀ j, (P j).natDegree < d+s)
    (hn : ∀ i ∉ deleted, ∀ j, (P j).eval (node i) = (A j).eval (node i) * w i) :
    ∃ leftLift : K[X], leftLift.natDegree < d ∧ ∀ i ∉ deleted, leftLift.eval (node i) = w i := by
  have hA0 : (A 0).natDegree ≤ s := hs ▸ le_max_left _ _
  have hA1 : (A 1).natDegree ≤ s := hs ▸ le_max_right _ _
  have cross : A 1 * P 0 = A 0 * P 1 := by
    apply eq_on_puncture hroom
    · exact natDegree_mul_le.trans_lt (by have := hP 0; omega)
    · exact natDegree_mul_le.trans_lt (by have := hP 1; omega)
    · intro i hi
      simp only [eval_mul, hn i hi]
      ring
  obtain ⟨j,hj,hjs⟩ := top_amplitude hcop
  obtain ⟨x,y,hxy⟩ := hcop
  let leftLift := x * P 0 + y * P 1
  have eqj : leftLift * A j = P j := by
    unfold leftLift
    fin_cases j
    · change (x*P 0 + y*P 1) * A 0 = P 0
      linear_combination P 0 * hxy - y * cross
    · change (x*P 0 + y*P 1) * A 1 = P 1
      linear_combination P 1 * hxy + x * cross
  refine ⟨leftLift, ?_, ?_⟩
  · by_cases hY : leftLift = 0
    · simpa [hY] using hpos
    have hd := natDegree_mul hY hj
    rw [eqj,hjs,hs] at hd
    have := hP j
    omega
  · intro i hi
    have h := congrArg (eval (node i)) hxy
    simp only [eval_add, eval_mul, eval_one] at h
    simp only [leftLift, eval_add, eval_mul, hn i hi]
    linear_combination w i * h
end
end K1_12
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace K1_12
noncomputable section
open Polynomial K1 FrobeniusLocator
private theorem coprime_factor_of_label {E Q P c a S : K[X]} {z : K} (hz : z ≠ 0)
    (reduced : IsCoprime Q E) (hid : E * P - C z * Q = c * a * S) :
    IsCoprime E c := by
  obtain ⟨x,y,hxy⟩ := reduced
  have inv : C z⁻¹ * C z = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hz, C_1]
  have eqQ : Q = C z⁻¹ * (E * P - c * a * S) := by
    have he : C z * Q = E * P - c * a * S := by linear_combination -hid
    rw [← he, ← mul_assoc, inv, one_mul]
  rw [eqQ] at hxy
  exact ⟨x * C z⁻¹ * P + y, -(x * C z⁻¹ * a * S), by linear_combination hxy⟩
end
end K1_12
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace K1_12_1
noncomputable section
open Polynomial K1 ProximityPrize.Benchmark
section Cyclic
variable {F : Type*} [Field F] {q : ℕ} [ExpChar F q]
private def conjugate (q n : ℕ) [ExpChar F q] (P : F[X]) : F[X] :=
  P.map (iterateFrobenius F q n)
private theorem conjugate_zero (P : F[X]) : conjugate q 0 P = P := by simp [conjugate]
private theorem conjugate_succ (n : ℕ) (P : F[X]) :
    (conjugate q n P).map (frobenius F q) = conjugate q (n + 1) P := by
  rw [conjugate, conjugate, map_map, add_comm n 1,
    iterateFrobenius_add F q 1 n, iterateFrobenius_one]
variable [Fintype F]
private theorem conjugate_six (card : Fintype.card F = q ^ 6) (P : F[X]) :
    conjugate q 6 P = P := by
  have hs : iterateFrobenius F q 6 = RingHom.id F := by
    apply RingHom.ext
    intro x
    change x ^ q ^ 6 = x
    rw [← card]
    exact FiniteField.pow_card x
  rw [conjugate, hs, map_id]
private def weights {S : Type*} [CommSemiring S] (A B : ℕ → S) (j : Fin 6) : S :=
  ∏ i : Fin 6, if i.val < j.val then A i.val else B i.val
private theorem weights_cycle {S : Type*} [CommSemiring S] (f : S →+* S) (A B : ℕ → S)
    (ha : ∀ n, f (A n) = A (n+1)) (hb : ∀ n, f (B n) = B (n+1))
    (hB : B 6 = B 0)
    (h : (∏ i : Fin 6, A i.val) = ∏ i : Fin 6, B i.val) (j : Fin 6) :
    A 0 * f (weights A B j) = B 0 * weights A B (j + 1) := by
  rw [Fin.prod_univ_six, Fin.prod_univ_six] at h
  change A 0 * A 1 * A 2 * A 3 * A 4 * A 5 = B 0 * B 1 * B 2 * B 3 * B 4 * B 5 at h
  fin_cases j <;> simp only [weights, Fin.prod_univ_six, Fin.add_def] <;>
    norm_num [ha, hb, hB]
  all_goals first | ac_rfl | (rw [← h]; ac_rfl)
private theorem frobenius_cycle (card : Fintype.card F = q ^ 6) (x : F) (j : Fin 6) :
    frobenius F q (x ^ q ^ j.val) = x ^ q ^ (j + 1).val := by
  have hpow : frobenius F q (x ^ q ^ j.val) = x ^ q ^ (j.val + 1) := by
    change (x ^ q ^ j.val) ^ q = _
    rw [← pow_mul, pow_succ q j.val]
  rw [hpow]
  by_cases hj : j.val = 5
  · have hj' : j = 5 := Fin.ext hj
    rw [hj', show (5 : Fin 6) + 1 = 0 by decide]
    change x ^ q ^ 6 = x ^ q ^ 0
    rw [pow_zero, pow_one, ← card, FiniteField.pow_card]
  · have hv : (j + 1).val = j.val + 1 := by
      change (j.val + 1) % 6 = j.val + 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [hv]
private theorem descent_nonzero (card : Fintype.card F = q ^ 6) (hq : 1 < q)
    {a b : F[X]} (hb : b ≠ 0)
    (h : (∏ i : Fin 6, conjugate q i.val a) = ∏ i : Fin 6, conjugate q i.val b) :
    ∃ Q : F[X], Q ≠ 0 ∧ a * Q.map (frobenius F q) = b * Q := by
  classical
  let W := weights (fun n => conjugate q n a) (fun n => conjugate q n b)
  let S : Polynomial F[X] := ∑ j : Fin 6, monomial (q ^ j.val) (W j)
  have hinj : Function.Injective (fun j : Fin 6 => q ^ j.val) := by
    intro i j hij
    exact Fin.ext ((pow_right_injective₀ (by omega : 0 < q) (ne_of_gt hq)) hij)
  have hW : W 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    change (if j.val < 0 then conjugate q j.val a else conjugate q j.val b) ≠ 0
    rw [ite_eq_right (Nat.not_lt_zero _)]
    exact (Polynomial.map_ne_zero_iff (iterateFrobenius F q j.val).injective).mpr hb
  have hS : S ≠ 0 := by
    intro hz
    apply hW
    have hc := congrArg (fun P : Polynomial F[X] => P.coeff (q ^ (0 : Fin 6).val)) hz
    simpa only [S, finsetSum_coeff, coeff_monomial, hinj.eq_iff, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, coeff_zero] using hc
  have hdeg : S.natDegree ≤ q ^ 5 := by
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact natDegree_monomial_le _ |>.trans
      (Nat.pow_le_pow_right (by omega) (by omega : j.val ≤ 5))
  obtain ⟨x, hx⟩ : ∃ x : F, S.eval (C x) ≠ 0 := by
    by_contra! hall
    have hroots : (Finset.univ.map ⟨C, C_injective⟩ : Finset F[X]).val ⊆ S.roots := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_def.mpr hy)
      exact (mem_roots hS).mpr (hall x)
    have hcount := card_le_degree_of_subset_roots hroots
    rw [Finset.card_map, Finset.card_univ, card] at hcount
    exact (not_le_of_gt (Nat.pow_lt_pow_right hq (by decide : 5 < 6))) (hcount.trans hdeg)
  refine ⟨S.eval (C x), hx, ?_⟩
  have hev : S.eval (C x) = ∑ j : Fin 6, W j * C (x ^ q ^ j.val) := by
    simp only [S, eval_finsetSum, eval_monomial, C_pow]
  have hstep (j : Fin 6) : a * (W j).map (frobenius F q) = b * W (j+1) := by
    change a * mapRingHom (frobenius F q) (W j) = b * W (j+1)
    simpa only [conjugate_zero] using
      weights_cycle (mapRingHom (frobenius F q)) _ _ (fun n => conjugate_succ n a)
        (fun n => conjugate_succ n b)
        ((conjugate_six card b).trans (conjugate_zero b).symm) h j
  rw [hev, Polynomial.map_sum, Finset.mul_sum, Finset.mul_sum]
  simp_rw [Polynomial.map_mul, map_C, ← mul_assoc, hstep, frobenius_cycle card]
  exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 6)) _ _ (fun _ => rfl)
end Cyclic
theorem denominator {a b : K[X]} (hb : b ≠ 0) (h : sixNorm a = sixNorm b) :
    ∃ Q : K[X], Q ≠ 0 ∧ a * Q.map twist = b * Q ∧ ∀ i, Q.eval (node i) ≠ 0 := by
  classical
  let P (d : ℕ) := ∃ Q : K[X], Q ≠ 0 ∧ a * Q.map twist = b * Q ∧ Q.natDegree = d
  have hex : ∃ d, P d := by
    obtain ⟨Q, hQ, hphase⟩ := descent_nonzero (F := K) (q := p) KoalaBear.card_ext6 (by decide) hb h
    exact ⟨Q.natDegree, Q, hQ, hphase, rfl⟩
  obtain ⟨Q, hQ, hphase, hdeg⟩ := Nat.find_spec hex
  refine ⟨Q, hQ, hphase, ?_⟩
  intro i hi
  let L : K[X] := Polynomial.X (R := K) - C (node i)
  have hL : L ≠ 0 := X_sub_C_ne_zero (node i)
  have hfix : L.map twist = L := by simp [L, K1_12.twist_node]
  obtain ⟨R, hR⟩ := (dvd_iff_isRoot.mpr hi : L ∣ Q)
  have hR0 : R ≠ 0 := fun hz => hQ (by rw [hR, hz, mul_zero])
  have hphaseR : a * R.map twist = b * R := by
    apply mul_left_cancel₀ hL
    rw [hR, Polynomial.map_mul, hfix] at hphase
    rw [← mul_left_comm L a, ← mul_left_comm L b] at hphase
    exact hphase
  have hmin := Nat.find_min' hex (show P R.natDegree from ⟨R, hR0, hphaseR, rfl⟩)
  rw [hR, natDegree_mul hL hR0, show L.natDegree = 1 from natDegree_X_sub_C _] at hdeg
  omega
end
end K1_12_1
end
section
namespace K1_13_3
noncomputable section
open Polynomial K1 K1_13
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent := Fin 4 →₀ ℕ
private def jetWeight (m : Exponent) : ℕ :=
  m.sum (fun i a => (133671 - i.val) * a)
private theorem bankRow_iff {w : I → K} {T : ℕ} {P : Row 4} :
    BankRow w T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight m ≤ T) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2, hc⟩
private def jetEval (S : Geom[X]) : Row 4 →ₗ[Geom] Geom[X] :=
  (MvPolynomial.aeval (jet S)).toLinearMap.restrictScalars Geom
private theorem jetEval_apply (S : Geom[X]) (P : Row 4) : jetEval S P = atJet P S := by
  rfl
private theorem dvd_smul_poly (d P : Geom[X]) (c : Geom) (h : d ∣ P) :
    d ∣ c • P := by
  rw [Polynomial.smul_eq_C_mul]
  exact h.mul_left _
private def bank (w : I → K) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow w T P}
  zero_mem' := by
    apply bankRow_iff.mpr
    simp [Contact, atJet]
  add_mem' {P Q} hP hQ := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    obtain ⟨hQ, hq⟩ := bankRow_iff.mp hQ
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
      have bounds :
          m.sum (fun _ a => a) ≤ 4012 ∧ m.sum (fun i a => i.val * a) ≤ 1650 ∧
            m 3 ≤ 550 ∧ jetWeight m ≤ T := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw⟩ := hP m h
          exact ⟨hb, hj, ht, by omega⟩
        · obtain ⟨hb, hj, ht, hw⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega⟩
      obtain ⟨hb, hj, ht, hw⟩ := bounds
      refine ⟨hb, hj, ht, ?_⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)
private def coefficientArray (T : ℕ) :
    Row 4 →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
  LinearMap.pi fun u =>
    (Polynomial.lcoeff Geom u.2.val).comp
      ((MvPolynomial.lcoeff Geom[X] (Finsupp.equivFunOnFinite.symm (fun i => (u.1 i).val))
        : Row 4 →ₗ[Geom[X]] Geom[X]).restrictScalars Geom)
private instance finiteBank (w : I → K) (T : ℕ) : Module.Finite Geom (bank w T) := by
  classical
  let f : bank w T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank w T).subtype
  have hzero (Q : bank w T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow w T P at hP
    apply Subtype.ext
    change P = 0
    apply MvPolynomial.ext
    intro m
    change _ = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hT : (P.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u : Fin 4 → Fin 4013 := fun i => ⟨m i, Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz
end
end K1_13_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι ν : Type} [Field F] [Fintype ι] [DecidableEq ι]
local instance regularDataDecidable (P : Prop) : Decidable P := Classical.propDecidable P
def RegularLocatorData (σ : ν → F →+* F) (x u v : ι → F)
    (k m t : ℕ) (Γ : Finset (ν → F)) : Prop :=
  ∀ z∈Γ,
    Module.finrank F (LinearMap.ker ((affineLocator σ x u v (m-t) t).map
      (MvPolynomial.eval₂Hom (RingHom.id F) z)).mulVecLin)=1 ∧
    ∃ E : Finset ι, E.card=t ∧
      ((affineLocator σ x u v (m-t) t).map (MvPolynomial.eval₂Hom (RingHom.id F) z)).mulVec
        (fun j : Fin (t+1) => (locator x E).coeff j.val)=0 ∧
      ¬(ExtendsOn x u k (Finset.univ\E) ∧ ExtendsOn x v k (Finset.univ\E))
theorem regular_data_of_bad_slopes [Fintype ν] [DecidableEq ν]
    (σ : ν → F →+* F) (x u v : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ b i, σ b (x i)=x i) (k A m L t : ℕ)
    (hkm : k+m=Fintype.card ι) (hm : m=L+t) (hA : A=k+L) (hkA : k<A)
    (Γ : Finset F) (hbad : ∀ γ∈Γ, Principal.BadSlope x u v k A γ)
    (hnull : ∀ γ∈Γ, Module.finrank F (LinearMap.ker
      (recurrenceMatrixAll (fun b j => σ b (syndrome x (fun i => u i+γ*v i) j)) m t).mulVecLin)=1) :
    RegularLocatorData σ x u v k m t (Γ.image (fun γ b => σ b γ)) := by
  intro z hz
  obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp hz
  have hM : (affineLocator σ x u v (m-t) t).map
      (MvPolynomial.eval₂Hom (RingHom.id F) (fun b => σ b γ))=
      recurrenceMatrixAll (fun b j => σ b (syndrome x (fun i => u i+γ*v i) j)) m t := by
    rw [affineLocator_eval_slope,recurrenceMatrixAll_conjugate]
  refine ⟨by rw [hM]; exact hnull γ hγ,?_⟩
  obtain ⟨T,hT,⟨P,hP,hPv⟩,hTbad⟩ := Principal.bad_slope_exact x hx u v k A hkA γ (hbad γ hγ)
  let E := Finset.univ\T
  have hE : E.card=t := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T),Finset.card_univ,hT]
    omega
  refine ⟨E,hE,?_,?_⟩
  · rw [affineLocator_eval_slope]
    apply conjugate_locator_annihilates σ x _ hx hfixed k (m-t) t (by omega) P hP E hE.le
    intro i hi
    have hiT : i∈T := by simpa only [E,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hi
    exact (hPv i hiT).symm
  · have hcomp : Finset.univ\E=T := by ext i; simp [E]
    rwa [hcomp]
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace K1_1
noncomputable section
open Polynomial Matrix FrobeniusLocator
variable {F : Type} [Field F]
def slice (s : Fin 2 → ℕ → F) (m n : ℕ) : Submodule F F[X] :=
  degreeLT F n ⊓ ⨅ b, ⨅ j : Fin (m+1-n), LinearMap.ker (Principal.recurrenceEval (s b) j.val)
theorem mem_slice (s : Fin 2 → ℕ → F) (m n : ℕ) (P : F[X]) :
    P ∈ slice s m n ↔ P.degree < (n : ℕ) ∧
      ∀ b j, j < m+1-n → Principal.recurrenceEval (s b) j P = 0 := by
  simp only [slice, Submodule.mem_inf, mem_degreeLT, Submodule.mem_iInf,
    LinearMap.mem_ker, Fin.forall_iff]
theorem slice_succ (s : Fin 2 → ℕ → F) (m n : ℕ) :
    slice s m (n+1) = Strata.recurrenceSpace s m n := by
  classical
  ext P
  rw [mem_slice, Strata.mem_recurrenceSpace]
  simp only [Nat.add_sub_add_right]
instance slice_finite (s : Fin 2 → ℕ → F) (m n : ℕ) :
    FiniteDimensional F (slice s m n) :=
  Module.Finite.of_injective (Submodule.inclusion (inf_le_left :
    slice s m n ≤ degreeLT F n)) (Submodule.inclusion_injective _)
theorem slice_mono (s : Fin 2 → ℕ → F) (m : ℕ) : Monotone (slice s m) := by
  intro a b hab P hP
  obtain ⟨hd, hr⟩ := (mem_slice s m a P).mp hP
  exact (mem_slice s m b P).mpr
    ⟨hd.trans_le (by exact_mod_cast hab), fun k j hj => hr k j (by omega)⟩
theorem slice_shift (s : Fin 2 → ℕ → F) (m n : ℕ) :
    (slice s m n).map (Strata.polynomialMul (Polynomial.X : F[X])) ≤ slice s m (n+1) := by
  rintro _ ⟨P, hP, rfl⟩
  obtain ⟨hd, hr⟩ := (mem_slice s m n P).mp hP
  apply (mem_slice s m (n+1) _).mpr
  change ((Polynomial.X : F[X]) * P).degree < ((n+1 : ℕ) : WithBot ℕ) ∧ _
  rw [mul_comm (Polynomial.X : F[X]) P]
  refine ⟨?_, ?_⟩
  · by_cases hP0 : P = 0
    · simp [hP0]
    have h := (natDegree_lt_iff_degree_lt hP0).mpr hd
    have hh := natDegree_mul hP0 (X_ne_zero : (Polynomial.X : F[X]) ≠ 0)
    rw [natDegree_X] at hh
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (P*Polynomial.X).natDegree < n+1 by omega))
  · intro b j hj
    change Principal.recurrenceEval (s b) j (Polynomial.X * P) = 0
    rw [mul_comm (Polynomial.X : F[X]) P, ← pow_one (Polynomial.X : F[X]),
      Principal.recurrenceEval_shift]
    exact hr b (j+1) (by omega)
theorem slice_overlap (s : Fin 2 → ℕ → F) (m n : ℕ) (hn : n < m) :
    slice s m (n+1) ⊓ (slice s m (n+1)).map (Strata.polynomialMul (Polynomial.X : F[X])) =
      (slice s m n).map (Strata.polynomialMul (Polynomial.X : F[X])) := by
  apply le_antisymm
  · rintro _ ⟨hXP, P, hP, rfl⟩
    refine ⟨P, ?_, rfl⟩
    by_cases hP0 : P = 0
    · simp [hP0]
    obtain ⟨_, hr⟩ := (mem_slice s m (n+1) P).mp hP
    change (Polynomial.X * P) ∈ slice s m (n+1) at hXP
    have hXP' : P*Polynomial.X ∈ slice s m (n+1) := by
      simpa only [mul_comm] using hXP
    obtain ⟨hd, hrX⟩ := (mem_slice s m (n+1) (P*Polynomial.X)).mp hXP'
    apply (mem_slice s m n P).mpr
    refine ⟨?_, ?_⟩
    · have hx := mul_ne_zero hP0 (X_ne_zero : (Polynomial.X : F[X]) ≠ 0)
      have h := (natDegree_lt_iff_degree_lt hx).mpr hd
      rw [natDegree_mul hP0 X_ne_zero, natDegree_X] at h
      exact degree_le_natDegree.trans_lt (by exact_mod_cast (show P.natDegree < n by omega))
    · intro b j hj
      by_cases hz : j = 0
      · exact hr b j (by omega)
      · have h := hrX b (j-1) (by omega)
        rw [← pow_one (Polynomial.X : F[X]), Principal.recurrenceEval_shift,
          show j-1+1=j by omega] at h
        exact h
  · exact le_inf (slice_shift s m n) (Submodule.map_mono (slice_mono s m (Nat.le_succ n)))
abbrev sliceDim (s : Fin 2 → ℕ → F) (m n : ℕ) :=
  Module.finrank F (slice s m n)
theorem sliceDim_zero (s : Fin 2 → ℕ → F) (m : ℕ) : sliceDim s m 0 = 0 := by
  have h : slice s m 0 = ⊥ := by
    apply le_bot_iff.mp
    intro P hP
    have hd := ((mem_slice s m 0 P).mp hP).1
    by_contra hn
    have hn' : P ≠ 0 := by simpa using hn
    have := (natDegree_lt_iff_degree_lt hn').mpr hd
    omega
  simp [h]
theorem sliceDim_succ (s : Fin 2 → ℕ → F) (m n : ℕ) :
    sliceDim s m (n+1) = Module.finrank F
      (LinearMap.ker (Principal.recurrenceMatrix s m n).mulVecLin) := by
  classical
  unfold sliceDim
  rw [slice_succ, Strata.recurrenceSpace_finrank]
  have hM : Strata.recurrenceMatrixAll s m n = Principal.recurrenceMatrix s m n := by
    ext i j
    simp [Strata.recurrenceMatrixAll, Principal.recurrenceMatrix, Nat.add_comm]
  rw [hM]
theorem sliceDim_convex (s : Fin 2 → ℕ → F) (m n : ℕ) (hn : n < m) :
    2 * sliceDim s m (n+1) ≤ sliceDim s m (n+2) + sliceDim s m n := by
  let f : F[X] →ₗ[F] F[X] := Strata.polynomialMul (Polynomial.X : F[X])
  have hf : Function.Injective f := fun _ _ h =>
    mul_left_cancel₀ (X_ne_zero : (Polynomial.X : F[X]) ≠ 0) h
  have hmap (k : ℕ) : Module.finrank F ((slice s m k).map f) = sliceDim s m k :=
    (Submodule.equivMapOfInjective f hf _).finrank_eq.symm
  let : FiniteDimensional F ((slice s m (n+1)).map f) :=
    Module.Finite.of_surjective _ (Submodule.equivMapOfInjective f hf _).surjective
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (slice s m (n+1))
    ((slice s m (n+1)).map f)
  have hover : slice s m (n+1) ⊓ (slice s m (n+1)).map f =
      (slice s m n).map f := slice_overlap s m n hn
  rw [hover, hmap, hmap] at hd
  have hle : slice s m (n+1) ⊔ (slice s m (n+1)).map f ≤ slice s m (n+2) :=
    sup_le (slice_mono s m (Nat.le_succ _)) (slice_shift s m (n+1))
  have := Submodule.finrank_mono hle
  unfold sliceDim at *
  omega
theorem principal_of_slice (s : Fin 2 → ℕ → F) (m a t : ℕ)
    (hat : a ≤ t) (htm : t ≤ m) (hne : 0 < sliceDim s m (a+1))
    (hnull : sliceDim s m (t+1) = (t-a)+1) :
    ∃ g : F[X], g ≠ 0 ∧ g.natDegree ≤ a ∧
      ∀ P : F[X], P.natDegree ≤ t →
        ((Principal.recurrenceMatrix s m t).mulVec (fun j => P.coeff j.val) = 0 ↔
          ∃ Q : F[X], Q.natDegree ≤ t-a ∧ P = g*Q) := by
  classical
  obtain ⟨g, hg⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hne
  have hg₀ : g.val ≠ 0 := fun he => hg (Subtype.ext he)
  have hmem : g.val ∈ Strata.recurrenceSpace s m a := by
    rw [← slice_succ]
    exact g.property
  obtain ⟨hdeg, hrec⟩ := (Strata.mem_recurrenceSpace s m a _).mp hmem
  let gBounded : degreeLT F (a+1) := ⟨g.val, mem_degreeLT.mpr hdeg⟩
  have hgK : Principal.InRecurrenceKernel s m a g.val :=
    ⟨Principal.degreeLT_natDegree_le gBounded, hrec⟩
  have hprod (Q : F[X]) (hQ : Q.natDegree ≤ t-a) :
      (Principal.recurrenceMatrix s m t).mulVec (fun j => (g.val*Q).coeff j.val) = 0 := by
    have hQK := Principal.small_kernel_multiples s m a (t-a) (by omega) g.val Q hgK hQ
    rw [show a+(t-a)=t by omega] at hQK
    exact ((Principal.recurrence_kernel_iff_matrix s m t _).mp hQK).2
  rw [sliceDim_succ] at hnull
  refine ⟨g.val, hg₀, hgK.1, fun P hP => ⟨?_, ?_⟩⟩
  · intro hker
    exact Principal.normal_kernel_factorization a (t-a) t (Principal.recurrenceMatrix s m t)
      g.val hg₀ hgK.1 (by omega) hnull
      (fun Q => hprod Q.val (Principal.degreeLT_natDegree_le Q)) P hP hker
  · rintro ⟨Q, hQ, rfl⟩
    exact hprod Q hQ
end
end K1_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace K1_1
noncomputable section
open Polynomial Matrix FrobeniusLocator
variable {F : Type} [Field F]
def IndependentMoments (s : Fin 2 → ℕ → F) (m : ℕ) : Prop :=
  ∃ i j : Fin m, s 0 i.val * s 1 j.val ≠ s 0 j.val * s 1 i.val
theorem sliceDim_last (s : Fin 2 → ℕ → F) (m : ℕ) :
    sliceDim s m (m+1) = m+1 := by
  have h : slice s m (m+1) = degreeLT F (m+1) := by
    ext P
    rw [mem_slice, mem_degreeLT]
    simp
  unfold sliceDim
  rw [h, (degreeLTEquiv F (m+1)).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]
theorem sliceDim_top (s : Fin 2 → ℕ → F) (m : ℕ) (hs : IndependentMoments s m) :
    sliceDim s m m + 2 = m := by
  obtain ⟨i, j, hij⟩ := hs
  cases m with
  | zero => exact Fin.elim0 i
  | succ k =>
    rw [sliceDim_succ]
    let M := Principal.recurrenceMatrix s (k+1) k
    let rows : Fin 2 → Fin 2 × Fin (k+1-k) := fun b => (b, ⟨0, by omega⟩)
    let cols : Fin 2 → Fin (k+1) := ![i,j]
    have hdet : (M.submatrix rows cols).det ≠ 0 := by
      rw [Matrix.det_fin_two, sub_ne_zero]
      change s 0 (0+i.val) * s 1 (0+j.val) ≠ s 0 (0+j.val) * s 1 (0+i.val)
      simpa only [zero_add] using hij
    have hlo := Matrix.rank_submatrix_le M rows cols
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hlo
    have hhi := M.rank_le_card_height
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hhi
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    change M.rank + Module.finrank F (LinearMap.ker M.mulVecLin) = _ at h
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    change Module.finrank F (LinearMap.ker M.mulVecLin) + 2 = k+1
    omega
theorem three_thresholds (d : ℕ → ℕ) (m : ℕ) (hzero : d 0 = 0)
    (hmono : Monotone d)
    (hconv : ∀ n < m, 2*d (n+1) ≤ d (n+2) + d n)
    (hlast : d (m+1) = d m + 3) :
    ∃ a b c : ℕ, a ≤ b ∧ b ≤ c ∧ c ≤ m ∧
      ∀ n ≤ m+1, d n = (n-a)+(n-b)+(n-c) := by
  let Δ (n : ℕ) := d (min n m+1) - d (min n m)
  have hΔm : Δ m = 3 := by simp [Δ, hlast]
  have hΔmono : Monotone Δ := by
    apply monotone_nat_of_le_succ
    intro n
    by_cases hn : n < m
    · simp only [Δ, min_eq_left hn.le, min_eq_left (show n+1≤m by omega)]
      change d (n+1) - d n ≤ d (n+2) - d (n+1)
      have h₀ : d n ≤ d (n+1) := hmono (Nat.le_succ n)
      have h₁ : d (n+1) ≤ d (n+2) := hmono (Nat.le_succ (n+1))
      have hc := hconv n hn
      omega
    · simp [Δ, min_eq_right (show m≤n by omega), min_eq_right (show m≤n+1 by omega)]
  have hΔmax (n : ℕ) : Δ n ≤ 3 := by
    by_cases h : n ≤ m
    · exact (hΔmono h).trans (by rw [hΔm])
    · simpa [Δ, min_eq_right (show m≤n by omega)] using hΔm.le
  have threshold (q : ℕ) (hq : q ≤ 3) :
      ∃ a ≤ m, ∀ n, q ≤ Δ n ↔ a ≤ n := by
    have hex : ∃ n, q ≤ Δ n := ⟨m, by rwa [hΔm]⟩
    refine ⟨Nat.find hex, Nat.find_min' hex (by rwa [hΔm]), fun n => ⟨Nat.find_min' hex, ?_⟩⟩
    intro hn
    exact (Nat.find_spec hex).trans (hΔmono hn)
  obtain ⟨a, ha, hA⟩ := threshold 1 (by decide)
  obtain ⟨b, hb, hB⟩ := threshold 2 (by decide)
  obtain ⟨c, hc, hC⟩ := threshold 3 (by decide)
  have hab := (hA b).mp (Nat.le_trans (by decide : 1 ≤ 2) ((hB b).mpr le_rfl))
  have hbc := (hB c).mp (Nat.le_trans (by decide : 2 ≤ 3) ((hC c).mpr le_rfl))
  refine ⟨a, b, c, hab, hbc, hc, ?_⟩
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    intro hn
    have hstep : Δ n = d (n+1) - d n := by
      simp [Δ, min_eq_left (show n≤m by omega)]
    have hprev := ih (by omega)
    have hle := hmono (Nat.le_succ n)
    have hbound := hΔmax n
    have hA' := hA n
    have hB' := hB n
    have hC' := hC n
    omega
theorem level_profile (s : Fin 2 → ℕ → F) (m : ℕ) (hs : IndependentMoments s m) :
    ∃ a b c : ℕ, a ≤ b ∧ b ≤ c ∧ c ≤ m ∧ a+b+c=2*m+2 ∧
      ∀ n ≤ m+1, sliceDim s m n = (n-a)+(n-b)+(n-c) := by
  have hlast := sliceDim_last s m
  have htop := sliceDim_top s m hs
  have hmono : Monotone (sliceDim s m) :=
    fun _ _ h => Submodule.finrank_mono (slice_mono s m h)
  obtain ⟨a, b, c, hab, hbc, hc, hdim⟩ := three_thresholds (sliceDim s m) m
    (sliceDim_zero s m) hmono (sliceDim_convex s m) (by omega)
  have h := hdim (m+1) le_rfl
  exact ⟨a, b, c, hab, hbc, hc, by omega, hdim⟩
theorem level_of_profile (s : Fin 2 → ℕ → F) (m a b c : ℕ)
    (hdim : ∀ n ≤ m+1, sliceDim s m n = (n-a)+(n-b)+(n-c)) :
    Strata.HasLevelHilbertFunction s m a b c := by
  intro H hH
  obtain ⟨t, ht⟩ : ∃ t, m-H=t+1 := ⟨m-H-1, by omega⟩
  have hrows : H+1 = m-t := by omega
  rw [ht, hrows]
  change Module.finrank F (LinearMap.ker (Principal.recurrenceMatrix s m t).mulVecLin) = _
  rw [← sliceDim_succ]
  exact hdim _ (by omega)
end
end K1_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_14_2_2_4_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
open MvPolynomial (weightedTotalDegree weightedTotalDegree_mul_le weightedTotalDegree_pow_le
  restrictWeightedDegree mem_restrictWeightedDegree_iff_weightedTotalDegree_le)
private abbrev expandSeed : Seeds →+* Ambient := rootIncl.comp rootSeeds
private theorem rootIncl_X (i : Fin 3) :
    rootIncl (MvPolynomial.X i) = MvPolynomial.X (Fin.castLE (by decide) i) := by
  simp [rootIncl]
private theorem row_sum (P : Jet) :
    toJet P = P.sum fun j g =>
      (g.sum fun i c => expandSeed c * MvPolynomial.X 2 ^ i) * MvPolynomial.X 3 ^ j := by
  simp only [toJet, toRoot, coe_eval₂RingHom, eval₂_eq_sum, RingHom.comp_apply,
    Polynomial.sum, map_sum, map_mul, map_pow, expandSeed, rootIncl_X]
  rfl
private def substitute {F : Type} [Field F] [Algebra FX F] (x : Fin 4 → Plane F) : Ambient →+* Plane F :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX F)) x
private theorem seed_substitution {F : Type} [Field F] [Algebra FX F] (x : Fin 4 → Plane F) (c : Seeds) :
    substitute x (expandSeed c) =
      MvPolynomial.aeval (fun i : Fin 2 => x (Fin.castLE (by decide) i))
        (MvPolynomial.map (algebraMap FX F) c) := by
  have he : (substitute x).comp expandSeed =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX F))
        (fun i : Fin 2 => x (Fin.castLE (by decide) i)) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [substitute, expandSeed, rootSeeds, rootIncl]
    · intro i
      fin_cases i <;> simp [substitute, expandSeed, rootSeeds, rootIncl]
  rw [← RingHom.comp_apply, he, MvPolynomial.aeval_def]
  apply (MvPolynomial.eval₂Hom_map_hom (algebraMap FX F) _ MvPolynomial.C c).symm
private theorem row_weight_le {F : Type} [Field F] [Algebra FX F] (w : Fin 2 → ℕ) (x : Fin 4 → Plane F)
    {P : Jet} {s : Shape} (hP : RowCaps P s) (a b c D : ℕ)
    (hseed : ∀ i : Fin 2, weightedTotalDegree w (x (Fin.castLE (by decide) i)) ≤ a)
    (hy : weightedTotalDegree w (x 2) ≤ b) (hv : weightedTotalDegree w (x 3) ≤ c)
    (hcap : ∀ j i, i + j ≤ s.B → j ≤ s.J → a * s.U + i * b + j * c ≤ D) :
    weightedTotalDegree w (substitute x (toJet P)) ≤ D := by
  classical
  have hcoeff (q : Seeds) : weightedTotalDegree w (substitute x (expandSeed q)) ≤
      a * q.totalDegree := by
    rw [seed_substitution]
    refine (MvPolynomial.weightedTotalDegree_aeval_le_of_le (fun _ : Fin 2 => a) w _ _
      hseed).trans ?_
    apply Finset.sup_le
    intro m hm
    have hdeg := MvPolynomial.le_totalDegree (MvPolynomial.support_map_subset _ _ hm)
    have hweight : Finsupp.weight (fun _ : Fin 2 => a) m = a * m.degree := by
      simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
        Finset.mul_sum, Nat.mul_comm]
    rw [hweight]
    exact Nat.mul_le_mul_left _ hdeg
  rw [row_sum]
  simp only [Polynomial.sum, map_sum, map_mul, map_pow, substitute, MvPolynomial.eval₂Hom_X']
  change weightedTotalDegree w (∑ j ∈ P.support,
    (∑ i ∈ (P.coeff j).support, substitute x (expandSeed ((P.coeff j).coeff i)) * x 2 ^ i) *
      x 3 ^ j) ≤ D
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sum_mem
  intro j _
  rw [Finset.sum_mul]
  apply Submodule.sum_mem
  intro i hi
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  obtain ⟨hij, hj, hseeddeg⟩ := hP j i (Polynomial.mem_support_iff.mp hi)
  refine (weightedTotalDegree_mul_le _ _ _).trans (le_trans ?_ (hcap j i hij hj))
  exact Nat.add_le_add
    ((weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add
      ((hcoeff _).trans (Nat.mul_le_mul_left _ hseeddeg))
      ((weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ hy))))
    ((weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ hv))
private theorem weight_X {F : Type} [Field F] (w : Fin 2 → ℕ) (i : Fin 2) :
    weightedTotalDegree w (MvPolynomial.X i : Plane F) = w i := by
  rw [MvPolynomial.X, MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero,
    Finsupp.weight_single, one_smul]
private theorem weight_line {F : Type} [Field F] (w : Fin 2 → ℕ) (a b : F) (i : Fin 2) :
    weightedTotalDegree w (MvPolynomial.C a - MvPolynomial.C b * MvPolynomial.X i : Plane F) ≤ w i := by
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · simp
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans (by simp [weight_X])
private abbrev seedValues : Fin 4 → Plane SeedField :=
  ![MvPolynomial.C (generic 0), MvPolynomial.C (generic 1), MvPolynomial.X 0, MvPolynomial.X 1]
private abbrev jetValues : Fin 4 → Plane SeedField :=
  ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C (generic 0), MvPolynomial.C (generic 1)]
theorem seedSlice_total {P : Jet} {s : Shape} (hP : RowCaps P s) :
    (mapGenericSeed (toJet P)).totalDegree ≤ s.B := by
  rw [← MvPolynomial.weightedTotalDegree_one]
  exact row_weight_le (F := SeedField) 1 seedValues hP 0 1 1 s.B
    (fun i => by fin_cases i <;> simp)
    (by simp [weight_X]) (by simp [weight_X]) (fun j i hij _ => by simpa using hij)
theorem seedSlice_derivative {P : Jet} {s : Shape} (hP : RowCaps P s) :
    (mapGenericSeed (toJet P)).degreeOf 1 ≤ s.J := by
  rw [← MvPolynomial.weightedTotalDegree_piSingle]
  exact row_weight_le (F := SeedField) (Pi.single 1 1) seedValues hP 0 0 1 s.J
    (fun i => by fin_cases i <;> simp)
    (by simp [MvPolynomial.degreeOf_X]) (by simp) (fun j i _ hj => by simpa using hj)
theorem jetSlice_total {P : Jet} {s : Shape} (hP : RowCaps P s) :
    (mapGenericJets (toJet P)).totalDegree ≤ s.U := by
  rw [← MvPolynomial.weightedTotalDegree_one]
  exact row_weight_le (F := SeedField) 1 jetValues hP 1 0 0 s.U
    (fun i => by fin_cases i <;> simp [weight_X])
    (by simp) (by simp) (by simp)
theorem lineSlice_seed (mixed : Bool) {P : Jet} {s : Shape} (hP : RowCaps P s) :
    (lineMap mixed (toJet P)).degreeOf 0 ≤ s.U := by
  rw [← MvPolynomial.weightedTotalDegree_piSingle]
  refine row_weight_le (F := SectionField) (Pi.single 0 1) (lineValues mixed) hP 1 0 0 s.U ?_ ?_ ?_ (by simp)
  · intro i
    fin_cases i
    · exact (weight_line (Pi.single 0 1) _ _ 0).trans (by simp)
    · simp [lineValues]
  · cases mixed
    · simp [lineValues]
    · exact (weight_line (Pi.single 0 1) _ _ 1).trans (by simp)
  · simp [lineValues, MvPolynomial.degreeOf_X]
theorem ordinateSlice_derivative {P : Jet} {s : Shape} (hP : RowCaps P s) :
    (lineMap false (toJet P)).degreeOf 1 ≤ s.J := by
  rw [← MvPolynomial.weightedTotalDegree_piSingle]
  refine row_weight_le (F := SectionField) (Pi.single 1 1) (lineValues false) hP 0 0 1 s.J ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact (weight_line (Pi.single 1 1) _ _ 0).trans (by simp)
    · simp [lineValues, MvPolynomial.degreeOf_X]
  · simp [lineValues]
  · simp [lineValues]
  · intro j i _ hj
    simpa using hj
theorem mixedSlice_jet {P : Jet} {s : Shape} (hP : RowCaps P s) :
    (lineMap true (toJet P)).degreeOf 1 ≤ s.B := by
  rw [← MvPolynomial.weightedTotalDegree_piSingle]
  refine row_weight_le (F := SectionField) (Pi.single 1 1) (lineValues true) hP 0 1 1 s.B ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact (weight_line (Pi.single 1 1) _ _ 0).trans (by simp)
    · simp [lineValues, MvPolynomial.degreeOf_X]
  · exact (weight_line (Pi.single 1 1) _ _ 1).trans (by simp)
  · simp [lineValues]
  · intro j i hij _
    simpa using hij
end
end K1_14_2_2_4_5
end
section
set_option autoImplicit false
namespace K1_14_2_2_4_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4
def c1 : Prop :=
  ∀ (F : Type) [Field F] (φ : Ambient →+* Plane F) (k : Fin 4),
    SectionChart F φ k →
    ∀ (P Q : Jet) (S : Finset (Ideal Ambient)) (d : ℕ),
      Module.Finite F (PlaneSection φ (RowIdeal P Q)) → 0 < d →
      (∀ I ∈ S, ∃ hI : Active I,
        sectionDegree I k ≠ 0 → (d : ℕ∞) ≤ localLength P Q I hI.prime) →
      d * mass S k ≤ Module.finrank F (PlaneSection φ (RowIdeal P Q))
def c2 : Prop :=
  SectionChart SeedField mapGenericSeed 0 ∧ SectionChart SeedField mapGenericJets 3
def c3 : Prop :=
  SectionChart SectionField (lineMap false) 1 ∧
    SectionChart SectionField (lineMap true) 2
def c4 : Prop :=
  ∀ (F : Type) [Field F] (f g : Plane F) (a b c e : ℕ),
    IsRelPrime f g → f.degreeOf 0 ≤ a → f.degreeOf 1 ≤ b →
    g.degreeOf 0 ≤ c → g.degreeOf 1 ≤ e →
    Module.Finite F (PlaneIntersection f g) ∧
      Module.finrank F (PlaneIntersection f g) ≤ a * e + c * b
def c5 : Prop :=
  ∀ (F : Type) [Field F] (f g : Plane F) (b j c e : ℕ),
    IsRelPrime f g → j ≤ b → e ≤ c →
    f.totalDegree ≤ b → f.degreeOf 1 ≤ j → g.totalDegree ≤ c → g.degreeOf 1 ≤ e →
    Module.Finite F (PlaneIntersection f g) ∧
      Module.finrank F (PlaneIntersection f g) ≤ b * e + c * j - j * e
private theorem map_rowIdeal {F : Type} [Field F] (φ : Ambient →+* Plane F) (P Q : Jet) :
    (RowIdeal P Q).map φ = Ideal.span {φ (toJet P), φ (toJet Q)} := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    K1_14_2_2_4.c5 := by
  intro P Q s t S k d _ _ hrel hs ht hP hQ hd hlocal
  have apply_cap {F : Type} [Field F] (φ : Ambient →+* Plane F) (k : Fin 4)
      (chart : SectionChart F φ k)
      (cap : Module.Finite F (PlaneIntersection (φ (toJet P)) (φ (toJet Q))) ∧
        Module.finrank F (PlaneIntersection (φ (toJet P)) (φ (toJet Q))) ≤ pairCap s t k)
      (hlocal : ∀ I ∈ S, ∃ hI : Active I,
        sectionDegree I k ≠ 0 → (d : ℕ∞) ≤ localLength P Q I hI.prime) :
      d * mass S k ≤ pairCap s t k := by
    obtain ⟨hfinite, hdim⟩ := cap
    have hmap := map_rowIdeal φ P Q
    have hfinite' : Module.Finite F (PlaneSection φ (RowIdeal P Q)) := by
      change Module.Finite F (Plane F ⧸ (RowIdeal P Q).map φ)
      rwa [hmap]
    refine (h1 F φ k chart P Q S d hfinite' hd hlocal).trans ?_
    change Module.finrank F (Plane F ⧸ (RowIdeal P Q).map φ) ≤ pairCap s t k
    rwa [hmap]
  fin_cases k
  · apply apply_cap mapGenericSeed 0 h2.1 _ hlocal
    exact h5 SeedField _ _ s.B s.J t.B t.J (h2.1.relPrime _ _ hrel) hs ht
      (seedSlice_total hP) (seedSlice_derivative hP) (seedSlice_total hQ) (seedSlice_derivative hQ)
  · apply apply_cap (lineMap false) 1 h3.1 _ hlocal
    exact h4 SectionField _ _ s.U s.J t.U t.J (h3.1.relPrime _ _ hrel)
      (lineSlice_seed false hP) (ordinateSlice_derivative hP)
      (lineSlice_seed false hQ) (ordinateSlice_derivative hQ)
  · apply apply_cap (lineMap true) 2 h3.2 _ hlocal
    exact h4 SectionField _ _ s.U s.B t.U t.B (h3.2.relPrime _ _ hrel)
      (lineSlice_seed true hP) (mixedSlice_jet hP) (lineSlice_seed true hQ) (mixedSlice_jet hQ)
  · apply apply_cap mapGenericJets 3 h2.2 _ hlocal
    have htotalP := jetSlice_total hP
    have htotalQ := jetSlice_total hQ
    obtain ⟨hfinite, hdim⟩ := h5 SeedField _ _ s.U s.U t.U t.U (h2.2.relPrime _ _ hrel)
      le_rfl le_rfl htotalP ((MvPolynomial.degreeOf_le_totalDegree _ 1).trans htotalP)
      htotalQ ((MvPolynomial.degreeOf_le_totalDegree _ 1).trans htotalQ)
    refine ⟨hfinite, ?_⟩
    change _ ≤ s.U * t.U
    simpa [Nat.mul_comm t.U s.U] using hdim
end
end K1_14_2_2_4_5
end
section
set_option autoImplicit false
namespace K1_14_2_2_4_5_3
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4_5
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev WithSlopes := MvPolynomial Bool Ambient
private abbrev Params := MvPolynomial (Fin 4) FX
private abbrev BeforeLocalization := MvPolynomial (Fin 2) Params
private abbrev Target := Plane SectionField
private def toChart {R : Type} [CommRing R] (mixed : Bool) :
    MvPolynomial Bool (MvPolynomial (Fin 4) R) →+*
      MvPolynomial (Fin 2) (MvPolynomial (Fin 4) R) :=
  eval₂Hom
    (eval₂Hom (C.comp C)
      ![C (MvPolynomial.X 2) - C (MvPolynomial.X 0) * MvPolynomial.X 0, MvPolynomial.X 0,
        if mixed then C (MvPolynomial.X 3) - C (MvPolynomial.X 1) * MvPolynomial.X 1
        else C (MvPolynomial.X 3), MvPolynomial.X 1])
    (fun i => if i then C (MvPolynomial.X 1) else C (MvPolynomial.X 0))
private def fromChart {R : Type} [CommRing R] (mixed : Bool) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin 4) R) →+*
      MvPolynomial Bool (MvPolynomial (Fin 4) R) :=
  eval₂Hom
    (eval₂Hom (C.comp C)
      ![MvPolynomial.X false, MvPolynomial.X true,
        C (MvPolynomial.X 0) + MvPolynomial.X false * C (MvPolynomial.X 1),
        if mixed then C (MvPolynomial.X 2) + MvPolynomial.X true * C (MvPolynomial.X 3)
        else C (MvPolynomial.X 2)])
    ![C (MvPolynomial.X 1), C (MvPolynomial.X 3)]
private def shear {R : Type} [CommRing R] (mixed : Bool) :
    MvPolynomial Bool (MvPolynomial (Fin 4) R) ≃+*
      MvPolynomial (Fin 2) (MvPolynomial (Fin 4) R) := by
  refine RingEquiv.ofRingHom (toChart mixed) (fromChart mixed) ?_ ?_
  · apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro a
        simp [toChart, fromChart]
      · intro i
        fin_cases i <;> cases mixed <;> simp [toChart, fromChart]
    · intro i
      fin_cases i <;> simp [toChart, fromChart]
  · apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro a
        simp [toChart, fromChart]
      · intro i
        fin_cases i <;> cases mixed <;>
          simp [toChart, fromChart, -MvPolynomial.coe_eval₂Hom]
    · intro i
      cases i <;> simp [toChart, fromChart]
private abbrev denominators : Submonoid BeforeLocalization :=
  (nonZeroDivisors Params).map C
private abbrev extendedMap (mixed : Bool) : WithSlopes →+* Target :=
  (algebraMap BeforeLocalization Target).comp (shear mixed).toRingHom
private theorem lineMap_eq (mixed : Bool) :
    lineMap mixed = (extendedMap mixed).comp C := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change lineMap mixed (C a) =
      MvPolynomial.map (algebraMap Params SectionField) (toChart mixed (C (C a)))
    simp [lineMap, toChart]
    rfl
  · intro i
    change lineMap mixed (MvPolynomial.X i) =
      MvPolynomial.map (algebraMap Params SectionField) (toChart mixed (C (MvPolynomial.X i)))
    fin_cases i <;> cases mixed <;>
      simp [lineMap, lineValues, toChart, sliceParameter]
private theorem polynomial_prime {R : Type} [CommRing R] (I : Ideal R) (hI : I.IsPrime) :
    (I.map (C : R →+* MvPolynomial Bool R)).IsPrime ∧
      (I.map (C : R →+* MvPolynomial Bool R)).comap C = I := by
  let _ : I.IsPrime := hI
  let q : MvPolynomial Bool R →+* MvPolynomial Bool (R ⧸ I) :=
    MvPolynomial.map (Ideal.Quotient.mk I)
  have hker : RingHom.ker q = I.map C := calc
    RingHom.ker q = (RingHom.ker (Ideal.Quotient.mk I)).map C :=
      MvPolynomial.ker_map (σ := Bool) (Ideal.Quotient.mk I)
    _ = I.map C := by rw [Ideal.mk_ker]
  rw [← hker]
  constructor
  · rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_isPrime q ⊥
  · rw [RingHom.comap_ker]
    have hq : q.comp C = C.comp (Ideal.Quotient.mk I) := by
      apply RingHom.ext
      intro a
      simp [q]
    rw [hq, RingHom.ker_comp_of_injective _ (MvPolynomial.C_injective _ _), Ideal.mk_ker]
private theorem flat_and_prime (mixed : Bool) :
    @Module.Flat Ambient Target _ _ (@Algebra.toModule _ _ _ _ (lineMap mixed).toAlgebra) ∧
    (∀ I : Ideal Ambient, I.IsPrime → I.map (lineMap mixed) ≠ ⊤ →
      (I.map (lineMap mixed)).IsPrime ∧ (I.map (lineMap mixed)).comap (lineMap mixed) = I) := by
  let slopeAlgebra : Algebra WithSlopes Target := (extendedMap mixed).toAlgebra
  let _ : Algebra WithSlopes Target := slopeAlgebra
  let S : Submonoid WithSlopes := denominators.comap (shear mixed).toMulEquiv.toMonoidHom
  let _ : IsLocalization S Target := by
    apply IsLocalization.of_ringEquiv_left (shear mixed) (M₁ := denominators)
    · change S.map (shear mixed).toMulEquiv.toMonoidHom = denominators
      exact Submonoid.map_comap_eq_of_surjective (shear mixed).surjective _
    · intro x
      rfl
  constructor
  · let ambientAlgebra : Algebra Ambient Target := (lineMap mixed).toAlgebra
    let _ : Algebra Ambient Target := ambientAlgebra
    let _ : Module Ambient Target := @Algebra.toModule _ _ _ _ ambientAlgebra
    let _ : Module WithSlopes Target := @Algebra.toModule _ _ _ _ slopeAlgebra
    let _ : IsScalarTower Ambient WithSlopes Target :=
      IsScalarTower.of_algebraMap_eq' (lineMap_eq mixed)
    let _ : Module.Flat WithSlopes Target := IsLocalization.flat Target S
    exact Module.Flat.trans Ambient WithSlopes Target
  · intro I hI hproper
    rw [lineMap_eq, ← Ideal.map_map] at hproper ⊢
    rw [← Ideal.comap_comap]
    obtain ⟨hprime, hcontract⟩ := polynomial_prime I hI
    let J : Ideal WithSlopes := I.map C
    have hd : Disjoint (S : Set WithSlopes) (J : Set WithSlopes) :=
      (IsLocalization.map_algebraMap_ne_top_iff_disjoint S Target J).mp hproper
    exact ⟨IsLocalization.isPrime_of_isPrime_disjoint S Target J hprime hd,
      (congrArg (fun D : Ideal WithSlopes => D.comap C)
        (IsLocalization.under_map_of_isPrime_disjoint S Target hprime hd)).trans hcontract⟩
private theorem relPrime_of_prime_over {R T : Type} [CommRing R] [CommRing T]
    [IsDomain R] [IsDomain T] [UniqueFactorizationMonoid R] [UniqueFactorizationMonoid T]
    (φ : R →+* T)
    (hφ : ∀ I : Ideal R, I.IsPrime → I.map φ ≠ ⊤ →
      (I.map φ).IsPrime ∧ (I.map φ).comap φ = I)
    (a b : R) (hab : IsRelPrime a b) : IsRelPrime (φ a) (φ b) := by
  have hinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    simpa using (hφ ⊥ Ideal.isPrime_bot (by simp)).2
  by_cases ha : a = 0
  · subst a
    simp only [map_zero, isRelPrime_zero_left] at hab ⊢
    exact hab.map φ
  have ha' : φ a ≠ 0 := fun h => ha (hinj (h.trans (map_zero φ).symm))
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors ha').mpr
  intro d hda hdb hd
  have liftFactor (x : R) : x ≠ 0 → d ∣ φ x →
      ∃ p : R, Prime p ∧ p ∣ x ∧ d ∣ φ p := by
    induction x using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => simp
    | h₂ u hu => exact fun _ hdu => (hd.not_isUnit (isUnit_of_dvd_unit hdu (hu.map φ))).elim
    | h₃ x p hx hp ih =>
      intro _ hdp
      rw [map_mul] at hdp
      rcases hd.dvd_mul.mp hdp with h | h
      · exact ⟨p, hp, dvd_mul_right p x, h⟩
      · obtain ⟨q, hq, hqx, hdq⟩ := ih hx h
        exact ⟨q, hq, hqx.trans (dvd_mul_left x p), hdq⟩
  obtain ⟨p, hp, hpa, hdp⟩ := liftFactor a ha hda
  have hproper : (Ideal.span {p}).map φ ≠ ⊤ := by
    intro htop
    rw [Ideal.map_span, Set.image_singleton] at htop
    exact hd.not_isUnit (isUnit_of_dvd_unit hdp (Ideal.span_singleton_eq_top.mp htop))
  obtain ⟨hprime, hcontract⟩ := hφ _ (Ideal.isPrime_span_singleton_of_prime hp) hproper
  have hp' : φ p ≠ 0 := fun h => hp.ne_zero (hinj (h.trans (map_zero φ).symm))
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_prime hp'] at hprime
  have hpb : φ p ∣ φ b :=
    ((hd.dvd_prime_iff_associated hprime).mp hdp).dvd'.trans hdb
  apply hp.not_isUnit (hab hpa ?_)
  rw [← Ideal.mem_span_singleton, ← hcontract, Ideal.mem_comap, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton]
  exact hpb
private theorem elim_eq_lineMap (mixed : Bool) :
    (K1_14_2_2_2_5.lineElim mixed).toRingHom.comp sectionBase = lineMap mixed := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [K1_14_2_2_2_5.lineElim, sectionBase, lineMap, MvPolynomial.algebraMap_eq]
  · intro i
    fin_cases i <;> cases mixed <;>
      simp [K1_14_2_2_2_5.lineElim, sectionBase, lineMap, lineValues]
private theorem finite_rank_of_equiv {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [Module SectionField A] [Module SectionField B] (e : A ≃ₗ[SectionField] B)
    (h : Module.Finite SectionField A) :
    Module.Finite SectionField B ∧ Module.finrank SectionField B = Module.finrank SectionField A :=
  letI := h
  ⟨Module.Finite.of_surjective e.toLinearMap e.surjective, e.finrank_eq.symm⟩
theorem proof : K1_14_2_2_4_5.c3 := by
  obtain ⟨hf₁, hp₁⟩ := flat_and_prime false
  obtain ⟨hf₂, hp₂⟩ := flat_and_prime true
  refine ⟨⟨hf₁, ?_, hp₁, relPrime_of_prime_over _ hp₁⟩,
    ⟨hf₂, ?_, hp₂, relPrime_of_prime_over _ hp₂⟩⟩
  · intro I hI
    have e := (K1_14_2_2_2_5.ordinateEquiv I).toLinearEquiv
    have h := finite_rank_of_equiv e hI.ordinate_finite
    change Module.Finite SectionField (PlaneSection
      ((K1_14_2_2_2_5.lineElim false).toRingHom.comp sectionBase) I) ∧
      Module.finrank SectionField (PlaneSection
        ((K1_14_2_2_2_5.lineElim false).toRingHom.comp sectionBase) I) =
        Module.finrank SectionField (OverOrdinate I) at h
    rwa [elim_eq_lineMap] at h
  · intro I hI
    have e := (K1_14_2_2_2_5.mixedEquiv I).toLinearEquiv
    have h := finite_rank_of_equiv e hI.mixed_finite
    change Module.Finite SectionField (PlaneSection
      ((K1_14_2_2_2_5.lineElim true).toRingHom.comp sectionBase) I) ∧
      Module.finrank SectionField (PlaneSection
        ((K1_14_2_2_2_5.lineElim true).toRingHom.comp sectionBase) I) =
        Module.finrank SectionField (OverMixed I) at h
    rwa [elim_eq_lineMap] at h
end
end K1_14_2_2_4_5_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_4_5_4
noncomputable section
open K1_14_2_2_4_5 MvPolynomial
private abbrev BoxPlane (F : Type) [Field F] := MvPolynomial (Option (Fin 1)) F
private abbrev box (F : Type) [Field F] :=
  restrictBidegree (Fin 1) F
variable {F : Type} [Field F]
private theorem mem_box {p : BoxPlane F} {i j : ℕ} :
    p ∈ box F i j ↔ p.degreeOf none ≤ i ∧ p.degreeOf (some 0) ≤ j := by
  simp only [mem_restrictBidegree, degreeOf_le_iff, Finsupp.degree_eq_sum, Fin.sum_univ_one,
    Finsupp.some_apply]
  exact ⟨fun h => ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩,
    fun h m hm => ⟨h.1 m hm, h.2 m hm⟩⟩
private theorem finrank_box (i j : ℕ) :
    Module.finrank F (box F i j) = (i + 1) * (j + 1) := by
  simp [box, finrank_restrictBidegree, Nat.card_eq_fintype_card]
private abbrev multiples (p : BoxPlane F) (i j : ℕ) : Submodule F (BoxPlane F) :=
  (box F i j).map (LinearMap.mulLeft F p)
private theorem finrank_multiples {p : BoxPlane F} (hp : p ≠ 0) (i j : ℕ) :
    Module.finrank F (multiples p i j) = (i + 1) * (j + 1) := by
  rw [multiples, ← LinearMap.range_domRestrict,
    LinearMap.finrank_range_of_inj, finrank_box]
  intro u v huv
  change p * (u : BoxPlane F) = p * (v : BoxPlane F) at huv
  exact Subtype.ext (mul_left_cancel₀ hp huv)
private theorem multiples_le_box {p : BoxPlane F} (i j : ℕ) :
    multiples p i j ≤ box F (p.degreeOf none + i) (p.degreeOf (some 0) + j) := by
  rintro _ ⟨q, hq, rfl⟩
  exact mul_mem_restrictBidegree (mem_box.mpr ⟨le_rfl, le_rfl⟩) hq
private theorem overlap_le {f g : BoxPlane F}
    (hg : g ≠ 0) (hrel : IsRelPrime f g) (i j : ℕ) :
    multiples f (g.degreeOf none + i) (g.degreeOf (some 0) + j) ⊓
      multiples g (f.degreeOf none + i) (f.degreeOf (some 0) + j) ≤
      multiples (f * g) i j := by
  let : UniqueFactorizationMonoid F := PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : UniqueFactorizationMonoid (BoxPlane F) :=
    MvPolynomial.uniqueFactorizationMonoid (Option (Fin 1))
  rintro p ⟨⟨u, hu, hpu⟩, ⟨v, _, hpv⟩⟩
  change f * u = p at hpu
  change g * v = p at hpv
  have hd : g ∣ f * u := ⟨v, hpu.trans hpv.symm⟩
  have hd' := UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors hg
    (fun h₁ h₂ hprime => hprime.not_isUnit (hrel h₂ h₁)) hd
  obtain ⟨w, rfl⟩ := hd'
  have hw : w ∈ box F i j := by
    by_cases hz : w = 0
    · simp [hz]
    rcases mem_box.mp hu with ⟨h₀, h₁⟩
    rw [degreeOf_mul_eq hg hz] at h₀
    rw [degreeOf_mul_eq hg hz] at h₁
    exact mem_box.mpr ⟨Nat.le_of_add_le_add_left h₀, Nat.le_of_add_le_add_left h₁⟩
  exact ⟨w, hw, (mul_assoc f g w).trans hpu⟩
private theorem box_image_le {f g : BoxPlane F} (hf : f ≠ 0) (hg : g ≠ 0)
    (hrel : IsRelPrime f g) (i j : ℕ) :
    Module.finrank F (quotientBidegreeLE (Ideal.span {f, g})
      (f.degreeOf none + g.degreeOf none + i) (f.degreeOf (some 0) + g.degreeOf (some 0) + j)) ≤
      f.degreeOf none * g.degreeOf (some 0) + g.degreeOf none * f.degreeOf (some 0) := by
  let a := f.degreeOf none
  let b := f.degreeOf (some 0)
  let c := g.degreeOf none
  let e := g.degreeOf (some 0)
  let W := box F (a + c + i) (b + e + j)
  let U := multiples f (c + i) (e + j)
  let V := multiples g (a + i) (b + j)
  let I : Ideal (BoxPlane F) := Ideal.span {f, g}
  let T := quotientBidegreeLE I (a + c + i) (b + e + j)
  let π := (Ideal.Quotient.mkₐ F I).toLinearMap.domRestrict W
  have hUW : U ≤ W := by
    simpa only [U, W, a, b, c, e, Nat.add_assoc] using
      (multiples_le_box (p := f) (c + i) (e + j))
  have hVW : V ≤ W := by
    simpa only [V, W, a, b, c, e, Nat.add_left_comm, Nat.add_assoc] using
      (multiples_le_box (p := g) (a + i) (b + j))
  have hW : U ⊔ V ≤ W := sup_le hUW hVW
  have hker : (U ⊔ V).comap W.subtype ≤ LinearMap.ker π := by
    have hUI : U ≤ I.restrictScalars F := by
      rintro _ ⟨p, _, rfl⟩
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have hVI : V ≤ I.restrictScalars F := by
      rintro _ ⟨p, _, rfl⟩
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    intro x hx
    have hx' : (x : BoxPlane F) ∈ U ⊔ V := hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((sup_le hUI hVI) hx')
  have hk := Submodule.finrank_mono hker
  rw [(Submodule.comapSubtypeEquivOfLe hW).finrank_eq] at hk
  have hover := Submodule.finrank_mono (overlap_le hg hrel i j)
  rw [finrank_multiples (mul_ne_zero hf hg)] at hover
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [show U = multiples f (c + i) (e + j) from rfl,
    show V = multiples g (a + i) (b + j) from rfl,
    finrank_multiples hf, finrank_multiples hg] at hsum
  have hrank := π.finrank_range_add_finrank_ker
  rw [show LinearMap.range π = T from LinearMap.range_domRestrict _ _] at hrank
  change _ + _ = Module.finrank F (box F (a + c + i) (b + e + j)) at hrank
  rw [finrank_box] at hrank
  have htotal : Module.finrank F T + Module.finrank F (U ⊔ V : Submodule F (BoxPlane F)) ≤
      (a + c + i + 1) * (b + e + j + 1) :=
    (Nat.add_le_add_left hk (Module.finrank F T)).trans_eq hrank
  have hpair : (c + i + 1) * (e + j + 1) + (a + i + 1) * (b + j + 1) ≤
      Module.finrank F (U ⊔ V : Submodule F (BoxPlane F)) + (i + 1) * (j + 1) :=
    hsum.symm.trans_le (Nat.add_le_add_left hover _)
  have harith :
      (a + c + i + 1) * (b + e + j + 1) + (i + 1) * (j + 1) =
      (c + i + 1) * (e + j + 1) + (a + i + 1) * (b + j + 1) + (a * e + c * b) := by
    ring
  change Module.finrank F T ≤ a * e + c * b
  omega
private theorem plane_bound (f g : BoxPlane F) (hrel : IsRelPrime f g) :
    Module.Finite F (BoxPlane F ⧸ Ideal.span {f, g}) ∧
    Module.finrank F (BoxPlane F ⧸ Ideal.span {f, g}) ≤
      f.degreeOf none * g.degreeOf (some 0) + g.degreeOf none * f.degreeOf (some 0) := by
  classical
  let I : Ideal (BoxPlane F) := Ideal.span {f, g}
  let Q := BoxPlane F ⧸ I
  let k := f.degreeOf none * g.degreeOf (some 0) + g.degreeOf none * f.degreeOf (some 0)
  change Module.Finite F Q ∧ Module.finrank F Q ≤ k
  have hfI : f ∈ I := Ideal.subset_span (by simp)
  have hgI : g ∈ I := Ideal.subset_span (by simp)
  by_cases ht : I = ⊤
  · let : Subsingleton Q := Ideal.Quotient.subsingleton_iff.mpr ht
    exact ⟨Module.Finite.of_injective (0 : Q →ₗ[F] F) (fun x y _ => Subsingleton.elim x y),
      (Module.finrank_eq_zero_of_subsingleton F Q).le.trans (Nat.zero_le k)⟩
  have hf : f ≠ 0 := by
    intro hz
    rw [hz] at hrel
    exact ht (Ideal.eq_top_of_isUnit_mem I hgI (isRelPrime_zero_left.mp hrel))
  have hg : g ≠ 0 := by
    intro hz
    rw [hz] at hrel
    exact ht (Ideal.eq_top_of_isUnit_mem I hfI (isRelPrime_zero_right.mp hrel))
  have hdim (n : ℕ) (x : Fin n → Q) (hx : LinearIndependent F x) : n ≤ k := by
    choose p hp using fun t => (Ideal.Quotient.mk_surjective (I := I) (x t))
    let i := Finset.univ.sup fun t : Fin n => (p t).degreeOf none
    let j := Finset.univ.sup fun t : Fin n => (p t).degreeOf (some 0)
    let A := f.degreeOf none + g.degreeOf none + i
    let B := f.degreeOf (some 0) + g.degreeOf (some 0) + j
    let S := quotientBidegreeLE I A B
    have hmem (t : Fin n) : x t ∈ S := by
      refine mem_quotientBidegreeLE.mpr ⟨p t, mem_box.mpr ⟨?_, ?_⟩, hp t⟩
      · have hi : (p t).degreeOf none ≤ i :=
          Finset.le_sup (f := fun u => (p u).degreeOf none) (Finset.mem_univ t)
        exact hi.trans (Nat.le_add_left _ _)
      · have hj : (p t).degreeOf (some 0) ≤ j :=
          Finset.le_sup (f := fun u => (p u).degreeOf (some 0)) (Finset.mem_univ t)
        exact hj.trans (Nat.le_add_left _ _)
    let y (t : Fin n) : S := ⟨x t, hmem t⟩
    have hy : LinearIndependent F y := LinearIndependent.of_comp S.subtype hx
    have hy' : n ≤ Module.finrank F S := by simpa using hy.fintype_card_le_finrank
    exact hy'.trans (box_image_le hf hg hrel i j)
  have hfinite : Module.Finite F Q := by
    apply Module.rank_lt_aleph0_iff.mp
    by_contra! h
    have hn : ((k + 1 : ℕ) : Cardinal) ≤ Module.rank F Q :=
      Cardinal.natCast_lt_aleph0.le.trans h
    obtain ⟨x, hx⟩ := exists_linearIndependent_of_le_rank hn
    have hh := hdim (k + 1) x hx
    omega
  obtain ⟨x, hx⟩ := exists_linearIndependent_of_le_finrank
    (le_rfl : Module.finrank F Q ≤ Module.finrank F Q)
  exact ⟨hfinite, hdim _ x hx⟩
theorem proof : K1_14_2_2_4_5.c4 := by
  intro F _ f g a b c e hrel hf₀ hf₁ hg₀ hg₁
  let ρ := MvPolynomial.renameEquiv F (finSuccEquiv 1)
  have hrel' : IsRelPrime (ρ f) (ρ g) := by
    apply IsRelPrime.of_map ρ.symm
    simpa using hrel
  have degree₀ (p : Plane F) : (ρ p).degreeOf none = p.degreeOf 0 := by
    simp only [ρ, renameEquiv_apply, ← show finSuccEquiv 1 0 = none from rfl,
      degreeOf_rename_of_injective (finSuccEquiv 1).injective]
  have degree₁ (p : Plane F) : (ρ p).degreeOf (some 0) = p.degreeOf 1 := by
    simp only [ρ, renameEquiv_apply, ← show finSuccEquiv 1 1 = some 0 from rfl,
      degreeOf_rename_of_injective (finSuccEquiv 1).injective]
  let q := Ideal.quotientEquivAlg (Ideal.span ({f, g} : Set (Plane F))) ρ (J :=
    Ideal.span {ρ f, ρ g}) (by simp [Ideal.map_span, Set.image_insert_eq, Set.image_singleton])
  obtain ⟨hfinite, hbound⟩ := plane_bound (ρ f) (ρ g) hrel'
  let _ := hfinite
  refine ⟨Module.Finite.of_surjective q.symm.toLinearMap q.symm.surjective, ?_⟩
  refine q.toLinearEquiv.finrank_eq.trans_le (hbound.trans ?_)
  simp only [degree₀, degree₁]
  exact Nat.add_le_add (Nat.mul_le_mul hf₀ hg₁) (Nat.mul_le_mul hg₀ hf₁)
end
end K1_14_2_2_4_5_4
end
section
set_option autoImplicit false
namespace K1_14_2_2_4_5_5
noncomputable section
open K1_14_2_2_4_5 (Plane PlaneIntersection)
open MvPolynomial
variable {F : Type} [Field F]
private abbrev cap (F : Type) [Field F] (B J : ℕ) : Submodule F (Plane F) :=
  restrictCappedDegree (Fin 2) F 1 B J
private theorem mem_cap {p : Plane F} {B J : ℕ} :
    p ∈ cap F B J ↔ p.totalDegree ≤ B ∧ p.degreeOf 1 ≤ J := by
  rw [mem_restrictCappedDegree, degreeOf_le_iff, totalDegree, Finset.sup_le_iff]
  exact ⟨fun h => ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩,
    fun h m hm => ⟨h.1 m hm, h.2 m hm⟩⟩
private abbrev multiples (f : Plane F) (B J : ℕ) : Submodule F (Plane F) :=
  (cap F B J).map (LinearMap.mulLeft F f)
private theorem mem_multiples {f p : Plane F} (hf : f ≠ 0) {B J : ℕ} :
    p ∈ multiples f B J ↔
      p ∈ cap F (f.totalDegree + B) (f.degreeOf 1 + J) ∧ f ∣ p := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨mul_mem_restrictCappedDegree (mem_cap.mpr ⟨le_rfl, le_rfl⟩) hq, ⟨q, rfl⟩⟩
  · rintro ⟨hp, q, rfl⟩
    refine ⟨q, ?_, rfl⟩
    by_cases hq : q = 0
    · rw [hq]
      exact Submodule.zero_mem _
    · rw [mem_cap, totalDegree_mul_of_isDomain hf hq, degreeOf_mul_eq hf hq] at hp
      exact mem_cap.mpr ⟨by omega, by omega⟩
private abbrev capCount (B J : ℕ) : ℕ :=
  (cappedDegreeExponents (Fin 2) 1 B J).ncard
private theorem finrank_multiples {f : Plane F} (hf : f ≠ 0) (B J : ℕ) :
    Module.finrank F (multiples f B J) = capCount B J := by
  rw [multiples, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj,
    finrank_restrictCappedDegree]
  intro p q h
  exact Subtype.ext (mul_left_cancel₀ hf h)
private theorem capCount_mixed (B J b j c e : ℕ)
    (hJB : J ≤ B) (hjb : j ≤ b) (hec : e ≤ c) :
    capCount (B + b + c) (J + j + e) + capCount B J =
      capCount (B + c) (J + e) + capCount (B + b) (J + j) +
        cappedDegreeMixedVolume b j c e := by
  have h00 := two_mul_ncard_cappedDegreeExponents_fin_two B J hJB
  have h10 := two_mul_ncard_cappedDegreeExponents_fin_two (B + b) (J + j) (by omega)
  have h01 := two_mul_ncard_cappedDegreeExponents_fin_two (B + c) (J + e) (by omega)
  have h11 := two_mul_ncard_cappedDegreeExponents_fin_two (B + b + c) (J + j + e) (by omega)
  have hcalc :
      (J + j + e + 1) * (2 * (B + b + c) + 2 - (J + j + e)) +
        (J + 1) * (2 * B + 2 - J) =
      (J + e + 1) * (2 * (B + c) + 2 - (J + e)) +
        (J + j + 1) * (2 * (B + b) + 2 - (J + j)) +
        2 * cappedDegreeMixedVolume b j c e := by
    unfold cappedDegreeMixedVolume
    zify [hec, show J + j + e ≤ 2 * (B + b + c) + 2 by omega,
      show J ≤ 2 * B + 2 by omega, show J + e ≤ 2 * (B + c) + 2 by omega,
      show J + j ≤ 2 * (B + b) + 2 by omega]
    ring
  change 2 * capCount B J = _ at h00
  change 2 * capCount (B + b) (J + j) = _ at h10
  change 2 * capCount (B + c) (J + e) = _ at h01
  change 2 * capCount (B + b + c) (J + j + e) = _ at h11
  rw [← h00, ← h10, ← h01, ← h11] at hcalc
  omega
private theorem filtered_bound {f g : Plane F} (hf : f ≠ 0) (hg : g ≠ 0)
    (hrel : IsRelPrime f g) (B J : ℕ) (hJB : J ≤ B) :
    Module.finrank F
      ((cap F (B + f.totalDegree + g.totalDegree) (J + f.degreeOf 1 + g.degreeOf 1)).map
        (Ideal.Quotient.mkₐ F (Ideal.span {f, g})).toLinearMap) ≤
      cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) g.totalDegree (g.degreeOf 1) := by
  let I : Ideal (Plane F) := Ideal.span {f, g}
  let V := cap F (B + f.totalDegree + g.totalDegree) (J + f.degreeOf 1 + g.degreeOf 1)
  let q := (Ideal.Quotient.mkₐ F I).toLinearMap
  let π := q.domRestrict V
  let K := (LinearMap.ker π).map V.subtype
  let U := multiples f (B + g.totalDegree) (J + g.degreeOf 1)
  let W := multiples g (B + f.totalDegree) (J + f.degreeOf 1)
  let T := multiples (f * g) B J
  have hU {p : Plane F} : p ∈ U ↔ p ∈ V ∧ f ∣ p := by
    simpa [U, V, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (mem_multiples hf (p := p) (B := B + g.totalDegree) (J := J + g.degreeOf 1))
  have hW {p : Plane F} : p ∈ W ↔ p ∈ V ∧ g ∣ p := by
    simpa [W, V, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (mem_multiples hg (p := p) (B := B + f.totalDegree) (J := J + f.degreeOf 1))
  have hT {p : Plane F} : p ∈ T ↔ p ∈ V ∧ f * g ∣ p := by
    simpa [T, V, totalDegree_mul_of_isDomain hf hg, degreeOf_mul_eq hf hg,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (mem_multiples (mul_ne_zero hf hg) (p := p) (B := B) (J := J))
  have hUW : U ⊓ W = T := by
    ext p
    simp only [Submodule.mem_inf, hU, hW, hT]
    exact ⟨fun ⟨⟨hp, hf'⟩, ⟨_, hg'⟩⟩ => ⟨hp, hrel.mul_dvd hf' hg'⟩,
      fun ⟨hp, hd⟩ => ⟨⟨hp, (dvd_mul_right f g).trans hd⟩, ⟨hp, (dvd_mul_left g f).trans hd⟩⟩⟩
  have hinK {p : Plane F} (hp : p ∈ V) (hI : p ∈ I) : p ∈ K := by
    refine ⟨⟨p, hp⟩, ?_, rfl⟩
    exact LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hI)
  have hfI : f ∈ I := Ideal.subset_span (by simp)
  have hgI : g ∈ I := Ideal.subset_span (by simp)
  have hle : U ⊔ W ≤ K := by
    apply sup_le
    · intro p hp
      obtain ⟨hp, d, rfl⟩ := hU.mp hp
      exact hinK hp (Ideal.mul_mem_right _ _ hfI)
    · intro p hp
      obtain ⟨hp, d, rfl⟩ := hW.mp hp
      exact hinK hp (Ideal.mul_mem_right _ _ hgI)
  have hdim := Submodule.finrank_mono hle
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [hUW, finrank_multiples hf, finrank_multiples hg, finrank_multiples (mul_ne_zero hf hg)]
    at hsum
  have hnull := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, finrank_restrictCappedDegree] at hnull
  change Module.finrank F (V.map q) + Module.finrank F (LinearMap.ker π) =
    capCount (B + f.totalDegree + g.totalDegree) (J + f.degreeOf 1 + g.degreeOf 1) at hnull
  rw [Submodule.finrank_map_subtype_eq] at hdim
  have hcount := capCount_mixed B J f.totalDegree (f.degreeOf 1) g.totalDegree (g.degreeOf 1)
    hJB (degreeOf_le_totalDegree f 1) (degreeOf_le_totalDegree g 1)
  change Module.finrank F (V.map q) ≤ _
  omega
private theorem finite_of_exhaustion {M : Type} [AddCommGroup M] [Module F M]
    (V : ℕ → Submodule F M) [∀ N, Module.Finite F (V N)] (hmono : Monotone V)
    (hex : ∀ x : M, ∃ N, x ∈ V N) (d : ℕ)
    (hb : ∀ N, Module.finrank F (V N) ≤ d) :
    Module.Finite F M ∧ Module.finrank F M ≤ d := by
  classical
  let P : ℕ → Prop := fun k => ∃ N, Module.finrank F (V N) = k
  obtain ⟨N, hN⟩ := Nat.findGreatest_spec (P := P) (hb 0) ⟨0, rfl⟩
  have htop : V N = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hn⟩ := hex x
    have hle : V N ≤ V (max N n) := hmono (le_max_left _ _)
    have hdim : Module.finrank F (V (max N n)) ≤ Module.finrank F (V N) := by
      rw [hN]
      exact Nat.le_findGreatest (P := P) (hb _) ⟨_, rfl⟩
    rw [Submodule.eq_of_le_of_finrank_le hle hdim]
    exact hmono (le_max_right _ _) hn
  let E : V N ≃ₗ[F] M := (LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv
  exact ⟨Module.Finite.of_surjective E.toLinearMap E.surjective, E.finrank_eq.symm.trans_le (hb N)⟩
private theorem top_quotient (f g : Plane F) (htop : Ideal.span {f, g} = ⊤) (d : ℕ) :
    Module.Finite F (PlaneIntersection f g) ∧ Module.finrank F (PlaneIntersection f g) ≤ d := by
  let : Subsingleton (PlaneIntersection f g) := Ideal.Quotient.subsingleton_iff.mpr htop
  exact ⟨inferInstance, (Module.finrank_eq_zero_of_subsingleton F _).trans_le (Nat.zero_le d)⟩
theorem proof : K1_14_2_2_4_5.c5 := by
  intro F _ f g b j c e hrel hjb hec hfb hfj hgc hge
  have hfI : f ∈ Ideal.span ({f, g} : Set (Plane F)) := Ideal.subset_span (by simp)
  have hgI : g ∈ Ideal.span ({f, g} : Set (Plane F)) := Ideal.subset_span (by simp)
  by_cases hf : f = 0
  · have hu : IsUnit g := hrel (hf ▸ dvd_zero g) dvd_rfl
    exact top_quotient f g (Ideal.eq_top_of_isUnit_mem _ hgI hu) _
  by_cases hg : g = 0
  · have hu : IsUnit f := hrel dvd_rfl (hg ▸ dvd_zero f)
    exact top_quotient f g (Ideal.eq_top_of_isUnit_mem _ hfI hu) _
  let I : Ideal (Plane F) := Ideal.span {f, g}
  let q := (Ideal.Quotient.mkₐ F I).toLinearMap
  let V (N : ℕ) :=
    (cap F (2 * N + f.totalDegree + g.totalDegree) (N + f.degreeOf 1 + g.degreeOf 1)).map q
  have hmono : Monotone V := by
    intro N M hNM
    apply Submodule.map_mono
    intro p hp
    obtain ⟨ht, hj⟩ := mem_cap.mp hp
    exact mem_cap.mpr ⟨by omega, by omega⟩
  have hex (x : PlaneIntersection f g) : ∃ N, x ∈ V N := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨p.totalDegree, p, mem_cap.mpr ⟨by omega, ?_⟩, rfl⟩
    have := degreeOf_le_totalDegree p 1
    omega
  obtain ⟨hfin, hle⟩ := finite_of_exhaustion V hmono hex _ fun N =>
    filtered_bound hf hg hrel (2 * N) N (by omega)
  have hpad := (cappedDegreeMixedVolume_mono_left (c := e) (b := c) hfb hfj)
  have hmix := cappedDegreeMixedVolume_mono_right (degreeOf_le_totalDegree f 1)
    (degreeOf_le_totalDegree g 1) hec hgc hge
  have hcap : cappedDegreeMixedVolume b j c e = b * e + c * j - j * e := by
    have hsub : j * e ≤ b * e + c * j :=
      (Nat.mul_le_mul_right _ hjb).trans (Nat.le_add_right _ _)
    unfold cappedDegreeMixedVolume
    zify [hec, hsub]
    ring
  exact ⟨hfin, hle.trans ((hmix.trans hpad).trans_eq hcap)⟩
end
end K1_14_2_2_4_5_5
end
section
set_option autoImplicit false
namespace K1_14_2_2_4_5_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_3 K1_14_2_2_4_5
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev SplitPoly := MvPolynomial (Fin 2) Seeds
private abbrev seedVariables : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  (finSumFinEquiv (m := 2) (n := 2)).symm.trans (Equiv.sumComm (Fin 2) (Fin 2))
private def seedChart : Ambient ≃+* SplitPoly :=
  ((MvPolynomial.renameEquiv FX seedVariables).trans
    (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2))).toRingEquiv
private theorem seed_map_eq : mapGenericSeed =
    (algebraMap SplitPoly FibreRing).comp seedChart.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [mapGenericSeed, seedChart]
    rfl
  · intro i
    rw [RingHom.comp_apply, mapGenericSeed, MvPolynomial.eval₂Hom_X']
    change _ = algebraMap SplitPoly FibreRing
      (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2)
        (MvPolynomial.renameEquiv FX seedVariables (MvPolynomial.X i)))
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, MvPolynomial.algebraMap_def]
    trans Sum.elim MvPolynomial.X (fun j => MvPolynomial.C (generic j)) (seedVariables i)
    · fin_cases i <;> rfl
    · cases seedVariables i <;> simp [generic]
private abbrev denominators : Submonoid SplitPoly :=
  (nonZeroDivisors Seeds).map MvPolynomial.C
private theorem chart_localization (e : Ambient ≃+* SplitPoly) :
    letI := ((algebraMap SplitPoly FibreRing).comp e.toRingHom).toAlgebra
    IsLocalization (denominators.map e.symm) FibreRing :=
  IsLocalization.isLocalization_of_base_ringEquiv denominators FibreRing e.symm
private theorem relPrime_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [DecompositionMonoid R] (M : Submonoid R) [IsLocalization M S] {a b : R}
    (hab : IsRelPrime a b) : IsRelPrime (algebraMap R S a) (algebraMap R S b) := by
  intro d ha hb
  obtain ⟨c, u, rfl⟩ := IsLocalization.exists_mk'_eq M d
  have hcu := IsLocalization.mk'_spec S c u
  have clear_denominator (x : R) (hx : IsLocalization.mk' S c u ∣ algebraMap R S x) :
      ∃ t : M, c ∣ (t : R) * x := by
    have hmem : algebraMap R S x ∈ (Ideal.span {c}).map (algebraMap R S) := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, ← hcu,
        (IsLocalization.map_units S u).mul_right_dvd]
      exact hx
    obtain ⟨t, ht, htx⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M S _ _).mp hmem
    exact ⟨⟨t, ht⟩, Ideal.mem_span_singleton.mp htx⟩
  obtain ⟨m, hm⟩ := clear_denominator a ha
  obtain ⟨n, hn⟩ := clear_denominator b hb
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hm
  have hyn : y ∣ (n : R) :=
    (hab.of_dvd_left hy).dvd_of_dvd_mul_right ((dvd_mul_left y x).trans hn)
  have hu : IsUnit (algebraMap R S (x * y)) := by
    rw [map_mul]
    exact (isUnit_of_dvd_unit (map_dvd _ hx) (IsLocalization.map_units S m)).mul
      (isUnit_of_dvd_unit (map_dvd _ hyn) (IsLocalization.map_units S n))
  apply isUnit_of_dvd_unit _ hu
  rw [← hcu]
  exact dvd_mul_right _ _
private theorem chart_of_localization (φ : Ambient →+* FibreRing) (k : Fin 4)
    (e : Ambient ≃+* SplitPoly)
    (hφ : φ = (algebraMap SplitPoly FibreRing).comp e.toRingHom)
    (hfinite : ∀ I : Ideal Ambient, Active I →
      Module.Finite SeedField (PlaneSection φ I) ∧
        Module.finrank SeedField (PlaneSection φ I) = sectionDegree I k) :
    SectionChart SeedField φ k := by
  subst φ
  let : Algebra Ambient FibreRing :=
    ((algebraMap SplitPoly FibreRing).comp e.toRingHom).toAlgebra
  let M : Submonoid Ambient := denominators.map e.symm
  let : IsLocalization M FibreRing := chart_localization e
  refine ⟨IsLocalization.flat FibreRing M, hfinite, ?_, ?_⟩
  · intro I hI hproper
    change I.map (algebraMap Ambient FibreRing) ≠ ⊤ at hproper
    change (I.map (algebraMap Ambient FibreRing)).IsPrime ∧
      (I.map (algebraMap Ambient FibreRing)).comap (algebraMap Ambient FibreRing) = I
    have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint M FibreRing I).mp hproper
    exact ⟨IsLocalization.isPrime_of_isPrime_disjoint M FibreRing I hI hd,
      IsLocalization.under_map_of_isPrime_disjoint M FibreRing hI hd⟩
  · intro a b hab
    exact relPrime_localization M hab
theorem proof : K1_14_2_2_4_5.c2 := by
  constructor
  · refine chart_of_localization mapGenericSeed 0 seedChart seed_map_eq ?_
    intro I hI
    exact ⟨hI.seed_finite, rfl⟩
  · refine chart_of_localization mapGenericJets 3 seedPresentation ?_ ?_
    · exact mapGenericJets_eq
    · intro I hI
      exact ⟨hI.jet_finite, rfl⟩
end
end K1_14_2_2_4_5_2
end
section
set_option autoImplicit false
namespace K1_14_2_2_2_4_3
theorem proof : K1_14_2_2_2_4.c3 := by
  intro F _ P Q u j v k hproper hP₀ hP₁ hQ₀ hQ₁
  let : UniqueFactorizationMonoid F := PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : UniqueFactorizationMonoid (K1_14_2_2_2_4.Plane F) :=
    MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  have hrel : IsRelPrime P Q :=
    WfDvdMonoid.isRelPrime_of_no_irreducible_factors
      (fun h => hproper.left_ne h.1) hproper.no_common
  exact K1_14_2_2_4_5_4.proof F P Q u j v k hrel hP₀ hP₁ hQ₀ hQ₁
end K1_14_2_2_2_4_3
end
section
set_option autoImplicit false
namespace K1_14_2_2_2_4_2
theorem proof : K1_14_2_2_2_4.c2 := by
  intro F _ P Q b j c k hj hk hProper hPb hPj hQc hQk
  have hRel : IsRelPrime P Q :=
    WfDvdMonoid.isRelPrime_of_no_irreducible_factors
      (fun h => hProper.left_ne h.1) hProper.no_common
  exact K1_14_2_2_4_5_5.proof F P Q b j c k hRel hj hk hPb hPj hQc hQk
end K1_14_2_2_2_4_2
end
section
namespace K1_13_2_2
noncomputable section
open K1_13 K1_13_2
open MvPolynomial
abbrev JetExp := Fin 4 →₀ ℕ
abbrev JetPoly := MvPolynomial (Fin 4) Geom
def gradeWeight : Fin 4 → ℕ := fun _ => 1
def oldWeight : Fin 4 → ℕ := Fin.val
def contactWeight : Fin 4 → ℕ := ![3, 0, 1, 2]
def activeFlag (i : BlockIndex) : Flag :=
  { initialFlag i with upper := min (initialFlag i).upper (2999 - offset i) }
def oldExponents (F : Flag) : Set JetExp :=
  { e | (e.weight gradeWeight : ℤ) = F.degree ∧
    F.lower ≤ (e.weight oldWeight : ℤ) ∧
    (e.weight oldWeight : ℤ) ≤ F.upper ∧ (e (3 : Fin 4) : ℤ) ≤ F.cap }
def targetExponents (F : Flag) : Set JetExp :=
  { e | (e.weight gradeWeight : ℤ) = F.degree ∧
    F.lower ≤ (e.weight oldWeight : ℤ) ∧ (e.weight contactWeight : ℤ) < F.order }
def cumulativeExponents (d u : ℤ) : Set JetExp :=
  { e | (e.weight gradeWeight : ℤ) = d ∧ (e.weight oldWeight : ℤ) ≤ u }
theorem finite_of_grade {s : Set JetExp} {d : ℤ}
    (hs : ∀ e ∈ s, (e.weight gradeWeight : ℤ) = d) : s.Finite := by
  refine (Finsupp.finite_of_nat_weight_le gradeWeight (fun _ => by simp [gradeWeight])
    d.toNat).subset ?_
  intro e he
  change e.weight gradeWeight ≤ d.toNat
  have hd := hs e he
  omega
theorem oldExponents_finite (F : Flag) : (oldExponents F).Finite :=
  finite_of_grade fun _ h => h.1
theorem targetExponents_finite (F : Flag) : (targetExponents F).Finite :=
  finite_of_grade fun _ h => h.1
theorem cumulativeExponents_finite (d u : ℤ) : (cumulativeExponents d u).Finite :=
  finite_of_grade fun _ h => h.1
def oldColumns (F : Flag) : Finset JetExp := (oldExponents_finite F).toFinset
def targetColumns (F : Flag) : Finset JetExp := (targetExponents_finite F).toFinset
def cumulativeColumns (d u : ℤ) : Finset JetExp := (cumulativeExponents_finite d u).toFinset
def CumulativeCount : Prop :=
  ∀ d u : ℤ, ((cumulativeColumns d u).card : ℤ) = cumulative d u
@[simp] theorem mem_oldColumns {F : Flag} {e : JetExp} :
    e ∈ oldColumns F ↔ e ∈ oldExponents F :=
  (oldExponents_finite F).mem_toFinset
@[simp] theorem mem_targetColumns {F : Flag} {e : JetExp} :
    e ∈ targetColumns F ↔ e ∈ targetExponents F :=
  (targetExponents_finite F).mem_toFinset
@[simp] theorem mem_cumulativeColumns {d u : ℤ} {e : JetExp} :
    e ∈ cumulativeColumns d u ↔ e ∈ cumulativeExponents d u :=
  (cumulativeExponents_finite d u).mem_toFinset
def oldSpace (F : Flag) : Submodule Geom JetPoly := restrictSupport Geom (oldExponents F)
def targetSpace (F : Flag) : Submodule Geom JetPoly := restrictSupport Geom (targetExponents F)
instance (F : Flag) : Module.Finite Geom (oldSpace F) :=
  restrictSupport_finite (oldExponents_finite F)
instance (F : Flag) : Module.Finite Geom (targetSpace F) :=
  restrictSupport_finite (targetExponents_finite F)
theorem finrank_oldSpace (F : Flag) :
    Module.finrank Geom (oldSpace F) = (oldColumns F).card := by
  conv_lhs => rw [oldSpace, ← (oldExponents_finite F).coe_toFinset]
  exact finrank_restrictSupport_finset (oldColumns F)
theorem finrank_targetSpace (F : Flag) :
    Module.finrank Geom (targetSpace F) = (targetColumns F).card := by
  conv_lhs => rw [targetSpace, ← (targetExponents_finite F).coe_toFinset]
  exact finrank_restrictSupport_finset (targetColumns F)
def shearImage (j : Fin 4) : JetPoly :=
  if j = 0 then MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 2 + MvPolynomial.X 3
  else MvPolynomial.X j
def coordinateChange : JetPoly →ₐ[Geom] JetPoly := bind₁ shearImage
def flagContact (F : Flag) : oldSpace F →ₗ[Geom] JetPoly :=
  (weightedTruncation contactWeight F.order.toNat).comp
    (coordinateChange.toLinearMap.comp (oldSpace F).subtype)
end
end K1_13_2_2
end
section
namespace K1_13_2_2
noncomputable section
open K1_13 K1_13_2
open MvPolynomial
def c1 : Prop :=
  ∀ i : BlockIndex,
    Module.finrank Geom (LinearMap.range (originBlock i)) ≤
      Module.finrank Geom (LinearMap.range (flagContact (activeFlag i)))
def c2 : Prop := CumulativeCount
def c3 : Prop :=
  CumulativeCount → ∀ F : Flag, ((oldColumns F).card : ℤ) = oldCount F
def c4 : Prop :=
  CumulativeCount → ∀ F : Flag, ((targetColumns F).card : ℤ) = targetCount F
def c5 : Prop :=
  ∀ (F : Flag) (power : Fin 11 → ℕ),
    ∃ f : LinearMap.ker (flagContact (residualFlag F power)) →ₗ[Geom]
        LinearMap.ker (flagContact F), Function.Injective f
theorem shearImage_grade (j : Fin 4) :
    (shearImage j).IsWeightedHomogeneous gradeWeight (gradeWeight j) := by
  have hX (k : Fin 4) :=
    isWeightedHomogeneous_X Geom gradeWeight k
  by_cases h : j = 0
  · subst j
    simp only [shearImage]
    exact (((hX 0).add (hX 1)).sub (hX 2)).add (hX 3)
  · simpa only [shearImage, ite_eq_right h] using hX j
theorem shearImage_order (j : Fin 4) :
    shearImage j ∈ restrictWeightedOrder oldWeight (oldWeight j) := by
  by_cases h : j = 0
  · subst j
    change shearImage 0 ∈ restrictWeightedOrder oldWeight 0
    simp
  · simp only [shearImage, ite_eq_right h]
    exact X_mem_restrictWeightedOrder oldWeight j le_rfl
theorem flagContact_mem_target (F : Flag) (p : oldSpace F) :
    flagContact F p ∈ targetSpace F := by
  change ∀ e ∈ (flagContact F p).support, e ∈ targetExponents F
  intro e he
  by_cases hp : (p : JetPoly) = 0
  · have hz : p = 0 := Subtype.ext hp
    simp [hz] at he
  have hd : 0 ≤ F.degree := by
    obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr
      (fun hs => hp (support_eq_empty.mp hs))
    have h := (p.2 hu).1
    omega
  have hgrade : (p : JetPoly).IsWeightedHomogeneous gradeWeight F.degree.toNat := by
    intro u hu
    have h := (p.2 (MvPolynomial.mem_support_iff.mpr hu)).1
    omega
  have hmin : (p : JetPoly) ∈ restrictWeightedOrder oldWeight F.lower.toNat := by
    intro u hu
    change F.lower.toNat ≤ u.weight oldWeight
    have h := (p.2 hu).2.1
    omega
  have hgrade' := hgrade.bind₁ shearImage_grade
  have hmin' := mem_restrictWeightedOrder.mp
    (bind₁_mem_restrictWeightedOrder shearImage_order hmin)
  change e ∈ (weightedTruncation contactWeight F.order.toNat
    (bind₁ shearImage (p : JetPoly))).support at he
  rw [MvPolynomial.mem_support_iff, coeff_weightedTruncation] at he
  split at he
  next hcut =>
    have hs := MvPolynomial.mem_support_iff.mpr he
    have hg := hgrade' he
    have hl := hmin' e hs
    change (e.weight gradeWeight : ℤ) = F.degree ∧
      F.lower ≤ (e.weight oldWeight : ℤ) ∧ (e.weight contactWeight : ℤ) < F.order
    exact ⟨by omega, by omega, by omega⟩
  next => exact (he rfl).elim
private theorem rank_le_target (F : Flag) :
    Module.finrank Geom (LinearMap.range (flagContact F)) ≤ (targetColumns F).card := by
  rw [← finrank_targetSpace]
  apply Submodule.finrank_mono
  rintro _ ⟨p, rfl⟩
  exact flagContact_mem_target F p
private theorem active_range_le (i : BlockIndex) :
    LinearMap.range (flagContact (activeFlag i)) ≤
      LinearMap.range (flagContact (initialFlag i)) := by
  rintro _ ⟨p, rfl⟩
  refine ⟨⟨p.1, ?_⟩, rfl⟩
  intro e he
  obtain ⟨hgrade, hlow, hupp, hcap⟩ := p.2 he
  exact ⟨hgrade, hlow, hupp.trans (min_le_left _ _), hcap⟩
private theorem rank_zero_of_order_nonpos (F : Flag) (h : F.order ≤ 0) :
    Module.finrank Geom (LinearMap.range (flagContact F)) = 0 := by
  have hz : flagContact F = 0 := by
    ext p : 1
    change weightedTruncation contactWeight F.order.toNat (coordinateChange (p : JetPoly)) = 0
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    simp [Int.toNat_of_nonpos h]
  simp [hz]
private theorem lower_le_kernel (F : Flag)
    (hcols : ((oldColumns F).card : ℤ) = oldCount F)
    (hrows : ((targetColumns F).card : ℤ) = targetCount F) :
    kernelLower F ≤ (Module.finrank Geom (LinearMap.ker (flagContact F)) : ℤ) := by
  have hr := rank_le_target F
  have hn := (flagContact F).finrank_range_add_finrank_ker
  rw [finrank_oldSpace] at hn
  unfold kernelLower
  split
  · exact Int.natCast_nonneg _
  · omega
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    K1_13_2.c2 := by
  intro i power
  let F := initialFlag i
  let A := activeFlag i
  have hOrigin := h1 i
  change Module.finrank Geom (LinearMap.range (originBlock i)) ≤
    Module.finrank Geom (LinearMap.range (flagContact A)) at hOrigin
  by_cases ho : F.order ≤ 0
  · have hz := rank_zero_of_order_nonpos A ho
    have h := hOrigin.trans (le_of_eq hz)
    have horder : (initialFlag i).order ≤ 0 := ho
    simpa [blockBound, horder] using h
  have hActive := (flagContact A).finrank_range_le
  rw [finrank_oldSpace] at hActive
  have hCols := h3 h2
  have hRows := h4 h2
  have hKernel0 := lower_le_kernel F (hCols F) (hRows F)
  have hKernel1 := lower_le_kernel (residualFlag F power)
    (hCols (residualFlag F power)) (hRows (residualFlag F power))
  obtain ⟨f, hf⟩ := h5 F power
  have hInj := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  have hRank := Submodule.finrank_mono (active_range_le i)
  change Module.finrank Geom (LinearMap.range (flagContact A)) ≤
    Module.finrank Geom (LinearMap.range (flagContact F)) at hRank
  have hNullity := (flagContact F).finrank_range_add_finrank_ker
  rw [finrank_oldSpace] at hNullity
  have hFullCols := hCols F
  have hActiveCols := hCols A
  have hbound :
      (Module.finrank Geom (LinearMap.range (originBlock i)) : ℤ) ≤
      min (oldCount A)
        (oldCount F - max 0 (max (kernelLower F) (kernelLower (residualFlag F power)))) := by
    apply le_min
    · omega
    · have hMax :
          max 0 (max (kernelLower F) (kernelLower (residualFlag F power))) ≤
            (Module.finrank Geom (LinearMap.ker (flagContact F)) : ℤ) := by
        exact max_le (Int.natCast_nonneg _) (max_le hKernel0 (by omega))
      omega
  unfold blockBound
  change Module.finrank Geom (LinearMap.range (originBlock i)) ≤
    (if F.order ≤ 0 then 0 else
      (min (oldCount A)
        (oldCount F - max 0 (max (kernelLower F) (kernelLower (residualFlag F power))))).toNat)
  rw [ite_eq_right ho]
  omega
end
end K1_13_2_2
end
section
namespace K1_13_2_2_2
open K1_13_2 K1_13_2_2 K1_13_8_1
open scoped BigOperators
noncomputable section
private abbrev Slot := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ
private def slots (b j : ℕ) : Finset Slot :=
  (Finset.range (min b (j / 3) + 1)).sigma (fun z =>
    (Finset.range (min (b - z) ((j - 3 * z) / 2) + 1)).sigma (fun y =>
      (Finset.range (min (b - z - y) (j - 3 * z - 2 * y) + 1)).sigma (fun x =>
        Finset.range (b - z - y - x + 1))))
private def slotGrade (q : Slot) : ℕ := q.2.2.2 + q.2.2.1 + q.2.1 + q.1
private def slotWeight (q : Slot) : ℕ := q.2.2.1 + 2 * q.2.1 + 3 * q.1
private theorem mem_slots (q : Slot) (b j : ℕ) :
    q ∈ slots b j ↔ slotGrade q ≤ b ∧ slotWeight q ≤ j := by
  rcases q with ⟨z, y, x, a⟩
  simp only [slots, Finset.mem_sigma, Finset.mem_range, slotGrade, slotWeight]
  constructor
  · rintro ⟨hz, hy, hx, ha⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hb, hj⟩
    exact ⟨by omega, by omega, by omega, by omega⟩
private theorem card_slots (b j : ℕ) : (slots b j).card = K1_13.symbols b j := by
  simp only [slots, K1_13.symbols, Finset.card_sigma, Finset.card_range]
private def slotOf (e : JetExp) : Slot := ⟨e 3, e 2, e 1, e 0⟩
private def exponentOf (q : Slot) : JetExp :=
  Finsupp.equivFunOnFinite.symm ![q.2.2.2, q.2.2.1, q.2.1, q.1]
private theorem grade_eq (e : JetExp) : e.weight gradeWeight = slotGrade (slotOf e) := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_succ, gradeWeight, slotGrade, slotOf, Nat.add_assoc]
private theorem weight_eq (e : JetExp) : e.weight oldWeight = slotWeight (slotOf e) := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_succ, oldWeight, slotWeight, slotOf]
  ring
private theorem exponentOf_slotOf (e : JetExp) : exponentOf (slotOf e) = e := by
  ext i
  fin_cases i <;> simp [exponentOf, slotOf]
private theorem slotOf_exponentOf (q : Slot) : slotOf (exponentOf q) = q := by
  rcases q with ⟨z, y, x, a⟩
  simp [slotOf, exponentOf]
private theorem card_slot_fiber (b j d : ℕ) (hd : d ≤ b) :
    ((slots b j).filter (fun q => slotGrade q = d)).card =
      (cumulativeColumns d j).card := by
  apply Finset.card_nbij' exponentOf slotOf
  · intro q hq
    obtain ⟨hmem, hgrade⟩ := Finset.mem_filter.mp hq
    have hw := (mem_slots q b j).mp hmem
    apply mem_cumulativeColumns.mpr
    change ((exponentOf q).weight gradeWeight : ℤ) = d ∧
      ((exponentOf q).weight oldWeight : ℤ) ≤ j
    rw [grade_eq, weight_eq, slotOf_exponentOf]
    exact ⟨by exact_mod_cast hgrade, by exact_mod_cast hw.2⟩
  · intro e he
    have hmem := mem_cumulativeColumns.mp he
    change (e.weight gradeWeight : ℤ) = d ∧ (e.weight oldWeight : ℤ) ≤ j at hmem
    rw [grade_eq, weight_eq] at hmem
    refine Finset.mem_filter.mpr ⟨(mem_slots _ b j).mpr ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
  · exact fun q _ => slotOf_exponentOf q
  · exact fun e _ => exponentOf_slotOf e
private theorem symbols_eq_sum (b j : ℕ) :
    (K1_13.symbols b j : ℤ) =
      ∑ d ∈ Finset.range (b + 1), ((cumulativeColumns d j).card : ℤ) := by
  rw [← Nat.cast_sum]
  congr 1
  rw [← card_slots]
  calc
    _ = ∑ d ∈ Finset.range (b + 1), ((slots b j).filter (fun q => slotGrade q = d)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro q hq
      have hg := ((mem_slots q b j).mp hq).1
      exact Finset.mem_range.mpr (by omega)
    _ = _ := Finset.sum_congr rfl fun d hd =>
      card_slot_fiber b j d (by simpa using Finset.mem_range.mp hd)
private theorem card_eq_gaussian (d j : ℕ) :
    ((cumulativeColumns d j).card : ℤ) = gaussian 3 d j := by
  have h (b : ℕ) := (symbols_eq_sum b j).symm.trans (symbols_gaussian b j)
  cases d with
  | zero => simpa using h 0
  | succ d =>
      have hs := h (d + 1)
      rw [Finset.sum_range_succ (fun k => ((cumulativeColumns k j).card : ℤ)) (d + 1),
        Finset.sum_range_succ (fun k => gaussian 3 k j) (d + 1), h d] at hs
      exact add_left_cancel hs
private theorem denominator_nat (u : ℕ) : K1_13_2.denominator u = row 0 u := by
  have hdiv : (u : ℤ) / 6 = ((u / 6 : ℕ) : ℤ) := (Int.natCast_ediv u 6).symm
  have hmod : (u : ℤ) % 6 = ((u % 6 : ℕ) : ℤ) := (Int.natCast_mod u 6).symm
  simp only [row_nat, K1_13_2.denominator, ite_eq_right (show ¬ (u : ℤ) < 0 by omega), hdiv, hmod]
  unfold K1_13_8.coefficient
  have hr : u % 6 < 6 := Nat.mod_lt _ (by decide)
  generalize u / 6 = q
  generalize u % 6 = r at hr ⊢
  by_cases hq : q < 2
  · interval_cases q <;> interval_cases r <;> decide
  have hq₁ : 1 ≤ q := by omega
  have hq₂ : 2 ≤ q := by omega
  have hd₃ : 6 ∣ q * (q - 1) * (q - 2) := by
    simpa [Nat.descFactorial_succ, Nat.factorial_succ, mul_comm, mul_left_comm, mul_assoc] using
      Nat.factorial_dvd_descFactorial q 3
  have h₃ := congrArg (fun n : ℕ => (n : ℤ)) (Nat.mul_div_cancel' hd₃)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv, Int.ofNat_sub hq₁,
    Int.ofNat_sub hq₂, Nat.cast_one] at h₃
  have hcubic : 36 * ((q : ℤ) * ((q : ℤ) - 1) * ((q : ℤ) - 2) / 6) =
      6 * (q : ℤ) * ((q : ℤ) - 1) * ((q : ℤ) - 2) := by
    linear_combination 6 * h₃
  interval_cases r <;>
    norm_num [K1_13_8.coefficients, Nat.cast_add, Nat.cast_mul, Int.natCast_ediv,
      Int.ofNat_sub hq₁, Int.ofNat_sub hq₂] <;>
    rw [hcubic] <;> ring
private theorem denominator_eq_row (u : ℤ) : K1_13_2.denominator u = row 0 u := by
  by_cases hu : u < 0
  · simp [K1_13_2.denominator, hu, row_neg _ hu]
  · simpa only [Int.toNat_of_nonneg (show 0 ≤ u by omega)] using denominator_nat u.toNat
theorem proof : K1_13_2_2.c2 := by
  intro d u
  by_cases hd : d < 0
  · have hz : cumulativeColumns d u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hg := (mem_cumulativeColumns.mp he).1
      omega
    simp [hz, cumulative, hd]
  by_cases hu : u < 0
  · have hz : cumulativeColumns d u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hw := (mem_cumulativeColumns.mp he).2
      omega
    simp [hz, cumulative, hu]
  let v := (min u (3 * d)).toNat
  have hv : (v : ℤ) = min u (3 * d) := Int.toNat_of_nonneg (by omega)
  have hd' : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hclip : cumulativeColumns d u = cumulativeColumns d v := by
    ext e
    simp only [mem_cumulativeColumns, cumulativeExponents, Set.mem_ofPred_eq, hv]
    rw [grade_eq, weight_eq]
    unfold slotGrade slotWeight
    omega
  calc
    _ = ((cumulativeColumns d.toNat v).card : ℤ) := by rw [hd', hclip]
    _ = gaussian 3 d.toNat v := card_eq_gaussian d.toNat v
    _ = cumulative d u := by
      rw [gaussian_expand]
      simp only [← denominator_eq_row, hd', hv]
      simp [cumulative, hd, hu]
      ring_nf
end
end K1_13_2_2_2
end
section
namespace K1_13_2_2_5
noncomputable section
open K1_13 K1_13_2 K1_13_2_2 MvPolynomial
open scoped BigOperators Pointwise
private structure Certificate (F : Flag) (p : JetPoly) : Prop where
  old_mem : p ∈ oldSpace F
  contact_mem : coordinateChange p ∈ restrictWeightedOrder contactWeight F.order.toNat
private def addFlag (A B : Flag) : Flag :=
  ⟨A.degree + B.degree, A.lower + B.lower, A.upper + B.upper, A.cap + B.cap,
    A.order + B.order⟩
private theorem Certificate.mul {A B : Flag} {p q : JetPoly}
    (hp : Certificate A p) (hq : Certificate B q) :
    Certificate (addFlag A B) (p * q) := by
  constructor
  · change ∀ e ∈ (p * q).support, e ∈ oldExponents (addFlag A B)
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul p q he)
    have ha' : a ∈ oldExponents A := hp.old_mem ha
    have hb' : b ∈ oldExponents B := hq.old_mem hb
    simp only [oldExponents, Set.mem_ofPred_eq, addFlag, map_add, Finsupp.add_apply,
      Nat.cast_add] at ha' hb' ⊢
    exact ⟨by omega, by omega, by omega, by omega⟩
  · rw [map_mul]
    apply restrictWeightedOrder_anti contactWeight
      (show (addFlag A B).order.toNat ≤ A.order.toNat + B.order.toNat by
        change (A.order + B.order).toNat ≤ A.order.toNat + B.order.toNat
        omega)
    exact mul_mem_restrictWeightedOrder hp.contact_mem hq.contact_mem
private theorem certificate_one : Certificate ⟨0, 0, 0, 0, 0⟩ 1 := by
  constructor
  · change ∀ e ∈ (1 : JetPoly).support, e ∈ oldExponents ⟨0, 0, 0, 0, 0⟩
    intro e he
    rw [support_one, Finset.mem_singleton] at he
    subst e
    simp [oldExponents]
  · simp
private def scaleFlag (n : ℕ) (F : Flag) : Flag :=
  ⟨(n : ℤ) * F.degree, (n : ℤ) * F.lower, (n : ℤ) * F.upper, (n : ℤ) * F.cap,
    (n : ℤ) * F.order⟩
private theorem Certificate.pow {F : Flag} {p : JetPoly} (hp : Certificate F p) (n : ℕ) :
    Certificate (scaleFlag n F) (p ^ n) := by
  induction n with
  | zero => simpa [scaleFlag] using certificate_one
  | succ n ih =>
      simpa [scaleFlag, addFlag, Nat.cast_succ, add_mul, pow_succ] using ih.mul hp
private abbrev x0 : JetPoly := MvPolynomial.X 0
private abbrev x1 : JetPoly := MvPolynomial.X 1
private abbrev x2 : JetPoly := MvPolynomial.X 2
private abbrev x3 : JetPoly := MvPolynomial.X 3
private abbrev U : JetPoly := x0 - x2 + x3
private def factor (j : Fin 11) : JetPoly :=
  ![x0, x1, x2, x3, x0 - x1 + x2 - x3, x0 - x1, x0 - x1 + x2,
    x0 * x1 - x1 * x1 + x0 * x2,
    x0 * x3 - x0 * x1 - x1 * x2 + x1 * x1,
    -(x0 * x3) - x0 * x2 - x2 * x2 + x1 * x3 + x1 * x2,
    x0 * x0 * x3 + x0 * x0 * x2 - (2 : ℕ) • (x0 * x1 * x2) - x0 * x1 * x1 + x1 * x1 * x1] j
private def transportedFactor (j : Fin 11) : JetPoly :=
  ![x0 + x1 - x2 + x3, x1, x2, x3, x0, x0 - x2 + x3, x0 + x3,
    x0 * x1 + x0 * x2 + x3 * x1 + x3 * x2 - x2 * x2,
    x0 * x3 - x0 * x1 - x2 * x3 + x3 * x3,
    -(x0 * x3) - x0 * x2 - x3 * x3,
    -(x1 * x1 * x0) + (2 : ℕ) • (x1 * U * x3) + U * U * (x3 + x2)] j
private theorem coordinateChange_factor (j : Fin 11) :
    coordinateChange (factor j) = transportedFactor j := by
  fin_cases j <;>
    simp only [factor, transportedFactor, two_nsmul] <;>
    simp (disch := decide) [coordinateChange, bind₁_X_right, shearImage, x0, x1, x2, x3, U] <;>
    ring
private def marker (j : Fin 11) : Fin 4 := ![0, 1, 2, 3, 0, 0, 0, 1, 1, 2, 1] j
private theorem factor_ne_zero (j : Fin 11) : factor j ≠ 0 := by
  intro h
  have he := congrArg (eval fun i : Fin 4 => if i = marker j then (1 : Geom) else 0) h
  fin_cases j <;> norm_num [factor, marker, x0, x1, x2, x3, eval_X, two_nsmul, Matrix.cons_val] at he
private theorem factor_mem_oldSpace (j : Fin 11) : factor j ∈ oldSpace (factorFlag j) := by
  fin_cases j <;> simp only [factor, Matrix.cons_val_zero', Matrix.cons_val_succ']
  case' «4» =>
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_) ?_
  case' «5» => refine Submodule.sub_mem _ ?_ ?_
  case' «6» => refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
  case' «7» => refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
  case' «8» =>
    refine Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_) ?_
  case' «9» =>
    refine Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.neg_mem _ ?_) ?_) ?_) ?_) ?_
  case' «10» =>
    refine Submodule.add_mem _
      (Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) (nsmul_mem ?_ 2)) ?_) ?_
  all_goals
    simp only [x0, x1, x2, x3, MvPolynomial.X, monomial_mul_monomial, mul_one, oldSpace,
      monomial_mem_restrictSupport]
    apply Or.inl
    simp only [oldExponents, Set.mem_ofPred_eq, factorFlag, Matrix.cons_val_zero', Matrix.cons_val_succ', oldWeight, gradeWeight,
      map_add, Finsupp.weight_single, one_smul, Finsupp.add_apply, Finsupp.single_apply]
    decide
private theorem cubic_contact :
    -(x1 * x1 * x0) + (2 : ℕ) • (x1 * U * x3) + U * U * (x3 + x2) ∈
      restrictWeightedOrder contactWeight 3 := by
  have h₀ : x0 ∈ restrictWeightedOrder contactWeight 3 :=
    X_mem_restrictWeightedOrder contactWeight 0 (show 3 ≤ contactWeight 0 by decide)
  have h₁ : x1 ∈ restrictWeightedOrder contactWeight 0 := by simp
  have h₂ : x2 ∈ restrictWeightedOrder contactWeight 1 :=
    X_mem_restrictWeightedOrder contactWeight 2 (show 1 ≤ contactWeight 2 by decide)
  have h₃ : x3 ∈ restrictWeightedOrder contactWeight 2 :=
    X_mem_restrictWeightedOrder contactWeight 3 (show 2 ≤ contactWeight 3 by decide)
  have h₀' := restrictWeightedOrder_anti (R := Geom) contactWeight (show 1 ≤ 3 by decide) h₀
  have h₃' := restrictWeightedOrder_anti (R := Geom) contactWeight (show 1 ≤ 2 by decide) h₃
  have hU : U ∈ restrictWeightedOrder contactWeight 1 :=
    Submodule.add_mem _ (Submodule.sub_mem _ h₀' h₂) h₃'
  have hFirst := mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder h₁ h₁) h₀
  have hMid := mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder h₁ hU) h₃
  have hLast := mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder hU hU)
    (Submodule.add_mem _ h₃' h₂)
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.neg_mem _ hFirst) (nsmul_mem hMid 2)) hLast
private theorem factor_contact (j : Fin 11) :
    coordinateChange (factor j) ∈ restrictWeightedOrder contactWeight (factorFlag j).order.toNat := by
  rw [coordinateChange_factor]
  fin_cases j <;> simp only [transportedFactor, factorFlag, Matrix.cons_val_zero', Matrix.cons_val_succ']
  case' «0» =>
    refine Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  case' «5» => refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
  case' «6» => refine Submodule.add_mem _ ?_ ?_
  case' «7» =>
    refine Submodule.sub_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_
  case' «8» =>
    refine Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_) ?_
  case' «9» =>
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.neg_mem _ ?_) ?_) ?_
  case' «10» => exact cubic_contact
  all_goals
    simp only [x0, x1, x2, x3, MvPolynomial.X, monomial_mul_monomial, mul_one,
      monomial_mem_restrictWeightedOrder]
    apply Or.inl
    simp only [map_add, Finsupp.weight_single, one_smul, contactWeight, Matrix.cons_val]
    decide
private def sumFlags (s : Finset (Fin 11)) (power : Fin 11 → ℕ) : Flag :=
  ⟨∑ j ∈ s, (power j : ℤ) * (factorFlag j).degree,
    ∑ j ∈ s, (power j : ℤ) * (factorFlag j).lower,
    ∑ j ∈ s, (power j : ℤ) * (factorFlag j).upper,
    ∑ j ∈ s, (power j : ℤ) * (factorFlag j).cap,
    ∑ j ∈ s, (power j : ℤ) * (factorFlag j).order⟩
private theorem certificate_prod (s : Finset (Fin 11)) (power : Fin 11 → ℕ) :
    Certificate (sumFlags s power) (∏ j ∈ s, factor j ^ power j) := by
  induction s using Finset.induction_on with
  | empty => simpa [sumFlags] using certificate_one
  | insert j s hj ih =>
      have h : Certificate (factorFlag j) (factor j) :=
        ⟨factor_mem_oldSpace j, factor_contact j⟩
      simpa [sumFlags, Finset.sum_insert hj, Finset.prod_insert hj, addFlag, scaleFlag] using
        (h.pow (power j)).mul ih
private theorem add_residual (F : Flag) (power : Fin 11 → ℕ) :
    addFlag (sumFlags Finset.univ power) (residualFlag F power) = F := by
  cases F
  simp [addFlag, sumFlags, residualFlag]
private theorem mem_ker_iff {F : Flag} (p : oldSpace F) :
    p ∈ LinearMap.ker (flagContact F) ↔
      coordinateChange (p : JetPoly) ∈ restrictWeightedOrder contactWeight F.order.toNat :=
  weightedTruncation_eq_zero_iff _ _ _
theorem proof : K1_13_2_2.c5 := by
  intro F power
  let R := residualFlag F power
  let T : JetPoly := ∏ j, factor j ^ power j
  have hT : T ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (factor_ne_zero j)
  have hCert : Certificate (sumFlags Finset.univ power) T := certificate_prod Finset.univ power
  let multiply : LinearMap.ker (flagContact R) →ₗ[Geom] JetPoly :=
    (LinearMap.mulLeft Geom T).comp
      ((oldSpace R).subtype.comp (LinearMap.ker (flagContact R)).subtype)
  have hMul (p : LinearMap.ker (flagContact R)) : Certificate F (multiply p) := by
    have hp : Certificate R (p.1 : JetPoly) := ⟨p.1.2, (mem_ker_iff p.1).mp p.2⟩
    have h := hCert.mul hp
    rw [show addFlag (sumFlags Finset.univ power) R = F from add_residual F power] at h
    exact h
  let lift := multiply.codRestrict (oldSpace F) fun p => (hMul p).old_mem
  let f := lift.codRestrict (LinearMap.ker (flagContact F)) fun p =>
    (mem_ker_iff (lift p)).mpr (hMul p).contact_mem
  refine ⟨f, ?_⟩
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  exact mul_left_cancel₀ hT (congrArg (fun r : LinearMap.ker (flagContact F) => (r.1 : JetPoly)) hpq)
end
end K1_13_2_2_5
end
section
namespace K1_13_2_2_1
noncomputable section
open K1_13 K1_13_2 K1_13_2_2
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
private def residualDegree (i : BlockIndex) : ℕ := min i.1.val 1650
private theorem active_degree (i : BlockIndex) :
    (activeFlag i).degree = (residualDegree i : ℤ) := by
  change min (i.1.val : ℤ) 1650 = ((min i.1.val 1650 : ℕ) : ℤ)
  omega
private def removed (i : BlockIndex) : ℕ := i.1.val - residualDegree i
private def stripped (i : BlockIndex) (e : SourceExponent) : JetExp :=
  Finsupp.equivFunOnFinite.symm
    ![e (some 0) - removed i, e (some 1), e (some 2), e (some 3)]
private theorem source_grade (e : SourceExponent) :
    e.weight jetDegreeWeight = e (some 0) + e (some 1) + e (some 2) + e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four]
private theorem source_index (e : SourceExponent) :
    e.weight jetDerivativeWeight = e (some 1) + 2 * e (some 2) + 3 * e (some 3) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_four, jetDerivativeWeight,
    smul_eq_mul, Nat.mul_comm]
private theorem removed_le (i : BlockIndex) (e : blockExponents i) :
    removed i ≤ e.val (some 0) := by
  have hd := e.property.2.2.1
  have hj := e.property.1.2.1
  rw [source_grade] at hd
  rw [source_index] at hj
  simp only [removed, residualDegree]
  omega
private theorem stripped_mem (i : BlockIndex) (e : blockExponents i) :
    stripped i e ∈ oldExponents (activeFlag i) := by
  have hd := e.property.2.2.1
  have hj := e.property.1.2.1
  have hc := e.property.1.2.2.1
  have hx := e.property.2.1
  have hg := e.property.2.2.2
  have ha := removed_le i e
  rw [source_grade] at hd
  rw [source_index] at hj hg
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, topWeight, Pi.single_apply,
    smul_eq_mul] at hc
  change ((stripped i e).weight gradeWeight : ℤ) = (activeFlag i).degree ∧
    -offset i ≤ ((stripped i e).weight oldWeight : ℤ) ∧
    ((stripped i e).weight oldWeight : ℤ) ≤ min 1650 (2999 - offset i) ∧
    ((stripped i e) 3 : ℤ) ≤ 550
  rw [active_degree]
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, gradeWeight, oldWeight, stripped,
    smul_eq_mul, Nat.mul_comm]
  simp only [removed, residualDegree] at *
  omega
private def encodeColumn (i : BlockIndex) (e : blockExponents i) : oldSpace (activeFlag i) := by
  refine ⟨monomial (stripped i e) 1, ?_⟩
  change monomial (stripped i e) 1 ∈ restrictSupport Geom (oldExponents (activeFlag i))
  exact (monomial_mem_restrictSupport Geom).mpr (Or.inl (stripped_mem i e))
private def encode (i : BlockIndex) : BlockSpace i →ₗ[Geom] oldSpace (activeFlag i) :=
  (basisRestrictSupport Geom (blockExponents i)).constr Geom (encodeColumn i)
private theorem encode_basis (i : BlockIndex) (e : blockExponents i) :
    ((encode i (basisRestrictSupport Geom (blockExponents i) e)) : JetPoly) =
      monomial (stripped i e) 1 :=
  congrArg Subtype.val
    ((basisRestrictSupport Geom (blockExponents i)).constr_basis Geom (encodeColumn i) e)
local notation "T" => (MvPolynomial.X (localT 3) : Local)
local notation "E" => (MvPolynomial.X (localE 3) : Local)
private def jetVar (j : Fin 3) : Local := MvPolynomial.X (localY j)
private def valueImage : Local := unscaledLocalImage 3 0 0 (some 0)
private def scaledImage : Fin 4 → Local :=
  ![T * E, T * jetVar 0, T ^ 2 * jetVar 1, T ^ 3 * jetVar 2]
private def originSubst : SourcePolynomial →ₐ[Geom] Local := unscaledLocalSubstitution 3 0 0
private theorem scaled_shear_zero : bind₁ scaledImage (shearImage 0) = valueImage := by
  simp [shearImage, scaledImage, valueImage, unscaledLocalImage, localCorrection, Fin.sum_univ_three, jetVar]
  ring
private theorem scaled_shear_succ (j : Fin 3) :
    bind₁ scaledImage (shearImage j.succ) = T ^ j.succ.val * jetVar j := by
  fin_cases j <;> simp [shearImage, scaledImage]
private theorem bind_monomial_one {σ τ : Type*} [Fintype σ]
    (f : σ → MvPolynomial τ Geom) (e : σ →₀ ℕ) :
    bind₁ f (monomial e 1) = ∏ j, f j ^ e j := by
  rw [bind₁_monomial, C_1, one_mul]
  exact Finsupp.prod_fintype e (fun j n => f j ^ n) (fun _ => pow_zero _)
private theorem origin_monomial (e : SourceExponent) :
    originSubst (monomial e 1) = T ^ e none *
      (valueImage ^ e (some 0) * (jetVar 0) ^ e (some 1) * (jetVar 1) ^ e (some 2) * (jetVar 2) ^ e (some 3)) := by
  rw [originSubst, unscaledLocalSubstitution, bind_monomial_one, Fintype.prod_option, Fin.prod_univ_four]
  change (C (0 : Geom) + T) ^ e none *
    (valueImage ^ e (some 0) * (jetVar 0) ^ e (some 1) * (jetVar 1) ^ e (some 2) * (jetVar 2) ^ e (some 3)) = _
  simp
private theorem stripped_monomial (i : BlockIndex) (e : SourceExponent) :
    bind₁ scaledImage (coordinateChange (monomial (stripped i e) 1)) =
    valueImage ^ (e (some 0) - removed i) *
      (T * jetVar 0) ^ e (some 1) * (T ^ 2 * jetVar 1) ^ e (some 2) * (T ^ 3 * jetVar 2) ^ e (some 3) := by
  rw [coordinateChange, bind₁_bind₁, bind_monomial_one, Fin.prod_univ_four]
  have h1 := scaled_shear_succ (0 : Fin 3)
  have h2 := scaled_shear_succ (1 : Fin 3)
  have h3 := scaled_shear_succ (2 : Fin 3)
  change bind₁ scaledImage (shearImage 1) = T ^ 1 * jetVar 0 at h1
  change bind₁ scaledImage (shearImage 2) = T ^ 2 * jetVar 1 at h2
  change bind₁ scaledImage (shearImage 3) = T ^ 3 * jetVar 2 at h3
  simp [scaled_shear_zero, h1, h2, h3, stripped]
private theorem shifted_origin_monomial (i : BlockIndex) (e : blockExponents i) :
    T ^ (-offset i).toNat * originSubst (monomial e.val 1) =
    T ^ (offset i).toNat * valueImage ^ removed i *
      bind₁ scaledImage (coordinateChange (monomial (stripped i e) 1)) := by
  have hx := e.property.2.2.2
  rw [source_index] at hx
  have ht : (-offset i).toNat + e.val none =
      (offset i).toNat + e.val (some 1) + 2 * e.val (some 2) + 3 * e.val (some 3) := by omega
  have ha : removed i + (e.val (some 0) - removed i) = e.val (some 0) := by
    have := removed_le i e
    omega
  have hT : T ^ (-offset i).toNat * T ^ e.val none =
      T ^ (offset i).toNat * T ^ e.val (some 1) * T ^ (2 * e.val (some 2)) *
        T ^ (3 * e.val (some 3)) := by
    simpa only [pow_add] using congrArg (T ^ ·) ht
  have hA : valueImage ^ e.val (some 0) =
      valueImage ^ removed i * valueImage ^ (e.val (some 0) - removed i) := by
    rw [← pow_add, ha]
  rw [origin_monomial, stripped_monomial]
  simp only [mul_pow, ← pow_mul]
  calc
    _ = (T ^ (-offset i).toNat * T ^ e.val none) *
        (valueImage ^ e.val (some 0) * (jetVar 0) ^ e.val (some 1) *
          (jetVar 1) ^ e.val (some 2) * (jetVar 2) ^ e.val (some 3)) := by ring
    _ = _ := by rw [hT, hA]; ring
private theorem shifted_origin (i : BlockIndex) (p : BlockSpace i) :
    T ^ (-offset i).toNat * originSubst (p : SourcePolynomial) =
    T ^ (offset i).toNat * valueImage ^ removed i *
      bind₁ scaledImage (coordinateChange ((encode i p : oldSpace (activeFlag i)) : JetPoly)) := by
  let l := (LinearMap.mulLeft Geom (T ^ (-offset i).toNat)).comp
    (originSubst.toLinearMap.comp (BlockSpace i).subtype)
  let r := (LinearMap.mulLeft Geom (T ^ (offset i).toNat * valueImage ^ removed i)).comp
    ((bind₁ scaledImage).toLinearMap.comp
      (coordinateChange.toLinearMap.comp ((oldSpace (activeFlag i)).subtype.comp (encode i))))
  have h : l = r := by
    apply (basisRestrictSupport Geom (blockExponents i)).ext
    intro e
    change T ^ (-offset i).toNat *
      originSubst (↑(basisRestrictSupport Geom (blockExponents i) e) : SourcePolynomial) =
      T ^ (offset i).toNat * valueImage ^ removed i *
        bind₁ scaledImage (coordinateChange
          (↑(encode i (basisRestrictSupport Geom (blockExponents i) e)) : JetPoly))
    rw [encode_basis, coe_basisRestrictSupport_apply]
    exact shifted_origin_monomial i e
  exact LinearMap.congr_fun h p
private def scaledWeight (j : Fin 4) : ℕ := contactWeight j + gradeWeight j
private theorem weight_scaled (e : JetExp) :
    e.weight scaledWeight = e.weight contactWeight + e.weight gradeWeight := by
  simp [Finsupp.weight_eq_sum, scaledWeight, smul_eq_mul, Nat.mul_add, Finset.sum_add_distrib]
private theorem t_power_order (n : ℕ) :
    T ^ n ∈ restrictWeightedOrder (localContactWeight 3) n := by
  simpa using pow_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := Geom) (localContactWeight 3) (localT 3) (m := 1) le_rfl) n
private theorem scaled_image_order (j : Fin 4) :
    scaledImage j ∈ restrictWeightedOrder (localContactWeight 3) (scaledWeight j) := by
  have hY (k : Fin 3) : jetVar k ∈ restrictWeightedOrder (localContactWeight 3) 0 := by simp
  have hE : E ∈ restrictWeightedOrder (localContactWeight 3) 3 :=
    X_mem_restrictWeightedOrder _ _ le_rfl
  fin_cases j
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 1) hE
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 1) (hY 0)
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 2) (hY 1)
  · simpa [scaledImage, scaledWeight, contactWeight, gradeWeight] using
      mul_mem_restrictWeightedOrder (t_power_order 3) (hY 2)
private theorem value_order :
    valueImage ∈ restrictWeightedOrder (localContactWeight 3) 1 := by
  have h (j : Fin 4) : scaledImage j ∈ restrictWeightedOrder (localContactWeight 3) 1 :=
    restrictWeightedOrder_anti _ (Nat.succ_le_succ (Nat.zero_le _)) (scaled_image_order j)
  rw [← scaled_shear_zero]
  simp only [shearImage, ite_true, map_add, map_sub, bind₁_X_right]
  exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ (h 0) (h 1)) (h 2)) (h 3)
private theorem order_of_t_power_mul {n m : ℕ} {p : Local}
    (h : T ^ n * p ∈ restrictWeightedOrder (localContactWeight 3) (m + n)) :
    p ∈ restrictWeightedOrder (localContactWeight 3) m := by
  rw [MvPolynomial.X_pow_eq_monomial] at h
  intro e he
  have hh := mem_restrictWeightedOrder.mp h (Finsupp.single (localT 3) n + e) (by
    rw [MvPolynomial.mem_support_iff, coeff_monomial_mul, one_mul]
    exact MvPolynomial.mem_support_iff.mp he)
  change m ≤ e.weight (localContactWeight 3)
  simp only [map_add, Finsupp.weight_single, localContactWeight_T, smul_eq_mul, mul_one] at hh
  omega
private theorem kernel_le (i : BlockIndex) :
    LinearMap.ker ((flagContact (activeFlag i)).comp (encode i)) ≤ LinearMap.ker (originBlock i) := by
  intro p hp
  let q : oldSpace (activeFlag i) := encode i p
  let shear : JetPoly := coordinateChange (q : JetPoly)
  let cut := (activeFlag i).order.toNat
  have hz : weightedTruncation contactWeight cut shear = 0 := LinearMap.mem_ker.mp hp
  have hcontact := (weightedTruncation_eq_zero_iff _ _ _).mp hz
  have hgrade : (q : JetPoly).IsWeightedHomogeneous gradeWeight (residualDegree i) := by
    intro e he
    have hd := (q.property (mem_support_iff.mpr he)).1
    change (e.weight gradeWeight : ℤ) = (activeFlag i).degree at hd
    rw [active_degree] at hd
    omega
  have hshear : shear.IsWeightedHomogeneous gradeWeight (residualDegree i) :=
    hgrade.bind₁ shearImage_grade
  have hscaled : shear ∈ restrictWeightedOrder scaledWeight (cut + residualDegree i) := by
    intro e he
    have hg := hshear (mem_support_iff.mp he)
    have hc := mem_restrictWeightedOrder.mp hcontact e he
    change cut + residualDegree i ≤ e.weight scaledWeight
    rw [weight_scaled, hg]
    exact Nat.add_le_add_right hc _
  have hprod := mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder (t_power_order (offset i).toNat)
      (by simpa using pow_mem_restrictWeightedOrder value_order (removed i)))
    (bind₁_mem_restrictWeightedOrder scaled_image_order hscaled)
  have hbound : 3000 + (-offset i).toNat ≤
      (offset i).toNat + removed i + (cut + residualDegree i) := by
    change 3000 + (-offset i).toNat ≤ (offset i).toNat + removed i +
      ((3000 - (i.1.val : ℤ) - offset i).toNat + residualDegree i)
    simp only [removed, residualDegree]
    omega
  have hshift : T ^ (-offset i).toNat * originSubst (p : SourcePolynomial) ∈
      restrictWeightedOrder (localContactWeight 3) (3000 + (-offset i).toNat) := by
    rw [shifted_origin]
    exact restrictWeightedOrder_anti _ hbound hprod
  apply LinearMap.mem_ker.mpr
  change weightedTruncation (localContactWeight 3) 3000 (originSubst (p : SourcePolynomial)) = 0
  exact (weightedTruncation_eq_zero_iff _ _ _).mpr (order_of_t_power_mul hshift)
theorem proof : K1_13_2_2.c1 := by
  intro i
  let f := (flagContact (activeFlag i)).comp (encode i)
  have hker := Submodule.finrank_mono (kernel_le i)
  change Module.finrank Geom (LinearMap.ker f) ≤
    Module.finrank Geom (LinearMap.ker (originBlock i)) at hker
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ := (originBlock i).finrank_range_add_finrank_ker
  exact (show Module.finrank Geom (LinearMap.range (originBlock i)) ≤
      Module.finrank Geom (LinearMap.range f) by omega).trans
    (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))
end
end K1_13_2_2_1
end
section
namespace K1_13_2_2_4
noncomputable section
open K1_13_2 K1_13_2_2
private theorem columns_finite (w : Fin 4 → ℕ) (d u : ℤ) :
    {e : JetExp | (e.weight gradeWeight : ℤ) = d ∧ (e.weight w : ℤ) ≤ u}.Finite :=
  finite_of_grade fun _ h => h.1
private def columns (w : Fin 4 → ℕ) (d u : ℤ) : Finset JetExp :=
  (columns_finite w d u).toFinset
private theorem mem_columns {w : Fin 4 → ℕ} {d u : ℤ} {e : JetExp} :
    e ∈ columns w d u ↔ (e.weight gradeWeight : ℤ) = d ∧ (e.weight w : ℤ) ≤ u :=
  (columns_finite w d u).mem_toFinset
private def cappedColumns (w : Fin 4 → ℕ) (d u : ℤ) (r : ℕ) : Finset JetExp :=
  (columns w d u).filter fun e => e 0 < r
private theorem mem_cappedColumns {w : Fin 4 → ℕ} {d u : ℤ} {r : ℕ} {e : JetExp} :
    e ∈ cappedColumns w d u r ↔
      (e.weight gradeWeight : ℤ) = d ∧ (e.weight w : ℤ) ≤ u ∧ e 0 < r := by
  simp only [cappedColumns, Finset.mem_filter, mem_columns, and_assoc]
private theorem card_old (hc : CumulativeCount) (d u : ℤ) :
    ((columns oldWeight d u).card : ℤ) = cumulative d u := by
  have h : columns oldWeight d u = cumulativeColumns d u := by
    ext e
    exact mem_columns.trans mem_cumulativeColumns.symm
  rw [h]
  exact hc d u
private theorem card_contact (hc : CumulativeCount) (d u : ℤ) :
    ((columns contactWeight d u).card : ℤ) = cumulative d u := by
  have hweight (i : Fin 4) : contactWeight (finRotate 4 i) = oldWeight i := by
    fin_cases i <;> rfl
  have h : (columns oldWeight d u).card = (columns contactWeight d u).card := by
    apply Finset.card_equiv (Finsupp.equivCongrLeft (finRotate 4))
    intro e
    simp only [mem_columns, Finsupp.equivCongrLeft_apply, Finsupp.weight_apply,
      Finsupp.sum_equivMapDomain, gradeWeight, hweight]
  rw [← h, card_old hc]
private theorem card_capped (w : Fin 4 → ℕ) (d u : ℤ) (r : ℕ) :
    ((cappedColumns w d u r).card : ℤ) = ((columns w d u).card : ℤ) -
      ((columns w (d - r) (u - r * (w 0 : ℤ))).card : ℤ) := by
  classical
  let tail := (columns w d u).filter fun e => r ≤ e 0
  have hshift (e : JetExp) :
      e ∈ columns w (d - r) (u - r * (w 0 : ℤ)) ↔
        e + Finsupp.single 0 r ∈ tail := by
    simp only [tail, Finset.mem_filter, mem_columns, map_add, Finsupp.weight_single,
      Finsupp.add_apply, Finsupp.single_eq_same, gradeWeight, smul_eq_mul, mul_one,
      Nat.cast_add, Nat.cast_mul]
    omega
  have htail : (columns w (d - r) (u - r * (w 0 : ℤ))).card = tail.card := by
    apply Finset.card_bij (fun e _ => e + Finsupp.single 0 r)
    · exact fun e he => (hshift e).mp he
    · intro e _ f _ hef
      exact add_right_cancel hef
    · intro e he
      have hr : r ≤ e 0 := (Finset.mem_filter.mp he).2
      have hle : Finsupp.single (0 : Fin 4) r ≤ e := by
        apply Finsupp.le_def.mpr
        intro i
        by_cases hi : (0 : Fin 4) = i
        · subst i
          simpa using hr
        · simp [hi]
      have heq : e - Finsupp.single 0 r + Finsupp.single 0 r = e := tsub_add_cancel_of_le hle
      exact ⟨_, (hshift _).mpr (by rwa [heq]), heq⟩
  have hdiff : columns w d u \ tail = cappedColumns w d u r := by
    ext e
    by_cases he : e ∈ columns w d u <;> simp [tail, cappedColumns, he]
  have hp := Finset.card_sdiff_add_card_eq_card
    (show tail ⊆ columns w d u from Finset.filter_subset _ _)
  rw [hdiff, ← htail] at hp
  omega
private theorem weight_identity (e : JetExp) :
    (e.weight oldWeight : ℤ) =
      (e.weight gradeWeight : ℤ) + (e.weight contactWeight : ℤ) - 4 * (e 0 : ℤ) := by
  have h : e.weight oldWeight + 4 * e 0 = e.weight gradeWeight + e.weight contactWeight := by
    simp only [Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul]
    change e 0 * 0 + e 1 * 1 + e 2 * 2 + e 3 * 3 + 4 * e 0 =
      (e 0 * 1 + e 1 * 1 + e 2 * 1 + e 3 * 1) +
        (e 0 * 3 + e 1 * 0 + e 2 * 1 + e 3 * 2)
    omega
  omega
theorem proof : K1_13_2_2.c4 := by
  classical
  intro hc F
  let balance : ℤ := F.order - 1 - F.lower + F.degree
  let removed : ℤ := min F.degree (balance / 4) + 1
  change _ = if balance < 0 then 0 else
    cumulative F.degree (F.order - 1) -
      cumulative (F.degree - removed) (F.order - 1 - 3 * removed) -
      cumulative F.degree (F.lower - 1) + cumulative (F.degree - removed) (F.lower - 1)
  by_cases hb : balance < 0
  · rw [ite_eq_left hb]
    have hempty : targetColumns F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨hg, hl, ho⟩ := mem_targetColumns.mp he
      have hw := weight_identity e
      dsimp only [balance] at hb
      omega
    simp [hempty]
  rw [ite_eq_right hb]
  have hdiv : 0 ≤ balance / 4 := by omega
  by_cases hd : F.degree < 0
  · have hempty : targetColumns F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hg := (mem_targetColumns.mp he).1
      omega
    have hmin : min F.degree (balance / 4) = F.degree := min_eq_left (by omega)
    have hr : F.degree - removed = -1 := by
      dsimp only [removed]
      rw [hmin]
      omega
    simp [hempty, hr, cumulative, hd]
  have hremoved : 0 ≤ removed := by
    have hmin : 0 ≤ min F.degree (balance / 4) := le_min (by omega) hdiv
    dsimp only [removed]
    omega
  let r := removed.toNat
  have hr : (r : ℤ) = removed := by
    dsimp only [r]
    omega
  have hcap (e : JetExp) : e 0 < r ↔ (e 0 : ℤ) ≤ min F.degree (balance / 4) := by
    dsimp only [removed] at hr
    omega
  let contact := cappedColumns contactWeight F.degree (F.order - 1) r
  let old := cappedColumns oldWeight F.degree (F.lower - 1) r
  have hsub : old ⊆ contact := by
    intro e he
    obtain ⟨hg, hi, ha⟩ := mem_cappedColumns.mp he
    have ha' := (le_min_iff.mp ((hcap e).mp ha)).2
    have hw := weight_identity e
    have hbal : 4 * (e 0 : ℤ) ≤ balance := by omega
    dsimp only [balance] at hbal
    exact mem_cappedColumns.mpr ⟨hg, by omega, ha⟩
  have hdiff : targetColumns F = contact \ old := by
    ext e
    rw [mem_targetColumns, Finset.mem_sdiff]
    change ((e.weight gradeWeight : ℤ) = F.degree ∧ F.lower ≤ (e.weight oldWeight : ℤ) ∧
      (e.weight contactWeight : ℤ) < F.order) ↔ e ∈ contact ∧ e ∉ old
    simp only [contact, old, mem_cappedColumns]
    constructor
    · rintro ⟨hg, hi, ho⟩
      have hw := weight_identity e
      have hgrade := Finsupp.le_weight gradeWeight (s := (0 : Fin 4)) (by decide) e
      have hd' : (e 0 : ℤ) ≤ F.degree := by omega
      have hb' : 4 * (e 0 : ℤ) ≤ balance := by
        dsimp only [balance]
        omega
      have ha := (hcap e).mpr (le_min hd' (by omega))
      refine ⟨⟨hg, by omega, ha⟩, ?_⟩
      intro he
      have hi' := he.2.1
      omega
    · rintro ⟨⟨hg, ho, ha⟩, hn⟩
      refine ⟨hg, ?_, by omega⟩
      by_contra! hi
      exact hn ⟨hg, by omega, ha⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [← hdiff] at hcard
  have hcontact := card_capped contactWeight F.degree (F.order - 1) r
  have hold := card_capped oldWeight F.degree (F.lower - 1) r
  change (contact.card : ℤ) = _ at hcontact
  change (old.card : ℤ) = _ at hold
  simp only [card_contact hc, hr, show (contactWeight 0 : ℤ) = 3 by rfl,
    mul_comm removed 3] at hcontact
  simp only [card_old hc, hr, show (oldWeight 0 : ℤ) = 0 by rfl, mul_zero, sub_zero] at hold
  omega
end
end K1_13_2_2_4
end
section
namespace K1_13_2_2_3
open K1_13_2 K1_13_2_2
noncomputable section
private def top (k : ℕ) : JetExp := Finsupp.single 3 k
private def tailColumns (d u : ℤ) (k : ℕ) : Finset JetExp :=
  (cumulativeColumns d u).filter fun e => k ≤ e 3
private def cappedColumns (d u cap : ℤ) : Finset JetExp :=
  (cumulativeColumns d u).filter fun e => (e 3 : ℤ) ≤ cap
private theorem mem_tailColumns {d u : ℤ} {k : ℕ} {e : JetExp} :
    e ∈ tailColumns d u k ↔ e ∈ cumulativeColumns d u ∧ k ≤ e 3 :=
  Finset.mem_filter
private theorem mem_cappedColumns {d u cap : ℤ} {e : JetExp} :
    e ∈ cappedColumns d u cap ↔ e ∈ cumulativeColumns d u ∧ (e 3 : ℤ) ≤ cap :=
  Finset.mem_filter
private theorem weight_add_top (w : Fin 4 → ℕ) (e : JetExp) (k : ℕ) :
    ((e + top k).weight w : ℤ) = (e.weight w : ℤ) + (w 3 : ℤ) * (k : ℤ) := by
  simp only [map_add, top, Finsupp.weight_single, smul_eq_mul, Nat.cast_add, Nat.cast_mul,
    mul_comm]
private theorem grade_add_top (e : JetExp) (k : ℕ) :
    ((e + top k).weight gradeWeight : ℤ) = (e.weight gradeWeight : ℤ) + k := by
  simpa only [gradeWeight, Nat.cast_one, one_mul] using weight_add_top gradeWeight e k
private theorem old_add_top (e : JetExp) (k : ℕ) :
    ((e + top k).weight oldWeight : ℤ) = (e.weight oldWeight : ℤ) + 3 * (k : ℤ) :=
  weight_add_top oldWeight e k
private theorem sub_add_top (e : JetExp) (k : ℕ) (he : k ≤ e 3) :
    e - top k + top k = e :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr he)
private theorem tail_card (d u : ℤ) (k : ℕ) :
    (tailColumns d u k).card = (cumulativeColumns (d - k) (u - 3 * (k : ℤ))).card := by
  refine Finset.card_nbij' (fun e => e - top k) (fun e => e + top k) ?_ ?_ ?_ ?_
  · intro e he
    change e ∈ tailColumns d u k at he
    obtain ⟨he, htop⟩ := mem_tailColumns.mp he
    obtain ⟨hd, hu⟩ := mem_cumulativeColumns.mp he
    have hg := grade_add_top (e - top k) k
    have hw := old_add_top (e - top k) k
    rw [sub_add_top e k htop] at hg hw
    apply mem_cumulativeColumns.mpr
    change ((e - top k).weight gradeWeight : ℤ) = d - k ∧
      ((e - top k).weight oldWeight : ℤ) ≤ u - 3 * (k : ℤ)
    exact ⟨by omega, by omega⟩
  · intro e he
    change e ∈ cumulativeColumns (d - k) (u - 3 * (k : ℤ)) at he
    obtain ⟨hd, hu⟩ := mem_cumulativeColumns.mp he
    apply mem_tailColumns.mpr
    refine ⟨mem_cumulativeColumns.mpr ?_, ?_⟩
    · rw [cumulativeExponents, Set.mem_ofPred_eq, grade_add_top, old_add_top]
      exact ⟨by omega, by omega⟩
    · simp [Finsupp.add_apply, top]
  · intro e he
    exact sub_add_top e k (mem_tailColumns.mp he).2
  · intro e _
    exact add_tsub_cancel_right e (top k)
private theorem card_sdiff_int {s t : Finset JetExp} (h : t ⊆ s) :
    ((s \ t).card : ℤ) = (s.card : ℤ) - (t.card : ℤ) := by
  have hc := Finset.card_sdiff_add_card_eq_card h
  omega
private theorem capped_card (hc : CumulativeCount) (d u cap : ℤ) :
    ((cappedColumns d u cap).card : ℤ) = cappedCount d u cap := by
  by_cases hcap : cap < 0
  · have hempty : cappedColumns d u cap = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have h := (mem_cappedColumns.mp he).2
      omega
    simp [hempty, cappedCount, hcap]
  · let k := (cap + 1).toNat
    have hk : (k : ℤ) = cap + 1 := Int.toNat_of_nonneg (by omega)
    have hsubset : tailColumns d u k ⊆ cumulativeColumns d u := fun _ he =>
      (mem_tailColumns.mp he).1
    have hset : cappedColumns d u cap = cumulativeColumns d u \ tailColumns d u k := by
      ext e
      simp only [mem_cappedColumns, Finset.mem_sdiff, mem_tailColumns]
      constructor
      · rintro ⟨he, htop⟩
        refine ⟨he, ?_⟩
        rintro ⟨_, htail⟩
        omega
      · rintro ⟨he, htail⟩
        refine ⟨he, ?_⟩
        by_contra htop
        exact htail ⟨he, by omega⟩
    have hd : d - (k : ℤ) = d - cap - 1 := by omega
    have hu : u - 3 * (k : ℤ) = u - 3 * (cap + 1) := by rw [hk]
    rw [hset, card_sdiff_int hsubset, tail_card, hc d u,
      hc (d - k) (u - 3 * (k : ℤ)), hd, hu, cappedCount, ite_eq_right hcap]
private theorem capped_subset {d u v cap : ℤ} (huv : u ≤ v) :
    cappedColumns d u cap ⊆ cappedColumns d v cap := by
  intro e he
  rw [mem_cappedColumns, mem_cumulativeColumns] at he ⊢
  obtain ⟨⟨hd, hu⟩, hcap⟩ := he
  exact ⟨⟨hd, hu.trans huv⟩, hcap⟩
private theorem oldColumns_eq (F : Flag) :
    oldColumns F =
      cappedColumns F.degree F.upper F.cap \
        cappedColumns F.degree (min F.upper (F.lower - 1)) F.cap := by
  ext e
  simp only [mem_oldColumns, oldExponents, Finset.mem_sdiff, mem_cappedColumns,
    mem_cumulativeColumns, cumulativeExponents, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hd, hl, hu, hcap⟩
    refine ⟨⟨⟨hd, hu⟩, hcap⟩, ?_⟩
    rintro ⟨⟨_, hcut⟩, _⟩
    have h := hcut.trans (min_le_right _ _)
    omega
  · rintro ⟨⟨⟨hd, hu⟩, hcap⟩, hexcluded⟩
    refine ⟨hd, ?_, hu, hcap⟩
    by_contra hl
    exact hexcluded ⟨⟨hd, le_min hu (by omega)⟩, hcap⟩
theorem proof : K1_13_2_2.c3 := by
  intro hc F
  rw [oldColumns_eq, card_sdiff_int (capped_subset (min_le_left _ _)),
    capped_card hc, capped_card hc, oldCount]
end
end K1_13_2_2_3
end
section
namespace K1_13_7_4
noncomputable section
open Polynomial K1_13 K1_13_7
open scoped BigOperators
def shiftHom (S : Geom[X]) : Row 3 →+* Row 3 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i))
theorem genericCoeff_injective : Function.Injective genericCoeff :=
  (algebraMap GenericX GeometricX).injective.comp
    (IsFractionRing.injective Geom[X] GenericX)
def genericHom : Row 3 →+* Lower := MvPolynomial.map genericCoeff
@[simp] theorem genericHom_apply (F : Row 3) : genericHom F = genericRow F := rfl
private theorem support_mul_C_subset {A : Type*} [CommSemiring A]
    (F : MvPolynomial (Fin 3) A) (a : A) :
    (MvPolynomial.C a * F).support ⊆ F.support := by
  intro m hm
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm ⊢
  exact right_ne_zero_of_mul hm
theorem exists_avoiding (V : Submodule Geom (Row 3)) (I : Set (Ideal Lower))
    (hfin : I.Finite) (hw : ∀ p ∈ I, ∃ R ∈ V, genericRow R ∉ p) :
    ∃ R ∈ V, ∀ p ∈ I, genericRow R ∉ p := by
  have : Finite I := hfin.to_subtype
  let lin : Row 3 →ₗ[Geom] Lower := {
    toFun := genericHom
    map_add' := map_add genericHom
    map_smul' := by
      intro a R
      simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
      congr 1
      rw [IsScalarTower.algebraMap_apply Geom Geom[X] (Row 3),
        IsScalarTower.algebraMap_apply Geom GeometricX Lower]
      change genericHom (MvPolynomial.C (algebraMap Geom Geom[X] a)) =
        MvPolynomial.C (algebraMap Geom GeometricX a)
      rw [genericHom, MvPolynomial.map_C]
      congr 1 }
  let W (p : I) : Submodule Geom V :=
    ((p.val.restrictScalars Geom).comap lin).comap V.subtype
  have hW (p : I) : W p ≠ ⊤ := by
    obtain ⟨R, hR, hn⟩ := hw p.val p.property
    intro h
    apply hn
    change (⟨R, hR⟩ : V) ∈ W p
    simp [h]
  obtain ⟨R, hR⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := I) (K := Geom) (M := V) W hW
  exact ⟨R.val, R.property, fun p hp => hR ⟨p, hp⟩⟩
theorem pair_le_iff {P Q : Row 3} {p : Ideal Lower} :
    pairIdeal P Q ≤ p ↔ genericRow P ∈ p ∧ genericRow Q ∈ p := by
  simp [pairIdeal, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
theorem triple_le_iff {P Q R : Row 3} {p : Ideal Lower} :
    tripleIdeal P Q R ≤ p ↔ genericRow P ∈ p ∧ genericRow Q ∈ p ∧ genericRow R ∈ p := by
  simp [tripleIdeal, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
theorem pair_height {P Q : Row 3} (hpq : ProperLowerPair P Q)
    {p : Ideal Lower} (hp : p ∈ (pairIdeal P Q).minimalPrimes) : p.height = 2 := by
  have : p.IsPrime := hp.isPrime
  have hncard : ({genericRow P, genericRow Q} : Set Lower).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by simp)
  have hle : p.height ≤ 2 :=
    (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hp).trans (by exact_mod_cast hncard)
  have hP := (pair_le_iff.mp hp.le).1
  have hQ := (pair_le_iff.mp hp.le).2
  have hnP : genericRow P ≠ 0 := by
    simpa [genericRow] using (MvPolynomial.map_injective _ genericCoeff_injective).ne hpq.1
  have hpbot : p ≠ ⊥ := fun h => hnP (Ideal.mem_bot.mp (h ▸ hP))
  have hone : 1 ≤ p.height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hpbot)
    simpa [Ideal.height_bot] using h
  have hnot : p.height ≠ 1 := by
    intro h
    have hprincipal := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one h
    obtain ⟨x, hx⟩ := hprincipal.principal
    change p = Ideal.span {x} at hx
    have hxP : x ∣ genericRow P := Ideal.mem_span_singleton.mp (by rw [← hx]; exact hP)
    have hxQ : x ∣ genericRow Q := Ideal.mem_span_singleton.mp (by rw [← hx]; exact hQ)
    have hxunit : IsUnit x := hpq.2.2 hxP hxQ
    exact Ideal.IsPrime.ne_top' (hx.trans (Ideal.span_singleton_eq_top.mpr hxunit))
  exact le_antisymm hle ((ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr
    (lt_of_le_of_ne hone (Ne.symm hnot)))
theorem height_le_three (p : PrimeSpectrum Lower) : p.asIdeal.height ≤ 3 := by
  have h := Ideal.height_le_ringKrullDim_of_isPrime (I := p.asIdeal)
  have hd : ringKrullDim Lower = 3 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [hd] at h
  exact WithBot.coe_le_coe.mp h
theorem localColength_lt_top {q : PrimeSpectrum Lower} {J : Ideal Lower}
    (hq : q.asIdeal ∈ J.minimalPrimes) : localColength q J < ⊤ := by
  let A := Localization.AtPrime q.asIdeal
  let L := J.map (algebraMap Lower A)
  change Module.length A (A ⧸ L) < ⊤
  have hmin : IsLocalRing.maximalIdeal A ∈ L.minimalPrimes := by
    rw [show L = J.map (algebraMap Lower A) from rfl,
      IsLocalization.minimalPrimes_map q.asIdeal.primeCompl A, Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A q.asIdeal]
    exact hq
  have : IsArtinianRing (A ⧸ L) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing L hmin
  exact lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_quotient L,
        isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := L))⟩))
def pointPrime (y : LowerPoint) : PrimeSpectrum Lower :=
  ⟨pointIdeal y, RingHom.ker_isPrime (MvPolynomial.eval y)⟩
theorem vanishes_at_prime {q : PrimeSpectrum Lower} {F : Lower} {d : ℕ}
    (hd : 0 < d) (h : VanishesTo q F d) : F ∈ q.asIdeal := by
  let A := Localization.AtPrime q.asIdeal
  change algebraMap Lower A F ∈ IsLocalRing.maximalIdeal A ^ d at h
  have hm : algebraMap Lower A F ∈ IsLocalRing.maximalIdeal A := by
    simpa using Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal A) hd h
  change F ∈ (IsLocalRing.maximalIdeal A).under Lower at hm
  rwa [IsLocalization.AtPrime.under_maximalIdeal A q.asIdeal] at hm
theorem point_order {F : Row 3} {S : Geom[X]} {d : ℕ} (hF : OrderAt F S d) :
    VanishesTo (pointPrime (lowerPoint S)) (genericRow F) d := by
  let y := lowerPoint S
  let q := pointPrime y
  let A := Localization.AtPrime q.asIdeal
  let ev : Row 3 →+* Lower := MvPolynomial.eval₂Hom (MvPolynomial.C.comp genericCoeff)
    (fun i => MvPolynomial.X i - MvPolynomial.C (y i))
  have hev : ev.comp (shiftHom S) = genericHom := by
    apply MvPolynomial.ringHom_ext <;> intro i <;>
      simp [shiftHom, ev, genericHom, y, lowerPoint]
  have heval : ev (shiftHom S F) = genericRow F := DFunLike.congr_fun hev F
  have hmem (i : Fin 3) : ev (MvPolynomial.X i) ∈ q.asIdeal := by
    simp [q, pointPrime, pointIdeal, ev, RingHom.mem_ker]
  have hprod (a : Fin 3 →₀ ℕ) :
      (a.prod (fun i k => ev (MvPolynomial.X i) ^ k)) ∈ q.asIdeal ^ multiOrder a := by
    unfold multiOrder Finsupp.sum Finsupp.prod
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hmem i) (a i)
  have hrow : genericRow F ∈ q.asIdeal ^ d := by
    rw [← heval, MvPolynomial.as_sum (shiftHom S F), map_sum]
    apply Ideal.sum_mem
    intro a ha
    rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
    apply Ideal.mul_mem_left
    have hda : d ≤ multiOrder a := hF a ha
    apply Ideal.pow_le_pow_right (I := q.asIdeal) hda
    simpa only [map_pow, Finsupp.prod] using hprod a
  change algebraMap Lower A (genericRow F) ∈ IsLocalRing.maximalIdeal A ^ d
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal A, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hrow
end
end K1_13_7_4
end
section
namespace K1_13_7_4
noncomputable section
open Polynomial K1_13
open scoped BigOperators
def taylorHom {A : Type*} [CommSemiring A] :
    MvPolynomial (Fin 3) A →+* MvPolynomial (Fin 3) (MvPolynomial (Fin 3) A) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun i => MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i)
private theorem pow_taylor {A : Type*} [CommSemiring A] (i : Fin 3) (k : ℕ)
    (f : A) :
    (MvPolynomial.C f + MvPolynomial.X i) ^ k =
      ∑ j ∈ Finset.range (k + 1), MvPolynomial.monomial (Finsupp.single i j)
        (f ^ (k - j) * (k.choose j : A)) := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.X_pow_eq_monomial, ← map_pow, ← MvPolynomial.C_eq_coe_nat,
    mul_assoc, ← map_mul, mul_comm, MvPolynomial.C_mul_monomial, mul_one]
private theorem taylor_monomial_coeff {A : Type*} [CommSemiring A]
    (m a : Fin 3 →₀ ℕ) (c : A) :
    (taylorHom (MvPolynomial.monomial m c)).coeff a =
      MvPolynomial.monomial (m - a) (c * ∏ i : Fin 3, ((m i).choose (a i) : A)) := by
  classical
  unfold taylorHom
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_pow, RingHom.comp_apply,
    MvPolynomial.coeff_C_mul]
  simp_rw [pow_taylor]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_prod]
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  have hindex (b : Fin 3 → ℕ) :
      (∑ i : Fin 3, Finsupp.single i (b i)) =
        Finsupp.equivFunOnFinite.symm b := by
    simpa using (Finsupp.univ_sum_single (Finsupp.equivFunOnFinite.symm b))
  simp_rw [hindex]
  by_cases ha : ∀ i, a i ≤ m i
  · have hmem : (a : Fin 3 → ℕ) ∈ Fintype.piFinset (fun i => Finset.range (m i + 1)) :=
      Fintype.mem_piFinset.mpr fun i => Finset.mem_range_succ_iff.mpr (ha i)
    rw [Finset.sum_eq_single_of_mem (a : Fin 3 → ℕ) hmem]
    · have hea : Finsupp.equivFunOnFinite.symm (a : Fin 3 → ℕ) = a :=
        Finsupp.equivFunOnFinite.symm_apply_apply a
      simp only [hea, ↓reduceIte]
      rw [MvPolynomial.monomial_eq, Finsupp.prod_pow, map_mul, map_prod,
        Finset.prod_mul_distrib]
      simp only [Finsupp.tsub_apply, map_natCast]
      ac_rfl
    · intro b _ hb
      have hba : Finsupp.equivFunOnFinite.symm b ≠ a := by
        intro h
        exact hb (by simpa using congrArg (fun x : Fin 3 →₀ ℕ => (x : Fin 3 → ℕ)) h)
      simp [hba]
  · push Not at ha
    obtain ⟨i, hi⟩ := ha
    have hzero : (∏ k : Fin 3, ((m k).choose (a k) : A)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt hi])
    rw [hzero, mul_zero, map_zero]
    suffices (∑ b ∈ Fintype.piFinset (fun i => Finset.range (m i + 1)),
        if Finsupp.equivFunOnFinite.symm b = a then
          ∏ i : Fin 3, (MvPolynomial.X i : MvPolynomial (Fin 3) A) ^ (m i - b i) *
            ((m i).choose (b i) : MvPolynomial (Fin 3) A) else 0) = 0 by
      rw [this, mul_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hn : Finsupp.equivFunOnFinite.symm b ≠ a := by
      intro h
      have hbi := Fintype.mem_piFinset.mp hb i
      have he : b i = a i := by
        simpa using congrArg (fun x : Fin 3 →₀ ℕ => x i) h
      exact (not_lt_of_ge (Finset.mem_range_succ_iff.mp (he ▸ hbi))) hi
    simp [hn]
theorem taylor_coeff {A : Type*} [CommSemiring A] (F : MvPolynomial (Fin 3) A)
    (a : Fin 3 →₀ ℕ) : (taylorHom F).coeff a = hassePartial a F := by
  unfold hassePartial
  conv_lhs => rw [MvPolynomial.as_sum F, map_sum, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun m _ => taylor_monomial_coeff m a (F.coeff m)
private theorem shift_hasse (S : Geom[X]) (F : Row 3) (a : Fin 3 →₀ ℕ) :
    shiftHom S (hassePartial a F) = hassePartial a (shiftHom S F) := by
  have h : (MvPolynomial.map (shiftHom S)).comp taylorHom = taylorHom.comp (shiftHom S) := by
    apply MvPolynomial.ringHom_ext <;> intro x
    · simp [shiftHom, taylorHom]
    · simp only [RingHom.comp_apply, shiftHom, taylorHom, MvPolynomial.eval₂Hom_X',
        map_add, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C, MvPolynomial.map_X]
      ac_rfl
  have hc := congrArg (fun P : MvPolynomial (Fin 3) (Row 3) => P.coeff a)
    (RingHom.congr_fun h F)
  simpa only [RingHom.comp_apply, MvPolynomial.coeff_map, taylor_coeff] using hc
theorem hasse_order (F : Row 3) (S : Geom[X]) (a : Fin 3 →₀ ℕ) (d : ℕ)
    (hF : OrderAt F S d) : OrderAt (hassePartial a F) S (d - multiOrder a) := by
  classical
  intro m hm
  change m ∈ (shiftHom S (hassePartial a F)).support at hm
  rw [shift_hasse] at hm
  change d - multiOrder a ≤ multiOrder m
  by_contra! hd
  apply (MvPolynomial.mem_support_iff.mp hm)
  unfold hassePartial
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro v hv
  rw [MvPolynomial.coeff_monomial]
  split_ifs with he
  · by_cases ha : a ≤ v
    · have hvd : d ≤ multiOrder v := hF v hv
      have hsum : multiOrder v = multiOrder a + multiOrder m := by
        have hv : a + m = v := he ▸ add_tsub_cancel_of_le ha
        rw [← hv]
        simp [multiOrder, Finsupp.sum_fintype, Finsupp.add_apply, Finset.sum_add_distrib]
      omega
    · have ⟨i, hi⟩ : ∃ i, v i < a i := by simpa [Finsupp.le_def, not_forall] using ha
      have hz : (∏ i : Fin 3, ((v i).choose (a i) : Geom[X])) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt hi])
      rw [hz, mul_zero]
  · rfl
end
end K1_13_7_4
end
section
namespace K1_13_7_4
noncomputable section
open Polynomial K1_13 K1_13_7
open scoped BigOperators
def c1 : Prop :=
  ∀ (q : PrimeSpectrum Lower) (F : Row 3) (d : ℕ), q.asIdeal.height = 2 →
    (∀ a : Fin 3 →₀ ℕ, multiOrder a < d → genericRow (hassePartial a F) ∈ q.asIdeal) →
    VanishesTo q (genericRow F) d
def c2 : Prop :=
  ∀ (n : ℕ), n = 2 ∨ n = 3 →
    ∀ (q : PrimeSpectrum Lower) (F : Fin n → Lower) (a : Fin n → ℕ),
      q.asIdeal.height = n →
      q.asIdeal ∈ (Ideal.span (Set.range F)).minimalPrimes →
      (∀ i, 0 < a i) → (∀ i, VanishesTo q (F i) (a i)) →
      (↑(∏ i, a i) : ℕ∞) ≤ localColength q (Ideal.span (Set.range F))
private theorem hasse_caps (a : Fin 3 →₀ ℕ) {F : Row 3} {b j : ℕ}
    (hF : LowerCaps F b j) : LowerCaps (hassePartial a F) b j := by
  classical
  have hs {m : Fin 3 →₀ ℕ} (hm : m ∈ (hassePartial a F).support) :
      ∃ v ∈ F.support, m = v - a := by
    by_contra! h
    apply (MvPolynomial.mem_support_iff.mp hm)
    unfold hassePartial
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro v hv
    simp [MvPolynomial.coeff_monomial, Ne.symm (h v hv)]
  have hweight (w : Fin 3 → ℕ) {m : Fin 3 →₀ ℕ}
      (hm : m ∈ (hassePartial a F).support) :
      ∃ v ∈ F.support, m.sum (fun i k => w i * k) ≤ v.sum (fun i k => w i * k) := by
    obtain ⟨v, hv, rfl⟩ := hs hm
    refine ⟨v, hv, ?_⟩
    simp only [Finsupp.sum_fintype _ _ (fun _ => Nat.mul_zero _)]
    exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  constructor
  · apply Finset.sup_le
    intro m hm
    obtain ⟨v, hv, h⟩ := hweight (fun _ => 1) hm
    exact (by simpa only [one_mul, multiOrder] using h : multiOrder m ≤ multiOrder v).trans
      ((Finset.le_sup (f := multiOrder) hv).trans hF.1)
  · apply Finset.sup_le
    intro m hm
    obtain ⟨v, hv, h⟩ := hweight Fin.val hm
    exact h.trans ((Finset.le_sup (f := fun m => m.sum (fun i k => i.val * k)) hv).trans hF.2)
end
end K1_13_7_4
end
section
namespace K1_13_7_4_1
open K1_13 K1_13_7 K1_13_7_4
open scoped BigOperators
private theorem eval_taylor_eq_zero {R B : Type*} [CommSemiring R] [CommRing B]
    (f g : MvPolynomial (Fin 3) R →+* B)
    (hC : ∀ r, f (MvPolynomial.C r) = g (MvPolynomial.C r))
    (I : Ideal B) (d : ℕ) (hI : I ^ d = ⊥)
    (hX : ∀ i, f (MvPolynomial.X i) - g (MvPolynomial.X i) ∈ I)
    (F : MvPolynomial (Fin 3) R)
    (hF : ∀ a, multiOrder a < d → g (hassePartial a F) = 0) :
    f F = 0 := by
  let u (i : Fin 3) := f (MvPolynomial.X i) - g (MvPolynomial.X i)
  let eval := MvPolynomial.eval₂Hom g u
  have he : eval.comp taylorHom = f := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, eval, taylorHom, MvPolynomial.eval₂Hom_C]
        using (hC r).symm
    · intro i
      simp only [RingHom.comp_apply, eval, taylorHom, MvPolynomial.eval₂Hom_X',
        map_add, MvPolynomial.eval₂Hom_C, u]
      abel
  rw [← RingHom.congr_fun he F, RingHom.comp_apply]
  conv_lhs => rw [MvPolynomial.as_sum (taylorHom F), map_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [show eval = MvPolynomial.eval₂Hom g u from rfl, MvPolynomial.eval₂Hom_monomial,
    taylor_coeff]
  by_cases ha : multiOrder a < d
  · rw [hF a ha, zero_mul]
  · have hm : (a.prod fun i k => u i ^ k) ∈ I ^ multiOrder a := by
      unfold Finsupp.prod multiOrder Finsupp.sum
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hX i) (a i)
    have hz : (a.prod fun i k => u i ^ k) = 0 :=
      Ideal.mem_bot.mp (hI ▸ Ideal.pow_le_pow_right (Nat.le_of_not_gt ha) hm)
    rw [hz, mul_zero]
private theorem factor_ker_pow {A : Type*} [CommRing A] (m : Ideal A) (d : ℕ)
    (hle : m ^ d ≤ m) : (RingHom.ker (Ideal.Quotient.factor hle)) ^ d = ⊥ := by
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow (Ideal.Quotient.mk (m ^ d)) m d]
  exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker])
private theorem exists_residue_section {K A : Type*} [Field K] [PerfectField K]
    [CommRing A] [Algebra K A] [Algebra.EssFiniteType K A]
    (m : Ideal A) [m.IsMaximal] (d : ℕ) (hle : m ^ d ≤ m) :
    ∃ s : (A ⧸ m) →ₐ[K] (A ⧸ (m ^ d)),
      ∀ y, Ideal.Quotient.factorₐ K hle (s y) = y := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let π := Ideal.Quotient.factorₐ K hle
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective hle
  have hnil : IsNilpotent (RingHom.ker π.toRingHom) := ⟨d, factor_ker_pow m d hle⟩
  exact ⟨Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K _) π hπ hnil,
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id K _) π hπ hnil⟩
theorem proof : K1_13_7_4.c1 := by
  intro q F d _ hF
  let A := Localization.AtPrime q.asIdeal
  let m := IsLocalRing.maximalIdeal A
  change algebraMap Lower A (genericRow F) ∈ m ^ d
  by_cases hd : d = 0
  · simp [hd]
  let B := A ⧸ (m ^ d)
  let L := A ⧸ m
  let K := GeometricX
  let hle : m ^ d ≤ m := by
    simpa only [pow_one] using
      (Ideal.pow_le_pow_right (I := m) (Nat.one_le_iff_ne_zero.mpr hd))
  let π : B →ₐ[K] L := Ideal.Quotient.factorₐ K hle
  obtain ⟨s, hs⟩ := exists_residue_section (K := K) m d hle
  have hnil : (RingHom.ker π.toRingHom) ^ d = ⊥ := factor_ker_pow m d hle
  let e : Lower →ₐ[K] B :=
    (Ideal.Quotient.mkₐ K (m ^ d)).comp (IsScalarTower.toAlgHom K Lower A)
  let f := e.toRingHom.comp genericHom
  let g := (s.comp (π.comp e)).toRingHom.comp genericHom
  have hC (r : Polynomial Geom) : f (MvPolynomial.C r) = g (MvPolynomial.C r) := by
    simp only [f, g, RingHom.comp_apply, genericHom, MvPolynomial.map_C]
    exact (e.commutes (genericCoeff r)).trans ((s.comp (π.comp e)).commutes (genericCoeff r)).symm
  have hX (i : Fin 3) : f (MvPolynomial.X i) - g (MvPolynomial.X i) ∈ RingHom.ker π.toRingHom := by
    change π (f (MvPolynomial.X i) - g (MvPolynomial.X i)) = 0
    rw [map_sub]
    change π (f (MvPolynomial.X i)) - π (s (π (f (MvPolynomial.X i)))) = 0
    rw [hs, sub_self]
  have hlow (a : Fin 3 →₀ ℕ) (ha : multiOrder a < d) : g (hassePartial a F) = 0 := by
    have hm : algebraMap Lower A (genericRow (hassePartial a F)) ∈ m := by
      change genericRow (hassePartial a F) ∈ m.under Lower
      rw [IsLocalization.AtPrime.under_maximalIdeal A q.asIdeal]
      exact hF a ha
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    change s (Ideal.Quotient.mk m (algebraMap Lower A (genericRow (hassePartial a F)))) = 0
    rw [hz, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp (eval_taylor_eq_zero f g hC _ d hnil hX F hlow)
end K1_13_7_4_1
end
section
set_option autoImplicit false
namespace K1_13_7_6_2_2
noncomputable section
open K1_13_7 LinearMap
abbrev At (q : PrimeSpectrum Lower) := Localization.AtPrime q.asIdeal
abbrev Loc (q : PrimeSpectrum Lower) (M : Type*) [AddCommGroup M]
    [Module Lower M] := LocalizedModule q.asIdeal.primeCompl M
def locLength (q : PrimeSpectrum Lower) (M : Type*) [AddCommGroup M]
    [Module Lower M] : ℕ∞ := Module.length (At q) (Loc q M)
def locQuotient (q : PrimeSpectrum Lower) (I : Ideal Lower) :
    Loc q (Lower ⧸ I) ≃ₗ[At q] (At q ⧸ I.map (algebraMap Lower (At q))) := by
  let S := q.asIdeal.primeCompl
  let f := Algebra.linearMap Lower (At q)
  have hI : Submodule.localized' (At q) S f I = I.map (algebraMap Lower (At q)) := by
    rw [Submodule.localized'_eq_span, Ideal.map, Ideal.span, Algebra.coe_linearMap]
  let e := IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (Lower ⧸ I))
    (Submodule.toLocalizedQuotient' (At q) S f I)
  exact (e.extendScalarsOfIsLocalization S (At q)).trans (Submodule.quotEquivOfEq _ _ hI)
theorem locLength_quotient (q : PrimeSpectrum Lower) (I : Ideal Lower) :
    locLength q (Lower ⧸ I) = localColength q I :=
  (locQuotient q I).length_eq
theorem length_coker_quotient {A : Type*} [CommRing A] (I : Ideal A) (t : A) :
    Module.length A ((A ⧸ I) ⧸ range (lsmul A (A ⧸ I) t)) =
      Module.length A (A ⧸ I ⊔ Ideal.span {t}) := by
  let H := (Ideal.span {t}).map (Ideal.Quotient.mkₐ A I)
  have heq : range (lsmul A (A ⧸ I) t) = H.restrictScalars A := by
    ext x
    change (∃ y : A ⧸ I, t • y = x) ↔ x ∈ H
    simp only [H, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    simp [Algebra.smul_def, mul_comm]
  rw [heq]
  exact ((Submodule.Quotient.restrictScalarsEquiv A H).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ A I (Ideal.span {t})).toLinearEquiv).length_eq
theorem length_coker_local (q : PrimeSpectrum Lower) (I : Ideal Lower) (t : Lower) :
    Module.length (At q)
      ((At q ⧸ I.map (algebraMap Lower (At q))) ⧸
        range (lsmul (At q) (At q ⧸ I.map (algebraMap Lower (At q)))
          (algebraMap Lower (At q) t))) = localColength q (I ⊔ Ideal.span {t}) := by
  rw [length_coker_quotient]
  change _ = Module.length (At q) (At q ⧸ (I ⊔ Ideal.span {t}).map (algebraMap Lower (At q)))
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
theorem cut_regular (q : PrimeSpectrum Lower) (I : Ideal Lower) (t : Lower)
    (h : IsSMulRegular (At q ⧸ I.map (algebraMap Lower (At q))) (algebraMap Lower (At q) t))
    (hfin : localColength q (I ⊔ Ideal.span {t}) < ⊤) :
    CutFinite (algebraMap Lower (At q) t) (Loc q (Lower ⧸ I)) ∧
      cutEuler (algebraMap Lower (At q) t) (Loc q (Lower ⧸ I)) =
        ((localColength q (I ⊔ Ideal.span {t})).toNat : ℤ) := by
  have hc := cut_congr (algebraMap Lower (At q) t) (locQuotient q I)
  rw [hc.1, hc.2]
  have hk := (isSMulRegular_iff_ker_lsmul_eq_bot
    (At q ⧸ I.map (algebraMap Lower (At q))) (algebraMap Lower (At q) t)).mp h
  unfold CutFinite cutEuler
  rw [hk, Module.length_bot, length_coker_local]
  exact ⟨⟨by simp, hfin⟩, by simp⟩
theorem locLength_prime_away {p q : PrimeSpectrum Lower} (h : ¬ p.asIdeal ≤ q.asIdeal) :
    locLength q (Lower ⧸ p.asIdeal) = 0 := by
  rw [locLength_quotient]
  have htop : p.asIdeal.map (algebraMap Lower (At q)) = ⊤ := by
    by_contra hne
    apply h
    intro x hx
    by_contra hn
    exact Set.disjoint_left.mp
      ((IsLocalization.map_algebraMap_ne_top_iff_disjoint q.asIdeal.primeCompl (At q) _).mp hne)
      (show x ∈ q.asIdeal.primeCompl from hn) hx
  simp [localColength, htop, Module.length_eq_zero]
theorem locLength_prime_self (q : PrimeSpectrum Lower) :
    locLength q (Lower ⧸ q.asIdeal) = 1 := by
  rw [locLength_quotient]
  change Module.length (At q) (At q ⧸ q.asIdeal.map (algebraMap Lower (At q))) = 1
  rw [IsLocalization.AtPrime.map_eq_maximalIdeal, Module.length_eq_one_iff]
  exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal _).1
end
end K1_13_7_6_2_2
end
section
namespace K1_13_7_4_2
open K1_13_7 K1_13_7_4
open scoped BigOperators
def c1 : Prop :=
  ∀ (n : ℕ), n = 2 ∨ n = 3 →
    ∀ (q : PrimeSpectrum Lower), q.asIdeal.height = n →
      ∀ (f : Fin n → Local q),
        (Ideal.span (Set.range f)).radical = IsLocalRing.maximalIdeal (Local q) →
        ∀ (i : Fin n) (y : Local q), f i * y ∈ remainingIdeal f i → y ∈ remainingIdeal f i
def c2 : Prop :=
  ∀ (n : ℕ), n = 2 ∨ n = 3 →
    ∀ (q : PrimeSpectrum Lower), q.asIdeal.height = n →
      ∀ (t : ℕ), 0 < t →
        ((t + n - 1).choose n : ℕ∞) ≤
          Module.length (Local q) (Local q ⧸ IsLocalRing.maximalIdeal (Local q) ^ t)
theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_4.c2 := by
  classical
  intro n hn q F a hheight hmin ha hv
  let R := Local q
  let m := IsLocalRing.maximalIdeal R
  let f : Fin n → R := fun i => algebraMap Lower R (F i)
  let I := Ideal.span (Set.range f)
  have hmap : (Ideal.span (Set.range F)).map (algebraMap Lower R) = I := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hrad : I.radical = m := by
    rw [← hmap, IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes R q.asIdeal _ hmin]
    exact Localization.AtPrime.map_eq_maximalIdeal
  have hcancel (e : Fin n → ℕ) (he : ∀ j, 0 < e j) (i : Fin n) (y : R)
      (hy : f i * y ∈ remainingIdeal (fun j => f j ^ e j) i) :
      y ∈ remainingIdeal (fun j => f j ^ e j) i := by
    let d (j : Fin n) : ℕ := if j = i then 1 else e j
    let g (j : Fin n) : R := f j ^ d j
    have hd (j : Fin n) : 0 < d j := by
      by_cases hj : j = i <;> simp [d, hj, he j]
    have hg : (Ideal.span (Set.range g)).radical = m :=
      (radical_span_powers f d hd).trans hrad
    have hgi : g i = f i := by simp [g, d]
    have hremain : remainingIdeal g i = remainingIdeal (fun j => f j ^ e j) i := by
      unfold remainingIdeal
      congr 1
      exact Set.image_congr fun j hj => by
        have hji : j ≠ i := hj
        simp [g, d, hji]
    rw [← hremain] at hy ⊢
    exact h1 n hn q hheight g hg i y (by simpa only [hgi] using hy)
  let M := ∏ i, a i
  let b (i : Fin n) := ∏ j ∈ Finset.univ.erase i, a j
  have hb (i : Fin n) : 0 < b i := Finset.prod_pos fun j _ => ha j
  have hab (i : Fin n) : b i * a i = M :=
    Finset.prod_erase_mul Finset.univ a (Finset.mem_univ i)
  let g (i : Fin n) := f i ^ b i
  have hcontain : Ideal.span (Set.range g) ≤ m ^ M := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have horder : f i ∈ m ^ a i := hv i
    change f i ^ b i ∈ m ^ M
    simpa only [← pow_mul, mul_comm (a i) (b i), hab i] using
      Ideal.pow_mem_pow horder (b i)
  have hlength := colength_ge_of_growth hn m g hcontain (h2 n hn q hheight)
  have hscale := power_colength f b hb hcancel
  change (↑(M ^ n) : ℕ∞) ≤ colength (Ideal.span (Set.range g)) at hlength
  rw [hscale] at hlength
  have hprod : (∏ i, b i) * M = M ^ n := by
    change (∏ i, b i) * (∏ i, a i) = M ^ n
    rw [← Finset.prod_mul_distrib]
    simp only [hab, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hbprod : 0 < ∏ i, b i := Finset.prod_pos fun i _ => hb i
  have hb0 : (↑(∏ i, b i) : ℕ∞) ≠ 0 := by exact_mod_cast hbprod.ne'
  rw [← hprod, ENat.natCast_mul] at hlength
  have hbound := (ENat.mul_le_mul_left_iff hb0 (ENat.natCast_ne_top _)).mp hlength
  change (M : ℕ∞) ≤ colength ((Ideal.span (Set.range F)).map (algebraMap Lower R))
  rw [hmap]
  exact hbound
end K1_13_7_4_2
end
section
namespace K1_13_7_4_2_2
open K1_13_7 K1_13_7_4_2 IsLocalRing
private theorem length_le_of_ring_surjection {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    Module.length B B ≤ Module.length A A := by
  let : Algebra A B := f.toAlgebra
  rw [← Module.length_eq_of_surjective (M := B) hf]
  exact Module.length_le_of_surjective (Algebra.linearMap A B) hf
theorem proof : K1_13_7_4_2.c2 := by
  intro n hn q hq t ht
  let R := Local q
  let K := ResidueField R
  let m := maximalIdeal R
  have hd : Module.finrank K (CotangentSpace R) = n := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal R, hq] at h
    exact_mod_cast h
  by_cases h : 2 ≤ t
  · let : Algebra.FormallySmooth Lower R :=
      Algebra.FormallySmooth.of_isLocalization q.asIdeal.primeCompl
    let : Algebra.FormallySmooth GeometricX R :=
      Algebra.FormallySmooth.comp GeometricX Lower R
    let : Algebra.EssFiniteType Lower R :=
      Algebra.EssFiniteType.of_isLocalization R q.asIdeal.primeCompl
    let : Algebra.EssFiniteType GeometricX R :=
      Algebra.EssFiniteType.comp GeometricX Lower R
    let : Algebra.EssFiniteType GeometricX K :=
      Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom GeometricX R K)
        (residue_surjective (R := R))
    obtain ⟨f, hf⟩ := exists_jet_surjection (k := GeometricX) h
      (Module.finBasisOfFinrankEq K (CotangentSpace R) hd)
    change _ ≤ Module.length R (R ⧸ m ^ t)
    rw [Module.length_eq_of_surjective (R := R ⧸ m ^ t) Ideal.Quotient.mk_surjective]
    exact (length_jets K n t ht).trans (length_le_of_ring_surjection f hf)
  · have ht' : t = 1 := by omega
    subst t
    rw [pow_one, show 1 + n - 1 = n by omega, Nat.choose_self, Nat.cast_one]
    change (1 : ℕ∞) ≤ Module.length R K
    rw [Module.length_eq_of_surjective (residue_surjective (R := R)), Module.length_eq_one]
end K1_13_7_4_2_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_3_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_3
open scoped Polynomial
private theorem degree_tower {F A B : Type} [Field F] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] [IsDomain A] [Nontrivial B]
    [Module.Finite F A] [Module.Finite F B] (f : A →ₐ[F] B) :
    ∃ g : ℕ, 0 < g ∧ Module.finrank F B = Module.finrank F A * g := by
  let : Field A := fieldOfFiniteDimensional F A
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  let : Module.Finite A B := Module.Finite.of_restrictScalars_finite F A B
  exact ⟨Module.finrank A B, Module.finrank_pos, (Module.finrank_mul_finrank F A B).symm⟩
theorem assemble
    (seedTower : ∀ I : Ideal Ambient, I.IsPrime → Nontrivial (JetSeedSection I) →
      IsDomain (JetSeedSection I) ∧
      ∃ (f : PlaneSeedSection (seedImage I) →ₐ[SeedField] RootSeedSection (rootImage I))
        (j : RootSeedSection (rootImage I) →ₐ[SeedField] JetSeedSection I),
        Function.Injective f ∧ Function.Injective j)
    (planeDegree : ∀ Q : Seeds, Q ≠ 0 →
      Module.finrank SeedField (PlaneSeedSection (Ideal.span {Q})) = Q.totalDegree)
    (yInclusion : ∀ I : Ideal Ambient,
      ∃ j : RootYSection (rootImage I) →ₐ[SeedField] JetYSection I, Function.Injective j) :
    K1_14_2_3.c2 := by
  intro I C hI hY hC hImg
  obtain ⟨hPrime, _, hFinite, hPositive⟩ := hI
  let := hPrime
  let := hFinite
  let := hY
  have : Nontrivial (JetSeedSection I) := (Module.finrank_pos_iff_of_free _ _).mp hPositive
  obtain ⟨hDomain, f, j, hf, hj⟩ := seedTower I hPrime inferInstance
  have := hDomain
  have : IsDomain (RootSeedSection (rootImage I)) := hj.isDomain j
  have : IsDomain (PlaneSeedSection (seedImage I)) := hf.isDomain f
  have : Module.Finite SeedField (RootSeedSection (rootImage I)) :=
    Module.Finite.of_injective j.toLinearMap hj
  have : Module.Finite SeedField (PlaneSeedSection (seedImage I)) :=
    Module.Finite.of_injective f.toLinearMap hf
  have hQ : MvPolynomial.map constantCoefficients C ≠ 0 := by
    have hinj : Function.Injective constantCoefficients :=
      (IsFractionRing.injective L[X] FX).comp Polynomial.C_injective
    exact fun h => hC.ne_zero ((MvPolynomial.map_injective constantCoefficients hinj) (h.trans (map_zero _).symm))
  have hD : Module.finrank SeedField (PlaneSeedSection (seedImage I)) = C.totalDegree := by
    rw [hImg, planeDegree _ hQ, constant_map_degree]
  obtain ⟨g, hg, hmul⟩ := degree_tower f
  rw [hD] at hmul
  obtain ⟨y, hy⟩ := yInclusion I
  have hrY : Module.Finite SeedField (RootYSection (rootImage I)) :=
    Module.Finite.of_injective y.toLinearMap hy
  refine ⟨g, hg, ⟨Ideal.IsPrime.comap rootIncl, C, hC, hImg, inferInstance, hmul, hrY, ?_⟩, ?_⟩
  · exact LinearMap.finrank_le_finrank_of_injective (f := y.toLinearMap) hy
  · rw [← hmul]
    exact LinearMap.finrank_le_finrank_of_injective (f := j.toLinearMap) hj
end
end K1_14_2_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_8
noncomputable section
open Polynomial K1 FrobeniusLocator ProximityPrize.Benchmark
def seedInclusion : K[X] →+* Frac := algebraMap K[X] Frac
theorem seedInclusion_injective : Function.Injective seedInclusion :=
  IsFractionRing.injective K[X] Frac
theorem extendSeed_injective : Function.Injective extendSeed :=
  Polynomial.map_injective seedInclusion seedInclusion_injective
theorem eval_liftX (f : K[X]) (x : K) : (liftX f).eval (C x) = C (f.eval x) := by
  simp [liftX, eval_map]
theorem lift_locator_dvd (S : Finset I) (P : Bivar)
    (hz : ∀ i ∈ S, P.eval (C (node i)) = 0) : liftX (locator node S) ∣ P := by
  classical
  apply (Polynomial.map_dvd_map seedInclusion seedInclusion_injective
    ((locator_monic node S).map Polynomial.C)).mp
  rw [Polynomial.map_map, locator_map]
  apply Strata.locator_dvd_of_eval_zero _
    ((seedInclusion_injective.comp Polynomial.C_injective).comp IRSProfile.domain.injective)
  intro i hi
  change (P.map seedInclusion).eval (seedInclusion (C (node i))) = 0
  rw [Polynomial.eval_map_apply, hz i hi, map_zero]
theorem coprime_after_factor (G A B : Frac[X])
    (hg : G ≠ 0) (ha : A ≠ 0) (hmax : ∀ D, D ∣ G * A → D ∣ G * B → D ∣ G) :
    IsCoprime A B := by
  classical
  apply EuclideanDomain.isCoprime_of_dvd (fun h => ha h.1)
  intro d hnonunit _ hda hdb
  obtain ⟨q, hq⟩ := hmax (G * d) (mul_dvd_mul_left G hda) (mul_dvd_mul_left G hdb)
  have heq : 1 = d * q := mul_left_cancel₀ hg (by
    calc
      G * 1 = G := mul_one _
      _ = (G * d) * q := hq
      _ = G * (d * q) := mul_assoc _ _ _)
  exact hnonunit (isUnit_iff_dvd_one.mpr ⟨q, heq⟩)
private theorem certificate_output_zero {F ι : Type} [Field F] {q k H : ℕ} {x a b : ι → F}
    (R : Strata.PolynomialRelationCertificate q x a b k H) (i : ι)
    (hU : (Principal.assemble (fun j => R.coefficients (0, j))).eval (C (x i)) = 0)
    (hV : (Principal.assemble (fun j => R.coefficients (1, j))).eval (C (x i)) = 0) :
    R.output.eval (C (x i)) = 0 := by
  simpa only [hU, hV, zero_mul, zero_add] using (R.nodes i).symm
end
end K1_8
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_8
noncomputable section
open Polynomial K1 FrobeniusLocator
private def fieldPower {F : Type*} [Field F] (x : F) (n : ℕ) : F := x ^ n
private theorem fieldPower_zero {F : Type*} [Field F] (x : F) :
    fieldPower x 0 = 1 := pow_zero x
private theorem fieldPower_succ {F : Type*} [Field F] (x : F) (n : ℕ) :
    fieldPower x (n + 1) = fieldPower x n * x := pow_succ x n
private theorem native_field_power (x : K) (n : ℕ) : fieldPower x n = x ^ n := by
  rw [CompPoly.Extension.Ext.pow_def]
  induction n with
  | zero => rw [fieldPower_zero, npowBinRec_zero]
  | succ n ih => rw [fieldPower_succ, npowBinRec_succ, ih]
private theorem native_nodes {q k H : ℕ} {x a b : I → K}
    (R : Strata.PolynomialRelationCertificate q x a b k H) (i : I) :
    (Principal.assemble (fun j => R.coefficients (0, j))).eval (C (x i)) *
        (C (a i) + Polynomial.X (R := K) * C (b i)) +
      (Principal.assemble (fun j => R.coefficients (1, j))).eval (C (x i)) *
        (C (a i ^ q) + Polynomial.X (R := K) ^ q * C (b i ^ q)) =
      R.output.eval (C (x i)) := by
  rw [← native_field_power (a i) q, ← native_field_power (b i) q]
  unfold fieldPower
  exact R.nodes i
private theorem cancel_and_scale {A : Type*} [CommRing A] [IsDomain A]
    {g U V W a b e : A} (hg : g ≠ 0)
    (h : (g * U) * a + (g * V) * b = g * W) : (e * U) * a + (e * V) * b = e * W := by
  have h₀ : U * a + V * b = W :=
    mul_left_cancel₀ hg (by simpa only [mul_add, mul_assoc] using h)
  simpa only [mul_add, mul_assoc] using congrArg (fun t => e * t) h₀
private theorem transfer_at {u : Words} {q k H : ℕ}
    (R : Strata.PolynomialRelationCertificate q node (u 0) (u 1) k H)
    (S : Finset I) (G U V W : Bivar)
    (hG : ∀ i ∉ S, G.eval (C (node i)) ≠ 0)
    (hU : Principal.assemble (fun j => R.coefficients (0, j)) = G * U)
    (hV : Principal.assemble (fun j => R.coefficients (1, j)) = G * V)
    (hW : R.output = G * W) (e : K[X]) :
    relationOnAt q u S (C e * U) (C e * V) (C e * W) := by
  intro i hi
  have hn := @native_nodes q k H node (u 0) (u 1) R i
  simp only [hU, hV, hW, eval_mul] at hn
  simpa only [eval_mul, eval_C] using
    (cancel_and_scale (e := e) (hG i hi) hn)
end
end K1_8
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 850000
namespace K1_8
noncomputable section
open Polynomial K1 FrobeniusLocator
def extendSeedHom : Bivar →+* Frac[X] := Polynomial.mapRingHom seedInclusion
private theorem liftX_degree (P : K[X]) : (liftX P).natDegree = P.natDegree :=
  natDegree_map_eq_of_injective Polynomial.C_injective P
private theorem seed_pow_height (n : ℕ) : (seed ^ n).natDegree = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact natDegree_pow_le.trans (by simp [seed])
private theorem two_term_height (P Q : K[X]) (n : ℕ) :
    (liftX P + seed ^ n * liftX Q).natDegree ≤ amplitudeDegree P Q := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · rw [liftX_degree]
    exact le_max_left _ _
  · apply natDegree_mul_le.trans
    rw [seed_pow_height, zero_add, liftX_degree]
    exact le_max_right _ _
private theorem threeU_height_at (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) :
    (threeUAt q a β).natDegree ≤ a.natDegree + amplitudeDegree (β 0) (β 1) := by
  unfold threeUAt
  apply natDegree_mul_le.trans
  rw [liftX_degree]
  apply Nat.add_le_add_left
  exact (two_term_height _ _ q).trans
    (max_le_max natDegree_map_le natDegree_map_le)
private theorem threeUAt_native : threeUAt p = (threeU : K[X] → (Fin 2 → K[X]) → Bivar) := by
  unfold threeUAt threeU
  rfl
private theorem threeU_height (a : K[X]) (β : Fin 2 → K[X]) :
    (threeU a β).natDegree ≤ a.natDegree + amplitudeDegree (β 0) (β 1) := by
  rw [← threeUAt_native]
  exact threeU_height_at p a β
private theorem threeV_height (b : K[X]) (α : Fin 2 → K[X]) :
    (threeV b α).natDegree ≤ b.natDegree + amplitudeDegree (α 0) (α 1) := by
  unfold threeV
  rw [natDegree_neg]
  apply natDegree_mul_le.trans
  rw [liftX_degree]
  apply Nat.add_le_add_left
  simpa only [pow_one] using two_term_height (α 0) (α 1) 1
private theorem common_multiplier {L : Type*} [CommRing L] {A B P Q : L}
    (hcop : IsCoprime A B) (hcross : A * Q = B * P) :
    ∃ E, P = E * A ∧ Q = E * B := by
  obtain ⟨r, t, hbez⟩ := hcop
  refine ⟨r * P + t * Q, ?_, ?_⟩
  · calc
      P = (r * A + t * B) * P := by rw [hbez, one_mul]
      _ = r * (A * P) + t * (B * P) := by ring
      _ = r * (A * P) + t * (A * Q) := by rw [hcross]
      _ = (r * P + t * Q) * A := by ring
  · calc
      Q = (r * A + t * B) * Q := by rw [hbez, one_mul]
      _ = r * (A * Q) + t * (B * Q) := by ring
      _ = r * (B * P) + t * (B * Q) := by rw [hcross]
      _ = (r * P + t * Q) * B := by ring
private theorem multiplier_degree_zero {A B P Q E : Frac[X]} {H : ℕ}
    (ha : A ≠ 0) (hb : B ≠ 0) (hp : P = E * A) (hq : Q = E * B)
    (hmax : max A.natDegree B.natDegree = H)
    (hpd : P.natDegree ≤ H) (hqd : Q.natDegree ≤ H) : E.natDegree = 0 := by
  by_cases he : E = 0
  · simp [he]
  rw [hp, natDegree_mul he ha] at hpd
  rw [hq, natDegree_mul he hb] at hqd
  omega
private theorem seed_scalar_coeff {P Q : Bivar} {s : Frac} (j : ℕ)
    (h : extendSeedHom P = C s * extendSeedHom Q) :
    seedInclusion (P.coeff j) = s * seedInclusion (Q.coeff j) := by
  have hc := congrArg (fun F : Frac[X] => F.coeff j) h
  change (P.map seedInclusion).coeff j = (C s * Q.map seedInclusion).coeff j at hc
  simpa only [coeff_C_mul, coeff_map] using hc
private theorem descend_scalar {ι : Type*} [Fintype ι]
    (A B : ι → K[X]) (hprim : PrimitiveVector.IsPrimitive A) (s : Frac)
    (hB : ∀ i, seedInclusion (B i) = s * seedInclusion (A i)) :
    ∃ e : K[X], seedInclusion e = s := by
  obtain ⟨w, hw⟩ := (PrimitiveVector.primitive_iff_bezout A).mp hprim
  refine ⟨∑ i, w i * B i, ?_⟩
  calc
    seedInclusion (∑ i, w i * B i) =
        ∑ i, seedInclusion (w i) * (s * seedInclusion (A i)) := by
      simp only [map_sum, map_mul, hB]
    _ = s * ∑ i, seedInclusion (w i) * seedInclusion (A i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = s * seedInclusion (∑ i, w i * A i) := by simp only [map_sum, map_mul]
    _ = s := by rw [hw, map_one, mul_one]
private theorem proportional_amplitudes {α β : Fin 2 → K[X]}
    (ha : IsCoprime (α 0) (α 1)) (hb : IsCoprime (β 0) (β 1))
    (hd : α 0 * β 1 = α 1 * β 0) :
    ∃ t : K, t ≠ 0 ∧ ∀ i, β i = C t * α i := by
  obtain ⟨c, h0, h1⟩ := common_multiplier (A := α 0) (B := α 1) ha hd
  obtain ⟨r, s, h⟩ := hb
  have hunit : IsUnit c := isUnit_iff_dvd_one.mpr ⟨r * α 0 + s * α 1, by
    calc
      1 = r * β 0 + s * β 1 := h.symm
      _ = c * (r * α 0 + s * α 1) := by rw [h0, h1]; ring⟩
  have hc : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hunit)
  refine ⟨c.coeff 0, ?_, ?_⟩
  · intro hz
    apply hunit.ne_zero
    rw [hc, hz, C_0]
  · intro i
    fin_cases i
    · change β 0 = C (c.coeff 0) * α 0
      exact h0.trans (congrArg (fun z => z * α 0) hc)
    · change β 1 = C (c.coeff 0) * α 1
      exact h1.trans (congrArg (fun z => z * α 1) hc)
private theorem rescale_at (q : ℕ) (a : K[X]) (α β : Fin 2 → K[X]) (t : K)
    (heq : ∀ i, (β i).map twist = C t * (α i).map twist) :
    threeUAt q (a * C t) α = threeUAt q a β := by
  simp only [threeUAt, heq, liftX, Polynomial.map_mul, Polynomial.map_C]
  ring
private theorem rescale_threeU (a : K[X]) (α β : Fin 2 → K[X]) (t : K)
    (heq : ∀ i, (β i).map twist = C t * (α i).map twist) :
    threeU (a * C t) α = threeU a β := by
  rw [← threeUAt_native]
  exact rescale_at p a α β t heq
end
end K1_8
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace K1_8
noncomputable section
open Polynomial K1
private def fourColumns {F : Type*} [Field F] (A B : F[X]) (p : ℕ) : Fin 4 → F[X] :=
  ![A, (Polynomial.X (R := F)) * A, B, (Polynomial.X (R := F)) ^ p * B]
private theorem first_pair_independent {F : Type*} [Field F] (A : F[X]) (hA : A ≠ 0) :
    LinearIndependent F ![A, (Polynomial.X (R := F)) * A] := by
  apply linearIndependent_fin2.mpr
  refine ⟨mul_ne_zero X_ne_zero hA, ?_⟩
  intro c hc
  change c • ((Polynomial.X (R := F)) * A) = A at hc
  rw [smul_eq_C_mul, ← mul_assoc] at hc
  have h : C c * (Polynomial.X (R := F)) = 1 := mul_right_cancel₀ hA (hc.trans (one_mul _).symm)
  have hc₀ := congrArg (fun Q : F[X] => Q.coeff 0) h
  simp only [coeff_C_mul, coeff_X_zero, mul_zero, coeff_one_zero, zero_ne_one] at hc₀
private theorem span_degree_interval {F : Type*} [Field F] {A W : F[X]}
    (hA : A ≠ 0) (hW : W ≠ 0) (hm : W ∈ Submodule.span F (Set.range ![A, (Polynomial.X (R := F)) * A])) :
    A.natDegree ≤ W.natDegree ∧ W.natDegree ≤ A.natDegree + 1 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hm
  have h : C (c 0) * A + C (c 1) * ((Polynomial.X (R := F)) * A) = W := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_C_mul] using hc
  let P := C (c 0) + C (c 1) * (Polynomial.X (R := F))
  have hW' : W = P * A := by rw [← h]; dsimp [P]; ring
  have hP : P ≠ 0 := fun hz => hW (by rw [hW', hz, zero_mul])
  have hPd : P.natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    exact max_le (by simp) (natDegree_mul_le.trans (by simp))
  have he := congrArg Polynomial.natDegree hW'
  rw [natDegree_mul hP hA] at he
  omega
private theorem lower_of_extra_column {F : Type*} [Field F] (A B : F[X]) (p : ℕ)
    (hA : A ≠ 0) (j : Fin 4)
    (hj : fourColumns A B p j ∉ Submodule.span F (Set.range ![A, (Polynomial.X (R := F)) * A])) :
    3 ≤ Module.finrank F (Submodule.span F (Set.range (fourColumns A B p))) := by
  let f : Fin 3 → F[X] := Fin.snoc ![A, (Polynomial.X (R := F)) * A] (fourColumns A B p j)
  have hf : LinearIndependent F f := linearIndependent_finSnoc.mpr ⟨first_pair_independent A hA, hj⟩
  have hs : Set.range f ⊆ Set.range (fourColumns A B p) := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨j, rfl⟩
  have := Module.Finite.span_of_finite F (Set.finite_range (fourColumns A B p))
  have hd := Submodule.finrank_mono (R := F) (Submodule.span_mono hs)
  simpa only [finrank_span_eq_card hf, Fintype.card_fin] using hd
private theorem three_or_four_of_columns {F : Type*} [Field F] (A B : F[X]) (p : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hp : 1 < p) :
    Module.finrank F (Submodule.span F (Set.range (fourColumns A B p))) = 4 ∨
      Module.finrank F (Submodule.span F (Set.range (fourColumns A B p))) = 3 := by
  have hle : Module.finrank F (Submodule.span F (Set.range (fourColumns A B p))) ≤ 4 := by
    simpa only [Set.finrank, Fintype.card_fin] using finrank_range_le_card (R := F) (fourColumns A B p)
  have hge : 3 ≤ Module.finrank F (Submodule.span F (Set.range (fourColumns A B p))) := by
    by_cases hm : B ∈ Submodule.span F (Set.range ![A, (Polynomial.X (R := F)) * A])
    · apply lower_of_extra_column A B p hA 3
      change (Polynomial.X (R := F)) ^ p * B ∉ Submodule.span F (Set.range ![A, (Polynomial.X (R := F)) * A])
      intro hpow
      have hne : (Polynomial.X (R := F)) ^ p * B ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hB
      have hBdeg := (span_degree_interval hA hB hm).1
      have hpowdeg := (span_degree_interval hA hne hpow).2
      rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hB, (monic_X (R := F)).natDegree_pow,
        natDegree_X, Nat.mul_one] at hpowdeg
      omega
    · exact lower_of_extra_column A B p hA 2 hm
  omega
private theorem column_family (U V : Bivar) (q : ℕ) :
    (fun j : Fin 4 => extendSeed (Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V else seed ^ q * V))) =
    fourColumns (extendSeed (Bivariate.swap U)) (extendSeed (Bivariate.swap V)) q := by
  funext j
  fin_cases j <;> simp [fourColumns, seed, Bivariate.swap_X, extendSeed, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X]
private theorem rank_cases_at (q : ℕ) (hq : 1 < q)
    (U V : Bivar) (hu : U ≠ 0) (hv : V ≠ 0) :
    columnRankAt q U V = 4 ∨ columnRankAt q U V = 3 := by
  let A := extendSeed (Bivariate.swap U)
  let B := extendSeed (Bivariate.swap V)
  have hs (W : Bivar) (hn : W ≠ 0) : extendSeed (Bivariate.swap W) ≠ 0 := by
    intro h
    apply hn
    apply (Bivariate.swap (R := K)).injective
    apply extendSeed_injective
    simpa only [map_zero, extendSeed, Polynomial.map_zero] using h
  unfold columnRankAt
  rw [column_family]
  exact three_or_four_of_columns A B q (hs U hu) (hs V hv) hq
theorem rank_cases (U V : Bivar) (hu : U ≠ 0) (hv : V ≠ 0) :
    columnRank U V = 4 ∨ columnRank U V = 3 :=
  rank_cases_at p (by decide) U V hu hv
end
end K1_8
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace K1_8
noncomputable section
open Polynomial K1
def c1 : Prop :=
  ∀ U V : Bivar, U ≠ 0 → V ≠ 0 → columnRank U V = 3 →
    Nonempty (AmplitudeDirection U V)
def c2 : Prop :=
  ∀ (U V : Bivar) (H : ℕ), U ≠ 0 → V ≠ 0 →
    IsCoprime (extendSeed U) (extendSeed V) →
    max U.natDegree V.natDegree = H → H < p - 1 →
    ∀ S : AmplitudeDirection U V,
      S.a.natDegree + amplitudeDegree (S.β 0) (S.β 1) ≤ H ∧
      S.b.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ H
end
end K1_8
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace K1_8_2
open Polynomial K1
noncomputable section
private def shape {R : Type*} [CommSemiring R] (n : ℕ) (u v : R) : R[X] :=
  C u + Polynomial.X (R := R) ^ n * C v
private theorem shape_coeffs {R : Type*} [CommSemiring R] {n : ℕ} (hn : n ≠ 0) (u v : R) :
    (shape n u v).coeff 0 = u ∧ (shape n u v).coeff n = v := by
  constructor
  · simp [shape, mul_comm (Polynomial.X (R := R) ^ n) (C v), Ne.symm hn]
  · simp [shape, mul_comm (Polynomial.X (R := R) ^ n) (C v), coeff_C_of_ne_zero hn]
private theorem primitive_shape {F : Type*} [Field F] {n : ℕ} (hn : n ≠ 0)
    {u v : F[X]} (hcop : IsCoprime u v) : (shape n u v).IsPrimitive := by
  intro d hd
  obtain ⟨h0, hn'⟩ := shape_coeffs hn u v
  have h := (C_dvd_iff_dvd_coeff _ _).mp hd
  exact hcop.isUnit_of_dvd' (h0 ▸ h 0) (hn' ▸ h n)
private theorem scalar_relPrime {F : Type*} [Field F] {a : F[X]} {P : F[X][X]}
    (ha : a ≠ 0) (hP : P.IsPrimitive) : IsRelPrime (C a) P := by
  intro d hda hdP
  have hdeg : d.natDegree = 0 :=
    Nat.eq_zero_of_le_zero ((natDegree_le_of_dvd hda (C_ne_zero.mpr ha)).trans_eq (natDegree_C a))
  rw [eq_C_of_natDegree_eq_zero hdeg] at hdP ⊢
  exact (hP _ hdP).map C
private def xHeight {F : Type*} [Field F] (P : F[X][X]) : ℕ :=
  (Bivariate.swap P).natDegree
private theorem xHeight_C {F : Type*} [Field F] (a : F[X]) : xHeight (C a) = a.natDegree := by
  rw [xHeight, Bivariate.swap_C, natDegree_map_eq_of_injective C_injective]
private theorem xHeight_mul {F : Type*} [Field F] {P Q : F[X][X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0) : xHeight (P * Q) = xHeight P + xHeight Q := by
  unfold xHeight
  rw [map_mul]
  exact natDegree_mul (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hP)
    (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hQ)
private theorem xHeight_pow {F : Type*} [Field F] (P : F[X][X]) (n : ℕ) :
    xHeight (P ^ n) = n * xHeight P := by
  rw [xHeight, map_pow, natDegree_pow, xHeight]
private theorem xHeight_shape {F : Type*} [Field F] {n : ℕ} (hn : n ≠ 0) (u v : F[X]) :
    xHeight (shape n u v) = max u.natDegree v.natDegree := by
  have hc (i : ℕ) :
      (Bivariate.swap (shape n u v)).coeff i = shape n (u.coeff i) (v.coeff i) := by
    rw [shape, map_add, map_mul, map_pow, Bivariate.swap_C, Bivariate.swap_C, Bivariate.swap_Y,
      ← C_pow, coeff_add, coeff_C_mul, coeff_map, coeff_map, shape]
  unfold xHeight
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [hc, coeff_eq_zero_of_natDegree_lt ((le_max_left _ _).trans_lt hi),
      coeff_eq_zero_of_natDegree_lt ((le_max_right _ _).trans_lt hi)]
    simp [shape]
  · apply max_le
    · by_cases hu : u = 0
      · simp [hu]
      apply le_natDegree_of_ne_zero
      intro hz
      have h := congrArg (fun W : F[X] => W.coeff 0) ((hc u.natDegree).symm.trans hz)
      rw [(shape_coeffs hn _ _).1, coeff_zero] at h
      exact hu (leadingCoeff_eq_zero.mp h)
    · by_cases hv : v = 0
      · simp [hv]
      apply le_natDegree_of_ne_zero
      intro hz
      have h := congrArg (fun W : F[X] => W.coeff n) ((hc v.natDegree).symm.trans hz)
      rw [(shape_coeffs hn _ _).2, coeff_zero] at h
      exact hv (leadingCoeff_eq_zero.mp h)
private theorem cross_heights {F : Type*} [Field F] {U V P Q : F[X][X]}
    (hU : U ≠ 0) (hV : V ≠ 0) (hcop : IsRelPrime P Q) (hcross : U * Q = V * P) :
    xHeight P ≤ xHeight U ∧ xHeight Q ≤ xHeight V := by
  have hp : P ∣ U := hcop.dvd_of_dvd_mul_right (by rw [hcross]; exact dvd_mul_left _ _)
  have hq : Q ∣ V := hcop.symm.dvd_of_dvd_mul_right (by rw [← hcross]; exact dvd_mul_left _ _)
  exact ⟨natDegree_le_of_dvd (_root_.map_dvd Bivariate.swap hp)
      (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hU),
    natDegree_le_of_dvd (_root_.map_dvd Bivariate.swap hq)
      (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hV)⟩
private theorem affine_sparse {F : Type*} [Field F] (q : ℕ) [ExpChar F q] (hq : q ≠ 0)
    {u v r s : F[X]} (huv : IsCoprime u v) (hrs : IsCoprime r s) :
    IsRelPrime (shape 1 u v) (shape q r s) ∨
      ∃ t : F[X], IsUnit t ∧ shape q r s = C t * (shape 1 u v) ^ q := by
  by_cases hv : v = 0
  · left
    subst v
    have hu : IsUnit u := huv.isUnit_of_dvd (dvd_zero _)
    simpa [shape] using (hu.map (C : F[X] →+* F[X][X])).isRelPrime_left
  have hAffine : shape 1 u v = C v * Polynomial.X (R := F[X]) + C u := by
    rw [shape, pow_one, add_comm, mul_comm (Polynomial.X (R := F[X]))]
  have hirr : Irreducible (shape 1 u v) := by
    rw [hAffine]
    exact irreducible_C_mul_X_add_C hv huv.symm.isRelPrime
  rcases hirr.dvd_or_isRelPrime (n := shape q r s) with hdiv | hcop
  · right
    have hpow : (shape 1 u v) ^ q = shape q (u ^ q) (v ^ q) := by
      simp only [shape, pow_one, add_pow_expChar _ _ q, mul_pow, ← C_pow]
    have hdiff : C (v ^ q) * shape q r s - C s * (shape 1 u v) ^ q =
        C (v ^ q * r - s * u ^ q) := by
      rw [hpow]
      simp only [shape, map_mul, map_sub]
      ring
    have hc : shape 1 u v ∣ C (v ^ q * r - s * u ^ q) := by
      rw [← hdiff]
      exact dvd_sub (hdiv.mul_left _) ((dvd_pow_self _ hq).mul_left _)
    have hcross : v ^ q * r = s * u ^ q := by
      apply sub_eq_zero.mp
      by_contra hne
      have hd := natDegree_le_of_dvd hc (C_ne_zero.mpr hne)
      rw [hAffine, natDegree_linear hv, natDegree_C] at hd
      omega
    have hp : IsCoprime (u ^ q) (v ^ q) := huv.pow
    obtain ⟨e, f, hbez⟩ := hp
    let t := e * r + f * s
    have hr : r = t * u ^ q := by
      calc
        r = (e * u ^ q + f * v ^ q) * r := by rw [hbez, one_mul]
        _ = t * u ^ q := by
          dsimp [t]
          linear_combination f * hcross
    have hs : s = t * v ^ q := by
      calc
        s = (e * u ^ q + f * v ^ q) * s := by rw [hbez, one_mul]
        _ = t * v ^ q := by
          dsimp [t]
          linear_combination - e * hcross
    have ht : shape q r s = C t * (shape 1 u v) ^ q := by
      rw [hpow, hr, hs]
      simp only [shape, map_mul]
      ring
    exact ⟨t, primitive_shape hq hrs t (ht ▸ dvd_mul_right _ _), ht⟩
  · exact Or.inl hcop
private theorem height_bound {F : Type*} [Field F] (q : ℕ) [ExpChar F q] (hq : 1 < q)
    {U₀ V : F[X][X]} {H : ℕ} (hU₀ : U₀ ≠ 0) (hV : V ≠ 0)
    (hU₀H : xHeight U₀ ≤ H) (hVH : xHeight V ≤ H) (hsmall : H < q - 1)
    {a b u v r s : F[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime a b) (huv : IsCoprime u v) (hrs : IsCoprime r s)
    (hdir : U₀ * -(C b * shape 1 u v) = V * (C a * shape q r s)) :
    a.natDegree + max r.natDegree s.natDegree ≤ H ∧
      b.natDegree + max u.natDegree v.natDegree ≤ H := by
  have hq0 : q ≠ 0 := by omega
  let U := -U₀
  have hU : U ≠ 0 := neg_ne_zero.mpr hU₀
  have hUH : xHeight U ≤ H := by
    simpa only [U, xHeight, map_neg, natDegree_neg] using hU₀H
  have hcross : U * (C b * shape 1 u v) = V * (C a * shape q r s) := by
    exact (neg_mul_comm U₀ (C b * shape 1 u v)).trans hdir
  let A := shape 1 u v
  let B := shape q r s
  have hA : A.IsPrimitive := primitive_shape one_ne_zero huv
  have hB : B.IsPrimitive := primitive_shape hq0 hrs
  have hab' : IsRelPrime (C a) (C b) := (hab.map C).isRelPrime
  have hAd : xHeight A = max u.natDegree v.natDegree := xHeight_shape one_ne_zero _ _
  have hBd : xHeight B = max r.natDegree s.natDegree := xHeight_shape hq0 _ _
  rcases affine_sparse q hq0 huv hrs with hcop | ⟨t, ht, hpow⟩
  · have hcop' : IsRelPrime (C a * B) (C b * A) :=
      (hab'.mul_right (scalar_relPrime ha hA)).mul_left
        ((scalar_relPrime hb hB).symm.mul_right hcop.symm)
    obtain ⟨hP, hQ⟩ := cross_heights hU hV hcop' hcross
    rw [xHeight_mul (C_ne_zero.mpr ha) hB.ne_zero, xHeight_C, hBd] at hP
    rw [xHeight_mul (C_ne_zero.mpr hb) hA.ne_zero, xHeight_C, hAd] at hQ
    exact ⟨hP.trans hUH, hQ.trans hVH⟩
  · change B = C t * A ^ q at hpow
    let D := C a * C t * A ^ (q - 1)
    have hD : IsRelPrime D (C b) :=
      (hab'.mul_left ((ht.map C).isRelPrime_left)).mul_left
        (scalar_relPrime hb hA).symm.pow_left
    have hfactor : C a * B = D * A := by
      have hqpow : A ^ q = A ^ (q - 1) * A := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q)]
      simp only [D, hpow, hqpow, mul_assoc]
    have hnew : U * C b = V * D := by
      apply mul_right_cancel₀ hA.ne_zero
      calc
        (U * C b) * A = U * (C b * A) := mul_assoc _ _ _
        _ = V * (C a * B) := hcross
        _ = (V * D) * A := by rw [hfactor, mul_assoc V D A]
    obtain ⟨hDle, hble⟩ := cross_heights hU hV hD hnew
    have ht0 : t.natDegree = 0 := natDegree_eq_zero_of_isUnit ht
    have hDa : xHeight D = a.natDegree + (q - 1) * xHeight A := by
      dsimp [D]
      rw [xHeight_mul (mul_ne_zero (C_ne_zero.mpr ha) (C_ne_zero.mpr ht.ne_zero))
            (pow_ne_zero _ hA.ne_zero),
        xHeight_mul (C_ne_zero.mpr ha) (C_ne_zero.mpr ht.ne_zero), xHeight_C, xHeight_C,
        xHeight_pow, ht0, add_zero]
    have hzero : xHeight A = 0 := by
      by_contra hn
      have hle := (Nat.mul_le_mul_left (q - 1) (Nat.one_le_iff_ne_zero.mpr hn))
      rw [Nat.mul_one] at hle
      rw [hDa] at hDle
      omega
    have hBzero : xHeight B = 0 := by
      rw [hpow, xHeight_mul (C_ne_zero.mpr ht.ne_zero) (pow_ne_zero _ hA.ne_zero),
        xHeight_C, xHeight_pow, hzero, ht0, Nat.mul_zero, add_zero]
    rw [hDa, hzero, Nat.mul_zero, add_zero] at hDle
    rw [xHeight_C] at hble
    rw [← hBd, ← hAd, hBzero, hzero, add_zero, add_zero]
    exact ⟨hDle.trans hUH, hble.trans hVH⟩
private theorem swap_threeUAt (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) :
    Bivariate.swap (K1_8.threeUAt q a β) = C a * shape q ((β 0).map twist) ((β 1).map twist) := by
  simp only [K1_8.threeUAt, shape, liftX, seed, map_add, map_mul, map_pow, Bivariate.swap_map_C,
    Bivariate.swap_X]
private theorem threeU_native : K1_8.threeUAt p = threeU := by
  unfold K1_8.threeUAt threeU
  rfl
private theorem swap_threeV (b : K[X]) (α : Fin 2 → K[X]) :
    Bivariate.swap (threeV b α) = -(C b * shape 1 (α 0) (α 1)) := by
  simp only [threeV, shape, liftX, seed, map_add, map_mul, map_neg, Bivariate.swap_map_C,
    Bivariate.swap_X, pow_one]
private theorem native_height_at (q : ℕ) [ExpChar K q] (hq : 1 < q)
    (U V : Bivar) (H : ℕ) (hU : U ≠ 0) (hV : V ≠ 0)
    (hmax : max U.natDegree V.natDegree = H) (hsmall : H < q - 1)
    (a b : K[X]) (α β : Fin 2 → K[X]) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime a b) (hα : IsCoprime (α 0) (α 1)) (hβ : IsCoprime (β 0) (β 1))
    (hdir : sameDirection U V (K1_8.threeUAt q a β) (threeV b α)) :
    a.natDegree + amplitudeDegree (β 0) (β 1) ≤ H ∧
      b.natDegree + amplitudeDegree (α 0) (α 1) ≤ H := by
  have hUH : U.natDegree ≤ H := hmax ▸ le_max_left _ _
  have hVH : V.natDegree ≤ H := hmax ▸ le_max_right _ _
  have hcross : Bivariate.swap U * -(C b * shape 1 (α 0) (α 1)) =
      Bivariate.swap V * (C a * shape q ((β 0).map twist) ((β 1).map twist)) := by
    have h := congrArg (Bivariate.swap (R := K)) hdir
    change Bivariate.swap (U * threeV b α) = Bivariate.swap (V * K1_8.threeUAt q a β) at h
    rwa [map_mul, map_mul, swap_threeV, swap_threeUAt] at h
  have hxU : xHeight (Bivariate.swap U) = U.natDegree := by
    rw [xHeight, Bivariate.swap_swap_apply]
  have hxV : xHeight (Bivariate.swap V) = V.natDegree := by
    rw [xHeight, Bivariate.swap_swap_apply]
  have hβ' : IsCoprime ((β 0).map twist) ((β 1).map twist) :=
    hβ.map (Polynomial.mapRingHom twist)
  have h := height_bound (F := K) q hq
    (U₀ := Bivariate.swap U) (V := Bivariate.swap V) (H := H)
    (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hU)
    (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hV)
    (hxU ▸ hUH) (hxV ▸ hVH) hsmall
    (a := a) (b := b) (u := α 0) (v := α 1)
    (r := (β 0).map twist) (s := (β 1).map twist)
    ha hb hab hα hβ' hcross
  simpa only [amplitudeDegree, natDegree_map_eq_of_injective twist.injective] using h
theorem proof : K1_8.c2 := by
  intro U V H hU hV _ hmax hsmall S
  apply native_height_at p (by decide) U V H hU hV hmax hsmall S.a S.b S.α S.β
    S.a_ne S.b_ne S.scalar_coprime S.α_primitive S.β_primitive
  rw [threeU_native]
  exact S.direction
end
end K1_8_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace K1_8_1
noncomputable section
open Polynomial K1 K1_8 FrobeniusLocator
open scoped BigOperators
private def evaluationFraction : Bivar →+* Frac[X] :=
  extendSeedHom.comp (Bivariate.swap (R := K)).toRingEquiv.toRingHom
private theorem evaluationFraction_injective : Function.Injective evaluationFraction :=
  extendSeed_injective.comp (Bivariate.swap (R := K)).injective
private theorem evaluationFraction_lift (f : K[X]) :
    evaluationFraction (liftX f) = C (seedInclusion f) := by
  change (Bivariate.swap (f.map C)).map seedInclusion = _
  rw [Bivariate.swap_map_C, Polynomial.map_C]
private def columns (q : ℕ) (U V : Bivar) (i : Fin 4) : Bivar :=
  if i = 0 then U else if i = 1 then seed * U else if i = 2 then V else seed ^ q * V
private theorem polynomial_dependence {U V : Bivar} (hr : columnRank U V = 3) :
    ∃ f : Fin 4 → K[X], f ≠ 0 ∧ ∑ i, liftX (f i) * columns p U V i = 0 := by
  classical
  have hdep : ¬ LinearIndependent Frac (fun i => evaluationFraction (columns p U V i)) := by
    intro h
    have hdim : columnRank U V = 4 := by
      change Module.finrank Frac
        (Submodule.span Frac (Set.range fun i => evaluationFraction (columns p U V i))) = 4
      simpa only [Fintype.card_fin] using finrank_span_eq_card h
    omega
  obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors K[X]) c
  choose f hf using hd
  have hcoeff (i : Fin 4) : seedInclusion (f i) = seedInclusion (d : K[X]) * c i := by
    simpa only [Algebra.smul_def, seedInclusion] using hf i
  have hdn : seedInclusion (d : K[X]) ≠ 0 := by
    intro hz
    exact nonZeroDivisors.ne_zero d.property
      (seedInclusion_injective (hz.trans (map_zero seedInclusion).symm))
  refine ⟨f, ?_, ?_⟩
  · intro hzero
    have hj' := hcoeff j
    rw [hzero, Pi.zero_apply, map_zero] at hj'
    exact hj ((mul_eq_zero.mp hj'.symm).resolve_left hdn)
  · have hscaled :
        ∑ i, evaluationFraction (liftX (f i)) * evaluationFraction (columns p U V i) =
          C (seedInclusion (d : K[X])) * ∑ i, c i • evaluationFraction (columns p U V i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [evaluationFraction_lift, hcoeff, Polynomial.C_mul, smul_eq_C_mul, mul_assoc]
    apply evaluationFraction_injective
    rw [map_zero, map_sum]
    simp only [map_mul, hscaled, hc, mul_zero]
private def amplitude (q : ℕ) (u v : K[X]) : Bivar :=
  liftX u + seed ^ q * liftX v
private theorem amplitude_zero (q : ℕ) : amplitude q 0 0 = 0 := by
  simp only [amplitude, liftX, Polynomial.map_zero, mul_zero, add_zero]
private theorem amplitude_scale (q : ℕ) (d u v : K[X]) :
    amplitude q (d * u) (d * v) = liftX d * amplitude q u v := by
  simp only [amplitude, liftX, Polynomial.map_mul]
  ring
private theorem amplitude_eq_zero {q : ℕ} (hq : 0 < q) {u v : K[X]}
    (h : amplitude q u v = 0) : u = 0 ∧ v = 0 := by
  have hswap : C u + (Polynomial.X (R := K[X])) ^ q * C v = 0 := by
    simpa only [amplitude, seed, liftX, map_add, map_mul, map_pow, map_zero,
      Bivariate.swap_X, Bivariate.swap_map_C] using congrArg (Bivariate.swap (R := K)) h
  have hu := congrArg (fun W : Bivar => W.coeff 0) hswap
  have hv := congrArg (fun W : Bivar => W.coeff q) hswap
  have hshift : ((Polynomial.X (R := K[X])) ^ q * C v).coeff q = v := by
    simpa only [Nat.zero_add, coeff_C_zero] using (coeff_X_pow_mul (C v : Bivar) q 0)
  constructor
  · simpa only [coeff_add, coeff_C_zero, coeff_X_pow_mul', Nat.not_le_of_lt hq,
      ite_false, add_zero, coeff_zero] using hu
  · simpa only [coeff_add, hshift, coeff_C, hq.ne', ite_false, zero_add, coeff_zero] using hv
private theorem group_dependence {q : ℕ} {U V : Bivar} {f : Fin 4 → K[X]}
    (h : ∑ i, liftX (f i) * columns q U V i = 0) :
    amplitude 1 (f 0) (f 1) * U + amplitude q (f 2) (f 3) * V = 0 := by
  have h0 : columns q U V 0 = U := rfl
  have h1 : columns q U V 1 = seed * U := rfl
  have h2 : columns q U V 2 = V := rfl
  have h3 : columns q U V 3 = seed ^ q * V := rfl
  rw [Fin.sum_univ_four, h0, h1, h2, h3] at h
  simpa only [amplitude, pow_one, add_mul, mul_assoc, mul_left_comm, add_assoc] using h
private theorem nonzero_pairs {q : ℕ} (hq : 0 < q) {U V : Bivar} (hu : U ≠ 0) (hv : V ≠ 0)
    {f : Fin 4 → K[X]} (hf : f ≠ 0)
    (h : amplitude 1 (f 0) (f 1) * U + amplitude q (f 2) (f 3) * V = 0) :
    (![f 0, f 1] : Fin 2 → K[X]) ≠ 0 ∧ (![f 2, f 3] : Fin 2 → K[X]) ≠ 0 := by
  constructor
  · intro hz
    have h0 : f 0 = 0 := congrFun hz 0
    have h1 : f 1 = 0 := congrFun hz 1
    rw [h0, h1, amplitude_zero, zero_mul, zero_add] at h
    have hz' : amplitude q (f 2) (f 3) = 0 := (mul_eq_zero.mp h).resolve_right hv
    obtain ⟨h2, h3⟩ := amplitude_eq_zero hq hz'
    apply hf
    funext i
    fin_cases i <;> assumption
  · intro hz
    have h2 : f 2 = 0 := congrFun hz 0
    have h3 : f 3 = 0 := congrFun hz 1
    rw [h2, h3, amplitude_zero, zero_mul, add_zero] at h
    have hz' : amplitude 1 (f 0) (f 1) = 0 := (mul_eq_zero.mp h).resolve_right hu
    obtain ⟨h0, h1⟩ := amplitude_eq_zero Nat.zero_lt_one hz'
    apply hf
    funext i
    fin_cases i <;> assumption
private theorem normalize_pair {u v : K[X]} (h : (![u, v] : Fin 2 → K[X]) ≠ 0) :
    ∃ (d : K[X]) (w : Fin 2 → K[X]), d ≠ 0 ∧
      u = d * w 0 ∧ v = d * w 1 ∧ IsCoprime (w 0) (w 1) := by
  obtain ⟨d, w, hd, hw, hprim⟩ := PrimitiveVector.exists_normalization ![u, v] h
  obtain ⟨r, hr⟩ := (PrimitiveVector.primitive_iff_bezout w).mp hprim
  exact ⟨d, w, hd, hw 0, hw 1, r 0, r 1, by simpa only [Fin.sum_univ_two] using hr⟩
private def twistEquiv : K ≃+* K :=
  RingEquiv.ofBijective twist ⟨twist.injective, Finite.surjective_of_injective twist.injective⟩
private def untwist : K →+* K := twistEquiv.symm.toRingHom
private theorem map_untwist_twist (f : K[X]) : (f.map untwist).map twist = f := by
  rw [Polynomial.map_map]
  have h : twist.comp untwist = RingHom.id K := by
    apply RingHom.ext
    intro x
    exact twistEquiv.apply_symm_apply x
  rw [h, Polynomial.map_id]
private theorem liftX_ne_zero {f : K[X]} (hf : f ≠ 0) : liftX f ≠ 0 := by
  intro h
  exact hf (Polynomial.map_injective Polynomial.C Polynomial.C_injective
    (h.trans (Polynomial.map_zero _).symm))
private theorem cross_of_scaled_dependence {d a b : K[X]} (hd : d ≠ 0) {U V F G : Bivar}
    (h : (liftX (d * b) * F) * U + (liftX (d * a) * G) * V = 0) :
    U * -(liftX b * F) = V * (liftX a * G) := by
  have hscaled : liftX d * (U * (liftX b * F) + V * (liftX a * G)) = 0 := by
    rw [← h]
    simp only [liftX, Polynomial.map_mul]
    ring
  have hz := (mul_eq_zero.mp hscaled).resolve_left (liftX_ne_zero hd)
  exact (_root_.mul_neg U (liftX b * F)).trans (neg_eq_iff_add_eq_zero.mpr hz)
private theorem primitive_dependence {q : ℕ} (hq : 0 < q) {U V : Bivar}
    (hU : U ≠ 0) (hV : V ≠ 0) {f : Fin 4 → K[X]} (hf : f ≠ 0)
    (hsum : ∑ i, liftX (f i) * columns q U V i = 0) :
    ∃ (α β : Fin 2 → K[X]) (a b : K[X]), a ≠ 0 ∧ b ≠ 0 ∧ IsCoprime a b ∧
      IsCoprime (α 0) (α 1) ∧ IsCoprime (β 0) (β 1) ∧
      sameDirection U V (threeUAt q a β) (threeV b α) := by
  have hrel := group_dependence (q := q) (U := U) (V := V) (f := f) hsum
  obtain ⟨hleft, hright⟩ := nonzero_pairs hq hU hV hf hrel
  obtain ⟨b₀, α, hb₀, h0, h1, hα⟩ := normalize_pair hleft
  obtain ⟨a₀, βσ, ha₀, h2, h3, hβσ⟩ := normalize_pair hright
  have hab₀ : (![a₀, b₀] : Fin 2 → K[X]) ≠ 0 := fun h => ha₀ (congrFun h 0)
  obtain ⟨d, ab, hd, ha, hb, hab⟩ := normalize_pair hab₀
  let β : Fin 2 → K[X] := fun i => (βσ i).map untwist
  have ha' : ab 0 ≠ 0 := fun hz => ha₀ (by rw [ha, hz, mul_zero])
  have hb' : ab 1 ≠ 0 := fun hz => hb₀ (by rw [hb, hz, mul_zero])
  refine ⟨α, β, ab 0, ab 1, ha', hb', hab, hα,
    hβσ.map (Polynomial.mapRingHom untwist), ?_⟩
  rw [h0, h1, h2, h3, ha, hb] at hrel
  simp only [amplitude_scale] at hrel
  have hcross := cross_of_scaled_dependence hd hrel
  simpa only [sameDirection, threeUAt, threeV, β, map_untwist_twist, amplitude, pow_one]
    using hcross
private theorem threeUAt_native : threeUAt p = (threeU : K[X] → (Fin 2 → K[X]) → Bivar) := by
  unfold threeUAt threeU
  rfl
theorem proof : K1_8.c1 := by
  intro U V hU hV hr
  have hp : 0 < p := by decide
  obtain ⟨f, hf, hsum⟩ := polynomial_dependence hr
  obtain ⟨α, β, a, b, ha, hb, hab, hα, hβ, hdir⟩ :=
    primitive_dependence (q := p) (U := U) (V := V) (f := f) hp hU hV hf hsum
  refine ⟨⟨α, β, a, b, ha, hb, hab, hα, hβ, ?_⟩⟩
  simpa only [threeUAt_native] using hdir
end
end K1_8_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace K1_9
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
abbrev K := K1.K
abbrev I := K1.I
abbrev node := K1.node
abbrev twist := K1.twist
def pencil (P Q : K[X]) (z : K) : K[X] := P + C z * Q
def fold (u : K1.Words) (z : K) (i : I) : K := u 0 i + z * u 1 i
theorem map_eval_node (P : K[X]) (i : I) :
    (P.map twist).eval (node i) = twist (P.eval (node i)) :=
  Strata.eval_coefficient_map twist P (node i) (Native.native_domain_fixed i)
theorem pencil_natDegree (P Q : K[X]) (z : K) :
    (pencil P Q z).natDegree ≤ max P.natDegree Q.natDegree :=
  (natDegree_add_le _ _).trans (max_le_max le_rfl (natDegree_C_mul_le z Q))
theorem degree_sub_lt {P Q : K[X]} {n : ℕ} (hP : P.degree < n) (hQ : Q.degree < n) :
    (P-Q).degree < n :=
  (Polynomial.degree_sub_le _ _).trans_lt (max_lt hP hQ)
theorem pencil_degree {P Q : K[X]} {n : ℕ} (hP : P.degree < n) (hQ : Q.degree < n) (z : K) :
    (pencil P Q z).degree < n := by
  apply (Polynomial.degree_add_le _ _).trans_lt (max_lt hP ?_)
  by_cases hz : z = 0
  · simp [hz]
  · simpa only [degree_C_mul hz] using hQ
theorem eq_on_nodes (S : Finset I) (P Q : K[X])
    (hP : P.degree < S.card) (hQ : Q.degree < S.card)
    (h : ∀ i ∈ S, P.eval (node i) = Q.eval (node i)) : P = Q :=
  Polynomial.eq_of_degrees_lt_of_eval_index_eq S
    (fun _ _ _ _ hxy => node.injective hxy) hP hQ h
def seedCoeff (P : K1.Bivar) (j : ℕ) : K[X] := (Bivariate.swap P).coeff j
def crossValue (u : K1.Words) (a b : K[X]) (A : Fin 2 → K[X])
    (i : I) (l j : Fin 2) : K :=
  a.eval (node i) * twist ((A l).eval (node i)) * u j i -
    b.eval (node i) * (A j).eval (node i) * twist (u l i)
def CoefficientIdentities (u : K1.Words) (a b : K[X]) (A : Fin 2 → K[X])
    (P : K1.Bivar) (i : I) : Prop :=
  (seedCoeff P 0).eval (node i) = crossValue u a b A i 0 0 ∧
  (seedCoeff P 1).eval (node i) = crossValue u a b A i 0 1 ∧
  (seedCoeff P K1.p).eval (node i) = crossValue u a b A i 1 0 ∧
  (seedCoeff P (K1.p + 1)).eval (node i) = crossValue u a b A i 1 1
structure PolarData (u : K1.Words) where
  a : K[X]
  b : K[X]
  A : Fin 2 → K[X]
  Q : K → K → K[X]
  a_ne : a ≠ 0
  norms_ne : K1.sixNorm a ≠ K1.sixNorm b
  primitive : IsCoprime (A 0) (A 1)
  a_bound : a.natDegree + K1.amplitudeDegree (A 0) (A 1) ≤ 32685
  b_bound : b.natDegree + K1.amplitudeDegree (A 0) (A 1) ≤ 32685
  Q_degree : ∀ r s, (Q r s).degree < 163757
  nodes : ∀ r s i,
    (Q r s).eval (node i) =
      a.eval (node i) * twist ((pencil (A 0) (A 1) r).eval (node i)) * fold u s i -
      b.eval (node i) * (pencil (A 0) (A 1) s).eval (node i) * twist (fold u r i)
private theorem iterate_six : iterateFrobenius K K1.p 6 = RingHom.id K := by
  apply RingHom.ext
  intro x
  change x ^ K1.p ^ 6 = x
  have hc : Fintype.card K = K1.p ^ 6 := KoalaBear.card_ext6
  rw [← hc]
  exact FiniteField.pow_card x
theorem sixNorm_twist (P : K[X]) : K1.sixNorm (P.map twist) = K1.sixNorm P := by
  unfold K1.sixNorm
  have h (j : Fin 6) :
      (P.map twist).map (iterateFrobenius K K1.p j.val) =
        P.map (iterateFrobenius K K1.p (j.val + 1)) := by
    rw [Polynomial.map_map, iterateFrobenius_add, iterateFrobenius_one]
    rfl
  simp_rw [h]
  rw [Fin.prod_univ_castSucc (n := 5),
    Fin.prod_univ_succ (f := fun j : Fin 6 => P.map (iterateFrobenius K K1.p j.val))]
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero, Nat.reduceAdd,
    iterate_six, iterateFrobenius_zero, Polynomial.map_id]
  exact mul_comm _ _
theorem sixNorm_mul (P Q : K[X]) : K1.sixNorm (P*Q) = K1.sixNorm P * K1.sixNorm Q := by
  simp only [K1.sixNorm, Polynomial.map_mul, Finset.prod_mul_distrib]
theorem sixNorm_ne_zero {P : K[X]} (h : P ≠ 0) : K1.sixNorm P ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ =>
    (Polynomial.map_ne_zero_iff (iterateFrobenius K K1.p j.val).injective).mpr h
end
end K1_9
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_9
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
private theorem all_card : (Finset.univ : Finset I).card = 262144 := by
  rw [Finset.card_univ, IRSProfile.card_index]
private theorem affine_zero (f χ : K → K) (h : Function.Injective χ)
    {r s : K} (hrs : r ≠ s) (hf : ∀ z, f z = f 0 + χ z * (f 1 - f 0))
    (hr : f r = 0) (hs : f s = 0) (z : K) : f z = 0 := by
  have h₁ := hf r
  have h₂ := hf s
  have hb : (χ r - χ s) * (f 1 - f 0) = 0 := by linear_combination h₂ - h₁ + hr - hs
  have hd := (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr (h.ne hrs))
  have hz : f z = f 0 := by simpa [hd] using hf z
  have hrr : f r = f 0 := by simpa [hd] using h₁
  exact hz.trans (hrr.symm.trans hr)
private def residual (u : K1.Words) (P Q : K[X]) : K1.Words :=
  fun j i => u j i - (if j = 0 then P else Q).eval (node i)
private theorem fold_residual (u : K1.Words) (P Q : K[X]) (z : K) (i : I) :
    fold (residual u P Q) z i = fold u z i - (pencil P Q z).eval (node i) := by
  simp [fold, pencil, residual]
  ring
end
end K1_9
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace K1_9
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
private theorem coeff_seedCoeff (P : K1.Bivar) (j m : ℕ) :
    (seedCoeff P j).coeff m = (P.coeff m).coeff j := by
  induction P using Polynomial.induction_on' with
  | add A B hA hB => simp only [seedCoeff, map_add, coeff_add] at hA hB ⊢; rw [hA, hB]
  | monomial n f =>
    simp only [seedCoeff, Bivariate.swap_monomial, coeff_mul_C, coeff_map,
      C_mul_X_pow_eq_monomial, coeff_monomial]
    split_ifs <;> simp
private theorem eval_seedCoeff (P : K1.Bivar) (j : ℕ) (x : K) :
    (seedCoeff P j).eval x = (P.eval (C x)).coeff j := by
  induction P using Polynomial.induction_on' with
  | add A B hA hB =>
    simp only [seedCoeff, map_add, coeff_add, eval_add] at hA hB ⊢
    rw [hA, hB]
  | monomial n f =>
    simp only [seedCoeff, Bivariate.swap_monomial, eval_monomial, ← C_pow, coeff_mul_C,
      coeff_map, eval_mul, eval_C, eval_pow, eval_X]
private theorem seedCoeff_degree (P : K1.Bivar) (j h : ℕ) (hp : P.degree < h) :
    (seedCoeff P j).degree < h := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro m hm
  rw [coeff_seedCoeff, coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast hm)), coeff_zero]
private theorem eval_liftX (P : K[X]) (x : K) :
    (K1.liftX P).eval (C x) = C (P.eval x) :=
  Polynomial.eval_map_apply Polynomial.C x
theorem eval_first (a : K1.K[X]) (A : Fin 2 → K1.K[X]) (i : K1.I) (n : ℕ) :
    (K1.liftX a * (K1.liftX ((A 0).map K1.twist) +
      K1.seed ^ n * K1.liftX ((A 1).map K1.twist))).eval (C (K1.node i)) =
      C (a.eval (K1.node i)) * (C (K1.twist ((A 0).eval (K1.node i))) +
        Polynomial.X ^ n * C (K1.twist ((A 1).eval (K1.node i)))) := by
  rw [eval_mul, eval_liftX a, eval_add, eval_liftX ((A 0).map K1.twist), eval_mul,
    eval_liftX ((A 1).map K1.twist), eval_pow, K1.seed, eval_C, map_eval_node, map_eval_node]
private theorem eval_threeV (b : K[X]) (A : Fin 2 → K[X]) (i : I) :
    (K1.threeV b A).eval (C (node i)) =
      -(C (b.eval (node i)) * (C ((A 0).eval (node i)) + (Polynomial.X (R := K)) * C ((A 1).eval (node i)))) := by
  unfold K1.threeV
  rw [eval_neg, eval_mul, eval_liftX b, eval_add, eval_liftX (A 0), eval_mul,
    eval_liftX (A 1), K1.seed, eval_C]
theorem coefficients_at_node
    (u : K1.Words) (a b : K1.K[X]) (A : Fin 2 → K1.K[X])
    (i : K1.I) (n : ℕ) (hn : 1 < n) (hσ : ∀ z : K1.K, z ^ n = K1.twist z) (P U : K1.Bivar)
    (hU : U.eval (C (K1.node i)) =
      C (a.eval (K1.node i)) * (C (K1.twist ((A 0).eval (K1.node i))) +
        Polynomial.X ^ n * C (K1.twist ((A 1).eval (K1.node i)))))
    (h : P.eval (C (K1.node i)) =
      U.eval (C (K1.node i)) *
          (C (u 0 i) + Polynomial.X (R := K1.K) * C (u 1 i)) +
      (K1.threeV b A).eval (C (K1.node i)) *
        (C (u 0 i ^ n) + Polynomial.X (R := K1.K) ^ n * C (u 1 i ^ n))) :
    (seedCoeff P 0).eval (node i) = crossValue u a b A i 0 0 ∧
    (seedCoeff P 1).eval (node i) = crossValue u a b A i 0 1 ∧
    (seedCoeff P n).eval (node i) = crossValue u a b A i 1 0 ∧
    (seedCoeff P (n + 1)).eval (node i) = crossValue u a b A i 1 1 := by
  let q := crossValue u a b A i
  have hexpand : P.eval (C (node i)) =
      C (q 0 0) + C (q 0 1) * Polynomial.X + C (q 1 0) * Polynomial.X ^ n +
        C (q 1 1) * Polynomial.X ^ (n + 1) := by
    rw [h, hU, hσ (u 0 i), hσ (u 1 i), eval_threeV, pow_succ (Polynomial.X (R := K)) n]
    simp only [q, crossValue, map_sub, map_mul]
    generalize (Polynomial.X (R := K)) ^ n = xp
    ring
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have hs0 : n + 1 ≠ 0 := by omega
  have hs1 : n + 1 ≠ 1 := by omega
  have hs : n + 1 ≠ n := by omega
  simp only [eval_seedCoeff, hexpand, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow,
    h0, h0.symm, h1, h1.symm, hs0, hs0.symm, hs1, hs1.symm, hs, hs.symm, ite_true, ite_false, and_self,
    Nat.zero_ne_one, Nat.one_ne_zero, zero_add, add_zero, q]
end
end K1_9
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
open scoped BigOperators
private def bivariate {R : Type*} [CommSemiring R] :
    Polynomial (Polynomial R) →+* MvPolynomial (Fin 2) R :=
  (MvPolynomial.finSuccEquiv R 1).symm.toRingHom.comp
    (Polynomial.mapRingHom (MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm.toRingHom)
private theorem coeff_bivariate {R : Type*} [CommSemiring R]
    (P : Polynomial (Polynomial R)) (d : Fin 2 →₀ ℕ) :
    (bivariate P).coeff d = (P.coeff (d 0)).coeff (d 1) := by
  let Q := (P.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm.toRingHom)
  change ((MvPolynomial.finSuccEquiv R 1).symm Q).coeff d = _
  rw [← Finsupp.cons_tail d, ← MvPolynomial.finSuccEquiv_coeff_coeff,
    AlgEquiv.apply_symm_apply]
  simp only [Q, Polynomial.coeff_map]
  change ((MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm (P.coeff (d 0))).coeff d.tail = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
  rfl
private theorem bivariate_injective {R : Type*} [CommSemiring R] :
    Function.Injective (bivariate (R := R)) := by
  exact (MvPolynomial.finSuccEquiv R 1).symm.injective.comp
    (Polynomial.map_injective _ (MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm.injective)
private theorem sum_exponents (d : Fin 2 →₀ ℕ) : (d.sum fun _ e => e) = d 1 + d 0 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two, Nat.add_comm]
private theorem bivariate_totalDegree_le_iff {R : Type*} [CommSemiring R]
    (P : Polynomial (Polynomial R)) (B : ℕ) :
    (bivariate P).totalDegree ≤ B ↔
      ∀ j i, (P.coeff j).coeff i ≠ 0 → i + j ≤ B := by
  constructor
  · intro h j i hji
    let d : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![j, i]
    have hd : d ∈ (bivariate P).support := by
      rw [MvPolynomial.mem_support_iff, coeff_bivariate]
      exact hji
    have hsum := (MvPolynomial.le_totalDegree hd).trans h
    rw [sum_exponents] at hsum
    exact hsum
  · intro h
    unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro d hd
    rw [sum_exponents]
    rw [MvPolynomial.mem_support_iff, coeff_bivariate] at hd
    exact h _ _ hd
private theorem coeff_fixedIncl (G : ODE) (j i : ℕ) :
    ((fixedIncl G).coeff j).coeff i = MvPolynomial.C ((G.coeff j).coeff i) := by
  simp only [fixedIncl, K1_14_3.fixedEmbedding, Polynomial.coe_mapRingHom, coeff_map]
private theorem fixedIncl_natDegree (G : ODE) : (fixedIncl G).natDegree = G.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective
    (Polynomial.map_injective _ (MvPolynomial.C_injective (Fin 2) FX)) G
private theorem fixedCaps {P : Jet} {G : ODE} {s : Shape}
    (hP : P ≠ 0) (hCaps : RowCaps P s) (hd : fixedIncl G ∣ P) :
    ODECaps G s.B s.J := by
  have hG : G ≠ 0 := by
    intro h
    exact hP (zero_dvd_iff.mp (by simpa only [h, map_zero] using hd))
  have hJ : P.natDegree ≤ s.J := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    apply Polynomial.ext
    intro i
    rw [coeff_zero]
    by_contra hi
    exact (Nat.not_le_of_lt hj) (hCaps j i hi).2.1
  have hB : (bivariate P).totalDegree ≤ s.B :=
    (bivariate_totalDegree_le_iff P s.B).mpr (fun j i h => (hCaps j i h).1)
  have hfixedB : (bivariate (fixedIncl G)).totalDegree ≤ s.B := by
    apply (MvPolynomial.totalDegree_le_of_dvd_of_isDomain (map_dvd bivariate hd) _).trans hB
    exact fun h => hP (bivariate_injective (h.trans (map_zero bivariate).symm))
  refine ⟨hG, ?_, ?_⟩
  · rw [← fixedIncl_natDegree G]
    exact (natDegree_le_of_dvd hd hP).trans hJ
  · intro j i hji
    apply (bivariate_totalDegree_le_iff (fixedIncl G) s.B).mp hfixedB j i
    rw [coeff_fixedIncl]
    exact fun h => hji ((MvPolynomial.C_injective (Fin 2) FX) (h.trans (map_zero _).symm))
private theorem extract (P : Jet) : P ≠ 0 →
    ∃ (G : ODE) (R : Jet), P = fixedIncl G * R ∧
      ∀ D : ODE, Irreducible (fixedIncl D) → ¬ fixedIncl D ∣ R := by
  classical
  refine (wellFounded_dvdNotUnit (α := Jet)).induction
    (C := fun P => P ≠ 0 → ∃ (G : ODE) (R : Jet), P = fixedIncl G * R ∧
      ∀ D : ODE, Irreducible (fixedIncl D) → ¬ fixedIncl D ∣ R) P ?_
  intro P ih hP
  by_cases h : ∃ D : ODE, Irreducible (fixedIncl D) ∧ fixedIncl D ∣ P
  · obtain ⟨D, hD, Q, hQ⟩ := h
    have hQ0 : Q ≠ 0 := by
      intro hz
      exact hP (by simpa [hz] using hQ)
    have hlt : DvdNotUnit Q P := ⟨hQ0, fixedIncl D, hD.not_isUnit, hQ.trans (mul_comm _ _)⟩
    obtain ⟨G, R, hR, hstrip⟩ := ih Q hlt hQ0
    refine ⟨D * G, R, ?_, hstrip⟩
    rw [map_mul, mul_assoc, ← hR, ← hQ]
  · refine ⟨1, P, by rw [map_one, one_mul], ?_⟩
    exact fun D hD hdiv => h ⟨D, hD, hdiv⟩
theorem proof : K1_14_2_2.c1 := by
  intro P s hP hCaps
  obtain ⟨G, R, hfac, hstrip⟩ := extract P hP
  exact ⟨⟨G, fixedCaps hP hCaps ⟨R, hfac⟩, R, hfac, hstrip⟩⟩
end
end K1_14_2_2_1
end
section
namespace K1_14_3_4_3
noncomputable section
open K1_14 K1_14_3 Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
def fibreEvaluation (y v : SeedClosure) : FibreJet →+* SeedClosure :=
  (evalRingHom y).comp (evalRingHom (C v))
theorem fibrePoint_eq_ker (y v : SeedClosure) :
    fibrePoint y v = RingHom.ker (fibreEvaluation y v) := by
  ext G
  exact mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero
instance fibrePoint_isPrime (y v : SeedClosure) : (fibrePoint y v).IsPrime := by
  rw [fibrePoint_eq_ker]
  exact RingHom.ker_isPrime (fibreEvaluation y v)
end
end K1_14_3_4_3
end
