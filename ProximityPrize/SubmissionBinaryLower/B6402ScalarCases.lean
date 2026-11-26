import ProximityPrize.SubmissionBinaryLower.B6402QuadraticCase
import ProximityPrize.SubmissionBinaryLower.B6402OrdinaryLinear
/-! Scalar list assembly with the 6402 agreement count and small-table
witnesses. The hard quartic geometry is supplied explicitly. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402ScalarCases
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd B6401KerDOrders B6401KerD2
open B6401Params hiding A
open B6402HybridP64 (A)
open B6402FarkasVerifier B6402IntFarkas B6402IntSmallCerts B6402CertsT1 B6402CertsT2 B6402CertsT3
open B6401SmallAlg B6401ResLineOrd B6402QuotBridge B6402PointSurplus B6401ListAndMCA
open B6401FactorBound (dXBi_zero cLiftZ cLiftZ_wdeg cLiftZ_natDegree irreducible_liftCRat_cLiftZ
  not_irred_kerD2_coeff1_zero card_roots_biPoly_le cLiftZ_sum_kerDBasisPoly wdegBi_ge_natDegree_mul
  resultant_54_ne_zero evalContact_contactDeriv)
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary BCHKSSubstitutionVanish P64Cofactor P64LineOrder
open scoped BigOperators
set_option maxHeartbeats 2500000
local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

def HardList : Prop :=
  ∀ (u : Idx → Fld) (F : ContactPoly Fld) (WF : ℕ) (fc : KerDIdx wY WF 1 → Fld),
    F=∑ e,cC (fc e)*kerDBasisPoly e.1 → Irreducible F → contactDeriv F=0 → F.natDegree=1 →
    wdeg wY F=WF → (F.coeff 1).natDegree=4 → (F.coeff 0).natDegree≤5 →
    5*wY≤WF+1 → WF+1<6*wY → (WF:ℚ)/wY<28/5 → resultant (F.coeff 0) (F.coeff 1) 5 4≠0 →
    ∀ (S : Finset (Fld[X])), (∀ P∈S,P.natDegree≤wY) →
      (∀ P∈S,A≤(Finset.univ.filter fun i : Idx => P.eval (BinaryIRSProfile.domain i)=u i).card) →
      (∀ P∈S,evalContact F P=0) → S.card≤100000

private lemma card_roots_contactDeriv_le {F0 : ContactPoly Fld}
    (hirr : Irreducible F0) (hdeg1 : 1 ≤ F0.natDegree) (hdeg2 : F0.natDegree ≤ 2)
    (hW : wdeg wY F0 ≤ 2 * A * 9 - 1) (hDne : contactDeriv F0 ≠ 0)
    (TF : Finset (Polynomial Fld)) (hTF : ∀ P ∈ TF, evalContact F0 P = 0) :
    TF.card ≤ 150 := by
  classical
  have hwY1 : 1 ≤ wY := by norm_num [wY]
  have hndvd : ¬ F0 ∣ contactDeriv F0 := by
    rw [dvd_contactDeriv_iff wY hwY1 hirr.ne_zero]; exact hDne
  let dF := F0.natDegree
  let dD := (contactDeriv F0).natDegree
  have hdD_le : dD ≤ dF + 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro k hk
    have hk1 : F0.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hk2 : F0.coeff (k - 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [coeff_contactDeriv, show k ≠ 0 by omega, ↓reduceIte, hk1, hk2, dXBi_zero, Polynomial.derivative_zero, add_zero]
  let R_el : BiPoly Fld := Polynomial.resultant F0 (contactDeriv F0) dF dD
  have hRel_ne : R_el ≠ 0 := by
    have hprim : F0.IsPrimitive := hirr.isPrimitive (by omega)
    let ι : BiPoly Fld →+* FractionRing (BiPoly Fld) := algebraMap (BiPoly Fld) (FractionRing (BiPoly Fld))
    have hι : Function.Injective ι := IsFractionRing.injective (BiPoly Fld) (FractionRing (BiPoly Fld))
    have hirrK : Irreducible (F0.map ι) := hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
    have hndvdK : ¬ F0.map ι ∣ (contactDeriv F0).map ι := fun h =>
      hndvd (hprim.dvd_of_fraction_map_dvd_fraction_map h)
    have hcop : IsCoprime (F0.map ι) ((contactDeriv F0).map ι) := by
      refine EuclideanDomain.isCoprime_of_dvd (x := F0.map ι) (y := (contactDeriv F0).map ι) (fun h => hirrK.ne_zero h.1) ?_
      intro p hp _ hpF hpD
      rcases hpF with ⟨q, hq⟩
      rcases hirrK.isUnit_or_isUnit hq with hu | hqu
      · exact hp hu
      · rcases hqu with ⟨u, hu⟩
        have hdvd_p : F0.map ι ∣ p := ⟨(u⁻¹ : _), by rw [hq, ← hu, mul_assoc, Units.mul_inv, mul_one]⟩
        exact hndvdK (hdvd_p.trans hpD)
    intro h0
    have hresK : Polynomial.resultant (F0.map ι) ((contactDeriv F0).map ι)
        (F0.map ι).natDegree ((contactDeriv F0).map ι).natDegree = 0 := by
      rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι,
        Polynomial.resultant_map_map, show Polynomial.resultant F0 (contactDeriv F0) dF dD = 0 from h0, map_zero]
    exact Polynomial.resultant_ne_zero _ _ hcop hresK
  have hRel_eval : ∀ P ∈ TF, R_el.eval P = 0 := by
    intro P hP
    have hFP : evalContact F0 P = 0 := hTF P hP
    have hDP : evalContact (contactDeriv F0) P = 0 := by
      rw [evalContact_contactDeriv, hFP, Polynomial.derivative_zero]
    let ψ : BiPoly Fld →+* RatFunc Fld := (algebraMap (Polynomial Fld) (RatFunc Fld)).comp (Polynomial.evalRingHom P)
    have hψ_inj : Function.Injective (algebraMap (Polynomial Fld) (RatFunc Fld)) :=
      IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
    apply hψ_inj; rw [map_zero]
    change ψ R_el = 0
    rw [show ψ R_el = Polynomial.resultant (F0.map ψ) ((contactDeriv F0).map ψ) dF dD from
      (Polynomial.resultant_map_map F0 (contactDeriv F0) dF dD ψ).symm]
    refine P64Resultant.fixed_resultant_eq_zero_of_common_root
      (y := algebraMap (Polynomial Fld) (RatFunc Fld) P.derivative)
      (Polynomial.natDegree_map_le) (Polynomial.natDegree_map_le) (by omega) ?_ ?_
    · have hcomm : (F0.map ψ).eval (algebraMap (Polynomial Fld) (RatFunc Fld) P.derivative) =
          algebraMap (Polynomial Fld) (RatFunc Fld) (evalContact F0 P) := by
        unfold evalContact ψ
        rw [← Polynomial.map_map, Polynomial.eval_map_apply]
      simpa [hFP] using hcomm
    · have hcomm : ((contactDeriv F0).map ψ).eval (algebraMap (Polynomial Fld) (RatFunc Fld) P.derivative) =
          algebraMap (Polynomial Fld) (RatFunc Fld) (evalContact (contactDeriv F0) P) := by
        unfold evalContact ψ
        rw [← Polynomial.map_map, Polynomial.eval_map_apply]
      simpa [hDP] using hcomm
  have hRel_deg : R_el.natDegree ≤ 150 := by
    have hW_D : wdeg wY (contactDeriv F0) ≤ 2 * A * 9 - 1 := by
      have h1 := wdeg_contactDeriv_add_one_le wY hwY1 F0 hDne; omega
    have hdeg_coeff : ∀ (Q : ContactPoly Fld), wdeg wY Q ≤ 2 * A * 9 - 1 → ∀ k, (Q.coeff k).natDegree ≤ 25 := by
      intro Q hWQ k
      by_cases hk : Q.coeff k = 0
      · simp [hk]
      · have h1 := wdegBi_le_of_wdeg_coeff hWQ k
        have h2 := wdegBi_ge_natDegree_mul wY (Q.coeff k) hk
        have hle := h2.trans h1
        have hN : 2 * A * 9 - 1 = 26689499 := by norm_num [A]
        have hw : wY = 1048575 := rfl
        rw [hw] at hle; omega
    unfold R_el Polynomial.resultant
    rw [Matrix.det_apply]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
    dsimp only [Function.comp_apply]
    have hsmul : ∀ (u : ℤˣ) (p : BiPoly Fld), (u • p).natDegree ≤ p.natDegree := fun u p => by
      rw [Units.smul_def]; rcases Int.units_eq_one_or u with rfl | rfl <;> simp
    refine (hsmul _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
    calc ∑ i : Fin (dF + dD), (Polynomial.sylvester F0 (contactDeriv F0) dF dD (σ i) i).natDegree
        ≤ ∑ _i : Fin (dF + dD), 25 := by
          apply Finset.sum_le_sum; intro i _
          simp only [Polynomial.sylvester, Matrix.of_apply]
          refine Fin.addCases (fun r => ?_) (fun r => ?_) i
          · simp only [Fin.addCases_left]; split_ifs
            · exact hdeg_coeff _ hW_D _
            · simp
          · simp only [Fin.addCases_right]; split_ifs
            · exact hdeg_coeff F0 hW _
            · simp
      _ = (dF + dD) * 25 := by simp
      _ ≤ 150 := by omega
  exact (card_roots_biPoly_le hRel_ne TF hRel_eval).trans hRel_deg

private lemma mapC_kerDLocalPoly (x0 y0 : Fld) (e : ℕ × ℕ × ℕ × ℕ) :
    (kerDLocalPoly x0 y0 e).map (Polynomial.mapRingHom (Polynomial.mapRingHom Polynomial.C)) =
      kerDLocalPoly (Polynomial.C x0) (Polynomial.C y0) e := by
  let ψ : LocalPoly Fld →+* LocalPoly (Polynomial Fld) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.C : Fld →+* Polynomial Fld)))
  change ψ (kerDLocalPoly x0 y0 e) = kerDLocalPoly (Polynomial.C x0) (Polynomial.C y0) e
  have hC : ∀ a : Fld, ψ (locC a) = locC (Polynomial.C a) := fun a => by
    unfold ψ locC; simp [Polynomial.map_C]
  have hR : ψ locR = locR := by unfold ψ locR; simp [Polynomial.map_C, Polynomial.map_X]
  have hW : ψ locW = locW := by unfold ψ locW; simp [Polynomial.map_C, Polynomial.map_X]
  have hT : ψ locT = locT := by unfold ψ locT; simp [Polynomial.map_X]
  have hU : ψ localU = localU := by unfold localU; rw [map_add, map_pow, map_mul, map_pow, hW, hT, hR]
  unfold kerDLocalPoly
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    map_add, map_add, map_mul, map_add, map_add,
    hR, hW, hT, hU, hC, hC, hC, hC, map_pow, map_pow]

/-- **Main Scalar List-Size Bound (`ScalarListBound 10000000`):**
At agreement threshold `A = 1482831`, every received word `u : Idx → Fld` has at most `10^7`
degree-`≤ wY` polynomials agreeing with `u` on `≥ A` coordinates! -/
theorem scalar_of_hard (hard : HardList) : B6402Protocol.ScalarListBound 10000000 := by
  classical
  intro u T hT
  let W0 : ℕ := 2 * A * 9 - 1
  have hsurp0 : Fintype.card Idx * rankKerD 9 2 * (0 + 1) + 0 * yWeightSum wY W0 2 <
      varsKerDExact wY W0 2 * (0 + 1) := by
    rw [BinaryIRSProfile.card_index]
    norm_num [N, A, wY, W0, rankKerD, varsKerDExact, Finset.sum_range_succ, Finset.sum_range_zero]
  obtain ⟨Qz, q_coord, hQz_eq, hQz_ne, _, hQz_deg, hQz_wdeg, hQz_wYZ, _, hQz_van⟩ :=
    exists_global_contact_interpolant_wtd BinaryIRSProfile.domain (fun i => Polynomial.C (u i))
      (dy := 0) (wY := wY) (W0 := W0) (s0 := 2) (m0 := 9) (D_ZF := 0)
      (by norm_num [wY]) (fun _ => by simp) (by simp) hsurp0
  let Q0 : ContactPoly Fld := evalZContact Qz 0
  have hQ0_sum : Q0 = ∑ e : KerDIdx wY W0 2, cC ((q_coord e).eval 0) * kerDBasisPoly e.1 := by
    dsimp only [Q0]; rw [hQz_eq]; exact evalZContact_sum_kerD q_coord 0
  have hQ0_ne : Q0 ≠ 0 := by
    intro h0; apply hQz_ne
    apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
    have hdeg0 : (((Qz.coeff k).coeff j).coeff i).natDegree = 0 :=
      Nat.eq_zero_of_le_zero (natDegree_Z_le_of_wYZ hQz_wYZ k j i)
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    have hev0 : (((Qz.coeff k).coeff j).coeff i).eval 0 = 0 := by
      have h1 := congrArg (fun Q : ContactPoly Fld => ((Q.coeff k).coeff j).coeff i) h0
      simpa [Q0, evalZContact] using h1
    rw [hC, Polynomial.eval_C] at hev0
    rw [hC, hev0, map_zero, Polynomial.coeff_zero, Polynomial.coeff_zero, Polynomial.coeff_zero]
  have hQ0_deg : Q0.natDegree ≤ 2 := (Polynomial.natDegree_map_le).trans hQz_deg
  have hQ0_wdeg : wdeg wY Q0 ≤ W0 := by
    rw [wdeg_le_iff]; intro k j i hnz
    have hnz' : ((Qz.coeff k).coeff j).coeff i ≠ 0 := fun h => hnz (by simp [Q0, evalZContact, h])
    exact (wdeg_le_iff wY W0 Qz).mp hQz_wdeg k j i hnz'
  have hQ0_van : ∀ P ∈ T, evalContact Q0 P = 0 := by
    intro P hP
    have ⟨hPdeg, hPcard⟩ := hT P hP
    dsimp only [Q0]; rw [hQz_eq]
    refine evalContact_eq_zero_of_global_coords BinaryIRSProfile.domain (fun i => Polynomial.C (u i))
      (by norm_num [wY]) (by norm_num [W0, A]) q_coord hQz_van 0 P hPdeg
      (Finset.univ.filter fun i : Idx => P.eval (BinaryIRSProfile.domain i) = u i) hPcard ?_
    intro i hi; simpa [Polynomial.eval_C] using (Finset.mem_filter.mp hi).2
  -- UFD factorization of `Q0` in `ContactPoly Fld`!
  let facs := UniqueFactorizationMonoid.normalizedFactors Q0
  let facs0 := facs.filter fun F => F.natDegree = 0
  let facs1 := facs.filter fun F => 1 ≤ F.natDegree
  have hfacs_split : facs = facs0 + facs1 := by
    ext F
    simp only [facs0, facs1, Multiset.count_add, Multiset.count_filter]
    by_cases h0 : F.natDegree = 0
    · simp [h0]
    · simp [h0, show 1 ≤ F.natDegree by omega]
  obtain ⟨uQ, huQ⟩ := UniqueFactorizationMonoid.prod_normalizedFactors (a := Q0) hQ0_ne
  have hQ0_fac : facs0.prod * facs1.prod * (uQ : ContactPoly Fld) = Q0 := by
    rw [← Multiset.prod_add, ← hfacs_split]; exact huQ
  have hfacs0_deg0 : facs0.prod.natDegree = 0 := by
    have hgen : ∀ m : Multiset (ContactPoly Fld), (∀ F ∈ m, F.natDegree = 0) → m.prod.natDegree = 0 := by
      intro m; induction m using Multiset.induction_on with
      | empty => intro _; simp
      | cons a s ih =>
          intro h
          rw [Multiset.prod_cons]
          exact Nat.eq_zero_of_le_zero (Polynomial.natDegree_mul_le.trans
            (by rw [h a (Multiset.mem_cons_self a s), ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))]))
    exact hgen facs0 fun F hF => (Multiset.mem_filter.mp hF).2
  let G0 : BiPoly Fld := facs0.prod.coeff 0
  have hfacs0_eq : facs0.prod = Polynomial.C G0 := Polynomial.eq_C_of_natDegree_eq_zero hfacs0_deg0
  have hG0_ne : G0 ≠ 0 := by
    intro h0; apply hQ0_ne
    rw [← hQ0_fac, hfacs0_eq, h0, map_zero, zero_mul, zero_mul]
  have hG0_deg : G0.natDegree ≤ 25 := by
    have hdvd0 : Polynomial.C G0 ∣ Q0 := ⟨facs1.prod * (uQ : ContactPoly Fld), by rw [← hQ0_fac, hfacs0_eq]; ring⟩
    rcases hdvd0 with ⟨R0, hR0⟩
    have hR0_ne : R0 ≠ 0 := fun h0 => hQ0_ne (by rw [hR0, h0, mul_zero])
    have hwG : wdeg wY (Polynomial.C G0) ≤ W0 := by
      have h1 := wdeg_mul wY (Polynomial.C_ne_zero.mpr hG0_ne) hR0_ne
      rw [← hR0] at h1; omega
    have hwBi : wdegBi wY G0 ≤ W0 := by simpa using wdegBi_le_of_wdeg_coeff hwG 0
    have hmul := wdegBi_ge_natDegree_mul wY G0 hG0_ne
    have hle := hmul.trans hwBi
    have hW0 : W0 = 26689499 := by norm_num [W0, A]
    have hw : wY = 1048575 := rfl
    rw [hw] at hle; omega
  have hfacs1_card : facs1.card ≤ 2 := by
    have hsum : ∀ m : Multiset (ContactPoly Fld), (∀ F ∈ m, Irreducible F ∧ 1 ≤ F.natDegree) →
        m.card ≤ m.prod.natDegree := by
      intro m; induction m using Multiset.induction_on with
      | empty => intro _; simp
      | cons a s ih =>
          intro h
          have ha := h a (Multiset.mem_cons_self a s)
          have hs : ∀ x ∈ s, Irreducible x ∧ 1 ≤ x.natDegree := fun x hx => h x (Multiset.mem_cons_of_mem hx)
          have hs_ne : s.prod ≠ 0 := Multiset.prod_ne_zero (s := s) fun h0 => (hs 0 h0).1.ne_zero rfl
          rw [Multiset.card_cons, Multiset.prod_cons, Polynomial.natDegree_mul ha.1.ne_zero hs_ne]
          have := ih hs; omega
    have h1 := hsum facs1 fun F hF => ⟨UniqueFactorizationMonoid.irreducible_of_normalized_factor F
      (Multiset.mem_filter.mp hF).1, (Multiset.mem_filter.mp hF).2⟩
    have hf1_ne : facs1.prod ≠ 0 := fun h0 => hQ0_ne (by rw [← hQ0_fac, h0, mul_zero, zero_mul])
    have hf0_ne : facs0.prod ≠ 0 := fun h0 => hQ0_ne (by rw [← hQ0_fac, h0, zero_mul, zero_mul])
    have hprod_deg : facs1.prod.natDegree ≤ Q0.natDegree := by
      rw [← hQ0_fac, Polynomial.natDegree_mul (mul_ne_zero hf0_ne hf1_ne) uQ.ne_zero,
        Polynomial.natDegree_mul hf0_ne hf1_ne]
      omega
    omega
  -- Every `P ∈ T` vanishes on either `G0` or some `F0 ∈ facs1.toFinset`!
  have hT_cover : T ⊆ (T.filter fun P => G0.eval P = 0) ∪
      facs1.toFinset.biUnion (fun F0 => T.filter fun P => evalContact F0 P = 0) := by
    intro P hP
    have h0 := hQ0_van P hP
    rw [← hQ0_fac, evalContact_mul, evalContact_mul, hfacs0_eq] at h0
    have hu_ne : evalContact (uQ : ContactPoly Fld) P ≠ 0 := by
      rcases uQ.isUnit with ⟨v, hv⟩
      intro h0'
      have h1 : evalContact (1 : ContactPoly Fld) P = 0 := by
        have hv1 := congrArg (fun q => evalContact q P) v.mul_inv
        rw [evalContact_mul, hv, h0', zero_mul] at hv1; exact hv1.symm
      have : evalContact (1 : ContactPoly Fld) P = 1 := by unfold evalContact; simp
      rw [this] at h1; exact one_ne_zero h1
    have h01 := (mul_eq_zero.mp h0).resolve_right hu_ne
    rcases mul_eq_zero.mp h01 with hG | hFprod
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP, by simpa [evalContact] using hG⟩)
    · have hex : ∃ F0 ∈ facs1, evalContact F0 P = 0 := by
        have hgen : ∀ m : Multiset (ContactPoly Fld), evalContact m.prod P = 0 → ∃ F0 ∈ m, evalContact F0 P = 0 := by
          intro m; induction m using Multiset.induction_on with
          | empty => intro h; unfold evalContact at h; simp at h
          | cons a s ih =>
              intro h; rw [Multiset.prod_cons, evalContact_mul] at h
              rcases mul_eq_zero.mp h with ha | hs
              · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
              · obtain ⟨F0, hF0, hev⟩ := ih hs; exact ⟨F0, Multiset.mem_cons_of_mem hF0, hev⟩
        exact hgen facs1 hFprod
      obtain ⟨F0, hF0, hev⟩ := hex
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨F0, Multiset.mem_toFinset.mpr hF0,
        Finset.mem_filter.mpr ⟨hP, hev⟩⟩)
  -- Bound each factor `F0 ∈ facs1.toFinset` by `≤ 100000`!
  have hfac_bound : ∀ F0 ∈ facs1.toFinset, (T.filter fun P => evalContact F0 P = 0).card ≤ 100000 := by
    intro F0 hF0
    have hF0_mem : F0 ∈ facs1 := Multiset.mem_toFinset.mp hF0
    have hirr : Irreducible F0 := UniqueFactorizationMonoid.irreducible_of_normalized_factor F0 (Multiset.mem_filter.mp hF0_mem).1
    have hd1 : 1 ≤ F0.natDegree := (Multiset.mem_filter.mp hF0_mem).2
    have hdvd : F0 ∣ Q0 := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_filter.mp hF0_mem).1
    rcases hdvd with ⟨Q', hQ'⟩
    have hQ'_ne : Q' ≠ 0 := fun h0 => hQ0_ne (by rw [hQ', h0, mul_zero])
    have hd2 : F0.natDegree ≤ 2 := by
      have := Polynomial.natDegree_mul hirr.ne_zero hQ'_ne; rw [← hQ'] at this; omega
    have hWF_le : wdeg wY F0 ≤ W0 := by
      have := wdeg_mul wY hirr.ne_zero hQ'_ne; rw [← hQ'] at this; omega
    set TF := T.filter fun P => evalContact F0 P = 0
    by_cases hDF : contactDeriv F0 ≠ 0
    · exact (card_roots_contactDeriv_le hirr hd1 hd2 hWF_le hDF TF (fun P hP => (Finset.mem_filter.mp hP).2)).trans (by omega)
    · push Not at hDF
      set W_F := wdeg wY F0
      have hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2 := by
        have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
        rw [div_le_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 2)]
        have h1 : W_F ≤ 26689499 := by simpa [W0, A] using hWF_le
        have h2 : (W_F : ℚ) ≤ 26689499 := by exact_mod_cast h1
        norm_num [wY]; linarith
      have hirr_rat : Irreducible (liftCRat (cLiftZ F0)) := irreducible_liftCRat_cLiftZ hirr
      have hdeg_lift : (cLiftZ F0).natDegree = F0.natDegree := cLiftZ_natDegree F0
      have hwdeg_lift : wdeg wY (cLiftZ F0) = W_F := cLiftZ_wdeg
      -- Helper to lift local shift exactness from `Fld` to `Fld[Z]` constants!
      have hlocal_lift : ∀ {d : ℕ} (f_coord : KerDIdx wY W_F d → Fld) (i : Idx),
          (∑ e : KerDIdx wY W_F d, locC (Polynomial.C (f_coord e)) * kerDLocalPoly (Polynomial.C (BinaryIRSProfile.domain i)) (Polynomial.C (u i)) e.1) =
          (∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1).map
            (Polynomial.mapRingHom (Polynomial.mapRingHom Polynomial.C)) := by
        intro d f_coord i
        let ψ : LocalPoly Fld →+* LocalPoly (Polynomial Fld) :=
          Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.C : Fld →+* Polynomial Fld)))
        change _ = ψ _
        rw [map_sum]
        apply Finset.sum_congr rfl; intro e _
        rw [map_mul]
        exact congrArg₂ (· * ·) (by unfold ψ locC; simp [Polynomial.map_C])
          (mapC_kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1).symm
      have htw_lift : ∀ {d : ℕ} (f_coord : KerDIdx wY W_F d → Fld) (i : Idx) (k_i : ℕ),
          (twOrdGE (∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1) k_i →
            twOrdGE (∑ e : KerDIdx wY W_F d, locC (Polynomial.C (f_coord e)) * kerDLocalPoly (Polynomial.C (BinaryIRSProfile.domain i)) (Polynomial.C (u i)) e.1) k_i) ∧
          ((∃ p q, p + q = k_i ∧ twCoeff (∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1) p q ≠ 0) →
            ∃ p q, p + q = k_i ∧ twCoeff (∑ e : KerDIdx wY W_F d, locC (Polynomial.C (f_coord e)) * kerDLocalPoly (Polynomial.C (BinaryIRSProfile.domain i)) (Polynomial.C (u i)) e.1) p q ≠ 0) := by
        intro d f_coord i k_i
        rw [hlocal_lift]
        constructor
        · intro h p q hpq
          simp only [twCoeff, Polynomial.coeff_map, Polynomial.coe_mapRingHom]
          change Polynomial.map Polynomial.C (twCoeff _ p q) = 0
          rw [h p q hpq, Polynomial.map_zero]
        · rintro ⟨p, q, hpq, hne⟩
          refine ⟨p, q, hpq, ?_⟩
          simp only [twCoeff, Polynomial.coeff_map, Polynomial.coe_mapRingHom]
          exact (Polynomial.map_ne_zero_iff Polynomial.C_injective).mpr hne
      have hcard_cap : ∀ {d m s : ℕ}, 1 ≤ d → d ≤ 2 → m ≤ 3000 → s ≤ 300 →
          (d * (2 * A * m - 1) + s * (W_F - d * (wY - 1))) / wY ≤ 100000 := by
        intro d m s hd1' hd2' hm3 hs3
        have hW1 : W_F ≤ 26689499 := by simpa [W0, A] using hWF_le
        have hnum : d * (2 * A * m - 1) + s * (W_F - d * (wY - 1)) ≤ 2 * (2 * A * 3000) + 300 * 26689499 := by
          have h1 : d * (2 * A * m - 1) ≤ 2 * (2 * A * 3000) :=
            Nat.mul_le_mul hd2' ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left (2 * A) hm3))
          have h2 : s * (W_F - d * (wY - 1)) ≤ 300 * 26689499 :=
            Nat.mul_le_mul hs3 (by omega)
          omega
        have hdiv : (2 * (2 * A * 3000) + 300 * 26689499) / wY ≤ 100000 := by norm_num [A, wY]
        exact (Nat.div_le_div_right hnum).trans hdiv
      rcases (show F0.natDegree = 1 ∨ F0.natDegree = 2 by omega) with hdF1 | hdF2
      · -- Subcase `dF = 1`:
        obtain ⟨f_coord, hF0_eq, _⟩ := (mem_kerD_iff_exists_unique_coords (wY := wY) (W := W_F) (s := 1) (by norm_num [wY]) F0).mp ⟨hDF, le_of_eq hdF1, le_rfl⟩
        have hf1_ne : F0.coeff 1 ≠ 0 := by
          rw [← hdF1, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
        have hWF_lo : 1 * (wY - 1) ≤ W_F := by
          have := wdegBi_coeff_le_of_wdeg (le_rfl : wdeg wY F0 ≤ W_F) 1 hf1_ne; omega
        let Loc (i : Idx) : LocalPoly Fld := ∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1
        have hLoc_ne : ∀ i : Idx, Loc i ≠ 0 := fun i =>
          localShift_ne_zero (BinaryIRSProfile.domain i) (u i) f_coord (hF0_eq ▸ hirr.ne_zero)
        let k : Idx → ℕ := fun i => exactTwOrd (Loc i)
        have hvan : ∀ i, twOrdGE (Loc i) (k i) := fun i => twOrdGE_exactTwOrd (hLoc_ne i)
        have hfinish1 : ∀ (m s : ℕ), 0 < m → m ≤ 3000 → 1 ≤ s → s ≤ 300 →
            (0 : ℚ) < vquotLbQ 1 m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 1 m s (k i)) / (N : ℚ) →
            TF.card ≤ 100000 := fun m s hm hm3 hs hs3 hsurp => by
          have hlift_eq : ∑ e : KerDIdx wY W_F 1, cC (Polynomial.C (f_coord e)) * kerDBasisPoly e.1 = cLiftZ F0 := by
            rw [← cLiftZ_sum_kerDBasisPoly, ← hF0_eq]
          have hcard := card_le_of_degZ_zero_surplus u le_rfl hs hm hWF_lo f_coord
            (by rw [hlift_eq]; exact hirr_rat) (by rw [hlift_eq, hdeg_lift, hdF1])
            (by rw [hlift_eq, hwdeg_lift]) k
            (fun i => ⟨(htw_lift f_coord i (k i)).1 (hvan i), fun _ => (htw_lift f_coord i (k i)).2 (exists_twCoeff_exactTwOrd (hLoc_ne i))⟩)
            hsurp TF (fun P hP => by
              have hPT := (Finset.mem_filter.mp hP).1
              exact ⟨(hT P hPT).1, (hT P hPT).2, by rw [← hF0_eq]; exact (Finset.mem_filter.mp hP).2⟩)
          exact hcard.trans (hcard_cap le_rfl (by omega) hm3 hs3)
        by_cases hemp : TF.Nonempty
        · obtain ⟨P0, hP0⟩ := hemp
          have hP0T := (Finset.mem_filter.mp hP0).1
          have hP0van := (Finset.mem_filter.mp hP0).2
          have hRes_ne_fn : 2 ≤ (F0.coeff 1).natDegree →
              Polynomial.resultant (F0.coeff 0) (F0.coeff 1) (F0.coeff 0).natDegree (F0.coeff 1).natDegree ≠ 0 := by
            intro h2
            have hd1_lift : 1 ≤ ((cLiftZ F0).coeff 1).natDegree := by
              have : ((cLiftZ F0).coeff 1).natDegree = (F0.coeff 1).natDegree := by
                unfold cLiftZ; simp only [Polynomial.coeff_map]
                exact Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective _ Polynomial.C_injective) _
              omega
            have ⟨_, _, hresZ⟩ := resY_f0_f1_ne_zero_of_irred_deg1 (cLiftZ F0) hirr_rat (by rw [hdeg_lift, hdF1]) hd1_lift
            intro h0; apply hresZ
            have hmap : Polynomial.resultant ((cLiftZ F0).coeff 0) ((cLiftZ F0).coeff 1)
                ((cLiftZ F0).coeff 0).natDegree ((cLiftZ F0).coeff 1).natDegree =
                (Polynomial.resultant (F0.coeff 0) (F0.coeff 1) (F0.coeff 0).natDegree (F0.coeff 1).natDegree).map Polynomial.C := by
              have hd0c : ((cLiftZ F0).coeff 0).natDegree = (F0.coeff 0).natDegree := by
                unfold cLiftZ; simp only [Polynomial.coeff_map]
                exact Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective _ Polynomial.C_injective) _
              have hd1c : ((cLiftZ F0).coeff 1).natDegree = (F0.coeff 1).natDegree := by
                unfold cLiftZ; simp only [Polynomial.coeff_map]
                exact Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective _ Polynomial.C_injective) _
              have hc0 : (cLiftZ F0).coeff 0 = (F0.coeff 0).map (Polynomial.mapRingHom Polynomial.C) := by
                unfold cLiftZ; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
              have hc1 : (cLiftZ F0).coeff 1 = (F0.coeff 1).map (Polynomial.mapRingHom Polynomial.C) := by
                unfold cLiftZ; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
              rw [hd0c, hd1c, hc0, hc1]
              exact Polynomial.resultant_map_map (F0.coeff 0) (F0.coeff 1)
                (F0.coeff 0).natDegree (F0.coeff 1).natDegree (Polynomial.mapRingHom Polynomial.C)
            rw [hmap, h0, Polynomial.map_zero]
          by_cases hT4 : (F0.coeff 1).natDegree = 4 ∧ (F0.coeff 0).natDegree ≤ 5 ∧ (W_F : ℚ) / (wY : ℚ) < 28 / 5
          · obtain ⟨hd1_4, hd0_5, hWF_28⟩ := hT4
            have hWF_5lo : 5 * wY ≤ W_F + 1 := by
              have hw1 : wdegBi wY (F0.coeff 1) + (wY - 1) ≤ W_F := by
                simpa only [one_mul] using wdegBi_coeff_le_of_wdeg (le_rfl : wdeg wY F0 ≤ W_F) 1 hf1_ne
              have h1 := wdegBi_ge_natDegree_mul wY (F0.coeff 1) hf1_ne
              rw [hd1_4] at h1
              have hw : 1 ≤ wY := by norm_num [wY]
              omega
            have hWF_6hi : W_F + 1 < 6 * wY := by
              have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
              have hmul : (W_F : ℚ) * 5 < 28 * (wY : ℚ) := by
                have := (div_lt_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 5)).mp hWF_28; linarith
              have hnat : W_F * 5 < 28 * wY := by exact_mod_cast hmul
              have hw : wY = 1048575 := rfl; omega
            have hRes54 : Polynomial.resultant (F0.coeff 0) (F0.coeff 1) 5 4 ≠ 0 := by
              have hres := hRes_ne_fn (by omega); rw [hd1_4] at hres
              exact resultant_54_ne_zero hd0_5 hd1_4 hf1_ne hres
            exact hard u F0 W_F f_coord hF0_eq hirr hDF hdF1 rfl hd1_4 hd0_5 hWF_5lo hWF_6hi hWF_28 hRes54 TF
              (fun P hp => (hT P (Finset.mem_filter.mp hp).1).1)
              (fun P hp => (hT P (Finset.mem_filter.mp hp).1).2)
              (fun P hp => (Finset.mem_filter.mp hp).2)
          · -- Table 1 scalar case!
            obtain ⟨c, _, _, hmpos, hm3, hs3, _, _, hsurp, hcap1, _⟩ :=
              t1_surplus_of_point f_coord u k hvan P0 (hT P0 hP0T).1
                (Finset.univ.filter fun i : Idx => P0.eval (BinaryIRSProfile.domain i) = u i)
                (hT P0 hP0T).2 (fun i hi => (Finset.mem_filter.mp hi).2)
                (by rw [← hF0_eq]; exact hP0van) (by rw [← hF0_eq]; exact hf1_ne) hWF_hi
                (by rw [← hF0_eq]; exact hRes_ne_fn) (by rw [← hF0_eq]; exact hT4)
            have hpars : 1 ≤ c.s ∧ 0 < c.δNum ∧ 0 < c.δDen := by
              unfold checkCapWitness at hcap1
              by_contra hbadp; push Not at hbadp
              have hif : (c.m == 0 || c.s < 1 || c.cHiDen == 0 || c.δNum == 0 || c.δDen == 0 || (1 : ℕ) == 0) = true := by
                rcases lt_or_ge c.s 1 with h1 | h1
                · simp [h1]
                · rcases Nat.eq_zero_or_pos c.δNum with h2 | h2
                  · simp [h2]
                  · have h3 : c.δDen = 0 := by have := hbadp h1 h2; omega
                    simp [h3]
              rw [if_pos hif] at hcap1; cases hcap1
            have hpos : (0 : ℚ) < (c.δNum : ℚ) / (c.δDen : ℚ) := div_pos (by exact_mod_cast hpars.2.1) (by exact_mod_cast hpars.2.2)
            exact hfinish1 c.m c.s hmpos hm3 hpars.1 hs3 (hpos.trans hsurp)
        · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty]; omega
      · -- Subcase `dF = 2`:
        by_cases hf1 : F0.coeff 1 = 0
        · exact False.elim (not_irred_kerD2_coeff1_zero hirr hDF hdF2 hf1)
        · obtain ⟨f_coord, hF0_eq, _⟩ := (mem_kerD_iff_exists_unique_coords (wY := wY) (W := W_F) (s := 2) (by norm_num [wY]) F0).mp ⟨hDF, le_of_eq hdF2, le_rfl⟩
          have hf2_ne : F0.coeff 2 ≠ 0 := by
            rw [← hdF2, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
          have hWF_lo : 2 * (wY - 1) ≤ W_F :=
            (Nat.le_add_left _ _).trans (wdegBi_coeff_le_of_wdeg (le_rfl : wdeg wY F0 ≤ W_F) 2 hf2_ne)
          have hd1_le25 : (F0.coeff 1).natDegree ≤ 25 := by
            have hw1 := wdegBi_le_of_wdeg_coeff hWF_le 1
            have h1 := wdegBi_ge_natDegree_mul wY (F0.coeff 1) hf1
            have hle := h1.trans hw1
            have hW0 : W0 = 26689499 := by norm_num [W0, A]
            have hw : wY = 1048575 := rfl
            rw [hw, hW0] at hle; omega
          have hd2_le25 : (F0.coeff 2).natDegree ≤ 25 := by
            have hw2 := wdegBi_le_of_wdeg_coeff hWF_le 2
            have h1 := wdegBi_ge_natDegree_mul wY (F0.coeff 2) hf2_ne
            have hle := h1.trans hw2
            have hW0 : W0 = 26689499 := by norm_num [W0, A]
            have hw : wY = 1048575 := rfl
            rw [hw, hW0] at hle; omega
          let TF1 := TF.filter fun P => (F0.coeff 1).eval P = 0
          let TF2 := TF.filter fun P => (F0.coeff 2).eval P = 0
          let TF_cl := TF.filter fun P => (F0.coeff 1).eval P ≠ 0 ∧ (F0.coeff 2).eval P ≠ 0
          have hTF1 : TF1.card ≤ 25 := (card_roots_biPoly_le hf1 TF1 (fun P hP => (Finset.mem_filter.mp hP).2)).trans hd1_le25
          have hTF2 : TF2.card ≤ 25 := (card_roots_biPoly_le hf2_ne TF2 (fun P hP => (Finset.mem_filter.mp hP).2)).trans hd2_le25
          have hTF_split : TF.card ≤ TF_cl.card + 50 := by
            have hsub : TF ⊆ TF_cl ∪ (TF1 ∪ TF2) := by
              intro P hP; simp only [Finset.mem_union, TF_cl, TF1, TF2, Finset.mem_filter]
              by_cases h1 : (F0.coeff 1).eval P = 0
              · exact Or.inr (Or.inl ⟨hP, h1⟩)
              · by_cases h2 : (F0.coeff 2).eval P = 0
                · exact Or.inr (Or.inr ⟨hP, h2⟩)
                · exact Or.inl ⟨hP, h1, h2⟩
            have hle := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
              (Nat.add_le_add_left (Finset.card_union_le _ _) _))
            omega
          have hcl_card : TF_cl.card ≤ 99950 := by
            by_cases hemp : TF_cl.Nonempty
            · obtain ⟨P0, hP0⟩ := hemp
              obtain ⟨hP0F, hP01, hP02⟩ := Finset.mem_filter.mp hP0
              have hP0T := (Finset.mem_filter.mp hP0F).1
              let Loc (i : Idx) : LocalPoly Fld := ∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1
              have hLoc_ne : ∀ i : Idx, Loc i ≠ 0 := fun i =>
                localShift_ne_zero (BinaryIRSProfile.domain i) (u i) f_coord (hF0_eq ▸ hirr.ne_zero)
              let k : Idx → ℕ := fun i => exactTwOrd (Loc i)
              have hvan : ∀ i, twOrdGE (Loc i) (k i) := fun i => twOrdGE_exactTwOrd (hLoc_ne i)
              have hcop_all : ∀ p : Polynomial (RatFunc Fld),
                  p ∣ (F0.coeff 0).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
                  p ∣ (F0.coeff 1).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
                  p ∣ (F0.coeff 2).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
                  IsUnit p := fun p hp0 hp1 hp2 =>
                no_common_irred_factor_of_irred hirr (by omega) p fun k' => by
                  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ 3 ≤ k' by omega) with rfl | rfl | rfl | hk3
                  · exact hp0
                  · exact hp1
                  · exact hp2
                  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.map_zero]; exact dvd_zero _
              obtain ⟨m, s, _, _, δN, δD, _, hm, hm3, hs, hs3, _, hδN, hδD, _, hsurp, _⟩ :=
                t23_surplus_of_point f_coord u k hvan P0 (hT P0 hP0T).1
                  (Finset.univ.filter fun i : Idx => P0.eval (BinaryIRSProfile.domain i) = u i)
                  (hT P0 hP0T).2 (fun i hi => (Finset.mem_filter.mp hi).2)
                  (by rw [← hF0_eq]; exact hf1) (by rw [← hF0_eq]; exact hf2_ne)
                  (by rw [← hF0_eq]; exact hP01) (by rw [← hF0_eq]; exact hP02)
                  hWF_hi (by rw [← hF0_eq]; exact hcop_all)
              have hlift_eq : ∑ e : KerDIdx wY W_F 2, cC (Polynomial.C (f_coord e)) * kerDBasisPoly e.1 = cLiftZ F0 := by
                rw [← cLiftZ_sum_kerDBasisPoly, ← hF0_eq]
              have hpos : (0 : ℚ) < (δN : ℚ) / (δD : ℚ) := div_pos (by exact_mod_cast hδN) (by exact_mod_cast hδD)
              have hcard := card_le_of_degZ_zero_surplus u (by omega) hs hm hWF_lo f_coord
                (by rw [hlift_eq]; exact hirr_rat) (by rw [hlift_eq, hdeg_lift, hdF2])
                (by rw [hlift_eq, hwdeg_lift]) k
                (fun i => ⟨(htw_lift f_coord i (k i)).1 (hvan i), fun _ => (htw_lift f_coord i (k i)).2 (exists_twCoeff_exactTwOrd (hLoc_ne i))⟩)
                (hpos.trans hsurp) TF_cl (fun P hP => by
                  have hPF := (Finset.mem_filter.mp hP).1
                  have hPT := (Finset.mem_filter.mp hPF).1
                  exact ⟨(hT P hPT).1, (hT P hPT).2, by rw [← hF0_eq]; exact (Finset.mem_filter.mp hPF).2⟩)
              have hW1 : W_F ≤ 26689499 := by simpa [W0, A] using hWF_le
              have hnum : 2 * (2 * A * m - 1) + s * (W_F - 2 * (wY - 1)) ≤ 2 * (2 * A * 3000) + 300 * 26689499 := by
                have h1 : 2 * (2 * A * m - 1) ≤ 2 * (2 * A * 3000) :=
                  Nat.mul_le_mul_left 2 ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left (2 * A) hm3))
                have h2 : s * (W_F - 2 * (wY - 1)) ≤ 300 * 26689499 :=
                  Nat.mul_le_mul hs3 (by omega)
                omega
              have hdiv : (2 * (2 * A * 3000) + 300 * 26689499) / wY ≤ 99950 := by norm_num [A, wY]
              exact hcard.trans ((Nat.div_le_div_right hnum).trans hdiv)
            · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty]; omega
          omega
  -- Combine `G0` (`≤ 25`) + at most `2` factors of `deg_R ≥ 1` (`≤ 2 * 100000`)!
  have hG0_card : (T.filter fun P => G0.eval P = 0).card ≤ 25 :=
    (card_roots_biPoly_le hG0_ne _ (fun P hP => (Finset.mem_filter.mp hP).2)).trans hG0_deg
  have hbi_card : (facs1.toFinset.biUnion (fun F0 => T.filter fun P => evalContact F0 P = 0)).card ≤ 200000 := by
    calc _ ≤ ∑ F0 ∈ facs1.toFinset, (T.filter fun P => evalContact F0 P = 0).card := Finset.card_biUnion_le
      _ ≤ ∑ _F0 ∈ facs1.toFinset, 100000 := Finset.sum_le_sum hfac_bound
      _ = facs1.toFinset.card * 100000 := by simp
      _ ≤ facs1.card * 100000 := Nat.mul_le_mul_right _ (Multiset.toFinset_card_le _)
      _ ≤ 2 * 100000 := Nat.mul_le_mul_right _ hfacs1_card
      _ = 200000 := by norm_num
  have htot := (Finset.card_le_card hT_cover).trans (Finset.card_union_le _ _)
  omega


#print axioms scalar_of_hard
end ProximityPrize.SubmissionBinaryLower.B6402ScalarCases
