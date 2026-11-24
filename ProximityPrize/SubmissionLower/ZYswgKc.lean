import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CU
import ProximityPrize.SubmissionLower.ZrIiE0d
import ProximityPrize.SubmissionLower.A
import ProximityPrize.SubmissionLower.BJ
import ProximityPrize.SubmissionLower.E7
import ProximityPrize.SubmissionLower.D6
import ProximityPrize.SubmissionLower.D9
import ProximityPrize.SubmissionLower.Z1sUWDe
set_option Elab.async false
open _root_ renaming Fin.sum_univ_eq_sum_range → zdx, Finset → zJe, Finset.card_univ → zDb, Finset.mem_insert_of_mem → zJN, Finset.mul_sum → zxw, Finset.prod_eq_zero → zue, Finset.prod_insert → zqX, Finset.prod_mul_distrib → zeY, Finset.range → z4x, Finset.sum_congr → zUo, Finset.sum_const → z7l, Finset.sum_le_sum → zQk, Finsupp.finite_of_degree_le → z31, Finsupp.sum_mapDomain_index → z2k, Fintype → z85, Fintype.card → zhP, Fintype.linearCombination → z3d, Fintype.ofFinite → zQs, Fintype.sum_sigma → zla, Function.Injective → zq4, IsFractionRing.injective → zxb, LinearIndependent → z14, Matrix → z30, Matrix.det_apply' → z00, Matrix.det_transpose → zgP, Matrix.submatrix_apply → z6T, MvPolynomial.X → z9v, Nat.add_sub_cancel → z2h, Nat.add_sub_of_le → zp3, Nat.cast_sub → zjK, Nat.mul_comm → z5A, Nat.mul_le_mul_left → zBI, Polynomial.X → z7y, Polynomial.natDegree_mul_le → zm2
set_option maxHeartbeats 2500000
section
set_option autoImplicit true
namespace qnnEPee
noncomputable section
open aR (ao)
open xE (Flag)
open akL (Jp MI aWa Oq)
open MvPolynomial
def relaxed (F : Flag) : Flag := { F with lower := 0 }
def tailColumns (F : Flag) : zJe Jp :=
  (aWa (relaxed F)).filter fun e => F.order ≤ (e.weight Oq : ℤ)
abbrev Tail (F : Flag) := ↥(tailColumns F)
def coord : Fin 4 → MI :=
  ![z9v 0, z9v 0 - z9v 1,
    z9v 0 - z9v 1 + z9v 2,
    z9v 0 - z9v 1 + z9v 2 - z9v 3]
def tailMonomial (e : Jp) : MI := ∏ i, coord i ^ e i
def tailMap (F : Flag) : (Tail F → ao) →ₗ[ao] MI :=
  z3d ao fun e => tailMonomial e.val
def debitMap (F : Flag) : (Tail F → ao) →ₗ[ao] MI :=
  (weightedTruncation Oq F.lower.toNat).comp (tailMap F)
def momentColumns (F : Flag) : zJe Jp :=
  akL.adw (F.lower - 1) (F.lower - 1)
def boxU (F : Flag) : ℤ := max 0 (min F.degree F.upper - (F.order + 2) / 3 + 1)
def boxV (F : Flag) : ℤ :=
  max 0 (min F.degree (F.upper / 2) - max 0 ((F.order - F.degree + 1) / 2) + 1)
def boxW (F : Flag) : ℤ := max 0 (min (min F.cap F.degree) (F.upper - F.order) + 1)
def reducedColumns (F : Flag) : zJe Jp :=
  (momentColumns F).filter fun e =>
    (e 1 : ℤ) < boxU F ∧ (e 2 : ℤ) < boxV F ∧ (e 3 : ℤ) < boxW F
def coordU (e : Jp) : ℕ := e 1 + e 2 + e 3
def coordV (e : Jp) : ℕ := e 2 + e 3
def coordW (e : Jp) : ℕ := e 3
def momentValue (a e : Jp) : ao :=
  (coordU e : ao) ^ a 1 * (coordV e : ao) ^ a 2 * (coordW e : ao) ^ a 3
def momentMap (F : Flag) (s : zJe Jp) : (Tail F → ao) →ₗ[ao] (↥s → ao) :=
  z3d ao fun e a => momentValue a.val e.val
end
end qnnEPee
end
section
set_option autoImplicit true
namespace qqJLTVc
noncomputable section
open aR (Shape)
open B8 (lS)
open agM (a1Z Vw diagonal)
open NU (hvol aD azm)
open private alt aCd bT8 DB bB8 bB9 from ProximityPrize.SubmissionLower.BI
open private diff translate ayr ahP dWL dWK dWS dd1 gqJ from ProximityPrize.SubmissionLower.CE
private def residual (d : ℚ × ℚ × ℚ) (x : ℚ × ℚ × ℚ) : ℚ :=
  diff d hvol x - horizontalDerivative d x
set_option maxRecDepth 4096 in
private theorem residual_third (d a b c : ℚ × ℚ × ℚ) :
    diff c (diff b (diff a (residual d))) = 0 := by
  funext x
  simp only [residual, diff, horizontalDerivative, hvol, Prod.fst_add, Prod.snd_add, Pi.zero_apply]
  ring
private theorem residual_fourth (d : Shape) (r : ℚ) (a b c e x : Shape × ℕ) :
    DB e (DB c (DB b (DB a (ahP r (residual (aD d)))))) x = 0 := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases c with ⟨c, hc⟩
  rcases e with ⟨e, he⟩
  simp only [dWL, bB8, bB9, dWK, dWS,
    residual_third]
  have hz (a : ℚ × ℚ × ℚ) : translate a 0 = 0 := rfl
  simp [ayr, ahP, hz, diff]
private theorem residual_volume (d : Shape) :
    (fun x => volumeDifference d x - volumeDerivative d x) =
      fun x => (7 / 90) * ahP 0 (residual (aD d)) x +
        (32 / 90) * ahP (1 / 4) (residual (aD d)) x +
        (12 / 90) * ahP (1 / 2) (residual (aD d)) x +
        (32 / 90) * ahP (3 / 4) (residual (aD d)) x +
        (7 / 90) * ahP 1 (residual (aD d)) x := by
  funext x
  simp only [volumeDifference, azm, volumeDerivative, residual, dd1,
    gqJ, ahP, diff, show (a1Z x (d, 0)).2 = x.2 by simp [a1Z]]
  ring
theorem derivative_differences (B : lS) (d : Shape) :
    (∑ J ∈ slots.powerset, (-1 : ℚ) ^ (slots.card - J.card) *
      volumeDerivative d (Vw B (diagonal J))) =
    ∑ J ∈ slots.powerset, (-1 : ℚ) ^ (slots.card - J.card) *
      volumeDifference d (Vw B (diagonal J)) := by
  symm
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  change alt B slots (fun x => volumeDifference d x - volumeDerivative d x) = _
  unfold slots
  rw [residual_volume, aCd _ (by decide), aCd _ (by decide),
    aCd _ (by decide), show ({4} : Finset (Fin 5)) = insert 4 ∅ from rfl,
    aCd _ (by decide), bT8]
  simp only [bB8, bB9, residual_fourth, mul_zero, add_zero]
end
end qqJLTVc
end
section
set_option autoImplicit true
namespace qqJLTVc
noncomputable section
open aR (Shape aO)
open B8 (bF)
open P6_6 (wP)
open NU (agJ aD direction ic azm hvol)
open private DB bB8 bB9 from ProximityPrize.SubmissionLower.BI
open private polar cb7 btK c4r glC dju ahP from ProximityPrize.SubmissionLower.CE
open private bwo bwp from ProximityPrize.SubmissionLower.T
private def quarterCap (k : ℕ) (a : Shape × ℕ) : Shape :=
  let w := k * a.2
  ⟨4*a.1.b - w, 4*a.1.j - 4*w, 4*a.1.t - 2*w⟩
private theorem quarter_chamber {k : ℕ} (hk : k ≤ 4) {a : Shape × ℕ} (ha : agJ a) :
    bF (quarterCap k a) ∧ aD (quarterCap k a) = (4 : ℚ) • ic (k / 4 : ℚ) a := by
  obtain ⟨⟨hb, hj⟩, ht⟩ := ha
  have hw := Nat.mul_le_mul_right a.2 hk
  have htw := zBI 4 ht
  rw [z5A 4 (2 * a.2), Nat.mul_assoc, z5A a.2 4] at htw
  let w := k * a.2
  change w ≤ 4 * a.2 at hw
  have h₁ : w ≤ 4 * a.1.b := by omega
  have h₂ : 4*w ≤ 4 * a.1.j := by omega
  have h₃ : 2*w ≤ 4 * a.1.t := by omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change 4*a.1.j - 4*w ≤ 4*a.1.b - w
    omega
  · change 3*(4*a.1.t - 2*w) ≤ 4*a.1.j - 4*w
    omega
  · change aD (⟨4*a.1.b-w, 4*a.1.j-4*w, 4*a.1.t-2*w⟩ : Shape) = _
    apply Prod.ext
    · change ((4 * a.1.b - w : ℕ) : ℚ) = 4 * ((a.1.b : ℚ) - ((k : ℚ) / 4 * a.2) * 1)
      push_cast [zjK h₁, w]
      ring
    · apply Prod.ext
      · change ((4 * a.1.j - 4*w : ℕ) : ℚ) = 4 * ((a.1.j : ℚ) - ((k : ℚ) / 4 * a.2) * 4)
        push_cast [zjK h₂, w]
        ring
      · change ((4 * a.1.t - 2*w : ℕ) : ℚ) = 4 * ((a.1.t : ℚ) - ((k : ℚ) / 4 * a.2) * 2)
        push_cast [zjK h₃, w]
        ring
private theorem polar_scale (p q a b : ℚ × ℚ × ℚ) (n : ℚ) :
    polar p q a (n • b) = n * polar p q a b := by
  change cb7 p q a (n • b) = n * cb7 p q a b
  rw [map_rat_smul, smul_eq_mul]
private theorem sample_polar_nonneg (d q : Shape) (hq : bF q)
    {k : ℕ} (hk : k ≤ 4) {a b : Shape × ℕ} (ha : agJ a) (hb : agJ b) :
    0 ≤ polar (aD d) (aD q) (ic (k / 4 : ℚ) a) (ic (k / 4 : ℚ) b) := by
  obtain ⟨hA, eA⟩ := quarter_chamber hk ha
  obtain ⟨hB, eB⟩ := quarter_chamber hk hb
  have h : (0 : ℚ) ≤ (wP d q (quarterCap k a) (quarterCap k b) : ℚ) := by
    exact_mod_cast (bwp d q _ _ hq hA hB)
  rw [← c4r, eA, eB, polar_scale, btK, polar_scale, ← btK] at h
  linarith only [h]
private theorem sample_nonneg (d q g a b : Shape) (u v : ℕ) (hq : bF q)
    (hg : agJ (g, 1)) (ha : agJ (a, u)) (hb : agJ (b, v))
    {k : ℕ} (hk : k ≤ 4) (x : Shape × ℕ) :
    0 ≤ DB (b, v) (DB (a, u) (DB (g, 1) (DB (q, 0)
      (DB (d, 0) (ahP (k / 4 : ℚ) hvol))))) x := by
  rw [glC]
  exact add_nonneg
    (add_nonneg (sample_polar_nonneg d q hq hk ha hb)
      (mul_nonneg (Nat.cast_nonneg _) (sample_polar_nonneg d q hq hk hg hb)))
    (mul_nonneg (Nat.cast_nonneg _) (sample_polar_nonneg d q hq hk hg ha))
theorem signed_volume_differences (d q g a b : Shape) (u v : ℕ) (x : Shape × ℕ) :
    DB (b, v) (DB (a, u) (DB (g, 1) (DB (q, 0)
      (DB (d, 0) azm)))) x = signedVolume d q g a b u v := by
  rw [dju]
  simp only [show direction = aD (⟨1, 4, 2⟩ : Shape) from rfl, c4r, signedVolume]
private theorem signed_volume_nonneg (d q g a b : Shape) (u v : ℕ) (hq : bF q)
    (hg : agJ (g, 1)) (ha : agJ (a, u)) (hb : agJ (b, v)) :
    0 ≤ signedVolume d q g a b u v := by
  let x : Shape × ℕ := (⟨0, 0, 0⟩, 0)
  have hvols : azm = fun x => (7 / 90) * ahP 0 hvol x +
      (32 / 90) * ahP (1 / 4) hvol x + (12 / 90) * ahP (1 / 2) hvol x +
      (32 / 90) * ahP (3 / 4) hvol x + (7 / 90) * ahP 1 hvol x := by
    funext x
    unfold azm ahP
    ring
  rw [← signed_volume_differences d q g a b u v x, hvols]
  simp only [bB8, bB9]
  have h0 := sample_nonneg d q g a b u v hq hg ha hb (k := 0) (by decide) x
  have h1 := sample_nonneg d q g a b u v hq hg ha hb (k := 1) (by decide) x
  have h2 := sample_nonneg d q g a b u v hq hg ha hb (k := 2) (by decide) x
  have h3 := sample_nonneg d q g a b u v hq hg ha hb (k := 3) (by decide) x
  have h4 := sample_nonneg d q g a b u v hq hg ha hb (k := 4) (by decide) x
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_div, div_self (by decide : (4 : ℚ) ≠ 0),
    show (2 : ℚ)/4 = 1/2 by norm_num] at h0 h1 h2 h3 h4
  positivity
theorem signed_volume_mono {d r q g a b : Shape} {u v : ℕ} (hr : aO d r) (hq : bF q)
    (hg : agJ (g, 1)) (ha : agJ (a, u)) (hb : agJ (b, v)) :
    signedVolume d q g a b u v ≤ signedVolume r q g a b u v := by
  let e : Shape := ⟨r.b - d.b, r.j - d.j, r.t - d.t⟩
  obtain ⟨hB, hJ, hT⟩ := hr
  have he : d.plus e = r := by
    cases r
    simp [e, Shape.plus, zp3 hB, zp3 hJ, zp3 hT]
  have hadd : signedVolume (d.plus e) q g a b u v =
      signedVolume d q g a b u v + signedVolume e q g a b u v := by
    have h (x y : Shape) : wP (d.plus e) q x y =
        wP d q x y + wP e q x y := bwo d e q x y
    simp only [signedVolume, h, Int.cast_add]
    ring
  rw [← he, hadd]
  exact le_add_of_nonneg_right (signed_volume_nonneg e q g a b u v hq hg ha hb)
end
end qqJLTVc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qs56oUd
noncomputable section
open Polynomial
open aR (ao af Shape aO shape iH)
open dN (GeoJets bC separant su oA Invariant kC)
open wH (Gh fW)
open Rl (Ve aqk He acp)
open P6_6 (bf gZ)
open P6_6_6 (rH Kq anZ)
def boc (x : Shape) : ℕ :=
  iH x.iU Kq (anZ x) (rH x)
def bnI (x : Shape) : ℕ :=
  iH x.iU Kq (anZ x) x.iU
def vU (f : af 4) : af 4 := su f bf
structure bbl (f : af 4) (D q : af 3) : Prop where
  ne_zero : q ≠ 0
  divides : q ∣ D
  caps : Gh q Kq.b Kq.j
  reduced : Squarefree (fW q)
  proper : IsRelPrime (bC f) (bC (He q))
  roots : ∀ S : ao[X], aR.cK D S = 0 → aR.cK q S = 0
  a4g : aO (shape (acp q)) ⟨Kq.b, Kq.j + 1, 1⟩
  simple : ∀ aI, (h : aqk f q aI) → aI.height = 2 ∧
    oA (kC f (He q)) aI h.minimal.isPrime = 1
  invariant : ∀ aI, aqk f q aI →
    bC (acp q) ∈ aI → Invariant f aI
structure Li (f : af 4) where
  denom : af 4
  Fr : Fin bf → af 4
  test : af 4
  denom_box : aO (shape denom) (rH (shape f))
  numer_box : ∀ i, aO (shape (Fr i)) (rH (shape f))
  aX4 : aO (shape test) (rH (shape f))
  test_iff : ∀ (aI : Ideal GeoJets), aI.IsPrime → bC f ∈ aI →
    bC (separant f) ∉ aI →
    (bC test ∈ aI ↔ bC (vU f) ∈ aI)
  ar5 : ∀ (L : Type) [Field L] [Algebra ao L] (S : L[X]),
    S.natDegree ≤ gZ → Ve f S = 0 →
    Ve (separant f) S ≠ 0 →
    Ve denom S ≠ 0 ∧ Ve test S = 0 ∧
      ∀ i, Ve (Fr i) S = Ve denom S * C (S.coeff i.val)
end
end qs56oUd
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qzTRNDe
noncomputable section
open Polynomial aR wH lB Tx aKu XU
open P6_6_6 (ahv IG)
open scoped BigOperators
open private cHe deY from ProximityPrize.SubmissionLower.CU
open private cXO cXN from ProximityPrize.SubmissionLower.J
open private dgl dgm c0w from ProximityPrize.SubmissionLower.J
structure bQ6 (f : af 4) (P Q : af 3) (r : PrimeSpectrum gQ) : Prop where
  component : r.asIdeal ∈ (xJ f P Q).minimalPrimes
  height : r.asIdeal.height = 3
  heavy : (↑ahv : ℕ∞) ≤ ajK r (xJ f P Q)
  finite : ajK r (xJ f P Q) < ⊤
theorem ewb (f : af 4) (P Q : af 3) (S : ao[X])
    (hf : Dd f S) (hcurve : P6_6_6.bac P Q (Ud S)) :
    ∃ r : PrimeSpectrum gQ, bQ6 f P Q r ∧
      r.asIdeal < Ol (zq S) := by
  obtain ⟨q, hmin, hht, hy, hweight, _⟩ := hcurve
  obtain ⟨p, hover, hr, hry⟩ := d3W hf hmin hy
  let r := PrimeSpectrum.comap (qR f) p
  have hc : r.asIdeal.comap aVJ = q.asIdeal := by
    change (p.asIdeal.comap (qR f)).comap aVJ = _
    rw [Ideal.comap_comap, bWW]
    exact hover.over.symm
  obtain ⟨ht, hproper⟩ := ds7 hf hht hy hr hry hc
  have ha : (YO f).leadingCoeff ≠ 0 :=
    fun h => bPz hf (by rw [h, map_zero])
  exact ⟨r, ⟨hr, ht, hweight.trans (cXO p rfl ha), cXN hr⟩, hproper⟩
private theorem cr0 {b j : ℕ} {P : af 3} (hP : Gh P b j) :
    Supported ⟨b, j, 0⟩ (vY P) := by
  classical
  intro m hm
  change m ∈ (MvPolynomial.rename Fin.castSucc (fW P)).support at hm
  rw [MvPolynomial.support_rename_of_injective (Fin.castSucc_injective 3), Finset.mem_image] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  have hn' : n ∈ P.support := MvPolynomial.support_map_subset qY P hn
  refine ⟨?_, ?_, ?_⟩
  · rw [z2k (fun _ => rfl) (fun _ _ _ => rfl)]
    exact (MvPolynomial.le_totalDegree hn').trans hP.1
  · rw [z2k (fun _ => Nat.mul_zero _) (fun _ _ _ => Nat.mul_add ..)]
    exact (Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => m.sum (fun i a => i.val * a)) hn').trans hP.2
  · have hlast : (3 : Fin 4) ∉ Set.range (@Fin.castSucc 3) := by
      rintro ⟨i, hi⟩
      exact Fin.castSucc_ne_last i hi
    exact (Finsupp.mapDomain_of_notMem_range n _ hlast).le
theorem de0 (f : af 4) (P Q : af 3)
    (hP : Gh P IG.b IG.j) (hQ : Gh Q IG.b IG.j)
    (R : zJe (PrimeSpectrum gQ)) (hR : ∀ r ∈ R, bQ6 f P Q r)
    (H : Shape) (hch : bF H ∧ 1 ≤ H.t)
    (cut : PrimeSpectrum gQ → gQ) (points : PrimeSpectrum gQ → zJe oe)
    (hpoints : ∀ r ∈ R, Supported H (cut r) ∧ bTw r (cut r) (points r)) :
    32 * ahv * (∑ r ∈ R, (points r).card) ≤
      iH (shape f).iU IG IG H := by
  classical
  let p := (shape f).iU
  let J := xJ f P Q
  have hp := Tn f
  have hq : bF IG := ⟨by decide, by decide⟩
  have hopen (r : PrimeSpectrum gQ) (hr : r ∈ R) : ∃ a, bQE J r a :=
    bzM.proof J r (hR r hr).component (hR r hr).height (hR r hr).finite
  let guard (r : PrimeSpectrum gQ) : gQ :=
    if hr : r ∈ R then Classical.choose (hopen r hr) else 0
  have hguard (r : PrimeSpectrum gQ) (hr : r ∈ R) : bQE J r (guard r) := by
    simpa only [guard, dite_eq_left hr] using Classical.choose_spec (hopen r hr)
  obtain ⟨D, Ig, hD, hselected⟩ :=
    cHe H (dgm hch.1 hch.2) R (fun r hr => (hR r hr).height)
      guard (fun r hr => (hguard r hr).1) cut points (fun r hr => hpoints r hr)
  have hdisjoint : (R : Set (PrimeSpectrum gQ)).PairwiseDisjoint Ig := by
    intro r hr s hs hrs
    apply Finset.disjoint_left.mpr
    intro y hyr hys
    have hmem : guard r ∈ s.asIdeal :=
      (hguard r hr).2.1 s.asIdeal (hR s hs).component (fun heq => hrs (PrimeSpectrum.ext heq.symm))
    have hcontains := ((hselected s hs).2.1.2 y hys).1
    have heval : MvPolynomial.eval y (guard r) = 0 := RingHom.mem_ker.mp (hcontains hmem)
    exact (hselected r hr).2.2 y hyr heval
  let all := R.biUnion Ig
  have hisolated (y : oe) (hy : y ∈ all) : bRb (ke J D) ahv y := by
    obtain ⟨r, hr, hyr⟩ := Finset.mem_biUnion.mp hy
    have h := hselected r hr
    obtain ⟨hcontains, hzero⟩ := h.2.1.2 y hyr
    obtain ⟨hmin, hlen⟩ := (hguard r hr).2.2 D h.2.1.1 y hcontains (h.2.2 y hyr) hzero
    exact ⟨hmin, (hR r hr).heavy.trans hlen⟩
  have hbound :=
    deY p IG H hp hq hch.1 (ay7 f) (vY P) (vY Q) D
      (dgl f) (cr0 hP) (cr0 hQ) hD ahv all hisolated
  rw [c0w bRF.proof hp hq hq hch.1] at hbound
  have hbound_int :
      ((32 * ahv * all.card : ℕ) : ℤ) ≤
        gI (gI (gI (gI Dn p) IG) IG) H
          ⟨0, 0, 0⟩ := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_natCast] using hbound
  have hbound_nat : 32 * ahv * all.card ≤ iH p IG IG H := by
    simpa only [iH, Int.toNat_natCast] using Int.toNat_le_toNat hbound_int
  apply le_trans _ hbound_nat
  apply zBI
  rw [show all.card = ∑ r ∈ R, (Ig r).card from Finset.card_biUnion hdisjoint]
  exact zQk fun r hr => (hselected r hr).1
end
end qzTRNDe
end
section
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace aeL
noncomputable section
open Polynomial Matrix
open cu (Shape)
open Ge (jJ)
open agU (Bb Xq aVz aDY)
open scoped BigOperators Matrix Polynomial
private def bfC {s :Shape} {t:Offset s} (e :Pivot s t ↪ Lh s t) :ℕ :=
 (∑ r,(e r).1.val) - ∑ r :Pivot s t,r.1.val
private theorem eAw {s :Shape} {t:Offset s} (e :Pivot s t ↪ Lh s t) :
    bfC e≤aDY s.B s.J t.val := by
  classical
  have hpivot: (∑ r :Pivot s t,r.1.val) =
      ∑ q∈z4x (s.B+1),q*Xq s.B s.J t.val q:= by
    simp only [Pivot,zla,z7l,zDb,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_id]
    rw [zdx (fun q=>Xq s.B s.J t.val q*q) (s.B+1)]
    simp only [z5A (Xq s.B s.J t.val _) _]
  unfold bfC aDY
  rw [hpivot]
  apply Nat.sub_le_sub_right
  unfold aVz
  apply Finset.le_inf'
  intro k _
  have hexcess :
      (∑ r,((e r).1.val - k)) ≤ ∑ u:Lh s t,(u.1.val - k) := by
    calc
      _ = ∑ u∈Finset.univ.map e,(u.1.val - k) :=
        (Finset.sum_map (Finset.univ :zJe (Pivot s t)) e (fun u=>u.1.val - k)).symm
      _≤_:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intros
        positivity)
  calc
    (∑ r,(e r).1.val) ≤ ∑ r,(k+((e r).1.val - k)) :=
      zQk fun r _=> by omega
    _≤zhP (Pivot s t)*k + ∑ u:Lh s t,(u.1.val - k) := by
      rw [Finset.sum_add_distrib]
      simp only [z7l,zDb,nsmul_eq_mul]
      exact Nat.add_le_add_left hexcess _
    _ = _:= by
      simp only [Pivot,Lh,zla,Fintype.card_sigma,Fintype.card_fin,
        z7l,zDb,nsmul_eq_mul,Nat.cast_id]
      rw [zdx (fun q=>Xq s.B s.J t.val q) (s.B+1),
        zdx (fun q=>Bb s.B s.J t.val q*(q-k)) (s.B+1)]
      simp only [z5A (Bb s.B s.J t.val _) (_-_)]
private theorem eAy {R:Type} [CommRing R] {s :Shape} {t:Offset s}
    (e :Pivot s t ↪ Lh s t) (z :R) :
    ((Pa s t z).submatrix id e).det =
      ((Pa s t (1 :R)).submatrix id e).det*z^bfC e := by
  classical
  rw [z00,z00,Finset.sum_mul]
  apply zUo rfl
  intro σ _
  simp only [z6T,id_eq,mul_assoc]
  congr 1
  by_cases hgood : ∀ i,(σ i).1.val≤(e i).1.val
  · have he (i:Pivot s t) :
        Pa s t z (σ i) (e i)=Pa s t (1 :R) (σ i) (e i) *
          z^((e i).1.val-(σ i).1.val) := by
      by_cases hj:a2N (e i)≤(σ i).1.val <;> simp [Pa,hgood i,hj]
    have hw: (∑ i,((e i).1.val-(σ i).1.val))=bfC e := by
      rw [Finset.sum_tsub_distrib _ (fun i _=>hgood i),bfC,
        Equiv.sum_comp σ (fun r :Pivot s t=>r.1.val)]
    simp only [he,zeY,Finset.prod_pow_eq_pow_sum,hw]
  · push Not at hgood
    obtain ⟨i,hi⟩:=hgood
    have hz (v :R) :Pa s t v (σ i) (e i)=0:= by
      simp [Pa,not_le_of_gt hi]
    rw [zue (Finset.mem_univ i) (hz z),
      zue (Finset.mem_univ i) (hz 1),zero_mul]
private theorem eE9 {R:Type} [Field R] (s :Shape) (t:Offset s) (z :R) :
    ∃ e :Pivot s t ↪ Lh s t,((Pa s t z).submatrix id e).det≠0:= by
  classical
  have h (q:jJ s) :=eKK R (Gv s t) (Bb s.B s.J t.val q.val)
    (aIN s t q)
  choose eq hEq using h
  let e :Pivot s t ↪ Lh s t:=⟨fun r=>⟨r.1,eq r.1 r.2⟩,by
    rintro ⟨q,i⟩ ⟨q',j⟩ hh
    have hq:q=q' := congrArg Sigma.fst hh
    subst q'
    have heq :eq q i=eq q j:=eq_of_heq ((Sigma.mk.inj_iff.mp hh).2)
    exact congrArg (Sigma.mk q) ((eq q).injective heq)⟩
  let A:=(Pa s t z).submatrix id e
  have htri:A.BlockTriangular (fun r=>r.1) := by
    intro i j hij
    change Pa s t z i (e j)=0
    have hlt: (e j).1.val< i.1.val :=hij
    simp [Pa,not_le_of_gt hlt]
  refine ⟨e,?_⟩
  change A.det≠0
  rw [htri.det_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro q _
  let f :Fin (Xq s.B s.J t.val q.val) ≃ {r :Pivot s t // r.1=q} :=
    Equiv.ofBijective (fun j=>⟨⟨q,j⟩,rfl⟩) (by
      constructor
      · intro i j hh
        exact eq_of_heq ((Sigma.mk.inj_iff.mp (congrArg Subtype.val hh)).2)
      · rintro ⟨⟨q',j⟩,hq⟩
        change q' = q at hq
        subst q'
        exact ⟨j,rfl⟩)
  rw [← Matrix.det_submatrix_equiv_self f]
  have hblock : ((A.toSquareBlock (fun r=>r.1) q).submatrix f f) =
      (btx (R:=R) (Gv s t) (Bb s.B s.J t.val q.val)
        (aIN s t q)).submatrix id (eq q) := by
    ext i j
    have hj:=((beO s t q (eq q j).val (eq q j).isLt).1).trans (min_le_left _ _)
    change Pa s t z ⟨q,i⟩ ⟨q,eq q j⟩ =
      ((Gv s t+(eq q j).val).choose i.val :R)
    simp [Pa,a2N,hj]
  rw [hblock]
  exact hEq q
theorem dAa (F:Type) [Field F] (s :Shape) (t:Offset s) (a b c:F)
    (hb:b≠0) :
    bQp (Pa s t (a6h a b c)) (aDY s.B s.J t.val) := by
  let δ:=aDY s.B s.J t.val
  let N :F[X] :=C a*z7y
  let D:F[X] :=C b+C c*z7y
  let f :=algebraMap F[X] (Ru F)
  have hc (u:F) :f (C u)=algebraMap F (Ru F) u :=
    (IsScalarTower.algebraMap_apply F F[X] (Ru F) u).symm
  have hD:D ≠0:= by
    intro hz
    apply hb
    simpa [D] using congrArg (fun p:F[X]=>p.coeff 0) hz
  have hDf :f D ≠0:= by
    simpa only [f,map_zero] using (zxb F[X] (Ru F)).ne hD
  have hz :a6h a b c=f N/f D:= by
    simp only [a6h,N,D,map_mul,map_add,hc]
    rfl
  have hNdeg:N.natDegree≤1 :=
    (zm2 (p:=C a) (q:=z7y)).trans (by simp)
  have hDdeg:D.natDegree≤1 := by
    unfold D
    rw [Polynomial.natDegree_C_add]
    exact Polynomial.natDegree_mul_le.trans (by simp)
  refine ⟨eE9 s t _,f D^δ,pow_ne_zero _ hDf,?_⟩
  intro e
  let d:=bfC e
  let m:=((Pa s t (1 :F)).submatrix id e).det
  have hd:d≤δ:=eAw e
  let g:=C m*N^d*D^(δ-d)
  refine ⟨g,?_,?_⟩
  · have hNd: (N^d).natDegree≤d :=
      Polynomial.natDegree_pow_le.trans (by simpa using zBI d hNdeg)
    have hDd: (D^(δ-d)).natDegree≤δ-d :=
      Polynomial.natDegree_pow_le.trans (by simpa using zBI (δ-d) hDdeg)
    have hg:=zm2 (p:=C m*N^d) (q:=D^(δ-d))
    have hm:=zm2 (p:=C m) (q:=N^d)
    rw [Polynomial.natDegree_C,zero_add] at hm
    change (C m*N^d*D^(δ-d)).natDegree≤δ
    omega
  · have hmapped: ((Pa s t (1 :F)).submatrix id e).map (algebraMap F (Ru F)) =
        (Pa s t (1 :Ru F)).submatrix id e := by
      ext i j
      simp only [Matrix.map_apply,z6T,Pa,apply_ite,map_zero,
        map_mul,map_natCast,map_pow,map_one]
      split_ifs <;> rfl
    have hm:f (C m)=((Pa s t (1 :Ru F)).submatrix id e).det:= by
      rw [hc]
      change (algebraMap F (Ru F)) ((Pa s t (1 :F)).submatrix id e).det= _
      rw [RingHom.map_det]
      exact congrArg Matrix.det hmapped
    have hpow:f D^δ*(f N/f D)^d=f N^d*f D^(δ-d) := by
      calc
        _=f N^d*(f D^δ/f D^d) := by rw [div_pow]; ring
        _ = _:= by
          congr 1
          apply (div_eq_iff (pow_ne_zero _ hDf)).2
          rw [← pow_add,Nat.sub_add_cancel hd]
    rw [eAy,hz]
    change f (C m*N^d*D^(δ-d)) =
      f D^δ*(((Pa s t (1 :Ru F)).submatrix id e).det*(f N/f D)^d)
    rw [map_mul,map_mul,map_pow,map_pow,hm,mul_left_comm (f D^δ),hpow]
    ac_rfl
end
end aeL
end
end
section
set_option autoImplicit true
namespace ON
noncomputable section


open aR (Shape)

open scoped BigOperators Polynomial
def tC (p:Shape) :Shape :=
 ⟨p.b,p.j+1,min (p.t+1) ((p.j+1)/2)⟩
end
end ON
end
section
section
set_option autoImplicit true
namespace Y3
noncomputable section
open Polynomial


theorem embed_injective :zq4 embed :=
 Polynomial.map_injective _ (MvPolynomial.map_injective _ (zxb _ _))
end
end Y3
end
end
section
set_option autoImplicit true
section
namespace aqp
open xE

open aFM (aM3)








def count (d n:ℕ) :ℕ :=
 match aM3 d n with
 | (a,b)=>Nat.sub a b
def ker (d l u h r :ℕ) :ℕ :=
 let Bp:= fun n=>if d< r then 0 else count (d-r) n
 (count d u+Bp (h-3*r))-(count d h+Bp l)
end aqp
end
end
section
set_option autoImplicit true
section
namespace AJ
open aR (Shape)

open scoped BigOperators
def bmI (s :Shape) :ℕ :=
  FI.a3U s.b s.j -
    if s.t+1≤ min s.b (s.j/3) then
     FI.a3U (s.b-(s.t+1)) (s.j-3*(s.t+1))
    else 0
def ahC (box used :Shape) :ℕ :=
  if used.b≤box.b∧used.j≤box.j∧used.t≤box.t then
    bmI ⟨box.b - used.b,box.j - used.j,box.t - used.t⟩
  else 0
def CL (f :ℕ→ℕ) :ℕ→ℕ
 | 0=>0
 | n+1=>CL f n+f n
def remainder (stop edge :Shape) :Shape :=
 ⟨stop.b-edge.b,stop.j-edge.j,stop.t - edge.t⟩
abbrev Triple :=ℕ×ℕ×ℕ
def unpack (a :Triple) :Shape :=⟨a.1,a.2.1,a.2.2⟩
end AJ
end
section
namespace AJ
open aR (Shape)
open scoped BigOperators
private def S6 (b j z :ℕ) :ℕ :=
 ∑ y∈z4x (min (b - z) ((j-3*z)/2)+1),
   ∑ x∈z4x (min (b - z - y) (j-3*z - 2*y)+1),
     (b - z - y - x+1)
private theorem euW (b j k z :ℕ) :
  S6 b j (k+z)=S6 (b - k) (j-3*k) z := by
 simp only [S6,Nat.mul_add,← Nat.sub_sub]
private theorem gum (b j k :ℕ) (hk :k≤ min b (j/3)) :
   aR.symbols b j =
     (∑ z∈z4x k,S6 b j z)+aR.symbols (b - k) (j-3*k) := by
 have hb:k≤b:=hk.trans (min_le_left _ _)
 have hjd:k≤j/3:=hk.trans (min_le_right _ _)
 have hdiv : (j-3*k)/3=j/3 - k := by omega
 have hlen:min b (j/3)+1=k+(min (b-k) ((j-3*k)/3)+1) := by
   rw [hdiv]
   omega
 change (∑ z∈z4x (min b (j/3)+1),S6 b j z)= _
 rw [hlen,Finset.sum_range_add]
 congr 1
 change (∑ z∈z4x (min (b-k) ((j-3*k)/3)+1),S6 b j (k+z)) =
   (∑ z∈z4x (min (b-k) ((j-3*k)/3)+1),S6 (b-k) (j-3*k) z)
 exact zUo rfl fun z _=>euW b j k z
theorem cr5 (s :Shape) :Ds.symbols s=bmI s := by
 rcases s with ⟨b,j,t⟩
 change (∑ z∈z4x (min t (min b (j/3))+1),S6 b j z) =
   FI.a3U b j -
    if t+1≤ min b (j/3) then FI.a3U (b-(t+1)) (j-3*(t+1)) else 0
 simp only [← aY8.gxW]
 split
 · rename_i ht
   rw [min_eq_left (by omega :t≤ min b (j/3)),gum b j (t+1) ht,z2h]
 · rename_i ht
   rw [min_eq_right (by omega :min b (j/3)≤t),Nat.sub_zero]
   rfl
theorem bOw (f :ℕ→ℕ) (n:ℕ) :
   CL f n = ∑ i∈z4x n,f i:= by
 induction n with
 | zero=>simp [CL]
 | succ n ih=>rw [CL,Finset.sum_range_succ,ih]
end AJ
end
section
namespace AJ
open aR (Shape)
open Ds (Valid oL)
@[simp] theorem ce7 (p e :Shape) :remainder (p.plus e) e=p:= by
  cases p
  simp only [remainder,Shape.plus,z2h]
theorem akw {p e :Shape} (hp:p=oL∨Valid p) (he :Valid e) :
   Valid (p.plus e) := by
 rcases hp with hp | hp
 · subst p
   change Valid ⟨0+e.b,0+e.j,0+e.t⟩
   simpa only [Nat.zero_add] using he
 · obtain ⟨hp₁,hp₂,hp₃⟩:=hp
   obtain ⟨he₁,he₂,he₃⟩:=he
   change 1≤p.t+e.t∧3*(p.t+e.t)≤p.j+e.j∧p.j+e.j≤3*(p.b+e.b)
   omega
end AJ
end
section
namespace ac5
noncomputable section

open fP (Ew m9)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
def asu (q:ℕ) :ℕ :=
 if q≤113 then 49 - 2*((q - 102)/2) else 36 - 2*((q - 114)/2)
def iO (q:ℕ) :ℕ:=min q (asu q)
def Vm (q:ℕ) (g:ℤ) :ℤ:=90-(q:ℤ) - g
abbrev XN (q:ℕ) (g:ℤ) :=
 {m:Fin 4 →₀ ℕ // Ew (iO q) (-g) 49 14 m}
abbrev ait (q:ℕ) (g:ℤ) :=
 {m:Fin 4 →₀ ℕ // m.degree=iO q ∧
   m.weight m9<(Vm q g).toNat}
instance gOZ (q:ℕ) (g:ℤ) :Finite (XN q g) :=
 ((z31 _).subset fun _ (h:Ew _ _ _ _ _) =>
   Nat.le_of_eq h.1).to_subtype
instance gO1 (q:ℕ) (g:ℤ) :Finite (ait q g) :=
 ((z31 _).subset fun _ (h:_∧_) =>
   Nat.le_of_eq h.1).to_subtype
noncomputable instance gO0 (q:ℕ) (g:ℤ) :z85 (XN q g) :=
 zQs _
noncomputable instance gO2 (q:ℕ) (g:ℤ) :z85 (ait q g) :=
 zQs _
end
end ac5
end
end
section
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace aSk
noncomputable section
open Polynomial Matrix
open scoped Polynomial BigOperators
variable {F ι κ:Type} [Field F] [z85 ι] [DecidableEq ι] [z85 κ]
local notation "K" => aeL.Ru F
local notation "φ" => algebraMap F[X] K
omit [z85 ι] in
private theorem dMF {s :zJe ι} (p:ι→F[X]) (d:ι→ℕ)
    (h : ∀ i∈s,(p i).natDegree≤d i) :
    (∏ i∈s,p i).coeff (∑ i∈s,d i) = ∏ i∈s,(p i).coeff (d i) := by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih =>
    rw [zqX hi,Finset.sum_insert hi,zqX hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (h i (Finset.mem_insert_self _ _))]
    · exact congrArg ((p i).coeff (d i) * ·) (ih fun j hj=>h j (zJN hj))
    · exact (Polynomial.natDegree_prod_le _ _).trans
        (zQk fun j hj=>h j (zJN hj))
private theorem d4f (B:z30 ι κ F) (hB:z14 F B.row) :
  ∃ e :ι ↪ κ,(B.submatrix id e).det≠0:= by
 classical
 have hr :B.rank=zhP ι:= by
  rw [Matrix.rank_eq_finrank_span_row,finrank_span_eq_card hB]
 obtain ⟨α,a,ha,hspan,hli⟩:=exists_linearIndependent' F B.col
 let:Finite α:=Finite.of_injective a ha
 let:z85 α:=zQs α
 have hc:zhP ι=zhP α:= by
  rw [← finrank_span_eq_card hli,hspan,← Matrix.rank_eq_finrank_span_cols,hr]
 let u:=Fintype.equivOfCardEq hc
 let e :ι ↪ κ:=u.toEmbedding.trans ⟨a,ha⟩
 have hli' : z14 F (B.submatrix id e).col:=hli.comp u u.injective
 exact ⟨e,((Matrix.isUnit_iff_isUnit_det _).mp
  (Matrix.linearIndependent_cols_iff_isUnit.mp hli')).ne_zero⟩
theorem d4s (Q:z30 ι κ F[X]) (d:ι→ℕ)
  (hdeg : ∀ r u,(Q r u).natDegree≤d r)
  (hlead:z14 F (a5a Q d).row) :
  ∃ e :ι ↪ κ,(Q.submatrix id e).det≠0∧(∑ r,d r)≤(Q.submatrix id e).det.natDegree := by
 obtain ⟨e,he⟩:=d4f (a5a Q d) hlead
 have hcoeff :
    (Q.submatrix id e).det.coeff (∑ r,d r)=((a5a Q d).submatrix id e).det:= by
  rw [← zgP (Q.submatrix id e),← zgP ((a5a Q d).submatrix id e),
    z00,z00,Polynomial.finsetSum_coeff]
  apply zUo rfl
  intro σ _
  rw [← map_intCast (C:F →+* F[X]),Polynomial.coeff_C_mul]
  simp only [Matrix.transpose_apply,z6T,id_eq,a5a]
  rw [dMF _ d (fun i _=>hdeg i (e (σ i)))]
 have hne : (Q.submatrix id e).det.coeff (∑ r,d r)≠0:=hcoeff.trans_ne he
 exact ⟨e,fun hz=>hne (by rw [hz,Polynomial.coeff_zero]),Polynomial.le_natDegree_of_ne_zero hne⟩
private theorem dWC {R:Type} [CommRing R]
    (Q:z30 ι κ R) (T:z30 κ ι R) :
    (Q*T).det = ∑ f :ι→κ,(∏ j,T (f j) j)*(Q.submatrix id f).det:= by
  classical
  calc
    (Q*T).det = ∑ f :ι→κ,∑ σ:Equiv.Perm ι,
        (↑↑(Equiv.Perm.sign σ) :R) * ∏ i,Q (σ i) (f i)*T (f i) i:= by
      simp only [z00,Matrix.mul_apply,Finset.prod_univ_sum,
        zxw,Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _:= by
      apply zUo rfl
      intro f _
      simp only [z00,zxw,z6T,id_eq,
        zeY,mul_comm,mul_assoc]
private theorem gl8 (Q:z30 ι κ F[X]) (T:z30 κ ι F[X])
   (hQT:Q*T=1) (t:K)
   (h : ∀ f :ι→κ,∃ g:F[X],φ g=t*φ (Q.submatrix id f).det) :
   ∃ g:F[X],φ g=t:= by
 classical
 choose g hg using h
 refine ⟨∑ f :ι→κ,(∏ j,T (f j) j)*g f,?_⟩
 have hh:=dWC Q T
 rw [hQT,Matrix.det_one] at hh
 have he :=congrArg φ hh
 simp only [map_one,map_sum,map_mul] at he
 simp only [map_sum,map_mul,hg]
 calc
   _=t * ∑ f :ι→κ,φ (∏ j,T (f j) j)*φ (Q.submatrix id f).det:= by
     rw [zxw]
     exact zUo rfl fun f _=>mul_left_comm _ _ _
   _=t:= by rw [← he,mul_one]
theorem aVV (M:z30 ι κ K) (D:ℕ)
    (Q:z30 ι κ F[X]) (T:z30 κ ι F[X]) (L:z30 ι ι K)
    (hQT:Q*T=1) (hM:M=L*Q.map φ) (hb:aeL.bQp M D)
    (e :ι ↪ κ) (he : (Q.submatrix id e).det≠0) :
    (Q.submatrix id e).det.natDegree≤D:= by
  classical
  obtain ⟨⟨e₀,he₀⟩,scale,hscale,hminors⟩:=hb
  have hdet (f :ι→κ) :
      (M.submatrix id f).det=L.det*φ (Q.submatrix id f).det:= by
    rw [hM,Matrix.submatrix_mul _ _ id id f Function.bijective_id,
      Matrix.submatrix_id_id,Matrix.det_mul,RingHom.map_det]
    rfl
  have hL:L.det≠0:= by
    intro hz
    exact he₀ (by rw [hdet,hz,zero_mul])
  have hall (f :ι→κ) : ∃ g:F[X],φ g=(scale*L.det)*φ (Q.submatrix id f).det:= by
    by_cases hf :zq4 f
    · let e' : ι ↪ κ:=⟨f,hf⟩
      obtain ⟨g,_,hg⟩:=hminors e'
      change φ g=scale*(M.submatrix id f).det at hg
      rw [hdet,← mul_assoc] at hg
      exact ⟨g,hg⟩
    · obtain ⟨i,j,hij,hne⟩:=Function.not_injective_iff.mp hf
      have hz : (Q.submatrix id f).det=0 :=
        Matrix.det_zero_of_column_eq hne (fun u=>congrArg (Q u) hij)
      exact ⟨0,by rw [hz,map_zero,mul_zero]⟩
  obtain ⟨p,hp⟩:=gl8 Q T hQT (scale*L.det) hall
  have hp0:p≠0:= by
    intro hz
    exact (mul_ne_zero hscale hL) (by rw [← hp,hz,map_zero])
  obtain ⟨g,hg,hge⟩:=hminors e
  have hmul :g=p*(Q.submatrix id e).det:= by
    apply zxb F[X] K
    rw [hge,hdet,map_mul,hp,mul_assoc]
  rw [hmul,Polynomial.natDegree_mul hp0 he] at hg
  exact (Nat.le_add_left _ _).trans hg
end
end aSk
end
end
