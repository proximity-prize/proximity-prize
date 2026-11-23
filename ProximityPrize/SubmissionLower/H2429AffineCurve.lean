import ProximityPrize.SubmissionLower.HighCore82258Family
import ProximityPrize.SubmissionLower.PeriodTwoPrefixReconstruction
import ProximityPrize.SubmissionLower.H2429AffineRates

set_option autoImplicit false
set_option Elab.async false

namespace H2429AffineCurve
noncomputable section
open HighCore82258 (K I node agreement blockLength p AnchorModel AnchoredFamily FixedWord
  persistent_card_le section_incidence)
open K1_14 (FX L seedEmbedding liftPoly)
open K1_14_2 (SmallRootCurve OnRoot SeedField RootSeedSection)
open K1_14_2_4
open K1_14_2_4_2
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart)
open ResidueSpace
open Finset Polynomial MvPolynomial
open scoped BigOperators
open private jetNumerator jet_bound jet_eval from ProximityPrize.SubmissionLower.UpperBranch3

def unit (g : ℕ) : ℚ :=
  let ρ := H2429AffineRates.ratio 0
  (1 + 2*ρ*128644) * (2*(g : ℚ)-1) + ρ

def Tariff {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) : Prop :=
  ∀ T ⊆ Γ, ∀ J g H, 0 < g → g ≤ 80 → SmallRootCurve J g H →
    Module.finrank SeedField (RootSeedSection J) < p →
    (∀ γ ∈ T, OnRoot J (M.label γ) (F.scalar γ)) → (T.card : ℚ) ≤ unit g * H + g

private theorem taylor_forms {n t g : ℕ} (htp : t < p) (hg : 0 < g)
    (f : FamilyEquation n) (hf : FamilyDegree f g) (eligible : Polynomial K → Prop)
    (c : K → FX) (a : K → Fin (t+1) → FX)
    (weights : ∀ x S, eligible S →
      seedEmbedding (S.eval x) = c x + ∑ j, a x j * (taylor center (S.map seedEmbedding)).coeff j) :
    ∃ C : TaylorForms n (ordinateBound t g) (taylorPower t),
      ∀ (v : Fin n → L) (S : Polynomial K), eligible S →
        (specialize f v).eval (liftPoly S) = 0 →
        (specialize f v).derivative.eval (liftPoly S) ≠ 0 → C.Recovers v S := by
  classical
  let F := flatten f
  let D := separant F ^ taylorPower t
  have hF := flatten_bound hf
  have hD : D ∈ box n (ordinateBound t g) (taylorPower t) := by
    have hb := box_pow (separant_bound hF) (taylorPower t)
    rw [Nat.mul_one] at hb
    exact mem_restrictBidegree_mono hb (Nat.le_add_left _ _) le_rfl
  let N (x : K) := c x • D + ∑ j, a x j • jetNumerator F t j
  have hN (x : K) : N x ∈ box n (ordinateBound t g) (taylorPower t) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hD)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (jet_bound hg hF j))
  refine ⟨⟨D,N,hD,hN⟩, ?_⟩
  intro v S hS hroot hsep
  have hroot' : markEval v S F = 0 := by rw [eval_flatten,hroot,map_zero]
  constructor
  · change markEval v S (separant F ^ taylorPower t) ≠ 0
    rw [map_pow,eval_separant]
    exact pow_ne_zero _ (by
      simpa only [map_zero] using (IsFractionRing.injective L[X] FX).ne hsep)
  · intro x
    change markEval v S (N x) = markEval v S D * seedEmbedding (S.eval x)
    rw [weights x S hS,mul_add,Finset.mul_sum]
    simp only [N,map_add,map_sum,MvPolynomial.smul_eq_C_mul,map_mul,
      MvPolynomial.eval_C,jet_eval htp F v S hroot']
    rw [mul_comm (c x)]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by dsimp only [D]; ring

private theorem power_cast {t : ℕ} (ht : 0 < t) : (taylorPower t : ℚ) = 2*(t : ℚ)-1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl

private theorem regular_count {n g H : ℕ} {U : Finset K} {s : K → Polynomial K} {w : I → K}
    (A : RegularChart U s g H n) (hw : FixedWord w U s 133500) (hg : 0 < g)
    (G : Polynomial K) (R : Fin 2 → Polynomial K)
    (off : ∀ i : I, G.eval (node i) ≠ 0)
    (hdegree : space G 128643 R ≤ degreeLT K 133501)
    (hspace : ∀ γ ∈ U, s γ ∈ space G 128643 R) :
    (U.card : ℚ) ≤ H2429AffineRates.ratio 0 * (257287*(2*(g : ℚ)-1)+1)*H+1 := by
  have hgQ : (1 : ℚ) ≤ g := by exact_mod_cast hg
  have hfee : 0 ≤ H2429AffineRates.ratio 0 * (257287*(2*(g : ℚ)-1)+1)*H := by
    refine mul_nonneg (mul_nonneg (by norm_num [H2429AffineRates.ratio]) (by linarith)) (Nat.cast_nonneg _)
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h,hfee]
  let sites := persistentNodes w U s
  let t := H2429AffineRates.order sites.card
  have hs : sites.card ≤ 133500 := persistent_card_le hw (by omega)
  have ht : 0 < t := Nat.le_max_left _ _
  have htp : t < p :=
    (max_le (by decide : 1 ≤ 128644) (Nat.sub_le _ _)).trans_lt (by decide)
  let nmap : I ↪ K := ⟨node, ProximityPrize.Benchmark.IRSProfile.domain.injective⟩
  have hinj : Function.Injective (Polynomial.eval₂RingHom seedEmbedding center) :=
    PeriodTwoPrefixReconstruction.eval₂_symbol_injective (algebraMap K L)
      (algebraMap L[X] FX) (IsFractionRing.injective L[X] FX)
  obtain ⟨c,a,ha⟩ := PeriodTwoPrefixReconstruction.indexed_interpolation_weights_2429
    G R nmap sites w (fun i _ => off i) hdegree (by decide : 133501 ≤ p)
    seedEmbedding center hinj
  let eligible (S : Polynomial K) := S ∈ space G 128643 R ∧ ∀ i ∈ sites, S.eval (node i) = w i
  obtain ⟨C,hC⟩ := taylor_forms htp hg A.equation A.equation_degree eligible c a
    (fun x S hS => ha x S hS.1 hS.2)
  let D := taylorPower t*(g*H) + ordinateBound t g*H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hC _ _ ⟨hspace γ hγ,fun _ hi => hits_persistent hγ hi⟩ (A.root γ hγ) (A.simple γ hγ)
  have hcount := section_incidence hw D hsection
  have hpos : (0 : ℚ) < 179876 - (sites.card : ℚ) := by
    have h : (sites.card : ℚ) ≤ 133500 := by exact_mod_cast hs
    linarith
  have hratio : (U.card : ℚ) ≤ H2429AffineRates.ratio sites.card * (D : ℚ) := by
    unfold H2429AffineRates.ratio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hpos).mpr
    rw [mul_comm (U.card : ℚ), ← show (agreement : ℚ) = 179876 by decide,
      ← show (blockLength : ℚ) = 262144 by decide, ← Nat.cast_sub (hs.trans (by decide : 133500 ≤ agreement)),
      ← Nat.cast_sub (hs.trans (by decide : 133500 ≤ blockLength))]
    exact_mod_cast hcount
  have hD : D = (taylorPower t*taylorPower g + 1)*H := by
    rw [← show g+(g-1) = taylorPower g by unfold taylorPower; omega]
    dsimp [D,ordinateBound]
    ring
  have hcharge := H2429AffineRates.curve hs (show (1 : ℚ) ≤ 2*(g : ℚ)-1 by linarith)
  refine hratio.trans (le_trans ?_ (le_add_of_nonneg_right (zero_le_one : (0 : ℚ) ≤ 1)))
  rw [hD]
  push_cast
  rw [power_cast ht,power_cast hg, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hcharge (Nat.cast_nonneg _)

theorem of_frame {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (G : Polynomial K) (R : Fin 2 → Polynomial K)
    (off : ∀ i : I, G.eval (node i) ≠ 0)
    (hdegree : space G 128643 R ≤ degreeLT K 133501)
    (hspace : ∀ γ ∈ Γ, F.scalar γ ∈ space G 128643 R) :
    Tariff M F := by
  intro T hT J g H hg hgLimit hcurve _ hmarks
  have hlabel : Set.InjOn M.label (T : Set K) := by
    intro γ _ η _ h
    exact sub_left_inj.mp h
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve hlabel hmarks
  have hw : FixedWord M.word U F.scalar 133500 := by
    refine ⟨F.distinct.mono (hU.trans hT), ?_, ?_⟩
    · intro γ hγ
      by_cases hz : F.scalar γ = 0
      · simp [hz]
      · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hz).mpr
          (mem_degreeLT.mp (hdegree (hspace γ (hT (hU hγ))))))
    · intro γ hγ
      let m := F.mark γ (hT (hU hγ))
      exact ⟨m.bad.support,m.bad.agreement,m.scalar_hits⟩
  have hregular := regular_count A hw hg G R off hdegree (fun γ hγ => hspace γ (hT (hU hγ)))
  have hgQ : (1 : ℚ) ≤ g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ) ≤ (taylorPower g : ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ) + (U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ)*H +
        (H2429AffineRates.ratio 0 * (257287*(2*(g : ℚ)-1)+1)*H+1) :=
      add_le_add hexcQ hregular
    _ ≤ unit g*H+g := by
      rw [power_cast hg,unit]
      have h := mul_nonneg (show (0 : ℚ) ≤ H2429AffineRates.ratio 0 by norm_num [H2429AffineRates.ratio])
        (mul_nonneg (show (0 : ℚ) ≤ 2*(g : ℚ)-1 by linarith) (Nat.cast_nonneg (α := ℚ) H))
      nlinarith only [h,hgQ]

end
end H2429AffineCurve
