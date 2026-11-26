import ProximityPrize.SubmissionBinaryLower.B6402ProfileMatch
import ProximityPrize.SubmissionBinaryLower.B6402GridRouting
namespace ProximityPrize.SubmissionBinaryLower.B6402SpecialRouting
open Polynomial B6401Params B6401ContactKerD B6401T4Grid B6402T4Rows B6402Table4Common B6402Table4NonK B6402Table4K
open B6402IntFarkas B6402GridProfile B6402GridRouting B6402RowTransport Native6402Grid
open B6401FactorBound (G_val std5Slot std5Slot_spec)
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
set_option autoImplicit false
set_option maxHeartbeats 2000000
local notation "Fld" => BinaryIRSProfile.Field

def Assigned (D : KerD45Data) (r : Fin 5) : Prop :=
  ∃ j : Fin 237,coversGap (key j) r ∧ lo (key j)≤(D.W_F:ℚ)/wY ∧ (D.W_F:ℚ)/wY≤hi (key j) ∧ Feasible D (key j)
lemma t4_start_end_bounds (D : KerD45Data) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5) :
    0 < T4_START_D ∧ 0 < T4_END_D ∧ T4_START_N * T4_END_D < T4_END_N * T4_START_D ∧
    (T4_START_N : ℚ) / (T4_START_D : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ) ∧
    (D.W_F : ℚ) / (wY : ℚ) ≤ (T4_END_N : ℚ) / (T4_END_D : ℚ) := by
  refine ⟨by norm_num [T4_START_D, wY], by norm_num [T4_END_D],
          by norm_num [T4_START_N, T4_START_D, T4_END_N, T4_END_D, wY], ?_, ?_⟩
  · unfold T4_START_N T4_START_D
    have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
    apply div_le_div_of_nonneg_right _ hwQ.le
    have h1 : 5 * wY - 1 ≤ D.W_F := by have := D.hWF_lo; omega
    exact_mod_cast h1
  · simpa [T4_END_N, T4_END_D] using hWF_hi

private theorem sameGap (k : Key) (r : Fin 5) (valid : coversGap k r) :
    let b:=B6401T4Grid.std5Bounds r
    (k.gap.1=b.1 ∧ k.gap.2.1=b.2.1 ∧ k.gap.2.2.1=b.2.2.1 ∧ k.gap.2.2.2=b.2.2.2) ∨
    (k.gap.1=0 ∧ k.gap.2.1=1 ∧ k.gap.2.2.1=1 ∧ k.gap.2.2.2=1) := by
  rcases valid with h|h
  · left; simp [h]
  · right; simp [h,single]

lemma t4_witness_of_t4a (D : KerD45Data) (r : Fin 5) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5)
    (br : T4ABranch)
    (hvalid : match br with
      | .det | .p0Zero => True
      | .p0 m21Nz _ p0M10D4 q2M21M10 => m21Nz = false → p0M10D4 = true ∧ q2M21M10 = false
      | .b1c1 _ _ bCase => bCase < 6)
    (x : Fin (t4aNumVars br) → ℚ) (hx_nn : ∀ j, 0 ≤ x j)
    (hx0 : x ⟨0, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n0 : ℚ) / (N : ℚ))
    (hx1 : x ⟨1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n1 : ℚ) / (N : ℚ))
    (hx2 : x ⟨2, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨3, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n3 : ℚ) / (N : ℚ))
    (hx4 : x ⟨4, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.nt : ℚ) / (N : ℚ))
    (hxic : x ⟨t4aNumVars br - 1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.W_F : ℚ) / (wY : ℚ))
    (hub : ∀ row ∈ (buildT4ARows br T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2).1.toList,
      RowValid (t4aNumVars br) row ∧ RowSatLe x row)
    (heq : ∀ row ∈ (buildT4ARows br T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2).2.toList,
      RowValid (t4aNumVars br) row ∧ RowSatEq x row) :
    Assigned D r := by
  have lw : 5*wY-1≤D.W_F := by have := D.hWF_lo; omega
  have left : ((5*wY-1:ℕ):ℚ)/wY≤(D.W_F:ℚ)/wY := div_le_div_of_nonneg_right (by exact_mod_cast lw) (by positivity)
  have startOk : first≤(D.W_F:ℚ)/wY := by
    have e : first=((5*wY-1:ℕ):ℚ)/wY := by norm_num [first,wY]
    rwa [e]
  obtain ⟨tagId,et⟩ := tag_A br hvalid
  obtain ⟨j,ej,gap,ld,ud,lc,uc⟩ := select tagId r _ startOk hWF_hi
  have eq := ej.trans et
  have satr := buildT4ARows_transport br x ld ud (hxic.symm ▸ lc) (hxic.symm ▸ uc) (sameGap (key j) r gap) hub heq
  refine ⟨j,gap,lc,uc,?_⟩
  unfold Feasible rows; rw [eq]
  exact ⟨by cases br <;> simp [arity,t4aNumVars],x,hx_nn,hx0,hx1,hx2,hx3,hx4,hxic,satr⟩


lemma t4_witness_of_t4b (D : KerD45Data) (r : Fin 5) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5)
    (br : T4BBranch) (hq1 : br.q1Case < 3) (hode : br.odeCase < 7)
    (x : Fin 49 → ℚ) (hx_nn : ∀ j, 0 ≤ x j)
    (hx0 : x ⟨0, by decide⟩ = (D.n0 : ℚ) / (N : ℚ))
    (hx1 : x ⟨1, by decide⟩ = (D.n1 : ℚ) / (N : ℚ))
    (hx2 : x ⟨2, by decide⟩ = (D.n2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨3, by decide⟩ = (D.n3 : ℚ) / (N : ℚ))
    (hx4 : x ⟨4, by decide⟩ = (D.nt : ℚ) / (N : ℚ))
    (hxic : x ⟨48, by decide⟩ = (D.W_F : ℚ) / (wY : ℚ))
    (hub : ∀ row ∈ (buildT4BRows br T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2).1.toList,
      RowValid 49 row ∧ RowSatLe x row)
    (heq : ∀ row ∈ (buildT4BRows br T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2).2.toList,
      RowValid 49 row ∧ RowSatEq x row) :
    Assigned D r := by
  have lw : 5*wY-1≤D.W_F := by have := D.hWF_lo; omega
  have left : ((5*wY-1:ℕ):ℚ)/wY≤(D.W_F:ℚ)/wY := div_le_div_of_nonneg_right (by exact_mod_cast lw) (by positivity)
  have startOk : first≤(D.W_F:ℚ)/wY := by
    have e : first=((5*wY-1:ℕ):ℚ)/wY := by norm_num [first,wY]
    rwa [e]
  obtain ⟨tagId,et⟩ := tag_B br hq1 hode
  obtain ⟨j,ej,gap,ld,ud,lc,uc⟩ := select tagId r _ startOk hWF_hi
  have eq := ej.trans et
  have satr := buildT4BRows_transport br x ld ud (hxic.symm ▸ lc) (hxic.symm ▸ uc) (sameGap (key j) r gap) hub heq
  refine ⟨j,gap,lc,uc,?_⟩
  unfold Feasible rows; rw [eq]
  exact ⟨(by decide : 5<49),x,hx_nn,hx0,hx1,hx2,hx3,hx4,hxic,satr⟩

lemma t4_point_det_witness (D : KerD45Data) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5)
    (hdet : D.detM ≠ 0) :
    Assigned D (std5Slot (G_val D.W_F D.k D.Az)) := by
  set r := std5Slot (G_val D.W_F D.k D.Az) with hr_def
  have ⟨hsD, heD, _, hlo, hhi⟩ := t4_start_end_bounds D hWF_hi
  have ⟨hloGD, hhiGD, hloG, hhiG⟩ := std5Slot_spec (B6402ProfileMatch.nonneg D)
  rw [← hr_def] at hloGD hhiGD hloG hhiG
  rw [←B6402ProfileMatch.gap_eq] at hloG hhiG
  obtain ⟨x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩ :=
    D.table4_det_sat hdet T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2
      hsD heD hloGD hhiGD hlo hhi hloG hhiG
  exact t4_witness_of_t4a D r hWF_hi .det trivial x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq

lemma t4_point_p0Zero_witness (D : KerD45Data) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5)
    (hminors : ∀ j : Fin 3, D.Bj 2 * D.Cj j + D.Cj 2 * D.Bj j = 0) :
    Assigned D (std5Slot (G_val D.W_F D.k D.Az)) := by
  have h2ne : D.Bj 2 ≠ 0 ∨ D.Cj 2 ≠ 0 := by
    by_contra hall; push Not at hall
    apply D.g2_ne_zero
    unfold KerD45Data.gj; rw [hall.1, hall.2, Polynomial.zero_comp, mul_zero, add_zero]
  let g := EuclideanDomain.gcd (D.Bj 2) (D.Cj 2)
  have hg_ne : g ≠ 0 := by
    intro h0; have := EuclideanDomain.gcd_eq_zero_iff.mp h0
    rcases h2ne with h | h <;> exact h (by tauto)
  rcases EuclideanDomain.gcd_dvd_left (D.Bj 2) (D.Cj 2) with ⟨c, hc⟩
  rcases EuclideanDomain.gcd_dvd_right (D.Bj 2) (D.Cj 2) with ⟨b, hb⟩
  have hcb_ne : c ≠ 0 ∨ b ≠ 0 := by
    rcases h2ne with h | h
    · left; intro hc0; rw [hc0, mul_zero] at hc; exact h hc
    · right; intro hb0; rw [hb0, mul_zero] at hb; exact h hb
  have hcop : ∀ d : Polynomial Fld, d ∣ c → d ∣ b → IsUnit d := by
    intro d hdc hdb
    have hd1 : g * d ∣ D.Bj 2 := by rw [hc]; exact mul_dvd_mul_left g hdc
    have hd2 : g * d ∣ D.Cj 2 := by rw [hb]; exact mul_dvd_mul_left g hdb
    have hd : g * d ∣ g := EuclideanDomain.dvd_gcd hd1 hd2
    rcases hd with ⟨u, hu⟩
    exact isUnit_iff_exists_inv.mpr ⟨u, mul_left_cancel₀ hg_ne (by
      calc g * (d * u) = g * d * u := by ring
        _ = g := hu.symm
        _ = g * 1 := (mul_one g).symm)⟩
  have hsyz : ∀ j : Fin 3, c * D.Cj j + b * D.Bj j = 0 := by
    intro j; apply mul_left_cancel₀ hg_ne; rw [mul_zero]
    calc g * (c * D.Cj j + b * D.Bj j) = (g * c) * D.Cj j + (g * b) * D.Bj j := by ring
      _ = D.Bj 2 * D.Cj j + D.Cj 2 * D.Bj j := by rw [← hc, ← hb]
      _ = 0 := hminors j
  set r := std5Slot (G_val D.W_F D.k D.Az) with hr_def
  have ⟨hsD, heD, _, hlo, hhi⟩ := t4_start_end_bounds D hWF_hi
  have ⟨hloGD, hhiGD, hloG, hhiG⟩ := std5Slot_spec (B6402ProfileMatch.nonneg D)
  rw [← hr_def] at hloGD hhiGD hloG hhiG
  rw [←B6402ProfileMatch.gap_eq] at hloG hhiG
  obtain ⟨x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩ :=
    D.table4_p0Zero_sat hcb_ne hcop hsyz T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2
      hsD heD hloGD hhiGD hlo hhi hloG hhiG
  exact t4_witness_of_t4a D r hWF_hi .p0Zero trivial x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq

lemma t4_point_syzygy_witness {D : KerD45Data} (S : KerD45Syzygy D)
    (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5) :
    Assigned D (std5Slot (G_val D.W_F D.k D.Az)) := by
  set r := std5Slot (G_val D.W_F D.k D.Az) with hr_def
  have ⟨hsD, heD, _, hlo, hhi⟩ := t4_start_end_bounds D hWF_hi
  have ⟨hloGD, hhiGD, hloG, hhiG⟩ := std5Slot_spec (B6402ProfileMatch.nonneg D)
  rw [← hr_def] at hloGD hhiGD hloG hhiG
  rw [←B6402ProfileMatch.gap_eq] at hloG hhiG
  rcases table4_algebra_of_syzygy S T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2
      hsD heD hloGD hhiGD hlo hhi hloG hhiG with
    ⟨br, hvalid, x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩ |
    ⟨br, hq1, hode, x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩
  · exact t4_witness_of_t4a D r hWF_hi br hvalid x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq
  · exact t4_witness_of_t4b D r hWF_hi br hq1 hode x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq

lemma t4_point_dichotomy (D : KerD45Data) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5) :
    EscapeUZero D ∨ Assigned D (std5Slot (G_val D.W_F D.k D.Az)) := by
  set r := std5Slot (G_val D.W_F D.k D.Az) with hr_def
  have ⟨hsD, heD, _, hlo, hhi⟩ := t4_start_end_bounds D hWF_hi
  have ⟨hloGD, hhiGD, hloG, hhiG⟩ := std5Slot_spec (B6402ProfileMatch.nonneg D)
  rw [← hr_def] at hloGD hhiGD hloG hhiG
  rw [←B6402ProfileMatch.gap_eq] at hloG hhiG
  rcases table4_algebra_dichotomy D T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2
      hsD heD hloGD hhiGD hlo hhi hloG hhiG with
    hesc |
    ⟨br, hvalid, x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩ |
    ⟨br, hq1, hode, x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩
  · exact Or.inl hesc
  · exact Or.inr (t4_witness_of_t4a D r hWF_hi br hvalid x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq)
  · exact Or.inr (t4_witness_of_t4b D r hWF_hi br hq1 hode x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq)


#print axioms t4_point_syzygy_witness
#print axioms t4_point_dichotomy
end ProximityPrize.SubmissionBinaryLower.B6402SpecialRouting
