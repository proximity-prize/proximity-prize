import ProximityPrize.SubmissionLower.R6970Height2313Main

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

set_option Elab.async false
set_option autoImplicit false

namespace ZGen.Hist
open P1_7_4
open K1_14_2_2_4 (highCap highScale pairCap residualShape)

def qf (a : ℕ × ℕ) : ℚ := (a.1 : ℚ) / (a.2 : ℚ)

def fmax (a b : ℕ × ℕ) : ℕ × ℕ := cond (Nat.ble (Nat.mul b.1 a.2) (Nat.mul a.1 b.2)) a b
def fmin (a b : ℕ × ℕ) : ℕ × ℕ := cond (Nat.ble (Nat.mul a.1 b.2) (Nat.mul b.1 a.2)) a b

theorem fmax_eq (a b : ℕ × ℕ) : fmax a b = if b.1 * a.2 ≤ a.1 * b.2 then a else b := by
  unfold fmax
  by_cases h : b.1 * a.2 ≤ a.1 * b.2
  · simp [Nat.ble_eq, Nat.mul_eq, h]
  · simp [Nat.ble_eq, Nat.mul_eq, h]
theorem fmin_eq (a b : ℕ × ℕ) : fmin a b = if a.1 * b.2 ≤ b.1 * a.2 then a else b := by
  unfold fmin
  by_cases h : a.1 * b.2 ≤ b.1 * a.2
  · simp [Nat.ble_eq, Nat.mul_eq, h]
  · simp [Nat.ble_eq, Nat.mul_eq, h]

theorem qf_le {a b : ℕ × ℕ} (ha : 0 < a.2) (hb : 0 < b.2) :
    qf a ≤ qf b ↔ a.1 * b.2 ≤ b.1 * a.2 := by
  unfold qf
  rw [div_le_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hb)]
  exact_mod_cast Iff.rfl

theorem max_qf {a b : ℕ × ℕ} (ha : 0 < a.2) (hb : 0 < b.2) : max (qf a) (qf b) = qf (fmax a b) := by
  rw [fmax_eq]
  by_cases h : b.1 * a.2 ≤ a.1 * b.2
  · rw [if_pos h]; exact max_eq_left ((qf_le hb ha).2 h)
  · rw [if_neg h]; exact max_eq_right (((qf_le ha hb)).2 (by omega))

theorem min_qf {a b : ℕ × ℕ} (ha : 0 < a.2) (hb : 0 < b.2) : min (qf a) (qf b) = qf (fmin a b) := by
  rw [fmin_eq]
  by_cases h : a.1 * b.2 ≤ b.1 * a.2
  · rw [if_pos h]; exact min_eq_left ((qf_le ha hb).2 h)
  · rw [if_neg h]; exact min_eq_right ((qf_le hb ha).2 (by omega))

theorem fmax_pos {a b : ℕ × ℕ} (ha : 0 < a.2) (hb : 0 < b.2) : 0 < (fmax a b).2 := by
  rw [fmax_eq]; split <;> assumption
theorem fmin_pos {a b : ℕ × ℕ} (ha : 0 < a.2) (hb : 0 < b.2) : 0 < (fmin a b).2 := by
  rw [fmin_eq]; split <;> assumption

theorem foldl_max (L : List (ℕ × ℕ)) (hL : ∀ x ∈ L, 0 < x.2) (init : ℕ × ℕ) (hi : 0 < init.2) :
    L.foldl (fun acc x => max acc (qf x)) (qf init) = qf (L.foldl fmax init) ∧ 0 < (L.foldl fmax init).2 := by
  induction L generalizing init with
  | nil => exact ⟨rfl, hi⟩
  | cons x L ih =>
    have hx := hL x (by simp)
    simp only [List.foldl_cons]
    rw [max_qf hi hx]
    exact ih (fun y hy => hL y (by simp [hy])) _ (fmax_pos hi hx)

theorem foldl_min (L : List ℕ) (g : ℕ → ℚ) (f : ℕ → ℕ × ℕ) (hg : ∀ x ∈ L, g x = qf (f x))
    (hL : ∀ x ∈ L, 0 < (f x).2) (init : ℕ × ℕ) (hi : 0 < init.2) :
    L.foldl (fun acc x => min acc (g x)) (qf init) = qf (L.foldl (fun acc x => fmin acc (f x)) init) ∧
      0 < (L.foldl (fun acc x => fmin acc (f x)) init).2 := by
  induction L generalizing init with
  | nil => exact ⟨rfl, hi⟩
  | cons x L ih =>
    have hx := hL x (by simp)
    simp only [List.foldl_cons]
    rw [hg x (by simp), min_qf hi hx]
    exact ih (fun y hy => hg y (by simp [hy])) (fun y hy => hL y (by simp [hy])) _ (fmin_pos hi hx)

def hcF (x z : ℕ) (k : Fin 4) : ℕ :=
  match k.val with
  | 0 => z
  | 1 => x
  | 2 => Nat.mul (Nat.mul 2 x) z
  | _ => Nat.mul x x

def hsF (r : ℕ) (k : Fin 4) : ℕ :=
  match k.val with
  | 0 => r
  | 1 => r
  | _ => Nat.mul r r

def pcF (sB sJ sU tB tJ tU : ℕ) (k : Fin 4) : ℕ :=
  match k.val with
  | 0 => Nat.sub (Nat.add (Nat.mul sB tJ) (Nat.mul tB sJ)) (Nat.mul sJ tJ)
  | 1 => Nat.add (Nat.mul sU tJ) (Nat.mul tU sJ)
  | 2 => Nat.add (Nat.mul sU tB) (Nat.mul tU sB)
  | _ => Nat.mul sU tU

theorem hcF_eq (x z : ℕ) (k : Fin 4) : hcF x z k = highCap x z k := by
  unfold hcF highCap; fin_cases k <;> rfl
theorem hsF_eq (r : ℕ) (k : Fin 4) : hsF r k = highScale r k := by
  unfold hsF highScale; fin_cases k <;> simp [Nat.mul_eq, pow_two]
theorem pcF_eq (s t : K1_14.Shape) (x z : ℕ) (k : Fin 4) :
    pcF (s.B - z) (min s.J (s.B - z)) (s.U - x) (t.B - z) (min t.J (t.B - z)) (t.U - x) k =
      pairCap (residualShape s x z) (residualShape t x z) k := by
  unfold pcF pairCap residualShape; fin_cases k <;> rfl

def sharedF (s t : K1_14.Shape) (x z r m : ℕ) (square : Bool) (k : Fin 4) : ℕ × ℕ :=
  let n := m + 1 - r
  let d := if (square || k == 3) = true then n ^ 2 else n
  (highCap x z k * d + highScale r k * pairCap (residualShape s x z) (residualShape t x z) k,
    highScale r k * d)

theorem highScale_pos {r : ℕ} (hr : 0 < r) (k : Fin 4) : 0 < highScale r k := by
  unfold highScale
  fin_cases k <;> simp [hr]

theorem shared_eq (s t : K1_14.Shape) (x z r m : ℕ) (square : Bool) (k : Fin 4) (hr : 0 < r) (hrm : r ≤ m) :
    sharedBound s t x z r m square k = qf (sharedF s t x z r m square k) ∧
      0 < (sharedF s t x z r m square k).2 := by
  have hs := highScale_pos hr k
  have hd : 0 < (if (square || k == 3) = true then (m + 1 - r) ^ 2 else m + 1 - r) := by
    split
    · exact pow_pos (by omega) _
    · omega
  refine ⟨?_, Nat.mul_pos hs hd⟩
  unfold sharedBound sharedF qf
  simp only
  rw [div_add_div _ _ (by exact_mod_cast hs.ne') (by exact_mod_cast hd.ne')]
  push_cast
  rfl

def cornerF (s t : K1_14.Shape) (r m : ℕ) (square : Bool) (k : Fin 4) : ℕ × ℕ :=
  let xs := [0, pairMinSeed s t]
  let zMax := pairMinOrdinate s t
  let zs := [0, zMax, min zMax (s.B - s.J), min zMax (t.B - t.J)]
  (xs.flatMap fun x => zs.map fun z => sharedF s t x z r m square k).foldl fmax (0, 1)

theorem corner_eq (s t : K1_14.Shape) (r m : ℕ) (square : Bool) (k : Fin 4) (hr : 0 < r) (hrm : r ≤ m) :
    cornerBound s t r m square k = qf (cornerF s t r m square k) ∧ 0 < (cornerF s t r m square k).2 := by
  unfold cornerBound cornerF
  simp only
  have h : ∀ x z, sharedBound s t x z r m square k = qf (sharedF s t x z r m square k) :=
    fun x z => (shared_eq s t x z r m square k hr hrm).1
  simp only [h]
  have e : (List.flatMap (fun x => List.map (fun z => qf (sharedF s t x z r m square k))
      [0, pairMinOrdinate s t, min (pairMinOrdinate s t) (s.B - s.J), min (pairMinOrdinate s t) (t.B - t.J)])
      [0, pairMinSeed s t]) =
      (List.flatMap (fun x => List.map (fun z => sharedF s t x z r m square k)
      [0, pairMinOrdinate s t, min (pairMinOrdinate s t) (s.B - s.J), min (pairMinOrdinate s t) (t.B - t.J)])
      [0, pairMinSeed s t]).map qf := by
    simp [List.map_flatMap, List.map_map, Function.comp_def]
  rw [e, List.foldl_map]
  have := foldl_max (List.flatMap (fun x => List.map (fun z => sharedF s t x z r m square k)
      [0, pairMinOrdinate s t, min (pairMinOrdinate s t) (s.B - s.J), min (pairMinOrdinate s t) (t.B - t.J)])
      [0, pairMinSeed s t]) (by
        intro y hy
        simp only [List.mem_flatMap, List.mem_map] at hy
        obtain ⟨x, _, z, _, rfl⟩ := hy
        exact (shared_eq s t x z r m square k hr hrm).2) (0, 1) (by decide)
  have h0 : (0 : ℚ) = qf (0, 1) := by simp [qf]
  rw [h0]
  exact this

def pairedF (s t : K1_14.Shape) (reserve : ℕ) (square : Bool) (k : Fin 4) : ℕ × ℕ :=
  let m := reserve + 1
  (List.range m).foldl (fun a r => fmin a (cornerF s t (r + 1) m square k)) (cornerF s t 1 m square k)

theorem paired_eq (s t : K1_14.Shape) (reserve : ℕ) (square : Bool) (k : Fin 4) :
    pairedCap s t reserve square k = qf (pairedF s t reserve square k) ∧ 0 < (pairedF s t reserve square k).2 := by
  unfold pairedCap pairedF
  simp only
  have h1 := corner_eq s t 1 (reserve + 1) square k (by omega) (by omega)
  rw [h1.1]
  exact foldl_min (List.range (reserve + 1)) (fun r => cornerBound s t (r + 1) (reserve + 1) square k)
    (fun r => cornerF s t (r + 1) (reserve + 1) square k)
    (fun r hr => (corner_eq s t (r + 1) (reserve + 1) square k (by omega) (by simp at hr; omega)).1)
    (fun r hr => (corner_eq s t (r + 1) (reserve + 1) square k (by omega) (by simp at hr; omega)).2)
    _ h1.2



def dF (sq : Bool) (k : Fin 4) (m r : ℕ) : ℕ :=
  let n := Nat.sub (Nat.add m 1) r
  cond (sq || Nat.beq k.val 3) (Nat.mul n n) n

theorem dF_eq (sq : Bool) (k : Fin 4) (m r : ℕ) :
    dF sq k m r = if (sq || k == 3) = true then (m + 1 - r) ^ 2 else m + 1 - r := by
  unfold dF
  cases sq <;> fin_cases k <;> simp [pow_two]

def cornerList (s t : K1_14.Shape) (k : Fin 4) : List (ℕ × ℕ) :=
  [0, Nat.min s.U t.U].flatMap fun x =>
    [0, Nat.min s.B t.B, Nat.min (Nat.min s.B t.B) (Nat.sub s.B s.J), Nat.min (Nat.min s.B t.B) (Nat.sub t.B t.J)].map fun z =>
      (hcF x z k, pcF (Nat.sub s.B z) (Nat.min s.J (Nat.sub s.B z)) (Nat.sub s.U x)
        (Nat.sub t.B z) (Nat.min t.J (Nat.sub t.B z)) (Nat.sub t.U x) k)

def cornerG (cs : List (ℕ × ℕ)) (hs d : ℕ) : ℕ × ℕ :=
  (cs.map fun c => (Nat.add (Nat.mul c.1 d) (Nat.mul hs c.2), Nat.mul hs d)).foldl fmax (0, 1)

theorem cornerG_eq (s t : K1_14.Shape) (r m : ℕ) (sq : Bool) (k : Fin 4) :
    cornerG (cornerList s t k) (hsF r k) (dF sq k m r) = cornerF s t r m sq k := by
  unfold cornerG cornerList cornerF
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  have h : ∀ x z, (Nat.add (Nat.mul (hcF x z k) (dF sq k m r))
      (Nat.mul (hsF r k) (pcF (Nat.sub s.B z) (Nat.min s.J (Nat.sub s.B z)) (Nat.sub s.U x)
        (Nat.sub t.B z) (Nat.min t.J (Nat.sub t.B z)) (Nat.sub t.U x) k)), Nat.mul (hsF r k) (dF sq k m r))
      = sharedF s t x z r m sq k := by
    intro x z
    unfold sharedF
    rw [dF_eq, hcF_eq, hsF_eq, ← pcF_eq]
    rfl
  simp only [h]
  rfl

def pairedG (s t : K1_14.Shape) (reserve : ℕ) (sq : Bool) (k : Fin 4) : ℕ × ℕ :=
  let m := reserve + 1
  let cs := cornerList s t k
  (List.range m).foldl (fun a r => fmin a (cornerG cs (hsF (r + 1) k) (dF sq k m (r + 1))))
    (cornerG cs (hsF 1 k) (dF sq k m 1))

theorem pairedG_eq (s t : K1_14.Shape) (reserve : ℕ) (sq : Bool) (k : Fin 4) :
    pairedG s t reserve sq k = pairedF s t reserve sq k := by
  unfold pairedG pairedF
  simp only [cornerG_eq]

open Lower6960.Prefix6969Main in
/-- Kernel-fast check of `Plan.Valid.history_step`. -/
def histOK (s : Plan) : Bool :=
  (List.finRange s.last).all fun i =>
    (List.finRange 4).all fun k =>
      let j : Fin s.count := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      let h := s.history i.val k
      let h' := s.history (i.val + 1) k
      let P := pairedG (s.freeShape j) (s.movingShape j) (s.reserve j) true k
      let M := fmin (h.num.toNat, h.den) P
      decide (0 ≤ h.num) && decide (0 ≤ h'.num) && (h'.num.toNat * M.2 == M.1 * h'.den)

theorem rat_eq_qf (h : ℚ) (hn : 0 ≤ h.num) : h = qf (h.num.toNat, h.den) := by
  unfold qf
  simp only
  have : ((h.num.toNat : ℕ) : ℚ) = (h.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  rw [this]
  exact (Rat.num_div_den h).symm

open Lower6960.Prefix6969Main in
theorem history_step_of_fast (s : Plan) (h : histOK s = true) :
    ∀ (i : Fin s.last) (k : Fin 4),
      let j : Fin s.count := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      s.history (i.val + 1) k = min (s.history i.val k)
        (pairedCap (s.freeShape j) (s.movingShape j) (s.reserve j) true k) := by
  intro i k j
  unfold histOK at h
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_finRange i)
  rw [List.all_eq_true] at h1
  have h2 := h1 k (List.mem_finRange k)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
  obtain ⟨⟨hn, hn'⟩, he⟩ := h2
  rw [pairedG_eq] at he
  obtain ⟨hp, hpos⟩ := paired_eq (s.freeShape j) (s.movingShape j) (s.reserve j) true k
  have hh : 0 < (s.history i.val k).den := Rat.den_pos _
  have hh' : 0 < (s.history (i.val + 1) k).den := Rat.den_pos _
  rw [hp, rat_eq_qf (s.history i.val k) hn, min_qf hh hpos]
  set M := fmin ((s.history i.val k).num.toNat, (s.history i.val k).den)
    (pairedF (s.freeShape j) (s.movingShape j) (s.reserve j) true k) with hM
  have hMpos : 0 < M.2 := fmin_pos hh hpos
  rw [rat_eq_qf _ hn']
  unfold qf
  simp only
  rw [div_eq_div_iff (by exact_mod_cast hh'.ne') (by exact_mod_cast hMpos.ne')]
  exact_mod_cast he

end ZGen.Hist

set_option Elab.async false
set_option autoImplicit false

namespace Lower6960.Prefix6969Main
noncomputable section
open K1 (p)
open P1_7_4 (dotQ)

/-- First two conjuncts of `Pricing.Valid.rates`, decided once for all stages
(the shared `seedLimit` is then evaluated a single time). -/
def RatesAB (x : Pricing) (s : Plan) : Prop :=
  ∀ i : Fin s.count, ((p+1 : ℕ) : ℚ)/81 ≤ (x.degreeRate i.val : ℚ) ∧
      min s.seedLimit (dotQ (s.cutWeight 0 i.val) (s.history i.val)) ≤ (x.degreeRate i.val : ℚ)

instance (x : Pricing) (s : Plan) : Decidable (RatesAB x s) := by unfold RatesAB; infer_instance

end
end Lower6960.Prefix6969Main

end Research6970.Height2313
