import ProximityPrize.SubmissionLower.Numeric2Aux
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6
open scoped BigOperators
open CJ0 (Jet blockRows blockCols blockMatrix)
open CJ1 (total total_eq_sum)
private theorem row_bounds (q u c d h : ℕ)
    (hr : (⟨c,d,h⟩ : Jet) ∈ blockRows 52 q ((u : ℤ)-20)) :
    h < q+1 ∧ rowLo q u h ≤ d ∧ d < rowHi q u h ∧ q-(h+d) = c := by
  simp only [blockRows, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
    Finset.mem_singleton, Jet.v, Jet.b, Jet.c, Jet.a, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hr
  unfold rowLo rowHi
  omega
private theorem col_bounds (q u c b a : ℕ)
    (hs : (⟨c,b,a⟩ : Jet) ∈ blockCols source q ((u : ℤ)-20)) :
    b < min q 20 + 1 ∧ colLo u b ≤ c ∧ c < colHi q b ∧ q-(b+c) = a := by
  change (⟨c,b,a⟩ : Jet) ∈ (CJ0.fullBox 71 20 9).filter _ at hs
  rw [Finset.mem_filter, CJ0.mem_fullBox (by decide) (by decide)] at hs
  simp only [Jet.q, Jet.v, Jet.a, Jet.b, Jet.c, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hs
  unfold colLo colHi
  omega
private def rowIndex (q u : ℕ) :
    ↥(blockRows 52 q ((u : ℤ)-20)) → Row q u
  | ⟨⟨c,d,h⟩, hr⟩ =>
    let H := row_bounds q u c d h hr
    ⟨⟨h,H.1⟩, ⟨d-rowLo q u h, by
      change d - rowLo q u h < rowHi q u h - rowLo q u h
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private def colIndex (q u : ℕ) :
    ↥(blockCols source q ((u : ℤ)-20)) → Col q u
  | ⟨⟨c,b,a⟩, hs⟩ =>
    let H := col_bounds q u c b a hs
    ⟨⟨b,H.1⟩, ⟨c-colLo u b, by
      change c - colLo u b < colHi q b - colLo u b
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private theorem rowJet_index (q u : ℕ) (r : ↥(blockRows 52 q ((u : ℤ)-20))) :
    rowJet q u (rowIndex q u r) = r.val := by
  rcases r with ⟨⟨c,d,h⟩,hr⟩
  obtain ⟨_, hlo, _, hc⟩ := row_bounds q u c d h hr
  change (⟨q-(h+(rowLo q u h+(d-rowLo q u h))),rowLo q u h+(d-rowLo q u h),h⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, hc]
private theorem colJet_index (q u : ℕ) (s : ↥(blockCols source q ((u : ℤ)-20))) :
    colJet q u (colIndex q u s) = s.val := by
  rcases s with ⟨⟨c,b,a⟩,hs⟩
  obtain ⟨_, hlo, _, ha⟩ := col_bounds q u c b a hs
  change (⟨colLo u b+(c-colLo u b),b,q-(b+(colLo u b+(c-colLo u b)))⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, ha]
theorem block_rank_le (q u : ℕ) :
    (blockMatrix source q ((u : ℤ)-20)).rank ≤ (packet q u).rank := by
  have he : blockMatrix source q ((u : ℤ)-20) =
      (packet q u).submatrix (rowIndex q u) (colIndex q u) := by
    ext r s
    change CJ0.blockEntry r.val s.val =
      CJ0.blockEntry (rowJet q u (rowIndex q u r)) (colJet q u (colIndex q u s))
    exact congrArg₂ CJ0.blockEntry (rowJet_index q u r).symm (colJet_index q u s).symm
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _
theorem card_row (q u : ℕ) : Fintype.card (Row q u) = rows q u := by
  simp only [Row, Fintype.card_sigma, Fintype.card_fin, rows, total_eq_sum,
    Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
theorem card_col (q u : ℕ) : Fintype.card (Col q u) = cols q u := by
  simp only [Col, Fintype.card_sigma, Fintype.card_fin, cols, total_eq_sum,
    Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
end CJ6
end
section
namespace CJ6.Packed
open Polynomial
open scoped Polynomial
theorem digit_eval (F : ℕ[X]) (B n : ℕ) (h : F.eval 1 < B) :
    F.eval B / B^n % B = F.coeff n := by
  have decomp (P : ℕ[X]) (x : ℕ) : P.eval x = P.coeff 0 + x * P.divX.eval x := by
    simpa [add_comm] using (congrArg (eval x) (X_mul_divX_add P)).symm
  induction n generalizing F with
  | zero =>
    have hh := decomp F 1
    simp only [one_mul] at hh
    have hh' : F.coeff 0 < B := by omega
    simp [decomp F B, Nat.mod_eq_of_lt hh']
  | succ n ih =>
    have hh := decomp F 1
    simp only [one_mul] at hh
    have h₀ : F.coeff 0 < B := by omega
    have hd : F.divX.eval 1 < B := by omega
    have hb : 0 < B := by omega
    rw [pow_succ', ← Nat.div_div_eq_div_mul, decomp F B, Nat.add_mul_div_left _ _ hb,
      Nat.div_eq_of_lt h₀, zero_add, ih _ hd, coeff_divX]
def signWeight (c w : ℕ) : ℕ :=
  if c % 2 = 0 then w else (CJ0.p - 1) * w
private theorem signWeight_cast (c w : ℕ) :
    (signWeight c w : ZMod CJ0.p) = (-1)^c * (w : ZMod CJ0.p) := by
  have hp : ((CJ0.p-1 : ℕ) : ZMod CJ0.p) = -1 := by
    rw [Nat.cast_sub (by decide : 1 ≤ CJ0.p), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have parity : (-1 : ZMod CJ0.p)^c = (-1)^(c%2) := by
    conv_lhs => rw [← Nat.mod_add_div c 2, pow_add, pow_mul]
    simp
  rw [parity]
  by_cases h : c % 2 = 0
  · simp [signWeight, h]
  · have h' : c % 2 = 1 := by omega
    rw [signWeight, if_neg h, Nat.cast_mul, hp, h', pow_one]
def shift (left : Bool) (q b : ℕ) : ℕ := if left then q-b else b
def slice (left : Bool) (outA inA : ℕ) : ℕ × ℕ :=
  if left then (outA,inA) else (inA,outA)
noncomputable def piece (left : Bool) (outA inA pos w : ℕ) : ℕ[X] :=
  let (a,h) := slice left outA inA
  C (CJ1.fastChoose a h * w) * (1+(Polynomial.X : Polynomial ℕ))^(a-h) * (Polynomial.X : Polynomial ℕ)^pos
def factor (left : Bool) (x outA inA : ℕ) : ℕ :=
  let (a,h) := slice left outA inA
  CJ1.fastChoose a h * (1+x)^(a-h)
theorem eval_piece (left : Bool) (outA inA pos w x : ℕ) :
    (piece left outA inA pos w).eval x = factor left x outA inA * (w * x^pos) := by
  cases left <;> simp [piece, slice, factor] <;> ring
private theorem fastChoose_eq (n k : ℕ) : CJ1.fastChoose n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm
theorem coeff_entry (left : Bool) (q : ℕ) (o v : CJ0.Jet) (w : ℕ)
    (ho : o.q = q) (hv : v.q = q) :
    (((piece left o.a v.a (shift left q v.b) (signWeight v.c w)).coeff
        (shift left q o.b) : ℕ) : ZMod CJ0.p) =
      (-1)^(o.c) * (((if left then CJ1.entryZ v o else CJ1.entryZ o v : ℤ) : ZMod CJ0.p)) * w := by
  have aux (r c : CJ0.Jet) (hr : r.q = q) (hc : c.q = q) :
      (if c.b ≤ r.b then c.a.choose r.a * (c.a-r.a).choose (r.b-c.b) else 0) =
      (if c.b ≤ r.b ∧ c.c ≤ r.c ∧ r.a + (r.b-c.b) + (r.c-c.c) = c.a then
        c.a.choose r.a * (c.a-r.a).choose (r.b-c.b) else 0) := by
    unfold CJ0.Jet.q at hr hc
    split_ifs with hb hcond
    · rfl
    · by_cases ha : c.a < r.a
      · simp [Nat.choose_eq_zero_of_lt ha]
      · have hbad : c.a-r.a < r.b-c.b := by omega
        simp [Nat.choose_eq_zero_of_lt hbad]
    · omega
    · rfl
  have sign (r c : ℕ) (hc : c ≤ r) :
      (-1 : ZMod CJ0.p)^r * (-1)^(r-c) = (-1)^c := by
    conv_lhs => lhs; rw [← Nat.sub_add_cancel hc, pow_add]
    have h : (-1 : ZMod CJ0.p)^(r-c) * (-1)^(r-c) = 1 := by
      rw [← mul_pow]; simp
    calc
      _ = ((-1 : ZMod CJ0.p)^(r-c) * (-1)^(r-c)) * (-1)^c := by ring
      _ = _ := by rw [h, one_mul]
  have sign' (r c : ℕ) (hc : c ≤ r) :
      (-1 : ZMod CJ0.p)^c * (-1)^(r-c) = (-1)^r := by
    rw [← pow_add, Nat.add_sub_of_le hc]
  have scalar (r c : CJ0.Jet) (hr : r.q = q) (hc : c.q = q) (s t : ℕ)
      (hs : c.c ≤ r.c → (-1 : ZMod CJ0.p)^s * (-1)^(r.c-c.c) = (-1)^t) :
      ((if c.b ≤ r.b then c.a.choose r.a * signWeight t w * (c.a-r.a).choose (r.b-c.b)
          else 0 : ℕ) : ZMod CJ0.p) = (-1)^s * (CJ1.entryZ r c : ZMod CJ0.p) * w := by
    have pull : (if c.b ≤ r.b then c.a.choose r.a * signWeight t w * (c.a-r.a).choose (r.b-c.b)
          else 0) = (if c.b ≤ r.b then c.a.choose r.a * (c.a-r.a).choose (r.b-c.b)
          else 0) * signWeight t w := by split <;> ring
    rw [pull, aux r c hr hc, CJ1.entryZ]
    split_ifs with hg
    · simp only [Nat.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
          Int.cast_natCast, signWeight_cast, fastChoose_eq, ← hs hg.2.1]
      ring
    · simp
  have hob : o.b ≤ q := by unfold CJ0.Jet.q at ho; omega
  have hvb : v.b ≤ q := by unfold CJ0.Jet.q at hv; omega
  cases left <;> simp only [piece, slice, shift, Bool.false_eq_true,
    ite_false, ite_true, coeff_mul_X_pow', coeff_C_mul, coeff_one_add_X_pow, Nat.cast_id, fastChoose_eq]
  · exact scalar o v ho hv o.c v.c (sign o.c v.c)
  · simp only [show (q-v.b ≤ q-o.b) ↔ o.b ≤ v.b by omega,
      show q-o.b-(q-v.b) = v.b-o.b by omega]
    exact scalar v o hv ho o.c v.c (sign' v.c o.c)
end CJ6.Packed
end
section
namespace CJ6.Packed
open Polynomial
abbrev Input := CJ0.Jet × ℕ
abbrev Bucket := ℕ × ℕ × ℕ
abbrev Band := ℕ × List ℕ
def radix : ℕ := 2^192
def insert (a s v : ℕ) : List Bucket → List Bucket
  | [] => [(a,s,v)]
  | (k,t,w)::bs => if a = k then (k,s+t,v+w)::bs else (k,t,w)::insert a s v bs
def pack (left : Bool) (q : ℕ) : List Input → List Bucket
  | [] => []
  | (j,w)::xs =>
    let v := signWeight j.c w
    insert j.a v (v * radix^(shift left q j.b)) (pack left q xs)
def value (big : Bool) (f : ℕ → ℕ) : List Bucket → ℕ
  | [] => 0
  | (a,s,v)::bs => f a * (if big then v else s) + value big f bs
private theorem value_insert (big : Bool) (f : ℕ → ℕ) (a s v : ℕ) (bs : List Bucket) :
    value big f (insert a s v bs) = f a * (if big then v else s) + value big f bs := by
  induction bs with
  | nil => simp [insert, value]
  | cons b bs ih =>
    obtain ⟨k,t,w⟩ := b
    by_cases h : a = k <;> cases big <;> simp [insert, value, h, ih, Nat.mul_add] <;> omega
noncomputable def poly (left : Bool) (q outA : ℕ) : List Input → Polynomial ℕ
  | [] => 0
  | (j,w)::xs => piece left outA j.a (shift left q j.b) (signWeight j.c w) + poly left q outA xs
theorem value_pack (big left : Bool) (q a : ℕ) (xs : List Input) :
    value big (factor left (if big then radix else 1) a) (pack left q xs) =
      (poly left q a xs).eval (if big then radix else 1) := by
  induction xs with
  | nil => simp [poly, pack, value]
  | cons v xs ih =>
    obtain ⟨j,w⟩ := v
    simp only [pack, poly, value_insert, eval_add, ih, eval_piece]
    cases big <;> simp
def checkBand (left : Bool) (bs : List Bucket) (band : Band) : Bool :=
  let a := band.1
  let s := value false (factor left 1 a) bs
  let v := value true (factor left radix a) bs
  decide (s < radix) && band.2.all (fun t => v / radix^t % radix % CJ0.p == 0)
theorem band_sound {left : Bool} {q : ℕ} {xs : List Input} {bands : List Band}
    (h : bands.all (checkBand left (pack left q xs)) = true)
    {a t : ℕ} (hm : ∃ b ∈ bands, b.1 = a ∧ t ∈ b.2) :
    (poly left q a xs).coeff t % CJ0.p = 0 := by
  obtain ⟨⟨a',ts⟩, hb, rfl, ht⟩ := hm
  have hb' := List.all_eq_true.mp h _ hb
  simp only [checkBand, Bool.and_eq_true, decide_eq_true_eq] at hb'
  have h₁ := value_pack false left q a' xs
  have h₂ := value_pack true left q a' xs
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
  obtain ⟨hsize, hd⟩ := hb'
  have ht' := List.all_eq_true.mp hd _ ht
  simp only [beq_iff_eq] at ht'
  rw [h₁] at hsize
  rwa [h₂, digit_eval _ _ _ hsize] at ht'
def covers (left : Bool) (q : ℕ) (bands : List Band) (j : CJ0.Jet) : Bool :=
  j.q == q && bands.any (fun b => b.1 == j.a && b.2.contains (shift left q j.b))
def axisList {α : Type} (n : ℕ) (len : ℕ → ℕ) (f : ℕ → ℕ → α) : List α :=
  (List.range n).flatMap (fun i => (List.range (len i)).map (f i))
theorem mem_axis {α : Type} {n : ℕ} {len : ℕ → ℕ} {f : ℕ → ℕ → α}
    {i k : ℕ} (hi : i < n) (hk : k < len i) : f i k ∈ axisList n len f := by
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩
theorem sum_axis {α M : Type} [AddCommMonoid M] (g : α → M)
    (n : ℕ) (len : ℕ → ℕ) (f : ℕ → ℕ → α) :
    ((axisList n len f).map g).sum =
      CJ1.total (fun i => CJ1.total (fun k => g (f i k)) (len i)) n := by
  have inner (i m : ℕ) : (((List.range m).map (f i)).map g).sum =
      CJ1.total (fun k => g (f i k)) m := by
    induction m with
    | zero => rfl
    | succ m ih => simpa only [List.range_succ, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, CJ1.total] using (congrArg (· + g (f i m)) ih)
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [axisList, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append, List.sum_append, inner, CJ1.total]
    exact congrArg (· + _) ih
def intTerm (left : Bool) (o : CJ0.Jet) (vw : Input) : ℤ :=
  (if left then CJ1.entryZ vw.1 o else CJ1.entryZ o vw.1) * (vw.2 : ℤ)
theorem coeff_sum (left : Bool) (q : ℕ) (o : CJ0.Jet) (xs : List Input) (ho : o.q = q)
    (hx : ∀ v ∈ xs, v.1.q = q) :
    (((poly left q o.a xs).coeff (shift left q o.b) : ℕ) : ZMod CJ0.p) =
      (-1)^o.c * (((xs.map (intTerm left o)).sum : ℤ) : ZMod CJ0.p) := by
  induction xs with
  | nil => simp [poly]
  | cons v xs ih =>
    obtain ⟨j,w⟩ := v
    rw [poly, coeff_add, Nat.cast_add, coeff_entry left q o j w ho (hx (j,w) (by simp)),
      ih (fun v hv => hx v (by simp [hv]))]
    simp only [List.map_cons, List.sum_cons, Int.cast_add, intTerm, Int.cast_mul,
      Int.cast_natCast, mul_add, mul_assoc]
theorem int_sum_zero {left : Bool} {q : ℕ} {o : CJ0.Jet} {xs : List Input} {bands : List Band}
    (hi : xs.all (fun v => v.1.q == q) = true)
    (hc : covers left q bands o = true)
    (hb : bands.all (checkBand left (pack left q xs)) = true) :
    (xs.map (intTerm left o)).sum % (CJ0.p : ℤ) = 0 := by
  simp only [covers, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.contains_iff_mem] at hc
  have hz := band_sound hb hc.2
  have hcast : (((poly left q o.a xs).coeff (shift left q o.b) : ℕ) : ZMod CJ0.p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hz)
  rw [coeff_sum left q o xs hc.1 (fun v hv => beq_iff_eq.mp (List.all_eq_true.mp hi v hv))] at hcast
  have hu : IsUnit ((-1 : ZMod CJ0.p)^o.c) := (isUnit_one.neg).pow _
  have hzero := hu.mul_right_eq_zero.mp hcast
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero)
end CJ6.Packed
end
section
namespace CJ6
open CJ1 (Block total total_eq_sum fastChoose entryZ right_witness)
open scoped BigOperators
local instance : Fact (Nat.Prime CJ0.p) := ⟨KoalaBear.is_prime⟩
def Guard (q u : ℕ) (z : Block) : Prop :=
  total (fiber z.bank.onRows q u) (outer z.bank.onRows q) ≤ z.cap + z.free.length ∧
  (∀ j : Fin z.free.length,
    z.free[j].1 < outer z.bank.onRows q ∧
    z.free[j].2 < fiber z.bank.onRows q u z.free[j].1) ∧
  ∀ j k : Fin z.free.length, z.coeff k z.free[j].1 z.free[j].2 = if j = k then 1 else 0
instance (q u : ℕ) (z : Block) : Decidable (Guard q u z) := by
  unfold Guard
  infer_instance
private theorem entryZ_cast (r c : CJ0.Jet) : (entryZ r c : ZMod CJ0.p) = CJ0.blockEntry r c := by
  unfold entryZ CJ0.blockEntry
  split <;> simp [fastChoose, ← Nat.choose_eq_descFactorial_div_factorial, *]
private def oriented (side : Bool) (q u : ℕ) :
    Matrix (Axis (!side) q u) (Axis side q u) (ZMod CJ0.p) :=
  fun r c => (orientedEntry side q u r.1 r.2 c.1 c.2 : ZMod CJ0.p)
private theorem oriented_rank (side : Bool) (q u : ℕ) :
    (oriented side q u).rank = (packet q u).rank := by
  cases side
  · have he : oriented false q u = packet q u := by
      ext r c
      exact entryZ_cast _ _
    rw [he]
    rfl
  · have he : oriented true q u = (packet q u).transpose := by
      ext r c
      exact entryZ_cast _ _
    rw [he]
    exact Matrix.rank_transpose _
private def vectors (q u : ℕ) (z : Block) :
    Matrix (Axis z.bank.onRows q u) (Fin z.free.length) (ZMod CJ0.p) :=
  fun c j => (z.coeff j c.1 c.2 : ZMod CJ0.p)
private theorem sum_axis {α : Type*} [AddCommMonoid α] (side : Bool) (q u : ℕ) (f : ℕ → ℕ → α) :
    (∑ x : Axis side q u, f x.1 x.2) =
      total (fun i => total (f i) (fiber side q u i)) (outer side q) := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma, total_eq_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [total_eq_sum, ← Fin.sum_univ_eq_sum_range]
private theorem mul_eq_dot (q u : ℕ) (z : Block) (r : Axis (!z.bank.onRows) q u)
    (j : Fin z.free.length) :
    (oriented z.bank.onRows q u * vectors q u z) r j = (dot q u z j r.1 r.2 : ZMod CJ0.p) := by
  rw [Matrix.mul_apply, dot, ← sum_axis, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro c _
  change (orientedEntry z.bank.onRows q u r.1 r.2 c.1 c.2 : ZMod CJ0.p) * (z.coeff j c.1 c.2 : ZMod CJ0.p) = _
  by_cases hh : z.coeff j c.1 c.2 = 0 <;> simp [hh]
theorem rank_of_dots {q u : ℕ} {z : Block} (hg : Guard q u z) (hd : Dots q u z) :
    (packet q u).rank ≤ z.cap := by
  obtain ⟨hsize, hfree, hid⟩ := hg
  let f (j : Fin z.free.length) : Axis z.bank.onRows q u :=
    ⟨⟨z.free[j].1,(hfree j).1⟩, ⟨z.free[j].2,(hfree j).2⟩⟩
  have hm : oriented z.bank.onRows q u * vectors q u z = 0 := by
    ext r j
    rw [mul_eq_dot, Matrix.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_of_emod_eq_zero (hd j j.isLt r.1 r.1.isLt r.2 r.2.isLt)
  have hi : (vectors q u z).submatrix f id = 1 := by
    ext j k
    change (z.coeff k z.free[j].1 z.free[j].2 : ZMod CJ0.p) = _
    rw [hid]
    by_cases h : j = k <;> simp [Matrix.one_apply, h]
  have hr := right_witness (oriented z.bank.onRows q u) (vectors q u z) f hm hi
  have hc (side : Bool) :
      Fintype.card (Axis side q u) = total (fiber side q u) (outer side q) := by
    cases side
    · exact card_col q u
    · exact card_row q u
  rw [hc, oriented_rank] at hr
  exact Nat.le_of_add_le_add_right (hr.trans hsize)
end CJ6
end
section
namespace CJ6.Fast
open CJ6 (rowAt colAt outer fiber dot VectorDots orientedEntry)
open CJ1 (Block total)
open CJ6.Packed
def point (row : Bool) (q u i k : ℕ) : CJ0.Jet := if row then rowAt q u i k else colAt q u i k
def inputs (q u : ℕ) (z : Block) (j : ℕ) : List Input :=
  axisList (outer z.bank.onRows q) (fiber z.bank.onRows q u)
    (fun i k => (point z.bank.onRows q u i k, z.coeff j i k))
def outputs (q u : ℕ) (z : Block) : List CJ0.Jet :=
  axisList (outer (!z.bank.onRows) q) (fiber (!z.bank.onRows) q u) (point (!z.bank.onRows) q u)
private theorem dot_eq (q u : ℕ) (z : Block) (j i k : ℕ) :
    dot q u z j i k = ((inputs q u z j).map (intTerm z.bank.onRows (point (!z.bank.onRows) q u i k))).sum := by
  rw [inputs, CJ6.Packed.sum_axis, dot]
  congr 1
  funext b
  congr 1
  funext t
  by_cases h : z.coeff j b t = 0
  · simp [h, intTerm]
  · cases hs : z.bank.onRows <;> simp [h, intTerm, point, orientedEntry]
theorem vector {q u : ℕ} {z : Block} {j : ℕ} (bands : List Band) (bs : List Bucket)
    (hi : (inputs q u z j).all (fun v => v.1.q == q) = true)
    (hc : (outputs q u z).all (covers z.bank.onRows q bands) = true)
    (hp : pack z.bank.onRows q (inputs q u z j) = bs)
    (hb : bands.all (checkBand z.bank.onRows bs) = true) : VectorDots q u z j := by
  intro i hᵢ k hₖ
  rw [dot_eq]
  subst bs
  apply int_sum_zero hi _ hb
  apply List.all_eq_true.mp hc
  exact mem_axis hᵢ hₖ
end CJ6.Fast
end
section
namespace CJ6.Fast
structure Lane where
  a : ℕ
  pos : ℕ
  n : ℕ
  width : ℕ
  digits : ℕ
private def expand (w : ℕ) : ℕ → Bool → ℕ → ℕ × ℕ
  | 0, _, _ => (0,0)
  | n+1, odd, x =>
    let v := x % 2^w
    let v := if odd then (CJ0.p-1)*v else v
    let t := expand w n (!odd) (x >>> w)
    (v+t.1, v+(t.2 <<< 192))
def bucket (left : Bool) (q : ℕ) (l : Lane) : CJ6.Packed.Bucket :=
  let c := if left then l.pos-l.a else q-l.a-l.pos
  let t := expand l.width l.n (c%2 == 1) l.digits
  (l.a, t.1, t.2 <<< (192*l.pos))
def buckets (left : Bool) (q : ℕ) (ls : List Lane) := ls.map (bucket left q)
def good (left : Bool) (q : ℕ) (ls : List Lane) (bs : List CJ6.Packed.Band) : Prop :=
  bs.all (CJ6.Packed.checkBand left (buckets left q ls)) = true
end CJ6.Fast
end
section
namespace CJ6
theorem belowZero {P : ℕ → Prop} : ∀ i < 0, P i := by omega
theorem belowSucc {P : ℕ → Prop} {n : ℕ} (h : ∀ i < n, P i) (hlast : P n) :
    ∀ i < n+1, P i := by
  intro i hi
  by_cases he : i = n
  · simpa only [he] using hlast
  · exact h i (by omega)
end CJ6
end
section
namespace CJ6
open CJ1 (total)
private def triangle (n : ℕ) := n*(n-1)/2
private theorem triangle_succ (n : ℕ) : triangle (n+1) = n + triangle n := by
  simp only [triangle, ← Nat.choose_two_right, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
private def ramp (s a b n : ℕ) :=
  let t := (b-a+s-1)/s
  let d := n-t
  d*(a+s*t-b) + s*triangle d
private theorem ramp_eq (s a b n : ℕ) (hs : s=1 ∨ s=2) :
    total (fun i => a+s*i-b) n = ramp s a b n := by
  let t := (b-a+s-1)/s
  have ht₀ : b ≤ a+s*t := by dsimp [t]; rcases hs with rfl|rfl <;> omega
  have ht₁ (i : ℕ) (hi : i < t) : a+s*i ≤ b := by
    dsimp [t] at hi
    rcases hs with rfl|rfl <;> omega
  change _ = (n-t)*(a+s*t-b) + s*triangle (n-t)
  induction n with
  | zero => simp [total, triangle]
  | succ n ih =>
    rw [total, ih]
    by_cases hn : n < t
    · have h₀ : n-t = 0 := by omega
      have h₁ : n+1-t = 0 := by omega
      simp [h₀, h₁, Nat.sub_eq_zero_of_le (ht₁ n hn)]
    · have hd : n+1-t = (n-t)+1 := by omega
      have hv : a+s*n-b = (a+s*t-b) + s*(n-t) := by
        rcases hs with rfl|rfl <;> omega
      rw [hd, triangle_succ, Nat.add_mul, one_mul, Nat.mul_add, hv]
      omega
private def quickRows (q u : ℕ) :=
  let a := u+2*q+1
  let n := q+1
  ramp 1 a 20 n + ramp 2 a (72+n) n - (ramp 2 a (20+n) n + ramp 1 a 72 n)
private theorem quickRows_eq (q u : ℕ) : rows q u = quickRows q u := by
  let a := u+2*q+1
  let n := q+1
  have summation (j : ℕ) (hj : j ≤ n) :
      total (rowLen q u) j + total (fun h => a+2*h-(20+n)) j +
        total (fun h => a+1*h-72) j =
      total (fun h => a+1*h-20) j + total (fun h => a+2*h-(72+n)) j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hi := ih (by omega)
      have cell : rowLen q u j + (a+2*j-(20+n)) + (a+1*j-72) =
          (a+1*j-20) + (a+2*j-(72+n)) := by
        dsimp [rowLen, rowHi, rowLo, a, n] at *
        omega
      simp only [total] at ⊢
      omega
  have eq := summation n (Nat.le_refl _)
  rw [ramp_eq 2 _ _ _ (Or.inr rfl), ramp_eq 1 _ _ _ (Or.inl rfl),
      ramp_eq 1 _ _ _ (Or.inl rfl), ramp_eq 2 _ _ _ (Or.inr rfl)] at eq
  change total (rowLen q u) n = ramp 1 a 20 n + ramp 2 a (72+n) n - (ramp 2 a (20+n) n + ramp 1 a 72 n)
  omega
private theorem cols_large (q u : ℕ) (hq : 20 ≤ q) : cols q u = cols 20 (min u 20) := by
  unfold cols
  rw [min_eq_right hq]
  congr 1
  funext b
  unfold colLen colHi colLo
  omega
private def colTable (u : ℕ) : ℕ := (0x78777674726f6c68645f5a544e47403830271e140a >>> (8*u)) % 256
private theorem colTable_eq : ∀ u < 21, cols 20 u = colTable u :=
  (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowZero (P := fun u => cols 20 u = colTable u)) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl)
private def quickCols (q u : ℕ) := if q < 20 then cols q u else colTable (min u 20)
private theorem quickCols_eq (q u : ℕ) : cols q u = quickCols q u := by
  unfold quickCols
  split
  · rfl
  · exact (cols_large _ _ (by omega)).trans (colTable_eq _ (by omega))
private def quickGrade (q : ℕ) := total (fun u =>
  boundIn q u (min (quickRows q u) (quickCols q u)) (cells q)) (72-q)
private theorem grade_eq_quick (q : ℕ) : grade q = quickGrade q := by
  unfold grade quickGrade allowance nominal
  simp only [quickRows_eq, quickCols_eq]
private theorem step {n s x y : ℕ} (hs : total grade n = s)
    (hx : quickGrade n = x) (hy : s + x = y) : total grade (n+1) = y := by
  rw [total, hs, grade_eq_quick, hx, hy]
local notation "row!" p "," v => step p (x := v) rfl rfl
end CJ6
end
section
namespace CJ6
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
end CJ6
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3
open scoped BigOperators
private def fastDen (u : ℤ) : ℤ :=
  if u < 0 then 0 else (u * (u * (2 * u + 21) + 66) + 72) / 72
private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem fastDen_eq (u : ℤ) : fastDen u = denominator u := by
  by_cases hu : u < 0
  · simp [fastDen, denominator, hu]
  simp only [fastDen, denominator, hu, ite_false]
  let q := u / 6
  let r := u % 6
  have hr : 0 ≤ r ∧ r < 6 := by dsimp [r]; omega
  have hu' : u = 6 * q + r := by dsimp [q, r]; omega
  have h₁ := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at h₁
  let d := 1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)
  change (u * (u * (2 * u + 21) + 66) + 72) / 72 = d
  have hpoly : u * (u * (2 * u + 21) + 66) + 72 =
      72 * d + r * (r * (2 * r - 15) + 30) := by
    rw [hu']
    dsimp only [d]
    linear_combination -36 * (h₁ + q * twice_half r + (57 + 6 * r) * twice_half q)
  rw [hpoly]
  have hc : 0 ≤ r * (r * (2 * r - 15) + 30) ∧
      r * (r * (2 * r - 15) + 30) < 72 := by
    obtain ⟨hr₀, hr₁⟩ := hr
    interval_cases r <;> norm_num
  omega
private def fastC (d u : ℤ) : ℤ :=
  if d < 0 || u < 0 then 0 else
    let v := min u (3 * d)
    let a := fastDen v
    if v ≤ d then a else
      let x := v - d
      let b := a - fastDen (x - 1) - fastDen (x - 2) - fastDen (x - 3)
      if x ≤ d + 2 then b else
        let y := x - d
        b + fastDen (y - 3) + fastDen (y - 4) + fastDen (y - 5)
private theorem fastC_eq (d u : ℤ) : fastC d u = cumulative d u := by
  unfold fastC cumulative
  split
  · rfl
  rename_i h
  simp only [fastDen_eq]
  have hden (x : ℤ) (hx : x < 0) : denominator x = 0 := by simp [denominator, hx]
  have hv : min u (3 * d) ≤ 3 * d := min_le_right _ _
  by_cases h₁ : min u (3 * d) ≤ d
  · simp (disch := omega) only [h₁, ite_true, hden, sub_zero, add_zero]
  · simp only [h₁, ite_false]
    rw [show min u (3 * d) - d - d = min u (3 * d) - 2 * d by ring]
    by_cases h₂ : min u (3 * d) - d ≤ d + 2
    · simp (disch := omega) only [h₂, ite_true, hden, add_zero, sub_zero]
    · simp (disch := omega) only [h₂, ite_false, hden, sub_zero]
private def fastOld (d lower cap : ℤ) : ℤ :=
  fastC d (3 * cap) - fastC d (min (3 * cap) (lower - 1))
private theorem fastOld_eq (d lower cap order : ℤ) (hc : 0 ≤ cap) :
    fastOld d lower cap = oldCount ⟨d, lower, 3 * cap, cap, order⟩ := by
  simp only [fastOld, fastC_eq, oldCount, cappedCount, not_lt.mpr hc, ite_false]
  have hz (u : ℤ) (h : u ≤ 3 * cap) :
      cumulative (d - cap - 1) (u - 3 * (cap + 1)) = 0 := by
    have hu : u - 3 * (cap + 1) < 0 := by omega
    simp [cumulative, hu]
  rw [hz _ le_rfl, hz _ (min_le_left _ _), sub_zero, sub_zero]
private def fastKernel (d lower cap order : ℤ) : ℤ :=
  if d < 0 || cap < 0 then 0 else
    let a := fastOld d lower cap
    let balance := order - 1 - lower + d
    if balance < 0 then a else
      let removed := min d (balance / 4) + 1
      let hi := fastC d (3 * cap)
      let adj := if lower - 1 ≤ 3 * cap then hi else a + fastC d (lower - 1)
      adj - fastC d (order - 1) +
        fastC (d - removed) (order - 1 - 3 * removed) - fastC (d - removed) (lower - 1)
private theorem fastKernel_eq (d lower cap order : ℤ) :
    fastKernel d lower cap order = kernelLower ⟨d, lower, 3 * cap, cap, order⟩ := by
  by_cases hd : d < 0
  · simp [fastKernel, kernelLower, hd]
  by_cases hc : cap < 0
  · simp [fastKernel, kernelLower, hc]
  have hu : ¬ 3 * cap < 0 := by omega
  simp only [fastKernel, kernelLower, targetCount, hd, hc, hu, decide_false, Bool.or_false,
    Bool.false_eq_true, ite_false]
  rw [← fastOld_eq _ _ _ _ (by omega)]
  by_cases hb : order - 1 - lower + d < 0
  · simp [hb]
  simp only [hb, ite_false, fastOld, fastC_eq]
  by_cases h : lower - 1 ≤ 3 * cap
  · simp only [h, ite_true, min_eq_right h]
    ring
  · simp only [h, ite_false]
    ring
def blockSaving (s j : ℕ) (p : Powers) : ℕ :=
  let lower : ℤ := 1650 - j
  let order : ℤ := 4650 - s - j
  let old := fastOld 1650 lower 550
  let initial := max 0 (fastKernel 1650 lower 550 order)
  let residual := fastKernel (1650 - (p.value + (p.top : ℤ) + 3 * p.cubic))
    (lower - (3 * (p.top : ℤ) + 2 * p.cubic)) (550 - (p.top + (p.cubic : ℤ)))
    (order - (2 * (p.top : ℤ) + 3 * p.cubic))
  (old - initial).toNat - (old - max initial residual).toNat
theorem blockSaving_eq (i : BlockIndex) (p : Powers) (hw : w3.Contains i) :
    blockSaving i.1.val i.2.val p = savings i p := by
  rcases hw with ⟨hs, _, _, hj, _, hsum⟩
  change 3012 ≤ i.1.val at hs
  change i.2.val ≤ 408 at hj
  change i.1.val + i.2.val ≤ 3796 at hsum
  have hd : min (i.1.val : ℤ) 1650 = 1650 := min_eq_right (by omega)
  have hu : min (1650 : ℤ) (2999 - offset i) = 1650 := by
    unfold offset
    apply min_eq_left
    omega
  have ho : 0 < (4650 : ℤ) - i.1.val - i.2.val := by omega
  have hi : initialFlag i = ⟨1650, 1650 - (i.2.val : ℤ), 1650, 550,
      4650 - (i.1.val : ℤ) - i.2.val⟩ := by
    unfold initialFlag offset
    rw [hd]
    congr 1 <;> ring
  have hz : residualFlag (initialFlag i) (fun _ => 0) = initialFlag i := by
    cases h : initialFlag i
    simp [residualFlag]
  unfold savings baseline blockBound blockSaving
  dsimp only
  rw [hz, hi]
  simp only [hu,
    not_le.mpr ho, ite_false, max_self, ← max_assoc]
  have hmin (a b : ℤ) (hb : 0 ≤ b) : min a (a - b) = a - b := min_eq_right (by omega)
  rw [hmin _ _ (le_max_left _ _), hmin _ _ ((le_max_left _ _).trans (le_max_left _ _))]
  rw [residualFlag_expand]
  rw [fastOld_eq _ _ _ (4650 - (i.1.val : ℤ) - i.2.val) (by decide), fastKernel_eq,
    fastKernel_eq]
  rw [show 3 * (550 - ((p.top : ℤ) + p.cubic)) =
    1650 - (3 * (p.top : ℤ) + 3 * p.cubic) by ring, show (3 : ℤ) * 550 = 1650 by decide]
theorem blockSaving_zero (s j : ℕ) : blockSaving s j ⟨0, 0, 0⟩ = 0 := by
  simp [blockSaving]
end K1_13_2_3_6
end
