import ProximityPrize.SubmissionLower.LowerAssembly

/-! Compact lower-bound proof; prior work is credited in the enclosed components. -/

section Compact_ThresholdIndexed80791
/-! An indexed evaluation of the same thin-band sum. Each term computes its
coordinates from the original box, avoiding long chains of nested subtraction. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.ThresholdIndexed
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (rawFlag)
open Lower80791.Oracle Lower80791.ThresholdFast Lower80791.PhaseChecks
open Lower80791.PhaseRows Lower80791.PhaseData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def indexedThin (w Dh delta dc dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => indexedThin w Dh delta dc dT dY dS T YS S n +
      delta * evalChannelCount (T-n*dT)
        (min (YS-n*dY) (thinTop w (Dh-n*(delta+dc)) (S-n*dS))) (S-n*dS)

theorem indexedThin_shift (w Dh delta dc dT dY dS T YS S n : ℕ) :
    indexedThin w Dh delta dc dT dY dS T YS S (n+1) =
      delta * evalChannelCount T (min YS (thinTop w Dh S)) S +
        indexedThin w (Dh-delta-dc) delta dc dT dY dS (T-dT) (YS-dY) (S-dS) n := by
  induction n with
  | zero => simp [indexedThin]
  | succ n ih =>
      rw [indexedThin, ih, indexedThin]
      have shift (x d : ℕ) : x-(n+1)*d = (x-d)-n*d := by
        rw [Nat.add_mul, Nat.one_mul, Nat.sub_sub]
        omega
      rw [shift T dT, shift YS dY, shift S dS, shift Dh (delta+dc)]
      rw [Nat.sub_sub]
      omega

theorem indexedThin_eq (w Dh delta dc dT dY dS T YS S fuel : ℕ) :
    indexedThin w Dh delta dc dT dY dS T YS S fuel =
      evalPowerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel := by
  induction fuel generalizing Dh T YS S with
  | zero => rfl
  | succ fuel ih =>
      rw [indexedThin_shift, evalPowerBandBudgetThin, ih]

def indexedBand (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  indexedThin 131071 (s.contactCap p) 50283 (contactDec p)
    (total p) (middle p) p.all (s.totalCap-total p)
    (s.middleCap-middle p) (s.slopeCap-p.all) (s.fuel p)

theorem indexedBand_eq (s : SourceNumbers) (p : FlagDegree) :
    indexedBand s p = evalBandThin s p := indexedThin_eq _ _ _ _ _ _ _ _ _ _ _

def IndexedSufficient (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  6917-(r+v) < threshold ∨
    let p := rawFlag r v threshold
    1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
      p.all ≤ s.slopeCap ∧ indexedBand s p < s.gap
instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (IndexedSufficient s r v threshold) := by
  unfold IndexedSufficient; infer_instance

theorem sufficient_of_indexed (s : SourceNumbers) (r v threshold : ℕ)
    (h : IndexedSufficient s r v threshold) :
    FastSourceThresholdSufficient s r v threshold := by
  rcases h with h | ⟨hr,ht,hy,hs,hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨hr,ht,hy,hs,Or.inl ((indexedBand_eq _ _) ▸ hb)⟩

def IndexedThresholdAt (r v : ℕ) : Prop :=
  ∀ j ∈ List.range 6, IndexedSufficient (phaseSource j) r v
    (thresholdAt (rowContext r v).threshold j)
instance (r v : ℕ) : Decidable (IndexedThresholdAt r v) := by
  unfold IndexedThresholdAt; infer_instance

theorem thresholdAt_of_indexed (r v : ℕ) (h : IndexedThresholdAt r v) : ThresholdAt r v := by
  intro j hj
  exact sufficient_of_indexed _ _ _ _ (h j hj)

end ProximityPrize.SubmissionLower.Lower80791.ThresholdIndexed

end Compact_ThresholdIndexed80791

section Compact_BandPolynomial80791
/-! A polynomial upper bound for threshold receipts. This is a runtime
optimization: the underlying geometric and threshold claims are unchanged. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.BandPolynomial
open scoped BigOperators
open LocatorLowQuotient Lower80791.ThresholdFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def boxPoly (w A B C : ℤ) : ℤ :=
  (C+w)*(3*(A+w)*(C+2*w)+C*(C+2*w)+6*A*B+9*w*B+3*B*C+3*B*B)

theorem choose_two_scaled (c : ℕ) :
    2 * (c+2).choose 2 = (c+2)*(c+1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (c+2) 2
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_comm] using h.symm

theorem choose_three_scaled (c : ℕ) :
    6 * (c+2).choose 3 = (c+2)*(c+1)*c := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (c+2) 3
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h.symm

theorem half_succ (c : ℕ) : 2*((c+1)*c/2) = (c+1)*c := by
  have h : 2 ∣ (c+1)*c := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (even_iff_two_dvd.mp (Nat.even_mul_succ_self c))
  simpa [Nat.mul_comm] using Nat.div_mul_cancel h

theorem half_pred (b : ℕ) : 2*(b*(b-1)/2)+b = b*b := by
  cases b with
  | zero => decide
  | succ b =>
      simp only [Nat.add_sub_cancel]
      rw [half_succ]
      ring

theorem channel_raw (a b c : ℕ) :
    6 * (channelCount (a+b+c) (b+c) c : ℤ) = boxPoly 1 a b c := by
  rw [channelCount_eq_fast]
  have hm : min (a+b+c) (b+c) = b+c := min_eq_right (by omega)
  have hk : min c (b+c) = c := min_eq_left (by omega)
  simp only [fastChannelCount, hm, hk]
  have hA : a+b+c+1-(b+c) = a+1 := by omega
  have hB : b+c-c = b := by omega
  rw [hA, hB]
  have hsub : (c+1)*c/2 ≤ (c+1)*(a+1+c+1) :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (by omega))
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub hsub]
  have h2 : (2 : ℤ)*((c+2).choose 2 : ℤ) = (c+2)*(c+1) := by
    exact_mod_cast choose_two_scaled c
  have h3 : (6 : ℤ)*((c+2).choose 3 : ℤ) = (c+2)*(c+1)*c := by
    exact_mod_cast choose_three_scaled c
  have hc : (2 : ℤ)*(((c+1)*c/2 : ℕ) : ℤ) = (c+1)*c := by
    exact_mod_cast half_succ c
  have hb : (2 : ℤ)*((b*(b-1)/2 : ℕ) : ℤ)+b = b*b := by
    exact_mod_cast half_pred b
  unfold boxPoly
  nlinarith only [h3, congrArg (fun x : ℤ => 3*(a+1)*x) h2,
    congrArg (fun x : ℤ => 3*(b : ℤ)*x) hc,
    congrArg (fun x : ℤ => 3*(c+1)*x) hb]


theorem channel_normalized (T YS S : ℕ) :
    channelCount T YS S =
      channelCount (T-min T YS+(min T YS-min S (min T YS))+min S (min T YS))
        (min T YS-min S (min T YS)+min S (min T YS)) (min S (min T YS)) := by
  have hU := Nat.min_le_left T YS
  have hk := Nat.min_le_right S (min T YS)
  have hT : T-min T YS+(min T YS-min S (min T YS))+min S (min T YS) = T := by omega
  have hY : min T YS-min S (min T YS)+min S (min T YS) = min T YS := by omega
  rw [hT, hY]
  rw [channelCount_eq_cappedKernel, channelCount_eq_cappedKernel]
  rw [min_eq_right hU]
  rw [kernelSumRange_eq, kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' : x ≤ min T YS := by have := Finset.mem_range.mp hx; omega
  unfold cappedTerm
  rw [min_assoc, min_eq_right hx']

theorem channel_poly (T YS S : ℕ) :
    6*(channelCount T YS S : ℤ) =
      boxPoly 1 ((T-min T YS : ℕ) : ℤ) ((min T YS-min S (min T YS) : ℕ) : ℤ) (min S (min T YS) : ℕ) := by
  rw [channel_normalized T YS S]
  exact channel_raw _ _ _

theorem boxPoly_scaled (w a b c : ℤ) :
    boxPoly w (w*a) (w*b) (w*c) = w^3*boxPoly 1 a b c := by
  unfold boxPoly
  ring

theorem boxPoly_mono (w a b c A B C : ℤ)
    (hw : 0 ≤ w) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) :
    boxPoly w a b c ≤ boxPoly w A B C := by
  have hA0 := ha.trans hA
  have hB0 := hb.trans hB
  have hC0 := hc.trans hC
  unfold boxPoly
  gcongr <;> positivity


/-- Rounding the thin middle width costs at most one unit in the outer width. -/
theorem channel_thin_bound (T YS S Dh : ℕ) :
    6*131071^3*(channelCount T (min YS ((Dh+S-1)/131071)) S : ℤ) ≤
      boxPoly 131071
        (131071*T-min (131071*T) (min (131071*YS) (Dh+S))+131071)
        (min (131071*T) (min (131071*YS) (Dh+S))-
          min (131071*S) (min (131071*T) (min (131071*YS) (Dh+S))))
        (min (131071*S) (min (131071*T) (min (131071*YS) (Dh+S)))) := by
  let U := min T (min YS ((Dh+S-1)/131071))
  let C := min S U
  let V : ℤ := min (131071*T) (min (131071*YS) (Dh+S))
  let K : ℤ := min (131071*S) V
  have hU : U ≤ T := Nat.min_le_left _ _
  have hC : C ≤ U := Nat.min_le_right _ _
  have hround : 131071*(U : ℤ) ≤ V ∧ V ≤ 131071*(U : ℤ)+131071 := by
    dsimp [U, V]
    omega
  have hK : 131071*(C : ℤ) ≤ K := by dsimp [C, K]; omega
  have hB : 131071*((U-C : ℕ) : ℤ) ≤ V-K := by
    dsimp [C, K]
    omega
  have hA : 131071*((T-U : ℕ) : ℤ) ≤ 131071*T-V+131071 := by omega
  have hm := boxPoly_mono 131071
    (131071*((T-U : ℕ) : ℤ)) (131071*((U-C : ℕ) : ℤ)) (131071*C)
    (131071*T-V+131071) (V-K) K (by norm_num) (by positivity)
    (by positivity) (by positivity) hA hB hK
  rw [boxPoly_scaled, ← channel_poly] at hm
  convert hm using 1 <;> push_cast <;> ring

structure Affine where
  constant : ℤ
  slope : ℤ
  deriving DecidableEq, Repr

def Affine.eval (a : Affine) (i : ℕ) : ℤ := a.constant+a.slope*i

def triplePrefix (a b c : Affine) (n : ℕ) : ℤ :=
  let x : ℤ := n
  12*x*(a.constant*b.constant*c.constant)+
  6*x*(x-1)*(a.slope*b.constant*c.constant+a.constant*b.slope*c.constant+a.constant*b.constant*c.slope)+
  2*x*(x-1)*(2*x-1)*(a.slope*b.slope*c.constant+a.slope*b.constant*c.slope+a.constant*b.slope*c.slope)+
  3*x*x*(x-1)*(x-1)*(a.slope*b.slope*c.slope)

theorem triplePrefix_eq (a b c : Affine) (n : ℕ) :
    triplePrefix a b c n = 12*∑ i ∈ Finset.range n, a.eval i*b.eval i*c.eval i := by
  induction n with
  | zero => simp [triplePrefix]
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ← ih]
      simp only [triplePrefix, Affine.eval, Nat.cast_add, Nat.cast_one]
      ring


def Affine.add (a b : Affine) : Affine := ⟨a.constant+b.constant,a.slope+b.slope⟩
def Affine.sub (a b : Affine) : Affine := ⟨a.constant-b.constant,a.slope-b.slope⟩
def Affine.scale (a : Affine) (k : ℤ) : Affine := ⟨k*a.constant,k*a.slope⟩
def Affine.plus (a : Affine) (k : ℤ) : Affine := ⟨a.constant+k,a.slope⟩

@[simp] theorem Affine.eval_add (a b : Affine) (i : ℕ) :
    (a.add b).eval i = a.eval i+b.eval i := by simp [Affine.add, Affine.eval]; ring
@[simp] theorem Affine.eval_sub (a b : Affine) (i : ℕ) :
    (a.sub b).eval i = a.eval i-b.eval i := by simp [Affine.sub, Affine.eval]; ring
@[simp] theorem Affine.eval_scale (a : Affine) (k : ℤ) (i : ℕ) :
    (a.scale k).eval i = k*a.eval i := by simp [Affine.scale, Affine.eval]; ring
@[simp] theorem Affine.eval_plus (a : Affine) (k : ℤ) (i : ℕ) :
    (a.plus k).eval i = a.eval i+k := by simp [Affine.plus, Affine.eval]; ring

def boxPrefix (a b c : Affine) (n : ℕ) : ℤ :=
  3*triplePrefix (c.plus 131071) (a.plus 131071) (c.plus (2*131071)) n+
  triplePrefix (c.plus 131071) c (c.plus (2*131071)) n+
  6*triplePrefix (c.plus 131071) a b n+
  9*131071*triplePrefix (c.plus 131071) b ⟨1,0⟩ n+
  3*triplePrefix (c.plus 131071) b c n+
  3*triplePrefix (c.plus 131071) b b n

theorem boxPrefix_eq (a b c : Affine) (n : ℕ) :
    boxPrefix a b c n =
      12*∑ i ∈ Finset.range n, boxPoly 131071 (a.eval i) (b.eval i) (c.eval i) := by
  simp only [boxPrefix, triplePrefix_eq, Affine.eval_plus]
  apply Eq.symm
  calc
    _ = ∑ i ∈ Finset.range n, 12*boxPoly 131071 (a.eval i) (b.eval i) (c.eval i) := by rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range n,
        ((3*(12*((c.eval i+131071)*(a.eval i+131071)*(c.eval i+2*131071))))+
        (12*((c.eval i+131071)*c.eval i*(c.eval i+2*131071)))+
        (6*(12*((c.eval i+131071)*a.eval i*b.eval i)))+
        (9*131071*(12*((c.eval i+131071)*b.eval i*(Affine.eval ⟨1,0⟩ i))))+
        (3*(12*((c.eval i+131071)*b.eval i*c.eval i)))+
        (3*(12*((c.eval i+131071)*b.eval i*b.eval i)))) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [boxPoly, Affine.eval]
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem boxPrefix_interval (a b c : Affine) (lo hi : ℕ) (h : lo ≤ hi) :
    boxPrefix a b c hi-boxPrefix a b c lo =
      12*∑ i ∈ Finset.Ico lo hi, boxPoly 131071 (a.eval i) (b.eval i) (c.eval i) := by
  rw [boxPrefix_eq, boxPrefix_eq]
  rw [← Finset.sum_range_add_sum_Ico _ h]
  ring

theorem Affine.nonneg_between (a : Affine) (lo hi i : ℕ)
    (hlo : lo ≤ i) (hhi : i ≤ hi) (h0 : 0 ≤ a.eval lo) (h1 : 0 ≤ a.eval hi) :
    0 ≤ a.eval i := by
  unfold Affine.eval at *
  rcases le_total 0 a.slope with hs | hs
  · have hh := mul_le_mul_of_nonneg_left (show (lo : ℤ) ≤ i by omega) hs
    omega
  · have hh := mul_le_mul_of_nonpos_left (show (i : ℤ) ≤ hi by omega) hs
    omega

end ProximityPrize.SubmissionLower.Lower80791.BandPolynomial




end Compact_BandPolynomial80791

section Compact_CompressedBand80791
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.CompressedBand
open scoped BigOperators
open Lower80791.BandPolynomial Lower80791.ThresholdIndexed
open Lower80791.ThresholdFast LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

structure Input where
  T : ℕ
  YS : ℕ
  S : ℕ
  Dh : ℕ
  dT : ℕ
  dY : ℕ
  dS : ℕ
  dDh : ℕ
  fuel : ℕ
  deriving DecidableEq, Repr

def Input.atT (p : Input) : Affine := ⟨p.T,-(p.dT : ℤ)⟩
def Input.atY (p : Input) : Affine := ⟨p.YS,-(p.dY : ℤ)⟩
def Input.atS (p : Input) : Affine := ⟨p.S,-(p.dS : ℤ)⟩
def Input.atDh (p : Input) : Affine := ⟨p.Dh,-(p.dDh : ℤ)⟩
def Input.count (p : Input) (i : ℕ) : ℕ :=
  channelCount (p.T-i*p.dT)
    (min (p.YS-i*p.dY) ((p.Dh-i*p.dDh+(p.S-i*p.dS)-1)/131071)) (p.S-i*p.dS)

def Input.dh (p : Input) (code : ℕ) : Affine := if 6 ≤ code then p.atDh else ⟨0,0⟩
def Input.u (p : Input) (code : ℕ) : Affine :=
  if code/2%3 = 0 then p.atT.scale 131071
  else if code/2%3 = 1 then p.atY.scale 131071
  else (p.dh code).add p.atS
def Input.c (p : Input) (code : ℕ) : Affine :=
  if code%2 = 0 then p.atS.scale 131071 else p.u code
def Input.a (p : Input) (code : ℕ) : Affine := ((p.atT.scale 131071).sub (p.u code)).plus 131071
def Input.b (p : Input) (code : ℕ) : Affine := (p.u code).sub (p.c code)

def conditions (p : Input) (code : ℕ) : List Affine :=
  [p.atT,p.atY,p.atS,if 6 ≤ code then p.atDh else p.atDh.scale (-1),
    (p.atT.scale 131071).sub (p.u code),
    (p.atY.scale 131071).sub (p.u code),
    ((p.dh code).add p.atS).sub (p.u code),
    (p.atS.scale 131071).sub (p.c code),
    (p.u code).sub (p.c code)]

def ValidAt (p : Input) (code i : ℕ) : Prop :=
  ∀ a ∈ conditions p code, 0 ≤ a.eval i
instance (p : Input) (code i : ℕ) : Decidable (ValidAt p code i) := by
  unfold ValidAt; infer_instance

theorem validAt_between (p : Input) (code lo hi i : ℕ)
    (hlo : lo ≤ i) (hhi : i ≤ hi) (h0 : ValidAt p code lo) (h1 : ValidAt p code hi) :
    ValidAt p code i := by
  intro a ha
  exact a.nonneg_between lo hi i hlo hhi (h0 a ha) (h1 a ha)

theorem linear_cast (t d i : ℕ) (h : 0 ≤ Affine.eval ⟨t,-(d : ℤ)⟩ i) :
    ((t-i*d : ℕ) : ℤ) = Affine.eval ⟨t,-(d : ℤ)⟩ i := by
  simp only [Affine.eval, neg_mul] at *
  have hc : ((i*d : ℕ) : ℤ) = (d : ℤ)*i := by push_cast; ring
  omega

theorem validAt_bound (p : Input) (code i : ℕ) (h : ValidAt p code i) :
    6*131071^3*(p.count i : ℤ) ≤
      boxPoly 131071 ((p.a code).eval i) ((p.b code).eval i) ((p.c code).eval i) := by
  simp only [ValidAt, conditions, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h
  rcases h with ⟨hT,hY,hS,hD,hU0,hU1,hU2,hC0,hC1⟩
  have htc := linear_cast p.T p.dT i hT
  have hyc := linear_cast p.YS p.dY i hY
  have hsc := linear_cast p.S p.dS i hS
  change ((p.T-i*p.dT : ℕ) : ℤ) = p.atT.eval i at htc
  change ((p.YS-i*p.dY : ℕ) : ℤ) = p.atY.eval i at hyc
  change ((p.S-i*p.dS : ℕ) : ℤ) = p.atS.eval i at hsc
  have hdc : ((p.Dh-i*p.dDh : ℕ) : ℤ) = (p.dh code).eval i := by
    unfold Input.dh
    split_ifs with hd
    · simp only [hd, ↓reduceIte] at hD
      exact linear_cast p.Dh p.dDh i hD
    · simp only [hd, ↓reduceIte, Affine.eval_scale] at hD
      simp only [Input.atDh, Affine.eval, neg_mul] at hD ⊢
      have hc : ((i*p.dDh : ℕ) : ℤ) = (p.dDh : ℤ)*i := by push_cast; ring
      omega
  simp only [Affine.eval_sub, Affine.eval_scale, Affine.eval_add] at hU0 hU1 hU2 hC0 hC1
  have hue : (p.u code).eval i =
      min (131071*p.atT.eval i) (min (131071*p.atY.eval i) ((p.dh code).eval i+p.atS.eval i)) := by
    by_cases h0 : code/2%3 = 0
    · simp only [Input.u, h0, ↓reduceIte, Affine.eval_scale] at hU0 hU1 hU2 ⊢
      omega
    · by_cases h1 : code/2%3 = 1
      · simp only [Input.u, h0, h1, Nat.one_ne_zero, ↓reduceIte, Affine.eval_scale] at hU0 hU1 hU2 ⊢
        omega
      · simp only [Input.u, h0, h1, Nat.one_ne_zero, ↓reduceIte, Affine.eval_add] at hU0 hU1 hU2 ⊢
        omega
  have hce : (p.c code).eval i = min (131071*p.atS.eval i) ((p.u code).eval i) := by
    by_cases h0 : code%2 = 0 <;>
      simp only [Input.c, h0, ↓reduceIte, Affine.eval_scale] at hC0 hC1 ⊢ <;> omega
  have hb := channel_thin_bound (p.T-i*p.dT) (p.YS-i*p.dY) (p.S-i*p.dS) (p.Dh-i*p.dDh)
  push_cast at hb
  rw [htc,hyc,hsc,hdc,← hue,← hce] at hb
  norm_num only [Int.reducePow, Int.reduceMul]
  simpa only [Input.count,Input.a,Input.b,Affine.eval_plus,Affine.eval_sub,Affine.eval_scale] using hb


structure Run where
  stop : ℕ
  code : ℕ
  deriving DecidableEq, Repr

def RunValid (p : Input) (start : ℕ) (run : Run) : Prop :=
  start < run.stop ∧ run.stop ≤ p.fuel ∧
    ValidAt p run.code start ∧ ValidAt p run.code (run.stop-1)
instance (p : Input) (start : ℕ) (run : Run) : Decidable (RunValid p start run) := by
  unfold RunValid; infer_instance

def runUpper (p : Input) (start : ℕ) (run : Run) : ℤ :=
  boxPrefix (p.a run.code) (p.b run.code) (p.c run.code) run.stop-
  boxPrefix (p.a run.code) (p.b run.code) (p.c run.code) start

theorem runValid_bound (p : Input) (start : ℕ) (run : Run)
    (h : RunValid p start run) :
    72*131071^3*(∑ i ∈ Finset.Ico start run.stop, (p.count i : ℤ)) ≤ runUpper p start run := by
  rw [runUpper, boxPrefix_interval _ _ _ _ _ h.1.le]
  have hs : (∑ i ∈ Finset.Ico start run.stop, 6*131071^3*(p.count i : ℤ)) ≤
      ∑ i ∈ Finset.Ico start run.stop,
        boxPoly 131071 ((p.a run.code).eval i) ((p.b run.code).eval i) ((p.c run.code).eval i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact validAt_bound p run.code i (validAt_between p run.code start (run.stop-1) i
      (Finset.mem_Ico.mp hi).1 (by have := (Finset.mem_Ico.mp hi).2; omega) h.2.2.1 h.2.2.2)
  rw [← Finset.mul_sum] at hs
  linarith

def RunsValid (p : Input) : ℕ → List Run → Prop
  | start, [] => start = p.fuel
  | start, run::runs => RunValid p start run ∧ RunsValid p run.stop runs
instance (p : Input) (start : ℕ) (runs : List Run) : Decidable (RunsValid p start runs) := by
  induction runs generalizing start with
  | nil => unfold RunsValid; infer_instance
  | cons run runs ih => unfold RunsValid; infer_instance

def runsUpper (p : Input) : ℕ → List Run → ℤ
  | _, [] => 0
  | start, run::runs => runUpper p start run+runsUpper p run.stop runs

theorem runsValid_bound (p : Input) (start : ℕ) (runs : List Run)
    (h : RunsValid p start runs) :
    72*131071^3*(∑ i ∈ Finset.Ico start p.fuel, (p.count i : ℤ)) ≤ runsUpper p start runs := by
  induction runs generalizing start with
  | nil => simp only [RunsValid] at h; simp [h, runsUpper]
  | cons run runs ih =>
      have h0 := runValid_bound p start run h.1
      have h1 := ih run.stop h.2
      rw [← Finset.sum_Ico_consecutive _ h.1.1.le h.1.2.1]
      simp only [runsUpper]
      linarith


open Lower80791.Oracle LocatorArbitraryPowerAvoidance
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (rawFlag)

def ofSource (s : SourceNumbers) (p : FlagDegree) : Input :=
  ⟨s.totalCap-total p,s.middleCap-middle p,s.slopeCap-p.all,s.contactCap p,
    total p,middle p,p.all,50283+contactDec p,s.fuel p⟩

theorem indexed_sum (p : Input) (dc n : ℕ) (hd : p.dDh = 50283+dc) :
    (indexedThin 131071 p.Dh 50283 dc p.dT p.dY p.dS p.T p.YS p.S n : ℤ) =
      50283*∑ i ∈ Finset.range n, (p.count i : ℤ) := by
  induction n with
  | zero => simp [indexedThin]
  | succ n ih =>
      rw [indexedThin, Nat.cast_add, Nat.cast_mul, ih, Finset.sum_range_succ]
      simp only [Input.count, channelCount_eq_eval, thinTop, hd]
      push_cast
      ring

theorem source_sum (s : SourceNumbers) (p : FlagDegree) :
    (indexedBand s p : ℤ) =
      50283*∑ i ∈ Finset.range (ofSource s p).fuel, ((ofSource s p).count i : ℤ) :=
  indexed_sum (ofSource s p) (contactDec p) (s.fuel p) rfl

def Sufficient (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) : Prop :=
  6917-(r+v) < threshold ∨
    let p := rawFlag r v threshold
    1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧ p.all ≤ s.slopeCap ∧
      RunsValid (ofSource s p) 0 runs ∧
      50283*runsUpper (ofSource s p) 0 runs < (s.gap : ℤ)*(72*131071^3)
instance (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) :
    Decidable (Sufficient s r v threshold runs) := by
  unfold Sufficient; infer_instance

theorem sufficient_sound (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run)
    (h : Sufficient s r v threshold runs) : FastSourceThresholdSufficient s r v threshold := by
  rcases h with h | ⟨hr,ht,hy,hs,hvalid,hgap⟩
  · exact Or.inl h
  apply sufficient_of_indexed
  refine Or.inr ⟨hr,ht,hy,hs,?_⟩
  have hb := runsValid_bound (ofSource s (rawFlag r v threshold)) 0 runs hvalid
  rw [Nat.Ico_zero_eq_range] at hb
  have he := source_sum s (rawFlag r v threshold)
  have hi : (indexedBand s (rawFlag r v threshold) : ℤ) < s.gap := by
    nlinarith only [hgap, congrArg (fun x : ℤ => (72*131071^3)*x) he,
      mul_le_mul_of_nonneg_left hb (show (0 : ℤ) ≤ 50283 by norm_num)]
  exact_mod_cast hi

end ProximityPrize.SubmissionLower.Lower80791.CompressedBand



end Compact_CompressedBand80791

section Compact_CompressedData80791
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.CompressedData
open Lower80791.CompressedBand
set_option autoImplicit false
set_option maxRecDepth 100000

private def row1PackedData : ℕ := 0x146c1fd00386000051587fa0070ca2a944b1fd400e2145528963fa801c4516aa26cfdd003894000051b07f400e1800014761fe801c3000051ec7fd003860000a3d8ffa0070d47aa8eb3ff400e25000014ac205003862954525880a00710a52949b203400e214a52936406801c4528aa4ad01d00389429a852b081400e20a6514b6206801c4298a52ec81d003885314a5d903a007114caa97b40f400e25000014ec20d00386000053d882a0070ca7a94eb20b400e214f529d6416801c453caa72d055003894000054b083400e18000151620e801c30000546c83d003860000a8d907a0070d51aaa2b41f400e250aaa152c215003882a9454d884a00710aa2953b213400e215452a76426801c4552aa9ed09d003894000055b085400e180001576216801c32aea55ac85d0038855d4ab590ba00711572aacb42f400e25000015ac21d003860000565887a0070caca958b21b400e215952b16436801c4566aac6d0dd0038942ba856b089400e20ae515b6222801c42b8a56ec885003885714add910a007115caab7b43f400e25000015ec22500386000057d889a0070cafa95eb225400e215f52bd644a801c457caaf2d125003894000058b08b400e18b15161622a801c42c4a586c8a5003885894b0d914a00711622ac2b451400e250000166c22d003862c9458d88ba00710b2a963b22d400e216552c7645a801c4594ab1ed165003894000059b08d400e180001676232801c32cea59ac8c50038859d4b35918a0071167aacdb463400e25000016ac235003862d545a588da00710b52969b237400e216a52d3646e801c45aaab4ed1b500389400005bb08f400e1800016d623a801c32daa5b2c8ed003885b54b6591da007116daad9b475400e250b8a16ec245003882e145bd890a00710b8296fb241400e217052df6482801c45c2ab7ed1fd0038942ea85cb091400e20ba51736246801c42e8a5cac915003885d14b95922a00711742ae5b489400e250000176c24d0038600005dd892a0070cbba976b249400e217752ed6492801c45dcabb2d24d00389400005eb093400e18bd5179624e801c42f4a5e6c93d003885e94bcd927a007117a2af2b49d400e25000017ec2550038600005f5895a0070cbea97cb255400e217d52f964aa801c45f6abe2d29d00389430285fb097400e20c0517f625a801c4302a5fec965003886054bfd92ca00711812affb4b1400e250c2a182c25d00388309460d897a00710c22983b25f400e2184530764be801c4610ac1ad2f5003894000061b099400e180001876266801c330ea61ac98d0038861d4c35931a0071187ab0db4c7400e25000018ac26d00386315462589aa00710c5a989b269400e218b531364d2801c462cac4ed345003894000063b09b400e18c7518d626e801c431ca636c9bd003886394c6d937a007118eab1bb4dd400e250000192c27500386325464589da00710c92991b275400e2192532364ea801c464aac8ad3a5003894000065b09f400e18cb5195627a801c432ca652c9ed003886594ca593da00711962b29b4f3400e25000019ac2850038600006658a0a0070ccca998b281400e219953316502801c4666acc6d3fd003894000067b0a1400e1800019d6286801c333aa672ca1d003886754ce5943a007119dab38b50b400e2500001a2c28d0038600006858a3a0070cd0a9a0b28d400e21a15341651a801c4686ad02d465003894000069b0a5400e180001a56292801c334aa692ca4d003886954d25949a00711a5ab48b525400e2500001aac29d0038600006a58a6a0070cd4a9a8b299400e21a953516532801c46a6ad42d4c500389400006bb0a9400e180001ad629e801c335aa6b2ca7d003886b54d6594fa00711adab58b53f400e2500001b2c2a50038636546c58a9a00710d929b0b2a7400e21b25361654e801c46c8ad82d52d00389400006db0ab400e18db51b562ae801c436ca6d2cab5003886d94da5956a00711b62b69b559400e2500001bac2b50038637546e58ada00710dd29b9b2b5400e21ba5373656a801c46eaadcad59d00389400006fb0af400e18df51bd62ba801c437ea6f6caed003886fd4ded95da00711bf2b7bb575400e2500001c2c2c500386000070d8b0a0070ce1a9c2b2c3400e21c353856586801c470eae12d60d003894392871b0b3400e20e451c762ca801c4390a71acb25003887214e35964a00711c82b8db591400e250e6a1cac2d500388399472d8b4a00710e6a9cbb2d1400e21cd539765a2801c4734ae5ad685003894000074b0b7400e18e951d162da801c43a4a742cb65003887494e8596ca00711d22ba0b5b1400e2500001d6c2e5003863ad47558b8a00710eba9d5b2e1400e21d753ab65c2801c475caeaad6fd0038943ba876b0bb400e20ee51db62ea801c43b8a76acba5003887714ed5974a00711dc2bb4b5cf400e250f0a1dec2f5003883c1477d8bca00710f0a9dfb2f1400e21e153bf65e2801c4784aefad77d003894000079b0bf400e18f351e562fa801c43cca792cbe5003887994f2597ca00711e6abc9b5f1400e2500001eac305003863d547a58c0a00710f5a9e9b301400e21eb53d36602801c47aeaf4ed8050038943e287bb0c3400e20f851ef630a801c43e2a7becc2d003887c54f7d985a00711f12bdeb613400e2500001f6c315003863ed47d58c4a00710fba9f4b313400e21f753e96626801c47dcafa6d8950038943fa87eb0c7400e20fe51fb631e801c43f8a7eacc75003887f14fd598ea00711fcabf5b637400e250000202c3250038640548058c9a00711012a00b325400e22025401664a801c480ab006d925003894412881b0cb400e21045207632e801c4410a81accbd003888215035997a0071208ac0db65d400e25000020ec33d0038641d48358cea0071107aa0cb339400e220f54196672801c483cb066d9c500389442a884b0d1400e210a52136342801c442aa84ecd0d00388855509d9a1a00712152c25b685400e25000021ac34d0038643548658d3a007110daa19b34d400e221b5433669a801c486eb0cada65003894000088b0d5400e191152216356801c4444a882cd5d0038888951059aba0071222ac40b6ad400e25114a226c36500388451489d8d8a0071114aa26b363400e2229544d66c6801c48a4b136db0d00389446288bb0db400e2118522d636e801c4460a8b6cdb5003888c1516d9b6a00712302c5bb6d9400e250000236c37d0038646d48d58dea007111baa34b379400e2237546966f2801c48deb1a6dbbd00389400008fb0e1400e191f523d6386801c447ea8f2ce15003888fd51e59c2a007123f2c78b707400e25122a242c3950038848d490d8e4a00711232a43b391400e224654876722801c491ab21edc7d00389449a892b0e7400e2127524b639e801c449ca92ece7500388939525d9cea007124e2c96b737400e2512aa252c3ad003884ad494d8eaa007112b2a53b3a9400e225654a76752801c4958b29add450038944ba896b0ed400e212f525b63b6801c44bca96ecedd0038897952dd9dba007125eacb6b76b400e25132a262c3c5003884cd498d8f0a00711332a63b3c3400e226654c76786801c499ab31ede1500389400009bb0f5400e1937526d63d2801c44dea9b2cf45003889bd53659e8a007126facd8b7a1400e2513ca276c3dd003884f149d58f7a007113c2a75b3df400e227854eb67be801c49e2b3aadef500389450289fb0fb400e2140527f63ee801c4502a9facfb500388a0553f59f6a0071281acfcb7d9400e25144a286c3fd003885154a1d8ffa0071145aa87b3fd400e228b550f67fa801c4a2cb43adfdd00389452a8a4b103400e214a5291640e801c4528aa46d03500388a51548da06a0071294ad22b817400e2514ea29ac41d0038853d4a6d907a007114f2a9ab41b400e229e55356836801c4a7ab4d6e0d50038945528a9b10b400e215452a5642e801c4552aa96d0b500388aa5552da16a00712a92d4ab857400e25158a2aec43d003885654abd90fa0071159aaafb43d400e22b3555f687a801c4aceb57ee1e500389457a8aeb113400e215f52bb644e801c457caaead13d00388af955d5a27a00712bead75b89b400e25164a2c6c465003885954b15918a00711652ac5b461400e22ca558b68c2801c4b28b62ee2fd0038945aa8b4b11d400e216a52d16472801c45aaab46d1cd00388b55568da39a00712d5ada2b8e3400e25170a2dec485003885c14b75921a0071170aaddb487400e22e155bb690e801c4b7eb6eae42d0038945da8bab127400e217752e9649a801c45dcaba6d26d00388bb9574da4da00712d0bda0b931400e2500002f2c4ad003865f54bdd92ba007117daaf6b4af400e22fb55ed695e801c4b0af60ee56d0038940000b8b131400e197572e964c6801c4610ac0ed30d00388c21581da61a00712b63d69b985400e2516ae2d2c4dd003880000b6d936a0070d8b2b11b4d9400e2316562369b2801c4aacf546e6c50038940000b1b13d400e196772cd64f2801c464aac7ed3c500388c9558fda78a00712a0bd3cb9df400e2515ee2bac50d00388581cafd942a0071199ab2eb509400e2333565d6a12801c4a5cf4a2e83d0038945638abb149400e215b72b56522801c4686acf6d48500388d0d59eda90a007128e3d166a2b400e2500002a6c53d00386559caa594ea007119a3b33b53b400e2353569b6a76801c4a18f415a8250038940000a7714d400e180002a2e542801c3644ec86d555003880001a65aaaa0070e7e3cf669e9400e250000295c525003860000a6b94ba0070d893b10b571400e233976716ae2801c49daf39da72d0038940000a37145400e18000292e51e801c3606ec0ad63500388ca1d93dac6a00712703cda69af400e250000285c50500386515ca23143a007117b3af4b5ab400e2318762f6b56801c49a6f335a65500389400009f613d400e19417280c4fe801c45d4eba2d72d00388c29d84dae5a00712633cc0697b400e250000279c4ed003864f9c9eb13ca007100002df75bb400e1afe75f96bd6801c4976f2d5a58500389400009c7137400e193b7272c4e2801c45aaeb4d9695003880001793af0a0070e583caa694b400e25136e26984cd003884e1c9b3135a007100002cc7593400e180005ceeb96801c394af27da4d50038940000997131400e19357266c4ca801c4586eb0596050038800016ebadba0070e4dbc95691f400e25130e25d84b5003884c9c98b12fa007115dbab8656f400e22d475a4cb46801c4922f22da42d003894000096612b400e192f725cc4b2801c4566eac1957d00388b2dd64b2c8a00712443c8268f7400e25000025584a5003864b5c95b12aa0071155baa9654f400e22c37582cb02801c48fef1e5a3950038944a38936125400e212a7252c49e801c4548ea89950500388aedd5cb2b8a007123b3c7068d3400e25126e249848d003884a1c933125a007114eba9b6533400e22b47564cac2801c48daf1a1a3050038944938916121400e21257248c48a801c452eea55949d00388ab5d55b2a9a0071232bc5f68af400e25122e241847d0038848dc913120a0071148ba8f6519400e22a67548ca8a801c48baf161a27d00389448388f611d400e21217240c47a801c4516ea25943500388a81d4f329ba007122abc50688f400e250000239846d0038647dc8f311ca0071142ba836501400e229a7530ca56801c489cf125a1fd00389400008d6119400e191d7238c46a801c4500e9f993dd00388a51d49328fa0071223bc416871400e2511ae231845d0038846dc8d3118a007113dba7964eb400e228e7518ca26801c4880f0eda18d00389446388b6115400e21197230c45a801c44ece9d1938500388a25d43b284a007121cbc346853400e25116e229844d0038845dc8b3114a0071138ba6f64d7400e22837504c9fa801c4866f0b5a11d0038944538896111400e21167228c44a801c44d8e9a9933d003889f9d3eb279a00712163c276839400e25112e221843d00388451c89b110a00711343a6664c5400e227974f0c9d2801c484cf085a0ad003894000088610d400e19127222c43a801c44c6e98592ed003889d5d39b26fa00712103c1a681f400e25000021d842d00386445c87b10da007112fba5d64b3400e227074dcc9ae801c4834f051a04d00389443b886610b400e210f721cc42e801c44b6e96592ad003889b1d353266a007120a3c0f6807400e2510ce215842500388435c863109a007112bba5564a3400e226774ccc98a801c481cf0259fed00389442b8846107400e210c7216c422801c44a6e945926d0038898dd30b25da0071204bc0467ef400e250000211841500386429c84b106a0071127ba4d6493400e225f74bcc966801c4806eff99f950038944238836105400e21097210c416801c4496e929922d0038896dd2d3255a00711ff3bf967d9400e25106e209840d00388421c833103a00711243a466483400e225874acc94a801c47f2efd19f3d0038940000826101400e1906720ac40a801c4488e90d91f500388951d29324ea00711fa3bef67c3400e25104e20583fd00388415c823101a0071120ba3f6475400e2250749cc92a801c47deefa99ee500389440b88060ff400e21037204c3fe801c447ce8f191bd00388935d25b246a00711f53be567af400e25000020183f500386409c80b0fea007111d3a396469400e2249748ec90e801c47caef819e9500389440387f60fb400e21017200c3f2801c446ee8d5918500388919d22323fa00711f0bbdc679b400e250fee1f983ed00388401c7fb0fba007111a3a32645b400e22437482c8f2801c47b8ef5d9e4d00389400007e60f9400e18fe71fac3ea801c4462e8bd9155003888fdd1f3239a00711ebbbd36789400e250fce1f583e5003883f5c7e30f9a00711173a2c644f400e223c7476c8da801c47a6ef399dfd00389400007d60f7400e18fc71f6c3e2801c4456e8a59125003888e5d1c3232a00711e7bbca6777400e250fae1f183d5003883edc7d30f6a00711143a276443400e2236746ac8be801c4794ef199dbd00389400007c60f5400e18fa71f2c3d6801c444ce89190f5003888cdd19322ca00711e33bc26765400e250f8e1ed83cd003883e5c7c30f4a0071111ba216437400e2230745ec8a6801c4784eef59d750038943db87a60f3400e20f871eec3ce801c4440e87d90cd003888b9d163227a00711df3bb96755400e250f6e1e983c5003883ddc7ab0f2a007110f3a1c642d400e222b7452c892801c4774eed99d350038943d387960f1400e20f671e8c3c6801c4436e865909d003888a1d13b221a00711db3bb26745400e2500001e583bd003863d1c79b0f0a007110cba176423400e22267448c87a801c4764eeb99cf50038943cb87860ef400e20f471e4c3be801c442ce85190750038888dd10b21ca00711d7bbaa6735400e2500001e183b5003863cdc78b0eea007110a3a126419400e2220743ec866801c4756ee999cb50038943c387760ed400e20f271e0c3b6801c4422e841904d00388879d0e3216a00711d3bba36725400e25

def row1 (index : ℕ) : List (List ℕ) :=
  if index < 136 then
    let packedCell := Nat.shiftRight row1PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row2PackedData : ℕ := 0x51b07f400e1800014561fe801c328aa512c7fd003885154a258ffa0071145aa89b3ff400e250000146c20500386000051d880a0070c000147b203400e1800028f6406801c351eaa3ad01d003894000052b081400e18a551496206801c4294a526c81d003885294a4d903a007114a2a92b40f400e250a6a14ac20d00388299452d882a00710a6294bb20b400e214c52976416801c4532aa5ed055003894000053b083400e1800014f620e801c329ea53ac83d0038853d4a75907a007114f2a9cb41f400e250000152c215003860000545884a0070c000151b213400e180002a36426801c3546aa8ad09d0038942aa854b085400e20aa51536216801c42a8a54ec85d003885514a9d90ba0071154aaa7b42f400e250000156c21d00386000055d887a0070caba956b21b400e215752ad6436801c455caab2d0dd003894000056b089400e180001596222801c32b2a562c885003885654ac5910a0071159aab1b43f400e250aea15ac225003882b9456d889a00710ae295bb225400e215c52b7644a801c4572aaded125003894000057b08b400e1800015f622a801c32bea57ac8a50038857d4af5914a007115f2abcb451400e250000162c22d003862c5458588ba00710b12961b22d400e216252c3645a801c4588ab0ad165003894000059b08d400e18b251636232801c42caa58ec8c5003885954b1d918a00711652ac7b463400e250000166c23500386000059d88da0070cb3a966b237400e216752cd646e801c459eab36d1b500389400005ab08f400e18b55169623a801c42d4a5a6c8ed003885a94b4d91da007116aaad3b475400e25000016ec2450038600005b5890a0070cb6a96cb241400e216d52d96482801c45b6ab66d1fd0038942e285bb091400e20b8516f6246801c42e0a5bec915003885c14b7d922a0071170aadfb489400e250baa172c24d003882e945cd892a00710ba2972b249400e217452e56492801c45d0ab96d24d00389400005db093400e18000177624e801c32eea5dac93d003885dd4bb5927a00711772aecb49d400e25000017ac255003862f545e5895a00710bd2979b255400e217a52f364aa801c45e8abcad29d00389400005fb097400e1800017d625a801c32faa5f2c965003885f54be592ca007117daaf8b4b1400e250c0a17ec25d0038830145fd897a00710c0a97fb25f400e218152ff64be801c4604abfed2f500389430a860b099400e20c251836266801c4308a60ec98d003886114c1d931a00711842b06b4c7400e250000186c26d00386000061d89aa0070cc3a986b269400e2187530d64d2801c461eac36d345003894000062b09b400e18c55189626e801c4316a626c9bd0038862d4c4d937a007118b2b13b4dd400e25000018ec2750038631d463589da00710c7298db275400e218e531b64ea801c463aac6ed3a5003894000064b09f400e18c95191627a801c4324a646c9ed003886494c8d93da0071192ab22b4f3400e250000196c2850038632d46558a0a00710cb2994b281400e219653296502801c4658aca6d3fd003894000066b0a1400e180001996286801c3332a662ca1d003886654cc5943a0071199ab31b50b400e25000019ec28d0038600006758a3a0070ccea99cb28d400e219d5339651a801c4676ace2d465003894000068b0a5400e180001a16292801c3342a682ca4d003886854d05949a00711a1ab40b525400e2500001a6c29d0038600006958a6a0070cd2a9a4b299400e21a553496532801c4696ad22d4c500389400006ab0a9400e180001a9629e801c3352a6a2ca7d003886a54d4594fa00711a9ab50b53f400e2500001aec2a50038600006b58a9a0070cd6a9acb2a7400e21ad5359654e801c46b6ad62d52d00389400006cb0ab400e18d951b162ae801c4364a6c2cab5003886c94d85956a00711b22b60b559400e2500001b6c2b50038636d46d58ada00710db29b4b2b5400e21b65369656a801c46d8ada6d59d00389400006eb0af400e18dd51b962ba801c4374a6e6caed003886e94dcd95da00711baab72b575400e2500001bec2c50038637d46f58b0a00710dfa9bdb2c3400e21bf537b6586801c46fcadeed60d003894000070b0b3400e180001c362ca801c3386a70acb250038870d4e15964a00711c3ab84b591400e250e4a1c6c2d500388391471d8b4a00710e429c6b2d1400e21c8538d65a2801c4720ae36d68500389439a872b0b7400e20e651cb62da801c439aa72ecb65003887354e5d96ca00711cd2b96b5b1400e2500001d2c2e5003863a547458b8a00710e929d0b2e1400e21d253a165c2801c4748ae82d6fd003894000075b0bb400e18eb51d562ea801c43aea756cba50038875d4ead974a00711d72baab5cf400e250eea1dac2f5003883b9476d8bca00710ee29dab2f1400e21dc53b565e2801c4770aed2d77d0038943c2877b0bf400e20f051df62fa801c43c2a77ecbe5003887854efd97ca00711e12bbeb5f1400e2500001e6c305003863cd47958c0a00710f329e4b301400e21e653c96602801c479aaf26d80500389400007ab0c3400e18f551e9630a801c43d6a7a6cc2d003887ad4f4d985a00711ebabd3b613400e250f8a1eec315003883e147bd8c4a00710f8a9efb313400e21f153df6626801c47c4af7ad89500389400007db0c7400e18fb51f5631e801c43eea7d2cc75003887dd4fa598ea00711f72be9b637400e250fea1fac325003883f947ed8c9a00710fe29fab325400e21fc53f5664a801c47f2afd6d925003894000080b0cb400e19015201632e801c4404a802ccbd003888095005997a0071202ac01b65d400e25104a206c33d00388411481d8cea00711042a06b339400e2208540d6672801c4822b036d9c5003894000083b0d1400e1907520d6342801c441ea832cd0d0038883d50659a1a007120f2c19b685400e2510aa212c34d00388429484d8d3a007110aaa13b34d400e22155427669a801c4854b096da65003894000086b0d5400e190d52196356801c4436a866cd5d0038886d50cd9aba007121bac32b6ad400e250000222c3650038644548858d8a00711112a20b363400e2222544166c6801c488ab102db0d003894452889b0db400e21145227636e801c4452a89acdb5003888a551359b6a00712292c4db6d9400e25118a22ec37d0038846148b58dea00711182a2db379400e2230545b66f2801c48c0b16edbbd00389400008db0e1400e191b52356386801c446ea8d2ce15003888dd51a59c2a0071237ac69b707400e25000023ec3950038647d48f58e4a007111faa3cb391400e223f54796722801c48fcb1e2dc7d00389448a890b0e7400e21235243639e801c448ca90ece7500388919521d9cea0071246ac87b737400e25126a24ac3ad0038849d492d8eaa00711272a4bb3a9400e224e54976752801c4938b25add450038944aa894b0ed400e212b525363b6801c44aca94ecedd00388959529d9dba00712562ca6b76b400e2512ea25ac3c5003884bd496d8f0a007112f2a5bb3c3400e225e54b76786801c497ab2dade150038944ca898b0f5400e2133526363d2801c44cca98ecf4500388999531d9e8a0071266acc7b7a1400e25000026ec3dd003864dd49b58f7a0071137aa6cb3df400e226f54d967be801c49beb362def50038944f289db0fb400e213c527563ee801c44f0a9d6cfb5003889e153ad9f6a0071278aceab7d9400e25140a27ec3fd0038850149fd8ffa0071140aa7eb3fd400e228154fd67fa801c4a06b3f2dfdd0038945128a1b103400e21455287640e801c4516aa1ed03500388a2d543da06a007128b2d0eb817400e2514aa292c41d003885294a45907a007114a2a91b41b400e229455236836801c4a52b48ae0d500389453a8a6b10b400e214f529b642e801c453caa6ad0b500388a7954d5a16a007129ead35b857400e25154a2a6c43d003885514a9590fa0071154aaa5b43d400e22a9554b687a801c4aa4b52ae1e50038945628abb113400e215952af644e801c4566aabed13d00388acd557da27a00712b3ad5fb89b400e2515ea2bac4650038857d4aed918a007115f2abab461400e22be557568c2801c4afab5d6e2fd0038945928b1b11d400e216552c56472801c4594ab16d1cd00388b29562da39a00712ca2d8bb8e3400e2516aa2d2c485003885a94b45921a007116aaad1b487400e22d555a3690e801c4b56b68ae42d0038945c28b7b127400e217052dd649a801c45c2ab76d26d00388b8556eda4da00712e1adbab931400e25176a2eac4ad003885dd4ba592ba00711772ae9b4af400e22ee55d3695e801c4b9cf736e56d0038945f28bdb131400e217d52f764c6801c45f6abdad30d00388bed57b5a61a00712d83daeb985400e2500002fac4dd003860000c0d936a0070d842b03b4d9400e2308560769b2801c4b28f64ae6c50038940000bab13d400e197972f164f2801c462cac46d3c500388c59588da78a00712be3d78b9df400e2516ee2dac50d003880000b8d942a0070d92ab1fb509400e2325563f6a12801c4acaf582e83d0038945a38b3b149400e216b72d56522801c4666acbad48500388ccd5975a90a00712a83d4aba3f400e25162e2c2c53d00388595cb2594ea00711a1ab3db53b400e2343567b6a76801c400014f5e9bd0038745738adb155400e215f72bd6556801c46a4ad36d55500388d4d5a6daaaa0071295bd256a49400e250000000055d003840000ad3959a0070d9f3b3db571400e236456bb6ae2801c4a36f455a89d0038940000a97151400e180002aae552801c3658ecaed635003880001abdac6a0070e85bd056a07400e25000029dc53500386545ca8314fa007118e3b1bb5ab400e234476876b56801c49faf3dda7a50038940000a57149400e1800029ae52e801c361aec32d72d00388ccdd98dae5a0071277bce969cb400e25000028dc51500386525ca43147a00711803afeb5eb400e232376456bd6801c49c4f371a6c50038940000a16141400e19457288c50e801c40000bd1d79500386c55d89db06a007126abccf6997400e25140e27d84f500388509ca0b140a007100002e975cf400e18000610ec1a801c3992f311a5f500389400009e713b400e193f727ac4f2801c45beeb7596e500388bf5d7db2faa007125f3cb86967400e2513ae27184dd003884edc9d3139a007116abad365a5400e22f275e0cbbe801c4966f2b5a53d00389400009b7135400e1938726ec4da801c459aeb2d964d00388ba1d7332e5a0071254bca3693b400e25134e26584c5003884d9c9a3133a00711623ac26581400e22de75b8cb6e801c493ef265a49d003894000098612f400e19337264c4c2801c4578eae995c500388b55d6a32d2a007124abc906911400e25000025dc4b5003864c1c97b12da007115abab36563400e22cd7596cb2a801c4918f21da3fd0038944b38956129400e212e725ac4ae801c455ceab1954d00388b15d61b2c1a0071241bc7e68ed400e2512ae251849d003884adc953128a0071153baa56545400e22be7578caea801c48f4f1d5a36d0038940000936125400e19297250c49a801c4540ea7994dd00388addd5ab2b2a00712393c6d68c9400e250000249848d0038649dc933124a007114d3a98652b400e22b0755ccaae801c48d4f195a2e50038940000916121400e19257246c486801c4528ea49947d00388aa5d53b2a5a00712313c5d68a9400e250000241847d0038648dc90b11fa00711473a8c6513400e22a37542ca7a801c48b6f159a26500389400008f611b400e1920723ec476801c4512ea1d941d00388a75d4db298a0071229bc4e6889400e25000023984650038647dc8eb11ba0071141ba8164fd400e2297752aca4a801c4898f11da1ed00389400008d6117400e191d7236c466801c44fce9f193cd00388a49d48328da00712233c40686d400e25000023184550038646dc8d3117a007113cba7764e9400e228c7516ca1e801c487ef0e9a17d00389400008b6115400e19197230c456801c44e8e9cd937d00388a1dd42b282a007121c3c336851400e25116e229844d0038845dc8b3113a00711383a6e64d5400e22827500c9f6801c4864f0b5a10d0038944538896111400e21157228c44a801c44d6e9a9932d003889f5d3e3278a00712163c276837400e25112e221843d00388451c89b110a0071133ba6564c3400e227974eec9ce801c484af085a0a5003894000088610d400e19127222c43a801c44c6e98592ed003889d1d39326ea00712103c1b681d400e25000021d842d00386445c87b10da007112fba5d64b1400e227074dcc9aa801c4834f055a04500389443b886610b400e210f721cc42e801c44b6e96592a5003889b1d353266a007120a3c0f6805400e2510ce215842500388439c863109a007112bba5564a1400e226774ccc986801c481ef0299fed0038940000856107400e190c7216c422801c44a6e94592650038898dd31325da0071204bc0567ef400e25000021184150038642dc84b106a0071127ba4e6493400e226074bcc966801c4808effd9f8d0038944238836105400e21097210c416801c4498e929922d00388971d2d3255a00711ffbbfa67d9400e25106e209840d00388421c83b103a00711243a476483400e225874acc94a801c47f4efd59f3d0038940000826101400e1907720ac40a801c448ae90d91f500388951d29b24ea00711fabbf067c5400e25104e20583fd00388415c823101a00711213a406477400e2251749ec92a801c47e0efad9eed00389400008160ff400e19047206c3fe801c447ce8f591bd00388935d263247a00711f5bbe667b1400e25000020183f50038640dc8130fea007111dba3a6469400e224a7492c90e801c47ceef899e9d00389440387f60fd400e21017200c3f6801c4470e8d9918d0038891dd22b240a00711f13bdd679d400e2500001fd83ed00386401c7fb0fba007111aba33645d400e22447484c8f6801c47bcef659e550038943fb87e60f9400e20ff71fcc3ea801c4464e8c5915d00388901d1fb23aa00711ecbbd5678b400e2500001f983e5003863f9c7eb0f9a0071117ba2e6451400e223d7478c8de801c47aaef419e0d0038943f387d60f7400e20fd71f8c3e2801c445ae8ad912d003888e9d1cb233a00711e8bbcc6779400e250fae1f183dd003883f1c7d30f7a00711153a286445400e2238746cc8c2801c4798ef219dc500389400007c60f5400e18fa71f2c3da801c444ee89590fd003888d5d19b22da00711e43bc46769400e250f8e1ed83cd003883e5c7c30f4a00711123a23643b400e22327460c8ae801c4788ef019d7d00389400007b60f3400e18f871eec3ce801c4444e88190d5003888bdd173228a00711e03bbc6757400e250f6e1e983c5003883ddc7b30f2a007110fba1e642f400e222c7456c896801c477aeee19d3d00389400007a60f1400e18f671eac3c6801c443ae86d90ad003888a9d143222a00711dcbbb46747400e25

def row2 (index : ℕ) : List (List ℕ) :=
  if index < 135 then
    let packedCell := Nat.shiftRight row2PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row3PackedData : ℕ := 0x146c205003860000515880a0070ca2a944b203400e214552896406801c4516aa26d01d003894000051b081400e180001476206801c3000051ec81d003860000a3d903a0070d47aa8eb40f400e25000014ac20d003862954525882a00710a52949b20b400e214a52936416801c4528aa4ad05500389429a852b083400e20a6514b620e801c4298a52ec83d003885314a5d907a007114caa97b41f400e25000014ec21500386000053d884a0070ca7a94eb213400e214f529d6426801c453caa72d09d003894000054b085400e180001516216801c30000546c85d003860000a8d90ba0070d51aaa2b42f400e250aaa152c21d003882a9454d887a00710aa2953b21b400e215452a76436801c4552aa9ed0dd003894000055b089400e180001576222801c32aea55ac8850038855d4ab5910a00711572aacb43f400e25000015ac225003860000565889a0070caca958b225400e215952b1644a801c4566aac6d1250038942ba856b08b400e20ae515b622a801c42b8a56ec8a5003885714add914a007115caab7b451400e25000015ec22d00386000057d88ba0070cafa95eb22d400e215f52bd645a801c457caaf2d165003894000058b08d400e18b151616232801c42c4a586c8c5003885894b0d918a00711622ac2b463400e250000166c235003862c9458d88da00710b2a963b237400e216552c7646e801c4594ab1ed1b5003894000059b08f400e18000167623a801c32cea59ac8ed0038859d4b3591da0071167aacdb475400e25000016ac245003862d545a5890a00710b52969b241400e216a52d36482801c45aaab4ed1fd00389400005bb091400e1800016d6246801c32daa5b2c915003885b54b65922a007116daad9b489400e250b8a16ec24d003882e145bd892a00710b8296fb249400e217052df6492801c45c2ab7ed24d0038942ea85cb093400e20ba5173624e801c42e8a5cac93d003885d14b95927a00711742ae5b49d400e250000176c2550038600005dd895a0070cbba976b255400e217752ed64aa801c45dcabb2d29d00389400005eb097400e18bd5179625a801c42f4a5e6c965003885e94bcd92ca007117a2af2b4b1400e25000017ec25d0038600005f5897a0070cbea97cb25f400e217d52f964be801c45f6abe2d2f500389430285fb099400e20c0517f6266801c4302a5fec98d003886054bfd931a00711812affb4c7400e250c2a182c26d00388309460d89aa00710c22983b269400e2184530764d2801c4610ac1ad345003894000061b09b400e18000187626e801c330ea61ac9bd0038861d4c35937a0071187ab0db4dd400e25000018ac27500386315462589da00710c5a989b275400e218b531364ea801c462cac4ed3a5003894000063b09f400e18c7518d627a801c431ca636c9ed003886394c6d93da007118eab1bb4f3400e250000192c2850038632546458a0a00710c92991b281400e219253236502801c464aac8ad3fd003894000065b0a1400e18cb51956286801c432ca652ca1d003886594ca5943a00711962b29b50b400e25000019ac28d0038600006658a3a0070ccca998b28d400e21995331651a801c4666acc6d465003894000067b0a5400e1800019d6292801c333aa672ca4d003886754ce5949a007119dab38b525400e2500001a2c29d0038600006858a6a0070cd0a9a0b299400e21a153416532801c4686ad02d4c5003894000069b0a9400e180001a5629e801c334aa692ca7d003886954d2594fa00711a5ab48b53f400e2500001aac2a50038600006a58a9a0070cd4a9a8b2a7400e21a95351654e801c46a6ad42d52d00389400006bb0ab400e180001ad62ae801c335aa6b2cab5003886b54d65956a00711adab58b559400e2500001b2c2b50038636546c58ada00710d929b0b2b5400e21b25361656a801c46c8ad82d59d00389400006db0af400e18db51b562ba801c436ca6d2caed003886d94da595da00711b62b69b575400e2500001bac2c50038637546e58b0a00710dd29b9b2c3400e21ba53736586801c46eaadcad60d00389400006fb0b3400e18df51bd62ca801c437ea6f6cb25003886fd4ded964a00711bf2b7bb591400e2500001c2c2d500386000070d8b4a0070ce1a9c2b2d1400e21c3538565a2801c470eae12d685003894392871b0b7400e20e451c762da801c4390a71acb65003887214e3596ca00711c82b8db5b1400e250e6a1cac2e500388399472d8b8a00710e6a9cbb2e1400e21cd539765c2801c4734ae5ad6fd003894000074b0bb400e18e951d162ea801c43a4a742cba5003887494e85974a00711d22ba0b5cf400e2500001d6c2f5003863ad47558bca00710eba9d5b2f1400e21d753ab65e2801c475caeaad77d0038943ba876b0bf400e20ee51db62fa801c43b8a76acbe5003887714ed597ca00711dc2bb4b5f1400e250f0a1dec305003883c1477d8c0a00710f0a9dfb301400e21e153bf6602801c4784aefad805003894000079b0c3400e18f351e5630a801c43cca792cc2d003887994f25985a00711e6abc9b613400e2500001eac315003863d547a58c4a00710f5a9e9b313400e21eb53d36626801c47aeaf4ed8950038943e287bb0c7400e20f851ef631e801c43e2a7becc75003887c54f7d98ea00711f12bdeb637400e2500001f6c325003863ed47d58c9a00710fba9f4b325400e21f753e9664a801c47dcafa6d9250038943fa87eb0cb400e20fe51fb632e801c43f8a7eaccbd003887f14fd5997a00711fcabf5b65d400e250000202c33d0038640548058cea00711012a00b339400e220254016672801c480ab006d9c5003894412881b0d1400e210452076342801c4410a81acd0d0038882150359a1a0071208ac0db685400e25000020ec34d0038641d48358d3a0071107aa0cb34d400e220f5419669a801c483cb066da6500389442a884b0d5400e210a52136356801c442aa84ecd5d00388855509d9aba00712152c25b6ad400e25000021ac3650038643548658d8a007110daa19b363400e221b543366c6801c486eb0cadb0d003894000088b0db400e19115221636e801c4444a882cdb50038888951059b6a0071222ac40b6d9400e25114a226c37d00388451489d8dea0071114aa26b379400e2229544d66f2801c48a4b136dbbd00389446288bb0e1400e2118522d6386801c4460a8b6ce15003888c1516d9c2a00712302c5bb707400e250000236c3950038646d48d58e4a007111baa34b391400e223754696722801c48deb1a6dc7d00389400008fb0e7400e191f523d639e801c447ea8f2ce75003888fd51e59cea007123f2c78b737400e25122a242c3ad0038848d490d8eaa00711232a43b3a9400e224654876752801c491ab21edd4500389449a892b0ed400e2127524b63b6801c449ca92ecedd00388939525d9dba007124e2c96b76b400e2512aa252c3c5003884ad494d8f0a007112b2a53b3c3400e225654a76786801c4958b29ade150038944ba896b0f5400e212f525b63d2801c44bca96ecf450038897952dd9e8a007125eacb6b7a1400e25132a262c3dd003884cd498d8f7a00711332a63b3df400e226654c767be801c499ab31edef500389400009bb0fb400e1937526d63ee801c44dea9b2cfb5003889bd53659f6a007126facd8b7d9400e2513ca276c3fd003884f149d58ffa007113c2a75b3fd400e227854eb67fa801c49e2b3aadfdd00389450289fb103400e2140527f640e801c4502a9fad03500388a0553f5a06a0071281acfcb817400e25144a286c41d003885154a1d907a0071145aa87b41b400e228b550f6836801c4a2cb43ae0d500389452a8a4b10b400e214a5291642e801c4528aa46d0b500388a51548da16a0071294ad22b857400e2514ea29ac43d0038853d4a6d90fa007114f2a9ab43d400e229e5535687a801c4a7ab4d6e1e50038945528a9b113400e215452a5644e801c4552aa96d13d00388aa5552da27a00712a92d4ab89b400e25158a2aec465003885654abd918a0071159aaafb461400e22b3555f68c2801c4aceb57ee2fd00389457a8aeb11d400e215f52bb6472801c457caaead1cd00388af955d5a39a00712bead75b8e3400e25164a2c6c485003885954b15921a00711652ac5b487400e22ca558b690e801c4b28b62ee42d0038945aa8b4b127400e216a52d1649a801c45aaab46d26d00388b55568da4da00712d5ada2b931400e25170a2dec4ad003885c14b7592ba0071170aaddb4af400e22e155bb695e801c4b86b6eae56d0038945da8bab131400e217752e964c6801c45dcaba6d30d00388bb9574da61a00712ee2dd3b985400e2517ca2f6c4dd003885f54bdd936a007117daaf6b4d9400e22fb55ed69b2801c4bc0f77ee6c50038946128c0b13d400e2184530364f2801c4610ac0ed3c500388c21581da78a00712e0bdbfb9df400e250000306c50d003860000c35942a0070d8b2b11b509400e231656236a12801c4b4cf68ee83d0038945eb8bcb149400e217e72fb6522801c464aac7ed48500388c9558fda90a00712c6bd89ba3f400e2500002e6c53d003865d9cbad94ea0071199ab2eb53b400e2333565d6a76801c4aecf5cae9cd0038945b38b5b155400e200002df6556801c3686acf6d55500388d0d59edaaaa00712b0bd5cbaa7400e25166e2cac575003885a5cb4595ca00711a9ab4db571400e2353569b6ae2801c4a9cf525aa450038940000000161400e100002c8e58e801c36bcad76d63500388d915aedac6a007129e3d376a6b400e2500002b9c56d0038657dcaf315da0071000034ab5ab400e1b7556dd6b56801c4a58f499a9250038940000000157400e115a72b2c562801c4670ecded72d003880001b25ae5a0070e8e3d166a29400e2500002a58545003860000ab3954a0070d943b27b5eb400e235176a16bd6801c4a1af41da8250038940000a7614d400e195172a0c53e801c4634ec62d83500388cfdd9f5b06a007127fbcfa69ed400e250000295852500386535ca6314ba0071000030c7615400e1b30765d6c62801c49e4f3b1a7450038945238a36145400e214a7292c522801c40000c01d7f5003860001913b20a0070e72bce069b7400e250000289c50d00386519ca2b144a007117abaf365e5400e2000062aec4e801c39b2f351a6750038940000a0613f400e19437284c502801c45d6eba5973d00388c25d83b306a0071266bcc86985400e2513ee27984ed00388501c9fb13da0071170badf65bb400e22fe75f8cbee801c4986f2f5a5bd00389400009d6139400e193d7278c4ea801c45b0eb5996a500388bd1d7932f1a007125c3cb36959400e25138e26d84d5003884e9c9cb137a0071167bacd6597400e22ea75d0cb9e801c495cf2a5a50d00389400009a6133400e1937726cc4d2801c458eeb15961d00388b85d6fb2dda00712523c9f692f400e250000265c4c5003864d1c99b131a007115fbabd6577400e22d875aecb56801c4936f259a46d0038944c3897612d400e21327262c4be801c4570ead995a500388b41d67b2cca00712493c8d6909400e2512ee25984ad003884bdc97312ca0071158baaf6559400e22c9758ecb16801c4912f211a3dd0038940000956129400e192d7258c4aa801c4554eaa1952d00388b05d6032bda0071240bc7c68e5400e250000251849d003864adc953127a00711523aa2653f400e22ba7572cada801c48f0f1d1a3550038940000936123400e1928724ec496801c453cea7194cd00388ad1d5932afa00712383c6b68c3400e250000249848500386499c92b123a007114c3a966527400e22ad7558caa6801c48d2f191a2cd003894000091611f400e19247246c486801c4524ea41946d00388a9dd5332a2a0071230bc5d68a5400e250000241847500386489c90b11fa0071146ba8b650f400e22a17540ca72801c48b4f155a25500389400008f611b400e1920723ec476801c4510ea19941500388a71d4d3297a0071229bc4e6887400e250000239846500386479c8eb11ba0071141ba8164fb400e2296752aca46801c4898f11da1e500389400008d6117400e191d7236c466801c44fce9f193c500388a45d47b28ba00712233c41686b400e25000023184550038646dc8d3117a007113cba7764e7400e228c7514ca1a801c487ef0e9a17500389446388b6115400e21197230c456801c44e8e9cd937500388a1dd42b281a007121cbc34684f400e25116e229844d0038845dc8b3113a00711383a6e64d5400e22827500c9f2801c4866f0b9a10d0038944538896111400e2116722ac44a801c44d8e9a9932d003889f5d3e3278a00712163c286835400e250000225843d00386451c89b110a0071133ba6664c3400e227974eec9ce801c484ef089a0ad003894000088610d400e19127222c43a801c44c6e98992ed003889d5d39b26fa0071210bc1c681f400e25110e21d842d00388445c88310da007112fba5e64b3400e227074dec9aa801c4836f05da04d00389443b886610b400e210f721cc42e801c44b8e96992ad003889b1d35b266a007120b3c116807400e250000219842500386439c86b10aa007112c3a5664a3400e226874cec98a801c4820f0319fed0038940000856107400e190c7216c422801c44a8e949926d00388991d31b25ea0071205bc0767f1400e2510ae21184150038842dc853107a0071128ba4f6493400e226174bec96a801c480cf0059f9d0038944238836105400e210a7212c416801c449ae92d923500388975d2db256a0071200bbfc67db400e25000020d840d00386421c83b104a00711253a486485400e225974b0c94e801c47f8efe19f4500389441b8826101400e2107720cc40a801c448ce91591fd00388959d2a324fa00711fbbbf367c7400e250000209840500386419c82b101a0071121ba426479400e225274a2c932801c47e4efb99ef500389400008160ff400e19047206c402801c4480e8f991c50038893dd26b248a00711f73be967b3400e25102e20183f50038840dc8130ffa007111eba3b646b400e224c7494c916801c47d2ef959ead00389400008060fd400e19027202c3f6801c4474e8e1919500388925d23b241a00711f2bbe067a1400e25100e1fd83ed00388405c8030fca007111bba35645f400e22457488c8fa801c47c0ef719e5d0038943fb87e60fb400e210071fec3ee801c4468e8c9916500388909d20b23ba00711ee3bd8678f400e2500001f983e5003863fdc7f30faa0071118ba306453400e223f747cc8e2801c47b0ef4d9e150038943f387d60f7400e20fd71f8c3e2801c445ce8b59135003888f1d1db235a00711e9bbcf677d400e2500001f583dd003863f1c7db0f7a00711163a2a6449400e223a7470c8ca801c479eef2d9dd50038943eb87c60f5400e20fb71f4c3da801c4452e89d910d003888ddd1ab22fa00711e5bbc7676d400e25

def row3 (index : ℕ) : List (List ℕ) :=
  if index < 134 then
    let packedCell := Nat.shiftRight row3PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row4PackedData : ℕ := 0x51b081400e180001456206801c328aa512c81d003885154a25903a0071145aa89b40f400e250000146c20d00386000051d882a0070c000147b20b400e1800028f6416801c351eaa3ad055003894000052b083400e18a55149620e801c4294a526c83d003885294a4d907a007114a2a92b41f400e250a6a14ac21500388299452d884a00710a6294bb213400e214c52976426801c4532aa5ed09d003894000053b085400e1800014f6216801c329ea53ac85d0038853d4a7590ba007114f2a9cb42f400e250000152c21d003860000545887a0070c000151b21b400e180002a36436801c3546aa8ad0dd0038942aa854b089400e20aa51536222801c42a8a54ec885003885514a9d910a0071154aaa7b43f400e250000156c22500386000055d889a0070caba956b225400e215752ad644a801c455caab2d125003894000056b08b400e18000159622a801c32b2a562c8a5003885654ac5914a0071159aab1b451400e250aea15ac22d003882b9456d88ba00710ae295bb22d400e215c52b7645a801c4572aaded165003894000057b08d400e1800015f6232801c32bea57ac8c50038857d4af5918a007115f2abcb463400e250000162c235003862c5458588da00710b12961b237400e216252c3646e801c4588ab0ad1b5003894000059b08f400e18b25163623a801c42caa58ec8ed003885954b1d91da00711652ac7b475400e250000166c24500386000059d890a0070cb3a966b241400e216752cd6482801c459eab36d1fd00389400005ab091400e18b551696246801c42d4a5a6c915003885a94b4d922a007116aaad3b489400e25000016ec24d0038600005b5892a0070cb6a96cb249400e216d52d96492801c45b6ab66d24d0038942e285bb093400e20b8516f624e801c42e0a5bec93d003885c14b7d927a0071170aadfb49d400e250baa172c255003882e945cd895a00710ba2972b255400e217452e564aa801c45d0ab96d29d00389400005db097400e18000177625a801c32eea5dac965003885dd4bb592ca00711772aecb4b1400e25000017ac25d003862f545e5897a00710bd2979b25f400e217a52f364be801c45e8abcad2f500389400005fb099400e1800017d6266801c32faa5f2c98d003885f54be5931a007117daaf8b4c7400e250c0a17ec26d0038830145fd89aa00710c0a97fb269400e218152ff64d2801c4604abfed34500389430a860b09b400e20c25183626e801c4308a60ec9bd003886114c1d937a00711842b06b4dd400e250000186c27500386000061d89da0070cc3a986b275400e2187530d64ea801c461eac36d3a5003894000062b09f400e18c55189627a801c4316a626c9ed0038862d4c4d93da007118b2b13b4f3400e25000018ec2850038631d46358a0a00710c7298db281400e218e531b6502801c463aac6ed3fd003894000064b0a1400e18c951916286801c4324a646ca1d003886494c8d943a0071192ab22b50b400e250000196c28d0038632d46558a3a00710cb2994b28d400e21965329651a801c4658aca6d465003894000066b0a5400e180001996292801c3332a662ca4d003886654cc5949a0071199ab31b525400e25000019ec29d0038600006758a6a0070ccea99cb299400e219d53396532801c4676ace2d4c5003894000068b0a9400e180001a1629e801c3342a682ca7d003886854d0594fa00711a1ab40b53f400e2500001a6c2a50038600006958a9a0070cd2a9a4b2a7400e21a55349654e801c4696ad22d52d00389400006ab0ab400e180001a962ae801c3352a6a2cab5003886a54d45956a00711a9ab50b559400e2500001aec2b50038600006b58ada0070cd6a9acb2b5400e21ad5359656a801c46b6ad62d59d00389400006cb0af400e18d951b162ba801c4364a6c2caed003886c94d8595da00711b22b60b575400e2500001b6c2c50038636d46d58b0a00710db29b4b2c3400e21b653696586801c46d8ada6d60d00389400006eb0b3400e18dd51b962ca801c4374a6e6cb25003886e94dcd964a00711baab72b591400e2500001bec2d50038637d46f58b4a00710dfa9bdb2d1400e21bf537b65a2801c46fcadeed685003894000070b0b7400e180001c362da801c3386a70acb650038870d4e1596ca00711c3ab84b5b1400e250e4a1c6c2e500388391471d8b8a00710e429c6b2e1400e21c8538d65c2801c4720ae36d6fd00389439a872b0bb400e20e651cb62ea801c439aa72ecba5003887354e5d974a00711cd2b96b5cf400e2500001d2c2f5003863a547458bca00710e929d0b2f1400e21d253a165e2801c4748ae82d77d003894000075b0bf400e18eb51d562fa801c43aea756cbe50038875d4ead97ca00711d72baab5f1400e250eea1dac305003883b9476d8c0a00710ee29dab301400e21dc53b56602801c4770aed2d8050038943c2877b0c3400e20f051df630a801c43c2a77ecc2d003887854efd985a00711e12bbeb613400e2500001e6c315003863cd47958c4a00710f329e4b313400e21e653c96626801c479aaf26d89500389400007ab0c7400e18f551e9631e801c43d6a7a6cc75003887ad4f4d98ea00711ebabd3b637400e250f8a1eec325003883e147bd8c9a00710f8a9efb325400e21f153df664a801c47c4af7ad92500389400007db0cb400e18fb51f5632e801c43eea7d2ccbd003887dd4fa5997a00711f72be9b65d400e250fea1fac33d003883f947ed8cea00710fe29fab339400e21fc53f56672801c47f2afd6d9c5003894000080b0d1400e190152016342801c4404a802cd0d0038880950059a1a0071202ac01b685400e25104a206c34d00388411481d8d3a00711042a06b34d400e2208540d669a801c4822b036da65003894000083b0d5400e1907520d6356801c441ea832cd5d0038883d50659aba007120f2c19b6ad400e2510aa212c36500388429484d8d8a007110aaa13b363400e2215542766c6801c4854b096db0d003894000086b0db400e190d5219636e801c4436a866cdb50038886d50cd9b6a007121bac32b6d9400e250000222c37d0038644548858dea00711112a20b379400e2222544166f2801c488ab102dbbd003894452889b0e1400e211452276386801c4452a89ace15003888a551359c2a00712292c4db707400e25118a22ec3950038846148b58e4a00711182a2db391400e2230545b6722801c48c0b16edc7d00389400008db0e7400e191b5235639e801c446ea8d2ce75003888dd51a59cea0071237ac69b737400e25000023ec3ad0038647d48f58eaa007111faa3cb3a9400e223f54796752801c48fcb1e2dd4500389448a890b0ed400e2123524363b6801c448ca90ecedd00388919521d9dba0071246ac87b76b400e25126a24ac3c50038849d492d8f0a00711272a4bb3c3400e224e54976786801c4938b25ade150038944aa894b0f5400e212b525363d2801c44aca94ecf4500388959529d9e8a00712562ca6b7a1400e2512ea25ac3dd003884bd496d8f7a007112f2a5bb3df400e225e54b767be801c497ab2dadef50038944ca898b0fb400e2133526363ee801c44cca98ecfb500388999531d9f6a0071266acc7b7d9400e25000026ec3fd003864dd49b58ffa0071137aa6cb3fd400e226f54d967fa801c49beb362dfdd0038944f289db103400e213c5275640e801c44f0a9d6d035003889e153ada06a0071278aceab817400e25140a27ec41d0038850149fd907a0071140aa7eb41b400e228154fd6836801c4a06b3f2e0d50038945128a1b10b400e21455287642e801c4516aa1ed0b500388a2d543da16a007128b2d0eb857400e2514aa292c43d003885294a4590fa007114a2a91b43d400e22945523687a801c4a52b48ae1e500389453a8a6b113400e214f529b644e801c453caa6ad13d00388a7954d5a27a007129ead35b89b400e25154a2a6c465003885514a95918a0071154aaa5b461400e22a9554b68c2801c4aa4b52ae2fd0038945628abb11d400e215952af6472801c4566aabed1cd00388acd557da39a00712b3ad5fb8e3400e2515ea2bac4850038857d4aed921a007115f2abab487400e22be5575690e801c4afab5d6e42d0038945928b1b127400e216552c5649a801c4594ab16d26d00388b29562da4da00712ca2d8bb931400e2516aa2d2c4ad003885a94b4592ba007116aaad1b4af400e22d555a3695e801c4b56b68ae56d0038945c28b7b131400e217052dd64c6801c45c2ab76d30d00388b8556eda61a00712e1adbab985400e25176a2eac4dd003885dd4ba5936a00711772ae9b4d9400e22ee55d369b2801c4bb8b74ee6c50038945f28bdb13d400e217d52f764f2801c45f6abdad3c500388bed57b5a78a00712fb2decb9df400e25184a302c50d003886114c0d942a00711842b03b509400e230856076a12801c400017d6e83d00387462a8c4b149400e218b53116522801c462cac46d48500388c59588da90a00712eb3dd5ba3f400e250000312c53d003860000c6594ea0070d92ab1fb53b400e2325563f6a76801c4b76f6e2e9cd0038946038bfb155400e200003076556801c3666acbad55500388ccd5975aaaa00712d0bd9ebaa7400e2500002f2c575003865f1cbdd95ca00711a1ab3db571400e2343567b6ae2801c4b16f61aeb7d0038945cb8b8b163400e217572e9658e801c46a6ad36d63500388d4d5a6dac6a007100005757ae1400e1d00002d9c5ad003865bdcb7596aa00711b22b5db5ab400e236456bb6b56801c4ac4f575aadd0038940000b37165400e180002d2e5a2801c30000db6d72d00386dd55b75ae5a00712a83d4b6a93400e2500002c5c585003860000b23963a0070dacbb58b5eb400e238757016bd6801c4a7ef4e9a9bd0038940000ae615b400e180002bee57a801c368eed1ad835003880001ba5b06a0070e97bd2a6a4d400e2500002b1c55d0038656dcad3159a007119b3b35b631400e236076bf6c62801c4a40f46da8bd0038940000aa7153400e180002aee556801c30000ca1d93500386d3dda6db2ba00712893d0d6a11400e2500002a1c53d0038654dca93151a0071000031a7631400e1800067eecf6801c3a08f3fda7d50038940000a6714b400e194f729cc536801c461cec31985d00388000198bb2fa0070e7bbcf269d9400e250000291851d0038652dca53149a00711813b0165ff400e23247644cc86801c49d6f399a70500389451b8a26143400e2148728ec516801c45f0ebd997ad00388c5dd8b3315a007126fbcda69a7400e250000285c50500386515ca23142a00711773aec65d5400e230c7614cc26801c49a8f33da64500389400009f613d400e19427282c4fe801c45c8eb8d970d00388c05d8032fea0071264bcc4697b400e25000027984ed003864fdc9f313ca007116e3ada65b1400e22f875eccbd2801c497ef2e9a5950038944eb89c6137400e213c7276c4e6801c45a6eb49967d00388bb9d76b2eba007125abcb0694f400e25000026d84d5003864e5c9c3136a0071165baca658f400e22e675c8cb8a801c4956f29da4f500389400009a6131400e1936726ac4ce801c4588eb0995fd00388b75d6e32d9a00712513c9d6929400e25132e26184bd003884d1c99b131a007115ebabb6571400e22d575a8cb46801c4932f251a45d0038944c3897612d400e21317260c4ba801c456cead1958d00388b39d6632c9a00712483c8c6905400e25000025984ad003864bdc97312ca0071157baae6555400e22c7758acb0a801c4910f20da3cd0038940000956129400e192d7258c4a6801c4552ea9d952500388b01d5f32bba00712403c7b68e1400e2500002518495003864adc953127a0071151baa1653b400e22b97570cad2801c48f0f1d1a3450038940000936123400e1928724ec496801c453aea6d94c500388acdd58b2aea0071238bc6c68c1400e250000249848500386499c92b123a007114c3a966525400e22ad7556caa2801c48d2f191a2c5003894000091611f400e19247246c486801c4524ea45946500388a9dd52b2a2a00712313c5d68a3400e250000241847500386489c90b11fa0071146ba8b650f400e22a17540ca72801c48b6f159a25500389400008f611b400e19217240c476801c4510ea19941500388a71d4d3296a007122a3c506887400e25000023984650038647dc8f311ba0071141ba8164fb400e2297752aca46801c489af125a1e500389400008d6117400e191d7238c466801c44fce9f593c500388a49d48328ca0071223bc42686b400e2511ae231845d0038846dc8d3117a007113d3a7864e7400e228d7516ca1e801c4882f0f1a17d00389446388b6115400e21197230c456801c44eae9d1937d00388a21d433282a007121d3c366851400e25116e229844d00388461c8bb114a0071138ba6f64d5400e22837504c9f6801c4868f0c1a11500389400008a6111400e1916722ac44a801c44dae9ad9335003889fdd3eb278a00712173c2a6839400e250000225843d00386455c8a3110a0071134ba6764c5400e227a74f2c9d2801c4852f091a0b500389444b888610d400e21137224c43e801c44cae98d92f5003889d9d3ab270a0071211bc1f6821400e25110e21d843500388449c88b10da0071130ba5f64b5400e227274e2c9b2801c483cf065a055003894000087610b400e1910721ec432801c44bae97192b5003889b9d36b267a007120c3c14680b400e25000021984250038643dc87310aa007112d3a5864a5400e226a74d2c98e801c4826f03d9ffd0038944338856107400e210d7218c426801c44ace951927d00388999d32b260a00712073c0a67f5400e250000215841d00386431c85b107a0071129ba516497400e226374c2c972801c4812f0119fa50038940000846105400e190b7214c41a801c449ee93992450038897dd2f3258a00712023c0067e1400e25108e20d840d00388425c843104a00711263a4a6489400e225c74b4c952801c47feefed9f550038940000836103400e1908720ec40e801c4492e91d920d00388961d2bb251a00711fd3bf667cb400e25000020984050038641dc833102a0071122ba44647b400e225574a6c93a801c47eaefc59f0d00389441388160ff400e21057208c402801c4484e90591d500388945d28324aa00711f8bbed67b9400e25000020583fd00386411c81b0ffa007111fba3e646f400e224e749ac91e801c47d8efa19ebd00389440b88060fd400e21037204c3fa801c4478e8ed91a50038892dd253244a00711f43be467a7400e25000020183f500386409c80b0fda007111cba386463400e2248748ec902801c47c8ef7d9e7500389400007f60fb400e19017200c3f2801c446ce8d5917500388915d22323da00711efbbdb6793400e25

def row4 (index : ℕ) : List (List ℕ) :=
  if index < 133 then
    let packedCell := Nat.shiftRight row4PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row5PackedData : ℕ := 0x146c20d003860000515882a0070ca2a944b20b400e214552896416801c4516aa26d055003894000051b083400e18000147620e801c3000051ec83d003860000a3d907a0070d47aa8eb41f400e25000014ac215003862954525884a00710a52949b213400e214a52936426801c4528aa4ad09d00389429a852b085400e20a6514b6216801c4298a52ec85d003885314a5d90ba007114caa97b42f400e25000014ec21d00386000053d887a0070ca7a94eb21b400e214f529d6436801c453caa72d0dd003894000054b089400e180001516222801c30000546c885003860000a8d910a0070d51aaa2b43f400e250aaa152c225003882a9454d889a00710aa2953b225400e215452a7644a801c4552aa9ed125003894000055b08b400e18000157622a801c32aea55ac8a50038855d4ab5914a00711572aacb451400e25000015ac22d00386000056588ba0070caca958b22d400e215952b1645a801c4566aac6d1650038942ba856b08d400e20ae515b6232801c42b8a56ec8c5003885714add918a007115caab7b463400e25000015ec23500386000057d88da0070cafa95eb237400e215f52bd646e801c457caaf2d1b5003894000058b08f400e18b15161623a801c42c4a586c8ed003885894b0d91da00711622ac2b475400e250000166c245003862c9458d890a00710b2a963b241400e216552c76482801c4594ab1ed1fd003894000059b091400e180001676246801c32cea59ac9150038859d4b35922a0071167aacdb489400e25000016ac24d003862d545a5892a00710b52969b249400e216a52d36492801c45aaab4ed24d00389400005bb093400e1800016d624e801c32daa5b2c93d003885b54b65927a007116daad9b49d400e250b8a16ec255003882e145bd895a00710b8296fb255400e217052df64aa801c45c2ab7ed29d0038942ea85cb097400e20ba5173625a801c42e8a5cac965003885d14b9592ca00711742ae5b4b1400e250000176c25d0038600005dd897a0070cbba976b25f400e217752ed64be801c45dcabb2d2f500389400005eb099400e18bd51796266801c42f4a5e6c98d003885e94bcd931a007117a2af2b4c7400e25000017ec26d0038600005f589aa0070cbea97cb269400e217d52f964d2801c45f6abe2d34500389430285fb09b400e20c0517f626e801c4302a5fec9bd003886054bfd937a00711812affb4dd400e250c2a182c27500388309460d89da00710c22983b275400e2184530764ea801c4610ac1ad3a5003894000061b09f400e18000187627a801c330ea61ac9ed0038861d4c3593da0071187ab0db4f3400e25000018ac2850038631546258a0a00710c5a989b281400e218b53136502801c462cac4ed3fd003894000063b0a1400e18c7518d6286801c431ca636ca1d003886394c6d943a007118eab1bb50b400e250000192c28d0038632546458a3a00710c92991b28d400e21925323651a801c464aac8ad465003894000065b0a5400e18cb51956292801c432ca652ca4d003886594ca5949a00711962b29b525400e25000019ac29d0038600006658a6a0070ccca998b299400e219953316532801c4666acc6d4c5003894000067b0a9400e1800019d629e801c333aa672ca7d003886754ce594fa007119dab38b53f400e2500001a2c2a50038600006858a9a0070cd0a9a0b2a7400e21a15341654e801c4686ad02d52d003894000069b0ab400e180001a562ae801c334aa692cab5003886954d25956a00711a5ab48b559400e2500001aac2b50038600006a58ada0070cd4a9a8b2b5400e21a95351656a801c46a6ad42d59d00389400006bb0af400e180001ad62ba801c335aa6b2caed003886b54d6595da00711adab58b575400e2500001b2c2c50038636546c58b0a00710d929b0b2c3400e21b253616586801c46c8ad82d60d00389400006db0b3400e18db51b562ca801c436ca6d2cb25003886d94da5964a00711b62b69b591400e2500001bac2d50038637546e58b4a00710dd29b9b2d1400e21ba537365a2801c46eaadcad68500389400006fb0b7400e18df51bd62da801c437ea6f6cb65003886fd4ded96ca00711bf2b7bb5b1400e2500001c2c2e500386000070d8b8a0070ce1a9c2b2e1400e21c3538565c2801c470eae12d6fd003894392871b0bb400e20e451c762ea801c4390a71acba5003887214e35974a00711c82b8db5cf400e250e6a1cac2f500388399472d8bca00710e6a9cbb2f1400e21cd539765e2801c4734ae5ad77d003894000074b0bf400e18e951d162fa801c43a4a742cbe5003887494e8597ca00711d22ba0b5f1400e2500001d6c305003863ad47558c0a00710eba9d5b301400e21d753ab6602801c475caeaad8050038943ba876b0c3400e20ee51db630a801c43b8a76acc2d003887714ed5985a00711dc2bb4b613400e250f0a1dec315003883c1477d8c4a00710f0a9dfb313400e21e153bf6626801c4784aefad895003894000079b0c7400e18f351e5631e801c43cca792cc75003887994f2598ea00711e6abc9b637400e2500001eac325003863d547a58c9a00710f5a9e9b325400e21eb53d3664a801c47aeaf4ed9250038943e287bb0cb400e20f851ef632e801c43e2a7beccbd003887c54f7d997a00711f12bdeb65d400e2500001f6c33d003863ed47d58cea00710fba9f4b339400e21f753e96672801c47dcafa6d9c50038943fa87eb0d1400e20fe51fb6342801c43f8a7eacd0d003887f14fd59a1a00711fcabf5b685400e250000202c34d0038640548058d3a00711012a00b34d400e22025401669a801c480ab006da65003894412881b0d5400e210452076356801c4410a81acd5d0038882150359aba0071208ac0db6ad400e25000020ec3650038641d48358d8a0071107aa0cb363400e220f541966c6801c483cb066db0d00389442a884b0db400e210a5213636e801c442aa84ecdb500388855509d9b6a00712152c25b6d9400e25000021ac37d0038643548658dea007110daa19b379400e221b543366f2801c486eb0cadbbd003894000088b0e1400e191152216386801c4444a882ce150038888951059c2a0071222ac40b707400e25114a226c39500388451489d8e4a0071114aa26b391400e2229544d6722801c48a4b136dc7d00389446288bb0e7400e2118522d639e801c4460a8b6ce75003888c1516d9cea00712302c5bb737400e250000236c3ad0038646d48d58eaa007111baa34b3a9400e223754696752801c48deb1a6dd4500389400008fb0ed400e191f523d63b6801c447ea8f2cedd003888fd51e59dba007123f2c78b76b400e25122a242c3c50038848d490d8f0a00711232a43b3c3400e224654876786801c491ab21ede1500389449a892b0f5400e2127524b63d2801c449ca92ecf4500388939525d9e8a007124e2c96b7a1400e2512aa252c3dd003884ad494d8f7a007112b2a53b3df400e225654a767be801c4958b29adef50038944ba896b0fb400e212f525b63ee801c44bca96ecfb50038897952dd9f6a007125eacb6b7d9400e25132a262c3fd003884cd498d8ffa00711332a63b3fd400e226654c767fa801c499ab31edfdd00389400009bb103400e1937526d640e801c44dea9b2d035003889bd5365a06a007126facd8b817400e2513ca276c41d003884f149d5907a007113c2a75b41b400e227854eb6836801c49e2b3aae0d500389450289fb10b400e2140527f642e801c4502a9fad0b500388a0553f5a16a0071281acfcb857400e25144a286c43d003885154a1d90fa0071145aa87b43d400e228b550f687a801c4a2cb43ae1e500389452a8a4b113400e214a5291644e801c4528aa46d13d00388a51548da27a0071294ad22b89b400e2514ea29ac4650038853d4a6d918a007114f2a9ab461400e229e553568c2801c4a7ab4d6e2fd0038945528a9b11d400e215452a56472801c4552aa96d1cd00388aa5552da39a00712a92d4ab8e3400e25158a2aec485003885654abd921a0071159aaafb487400e22b3555f690e801c4aceb57ee42d00389457a8aeb127400e215f52bb649a801c457caaead26d00388af955d5a4da00712bead75b931400e25164a2c6c4ad003885954b1592ba00711652ac5b4af400e22ca558b695e801c4b28b62ee56d0038945aa8b4b131400e216a52d164c6801c45aaab46d30d00388b55568da61a00712d5ada2b985400e25170a2dec4dd003885c14b75936a0071170aaddb4d9400e22e155bb69b2801c4b86b6eae6c50038945da8bab13d400e217752e964f2801c45dcaba6d3c500388bb9574da78a00712ee2dd3b9df400e2517ca2f6c50d003885f54bdd942a007117daaf6b509400e22fb55ed6a12801c4becb7b2e83d0038946128c0b149400e218453036522801c4610ac0ed48500388c21581da90a0071308ae07ba3f400e2518aa312c53d0038862d4c4594ea007118b2b11b53b400e231656236a76801c4000183ae9cd00387464a8c7b155400e2192531f6556801c464aac7ed55500388c9558fdaaaa00712f83deebaa7400e25000031ec575003860000c9d95ca0070d99ab2eb571400e2333565d6ae2801c4ba6f742eb7d0038940000c3b163400e18000315658e801c3686acf6d63500388d0d59edac6a00712dd3db6bb19400e2500002fec5ad0038660dcc1596aa00711a9ab4db5ab400e2353569b6b56801c4000168decf50038740000bcb173400e197c72f765ca801c46c8ad76d72d00388d915aedae5a00712c6bd886b0f400e2500002e5c5c5003860000bb3975a0070dbaab6eb5eb400e237556dd6bd6801c4af2f5d1ab95003894000000016d400e100002e0e5be801c30000e02d83500386e1d5c05b06a00712b33d626abf400e2500002d1c59d003865adcb53169a0071000036bb631400e1b9a57276c62801c4aaaf541aa6d0038940000b16161400e196672cac592801c46b2ed62d95d00388e21dc3db2ba00712a2bd406a79400e2500002bdc57500386585cb0315fa00711a43b46b67d400e200006e76cfa801c3a6af4c5a9650038940000ad7159400e195d72b8c56e801c40000ce5d9bd00386d89db05b53a0071293bd226a3b400e2500002adc55500386565cabb156a0071195bb296651400e235176a0cd3e801c4a32f451a8750038940000a97151400e195572a8c54a801c463cec7598dd00388d09da0b340a00712863d076a01400e25000029d853500386545ca8314ea00711893b11661f400e23357666ccca801c49fef3eda79d0038940000a56149400e194d7298c52e801c460eec19982500388ca1d93b325a0071279bcee69cf400e25148e28d851500388529ca4b147a007117ebafb65f3400e231d7636cc66801c49d0f38da6dd0038940000a26143400e1947728cc512801c45e6ebc9977d00388c49d88330ea007126e3cd8699f400e25142e28184fd00388511ca1b141a00711753ae965cd400e2307760ccc12801c49a4f335a62500389400009f613d400e19417280c4fa801c45c4eb8196ed00388bf9d7e32faa00712643cc36975400e2513ce27584e5003884f9c9eb13ba007116cbad865ab400e22f575e6cbc6801c497cf2e5a57d0038944eb89c6137400e213b7274c4e2801c45a2eb41966d00388bb1d75b2e8a007125a3cb0694b400e25000026d84d5003864e5c9c3135a00711653ac9658b400e22e475c4cb82801c4956f29da4e500389400009a6131400e1936726ac4ce801c4586eb0995f500388b71d6db2d8a00712513c9e6927400e25132e26184bd003884d1c99b130a007115e3abb656f400e22d575a6cb42801c4932f255a4550038944c3897612d400e21327262c4ba801c456cead1958500388b35d6632c9a0071248bc8d6903400e2512ee25984ad003884bdc97312ca00711583aae6555400e22c7758acb0a801c4912f215a3cd0038940000956129400e192d7258c4a6801c4552eaa1952500388b01d5fb2bba0071240bc7d68e3400e2500002518495003864adc953127a00711523aa2653d400e22ba7570cad6801c48f4f1d9a34d0038940000936123400e19297250c496801c453cea7594c500388ad1d5932aea00712393c6e68c3400e25000024984850038649dc933123a007114cba976527400e22ae755acaa2801c48d6f19da2cd003894000091611f400e19257248c486801c4528ea49946d00388aa1d53b2a3a00712323c6068a5400e25122e24184750038848dc91311fa00711473a8d6511400e22a37544ca76801c48baf165a25d00389448388f611b400e21217240c476801c4514ea21941d00388a79d4e3298a007122bbc526889400e2511ee239846d0038800008fb11ba0070d42ba8364fd400e2299752eca4a801c48a0f131a1ed00389447388d6119400e211e723ac466801c4500e9fd93d500388a51d49328da00712253c45686f400e250000235845d00386471c8db118a007113e3a7a64eb400e228f751aca22801c4886f0fda18500389400008c6115400e191a7232c45a801c44eee9d9938500388a29d44b284a007121ebc396855400e25000022d844d00386465c8c3114a0071139ba7264d9400e22867508c9fe801c4870f0d1a12500389445b88a6111400e2117722cc44e801c44dee9b9934500388a05d40327ba00712193c2e683d400e25114e225844500388459c8ab111a0071135ba6a64c9400e227d74f8c9da801c4858f0a1a0c5003894000089610f400e19147226c43e801c44cee9999305003889e5d3c3272a0071213bc236827400e25000022184350038644dc89310ea00711323a6264b9400e227574e6c9ba801c4842f075a06d003894443887610b400e21117220c432801c44c0e97992c5003889c5d38326aa007120e3c18680f400e25000021d842d00386441c87b10ba007112e3a5b64ab400e226d74d8c99a801c482ef04da0150038940000866109400e190e721ac426801c44b2e95d928d003889a5d343262a00712093c0e67fb400e2510ce215841d00388435c863108a007112aba54649b400e226674c8c97a801c481af0259fc500389442b8846105400e210c7216c41e801c44a4e941925500388989d30b25ba00712043c0467e7400e250000211841500386429c84b105a0071127ba4d648f400e225f74bac95e801c4806effd9f750038944238836103400e21097210c412801c4496e929921d0038896dd2d3254a00711ff3bfa67d3400e25000020d840500386421c83b103a00711243a476481400e225874aec942801c47f4efd99f250038940000826101400e1907720cc406801c448ae91191ed00388955d29b24da00711fabbf167bf400e25

def row5 (index : ℕ) : List (List ℕ) :=
  if index < 132 then
    let packedCell := Nat.shiftRight row5PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row6PackedData : ℕ := 0x51b083400e18000145620e801c328aa512c83d003885154a25907a0071145aa89b41f400e250000146c21500386000051d884a0070c000147b213400e1800028f6426801c351eaa3ad09d003894000052b085400e18a551496216801c4294a526c85d003885294a4d90ba007114a2a92b42f400e250a6a14ac21d00388299452d887a00710a6294bb21b400e214c52976436801c4532aa5ed0dd003894000053b089400e1800014f6222801c329ea53ac8850038853d4a75910a007114f2a9cb43f400e250000152c225003860000545889a0070c000151b225400e180002a3644a801c3546aa8ad1250038942aa854b08b400e20aa5153622a801c42a8a54ec8a5003885514a9d914a0071154aaa7b451400e250000156c22d00386000055d88ba0070caba956b22d400e215752ad645a801c455caab2d165003894000056b08d400e180001596232801c32b2a562c8c5003885654ac5918a0071159aab1b463400e250aea15ac235003882b9456d88da00710ae295bb237400e215c52b7646e801c4572aaded1b5003894000057b08f400e1800015f623a801c32bea57ac8ed0038857d4af591da007115f2abcb475400e250000162c245003862c54585890a00710b12961b241400e216252c36482801c4588ab0ad1fd003894000059b091400e18b251636246801c42caa58ec915003885954b1d922a00711652ac7b489400e250000166c24d00386000059d892a0070cb3a966b249400e216752cd6492801c459eab36d24d00389400005ab093400e18b55169624e801c42d4a5a6c93d003885a94b4d927a007116aaad3b49d400e25000016ec2550038600005b5895a0070cb6a96cb255400e216d52d964aa801c45b6ab66d29d0038942e285bb097400e20b8516f625a801c42e0a5bec965003885c14b7d92ca0071170aadfb4b1400e250baa172c25d003882e945cd897a00710ba2972b25f400e217452e564be801c45d0ab96d2f500389400005db099400e180001776266801c32eea5dac98d003885dd4bb5931a00711772aecb4c7400e25000017ac26d003862f545e589aa00710bd2979b269400e217a52f364d2801c45e8abcad34500389400005fb09b400e1800017d626e801c32faa5f2c9bd003885f54be5937a007117daaf8b4dd400e250c0a17ec2750038830145fd89da00710c0a97fb275400e218152ff64ea801c4604abfed3a500389430a860b09f400e20c25183627a801c4308a60ec9ed003886114c1d93da00711842b06b4f3400e250000186c28500386000061d8a0a0070cc3a986b281400e2187530d6502801c461eac36d3fd003894000062b0a1400e18c551896286801c4316a626ca1d0038862d4c4d943a007118b2b13b50b400e25000018ec28d0038631d46358a3a00710c7298db28d400e218e531b651a801c463aac6ed465003894000064b0a5400e18c951916292801c4324a646ca4d003886494c8d949a0071192ab22b525400e250000196c29d0038632d46558a6a00710cb2994b299400e219653296532801c4658aca6d4c5003894000066b0a9400e18000199629e801c3332a662ca7d003886654cc594fa0071199ab31b53f400e25000019ec2a50038600006758a9a0070ccea99cb2a7400e219d5339654e801c4676ace2d52d003894000068b0ab400e180001a162ae801c3342a682cab5003886854d05956a00711a1ab40b559400e2500001a6c2b50038600006958ada0070cd2a9a4b2b5400e21a55349656a801c4696ad22d59d00389400006ab0af400e180001a962ba801c3352a6a2caed003886a54d4595da00711a9ab50b575400e2500001aec2c50038600006b58b0a0070cd6a9acb2c3400e21ad53596586801c46b6ad62d60d00389400006cb0b3400e18d951b162ca801c4364a6c2cb25003886c94d85964a00711b22b60b591400e2500001b6c2d50038636d46d58b4a00710db29b4b2d1400e21b6536965a2801c46d8ada6d68500389400006eb0b7400e18dd51b962da801c4374a6e6cb65003886e94dcd96ca00711baab72b5b1400e2500001bec2e50038637d46f58b8a00710dfa9bdb2e1400e21bf537b65c2801c46fcadeed6fd003894000070b0bb400e180001c362ea801c3386a70acba50038870d4e15974a00711c3ab84b5cf400e250e4a1c6c2f500388391471d8bca00710e429c6b2f1400e21c8538d65e2801c4720ae36d77d00389439a872b0bf400e20e651cb62fa801c439aa72ecbe5003887354e5d97ca00711cd2b96b5f1400e2500001d2c305003863a547458c0a00710e929d0b301400e21d253a16602801c4748ae82d805003894000075b0c3400e18eb51d5630a801c43aea756cc2d0038875d4ead985a00711d72baab613400e250eea1dac315003883b9476d8c4a00710ee29dab313400e21dc53b56626801c4770aed2d8950038943c2877b0c7400e20f051df631e801c43c2a77ecc75003887854efd98ea00711e12bbeb637400e2500001e6c325003863cd47958c9a00710f329e4b325400e21e653c9664a801c479aaf26d92500389400007ab0cb400e18f551e9632e801c43d6a7a6ccbd003887ad4f4d997a00711ebabd3b65d400e250f8a1eec33d003883e147bd8cea00710f8a9efb339400e21f153df6672801c47c4af7ad9c500389400007db0d1400e18fb51f56342801c43eea7d2cd0d003887dd4fa59a1a00711f72be9b685400e250fea1fac34d003883f947ed8d3a00710fe29fab34d400e21fc53f5669a801c47f2afd6da65003894000080b0d5400e190152016356801c4404a802cd5d0038880950059aba0071202ac01b6ad400e25104a206c36500388411481d8d8a00711042a06b363400e2208540d66c6801c4822b036db0d003894000083b0db400e1907520d636e801c441ea832cdb50038883d50659b6a007120f2c19b6d9400e2510aa212c37d00388429484d8dea007110aaa13b379400e2215542766f2801c4854b096dbbd003894000086b0e1400e190d52196386801c4436a866ce150038886d50cd9c2a007121bac32b707400e250000222c3950038644548858e4a00711112a20b391400e222254416722801c488ab102dc7d003894452889b0e7400e21145227639e801c4452a89ace75003888a551359cea00712292c4db737400e25118a22ec3ad0038846148b58eaa00711182a2db3a9400e2230545b6752801c48c0b16edd4500389400008db0ed400e191b523563b6801c446ea8d2cedd003888dd51a59dba0071237ac69b76b400e25000023ec3c50038647d48f58f0a007111faa3cb3c3400e223f54796786801c48fcb1e2de1500389448a890b0f5400e2123524363d2801c448ca90ecf4500388919521d9e8a0071246ac87b7a1400e25126a24ac3dd0038849d492d8f7a00711272a4bb3df400e224e549767be801c4938b25adef50038944aa894b0fb400e212b525363ee801c44aca94ecfb500388959529d9f6a00712562ca6b7d9400e2512ea25ac3fd003884bd496d8ffa007112f2a5bb3fd400e225e54b767fa801c497ab2dadfdd0038944ca898b103400e21335263640e801c44cca98ed03500388999531da06a0071266acc7b817400e25000026ec41d003864dd49b5907a0071137aa6cb41b400e226f54d96836801c49beb362e0d50038944f289db10b400e213c5275642e801c44f0a9d6d0b5003889e153ada16a0071278aceab857400e25140a27ec43d0038850149fd90fa0071140aa7eb43d400e228154fd687a801c4a06b3f2e1e50038945128a1b113400e21455287644e801c4516aa1ed13d00388a2d543da27a007128b2d0eb89b400e2514aa292c465003885294a45918a007114a2a91b461400e2294552368c2801c4a52b48ae2fd00389453a8a6b11d400e214f529b6472801c453caa6ad1cd00388a7954d5a39a007129ead35b8e3400e25154a2a6c485003885514a95921a0071154aaa5b487400e22a9554b690e801c4aa4b52ae42d0038945628abb127400e215952af649a801c4566aabed26d00388acd557da4da00712b3ad5fb931400e2515ea2bac4ad0038857d4aed92ba007115f2abab4af400e22be5575695e801c4afab5d6e56d0038945928b1b131400e216552c564c6801c4594ab16d30d00388b29562da61a00712ca2d8bb985400e2516aa2d2c4dd003885a94b45936a007116aaad1b4d9400e22d555a369b2801c4b56b68ae6c50038945c28b7b13d400e217052dd64f2801c45c2ab76d3c500388b8556eda78a00712e1adbab9df400e25176a2eac50d003885dd4ba5942a00711772ae9b509400e22ee55d36a12801c4bb8b74ee83d0038945f28bdb149400e217d52f76522801c45f6abdad48500388bed57b5a90a00712fb2decba3f400e25184a302c53d003886114c0d94ea00711842b03b53b400e230856076a76801c4c22b81ee9cd00389462a8c4b155400e218b53116556801c462cac46d55500388c59588daaaa0071316ae22baa7400e25192a31ec575003886494c7d95ca0071192ab1fb571400e2325563f6ae2801c4c5cf8b6eb7d0038946628cbb163400e2199532f658e801c4666acbad63500388ccd5975ac6a00713073e0cbb19400e25000032ec5ad003860000ce596aa0070da1ab3db5ab400e2343567b6b56801c4be2f7baed550038940000c7b173400e1993732565ca801c46a6ad36d72d00388d4d5a6dae5a00712eb3dd2bb93400e25000030ec5ed0038662dcc5597aa00711b22b5db5eb400e236456bb6bd6801c4b7cf6e9adcd0038940000c0717f400e18000308e60e801c36eaadbad83500388dd55b75b06a00712d4bda46b47400e2500002f5c5e5003865f9cbeb17ca00711c3ab80b631400e238757016c62801c4b28f641ac6d0038940000ba7173400e197872eec5da801c4730ae4ed95d00388e695c9db2ba00712c0bd7c6af3400e2500002dd85b5003865c9cb8b170a00711c13b81b67d400e23ae574d6cfa801c4adef5adab350038940000b57169400e196d72d8c5ae801c46dcedb6da9d003880001d05b53a0070eaf3d5a6aab400e2500002c9858d003865a1cb3b166a00711aebb5c66b7400e238b77156da6801c4a9cf529aa250038940000b0615f400e196472c6c586801c469aed319a5d003880001bc3b77a0070e9fbd3a6a69400e2500002b9856d0038657dcaf315da007119fbb3d6679400e236776cccd96801c4a62f4b5a9350038940000ac6157400e195b72b4c566801c4662ecc1997d00388d61dabb356a0071291bd1f6a31400e2500002a9854d00386561cabb155a0071192bb246645400e234a7690cd1e801c4a2cf449a85500389454b8a8614f400e215472a6c546801c4634ec6198b500388cf1d9db339a0071284bd0569fb400e2514ee299852d003880000a8314ea0070d87bb0d6617400e2330765eccb6801c49faf3e5a7850038940000a56149400e194d7298c52a801c460aec0d980d00388c95d91b321a00712793cee69cb400e25148e28d851500388529ca4b147a007117dbafa65ef400e231a7632cc5a801c49cef38da6cd0038940000a26143400e1947728cc512801c45e4ebc5977500388c41d87b30ca007126ebcd9699d400e25142e28184fd00388511ca1b141a00711753ae865cb400e2306760acc0a801c49a4f339a62500389400009f613d400e19417280c4fa801c45c2eb8196ed00388bf5d7e32f9a00712643cc46973400e25000027984e5003864fdc9f313ba007116d3ad865ab400e22f575e6cbc2801c497ef2eda5850038944eb89c6137400e213c7276c4e2801c45a4eb45966d00388bb5d75b2e8a007125b3cb2694d400e25138e26d84d50038800009cb136a0070d65baca658d400e22e575c6cb82801c495af2a5a4ed00389400009a6131400e1937726cc4ce801c4588eb0d95fd00388b75d6e32d8a00712523ca06929400e25000026584bd003864d5c9a3131a007115f3abc6571400e22d675aacb46801c4938f261a45d003894000098612d400e18000264c4be801c356eead9959500388b3dd6732caa007124a3c906907400e25000025d84ad003864c1c97b12ca0071158bab06557400e22c97590cb0e801c4918f221a3dd0038944b38956129400e212e725ac4aa801c4558eaa9952d00388b0dd60b2bda00712423c8168e7400e2512ae251849d003884b1c95b128a00711533aa56541400e22bc7576cada801c48faf1e5a35d0038944a38936125400e212a7252c49a801c4542ea7d94d500388addd5ab2b1a007123b3c7268c7400e25126e249848d003884a1c93b124a007114dba9a652b400e22b17560caae801c48def1ada2e50038940000926121400e1926724ac48a801c452cea55948500388aadd5532a5a00712343c6468ab400e250000245847d00386491c91b120a0071148ba906515400e22a6754aca82801c48c2f175a275003894000090611d400e18000244c47a801c351aea2d943500388a85d50329aa007122d3c57688f400e25000023d846d00386485c90311ca00711443a876503400e229c7536ca56801c48a8f145a20d00389400008e6119400e191f723cc46a801c4508ea0993e500388a5dd4b3290a00712273c4a6875400e2511ce235845d00388475c8e3119a007113fba7e64f1400e22927522ca32801c4890f111a1a500389446b88c6115400e211c7236c45e801c44f6e9e5939d00388a39d46b287a00712213c3e685d400e250000231845500386469c8cb115a007113bba7564df400e22897510ca0a801c4878f0e1a14500389400008b6113400e19197230c452801c44e6e9c5935d00388a15d42327ea007121b3c336845400e25116e22984450038845dc8b3112a0071137ba6d64cf400e22817500c9ea801c4862f0b5a0e5003894453889610f400e2000022ac446801c34d6e9a9931d003889f5d3db275a0071215bc28682d400e250000225843d00386451c89b10fa0071133ba6664bf400e227974f0c9c6801c484cf089a08d003894000088610d400e19137224c43a801c44c6e98992dd003889d5d3a326da0071210bc1d6817400e25110e21d842d00388445c88310ca00711303a5f64b1400e227174e0c9aa801c4838f061a0350038940000876109400e1910721ec42e801c44bae96d92a5003889b5d363266a007120bbc136803400e2500002198425003860000873109a0070d2cba5864a3400e226a74d2c98a801c4824f0399fe50038944338856107400e210d7218c422801c44ace951926d00388999d32b25ea0071206bc0967ef400e25

def row6 (index : ℕ) : List (List ℕ) :=
  if index < 131 then
    let packedCell := Nat.shiftRight row6PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row7PackedData : ℕ := 0x146c215003860000515884a0070ca2a944b213400e214552896426801c4516aa26d09d003894000051b085400e180001476216801c3000051ec85d003860000a3d90ba0070d47aa8eb42f400e25000014ac21d003862954525887a00710a52949b21b400e214a52936436801c4528aa4ad0dd00389429a852b089400e20a6514b6222801c4298a52ec885003885314a5d910a007114caa97b43f400e25000014ec22500386000053d889a0070ca7a94eb225400e214f529d644a801c453caa72d125003894000054b08b400e18000151622a801c30000546c8a5003860000a8d914a0070d51aaa2b451400e250aaa152c22d003882a9454d88ba00710aa2953b22d400e215452a7645a801c4552aa9ed165003894000055b08d400e180001576232801c32aea55ac8c50038855d4ab5918a00711572aacb463400e25000015ac23500386000056588da0070caca958b237400e215952b1646e801c4566aac6d1b50038942ba856b08f400e20ae515b623a801c42b8a56ec8ed003885714add91da007115caab7b475400e25000015ec24500386000057d890a0070cafa95eb241400e215f52bd6482801c457caaf2d1fd003894000058b091400e18b151616246801c42c4a586c915003885894b0d922a00711622ac2b489400e250000166c24d003862c9458d892a00710b2a963b249400e216552c76492801c4594ab1ed24d003894000059b093400e18000167624e801c32cea59ac93d0038859d4b35927a0071167aacdb49d400e25000016ac255003862d545a5895a00710b52969b255400e216a52d364aa801c45aaab4ed29d00389400005bb097400e1800016d625a801c32daa5b2c965003885b54b6592ca007116daad9b4b1400e250b8a16ec25d003882e145bd897a00710b8296fb25f400e217052df64be801c45c2ab7ed2f50038942ea85cb099400e20ba51736266801c42e8a5cac98d003885d14b95931a00711742ae5b4c7400e250000176c26d0038600005dd89aa0070cbba976b269400e217752ed64d2801c45dcabb2d34500389400005eb09b400e18bd5179626e801c42f4a5e6c9bd003885e94bcd937a007117a2af2b4dd400e25000017ec2750038600005f589da0070cbea97cb275400e217d52f964ea801c45f6abe2d3a500389430285fb09f400e20c0517f627a801c4302a5fec9ed003886054bfd93da00711812affb4f3400e250c2a182c28500388309460d8a0a00710c22983b281400e218453076502801c4610ac1ad3fd003894000061b0a1400e180001876286801c330ea61aca1d0038861d4c35943a0071187ab0db50b400e25000018ac28d0038631546258a3a00710c5a989b28d400e218b5313651a801c462cac4ed465003894000063b0a5400e18c7518d6292801c431ca636ca4d003886394c6d949a007118eab1bb525400e250000192c29d0038632546458a6a00710c92991b299400e219253236532801c464aac8ad4c5003894000065b0a9400e18cb5195629e801c432ca652ca7d003886594ca594fa00711962b29b53f400e25000019ac2a50038600006658a9a0070ccca998b2a7400e21995331654e801c4666acc6d52d003894000067b0ab400e1800019d62ae801c333aa672cab5003886754ce5956a007119dab38b559400e2500001a2c2b50038600006858ada0070cd0a9a0b2b5400e21a15341656a801c4686ad02d59d003894000069b0af400e180001a562ba801c334aa692caed003886954d2595da00711a5ab48b575400e2500001aac2c50038600006a58b0a0070cd4a9a8b2c3400e21a953516586801c46a6ad42d60d00389400006bb0b3400e180001ad62ca801c335aa6b2cb25003886b54d65964a00711adab58b591400e2500001b2c2d50038636546c58b4a00710d929b0b2d1400e21b2536165a2801c46c8ad82d68500389400006db0b7400e18db51b562da801c436ca6d2cb65003886d94da596ca00711b62b69b5b1400e2500001bac2e50038637546e58b8a00710dd29b9b2e1400e21ba537365c2801c46eaadcad6fd00389400006fb0bb400e18df51bd62ea801c437ea6f6cba5003886fd4ded974a00711bf2b7bb5cf400e2500001c2c2f500386000070d8bca0070ce1a9c2b2f1400e21c3538565e2801c470eae12d77d003894392871b0bf400e20e451c762fa801c4390a71acbe5003887214e3597ca00711c82b8db5f1400e250e6a1cac30500388399472d8c0a00710e6a9cbb301400e21cd53976602801c4734ae5ad805003894000074b0c3400e18e951d1630a801c43a4a742cc2d003887494e85985a00711d22ba0b613400e2500001d6c315003863ad47558c4a00710eba9d5b313400e21d753ab6626801c475caeaad8950038943ba876b0c7400e20ee51db631e801c43b8a76acc75003887714ed598ea00711dc2bb4b637400e250f0a1dec325003883c1477d8c9a00710f0a9dfb325400e21e153bf664a801c4784aefad925003894000079b0cb400e18f351e5632e801c43cca792ccbd003887994f25997a00711e6abc9b65d400e2500001eac33d003863d547a58cea00710f5a9e9b339400e21eb53d36672801c47aeaf4ed9c50038943e287bb0d1400e20f851ef6342801c43e2a7becd0d003887c54f7d9a1a00711f12bdeb685400e2500001f6c34d003863ed47d58d3a00710fba9f4b34d400e21f753e9669a801c47dcafa6da650038943fa87eb0d5400e20fe51fb6356801c43f8a7eacd5d003887f14fd59aba00711fcabf5b6ad400e250000202c3650038640548058d8a00711012a00b363400e2202540166c6801c480ab006db0d003894412881b0db400e21045207636e801c4410a81acdb50038882150359b6a0071208ac0db6d9400e25000020ec37d0038641d48358dea0071107aa0cb379400e220f541966f2801c483cb066dbbd00389442a884b0e1400e210a52136386801c442aa84ece1500388855509d9c2a00712152c25b707400e25000021ac3950038643548658e4a007110daa19b391400e221b54336722801c486eb0cadc7d003894000088b0e7400e19115221639e801c4444a882ce750038888951059cea0071222ac40b737400e25114a226c3ad00388451489d8eaa0071114aa26b3a9400e2229544d6752801c48a4b136dd4500389446288bb0ed400e2118522d63b6801c4460a8b6cedd003888c1516d9dba00712302c5bb76b400e250000236c3c50038646d48d58f0a007111baa34b3c3400e223754696786801c48deb1a6de1500389400008fb0f5400e191f523d63d2801c447ea8f2cf45003888fd51e59e8a007123f2c78b7a1400e25122a242c3dd0038848d490d8f7a00711232a43b3df400e2246548767be801c491ab21edef500389449a892b0fb400e2127524b63ee801c449ca92ecfb500388939525d9f6a007124e2c96b7d9400e2512aa252c3fd003884ad494d8ffa007112b2a53b3fd400e225654a767fa801c4958b29adfdd0038944ba896b103400e212f525b640e801c44bca96ed0350038897952dda06a007125eacb6b817400e25132a262c41d003884cd498d907a00711332a63b41b400e226654c76836801c499ab31ee0d500389400009bb10b400e1937526d642e801c44dea9b2d0b5003889bd5365a16a007126facd8b857400e2513ca276c43d003884f149d590fa007113c2a75b43d400e227854eb687a801c49e2b3aae1e500389450289fb113400e2140527f644e801c4502a9fad13d00388a0553f5a27a0071281acfcb89b400e25144a286c465003885154a1d918a0071145aa87b461400e228b550f68c2801c4a2cb43ae2fd00389452a8a4b11d400e214a52916472801c4528aa46d1cd00388a51548da39a0071294ad22b8e3400e2514ea29ac4850038853d4a6d921a007114f2a9ab487400e229e5535690e801c4a7ab4d6e42d0038945528a9b127400e215452a5649a801c4552aa96d26d00388aa5552da4da00712a92d4ab931400e25158a2aec4ad003885654abd92ba0071159aaafb4af400e22b3555f695e801c4aceb57ee56d00389457a8aeb131400e215f52bb64c6801c457caaead30d00388af955d5a61a00712bead75b985400e25164a2c6c4dd003885954b15936a00711652ac5b4d9400e22ca558b69b2801c4b28b62ee6c50038945aa8b4b13d400e216a52d164f2801c45aaab46d3c500388b55568da78a00712d5ada2b9df400e25170a2dec50d003885c14b75942a0071170aaddb509400e22e155bb6a12801c4b86b6eae83d0038945da8bab149400e217752e96522801c45dcaba6d48500388bb9574da90a00712ee2dd3ba3f400e2517ca2f6c53d003885f54bdd94ea007117daaf6b53b400e22fb55ed6a76801c4becb7b2e9cd0038946128c0b155400e218453036556801c4610ac0ed55500388c21581daaaa0071308ae07baa7400e2518aa312c5750038862d4c4595ca007118b2b11b571400e231656236ae2801c4c5ab88aeb7d00389464a8c7b163400e2192531f658e801c464aac7ed63500388c9558fdac6a00713252e3ebb19400e25198a32ec5ad003886654cbd96aa0071199ab2eb5ab400e2333565d6b56801c4000194aed550038746828cfb173400e21a1533d65ca801c4686acf6d72d00388d0d59edae5a00713193e30bb93400e250000346c5ed003860000d3597aa0070da9ab4db5eb400e2353569b6bd6801c4c26f842ef550038940000ccb183400e1800033b660e801c36c8ad76d83500388d915aedb06a00712fc3df56be9400e250000322c63500386655cca598ca00711baab6eb631400e237556dd6c62801c4bc0f771aedd0038940000c57189400e1800031ce636801c370eae02d95d00388e1d5c05b2ba00712e43dc56b85400e250000000060d003840000c3b986a0070dcd2b93b67d400e239a57276cfa801c4b66f6bdad65003894000000017d400e11817300c5fe801c475cae9ada9d00388eb95d35b53a00712cfbd9c6b31400e2500002f1c5dd003865edcbd3179a00711cf3b9db6d3400e23c257756da6801c4b1af625ac250038940000b96171400e180002eac5d2801c3712ee22dbfd003880001dfdb7fa0070ebdbd776ae5400e2500002d985ad003865c5cb8316ea00711bbbb7666eb400e23a977516e5e801c4ad4f59dab050038940000b46167400e196c72d6c5a6801c46cced959b2500388e55dca3393a00712ad3d576aa1400e2500002c9858d0038659dcb33165a00711abbb5566a9400e23837704ce06801c4a98f521aa0d0038940000b0615f400e196372c4c586801c4692ed1d9a3500388dc9db8b370a007129f3d3a6a65400e2500002b9856d0038657dcaf315ca007119e3b3a6671400e236376c4cd82801c4a60f4b1a9250038940000ac6157400e195b72b4c562801c465eecb9996500388d55daa3352a0071291bd1f6a2d400e2500002a9854d00386561cabb155a00711923b236641400e2348768ecd16801c4a2ef44da84d00389454b8a8614f400e215472a6c546801c4632ec6198ad00388cf1d9db338a0071285bd0769fb400e25000029d852d00386545ca8314ea0071187bb0e6617400e2330765eccb2801c49fef3eda78d0038945338a56149400e214e729ac52a801c460cec11980d00388c99d923322a007127a3cf069cb400e25000029185150038652dca53147a007117ebafb65f1400e231b7634cc5e801c49d4f399a6dd00389451b8a26143400e2148728ec512801c45e8ebcd977d00388c49d88b30da007126fbcdc69a1400e25000028584fd00386515ca23141a00711763aeb65cd400e23097610cc12801c49aaf349a63500389450389f613d400e21427282c4fe801c45c8eb8d96f500388c01d7fb2fba00712663cc86979400e2513ee27984ed00388501c9fb13ca007116ebadb65af400e22f875eecbce801c4986f2fda59500389400009d6137400e193d7278c4e6801c45aaeb51967d00388bc1d77b2eba007125d3cb66953400e25000027184d5003864edc9d3137a00711673acd6591400e22e875cecb8e801c4962f2b9a50500389400009b6133400e18000270c4d2801c3590eb1d961500388b85d7032dca0071254bca5692f400e25134e26584c5003884d9c9ab132a0071160bac06577400e22da75b2cb52801c4942f275a47d0038944cb898612f400e21347266c4c2801c4576eae995ad00388b4dd6932cea007124cbc95690f400e25130e25d84b5003884c9c98b12da007115abab4655f400e22cd7598cb1e801c4922f239a3fd0038944bb8966129400e2130725ec4ae801c4560eab9954d00388b1dd6332c1a0071244bc8668ef400e2512ce255849d00388000096b129a0070d553aa96547400e22c17580caee801c4904f1f9a37d0038944ab8946125400e212c7256c49e801c454aea9194f500388aedd5d32b5a007123dbc7868d1400e25128e24d848d003884a9c94b125a00711503a9f6533400e22b57568cabe801c48e8f1c5a30d00389449b8926123400e2128724ec48e801c4536ea65949d00388ac1d57b2a9a0071236bc6a68b3400e25124e245848500388499c92b121a007114b3a95651d400e22ab7554ca92801c48cef18da29d003894000091611f400e19247246c47e801c4522ea41945500388a99d52b29fa00712303c5d6899400e250000241847500386000091311ea0070d46ba8b650b400e22a17540ca6a801c48b4f15da23500389400008f611b400e19217240c472801c4510ea1d940500388a71d4db295a007122a3c50687f400e25000023984650038647dc8f311aa00711423a8364f9400e2297752cca42801c489cf12da1cd00389447388d6117400e2000023ac462801c3500e9f993c500388a4dd49328ca00712243c456867400e2511ae231845500388471c8db117a007113dba7a64e7400e228e751aca1e801c4884f0fda16d00389400008c6115400e191a7232c456801c44eee9d9937d00388a29d44b283a007121ebc39684f400e25000022d844d00386465c8c3114a0071139ba7264d7400e2286750ac9fa801c486ef0d1a10d00389445b88a6111400e2117722cc44a801c44e0e9b9933d00388a09d40b27aa00712193c2e6839400e250000229843d00386459c8ab111a00711363a6b64c7400e227e74fac9da801c4858f0a5a0b5003894000089610f400e18000228c43e801c34d0e99d9305003889e9d3cb272a0071213bc246823400e25

def row7 (index : ℕ) : List (List ℕ) :=
  if index < 130 then
    let packedCell := Nat.shiftRight row7PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row8PackedData : ℕ := 0x51b085400e180001456216801c328aa512c85d003885154a2590ba0071145aa89b42f400e250000146c21d00386000051d887a0070c000147b21b400e1800028f6436801c351eaa3ad0dd003894000052b089400e18a551496222801c4294a526c885003885294a4d910a007114a2a92b43f400e250a6a14ac22500388299452d889a00710a6294bb225400e214c5297644a801c4532aa5ed125003894000053b08b400e1800014f622a801c329ea53ac8a50038853d4a75914a007114f2a9cb451400e250000152c22d00386000054588ba0070c000151b22d400e180002a3645a801c3546aa8ad1650038942aa854b08d400e20aa51536232801c42a8a54ec8c5003885514a9d918a0071154aaa7b463400e250000156c23500386000055d88da0070caba956b237400e215752ad646e801c455caab2d1b5003894000056b08f400e18000159623a801c32b2a562c8ed003885654ac591da0071159aab1b475400e250aea15ac245003882b9456d890a00710ae295bb241400e215c52b76482801c4572aaded1fd003894000057b091400e1800015f6246801c32bea57ac9150038857d4af5922a007115f2abcb489400e250000162c24d003862c54585892a00710b12961b249400e216252c36492801c4588ab0ad24d003894000059b093400e18b25163624e801c42caa58ec93d003885954b1d927a00711652ac7b49d400e250000166c25500386000059d895a0070cb3a966b255400e216752cd64aa801c459eab36d29d00389400005ab097400e18b55169625a801c42d4a5a6c965003885a94b4d92ca007116aaad3b4b1400e25000016ec25d0038600005b5897a0070cb6a96cb25f400e216d52d964be801c45b6ab66d2f50038942e285bb099400e20b8516f6266801c42e0a5bec98d003885c14b7d931a0071170aadfb4c7400e250baa172c26d003882e945cd89aa00710ba2972b269400e217452e564d2801c45d0ab96d34500389400005db09b400e18000177626e801c32eea5dac9bd003885dd4bb5937a00711772aecb4dd400e25000017ac275003862f545e589da00710bd2979b275400e217a52f364ea801c45e8abcad3a500389400005fb09f400e1800017d627a801c32faa5f2c9ed003885f54be593da007117daaf8b4f3400e250c0a17ec2850038830145fd8a0a00710c0a97fb281400e218152ff6502801c4604abfed3fd00389430a860b0a1400e20c251836286801c4308a60eca1d003886114c1d943a00711842b06b50b400e250000186c28d00386000061d8a3a0070cc3a986b28d400e2187530d651a801c461eac36d465003894000062b0a5400e18c551896292801c4316a626ca4d0038862d4c4d949a007118b2b13b525400e25000018ec29d0038631d46358a6a00710c7298db299400e218e531b6532801c463aac6ed4c5003894000064b0a9400e18c95191629e801c4324a646ca7d003886494c8d94fa0071192ab22b53f400e250000196c2a50038632d46558a9a00710cb2994b2a7400e21965329654e801c4658aca6d52d003894000066b0ab400e1800019962ae801c3332a662cab5003886654cc5956a0071199ab31b559400e25000019ec2b50038600006758ada0070ccea99cb2b5400e219d5339656a801c4676ace2d59d003894000068b0af400e180001a162ba801c3342a682caed003886854d0595da00711a1ab40b575400e2500001a6c2c50038600006958b0a0070cd2a9a4b2c3400e21a553496586801c4696ad22d60d00389400006ab0b3400e180001a962ca801c3352a6a2cb25003886a54d45964a00711a9ab50b591400e2500001aec2d50038600006b58b4a0070cd6a9acb2d1400e21ad535965a2801c46b6ad62d68500389400006cb0b7400e18d951b162da801c4364a6c2cb65003886c94d8596ca00711b22b60b5b1400e2500001b6c2e50038636d46d58b8a00710db29b4b2e1400e21b6536965c2801c46d8ada6d6fd00389400006eb0bb400e18dd51b962ea801c4374a6e6cba5003886e94dcd974a00711baab72b5cf400e2500001bec2f50038637d46f58bca00710dfa9bdb2f1400e21bf537b65e2801c46fcadeed77d003894000070b0bf400e180001c362fa801c3386a70acbe50038870d4e1597ca00711c3ab84b5f1400e250e4a1c6c30500388391471d8c0a00710e429c6b301400e21c8538d6602801c4720ae36d80500389439a872b0c3400e20e651cb630a801c439aa72ecc2d003887354e5d985a00711cd2b96b613400e2500001d2c315003863a547458c4a00710e929d0b313400e21d253a16626801c4748ae82d895003894000075b0c7400e18eb51d5631e801c43aea756cc750038875d4ead98ea00711d72baab637400e250eea1dac325003883b9476d8c9a00710ee29dab325400e21dc53b5664a801c4770aed2d9250038943c2877b0cb400e20f051df632e801c43c2a77eccbd003887854efd997a00711e12bbeb65d400e2500001e6c33d003863cd47958cea00710f329e4b339400e21e653c96672801c479aaf26d9c500389400007ab0d1400e18f551e96342801c43d6a7a6cd0d003887ad4f4d9a1a00711ebabd3b685400e250f8a1eec34d003883e147bd8d3a00710f8a9efb34d400e21f153df669a801c47c4af7ada6500389400007db0d5400e18fb51f56356801c43eea7d2cd5d003887dd4fa59aba00711f72be9b6ad400e250fea1fac365003883f947ed8d8a00710fe29fab363400e21fc53f566c6801c47f2afd6db0d003894000080b0db400e19015201636e801c4404a802cdb50038880950059b6a0071202ac01b6d9400e25104a206c37d00388411481d8dea00711042a06b379400e2208540d66f2801c4822b036dbbd003894000083b0e1400e1907520d6386801c441ea832ce150038883d50659c2a007120f2c19b707400e2510aa212c39500388429484d8e4a007110aaa13b391400e221554276722801c4854b096dc7d003894000086b0e7400e190d5219639e801c4436a866ce750038886d50cd9cea007121bac32b737400e250000222c3ad0038644548858eaa00711112a20b3a9400e222254416752801c488ab102dd45003894452889b0ed400e2114522763b6801c4452a89acedd003888a551359dba00712292c4db76b400e25118a22ec3c50038846148b58f0a00711182a2db3c3400e2230545b6786801c48c0b16ede1500389400008db0f5400e191b523563d2801c446ea8d2cf45003888dd51a59e8a0071237ac69b7a1400e25000023ec3dd0038647d48f58f7a007111faa3cb3df400e223f547967be801c48fcb1e2def500389448a890b0fb400e2123524363ee801c448ca90ecfb500388919521d9f6a0071246ac87b7d9400e25126a24ac3fd0038849d492d8ffa00711272a4bb3fd400e224e549767fa801c4938b25adfdd0038944aa894b103400e212b5253640e801c44aca94ed03500388959529da06a00712562ca6b817400e2512ea25ac41d003884bd496d907a007112f2a5bb41b400e225e54b76836801c497ab2dae0d50038944ca898b10b400e21335263642e801c44cca98ed0b500388999531da16a0071266acc7b857400e25000026ec43d003864dd49b590fa0071137aa6cb43d400e226f54d9687a801c49beb362e1e50038944f289db113400e213c5275644e801c44f0a9d6d13d003889e153ada27a0071278aceab89b400e25140a27ec4650038850149fd918a0071140aa7eb461400e228154fd68c2801c4a06b3f2e2fd0038945128a1b11d400e214552876472801c4516aa1ed1cd00388a2d543da39a007128b2d0eb8e3400e2514aa292c485003885294a45921a007114a2a91b487400e22945523690e801c4a52b48ae42d00389453a8a6b127400e214f529b649a801c453caa6ad26d00388a7954d5a4da007129ead35b931400e25154a2a6c4ad003885514a9592ba0071154aaa5b4af400e22a9554b695e801c4aa4b52ae56d0038945628abb131400e215952af64c6801c4566aabed30d00388acd557da61a00712b3ad5fb985400e2515ea2bac4dd0038857d4aed936a007115f2abab4d9400e22be557569b2801c4afab5d6e6c50038945928b1b13d400e216552c564f2801c4594ab16d3c500388b29562da78a00712ca2d8bb9df400e2516aa2d2c50d003885a94b45942a007116aaad1b509400e22d555a36a12801c4b56b68ae83d0038945c28b7b149400e217052dd6522801c45c2ab76d48500388b8556eda90a00712e1adbaba3f400e25176a2eac53d003885dd4ba594ea00711772ae9b53b400e22ee55d36a76801c4bb8b74ee9cd0038945f28bdb155400e217d52f76556801c45f6abdad55500388bed57b5aaaa00712fb2decbaa7400e25184a302c575003886114c0d95ca00711842b03b571400e230856076ae2801c4c22b81eeb7d00389462a8c4b163400e218b5311658e801c462cac46d63500388c59588dac6a0071316ae22bb19400e25192a31ec5ad003886494c7d96aa0071192ab1fb5ab400e2325563f6b56801c4c94b8faed550038946628cbb173400e2199532f65ca801c4666acbad72d00388ccd5975ae5a0071333ae5cbb93400e251a0a33ec5ed003886854cf597aa00711a1ab3db5eb400e2343567b6bd6801c4d00b9eaef550038946a28d3b183400e21a9534d660e801c46a6ad36d83500388d4d5a6db06a007132ebe5cbc19400e25000035ec635003866c94d7598ca00711b22b5db631400e236456bb6c62801c4c7cf8eef17d0038940000d2b195400e19aa73536656801c46eaadbad95d00388dd55b75b2ba0071310be1e6c3b400e2500000000675003840000d0d99fa0070dc3ab80b67d400e238757016cfa801c4c0ef811b0150038940000000195400e10000332c662801c3734ae4eda9d00388e695c9db53a00712f73deb6bd1400e25000031d8635003860000c93991a0070dd72ba6b6d3400e23ae574d6da6801c4bb0f755ae8d0038940000c47187400e18000316c62a801c3784aeeadbfd00388f095dd5b7fa00712e1bdc06b77400e250000305c605003860000c2b184a0070c0003c2b72f400e1bd7579f6e5e801c4b60f6b5ad3d0038940000be617b400e198072fec5fa801c400000001d5d00384f9d5f2dbb1a00712cebd9a6b29400e2500002ed85d5003860000bd3178a0070c000397672d400e1bcf779d6f2e801c4b18f621ac0d0038940000b96171400e180002eac5ce801c370aee119c1d003880001dcbbb8a0070ebdbd786ae1400e2516ee2d985ad003885c5cb8316ea00711babb7466e5400e23a57748ce8e801c4ad6f5a1ab050038940000b46167400e180002d8c5aa801c36caed919b1d00388e4ddc93391a00712ae3d596aa1400e2500002c9858d003865a1cb3b165a00711abbb5666a9400e20000704ce02801c3a9cf52daa150038940000b0615f400e196472c6c586801c4694ed259a3d00388dcddb93370a00712a0bd3d6a67400e2515ee2b9856d00388581cafb15da007119f3b3d6675400e236576c8cd8a801c4a66f4c1a93500389456b8ac6157400e200002b8c566801c3664ecc5997500388d61dabb354a0071293bd246a33400e2500002ad854d00386565cac3156a0071193bb266647400e20000696cd22801c3a36f461a8650038940000a96151400e195672aac54a801c463aec7198c500388d01d9fb33ca0071287bd0c6a01400e25150e29d8535003880000a9314fa0070d89bb12661d400e23357668ccc2801c4a08f405a7ad0038940000a6614b400e1800029ec532801c3614ec25982d003880001953326a0070e7d3cf669d5400e250000295851d003860000a63149a0070d80bb0065f9400e23217640cc72801c49def3b1a6fd0038940000a36145400e194a7292c51a801c45f2ebe1979d0038800018bb312a0070e72bce269ab400e25000028985050038651dca33143a0071178baf065d7400e2000061ccc26801c39b8f365a65d00389450b8a0613f400e21447286c502801c45d2eba1971d00388c19d82b301a00712693ccf6983400e25140e27d84f500388509ca0b13da00711713ae165b9400e22fe75facbe2801c4992f319a5bd00389400009e6139400e193f727cc4ee801c45b6eb6996ad00388bd9d7ab2f0a0071260bcbd695f400e25000027584dd003864f5c9e3138a007116a3ad3659d400e22ef75dccba6801c4970f2d5a52d00389400009c6135400e18000274c4da801c359ceb35963d00388ba1d73b2e1a00712583cac693b400e25136e26984cd003884e1c9bb134a0071163bac66581400e22e175c0cb6a801c4950f291a4ad0038944d38996131400e2136726ac4c6801c4582eb0195d500388b69d6cb2d4a00712503c9c6919400e25132e26184b5003884d1c99b12fa007115dbaba6569400e22d475a6cb36801c4930f255a4250038944c3897612b400e21327262c4b6801c456cead5957d00388000166b2c7a0070e48bc8e68fb400e2512ee25984a5003884c1c97b12ba00711583aaf6553400e22c8758ecb06801c4912f219a3ad0038944b38956127400e212e725ac4a6801c4556eaa9951d00388b09d60b2bba00712413c7f68dd400e2512ae2518495003884b1c95b127a00711533aa5653d400e22bc7576cad6801c48f6f1e1a33d0038944a38936123400e212a7252c496801c4542ea8194cd00388addd5b32b0a007123abc7168c1400e25000024d848d003864a1c93b123a007114e3a9b6529400e22b27562caaa801c48dcf1ada2cd0038940000926121400e1800024cc486801c352eea59947d00388ab5d5632a5a00712343c6568a7400e250000245847d00386495c923120a0071149ba926517400e22a8754eca82801c48c4f179a265003894000090611d400e19237244c47a801c451cea35943500388a8dd51329ba007122dbc58688d400e25120e23d846d00388485c90311ca00711453a896505400e229e753aca5a801c48aaf149a1fd00389447b88e6119400e2120723ec46a801c450cea1593ed00388a69d4cb292a00712283c4c6873400e250000239845d00386479c8eb119a0071140ba8064f3400e22957528ca36801c4894f11da19d00389400008d6117400e18000238c45e801c34fce9f193ad00388a45d483289a00712223c41685d400e25

def row8 (index : ℕ) : List (List ℕ) :=
  if index < 129 then
    let packedCell := Nat.shiftRight row8PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row9PackedData : ℕ := 0x146c21d003860000515887a0070ca2a944b21b400e214552896436801c4516aa26d0dd003894000051b089400e180001476222801c3000051ec885003860000a3d910a0070d47aa8eb43f400e25000014ac225003862954525889a00710a52949b225400e214a5293644a801c4528aa4ad12500389429a852b08b400e20a6514b622a801c4298a52ec8a5003885314a5d914a007114caa97b451400e25000014ec22d00386000053d88ba0070ca7a94eb22d400e214f529d645a801c453caa72d165003894000054b08d400e180001516232801c30000546c8c5003860000a8d918a0070d51aaa2b463400e250aaa152c235003882a9454d88da00710aa2953b237400e215452a7646e801c4552aa9ed1b5003894000055b08f400e18000157623a801c32aea55ac8ed0038855d4ab591da00711572aacb475400e25000015ac245003860000565890a0070caca958b241400e215952b16482801c4566aac6d1fd0038942ba856b091400e20ae515b6246801c42b8a56ec915003885714add922a007115caab7b489400e25000015ec24d00386000057d892a0070cafa95eb249400e215f52bd6492801c457caaf2d24d003894000058b093400e18b15161624e801c42c4a586c93d003885894b0d927a00711622ac2b49d400e250000166c255003862c9458d895a00710b2a963b255400e216552c764aa801c4594ab1ed29d003894000059b097400e18000167625a801c32cea59ac9650038859d4b3592ca0071167aacdb4b1400e25000016ac25d003862d545a5897a00710b52969b25f400e216a52d364be801c45aaab4ed2f500389400005bb099400e1800016d6266801c32daa5b2c98d003885b54b65931a007116daad9b4c7400e250b8a16ec26d003882e145bd89aa00710b8296fb269400e217052df64d2801c45c2ab7ed3450038942ea85cb09b400e20ba5173626e801c42e8a5cac9bd003885d14b95937a00711742ae5b4dd400e250000176c2750038600005dd89da0070cbba976b275400e217752ed64ea801c45dcabb2d3a500389400005eb09f400e18bd5179627a801c42f4a5e6c9ed003885e94bcd93da007117a2af2b4f3400e25000017ec2850038600005f58a0a0070cbea97cb281400e217d52f96502801c45f6abe2d3fd00389430285fb0a1400e20c0517f6286801c4302a5feca1d003886054bfd943a00711812affb50b400e250c2a182c28d00388309460d8a3a00710c22983b28d400e21845307651a801c4610ac1ad465003894000061b0a5400e180001876292801c330ea61aca4d0038861d4c35949a0071187ab0db525400e25000018ac29d0038631546258a6a00710c5a989b299400e218b53136532801c462cac4ed4c5003894000063b0a9400e18c7518d629e801c431ca636ca7d003886394c6d94fa007118eab1bb53f400e250000192c2a50038632546458a9a00710c92991b2a7400e21925323654e801c464aac8ad52d003894000065b0ab400e18cb519562ae801c432ca652cab5003886594ca5956a00711962b29b559400e25000019ac2b50038600006658ada0070ccca998b2b5400e21995331656a801c4666acc6d59d003894000067b0af400e1800019d62ba801c333aa672caed003886754ce595da007119dab38b575400e2500001a2c2c50038600006858b0a0070cd0a9a0b2c3400e21a153416586801c4686ad02d60d003894000069b0b3400e180001a562ca801c334aa692cb25003886954d25964a00711a5ab48b591400e2500001aac2d50038600006a58b4a0070cd4a9a8b2d1400e21a9535165a2801c46a6ad42d68500389400006bb0b7400e180001ad62da801c335aa6b2cb65003886b54d6596ca00711adab58b5b1400e2500001b2c2e50038636546c58b8a00710d929b0b2e1400e21b2536165c2801c46c8ad82d6fd00389400006db0bb400e18db51b562ea801c436ca6d2cba5003886d94da5974a00711b62b69b5cf400e2500001bac2f50038637546e58bca00710dd29b9b2f1400e21ba537365e2801c46eaadcad77d00389400006fb0bf400e18df51bd62fa801c437ea6f6cbe5003886fd4ded97ca00711bf2b7bb5f1400e2500001c2c30500386000070d8c0a0070ce1a9c2b301400e21c353856602801c470eae12d805003894392871b0c3400e20e451c7630a801c4390a71acc2d003887214e35985a00711c82b8db613400e250e6a1cac31500388399472d8c4a00710e6a9cbb313400e21cd53976626801c4734ae5ad895003894000074b0c7400e18e951d1631e801c43a4a742cc75003887494e8598ea00711d22ba0b637400e2500001d6c325003863ad47558c9a00710eba9d5b325400e21d753ab664a801c475caeaad9250038943ba876b0cb400e20ee51db632e801c43b8a76accbd003887714ed5997a00711dc2bb4b65d400e250f0a1dec33d003883c1477d8cea00710f0a9dfb339400e21e153bf6672801c4784aefad9c5003894000079b0d1400e18f351e56342801c43cca792cd0d003887994f259a1a00711e6abc9b685400e2500001eac34d003863d547a58d3a00710f5a9e9b34d400e21eb53d3669a801c47aeaf4eda650038943e287bb0d5400e20f851ef6356801c43e2a7becd5d003887c54f7d9aba00711f12bdeb6ad400e2500001f6c365003863ed47d58d8a00710fba9f4b363400e21f753e966c6801c47dcafa6db0d0038943fa87eb0db400e20fe51fb636e801c43f8a7eacdb5003887f14fd59b6a00711fcabf5b6d9400e250000202c37d0038640548058dea00711012a00b379400e2202540166f2801c480ab006dbbd003894412881b0e1400e210452076386801c4410a81ace150038882150359c2a0071208ac0db707400e25000020ec3950038641d48358e4a0071107aa0cb391400e220f54196722801c483cb066dc7d00389442a884b0e7400e210a5213639e801c442aa84ece7500388855509d9cea00712152c25b737400e25000021ac3ad0038643548658eaa007110daa19b3a9400e221b54336752801c486eb0cadd45003894000088b0ed400e1911522163b6801c4444a882cedd0038888951059dba0071222ac40b76b400e25114a226c3c500388451489d8f0a0071114aa26b3c3400e2229544d6786801c48a4b136de1500389446288bb0f5400e2118522d63d2801c4460a8b6cf45003888c1516d9e8a00712302c5bb7a1400e250000236c3dd0038646d48d58f7a007111baa34b3df400e2237546967be801c48deb1a6def500389400008fb0fb400e191f523d63ee801c447ea8f2cfb5003888fd51e59f6a007123f2c78b7d9400e25122a242c3fd0038848d490d8ffa00711232a43b3fd400e2246548767fa801c491ab21edfdd00389449a892b103400e2127524b640e801c449ca92ed03500388939525da06a007124e2c96b817400e2512aa252c41d003884ad494d907a007112b2a53b41b400e225654a76836801c4958b29ae0d50038944ba896b10b400e212f525b642e801c44bca96ed0b50038897952dda16a007125eacb6b857400e25132a262c43d003884cd498d90fa00711332a63b43d400e226654c7687a801c499ab31ee1e500389400009bb113400e1937526d644e801c44dea9b2d13d003889bd5365a27a007126facd8b89b400e2513ca276c465003884f149d5918a007113c2a75b461400e227854eb68c2801c49e2b3aae2fd00389450289fb11d400e2140527f6472801c4502a9fad1cd00388a0553f5a39a0071281acfcb8e3400e25144a286c485003885154a1d921a0071145aa87b487400e228b550f690e801c4a2cb43ae42d00389452a8a4b127400e214a5291649a801c4528aa46d26d00388a51548da4da0071294ad22b931400e2514ea29ac4ad0038853d4a6d92ba007114f2a9ab4af400e229e5535695e801c4a7ab4d6e56d0038945528a9b131400e215452a564c6801c4552aa96d30d00388aa5552da61a00712a92d4ab985400e25158a2aec4dd003885654abd936a0071159aaafb4d9400e22b3555f69b2801c4aceb57ee6c500389457a8aeb13d400e215f52bb64f2801c457caaead3c500388af955d5a78a00712bead75b9df400e25164a2c6c50d003885954b15942a00711652ac5b509400e22ca558b6a12801c4b28b62ee83d0038945aa8b4b149400e216a52d16522801c45aaab46d48500388b55568da90a00712d5ada2ba3f400e25170a2dec53d003885c14b7594ea0071170aaddb53b400e22e155bb6a76801c4b86b6eae9cd0038945da8bab155400e217752e96556801c45dcaba6d55500388bb9574daaaa00712ee2dd3baa7400e2517ca2f6c575003885f54bdd95ca007117daaf6b571400e22fb55ed6ae2801c4becb7b2eb7d0038946128c0b163400e21845303658e801c4610ac0ed63500388c21581dac6a0071308ae07bb19400e2518aa312c5ad0038862d4c4596aa007118b2b11b5ab400e231656236b56801c4c5ab88aed5500389464a8c7b173400e2192531f65ca801c464aac7ed72d00388c9558fdae5a00713252e3ebb93400e25198a32ec5ed003886654cbd97aa0071199ab2eb5eb400e2333565d6bd6801c4cceb972ef550038946828cfb183400e21a1533d660e801c4686acf6d83500388d0d59edb06a00713432e7abc19400e251a8a34ec635003886a54d3598ca00711a9ab4db631400e2353569b6c62801c4d4cba6af17d0038946ca8d7b195400e21b2535d6656801c46c8ad76d95d00388d915aedb2ba007134a3e93bcab400e251baa36ec67d003886e94dbd99fa00711baab6eb67d400e237556dd6cfa801c4ce4f9c1b37d0038940000dab1a9400e1800037566a6801c370eae02da9d00388e1d5c05b53a0071329be516c9f400e250000359c6ad0038600000001b0a00709cd2b93b6d3400e239a57276da6801c4c6ef8d5b19500389400000001a3400e10000350e69e801c375cae9adbfd00388eb95d35b7fa007130ebe1b6c2f400e250000339c66d003860000d0319fa0070de12bbab72f400e23c257756e5e801c4c0af80daff50038940000ca6193400e18000332e662801c37aeaf3edd8d00388f5d5e7dbb1a00712f73dec6bcf400e25000031d8635003860000c93191a0070df72be5b797400e23ee57cb6f2e801c4bb4f75dae8d0038940000c46187400e18000318c62a801c300000001ec5003850155fe5be8a00712e33dc36b79400e2500003058605003860000c33184a0070c0003c26783400e180000001006801c2b66f6c1ad4d0038945fb8be617b400e21817300c5fe801c475ceeb59d65003880001f4bbe8a0070ed0bd9f6b2d400e2500002f185dd003865f1cbdb179a0071000039b6733400e180007a4cf46801c3b20f639ac2d0038945d38b96171400e217772ecc5d2801c4714ee259c3d003880001df33bca0070ec0bd7e6ae9400e25170e2dd85b5003885cdcb93170a0071000037a66ef400e1bac7756cea6801c4ae2f5bdab250038940000b56169400e180002dcc5ae801c36d8edad9b45003880001cd3397a0070eb1bd616aad400e2500002cd8595003860000b53167a0070c00035e66b5400e1b8b7714ce1e801c4aaaf549aa3d0038945938b16161400e200002ccc58e801c30000d459a6d00386df1dbdb378a00712a43d456a75400e25160e2bd8575003880000b1315fa0070c0003456683400e1b6e76dacdaa801c4a76f4e5a9650038940000ae6159400e195f72bcc56e801c4674ece599ad00388d85db0335da0071297bd2c6a3f400e2500002b18555003860000adb158a0070c00032f6655400e1b5576a8cd42801c4a46f485a8a500389455b8aa6153400e200002b0c552801c30000c959905003860001a4b345a0070e8c3d156a0f400e2500002a5853d00386555caa3151a007118e3b1b662d400e2000067ccce6801c3a1af429a7e50038945438a7614d400e215272a2c53a801c4626ec49986d0038800019a332fa0070e813d0069e3400e25000029985250038653dca7314ba00711853b096609400e20000654cc96801c39f0f3d9a73d00389452b8a46147400e20000298c522801c3604ec0597dd00388c85d90331ba00712773ceb69b9400e25000028d850d00386529ca4b145a007117d3af965e7400e20000630cc4e801c39caf389a6950038940000a26141400e1947728cc50e801c45e4ebc5975d00388c41d87b30aa007126dbcd96993400e25000028584fd003860000a23140a0070d75baea65c9400e2308760ecc06801c49a6f341a60500389450389f613b400e21427282c4f6801c40000b8d96ed00386c01d7fb2f9a00712653cc7696f400e25000027984e50038600009fb13ba0070d6ebadc65ad400e200005f0cbca801c3982f2fda57500389400009d6137400e193d7278c4e2801c45aceb55967d00388bc5d7832eaa007125cbcb6694b400e25000027184d5003864edc9d3136a00711683acf6591400e200005d4cb8e801c3962f2b9a4ed00389400009b6133400e19397270c4d2801c4594eb25961500388b91d71b2dda0071254bca6692b400e25000026984c50038600009b3132a0070d623ac36579400e22dd75b8cb5a801c4944f27da46d003894000099612f400e18000268c4c2801c357ceaf595b500388b5dd6b32d0a007124d3c97690b400e25000026184b500386000099312da0070d5cbab86563400e22d175a0cb2a801c4926f241a3f5003894000097612b400e18000260c4ae801c3566eac9955d00388b2dd6532c4a00712463c8968ed400e25000025984a5003860000973129a0070d573aad654d400e22c6758acafa801c490af209a37d0038940000956127400e192d7258c4a2801c4552eaa1950d00388b01d5fb2b8a007123f3c7b68d1400e2500002518495003864adc953126a00711523aa36539400e22bb7574cace801c48f0f1d5a30d0038940000936123400e19297250c492801c453eea7994bd0038800015ab2aea0070e38bc6e68b7400e25126e249848500388000093b122a0070d4dba9a6525400e20000560caa2801c38d6f1a1a2a5003894493891611f400e2126724ac482801c452cea55946d00388ab1d55b2a3a0071232bc62689d400e25

def row9 (index : ℕ) : List (List ℕ) :=
  if index < 128 then
    let packedCell := Nat.shiftRight row9PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row10PackedData : ℕ := 0x51b089400e180001456222801c328aa512c885003885154a25910a0071145aa89b43f400e250000146c22500386000051d889a0070c000147b225400e1800028f644a801c351eaa3ad125003894000052b08b400e18a55149622a801c4294a526c8a5003885294a4d914a007114a2a92b451400e250a6a14ac22d00388299452d88ba00710a6294bb22d400e214c5297645a801c4532aa5ed165003894000053b08d400e1800014f6232801c329ea53ac8c50038853d4a75918a007114f2a9cb463400e250000152c23500386000054588da0070c000151b237400e180002a3646e801c3546aa8ad1b50038942aa854b08f400e20aa5153623a801c42a8a54ec8ed003885514a9d91da0071154aaa7b475400e250000156c24500386000055d890a0070caba956b241400e215752ad6482801c455caab2d1fd003894000056b091400e180001596246801c32b2a562c915003885654ac5922a0071159aab1b489400e250aea15ac24d003882b9456d892a00710ae295bb249400e215c52b76492801c4572aaded24d003894000057b093400e1800015f624e801c32bea57ac93d0038857d4af5927a007115f2abcb49d400e250000162c255003862c54585895a00710b12961b255400e216252c364aa801c4588ab0ad29d003894000059b097400e18b25163625a801c42caa58ec965003885954b1d92ca00711652ac7b4b1400e250000166c25d00386000059d897a0070cb3a966b25f400e216752cd64be801c459eab36d2f500389400005ab099400e18b551696266801c42d4a5a6c98d003885a94b4d931a007116aaad3b4c7400e25000016ec26d0038600005b589aa0070cb6a96cb269400e216d52d964d2801c45b6ab66d3450038942e285bb09b400e20b8516f626e801c42e0a5bec9bd003885c14b7d937a0071170aadfb4dd400e250baa172c275003882e945cd89da00710ba2972b275400e217452e564ea801c45d0ab96d3a500389400005db09f400e18000177627a801c32eea5dac9ed003885dd4bb593da00711772aecb4f3400e25000017ac285003862f545e58a0a00710bd2979b281400e217a52f36502801c45e8abcad3fd00389400005fb0a1400e1800017d6286801c32faa5f2ca1d003885f54be5943a007117daaf8b50b400e250c0a17ec28d0038830145fd8a3a00710c0a97fb28d400e218152ff651a801c4604abfed46500389430a860b0a5400e20c251836292801c4308a60eca4d003886114c1d949a00711842b06b525400e250000186c29d00386000061d8a6a0070cc3a986b299400e2187530d6532801c461eac36d4c5003894000062b0a9400e18c55189629e801c4316a626ca7d0038862d4c4d94fa007118b2b13b53f400e25000018ec2a50038631d46358a9a00710c7298db2a7400e218e531b654e801c463aac6ed52d003894000064b0ab400e18c9519162ae801c4324a646cab5003886494c8d956a0071192ab22b559400e250000196c2b50038632d46558ada00710cb2994b2b5400e21965329656a801c4658aca6d59d003894000066b0af400e1800019962ba801c3332a662caed003886654cc595da0071199ab31b575400e25000019ec2c50038600006758b0a0070ccea99cb2c3400e219d53396586801c4676ace2d60d003894000068b0b3400e180001a162ca801c3342a682cb25003886854d05964a00711a1ab40b591400e2500001a6c2d50038600006958b4a0070cd2a9a4b2d1400e21a5534965a2801c4696ad22d68500389400006ab0b7400e180001a962da801c3352a6a2cb65003886a54d4596ca00711a9ab50b5b1400e2500001aec2e50038600006b58b8a0070cd6a9acb2e1400e21ad535965c2801c46b6ad62d6fd00389400006cb0bb400e18d951b162ea801c4364a6c2cba5003886c94d85974a00711b22b60b5cf400e2500001b6c2f50038636d46d58bca00710db29b4b2f1400e21b6536965e2801c46d8ada6d77d00389400006eb0bf400e18dd51b962fa801c4374a6e6cbe5003886e94dcd97ca00711baab72b5f1400e2500001bec3050038637d46f58c0a00710dfa9bdb301400e21bf537b6602801c46fcadeed805003894000070b0c3400e180001c3630a801c3386a70acc2d0038870d4e15985a00711c3ab84b613400e250e4a1c6c31500388391471d8c4a00710e429c6b313400e21c8538d6626801c4720ae36d89500389439a872b0c7400e20e651cb631e801c439aa72ecc75003887354e5d98ea00711cd2b96b637400e2500001d2c325003863a547458c9a00710e929d0b325400e21d253a1664a801c4748ae82d925003894000075b0cb400e18eb51d5632e801c43aea756ccbd0038875d4ead997a00711d72baab65d400e250eea1dac33d003883b9476d8cea00710ee29dab339400e21dc53b56672801c4770aed2d9c50038943c2877b0d1400e20f051df6342801c43c2a77ecd0d003887854efd9a1a00711e12bbeb685400e2500001e6c34d003863cd47958d3a00710f329e4b34d400e21e653c9669a801c479aaf26da6500389400007ab0d5400e18f551e96356801c43d6a7a6cd5d003887ad4f4d9aba00711ebabd3b6ad400e250f8a1eec365003883e147bd8d8a00710f8a9efb363400e21f153df66c6801c47c4af7adb0d00389400007db0db400e18fb51f5636e801c43eea7d2cdb5003887dd4fa59b6a00711f72be9b6d9400e250fea1fac37d003883f947ed8dea00710fe29fab379400e21fc53f566f2801c47f2afd6dbbd003894000080b0e1400e190152016386801c4404a802ce150038880950059c2a0071202ac01b707400e25104a206c39500388411481d8e4a00711042a06b391400e2208540d6722801c4822b036dc7d003894000083b0e7400e1907520d639e801c441ea832ce750038883d50659cea007120f2c19b737400e2510aa212c3ad00388429484d8eaa007110aaa13b3a9400e221554276752801c4854b096dd45003894000086b0ed400e190d521963b6801c4436a866cedd0038886d50cd9dba007121bac32b76b400e250000222c3c50038644548858f0a00711112a20b3c3400e222254416786801c488ab102de15003894452889b0f5400e2114522763d2801c4452a89acf45003888a551359e8a00712292c4db7a1400e25118a22ec3dd0038846148b58f7a00711182a2db3df400e2230545b67be801c48c0b16edef500389400008db0fb400e191b523563ee801c446ea8d2cfb5003888dd51a59f6a0071237ac69b7d9400e25000023ec3fd0038647d48f58ffa007111faa3cb3fd400e223f547967fa801c48fcb1e2dfdd00389448a890b103400e21235243640e801c448ca90ed03500388919521da06a0071246ac87b817400e25126a24ac41d0038849d492d907a00711272a4bb41b400e224e54976836801c4938b25ae0d50038944aa894b10b400e212b5253642e801c44aca94ed0b500388959529da16a00712562ca6b857400e2512ea25ac43d003884bd496d90fa007112f2a5bb43d400e225e54b7687a801c497ab2dae1e50038944ca898b113400e21335263644e801c44cca98ed13d00388999531da27a0071266acc7b89b400e25000026ec465003864dd49b5918a0071137aa6cb461400e226f54d968c2801c49beb362e2fd0038944f289db11d400e213c52756472801c44f0a9d6d1cd003889e153ada39a0071278aceab8e3400e25140a27ec4850038850149fd921a0071140aa7eb487400e228154fd690e801c4a06b3f2e42d0038945128a1b127400e21455287649a801c4516aa1ed26d00388a2d543da4da007128b2d0eb931400e2514aa292c4ad003885294a4592ba007114a2a91b4af400e22945523695e801c4a52b48ae56d00389453a8a6b131400e214f529b64c6801c453caa6ad30d00388a7954d5a61a007129ead35b985400e25154a2a6c4dd003885514a95936a0071154aaa5b4d9400e22a9554b69b2801c4aa4b52ae6c50038945628abb13d400e215952af64f2801c4566aabed3c500388acd557da78a00712b3ad5fb9df400e2515ea2bac50d0038857d4aed942a007115f2abab509400e22be55756a12801c4afab5d6e83d0038945928b1b149400e216552c56522801c4594ab16d48500388b29562da90a00712ca2d8bba3f400e2516aa2d2c53d003885a94b4594ea007116aaad1b53b400e22d555a36a76801c4b56b68ae9cd0038945c28b7b155400e217052dd6556801c45c2ab76d55500388b8556edaaaa00712e1adbabaa7400e25176a2eac575003885dd4ba595ca00711772ae9b571400e22ee55d36ae2801c4bb8b74eeb7d0038945f28bdb163400e217d52f7658e801c45f6abdad63500388bed57b5ac6a00712fb2decbb19400e25184a302c5ad003886114c0d96aa00711842b03b5ab400e230856076b56801c4c22b81eed5500389462a8c4b173400e218b531165ca801c462cac46d72d00388c59588dae5a0071316ae22bb93400e25192a31ec5ed003886494c7d97aa0071192ab1fb5eb400e2325563f6bd6801c4c94b8faef550038946628cbb183400e2199532f660e801c4666acbad83500388ccd5975b06a0071333ae5cbc19400e251a0a33ec635003886854cf598ca00711a1ab3db631400e2343567b6c62801c4d0cb9eaf17d0038946a28d3b195400e21a9534d6656801c46a6ad36d95d00388d4d5a6db2ba00713532e9abcab400e251b2a35ec67d003886c94d7599fa00711b22b5db67d400e236456bb6cfa801c4d90baeef3e50038946ea8dbb1a9400e21ba536f66a6801c46eaadbada9d00388dd55b75b53a007100006d9bd4b400e1d1c2a382c6d50038870d4e059b4a00711c3ab80b6d3400e238757016da6801c4d68facdb5950038940000e4b1c1400e19cd53936702801c4734ae4edbfd00388e695c9db7fa00713493e916d1f400e25000000006fd0038400000001c4a00709d72ba6b72f400e23ae574d6e5e801c4ce8f9c9b37d00389400000001b5400e10000376e6ea801c3784aeeadd8d00388f095dd5bb1a007132bbe566ca3400e25000000006b5003840000d931b1a0070debabcfb797400e23d7579f6f2e801c4c7af8edb1b500389400000001a5400e10000354c6a6801c300000001ee50038400000003dca0070b123e226c39400e25000033d86750038668dcd131a1a0071000000007b9400e100000000f72801c2c1af82db0250038940000cc7197400e199c7336c66a801c400000001ee50038400000003dca0070afc3df66bdd400e250000321863d003860000cab193a0070c00000007b9400e100000000f72801c2bc6f785aecd0038946338c56189400e2000031ec636801c300000001ee50038400000003dca0070ae83dce6b8b400e25000030d861500386629cc4b187a007100003d0679d400e180000000f72801c2b7cf6f1ad950038940000c0617f400e19857308c60a801c40000ef19dcd0038600000003dca0070ad63daa6b41400e2500002f985e500386601cbfb17da00711d53ba9674f400e200000000f72801c2b38f669ac7d0038945e38bb6175400e217b72f4c5e2801c40000e659cad003860001e833cea0070ec6bd8b6aff400e2500002e585c5003860000bb3173a0070c000389670b400e1bbe777aceea801c4afcf5edab7d0038940000b7616d400e180002e4c5be801c30000de99bb5003860001d633a9a0070eb7bd6d6ac1400e2500002d585a5003860000b7316ba0070c00036c66d1400e18000738ce62801c3ac2f57daa950038940000b36165400e180002d4c59a801c36c0ed7d9add003880001c6b389a0070eaa3d526a89400e25164e2c58585003880000b33163a0070daa3b53669d400e200006fecdea801c3a90f515a9bd0038940000b0615d400e196372c4c57e801c40000d219a1d00386dc9db8b36da007129dbd396a55400e2500002b98565003860000afb15ba0070c00033d666f400e180006cacd82801c3a60f4b5a8f500389456b8ac6155400e200002b8c562801c30000ccd996d00386d69dacb354a00712923d226a27400e2500002ad854d00386565cac3155a007100003296647400e1b4f769ccd26801c4a34f45da83d0038940000a9614f400e195672aac54a801c4640ec7d98cd00388d11da1b33ea0071287bd0d69fb400e2500002a185350038654dca9314fa007118bbb166621400e233a7672ccd2801c4a0af409a79500389453b8a66149400e200002a0c532801c361eec39984500388000198332aa0070e7dbcf869d1400e250000295851d003860000a6b149a0070c00030665ff400e1800064ecc86801c39e2f3bda6f50038940000a46145400e194b7294c51a801c40000bf997bd0038600018f3318a0070e743ce669a9400e25146e2898505003880000a43143a0070d7bbaf665e1400e2000062ccc3e801c39bef375a65d0038940000a1613f400e1946728ac506801c45e0ebbd974500388c39d86b307a007126b3cd46985400e25000028184f5003860000a1b13ea0070d74bae865c3400e2000060ccbfe801c399cf32da5cd00389400009f613b400e19417280c4f2801c45c4eb8596d500388bfdd7f32f8a00712633cc36961400e25000027984e5003864fdc9f313aa007116e3adb65a9400e22f875eecbc2801c497cf2eda54500389400009d6135400e18000278c4de801c30000b55966d00386bc5d7832e9a007125b3cb36941400e25000027184cd0038600009d3135a0070c0002cf658f400e180005d4cb8a801c395cf2b1a4c500389400009b6131400e18000270c4ce801c30000b25960d00386b91d71b2dca0071253bca46921400e25000026984bd003864d9c9ab131a00711623ac36577400e200005bacb5a801c393ef275a44d003894000099612d400e18000268c4be801c30000af995b50038600016bb2cfa0070e4c3c956903400e25000026184ad00386000099312da0070d5cbab86561400e22d275a2cb2a801c4922f23da3d50038940000976129400e18000260c4ae801c3568eacd955d00388b31d65b2c4a00712453c8868e7400e25

def row10 (index : ℕ) : List (List ℕ) :=
  if index < 127 then
    let packedCell := Nat.shiftRight row10PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row11PackedData : ℕ := 0x146c225003860000515889a0070ca2a944b225400e21455289644a801c4516aa26d125003894000051b08b400e18000147622a801c3000051ec8a5003860000a3d914a0070d47aa8eb451400e25000014ac22d00386295452588ba00710a52949b22d400e214a5293645a801c4528aa4ad16500389429a852b08d400e20a6514b6232801c4298a52ec8c5003885314a5d918a007114caa97b463400e25000014ec23500386000053d88da0070ca7a94eb237400e214f529d646e801c453caa72d1b5003894000054b08f400e18000151623a801c30000546c8ed003860000a8d91da0070d51aaa2b475400e250aaa152c245003882a9454d890a00710aa2953b241400e215452a76482801c4552aa9ed1fd003894000055b091400e180001576246801c32aea55ac9150038855d4ab5922a00711572aacb489400e25000015ac24d003860000565892a0070caca958b249400e215952b16492801c4566aac6d24d0038942ba856b093400e20ae515b624e801c42b8a56ec93d003885714add927a007115caab7b49d400e25000015ec25500386000057d895a0070cafa95eb255400e215f52bd64aa801c457caaf2d29d003894000058b097400e18b15161625a801c42c4a586c965003885894b0d92ca00711622ac2b4b1400e250000166c25d003862c9458d897a00710b2a963b25f400e216552c764be801c4594ab1ed2f5003894000059b099400e180001676266801c32cea59ac98d0038859d4b35931a0071167aacdb4c7400e25000016ac26d003862d545a589aa00710b52969b269400e216a52d364d2801c45aaab4ed34500389400005bb09b400e1800016d626e801c32daa5b2c9bd003885b54b65937a007116daad9b4dd400e250b8a16ec275003882e145bd89da00710b8296fb275400e217052df64ea801c45c2ab7ed3a50038942ea85cb09f400e20ba5173627a801c42e8a5cac9ed003885d14b9593da00711742ae5b4f3400e250000176c2850038600005dd8a0a0070cbba976b281400e217752ed6502801c45dcabb2d3fd00389400005eb0a1400e18bd51796286801c42f4a5e6ca1d003885e94bcd943a007117a2af2b50b400e25000017ec28d0038600005f58a3a0070cbea97cb28d400e217d52f9651a801c45f6abe2d46500389430285fb0a5400e20c0517f6292801c4302a5feca4d003886054bfd949a00711812affb525400e250c2a182c29d00388309460d8a6a00710c22983b299400e218453076532801c4610ac1ad4c5003894000061b0a9400e18000187629e801c330ea61aca7d0038861d4c3594fa0071187ab0db53f400e25000018ac2a50038631546258a9a00710c5a989b2a7400e218b5313654e801c462cac4ed52d003894000063b0ab400e18c7518d62ae801c431ca636cab5003886394c6d956a007118eab1bb559400e250000192c2b50038632546458ada00710c92991b2b5400e21925323656a801c464aac8ad59d003894000065b0af400e18cb519562ba801c432ca652caed003886594ca595da00711962b29b575400e25000019ac2c50038600006658b0a0070ccca998b2c3400e219953316586801c4666acc6d60d003894000067b0b3400e1800019d62ca801c333aa672cb25003886754ce5964a007119dab38b591400e2500001a2c2d50038600006858b4a0070cd0a9a0b2d1400e21a1534165a2801c4686ad02d685003894000069b0b7400e180001a562da801c334aa692cb65003886954d2596ca00711a5ab48b5b1400e2500001aac2e50038600006a58b8a0070cd4a9a8b2e1400e21a9535165c2801c46a6ad42d6fd00389400006bb0bb400e180001ad62ea801c335aa6b2cba5003886b54d65974a00711adab58b5cf400e2500001b2c2f50038636546c58bca00710d929b0b2f1400e21b2536165e2801c46c8ad82d77d00389400006db0bf400e18db51b562fa801c436ca6d2cbe5003886d94da597ca00711b62b69b5f1400e2500001bac3050038637546e58c0a00710dd29b9b301400e21ba53736602801c46eaadcad80500389400006fb0c3400e18df51bd630a801c437ea6f6cc2d003886fd4ded985a00711bf2b7bb613400e2500001c2c31500386000070d8c4a0070ce1a9c2b313400e21c353856626801c470eae12d895003894392871b0c7400e20e451c7631e801c4390a71acc75003887214e3598ea00711c82b8db637400e250e6a1cac32500388399472d8c9a00710e6a9cbb325400e21cd5397664a801c4734ae5ad925003894000074b0cb400e18e951d1632e801c43a4a742ccbd003887494e85997a00711d22ba0b65d400e2500001d6c33d003863ad47558cea00710eba9d5b339400e21d753ab6672801c475caeaad9c50038943ba876b0d1400e20ee51db6342801c43b8a76acd0d003887714ed59a1a00711dc2bb4b685400e250f0a1dec34d003883c1477d8d3a00710f0a9dfb34d400e21e153bf669a801c4784aefada65003894000079b0d5400e18f351e56356801c43cca792cd5d003887994f259aba00711e6abc9b6ad400e2500001eac365003863d547a58d8a00710f5a9e9b363400e21eb53d366c6801c47aeaf4edb0d0038943e287bb0db400e20f851ef636e801c43e2a7becdb5003887c54f7d9b6a00711f12bdeb6d9400e2500001f6c37d003863ed47d58dea00710fba9f4b379400e21f753e966f2801c47dcafa6dbbd0038943fa87eb0e1400e20fe51fb6386801c43f8a7eace15003887f14fd59c2a00711fcabf5b707400e250000202c3950038640548058e4a00711012a00b391400e220254016722801c480ab006dc7d003894412881b0e7400e21045207639e801c4410a81ace750038882150359cea0071208ac0db737400e25000020ec3ad0038641d48358eaa0071107aa0cb3a9400e220f54196752801c483cb066dd4500389442a884b0ed400e210a521363b6801c442aa84ecedd00388855509d9dba00712152c25b76b400e25000021ac3c50038643548658f0a007110daa19b3c3400e221b54336786801c486eb0cade15003894000088b0f5400e1911522163d2801c4444a882cf450038888951059e8a0071222ac40b7a1400e25114a226c3dd00388451489d8f7a0071114aa26b3df400e2229544d67be801c48a4b136def500389446288bb0fb400e2118522d63ee801c4460a8b6cfb5003888c1516d9f6a00712302c5bb7d9400e250000236c3fd0038646d48d58ffa007111baa34b3fd400e2237546967fa801c48deb1a6dfdd00389400008fb103400e191f523d640e801c447ea8f2d035003888fd51e5a06a007123f2c78b817400e25122a242c41d0038848d490d907a00711232a43b41b400e224654876836801c491ab21ee0d500389449a892b10b400e2127524b642e801c449ca92ed0b500388939525da16a007124e2c96b857400e2512aa252c43d003884ad494d90fa007112b2a53b43d400e225654a7687a801c4958b29ae1e50038944ba896b113400e212f525b644e801c44bca96ed13d0038897952dda27a007125eacb6b89b400e25132a262c465003884cd498d918a00711332a63b461400e226654c768c2801c499ab31ee2fd00389400009bb11d400e1937526d6472801c44dea9b2d1cd003889bd5365a39a007126facd8b8e3400e2513ca276c485003884f149d5921a007113c2a75b487400e227854eb690e801c49e2b3aae42d00389450289fb127400e2140527f649a801c4502a9fad26d00388a0553f5a4da0071281acfcb931400e25144a286c4ad003885154a1d92ba0071145aa87b4af400e228b550f695e801c4a2cb43ae56d00389452a8a4b131400e214a529164c6801c4528aa46d30d00388a51548da61a0071294ad22b985400e2514ea29ac4dd0038853d4a6d936a007114f2a9ab4d9400e229e553569b2801c4a7ab4d6e6c50038945528a9b13d400e215452a564f2801c4552aa96d3c500388aa5552da78a00712a92d4ab9df400e25158a2aec50d003885654abd942a0071159aaafb509400e22b3555f6a12801c4aceb57ee83d00389457a8aeb149400e215f52bb6522801c457caaead48500388af955d5a90a00712bead75ba3f400e25164a2c6c53d003885954b1594ea00711652ac5b53b400e22ca558b6a76801c4b28b62ee9cd0038945aa8b4b155400e216a52d16556801c45aaab46d55500388b55568daaaa00712d5ada2baa7400e25170a2dec575003885c14b7595ca0071170aaddb571400e22e155bb6ae2801c4b86b6eaeb7d0038945da8bab163400e217752e9658e801c45dcaba6d63500388bb9574dac6a00712ee2dd3bb19400e2517ca2f6c5ad003885f54bdd96aa007117daaf6b5ab400e22fb55ed6b56801c4becb7b2ed550038946128c0b173400e2184530365ca801c4610ac0ed72d00388c21581dae5a0071308ae07bb93400e2518aa312c5ed0038862d4c4597aa007118b2b11b5eb400e231656236bd6801c4c5ab88aef5500389464a8c7b183400e2192531f660e801c464aac7ed83500388c9558fdb06a00713252e3ebc19400e25198a32ec635003886654cbd98ca0071199ab2eb631400e2333565d6c62801c4cceb972f17d0038946828cfb195400e21a1533d6656801c4686acf6d95d00388d0d59edb2ba00713432e7abcab400e251a8a34ec67d003886a54d3599fa00711a9ab4db67d400e2353569b6cfa801c4d4cba6af3e50038946ca8d7b1a9400e21b2535d66a6801c46c8ad76da9d00388d915aedb53a00713642ebbbd4b400e251baa36ec6d5003886e94dbd9b4a00711baab6eb6d3400e237556dd6da6801c4dd6bb76f68500389400000001c1400e10000382a702801c3704ae02dbfd00388e095c05b7fa0071385af01bdfd400e25000000007050038400000001c1a007080000000705400e100000000e0a801c20000000385d00385400000001c1400e100000000706801c200000001c15003840000000382a007080006e56dc7400e1d000000007050038400000001c1a007080000000705400e100000000e0a801c20001b09b5f500387400000001c1400e100000000706801c200000001c15003840000000382a0070b513ea16d3b400e25000000007050038400000001c1a007080000000705400e100000000e0a801c20001a11b3f500387400000001bb400e10000382c702801c300000001c15003840000000382a0070b34be686cc3400e25000000006cd003840000dc31b7a0070c0000000705400e100000000e0a801c2c9ef939b2350038940000d661ab400e18000360c6be801c300000001c15003840000000382a0070b1b3e356c5b400e250000349868d003860000d4b1a7a0070c0000000705400e100000000e0a801c2c3ef879b0ad0038940000cf619d400e18000344c682801c300000001c15003840000000382a0070b053e096bff400e2500003318655003860000ce3199a0070c0000000705400e100000000e0a801c2becf7d5af550038940000c9618f400e1800032cc64e801c300000001c15003840000000382a0070af1bde16bad400e2500003198625003860000c8318da0070c0000000705400e100000000e0a801c2ba0f73dae1d0038940000c36185400e18000316c622801c300000001c15003840000000382a0070adfbdbe6b63400e25000030585fd003860000c33183a0070c0000000705400e100000000e0a801c2b5ef6b5ad050038945fb8be617b400e20000302c5fa801c300000001c15003840000000382a0070acfbd9e6b21400e2500002f185dd003860000be3179a0070c0000000705400e100000000e0a801c2b20f639ac050038940000ba6171400e180002f0c5d2801c300000001c15003840000000382a0070ac13d806ae3400e2500002e185b5003860000ba3170a0070c0003826701400e180000000e0a801c2ae8f5c9ab1d0038940000b66169400e180002e0c5b2801c30000de19b95003860000000382a0070ab33d656aab400e2500002d18595003860000b63168a0070c00036b66cb400e180000000e0a801c2ab2f561aa4500389459b8b26161400e200002d0c592801c36beed799ac5003880000000382a0070aa6bd4c6a77400e2500002c5857d003860000b2b161a0070c0003536699400e18000700cdea801c3a82f501a97d0038940000af615b400e196272c2c576801c40000d219a0d003860001b9b36da0070e9b3d346a47400e2515ce2b5855d003880000af315aa0070c00033d666d400e180006cecd86801c3a56f4a5a8bd0038940000ac6155400e180002b6c55e801c30000cd1996d003860001ae3355a0070e903d1e6a19400e25156e2a98545003880000ac3153a0070c00032a6647400e180006a2cd2a801c3a2cf451a80d0038940000a9614f400e180002aac546801c30000c8598d5003860001a3b340a0070e863d0a69ef400e2500002a1852d003860000a9314ea0070d8cbb186623400e2000067accda801c3a04f401a76d0038940000a66149400e1950729ec52e801c40000c41984500386cd1d99b32ca007127cbcf769c7400e250000295851d003860000a6b148a0070c0003086601400e1b2b7654cc8e801c49def3b9a6d50038940000a46143400e194b7294c516801c4602ec0197c500388000191331aa0070e733ce469a1400e25146e2898505003880000a43143a0070c0002f965e3400e1b1a7632cc4a801c49bcf371a6450038940000a1613f400e1946728ac502801c40000bc9975500386000189330aa0070e6abcd3697f400e25000028184f5003860000a1b13ea0070d763aeb65c7400e20000614cc0a801c399af32da5b500389400009f613b400e18000282c4f2801c30000b9596e500386000181b2fba0070e62bcc3695d400e25000027984dd003864fdc9f3139a007116fbade65ad400e200005f8cbd2801c397af2eda53500389400009d6135400e193d7278c4de801c40000b61967d0038600017ab2eda0070e5b3cb4693d400e25

def row11 (index : ℕ) : List (List ℕ) :=
  if index < 126 then
    let packedCell := Nat.shiftRight row11PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row12PackedData : ℕ := 0x51b08b400e18000145622a801c328aa512c8a5003885154a25914a0071145aa89b451400e250000146c22d00386000051d88ba0070c000147b22d400e1800028f645a801c351eaa3ad165003894000052b08d400e18a551496232801c4294a526c8c5003885294a4d918a007114a2a92b463400e250a6a14ac23500388299452d88da00710a6294bb237400e214c5297646e801c4532aa5ed1b5003894000053b08f400e1800014f623a801c329ea53ac8ed0038853d4a7591da007114f2a9cb475400e250000152c245003860000545890a0070c000151b241400e180002a36482801c3546aa8ad1fd0038942aa854b091400e20aa51536246801c42a8a54ec915003885514a9d922a0071154aaa7b489400e250000156c24d00386000055d892a0070caba956b249400e215752ad6492801c455caab2d24d003894000056b093400e18000159624e801c32b2a562c93d003885654ac5927a0071159aab1b49d400e250aea15ac255003882b9456d895a00710ae295bb255400e215c52b764aa801c4572aaded29d003894000057b097400e1800015f625a801c32bea57ac9650038857d4af592ca007115f2abcb4b1400e250000162c25d003862c54585897a00710b12961b25f400e216252c364be801c4588ab0ad2f5003894000059b099400e18b251636266801c42caa58ec98d003885954b1d931a00711652ac7b4c7400e250000166c26d00386000059d89aa0070cb3a966b269400e216752cd64d2801c459eab36d34500389400005ab09b400e18b55169626e801c42d4a5a6c9bd003885a94b4d937a007116aaad3b4dd400e25000016ec2750038600005b589da0070cb6a96cb275400e216d52d964ea801c45b6ab66d3a50038942e285bb09f400e20b8516f627a801c42e0a5bec9ed003885c14b7d93da0071170aadfb4f3400e250baa172c285003882e945cd8a0a00710ba2972b281400e217452e56502801c45d0ab96d3fd00389400005db0a1400e180001776286801c32eea5daca1d003885dd4bb5943a00711772aecb50b400e25000017ac28d003862f545e58a3a00710bd2979b28d400e217a52f3651a801c45e8abcad46500389400005fb0a5400e1800017d6292801c32faa5f2ca4d003885f54be5949a007117daaf8b525400e250c0a17ec29d0038830145fd8a6a00710c0a97fb299400e218152ff6532801c4604abfed4c500389430a860b0a9400e20c25183629e801c4308a60eca7d003886114c1d94fa00711842b06b53f400e250000186c2a500386000061d8a9a0070cc3a986b2a7400e2187530d654e801c461eac36d52d003894000062b0ab400e18c5518962ae801c4316a626cab50038862d4c4d956a007118b2b13b559400e25000018ec2b50038631d46358ada00710c7298db2b5400e218e531b656a801c463aac6ed59d003894000064b0af400e18c9519162ba801c4324a646caed003886494c8d95da0071192ab22b575400e250000196c2c50038632d46558b0a00710cb2994b2c3400e219653296586801c4658aca6d60d003894000066b0b3400e1800019962ca801c3332a662cb25003886654cc5964a0071199ab31b591400e25000019ec2d50038600006758b4a0070ccea99cb2d1400e219d533965a2801c4676ace2d685003894000068b0b7400e180001a162da801c3342a682cb65003886854d0596ca00711a1ab40b5b1400e2500001a6c2e50038600006958b8a0070cd2a9a4b2e1400e21a5534965c2801c4696ad22d6fd00389400006ab0bb400e180001a962ea801c3352a6a2cba5003886a54d45974a00711a9ab50b5cf400e2500001aec2f50038600006b58bca0070cd6a9acb2f1400e21ad535965e2801c46b6ad62d77d00389400006cb0bf400e18d951b162fa801c4364a6c2cbe5003886c94d8597ca00711b22b60b5f1400e2500001b6c3050038636d46d58c0a00710db29b4b301400e21b653696602801c46d8ada6d80500389400006eb0c3400e18dd51b9630a801c4374a6e6cc2d003886e94dcd985a00711baab72b613400e2500001bec3150038637d46f58c4a00710dfa9bdb313400e21bf537b6626801c46fcadeed895003894000070b0c7400e180001c3631e801c3386a70acc750038870d4e1598ea00711c3ab84b637400e250e4a1c6c32500388391471d8c9a00710e429c6b325400e21c8538d664a801c4720ae36d92500389439a872b0cb400e20e651cb632e801c439aa72eccbd003887354e5d997a00711cd2b96b65d400e2500001d2c33d003863a547458cea00710e929d0b339400e21d253a16672801c4748ae82d9c5003894000075b0d1400e18eb51d56342801c43aea756cd0d0038875d4ead9a1a00711d72baab685400e250eea1dac34d003883b9476d8d3a00710ee29dab34d400e21dc53b5669a801c4770aed2da650038943c2877b0d5400e20f051df6356801c43c2a77ecd5d003887854efd9aba00711e12bbeb6ad400e2500001e6c365003863cd47958d8a00710f329e4b363400e21e653c966c6801c479aaf26db0d00389400007ab0db400e18f551e9636e801c43d6a7a6cdb5003887ad4f4d9b6a00711ebabd3b6d9400e250f8a1eec37d003883e147bd8dea00710f8a9efb379400e21f153df66f2801c47c4af7adbbd00389400007db0e1400e18fb51f56386801c43eea7d2ce15003887dd4fa59c2a00711f72be9b707400e250fea1fac395003883f947ed8e4a00710fe29fab391400e21fc53f56722801c47f2afd6dc7d003894000080b0e7400e19015201639e801c4404a802ce750038880950059cea0071202ac01b737400e25104a206c3ad00388411481d8eaa00711042a06b3a9400e2208540d6752801c4822b036dd45003894000083b0ed400e1907520d63b6801c441ea832cedd0038883d50659dba007120f2c19b76b400e2510aa212c3c500388429484d8f0a007110aaa13b3c3400e221554276786801c4854b096de15003894000086b0f5400e190d521963d2801c4436a866cf450038886d50cd9e8a007121bac32b7a1400e250000222c3dd0038644548858f7a00711112a20b3df400e2222544167be801c488ab102def5003894452889b0fb400e2114522763ee801c4452a89acfb5003888a551359f6a00712292c4db7d9400e25118a22ec3fd0038846148b58ffa00711182a2db3fd400e2230545b67fa801c48c0b16edfdd00389400008db103400e191b5235640e801c446ea8d2d035003888dd51a5a06a0071237ac69b817400e25000023ec41d0038647d48f5907a007111faa3cb41b400e223f54796836801c48fcb1e2e0d500389448a890b10b400e21235243642e801c448ca90ed0b500388919521da16a0071246ac87b857400e25126a24ac43d0038849d492d90fa00711272a4bb43d400e224e5497687a801c4938b25ae1e50038944aa894b113400e212b5253644e801c44aca94ed13d00388959529da27a00712562ca6b89b400e2512ea25ac465003884bd496d918a007112f2a5bb461400e225e54b768c2801c497ab2dae2fd0038944ca898b11d400e213352636472801c44cca98ed1cd00388999531da39a0071266acc7b8e3400e25000026ec485003864dd49b5921a0071137aa6cb487400e226f54d9690e801c49beb362e42d0038944f289db127400e213c5275649a801c44f0a9d6d26d003889e153ada4da0071278aceab931400e25140a27ec4ad0038850149fd92ba0071140aa7eb4af400e228154fd695e801c4a06b3f2e56d0038945128a1b131400e2145528764c6801c4516aa1ed30d00388a2d543da61a007128b2d0eb985400e2514aa292c4dd003885294a45936a007114a2a91b4d9400e2294552369b2801c4a52b48ae6c500389453a8a6b13d400e214f529b64f2801c453caa6ad3c500388a7954d5a78a007129ead35b9df400e25154a2a6c50d003885514a95942a0071154aaa5b509400e22a9554b6a12801c4aa4b52ae83d0038945628abb149400e215952af6522801c4566aabed48500388acd557da90a00712b3ad5fba3f400e2515ea2bac53d0038857d4aed94ea007115f2abab53b400e22be55756a76801c4afab5d6e9cd0038945928b1b155400e216552c56556801c4594ab16d55500388b29562daaaa00712ca2d8bbaa7400e2516aa2d2c575003885a94b4595ca007116aaad1b571400e22d555a36ae2801c4b56b68aeb7d0038945c28b7b163400e217052dd658e801c45c2ab76d63500388b8556edac6a00712e1adbabb19400e25176a2eac5ad003885dd4ba596aa00711772ae9b5ab400e22ee55d36b56801c4bb8b74eed550038945f28bdb173400e217d52f765ca801c45f6abdad72d00388bed57b5ae5a00712fb2decbb93400e25184a302c5ed003886114c0d97aa00711842b03b5eb400e230856076bd6801c4c22b81eef5500389462a8c4b183400e218b5311660e801c462cac46d83500388c59588db06a0071316ae22bc19400e25192a31ec635003886494c7d98ca0071192ab1fb631400e2325563f6c62801c4c94b8faf17d0038946628cbb195400e2199532f6656801c4666acbad95d00388ccd5975b2ba0071333ae5cbcab400e250000000066d00384000000019ba007080000000671400e100000000ce2801c2000000033ad003854000000019b400e10000000066e801c2000000019c5003840000000338a007080000000ceb400e150000000066d00384000000019ba007080000000671400e100000000ce2801c2000000033ad003854000000019b400e10000000066e801c2000000019c5003840000000338a007080000000ceb400e150000000066d00384000000019ba007080000000671400e100000000ce2801c2000000033ad003854000000019b400e10000000066e801c2000000019c5003840000000338a007080000000ceb400e150000000066d00384000000019ba007080000000671400e100000000ce2801c2000000033ad003854000000019b400e10000000066e801c2000000019c5003840000000338a007080000000ceb400e150000000066d00384000000019ba007080000000671400e100000000ce2801c2000000033ad003854000000019b400e10000000066e801c2000000019c5003840000000338a007080000000ceb400e150000000066d00384000000019ba007080000000671400e100000000ce2801c2000000033ad003854000000019b400e10000000066e801c2000000019c5003840000000338a007080000000ceb400e150000000066d00384000000019ba007080000000671400e100000000ce2801c2000000033ad003854000000019b400e10000000066e801c2000000019c5003840000000338a007080000000ceb400e150000000066d00384000000019ba007080000000671400e100000000ce2801c200019c1b335003874000000019b400e10000000066e801c2000000019c5003840000000338a007080006576c99400e1d0000000066d00384000000019ba007080000000671400e100000000ce2801c20001901b1a5003874000000019b400e10000000066e801c2000000019c5003840000000338a0070b153e296c3b400e250000000066d00384000000019ba007080000000671400e100000000ce2801c2c2af851b03d0038940000cd6199400e18000000066e801c2000000019c5003840000000338a0070b00be006be5400e25000032d864d003860000cd3197a0070c0000000671400e100000000ce2801c2bdcf7b5aefd0038940000c8618d400e1800032ac646801c3000000019c5003840000000338a0070aee3ddb6b99400e250000319862500386641cc7b18ca007100000000671400e100000000ce2801c2b96f729add50038940000c36183400e18000314c61e801c3000000019c5003840000000338a0070addbdba6b55400e25000030585fd00386619cc2b182a007100000000671400e100000000ce2801c2b56f6a9accd0038945fb8be6179400e20000302c5f6801c3000000019c5003840000000338a0070ace3d9b6b15400e2500002f185d5003865f5cbe3178a007100000000671400e100000000ce2801c2b1cf635abdd0038940000ba6171400e180002f0c5d2801c3000000019c5003840000000338a0070ac03d7f6adb400e2500002e185b5003860000ba3170a0070c0000000671400e100000000ce2801c2ae6f5c9aafd0038940000b66169400e197172e0c5b2801c4000000019c5003840000000338a0070ab33d656aa5400e2500002d58595003860000b6b168a0070c0000000671400e100000000ce2801c2ab2f561aa2d0038940000b36163400e180002d2c596801c3000000019c5003840000000338a0070aa73d4d6a73400e2500002c5857d003860000b33161a0070c0000000671400e100000000ce2801c2a84f505a96d0038940000b0615b400e196372c4c57a801c4000000019c5003840000000338a0070a9bbd366a45400e2500002b98565003860000afb15aa0070c0000000671400e100000000ce2801c2a5af4ada8bd0038940000ad6155400e180002b8c55e801c30000ce199ad003860000000338a0070a913d216a19400e2500002ad854d003860000acb154a0070c0003346657400e180000000ce2801c2a30f459a80d0038940000aa614f400e195772acc546801c40000ca99915003860000000338a0070a873d0d69ef400e2500002a18535003860000aa314ea0070d913b216633400e200000000ce2801c2a0af40da7750038940000a76149400e180002a2c532801c30000c6598850038600019c3337a0070e7dbcfa69c9400e250000299851d0038653dca73149a007100003116611400e1800066cccba801c39e4f3c5a6dd00389452b8a46145400e20000298c51a801c30000c259805003860001973325a0070e753ce869a5400e25

def row12 (index : ℕ) : List (List ℕ) :=
  if index < 125 then
    let packedCell := Nat.shiftRight row12PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row13PackedData : ℕ := 0x146c22d00386000051588ba0070ca2a944b22d400e21455289645a801c4516aa26d165003894000051b08d400e180001476232801c3000051ec8c5003860000a3d918a0070d47aa8eb463400e25000014ac23500386295452588da00710a52949b237400e214a5293646e801c4528aa4ad1b500389429a852b08f400e20a6514b623a801c4298a52ec8ed003885314a5d91da007114caa97b475400e25000014ec24500386000053d890a0070ca7a94eb241400e214f529d6482801c453caa72d1fd003894000054b091400e180001516246801c30000546c915003860000a8d922a0070d51aaa2b489400e250aaa152c24d003882a9454d892a00710aa2953b249400e215452a76492801c4552aa9ed24d003894000055b093400e18000157624e801c32aea55ac93d0038855d4ab5927a00711572aacb49d400e25000015ac255003860000565895a0070caca958b255400e215952b164aa801c4566aac6d29d0038942ba856b097400e20ae515b625a801c42b8a56ec965003885714add92ca007115caab7b4b1400e25000015ec25d00386000057d897a0070cafa95eb25f400e215f52bd64be801c457caaf2d2f5003894000058b099400e18b151616266801c42c4a586c98d003885894b0d931a00711622ac2b4c7400e250000166c26d003862c9458d89aa00710b2a963b269400e216552c764d2801c4594ab1ed345003894000059b09b400e18000167626e801c32cea59ac9bd0038859d4b35937a0071167aacdb4dd400e25000016ac275003862d545a589da00710b52969b275400e216a52d364ea801c45aaab4ed3a500389400005bb09f400e1800016d627a801c32daa5b2c9ed003885b54b6593da007116daad9b4f3400e250b8a16ec285003882e145bd8a0a00710b8296fb281400e217052df6502801c45c2ab7ed3fd0038942ea85cb0a1400e20ba51736286801c42e8a5caca1d003885d14b95943a00711742ae5b50b400e250000176c28d0038600005dd8a3a0070cbba976b28d400e217752ed651a801c45dcabb2d46500389400005eb0a5400e18bd51796292801c42f4a5e6ca4d003885e94bcd949a007117a2af2b525400e25000017ec29d0038600005f58a6a0070cbea97cb299400e217d52f96532801c45f6abe2d4c500389430285fb0a9400e20c0517f629e801c4302a5feca7d003886054bfd94fa00711812affb53f400e250c2a182c2a500388309460d8a9a00710c22983b2a7400e21845307654e801c4610ac1ad52d003894000061b0ab400e1800018762ae801c330ea61acab50038861d4c35956a0071187ab0db559400e25000018ac2b50038631546258ada00710c5a989b2b5400e218b5313656a801c462cac4ed59d003894000063b0af400e18c7518d62ba801c431ca636caed003886394c6d95da007118eab1bb575400e250000192c2c50038632546458b0a00710c92991b2c3400e219253236586801c464aac8ad60d003894000065b0b3400e18cb519562ca801c432ca652cb25003886594ca5964a00711962b29b591400e25000019ac2d50038600006658b4a0070ccca998b2d1400e2199533165a2801c4666acc6d685003894000067b0b7400e1800019d62da801c333aa672cb65003886754ce596ca007119dab38b5b1400e2500001a2c2e50038600006858b8a0070cd0a9a0b2e1400e21a1534165c2801c4686ad02d6fd003894000069b0bb400e180001a562ea801c334aa692cba5003886954d25974a00711a5ab48b5cf400e2500001aac2f50038600006a58bca0070cd4a9a8b2f1400e21a9535165e2801c46a6ad42d77d00389400006bb0bf400e180001ad62fa801c335aa6b2cbe5003886b54d6597ca00711adab58b5f1400e2500001b2c3050038636546c58c0a00710d929b0b301400e21b253616602801c46c8ad82d80500389400006db0c3400e18db51b5630a801c436ca6d2cc2d003886d94da5985a00711b62b69b613400e2500001bac3150038637546e58c4a00710dd29b9b313400e21ba53736626801c46eaadcad89500389400006fb0c7400e18df51bd631e801c437ea6f6cc75003886fd4ded98ea00711bf2b7bb637400e2500001c2c32500386000070d8c9a0070ce1a9c2b325400e21c35385664a801c470eae12d925003894392871b0cb400e20e451c7632e801c4390a71accbd003887214e35997a00711c82b8db65d400e250e6a1cac33d00388399472d8cea00710e6a9cbb339400e21cd53976672801c4734ae5ad9c5003894000074b0d1400e18e951d16342801c43a4a742cd0d003887494e859a1a00711d22ba0b685400e2500001d6c34d003863ad47558d3a00710eba9d5b34d400e21d753ab669a801c475caeaada650038943ba876b0d5400e20ee51db6356801c43b8a76acd5d003887714ed59aba00711dc2bb4b6ad400e250f0a1dec365003883c1477d8d8a00710f0a9dfb363400e21e153bf66c6801c4784aefadb0d003894000079b0db400e18f351e5636e801c43cca792cdb5003887994f259b6a00711e6abc9b6d9400e2500001eac37d003863d547a58dea00710f5a9e9b379400e21eb53d366f2801c47aeaf4edbbd0038943e287bb0e1400e20f851ef6386801c43e2a7bece15003887c54f7d9c2a00711f12bdeb707400e2500001f6c395003863ed47d58e4a00710fba9f4b391400e21f753e96722801c47dcafa6dc7d0038943fa87eb0e7400e20fe51fb639e801c43f8a7eace75003887f14fd59cea00711fcabf5b737400e250000202c3ad0038640548058eaa00711012a00b3a9400e220254016752801c480ab006dd45003894412881b0ed400e2104520763b6801c4410a81acedd0038882150359dba0071208ac0db76b400e25000020ec3c50038641d48358f0a0071107aa0cb3c3400e220f54196786801c483cb066de1500389442a884b0f5400e210a521363d2801c442aa84ecf4500388855509d9e8a00712152c25b7a1400e25000021ac3dd0038643548658f7a007110daa19b3df400e221b543367be801c486eb0cadef5003894000088b0fb400e1911522163ee801c4444a882cfb50038888951059f6a0071222ac40b7d9400e25114a226c3fd00388451489d8ffa0071114aa26b3fd400e2229544d67fa801c48a4b136dfdd00389446288bb103400e2118522d640e801c4460a8b6d035003888c1516da06a00712302c5bb817400e250000236c41d0038646d48d5907a007111baa34b41b400e223754696836801c48deb1a6e0d500389400008fb10b400e191f523d642e801c447ea8f2d0b5003888fd51e5a16a007123f2c78b857400e25122a242c43d0038848d490d90fa00711232a43b43d400e22465487687a801c491ab21ee1e500389449a892b113400e2127524b644e801c449ca92ed13d00388939525da27a007124e2c96b89b400e2512aa252c465003884ad494d918a007112b2a53b461400e225654a768c2801c4958b29ae2fd0038944ba896b11d400e212f525b6472801c44bca96ed1cd0038897952dda39a007125eacb6b8e3400e25132a262c485003884cd498d921a00711332a63b487400e226654c7690e801c499ab31ee42d00389400009bb127400e1937526d649a801c44dea9b2d26d003889bd5365a4da007126facd8b931400e2513ca276c4ad003884f149d592ba007113c2a75b4af400e227854eb695e801c49e2b3aae56d00389450289fb131400e2140527f64c6801c4502a9fad30d00388a0553f5a61a0071281acfcb985400e25144a286c4dd003885154a1d936a0071145aa87b4d9400e228b550f69b2801c4a2cb43ae6c500389452a8a4b13d400e214a529164f2801c4528aa46d3c500388a51548da78a0071294ad22b9df400e2514ea29ac50d0038853d4a6d942a007114f2a9ab509400e229e55356a12801c4a7ab4d6e83d0038945528a9b149400e215452a56522801c4552aa96d48500388aa5552da90a00712a92d4aba3f400e25158a2aec53d003885654abd94ea0071159aaafb53b400e22b3555f6a76801c4aceb57ee9cd00389457a8aeb155400e215f52bb6556801c457caaead55500388af955d5aaaa00712bead75baa7400e25164a2c6c575003885954b1595ca00711652ac5b571400e22ca558b6ae2801c4b28b62eeb7d0038945aa8b4b163400e216a52d1658e801c45aaab46d63500388b55568dac6a00712d5ada2bb19400e25170a2dec5ad003885c14b7596aa0071170aaddb5ab400e22e155bb6b56801c4b86b6eaed550038945da8bab173400e217752e965ca801c45dcaba6d72d00388bb9574dae5a00712ee2dd3bb93400e2500002f905ed003865f10bdd97aa007117c2af6b5eb400e22f855ed6bd6801c4becb7b2ef55003894000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080000000bed400e15000000005f500384000000017ca0070800000005f1400e100000000be2801c200000002fb5003854000000017d400e1000000005f2801c2000000017c50038400000002f8a007080005f66beb400e1d000000005f500384000000017ca0070800000005f1400e100000000be2801c200017d5af15003874000000017d400e1000000005f2801c2000000017c50038400000002f8a007080005e36ba1400e1d000000005f500384000000017ca0070800000005f1400e100000000be2801c20001749adfd003874000000017d400e1000000005f2801c2000000017c50038400000002f8a0070ae13dc16b5d400e25000000005f500384000000017ca0070800000005f1400e100000000be2801c200016c9acf5003874000000017d400e1000000005f2801c2000000017c50038400000002f8a0070ad23da36b1f400e2500002f985e5003860000be317ba0070c00000005f1400e100000000be2801c20001655ac050038740000bc6175400e180002f8c5de801c3000000017c50038400000002f8a0070ac43d876ae5400e2500002e985c5003860000bc3173a0070c00000005f1400e100000000be2801c200015e9ab250038740000b8616d400e180002e8c5be801c3000000017c50038400000002f8a0070ab73d6d6aaf400e2500002d985a5003860000b8316ba0070c00000005f1400e100000000be2801c2ac4f585aa5d0038940000b56165400e180002dac59e801c3000000017c50038400000002f8a0070aab3d556a7f400e2500002cd8585003860000b4b164a0070c00000005f1400e100000000be2801c20001529a99d0038740000b1615d400e180002ccc582801c3000000017c50038400000002f8a0070aa03d3f6a51400e2500002c1856d003860000b1b15da0070c00000005f1400e100000000be2801c2a6af4d1a8ed0038940000ae6157400e180002c0c56a801c3000000017c50038400000002f8a0070a953d296a25400e25

def row13 (index : ℕ) : List (List ℕ) :=
  if index < 124 then
    let packedCell := Nat.shiftRight row13PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row14PackedData : ℕ := 0x51b08d400e180001456232801c328aa512c8c5003885154a25918a0071145aa89b463400e250000146c23500386000051d88da0070c000147b237400e1800028f646e801c351eaa3ad1b5003894000052b08f400e18a55149623a801c4294a526c8ed003885294a4d91da007114a2a92b475400e250a6a14ac24500388299452d890a00710a6294bb241400e214c52976482801c4532aa5ed1fd003894000053b091400e1800014f6246801c329ea53ac9150038853d4a75922a007114f2a9cb489400e250000152c24d003860000545892a0070c000151b249400e180002a36492801c3546aa8ad24d0038942aa854b093400e20aa5153624e801c42a8a54ec93d003885514a9d927a0071154aaa7b49d400e250000156c25500386000055d895a0070caba956b255400e215752ad64aa801c455caab2d29d003894000056b097400e18000159625a801c32b2a562c965003885654ac592ca0071159aab1b4b1400e250aea15ac25d003882b9456d897a00710ae295bb25f400e215c52b764be801c4572aaded2f5003894000057b099400e1800015f6266801c32bea57ac98d0038857d4af5931a007115f2abcb4c7400e250000162c26d003862c5458589aa00710b12961b269400e216252c364d2801c4588ab0ad345003894000059b09b400e18b25163626e801c42caa58ec9bd003885954b1d937a00711652ac7b4dd400e250000166c27500386000059d89da0070cb3a966b275400e216752cd64ea801c459eab36d3a500389400005ab09f400e18b55169627a801c42d4a5a6c9ed003885a94b4d93da007116aaad3b4f3400e25000016ec2850038600005b58a0a0070cb6a96cb281400e216d52d96502801c45b6ab66d3fd0038942e285bb0a1400e20b8516f6286801c42e0a5beca1d003885c14b7d943a0071170aadfb50b400e250baa172c28d003882e945cd8a3a00710ba2972b28d400e217452e5651a801c45d0ab96d46500389400005db0a5400e180001776292801c32eea5daca4d003885dd4bb5949a00711772aecb525400e25000017ac29d003862f545e58a6a00710bd2979b299400e217a52f36532801c45e8abcad4c500389400005fb0a9400e1800017d629e801c32faa5f2ca7d003885f54be594fa007117daaf8b53f400e250c0a17ec2a50038830145fd8a9a00710c0a97fb2a7400e218152ff654e801c4604abfed52d00389430a860b0ab400e20c2518362ae801c4308a60ecab5003886114c1d956a00711842b06b559400e250000186c2b500386000061d8ada0070cc3a986b2b5400e2187530d656a801c461eac36d59d003894000062b0af400e18c5518962ba801c4316a626caed0038862d4c4d95da007118b2b13b575400e25000018ec2c50038631d46358b0a00710c7298db2c3400e218e531b6586801c463aac6ed60d003894000064b0b3400e18c9519162ca801c4324a646cb25003886494c8d964a0071192ab22b591400e250000196c2d50038632d46558b4a00710cb2994b2d1400e2196532965a2801c4658aca6d685003894000066b0b7400e1800019962da801c3332a662cb65003886654cc596ca0071199ab31b5b1400e25000019ec2e50038600006758b8a0070ccea99cb2e1400e219d533965c2801c4676ace2d6fd003894000068b0bb400e180001a162ea801c3342a682cba5003886854d05974a00711a1ab40b5cf400e2500001a6c2f50038600006958bca0070cd2a9a4b2f1400e21a5534965e2801c4696ad22d77d00389400006ab0bf400e180001a962fa801c3352a6a2cbe5003886a54d4597ca00711a9ab50b5f1400e2500001aec3050038600006b58c0a0070cd6a9acb301400e21ad53596602801c46b6ad62d80500389400006cb0c3400e18d951b1630a801c4364a6c2cc2d003886c94d85985a00711b22b60b613400e2500001b6c3150038636d46d58c4a00710db29b4b313400e21b653696626801c46d8ada6d89500389400006eb0c7400e18dd51b9631e801c4374a6e6cc75003886e94dcd98ea00711baab72b637400e2500001bec3250038637d46f58c9a00710dfa9bdb325400e21bf537b664a801c46fcadeed925003894000070b0cb400e180001c3632e801c3386a70accbd0038870d4e15997a00711c3ab84b65d400e250e4a1c6c33d00388391471d8cea00710e429c6b339400e21c8538d6672801c4720ae36d9c500389439a872b0d1400e20e651cb6342801c439aa72ecd0d003887354e5d9a1a00711cd2b96b685400e2500001d2c34d003863a547458d3a00710e929d0b34d400e21d253a1669a801c4748ae82da65003894000075b0d5400e18eb51d56356801c43aea756cd5d0038875d4ead9aba00711d72baab6ad400e250eea1dac365003883b9476d8d8a00710ee29dab363400e21dc53b566c6801c4770aed2db0d0038943c2877b0db400e20f051df636e801c43c2a77ecdb5003887854efd9b6a00711e12bbeb6d9400e2500001e6c37d003863cd47958dea00710f329e4b379400e21e653c966f2801c479aaf26dbbd00389400007ab0e1400e18f551e96386801c43d6a7a6ce15003887ad4f4d9c2a00711ebabd3b707400e250f8a1eec395003883e147bd8e4a00710f8a9efb391400e21f153df6722801c47c4af7adc7d00389400007db0e7400e18fb51f5639e801c43eea7d2ce75003887dd4fa59cea00711f72be9b737400e250fea1fac3ad003883f947ed8eaa00710fe29fab3a9400e21fc53f56752801c47f2afd6dd45003894000080b0ed400e1901520163b6801c4404a802cedd0038880950059dba0071202ac01b76b400e25104a206c3c500388411481d8f0a00711042a06b3c3400e2208540d6786801c4822b036de15003894000083b0f5400e1907520d63d2801c441ea832cf450038883d50659e8a007120f2c19b7a1400e2510aa212c3dd00388429484d8f7a007110aaa13b3df400e2215542767be801c4854b096def5003894000086b0fb400e190d521963ee801c4436a866cfb50038886d50cd9f6a007121bac32b7d9400e250000222c3fd0038644548858ffa00711112a20b3fd400e2222544167fa801c488ab102dfdd003894452889b103400e21145227640e801c4452a89ad035003888a55135a06a00712292c4db817400e25118a22ec41d0038846148b5907a00711182a2db41b400e2230545b6836801c48c0b16ee0d500389400008db10b400e191b5235642e801c446ea8d2d0b5003888dd51a5a16a0071237ac69b857400e25000023ec43d0038647d48f590fa007111faa3cb43d400e223f5479687a801c48fcb1e2e1e500389448a890b113400e21235243644e801c448ca90ed13d00388919521da27a0071246ac87b89b400e25126a24ac4650038849d492d918a00711272a4bb461400e224e549768c2801c4938b25ae2fd0038944aa894b11d400e212b52536472801c44aca94ed1cd00388959529da39a00712562ca6b8e3400e2512ea25ac485003884bd496d921a007112f2a5bb487400e225e54b7690e801c497ab2dae42d0038944ca898b127400e21335263649a801c44cca98ed26d00388999531da4da0071266acc7b931400e25000026ec4ad003864dd49b592ba0071137aa6cb4af400e226f54d9695e801c49beb362e56d0038944f289db131400e213c527564c6801c44f0a9d6d30d003889e153ada61a0071278aceab985400e25140a27ec4dd0038850149fd936a0071140aa7eb4d9400e228154fd69b2801c4a06b3f2e6c50038945128a1b13d400e2145528764f2801c4516aa1ed3c500388a2d543da78a007128b2d0eb9df400e2514aa292c50d003885294a45942a007114a2a91b509400e229455236a12801c4a52b48ae83d00389453a8a6b149400e214f529b6522801c453caa6ad48500388a7954d5a90a007129ead35ba3f400e25154a2a6c53d003885514a9594ea0071154aaa5b53b400e22a9554b6a76801c4aa4b52ae9cd0038945628abb155400e215952af6556801c4566aabed55500388acd557daaaa00712b3ad5fbaa7400e2500002bd45750038657d4aed95ca007115f2abab571400e22be55756ae2801c4afab5d6eb7d0038940000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080000000b13400e1500000000585003840000000160a007080000000585400e100000000b0a801c200000002c4d0038540000000161400e100000000582801c2000000016150038400000002c2a007080005896b07400e1d00000000585003840000000160a007080000000585400e100000000b0a801c20001625aba50038740000000161400e100000000582801c2000000016150038400000002c2a007080005806acf400e1d

def row14 (index : ℕ) : List (List ℕ) :=
  if index < 123 then
    let packedCell := Nat.shiftRight row14PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row15PackedData : ℕ := 0x146c23500386000051588da0070ca2a944b237400e21455289646e801c4516aa26d1b5003894000051b08f400e18000147623a801c3000051ec8ed003860000a3d91da0070d47aa8eb475400e25000014ac245003862954525890a00710a52949b241400e214a52936482801c4528aa4ad1fd00389429a852b091400e20a6514b6246801c4298a52ec915003885314a5d922a007114caa97b489400e25000014ec24d00386000053d892a0070ca7a94eb249400e214f529d6492801c453caa72d24d003894000054b093400e18000151624e801c30000546c93d003860000a8d927a0070d51aaa2b49d400e250aaa152c255003882a9454d895a00710aa2953b255400e215452a764aa801c4552aa9ed29d003894000055b097400e18000157625a801c32aea55ac9650038855d4ab592ca00711572aacb4b1400e25000015ac25d003860000565897a0070caca958b25f400e215952b164be801c4566aac6d2f50038942ba856b099400e20ae515b6266801c42b8a56ec98d003885714add931a007115caab7b4c7400e25000015ec26d00386000057d89aa0070cafa95eb269400e215f52bd64d2801c457caaf2d345003894000058b09b400e18b15161626e801c42c4a586c9bd003885894b0d937a00711622ac2b4dd400e250000166c275003862c9458d89da00710b2a963b275400e216552c764ea801c4594ab1ed3a5003894000059b09f400e18000167627a801c32cea59ac9ed0038859d4b3593da0071167aacdb4f3400e25000016ac285003862d545a58a0a00710b52969b281400e216a52d36502801c45aaab4ed3fd00389400005bb0a1400e1800016d6286801c32daa5b2ca1d003885b54b65943a007116daad9b50b400e250b8a16ec28d003882e145bd8a3a00710b8296fb28d400e217052df651a801c45c2ab7ed4650038942ea85cb0a5400e20ba51736292801c42e8a5caca4d003885d14b95949a00711742ae5b525400e250000176c29d0038600005dd8a6a0070cbba976b299400e217752ed6532801c45dcabb2d4c500389400005eb0a9400e18bd5179629e801c42f4a5e6ca7d003885e94bcd94fa007117a2af2b53f400e25000017ec2a50038600005f58a9a0070cbea97cb2a7400e217d52f9654e801c45f6abe2d52d00389430285fb0ab400e20c0517f62ae801c4302a5fecab5003886054bfd956a00711812affb559400e250c2a182c2b500388309460d8ada00710c22983b2b5400e21845307656a801c4610ac1ad59d003894000061b0af400e1800018762ba801c330ea61acaed0038861d4c3595da0071187ab0db575400e25000018ac2c50038631546258b0a00710c5a989b2c3400e218b53136586801c462cac4ed60d003894000063b0b3400e18c7518d62ca801c431ca636cb25003886394c6d964a007118eab1bb591400e250000192c2d50038632546458b4a00710c92991b2d1400e2192532365a2801c464aac8ad685003894000065b0b7400e18cb519562da801c432ca652cb65003886594ca596ca00711962b29b5b1400e25000019ac2e50038600006658b8a0070ccca998b2e1400e2199533165c2801c4666acc6d6fd003894000067b0bb400e1800019d62ea801c333aa672cba5003886754ce5974a007119dab38b5cf400e2500001a2c2f50038600006858bca0070cd0a9a0b2f1400e21a1534165e2801c4686ad02d77d003894000069b0bf400e180001a562fa801c334aa692cbe5003886954d2597ca00711a5ab48b5f1400e2500001aac3050038600006a58c0a0070cd4a9a8b301400e21a953516602801c46a6ad42d80500389400006bb0c3400e180001ad630a801c335aa6b2cc2d003886b54d65985a00711adab58b613400e2500001b2c3150038636546c58c4a00710d929b0b313400e21b253616626801c46c8ad82d89500389400006db0c7400e18db51b5631e801c436ca6d2cc75003886d94da598ea00711b62b69b637400e2500001bac3250038637546e58c9a00710dd29b9b325400e21ba5373664a801c46eaadcad92500389400006fb0cb400e18df51bd632e801c437ea6f6ccbd003886fd4ded997a00711bf2b7bb65d400e2500001c2c33d00386000070d8cea0070ce1a9c2b339400e21c353856672801c470eae12d9c5003894392871b0d1400e20e451c76342801c4390a71acd0d003887214e359a1a00711c82b8db685400e250e6a1cac34d00388399472d8d3a00710e6a9cbb34d400e21cd5397669a801c4734ae5ada65003894000074b0d5400e18e951d16356801c43a4a742cd5d003887494e859aba00711d22ba0b6ad400e2500001d6c365003863ad47558d8a00710eba9d5b363400e21d753ab66c6801c475caeaadb0d0038943ba876b0db400e20ee51db636e801c43b8a76acdb5003887714ed59b6a00711dc2bb4b6d9400e250f0a1dec37d003883c1477d8dea00710f0a9dfb379400e21e153bf66f2801c4784aefadbbd003894000079b0e1400e18f351e56386801c43cca792ce15003887994f259c2a00711e6abc9b707400e2500001eac395003863d547a58e4a00710f5a9e9b391400e21eb53d36722801c47aeaf4edc7d0038943e287bb0e7400e20f851ef639e801c43e2a7bece75003887c54f7d9cea00711f12bdeb737400e2500001f6c3ad003863ed47d58eaa00710fba9f4b3a9400e21f753e96752801c47dcafa6dd450038943fa87eb0ed400e20fe51fb63b6801c43f8a7eacedd003887f14fd59dba00711fcabf5b76b400e250000202c3c50038640548058f0a00711012a00b3c3400e220254016786801c480ab006de15003894412881b0f5400e2104520763d2801c4410a81acf450038882150359e8a0071208ac0db7a1400e25000020ec3dd0038641d48358f7a0071107aa0cb3df400e220f541967be801c483cb066def500389442a884b0fb400e210a521363ee801c442aa84ecfb500388855509d9f6a00712152c25b7d9400e25000021ac3fd0038643548658ffa007110daa19b3fd400e221b543367fa801c486eb0cadfdd003894000088b103400e19115221640e801c4444a882d035003888895105a06a0071222ac40b817400e25114a226c41d00388451489d907a0071114aa26b41b400e2229544d6836801c48a4b136e0d500389446288bb10b400e2118522d642e801c4460a8b6d0b5003888c1516da16a00712302c5bb857400e250000236c43d0038646d48d590fa007111baa34b43d400e22375469687a801c48deb1a6e1e500389400008fb113400e191f523d644e801c447ea8f2d13d003888fd51e5a27a007123f2c78b89b400e25122a242c4650038848d490d918a00711232a43b461400e2246548768c2801c491ab21ee2fd00389449a892b11d400e2127524b6472801c449ca92ed1cd00388939525da39a007124e2c96b8e3400e2512aa252c485003884ad494d921a007112b2a53b487400e225654a7690e801c4958b29ae42d0038944ba896b127400e212f525b649a801c44bca96ed26d0038897952dda4da007125eacb6b931400e25132a262c4ad003884cd498d92ba00711332a63b4af400e226654c7695e801c499ab31ee56d00389400009bb131400e1937526d64c6801c44dea9b2d30d003889bd5365a61a007126facd8b985400e2513ca276c4dd003884f149d5936a007113c2a75b4d9400e227854eb69b2801c49e2b3aae6c500389450289fb13d400e2140527f64f2801c4502a9fad3c500388a0553f5a78a0071281acfcb9df400e250000289450d003865154a1d942a0071145aa87b509400e228b550f6a12801c4a2cb43ae83d0038940000000149400e10000292a522801c3526aa46d48500388a4d548da90a0071294ad22ba3f400e2500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e1500000000525003840000000149a007080000000527400e100000000a4e801c2000000029550038540000000149400e100000000526801c20000000149d003840000000293a007080000000a55400e15

def row15 (index : ℕ) : List (List ℕ) :=
  if index < 122 then
    let packedCell := Nat.shiftRight row15PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row16PackedData : ℕ := 0x51b08f400e18000145623a801c328aa512c8ed003885154a2591da0071145aa89b475400e250000146c24500386000051d890a0070c000147b241400e1800028f6482801c351eaa3ad1fd003894000052b091400e18a551496246801c4294a526c915003885294a4d922a007114a2a92b489400e250a6a14ac24d00388299452d892a00710a6294bb249400e214c52976492801c4532aa5ed24d003894000053b093400e1800014f624e801c329ea53ac93d0038853d4a75927a007114f2a9cb49d400e250000152c255003860000545895a0070c000151b255400e180002a364aa801c3546aa8ad29d0038942aa854b097400e20aa5153625a801c42a8a54ec965003885514a9d92ca0071154aaa7b4b1400e250000156c25d00386000055d897a0070caba956b25f400e215752ad64be801c455caab2d2f5003894000056b099400e180001596266801c32b2a562c98d003885654ac5931a0071159aab1b4c7400e250aea15ac26d003882b9456d89aa00710ae295bb269400e215c52b764d2801c4572aaded345003894000057b09b400e1800015f626e801c32bea57ac9bd0038857d4af5937a007115f2abcb4dd400e250000162c275003862c5458589da00710b12961b275400e216252c364ea801c4588ab0ad3a5003894000059b09f400e18b25163627a801c42caa58ec9ed003885954b1d93da00711652ac7b4f3400e250000166c28500386000059d8a0a0070cb3a966b281400e216752cd6502801c459eab36d3fd00389400005ab0a1400e18b551696286801c42d4a5a6ca1d003885a94b4d943a007116aaad3b50b400e25000016ec28d0038600005b58a3a0070cb6a96cb28d400e216d52d9651a801c45b6ab66d4650038942e285bb0a5400e20b8516f6292801c42e0a5beca4d003885c14b7d949a0071170aadfb525400e250baa172c29d003882e945cd8a6a00710ba2972b299400e217452e56532801c45d0ab96d4c500389400005db0a9400e18000177629e801c32eea5daca7d003885dd4bb594fa00711772aecb53f400e25000017ac2a5003862f545e58a9a00710bd2979b2a7400e217a52f3654e801c45e8abcad52d00389400005fb0ab400e1800017d62ae801c32faa5f2cab5003885f54be5956a007117daaf8b559400e250c0a17ec2b50038830145fd8ada00710c0a97fb2b5400e218152ff656a801c4604abfed59d00389430a860b0af400e20c2518362ba801c4308a60ecaed003886114c1d95da00711842b06b575400e250000186c2c500386000061d8b0a0070cc3a986b2c3400e2187530d6586801c461eac36d60d003894000062b0b3400e18c5518962ca801c4316a626cb250038862d4c4d964a007118b2b13b591400e25000018ec2d50038631d46358b4a00710c7298db2d1400e218e531b65a2801c463aac6ed685003894000064b0b7400e18c9519162da801c4324a646cb65003886494c8d96ca0071192ab22b5b1400e250000196c2e50038632d46558b8a00710cb2994b2e1400e2196532965c2801c4658aca6d6fd003894000066b0bb400e1800019962ea801c3332a662cba5003886654cc5974a0071199ab31b5cf400e25000019ec2f50038600006758bca0070ccea99cb2f1400e219d533965e2801c4676ace2d77d003894000068b0bf400e180001a162fa801c3342a682cbe5003886854d0597ca00711a1ab40b5f1400e2500001a6c3050038600006958c0a0070cd2a9a4b301400e21a553496602801c4696ad22d80500389400006ab0c3400e180001a9630a801c3352a6a2cc2d003886a54d45985a00711a9ab50b613400e2500001aec3150038600006b58c4a0070cd6a9acb313400e21ad53596626801c46b6ad62d89500389400006cb0c7400e18d951b1631e801c4364a6c2cc75003886c94d8598ea00711b22b60b637400e2500001b6c3250038636d46d58c9a00710db29b4b325400e21b65369664a801c46d8ada6d92500389400006eb0cb400e18dd51b9632e801c4374a6e6ccbd003886e94dcd997a00711baab72b65d400e2500001bec33d0038637d46f58cea00710dfa9bdb339400e21bf537b6672801c46fcadeed9c5003894000070b0d1400e180001c36342801c3386a70acd0d0038870d4e159a1a00711c3ab84b685400e250e4a1c6c34d00388391471d8d3a00710e429c6b34d400e21c8538d669a801c4720ae36da6500389439a872b0d5400e20e651cb6356801c439aa72ecd5d003887354e5d9aba00711cd2b96b6ad400e2500001d2c365003863a547458d8a00710e929d0b363400e21d253a166c6801c4748ae82db0d003894000075b0db400e18eb51d5636e801c43aea756cdb50038875d4ead9b6a00711d72baab6d9400e250eea1dac37d003883b9476d8dea00710ee29dab379400e21dc53b566f2801c4770aed2dbbd0038943c2877b0e1400e20f051df6386801c43c2a77ece15003887854efd9c2a00711e12bbeb707400e2500001e6c395003863cd47958e4a00710f329e4b391400e21e653c96722801c479aaf26dc7d00389400007ab0e7400e18f551e9639e801c43d6a7a6ce75003887ad4f4d9cea00711ebabd3b737400e250f8a1eec3ad003883e147bd8eaa00710f8a9efb3a9400e21f153df6752801c47c4af7add4500389400007db0ed400e18fb51f563b6801c43eea7d2cedd003887dd4fa59dba00711f72be9b76b400e250fea1fac3c5003883f947ed8f0a00710fe29fab3c3400e21fc53f56786801c47f2afd6de15003894000080b0f5400e1901520163d2801c4404a802cf450038880950059e8a0071202ac01b7a1400e25104a206c3dd00388411481d8f7a00711042a06b3df400e2208540d67be801c4822b036def5003894000083b0fb400e1907520d63ee801c441ea832cfb50038883d50659f6a007120f2c19b7d9400e2510aa212c3fd00388429484d8ffa007110aaa13b3fd400e2215542767fa801c4854b096dfdd003894000086b103400e190d5219640e801c4436a866d0350038886d50cda06a007121bac32b817400e250000222c41d003864454885907a00711112a20b41b400e222254416836801c488ab102e0d5003894452889b10b400e21145227642e801c4452a89ad0b5003888a55135a16a00712292c4db857400e25118a22ec43d0038846148b590fa00711182a2db43d400e2230545b687a801c48c0b16ee1e500389400008db113400e191b5235644e801c446ea8d2d13d003888dd51a5a27a0071237ac69b89b400e25000023ec4650038647d48f5918a007111faa3cb461400e223f547968c2801c48fcb1e2e2fd00389448a890b11d400e212352436472801c448ca90ed1cd00388919521da39a0071246ac87b8e3400e25126a24ac4850038849d492d921a00711272a4bb487400e224e5497690e801c4938b25ae42d0038944aa894b127400e212b5253649a801c44aca94ed26d00388959529da4da00712562ca6b931400e2512ea25ac4ad003884bd496d92ba007112f2a5bb4af400e225e54b7695e801c497ab2dae56d0038940000995131400e18000266a4c6801c34cca98ed30d00388999531da61a0071266acc7b985400e25000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15000000004d5003840000000134a0070800000004d5400e1000000009aa801c2000000026c50038540000000135400e1000000004d2801c20000000135500384000000026aa0070800000009b1400e15

def row16 (index : ℕ) : List (List ℕ) :=
  if index < 121 then
    let packedCell := Nat.shiftRight row16PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row17PackedData : ℕ := 0x146c245003860000515890a0070ca2a944b241400e214552896482801c4516aa26d1fd003894000051b091400e180001476246801c3000051ec915003860000a3d922a0070d47aa8eb489400e25000014ac24d003862954525892a00710a52949b249400e214a52936492801c4528aa4ad24d00389429a852b093400e20a6514b624e801c4298a52ec93d003885314a5d927a007114caa97b49d400e25000014ec25500386000053d895a0070ca7a94eb255400e214f529d64aa801c453caa72d29d003894000054b097400e18000151625a801c30000546c965003860000a8d92ca0070d51aaa2b4b1400e250aaa152c25d003882a9454d897a00710aa2953b25f400e215452a764be801c4552aa9ed2f5003894000055b099400e180001576266801c32aea55ac98d0038855d4ab5931a00711572aacb4c7400e25000015ac26d00386000056589aa0070caca958b269400e215952b164d2801c4566aac6d3450038942ba856b09b400e20ae515b626e801c42b8a56ec9bd003885714add937a007115caab7b4dd400e25000015ec27500386000057d89da0070cafa95eb275400e215f52bd64ea801c457caaf2d3a5003894000058b09f400e18b15161627a801c42c4a586c9ed003885894b0d93da00711622ac2b4f3400e250000166c285003862c9458d8a0a00710b2a963b281400e216552c76502801c4594ab1ed3fd003894000059b0a1400e180001676286801c32cea59aca1d0038859d4b35943a0071167aacdb50b400e25000016ac28d003862d545a58a3a00710b52969b28d400e216a52d3651a801c45aaab4ed46500389400005bb0a5400e1800016d6292801c32daa5b2ca4d003885b54b65949a007116daad9b525400e250b8a16ec29d003882e145bd8a6a00710b8296fb299400e217052df6532801c45c2ab7ed4c50038942ea85cb0a9400e20ba5173629e801c42e8a5caca7d003885d14b9594fa00711742ae5b53f400e250000176c2a50038600005dd8a9a0070cbba976b2a7400e217752ed654e801c45dcabb2d52d00389400005eb0ab400e18bd517962ae801c42f4a5e6cab5003885e94bcd956a007117a2af2b559400e25000017ec2b50038600005f58ada0070cbea97cb2b5400e217d52f9656a801c45f6abe2d59d00389430285fb0af400e20c0517f62ba801c4302a5fecaed003886054bfd95da00711812affb575400e250c2a182c2c500388309460d8b0a00710c22983b2c3400e218453076586801c4610ac1ad60d003894000061b0b3400e1800018762ca801c330ea61acb250038861d4c35964a0071187ab0db591400e25000018ac2d50038631546258b4a00710c5a989b2d1400e218b531365a2801c462cac4ed685003894000063b0b7400e18c7518d62da801c431ca636cb65003886394c6d96ca007118eab1bb5b1400e250000192c2e50038632546458b8a00710c92991b2e1400e2192532365c2801c464aac8ad6fd003894000065b0bb400e18cb519562ea801c432ca652cba5003886594ca5974a00711962b29b5cf400e25000019ac2f50038600006658bca0070ccca998b2f1400e2199533165e2801c4666acc6d77d003894000067b0bf400e1800019d62fa801c333aa672cbe5003886754ce597ca007119dab38b5f1400e2500001a2c3050038600006858c0a0070cd0a9a0b301400e21a153416602801c4686ad02d805003894000069b0c3400e180001a5630a801c334aa692cc2d003886954d25985a00711a5ab48b613400e2500001aac3150038600006a58c4a0070cd4a9a8b313400e21a953516626801c46a6ad42d89500389400006bb0c7400e180001ad631e801c335aa6b2cc75003886b54d6598ea00711adab58b637400e2500001b2c3250038636546c58c9a00710d929b0b325400e21b25361664a801c46c8ad82d92500389400006db0cb400e18db51b5632e801c436ca6d2ccbd003886d94da5997a00711b62b69b65d400e2500001bac33d0038637546e58cea00710dd29b9b339400e21ba53736672801c46eaadcad9c500389400006fb0d1400e18df51bd6342801c437ea6f6cd0d003886fd4ded9a1a00711bf2b7bb685400e2500001c2c34d00386000070d8d3a0070ce1a9c2b34d400e21c35385669a801c470eae12da65003894392871b0d5400e20e451c76356801c4390a71acd5d003887214e359aba00711c82b8db6ad400e250e6a1cac36500388399472d8d8a00710e6a9cbb363400e21cd539766c6801c4734ae5adb0d003894000074b0db400e18e951d1636e801c43a4a742cdb5003887494e859b6a00711d22ba0b6d9400e2500001d6c37d003863ad47558dea00710eba9d5b379400e21d753ab66f2801c475caeaadbbd0038943ba876b0e1400e20ee51db6386801c43b8a76ace15003887714ed59c2a00711dc2bb4b707400e250f0a1dec395003883c1477d8e4a00710f0a9dfb391400e21e153bf6722801c4784aefadc7d003894000079b0e7400e18f351e5639e801c43cca792ce75003887994f259cea00711e6abc9b737400e2500001eac3ad003863d547a58eaa00710f5a9e9b3a9400e21eb53d36752801c47aeaf4edd450038943e287bb0ed400e20f851ef63b6801c43e2a7becedd003887c54f7d9dba00711f12bdeb76b400e2500001f6c3c5003863ed47d58f0a00710fba9f4b3c3400e21f753e96786801c47dcafa6de150038943fa87eb0f5400e20fe51fb63d2801c43f8a7eacf45003887f14fd59e8a00711fcabf5b7a1400e250000202c3dd0038640548058f7a00711012a00b3df400e2202540167be801c480ab006def5003894412881b0fb400e2104520763ee801c4410a81acfb50038882150359f6a0071208ac0db7d9400e25000020ec3fd0038641d48358ffa0071107aa0cb3fd400e220f541967fa801c483cb066dfdd00389442a884b103400e210a5213640e801c442aa84ed03500388855509da06a00712152c25b817400e25000021ac41d003864354865907a007110daa19b41b400e221b54336836801c486eb0cae0d5003894000088b10b400e19115221642e801c4444a882d0b5003888895105a16a0071222ac40b857400e25114a226c43d00388451489d90fa0071114aa26b43d400e2229544d687a801c48a4b136e1e500389446288bb113400e2118522d644e801c4460a8b6d13d003888c1516da27a00712302c5bb89b400e250000236c4650038646d48d5918a007111baa34b461400e2237546968c2801c48deb1a6e2fd00389400008fb11d400e191f523d6472801c447ea8f2d1cd003888fd51e5a39a007123f2c78b8e3400e2500002454485003860000912921a0070c0002455487400e1800048aa90e801c391ab21ee42d0038940000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e150000000048d003840000000122a00708000000048b400e100000000916801c20000000247d0038540000000123400e10000000048a801c20000000122d003840000000245a00708000000091f400e15

def row17 (index : ℕ) : List (List ℕ) :=
  if index < 120 then
    let packedCell := Nat.shiftRight row17PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row18PackedData : ℕ := 0x51b091400e180001456246801c328aa512c915003885154a25922a0071145aa89b489400e250000146c24d00386000051d892a0070c000147b249400e1800028f6492801c351eaa3ad24d003894000052b093400e18a55149624e801c4294a526c93d003885294a4d927a007114a2a92b49d400e250a6a14ac25500388299452d895a00710a6294bb255400e214c529764aa801c4532aa5ed29d003894000053b097400e1800014f625a801c329ea53ac9650038853d4a7592ca007114f2a9cb4b1400e250000152c25d003860000545897a0070c000151b25f400e180002a364be801c3546aa8ad2f50038942aa854b099400e20aa51536266801c42a8a54ec98d003885514a9d931a0071154aaa7b4c7400e250000156c26d00386000055d89aa0070caba956b269400e215752ad64d2801c455caab2d345003894000056b09b400e18000159626e801c32b2a562c9bd003885654ac5937a0071159aab1b4dd400e250aea15ac275003882b9456d89da00710ae295bb275400e215c52b764ea801c4572aaded3a5003894000057b09f400e1800015f627a801c32bea57ac9ed0038857d4af593da007115f2abcb4f3400e250000162c285003862c545858a0a00710b12961b281400e216252c36502801c4588ab0ad3fd003894000059b0a1400e18b251636286801c42caa58eca1d003885954b1d943a00711652ac7b50b400e250000166c28d00386000059d8a3a0070cb3a966b28d400e216752cd651a801c459eab36d46500389400005ab0a5400e18b551696292801c42d4a5a6ca4d003885a94b4d949a007116aaad3b525400e25000016ec29d0038600005b58a6a0070cb6a96cb299400e216d52d96532801c45b6ab66d4c50038942e285bb0a9400e20b8516f629e801c42e0a5beca7d003885c14b7d94fa0071170aadfb53f400e250baa172c2a5003882e945cd8a9a00710ba2972b2a7400e217452e5654e801c45d0ab96d52d00389400005db0ab400e1800017762ae801c32eea5dacab5003885dd4bb5956a00711772aecb559400e25000017ac2b5003862f545e58ada00710bd2979b2b5400e217a52f3656a801c45e8abcad59d00389400005fb0af400e1800017d62ba801c32faa5f2caed003885f54be595da007117daaf8b575400e250c0a17ec2c50038830145fd8b0a00710c0a97fb2c3400e218152ff6586801c4604abfed60d00389430a860b0b3400e20c2518362ca801c4308a60ecb25003886114c1d964a00711842b06b591400e250000186c2d500386000061d8b4a0070cc3a986b2d1400e2187530d65a2801c461eac36d685003894000062b0b7400e18c5518962da801c4316a626cb650038862d4c4d96ca007118b2b13b5b1400e25000018ec2e50038631d46358b8a00710c7298db2e1400e218e531b65c2801c463aac6ed6fd003894000064b0bb400e18c9519162ea801c4324a646cba5003886494c8d974a0071192ab22b5cf400e250000196c2f50038632d46558bca00710cb2994b2f1400e2196532965e2801c4658aca6d77d003894000066b0bf400e1800019962fa801c3332a662cbe5003886654cc597ca0071199ab31b5f1400e25000019ec3050038600006758c0a0070ccea99cb301400e219d53396602801c4676ace2d805003894000068b0c3400e180001a1630a801c3342a682cc2d003886854d05985a00711a1ab40b613400e2500001a6c3150038600006958c4a0070cd2a9a4b313400e21a553496626801c4696ad22d89500389400006ab0c7400e180001a9631e801c3352a6a2cc75003886a54d4598ea00711a9ab50b637400e2500001aec3250038600006b58c9a0070cd6a9acb325400e21ad5359664a801c46b6ad62d92500389400006cb0cb400e18d951b1632e801c4364a6c2ccbd003886c94d85997a00711b22b60b65d400e2500001b6c33d0038636d46d58cea00710db29b4b339400e21b653696672801c46d8ada6d9c500389400006eb0d1400e18dd51b96342801c4374a6e6cd0d003886e94dcd9a1a00711baab72b685400e2500001bec34d0038637d46f58d3a00710dfa9bdb34d400e21bf537b669a801c46fcadeeda65003894000070b0d5400e180001c36356801c3386a70acd5d0038870d4e159aba00711c3ab84b6ad400e250e4a1c6c36500388391471d8d8a00710e429c6b363400e21c8538d66c6801c4720ae36db0d00389439a872b0db400e20e651cb636e801c439aa72ecdb5003887354e5d9b6a00711cd2b96b6d9400e2500001d2c37d003863a547458dea00710e929d0b379400e21d253a166f2801c4748ae82dbbd003894000075b0e1400e18eb51d56386801c43aea756ce150038875d4ead9c2a00711d72baab707400e250eea1dac395003883b9476d8e4a00710ee29dab391400e21dc53b56722801c4770aed2dc7d0038943c2877b0e7400e20f051df639e801c43c2a77ece75003887854efd9cea00711e12bbeb737400e2500001e6c3ad003863cd47958eaa00710f329e4b3a9400e21e653c96752801c479aaf26dd4500389400007ab0ed400e18f551e963b6801c43d6a7a6cedd003887ad4f4d9dba00711ebabd3b76b400e250f8a1eec3c5003883e147bd8f0a00710f8a9efb3c3400e21f153df6786801c47c4af7ade1500389400007db0f5400e18fb51f563d2801c43eea7d2cf45003887dd4fa59e8a00711f72be9b7a1400e250fea1fac3dd003883f947ed8f7a00710fe29fab3df400e21fc53f567be801c47f2afd6def5003894000080b0fb400e1901520163ee801c4404a802cfb50038880950059f6a0071202ac01b7d9400e25104a206c3fd00388411481d8ffa00711042a06b3fd400e2208540d67fa801c4822b036dfdd003894000083b103400e1907520d640e801c441ea832d0350038883d5065a06a007120f2c19b817400e2510aa212c41d00388429484d907a007110aaa13b41b400e221554276836801c4854b096e0d5003894000086b10b400e190d5219642e801c4436a866d0b50038886d50cda16a007121bac32b857400e250000222c43d00386445488590fa00711112a20b43d400e22225441687a801c488ab102e1e50038940000000113400e10000000044a801c20000000112d003840000000225a0070800044e589b400e1d0000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e150000000044d003840000000112a00708000000044b400e100000000896801c2000000022750038540000000113400e10000000044a801c20000000112d003840000000225a00708000000089d400e15

def row18 (index : ℕ) : List (List ℕ) :=
  if index < 119 then
    let packedCell := Nat.shiftRight row18PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row19PackedData : ℕ := 0x146c24d003860000515892a0070ca2a944b249400e214552896492801c4516aa26d24d003894000051b093400e18000147624e801c3000051ec93d003860000a3d927a0070d47aa8eb49d400e25000014ac255003862954525895a00710a52949b255400e214a529364aa801c4528aa4ad29d00389429a852b097400e20a6514b625a801c4298a52ec965003885314a5d92ca007114caa97b4b1400e25000014ec25d00386000053d897a0070ca7a94eb25f400e214f529d64be801c453caa72d2f5003894000054b099400e180001516266801c30000546c98d003860000a8d931a0070d51aaa2b4c7400e250aaa152c26d003882a9454d89aa00710aa2953b269400e215452a764d2801c4552aa9ed345003894000055b09b400e18000157626e801c32aea55ac9bd0038855d4ab5937a00711572aacb4dd400e25000015ac27500386000056589da0070caca958b275400e215952b164ea801c4566aac6d3a50038942ba856b09f400e20ae515b627a801c42b8a56ec9ed003885714add93da007115caab7b4f3400e25000015ec28500386000057d8a0a0070cafa95eb281400e215f52bd6502801c457caaf2d3fd003894000058b0a1400e18b151616286801c42c4a586ca1d003885894b0d943a00711622ac2b50b400e250000166c28d003862c9458d8a3a00710b2a963b28d400e216552c7651a801c4594ab1ed465003894000059b0a5400e180001676292801c32cea59aca4d0038859d4b35949a0071167aacdb525400e25000016ac29d003862d545a58a6a00710b52969b299400e216a52d36532801c45aaab4ed4c500389400005bb0a9400e1800016d629e801c32daa5b2ca7d003885b54b6594fa007116daad9b53f400e250b8a16ec2a5003882e145bd8a9a00710b8296fb2a7400e217052df654e801c45c2ab7ed52d0038942ea85cb0ab400e20ba517362ae801c42e8a5cacab5003885d14b95956a00711742ae5b559400e250000176c2b50038600005dd8ada0070cbba976b2b5400e217752ed656a801c45dcabb2d59d00389400005eb0af400e18bd517962ba801c42f4a5e6caed003885e94bcd95da007117a2af2b575400e25000017ec2c50038600005f58b0a0070cbea97cb2c3400e217d52f96586801c45f6abe2d60d00389430285fb0b3400e20c0517f62ca801c4302a5fecb25003886054bfd964a00711812affb591400e250c2a182c2d500388309460d8b4a00710c22983b2d1400e2184530765a2801c4610ac1ad685003894000061b0b7400e1800018762da801c330ea61acb650038861d4c3596ca0071187ab0db5b1400e25000018ac2e50038631546258b8a00710c5a989b2e1400e218b531365c2801c462cac4ed6fd003894000063b0bb400e18c7518d62ea801c431ca636cba5003886394c6d974a007118eab1bb5cf400e250000192c2f50038632546458bca00710c92991b2f1400e2192532365e2801c464aac8ad77d003894000065b0bf400e18cb519562fa801c432ca652cbe5003886594ca597ca00711962b29b5f1400e25000019ac3050038600006658c0a0070ccca998b301400e219953316602801c4666acc6d805003894000067b0c3400e1800019d630a801c333aa672cc2d003886754ce5985a007119dab38b613400e2500001a2c3150038600006858c4a0070cd0a9a0b313400e21a153416626801c4686ad02d895003894000069b0c7400e180001a5631e801c334aa692cc75003886954d2598ea00711a5ab48b637400e2500001aac3250038600006a58c9a0070cd4a9a8b325400e21a95351664a801c46a6ad42d92500389400006bb0cb400e180001ad632e801c335aa6b2ccbd003886b54d65997a00711adab58b65d400e2500001b2c33d0038636546c58cea00710d929b0b339400e21b253616672801c46c8ad82d9c500389400006db0d1400e18db51b56342801c436ca6d2cd0d003886d94da59a1a00711b62b69b685400e2500001bac34d0038637546e58d3a00710dd29b9b34d400e21ba5373669a801c46eaadcada6500389400006fb0d5400e18df51bd6356801c437ea6f6cd5d003886fd4ded9aba00711bf2b7bb6ad400e2500001c2c36500386000070d8d8a0070ce1a9c2b363400e21c3538566c6801c470eae12db0d003894392871b0db400e20e451c7636e801c4390a71acdb5003887214e359b6a00711c82b8db6d9400e250e6a1cac37d00388399472d8dea00710e6a9cbb379400e21cd539766f2801c4734ae5adbbd003894000074b0e1400e18e951d16386801c43a4a742ce15003887494e859c2a00711d22ba0b707400e2500001d6c395003863ad47558e4a00710eba9d5b391400e21d753ab6722801c475caeaadc7d0038943ba876b0e7400e20ee51db639e801c43b8a76ace75003887714ed59cea00711dc2bb4b737400e250f0a1dec3ad003883c1477d8eaa00710f0a9dfb3a9400e21e153bf6752801c4784aefadd45003894000079b0ed400e18f351e563b6801c43cca792cedd003887994f259dba00711e6abc9b76b400e2500001eac3c5003863d547a58f0a00710f5a9e9b3c3400e21eb53d36786801c47aeaf4ede150038943e287bb0f5400e20f851ef63d2801c43e2a7becf45003887c54f7d9e8a00711f12bdeb7a1400e2500001f6c3dd003863ed47d58f7a00710fba9f4b3df400e21f753e967be801c47dcafa6def50038943fa87eb0fb400e20fe51fb63ee801c43f8a7eacfb5003887f14fd59f6a00711fcabf5b7d9400e250000202c3fd0038640548058ffa00711012a00b3fd400e2202540167fa801c480ab006dfdd0038940000824103400e18000208840e801c300008215035003860001042a06a0070e08ac0db817400e2500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e1500000000415003840000000104a007080000000411400e100000000822801c2000000020a50038540000000105400e100000000412801c200000001045003840000000208a007080000000829400e15

def row19 (index : ℕ) : List (List ℕ) :=
  if index < 118 then
    let packedCell := Nat.shiftRight row19PackedData (index * 318)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 32767)) 15 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 63 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row20PackedData : ℕ := 0x146c49a00e18000515927401c3515544b49e80388a2aa89693d007128b5a26e4ea00e25000051b12a8038600014764ad0070c00051ed2aa00e18000a3da55401c3a3d68eb94e80389400014ac4ba00e194aa52592d401c4529549b4b280388a52a93696500712945a4ae58a00e2514d452b12e8038853294b64bd007114c552ed2fa00e2298aa5da5f401c4a65697b97a80389400014ec4ca00e1800053d933401c353d54eb4c680388a7aa9d698d007129e5a72e63a00e25000054b1368038600015164d50070c000546d34a00e18000a8da69401c3a8d6a2b9a2803894555152c4da00e2154a54d937401c4551553b4de80388aa2aa769bd00712a95a9ee6ea00e25000055b13a8038600015764ed0070d57555ad3aa00e22aeaab5a75401c4ab96acb9d280389400015ac4fa00e1800056593d401c3565558b4f680388acaab169ed00712b35ac6e79a00e2515d456b1428038857295b6505007115c556ed40a00e22b8aadda81401c4ae56b7b9fe80389400015ec50a00e1800057d943401c357d55eb50e80388afaabd6a1d00712be5af2e85a00e25000058b1468038658a961651d00711625586d46a00e22c4ab0da8d401c4b116c2ba32803894000166c52a00e1964a58d949401c4595563b52680388b2aac76a4d00712ca5b1ee92a00e25000059b14e8038600016765350070d67559ad4ca00e22ceab35a99401c4b3d6cdba6280389400016ac54a00e196aa5a594f401c45a9569b53e80388b52ad36a7d00712d55b4ee9fa00e2500005bb1528038600016d654d0070d6d55b2d53a00e22daab65aa7401c4b6d6d9ba968038945c516ec55a00e2170a5bd957401c45c156fb55a80388b82adf6ab500712e15b7eeaca00e2517545cb15a803885d2973656d007117455cad5aa00e22e8ab95ab5401c4ba16e5bace803894000176c57a00e180005dd95d401c35dd576b57680388bbaaed6aed00712ee5bb2ebaa00e2500005eb162803865ea9796585007117a55e6d61a00e22f4abcdac3401c4bd16f2bb0680389400017ec59a00e180005f5965401c35f557cb59280388beaaf96b2500712fb5be2ec8a00e2518145fb16a8038860297f65a5007118155fed68a00e2302abfdad1401c4c096ffbb42803894615182c5ba00e2184a60d96d401c4611583b5b280388c22b076b6500713085c1aed8a00e25000061b1728038600018765c50070d87561ad70a00e230eac35ae1401c4c3d70dbb7e80389400018ac5da00e198aa625975401c462d589b5d280388c5ab136ba500713165c4eee7a00e25000063b17a8038663a98d65e5007118e5636d78a00e231cac6daf1401c4c7571bbbbe803894000192c5fa00e1992a64597d401c4649591b5f280388c92b236be500713255c8aef8a00e25000065b1828038665a995660500711965652d80a00e232caca5b01401c4cb1729bc0280389400019ac61a00e18000665985401c3665598b61680388ccab316c2d00713335cc6f09a00e25000067b18a8038600019d66250070d9d5672d89a00e233aace5b13401c4ced738bc4a8038940001a2c63a00e1800068598f401c36855a0b63a80388d0ab416c7500713435d02f1ba00e25000069b192803860001a5664d0070da55692d92a00e234aad25b25401c4d2d748bc928038940001aac65a00e180006a5997401c36a55a8b65e80388d4ab516cbd00713535d42f2ea00e2500006bb19e803860001ad66750070dad56b2d9ca00e235aad65b39401c4d6d758bce28038940001b2c68a00e19b2a6c59a1401c46c95b0b68680388d92b616d0d00713645d82f42a00e2500006db1a6803866da9b5669d00711b656d2da6a00e236cada5b4d401c4db1769bd328038940001bac6aa00e19baa6e59ab401c46e95b9b6ae80388dd2b736d5d00713755dcaf56a00e2500006fb1b2803866fa9bd66c500711bf56f6db1a00e237eadedb63401c4df977bbd868038940001c2c6da00e1800070d9b7401c370d5c2b6da80388e1ab856db500713875e12f6ca00e251c9471b1be803887229c766f500711c8571adbca00e2390ae35b79401c4e4178dbdde8038947351cac70a00e21cca72d9c3401c47355cbb70a80388e6ab976e15007139a5e5af83a00e25000074b1ca8038674a9d1672500711d25742dc8a00e23a4ae85b91401c4e917a0be3e8038940001d6c73a00e19d6a7559cf401c475d5d5b73a80388ebabab6e7500713ae5eaaf9ba00e251dd476b1d6803887729db675500711dc576add4a00e23b8aed5ba9401c4ee17b4bea28038947851dec76a00e21e0a77d9db401c47855dfb76e80388f0abbf6edd00713c25efafb5a00e25000079b1e28038679a9e5678500711e65792de1a00e23ccaf25bc3401c4f357c9bf0a80389400000007aa00e100007aa9e9401c37ad5e9b7a280388f5abd36f4500713d75f4efd0a00e2500000001ee8038400000007bd007080000001eea00e100000003dd401c20003e05f7a80387400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e1500000001ee8038400000007bd007080000001eea00e100000003dd401c20000000f8280385400000007ba00e100000001ef401c200000007ba803840000000f75007080000003e0a00e15

def row20 (index : ℕ) : List (List ℕ) :=
  if index < 117 then
    let packedCell := Nat.shiftRight row20PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row21PackedData : ℕ := 0x51b12a8038600014564ad0070d455512d2aa00e228aaa25a55401c4a2d689b94e803894000146c4ba00e1800051d92d401c3000147b4b28038600028f69650070e8f5a3ae58a00e25000052b12e8038652a94964bd007114a5526d2fa00e2294aa4da5f401c4a51692b97a80389453514ac4ca00e214ca52d933401c453154bb4c680388a62a97698d00712995a5ee63a00e25000053b1368038600014f64d50070d4f553ad34a00e229eaa75a69401c4a7969cb9a2803894000152c4da00e18000545937401c3000151b4de803860002a369bd0070ea35a8ae6ea00e25155454b13a8038855295364ed0071154554ed3aa00e22a8aa9da75401c4aa56a7b9d2803894000156c4fa00e1800055d93d401c355d556b4f680388abaaad69ed00712ae5ab2e79a00e25000056b1428038600015965050070d595562d40a00e22b2aac5a81401c4acd6b1b9fe80389457515ac50a00e215ca56d943401c457155bb50e80388ae2ab76a1d00712b95adee85a00e25000057b1468038600015f651d0070d5f557ad46a00e22beaaf5a8d401c4af96bcba32803894000162c52a00e1962a585949401c4589561b52680388b12ac36a4d00712c45b0ae92a00e25000059b14e8038659296365350071165558ed4ca00e22caab1da99401c4b296c7ba62803894000166c54a00e1800059d94f401c359d566b53e80388b3aacd6a7d00712cf5b36e9fa00e2500005ab152803865aa969654d007116a55a6d53a00e22d4ab4daa7401c4b556d3ba9680389400016ec55a00e180005b5957401c35b556cb55a80388b6aad96ab500712db5b66eaca00e2517145bb15a803885c296f656d007117055bed5aa00e22e0ab7dab5401c4b856dfbace8038945d5172c57a00e2174a5cd95d401c45d1572b57680388ba2ae56aed00712e85b96ebaa00e2500005db1628038600017765850070d7755dad61a00e22eeabb5ac3401c4bb96ecbb0680389400017ac59a00e197aa5e5965401c45e9579b59280388bd2af36b2500712f45bcaec8a00e2500005fb16a8038600017d65a50070d7d55f2d68a00e22faabe5ad1401c4bed6f8bb4280389460517ec5ba00e2180a5fd96d401c460557fb5b280388c0aaff6b6500713025bfeed8a00e25185460b1728038861298365c50071184560ed70a00e2308ac1dae1401c4c21706bb7e803894000186c5da00e1800061d975401c361d586b5d280388c3ab0d6ba5007130f5c36ee7a00e25000062b17a8038662a98965e5007118b5626d78a00e2316ac4daf1401c4c59713bbbe80389400018ec5fa00e198ea63597d401c463958db5f280388c72b1b6be5007131d5c6eef8a00e25000064b1828038664a991660500711925646d80a00e2324ac8db01401c4c95722bc02803894000196c61a00e1996a655985401c4659594b61680388cb2b296c2d007132c5ca6f09a00e25000066b18a8038600019966250070d995662d89a00e2332acc5b13401c4ccd731bc4a80389400019ec63a00e1800067598f401c367559cb63a80388ceab396c75007133b5ce2f1ba00e25000068b192803860001a1664d0070da15682d92a00e2342ad05b25401c4d0d740bc928038940001a6c65a00e18000695997401c36955a4b65e80388d2ab496cbd007134b5d22f2ea00e2500006ab19e803860001a966750070da956a2d9ca00e2352ad45b39401c4d4d750bce28038940001aec68a00e180006b59a1401c36b55acb68680388d6ab596d0d007135b5d62f42a00e2500006cb1a6803866ca9b1669d00711b256c2da6a00e2364ad85b4d401c4d91760bd328038940001b6c6aa00e19b6a6d59ab401c46d95b4b6ae80388db2b696d5d007136c5da6f56a00e2500006eb1b2803866ea9b966c500711ba56e6db1a00e2374adcdb63401c4dd5772bd868038940001bec6da00e19bea6f59b7401c46fd5bdb6da80388dfab7b6db5007137e5deef6ca00e25000070b1be803860001c366f50070dc3570adbca00e2386ae15b79401c4e1d784bdde8038947251c6c70a00e21c8a71d9c3401c47215c6b70a80388e42b8d6e1500713905e36f83a00e2500007351ca803867329cb672500711cd572edc8a00e239aae5db91401c4e69796be3e8038940001d2c73a00e19d2a7459cf401c47495d0b73a80388e92ba16e7500713a45e82f9ba00e2500000001d6803840001d6a7550070dd65756dd4a00e23acaeadba9401c4eb97aabea2803894000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e1500000001d680384000000075d007080000001d6a00e100000003ad401c20000000ec2803854000000075a00e100000001d7401c2000000075a803840000000eb5007080000003b0a00e15

def row21 (index : ℕ) : List (List ℕ) :=
  if index < 116 then
    let packedCell := Nat.shiftRight row21PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row22PackedData : ℕ := 0x146c4ba00e1800051592d401c3515544b4b280388a2aa896965007128b5a26e58a00e25000051b12e8038600014764bd0070c00051ed2fa00e18000a3da5f401c3a3d68eb97a80389400014ac4ca00e194aa525933401c4529549b4c680388a52a93698d00712945a4ae63a00e2514d452b1368038853294b64d5007114c552ed34a00e2298aa5da69401c4a65697b9a280389400014ec4da00e1800053d937401c353d54eb4de80388a7aa9d69bd007129e5a72e6ea00e25000054b13a8038600015164ed0070c000546d3aa00e18000a8da75401c3a8d6a2b9d2803894555152c4fa00e2154a54d93d401c4551553b4f680388aa2aa769ed00712a95a9ee79a00e25000055b1428038600015765050070d57555ad40a00e22aeaab5a81401c4ab96acb9fe80389400015ac50a00e18000565943401c3565558b50e80388acaab16a1d00712b35ac6e85a00e2515d456b1468038857295b651d007115c556ed46a00e22b8aadda8d401c4ae56b7ba3280389400015ec52a00e1800057d949401c357d55eb52680388afaabd6a4d00712be5af2e92a00e25000058b14e8038658a961653500711625586d4ca00e22c4ab0da99401c4b116c2ba62803894000166c54a00e1964a58d94f401c4595563b53e80388b2aac76a7d00712ca5b1ee9fa00e25000059b15280386000167654d0070d67559ad53a00e22ceab35aa7401c4b3d6cdba9680389400016ac55a00e196aa5a5957401c45a9569b55a80388b52ad36ab500712d55b4eeaca00e2500005bb15a8038600016d656d0070d6d55b2d5aa00e22daab65ab5401c4b6d6d9bace8038945c516ec57a00e2170a5bd95d401c45c156fb57680388b82adf6aed00712e15b7eebaa00e2517545cb162803885d29736585007117455cad61a00e22e8ab95ac3401c4ba16e5bb06803894000176c59a00e180005dd965401c35dd576b59280388bbaaed6b2500712ee5bb2ec8a00e2500005eb16a803865ea97965a5007117a55e6d68a00e22f4abcdad1401c4bd16f2bb4280389400017ec5ba00e180005f596d401c35f557cb5b280388beaaf96b6500712fb5be2ed8a00e2518145fb1728038860297f65c5007118155fed70a00e2302abfdae1401c4c096ffbb7e803894615182c5da00e2184a60d975401c4611583b5d280388c22b076ba500713085c1aee7a00e25000061b17a8038600018765e50070d87561ad78a00e230eac35af1401c4c3d70dbbbe80389400018ac5fa00e198aa62597d401c462d589b5f280388c5ab136be500713165c4eef8a00e25000063b1828038663a98d6605007118e5636d80a00e231cac6db01401c4c7571bbc02803894000192c61a00e1992a645985401c4649591b61680388c92b236c2d00713255c8af09a00e25000065b18a8038665a995662500711965652d89a00e232caca5b13401c4cb1729bc4a80389400019ac63a00e1800066598f401c3665598b63a80388ccab316c7500713335cc6f1ba00e25000067b1928038600019d664d0070d9d5672d92a00e233aace5b25401c4ced738bc928038940001a2c65a00e18000685997401c36855a0b65e80388d0ab416cbd00713435d02f2ea00e25000069b19e803860001a566750070da55692d9ca00e234aad25b39401c4d2d748bce28038940001aac68a00e180006a59a1401c36a55a8b68680388d4ab516d0d00713535d42f42a00e2500006bb1a6803860001ad669d0070dad56b2da6a00e235aad65b4d401c4d6d758bd328038940001b2c6aa00e19b2a6c59ab401c46c95b0b6ae80388d92b616d5d00713645d82f56a00e2500006db1b2803866da9b566c500711b656d2db1a00e236cada5b63401c4db1769bd868038940001bac6da00e19baa6e59b7401c46e95b9b6da80388dd2b736db500713755dcaf6ca00e2500000001be803840001bea6f50070dbf56f6dbca00e237eadedb79401c4df977bbdde803894000000070a00e100000001c1401c20000000706803840000000e0d0070b855e12f83a00e2500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e1500000001c2803840000000705007080000001c1a00e10000000383401c20000000e16803854000000070a00e100000001c1401c20000000706803840000000e0d00708000000385a00e15

def row22 (index : ℕ) : List (List ℕ) :=
  if index < 115 then
    let packedCell := Nat.shiftRight row22PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row23PackedData : ℕ := 0x51b12e8038600014564bd0070d455512d2fa00e228aaa25a5f401c4a2d689b97a803894000146c4ca00e1800051d933401c3000147b4c68038600028f698d0070e8f5a3ae63a00e25000052b1368038652a94964d5007114a5526d34a00e2294aa4da69401c4a51692b9a280389453514ac4da00e214ca52d937401c453154bb4de80388a62a9769bd00712995a5ee6ea00e25000053b13a8038600014f64ed0070d4f553ad3aa00e229eaa75a75401c4a7969cb9d2803894000152c4fa00e1800054593d401c3000151b4f6803860002a369ed0070ea35a8ae79a00e25155454b1428038855295365050071154554ed40a00e22a8aa9da81401c4aa56a7b9fe803894000156c50a00e1800055d943401c355d556b50e80388abaaad6a1d00712ae5ab2e85a00e25000056b14680386000159651d0070d595562d46a00e22b2aac5a8d401c4acd6b1ba3280389457515ac52a00e215ca56d949401c457155bb52680388ae2ab76a4d00712b95adee92a00e25000057b14e8038600015f65350070d5f557ad4ca00e22beaaf5a99401c4af96bcba62803894000162c54a00e1962a58594f401c4589561b53e80388b12ac36a7d00712c45b0ae9fa00e25000059b15280386592963654d0071165558ed53a00e22caab1daa7401c4b296c7ba96803894000166c55a00e1800059d957401c359d566b55a80388b3aacd6ab500712cf5b36eaca00e2500005ab15a803865aa969656d007116a55a6d5aa00e22d4ab4dab5401c4b556d3bace80389400016ec57a00e180005b595d401c35b556cb57680388b6aad96aed00712db5b66ebaa00e2517145bb162803885c296f6585007117055bed61a00e22e0ab7dac3401c4b856dfbb068038945d5172c59a00e2174a5cd965401c45d1572b59280388ba2ae56b2500712e85b96ec8a00e2500005db16a8038600017765a50070d7755dad68a00e22eeabb5ad1401c4bb96ecbb4280389400017ac5ba00e197aa5e596d401c45e9579b5b280388bd2af36b6500712f45bcaed8a00e2500005fb1728038600017d65c50070d7d55f2d70a00e22faabe5ae1401c4bed6f8bb7e80389460517ec5da00e2180a5fd975401c460557fb5d280388c0aaff6ba500713025bfeee7a00e25185460b17a8038861298365e50071184560ed78a00e2308ac1daf1401c4c21706bbbe803894000186c5fa00e1800061d97d401c361d586b5f280388c3ab0d6be5007130f5c36ef8a00e25000062b1828038662a9896605007118b5626d80a00e2316ac4db01401c4c59713bc0280389400018ec61a00e198ea635985401c463958db61680388c72b1b6c2d007131d5c6ef09a00e25000064b18a8038664a991662500711925646d89a00e2324ac8db13401c4c95722bc4a803894000196c63a00e1996a65598f401c4659594b63a80388cb2b296c75007132c5ca6f1ba00e25000066b19280386000199664d0070d995662d92a00e2332acc5b25401c4ccd731bc9280389400019ec65a00e18000675997401c367559cb65e80388ceab396cbd007133b5ce2f2ea00e25000068b19e803860001a166750070da15682d9ca00e2342ad05b39401c4d0d740bce28038940001a6c68a00e180006959a1401c36955a4b68680388d2ab496d0d007134b5d22f42a00e2500006ab1a6803860001a9669d0070da956a2da6a00e2352ad45b4d401c4d4d750bd328038940001aec6aa00e180006b59ab401c36b55acb6ae80388d6ab596d5d007135b5d62f56a00e2500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e1500000001ae8038400000006b5007080000001ada00e1000000035b401c20000000d7a80385400000006ba00e100000001ad401c200000006b6803840000000d6d0070800000035ea00e15

def row23 (index : ℕ) : List (List ℕ) :=
  if index < 114 then
    let packedCell := Nat.shiftRight row23PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row24PackedData : ℕ := 0x146c4ca00e18000515933401c3515544b4c680388a2aa89698d007128b5a26e63a00e25000051b1368038600014764d50070c00051ed34a00e18000a3da69401c3a3d68eb9a280389400014ac4da00e194aa525937401c4529549b4de80388a52a9369bd00712945a4ae6ea00e2514d452b13a8038853294b64ed007114c552ed3aa00e2298aa5da75401c4a65697b9d280389400014ec4fa00e1800053d93d401c353d54eb4f680388a7aa9d69ed007129e5a72e79a00e25000054b1428038600015165050070c000546d40a00e18000a8da81401c3a8d6a2b9fe803894555152c50a00e2154a54d943401c4551553b50e80388aa2aa76a1d00712a95a9ee85a00e25000055b14680386000157651d0070d57555ad46a00e22aeaab5a8d401c4ab96acba3280389400015ac52a00e18000565949401c3565558b52680388acaab16a4d00712b35ac6e92a00e2515d456b14e8038857295b6535007115c556ed4ca00e22b8aadda99401c4ae56b7ba6280389400015ec54a00e1800057d94f401c357d55eb53e80388afaabd6a7d00712be5af2e9fa00e25000058b1528038658a961654d00711625586d53a00e22c4ab0daa7401c4b116c2ba96803894000166c55a00e1964a58d957401c4595563b55a80388b2aac76ab500712ca5b1eeaca00e25000059b15a80386000167656d0070d67559ad5aa00e22ceab35ab5401c4b3d6cdbace80389400016ac57a00e196aa5a595d401c45a9569b57680388b52ad36aed00712d55b4eebaa00e2500005bb1628038600016d65850070d6d55b2d61a00e22daab65ac3401c4b6d6d9bb068038945c516ec59a00e2170a5bd965401c45c156fb59280388b82adf6b2500712e15b7eec8a00e2517545cb16a803885d297365a5007117455cad68a00e22e8ab95ad1401c4ba16e5bb42803894000176c5ba00e180005dd96d401c35dd576b5b280388bbaaed6b6500712ee5bb2ed8a00e2500005eb172803865ea97965c5007117a55e6d70a00e22f4abcdae1401c4bd16f2bb7e80389400017ec5da00e180005f5975401c35f557cb5d280388beaaf96ba500712fb5be2ee7a00e2518145fb17a8038860297f65e5007118155fed78a00e2302abfdaf1401c4c096ffbbbe803894615182c5fa00e2184a60d97d401c4611583b5f280388c22b076be500713085c1aef8a00e25000061b1828038600018766050070d87561ad80a00e230eac35b01401c4c3d70dbc0280389400018ac61a00e198aa625985401c462d589b61680388c5ab136c2d00713165c4ef09a00e25000063b18a8038663a98d6625007118e5636d89a00e231cac6db13401c4c7571bbc4a803894000192c63a00e1992a64598f401c4649591b63a80388c92b236c7500713255c8af1ba00e25000065b1928038665a995664d00711965652d92a00e232caca5b25401c4cb1729bc9280389400019ac65a00e18000665997401c3665598b65e80388ccab316cbd00713335cc6f2ea00e25000000019a80384000000066d0070800000019ca00e10000000339401c200033a5ce2803874000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15000000019a80384000000066d0070800000019ca00e10000000339401c20000000cea803854000000066a00e1000000019b401c20000000672803840000000ce50070800000033aa00e15

def row24 (index : ℕ) : List (List ℕ) :=
  if index < 113 then
    let packedCell := Nat.shiftRight row24PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row25PackedData : ℕ := 0x51b1368038600014564d50070d455512d34a00e228aaa25a69401c4a2d689b9a2803894000146c4da00e1800051d937401c3000147b4de8038600028f69bd0070e8f5a3ae6ea00e25000052b13a8038652a94964ed007114a5526d3aa00e2294aa4da75401c4a51692b9d280389453514ac4fa00e214ca52d93d401c453154bb4f680388a62a9769ed00712995a5ee79a00e25000053b1428038600014f65050070d4f553ad40a00e229eaa75a81401c4a7969cb9fe803894000152c50a00e18000545943401c3000151b50e803860002a36a1d0070ea35a8ae85a00e25155454b14680388552953651d0071154554ed46a00e22a8aa9da8d401c4aa56a7ba32803894000156c52a00e1800055d949401c355d556b52680388abaaad6a4d00712ae5ab2e92a00e25000056b14e8038600015965350070d595562d4ca00e22b2aac5a99401c4acd6b1ba6280389457515ac54a00e215ca56d94f401c457155bb53e80388ae2ab76a7d00712b95adee9fa00e25000057b1528038600015f654d0070d5f557ad53a00e22beaaf5aa7401c4af96bcba96803894000162c55a00e1962a585957401c4589561b55a80388b12ac36ab500712c45b0aeaca00e25000059b15a80386592963656d0071165558ed5aa00e22caab1dab5401c4b296c7bace803894000166c57a00e1800059d95d401c359d566b57680388b3aacd6aed00712cf5b36ebaa00e2500005ab162803865aa9696585007116a55a6d61a00e22d4ab4dac3401c4b556d3bb0680389400016ec59a00e180005b5965401c35b556cb59280388b6aad96b2500712db5b66ec8a00e2517145bb16a803885c296f65a5007117055bed68a00e22e0ab7dad1401c4b856dfbb428038945d5172c5ba00e2174a5cd96d401c45d1572b5b280388ba2ae56b6500712e85b96ed8a00e2500005db1728038600017765c50070d7755dad70a00e22eeabb5ae1401c4bb96ecbb7e80389400017ac5da00e197aa5e5975401c45e9579b5d280388bd2af36ba500712f45bcaee7a00e2500005fb17a8038600017d65e50070d7d55f2d78a00e22faabe5af1401c4bed6f8bbbe80389400018145fa00e1980a5fd97d401c460557fb5f280388c0aaff6be500713025bfeef8a00e2500006151828038661298366050071184560ed80a00e2308ac1db01401c4c21706bc02803894000000061a00e1000061d985401c361d586b61680388c3ab0d6c2d007130f5c36f09a00e25000000018a8038400018aa6250070c00062d589a00e18000c5ab13401c3c59713bc4a803894000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15000000018a80384000000062d0070800000018ba00e10000000317401c20000000c66803854000000062a00e1000000018b401c2000000062e803840000000c5d00708000000319a00e15

def row25 (index : ℕ) : List (List ℕ) :=
  if index < 112 then
    let packedCell := Nat.shiftRight row25PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row26PackedData : ℕ := 0x146c4da00e18000515937401c3515544b4de80388a2aa8969bd007128b5a26e6ea00e25000051b13a8038600014764ed0070c00051ed3aa00e18000a3da75401c3a3d68eb9d280389400014ac4fa00e194aa52593d401c4529549b4f680388a52a9369ed00712945a4ae79a00e2514d452b1428038853294b6505007114c552ed40a00e2298aa5da81401c4a65697b9fe80389400014ec50a00e1800053d943401c353d54eb50e80388a7aa9d6a1d007129e5a72e85a00e25000054b14680386000151651d0070c000546d46a00e18000a8da8d401c3a8d6a2ba32803894555152c52a00e2154a54d949401c4551553b52680388aa2aa76a4d00712a95a9ee92a00e25000055b14e8038600015765350070d57555ad4ca00e22aeaab5a99401c4ab96acba6280389400015ac54a00e1800056594f401c3565558b53e80388acaab16a7d00712b35ac6e9fa00e2515d456b1528038857295b654d007115c556ed53a00e22b8aaddaa7401c4ae56b7ba9680389400015ec55a00e1800057d957401c357d55eb55a80388afaabd6ab500712be5af2eaca00e25000058b15a8038658a961656d00711625586d5aa00e22c4ab0dab5401c4b116c2bace803894000166c57a00e1964a58d95d401c4595563b57680388b2aac76aed00712ca5b1eebaa00e25000059b1628038600016765850070d67559ad61a00e22ceab35ac3401c4b3d6cdbb0680389400016ac59a00e196aa5a5965401c45a9569b59280388b52ad36b2500712d55b4eec8a00e2500005bb16a8038600016d65a50070d6d55b2d68a00e22daab65ad1401c4b6d6d9bb4280389400017145ba00e1970a5bd96d401c45c156fb5b280388b82adf6b6500712e15b7eed8a00e2500005d5172803865d297365c5007117455cad70a00e22e8ab95ae1401c4ba16e5bb7e80389400000005da00e100005dd975401c35dd576b5d280388bbaaed6ba500712ee5bb2ee7a00e25000000017a8038400017aa5e50070d7a55e6d78a00e22f4abcdaf1401c4bd16f2bbbe80389400000005fa00e1000000017d401c200000005f2803840000000be500708000bed6f8a00e1d000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15000000017e8038400000005f50070800000017ca00e100000002f9401c20000000bee80385400000005fa00e1000000017d401c200000005f2803840000000be5007080000002fba00e15

def row26 (index : ℕ) : List (List ℕ) :=
  if index < 111 then
    let packedCell := Nat.shiftRight row26PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row27PackedData : ℕ := 0x51b13a8038600014564ed0070d455512d3aa00e228aaa25a75401c4a2d689b9d2803894000146c4fa00e1800051d93d401c3000147b4f68038600028f69ed0070e8f5a3ae79a00e25000052b1428038652a9496505007114a5526d40a00e2294aa4da81401c4a51692b9fe80389453514ac50a00e214ca52d943401c453154bb50e80388a62a976a1d00712995a5ee85a00e25000053b1468038600014f651d0070d4f553ad46a00e229eaa75a8d401c4a7969cba32803894000152c52a00e18000545949401c3000151b526803860002a36a4d0070ea35a8ae92a00e25155454b14e8038855295365350071154554ed4ca00e22a8aa9da99401c4aa56a7ba62803894000156c54a00e1800055d94f401c355d556b53e80388abaaad6a7d00712ae5ab2e9fa00e25000056b15280386000159654d0070d595562d53a00e22b2aac5aa7401c4acd6b1ba9680389457515ac55a00e215ca56d957401c457155bb55a80388ae2ab76ab500712b95adeeaca00e25000057b15a8038600015f656d0070d5f557ad5aa00e22beaaf5ab5401c4af96bcbace803894000162c57a00e1962a58595d401c4589561b57680388b12ac36aed00712c45b0aebaa00e25000059b1628038659296365850071165558ed61a00e22caab1dac3401c4b296c7bb06803894000000059a00e1000059d965401c359d566b59280388b3aacd6b2500712cf5b36ec8a00e25000000016a8038400016aa5a50070d6a55a6d68a00e22d4ab4dad1401c4b556d3bb4280389400000005ba00e1000000016d401c200016d55b2803860002daab650070edb5b66ed8a00e25000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15000000016e8038400000005b50070800000016ea00e100000002dd401c20000000b7a80385400000005ba00e1000000016d401c200000005ba803840000000b75007080000002dea00e15

def row27 (index : ℕ) : List (List ℕ) :=
  if index < 110 then
    let packedCell := Nat.shiftRight row27PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row28PackedData : ℕ := 0x146c4fa00e1800051593d401c3515544b4f680388a2aa8969ed007128b5a26e79a00e25000051b1428038600014765050070c00051ed40a00e18000a3da81401c3a3d68eb9fe80389400014ac50a00e194aa525943401c4529549b50e80388a52a936a1d00712945a4ae85a00e2514d452b1468038853294b651d007114c552ed46a00e2298aa5da8d401c4a65697ba3280389400014ec52a00e1800053d949401c353d54eb52680388a7aa9d6a4d007129e5a72e92a00e25000054b14e8038600015165350070c000546d4ca00e18000a8da99401c3a8d6a2ba62803894000155454a00e1954a54d94f401c4551553b53e80388aa2aa76a7d00712a95a9ee9fa00e25000055b15280386000157654d0070d57555ad53a00e22aeaab5aa7401c4ab96acba9680389400015ac55a00e18000565957401c3565558b55a80388acaab16ab500712b35ac6eaca00e25000057515a8038600015ca56d0070d5c556ed5aa00e22b8aaddab5401c4ae56b7bace803894000000057a00e1000057d95d401c357d55eb57680388afaabd6aed00712be5af2ebaa00e25000000016280384000000058500708000000161a00e100000002c3401c2b116c2bb06803894000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15000000016280384000000058500708000000161a00e100000002c3401c20000000b12803854000000058a00e10000000161401c20000000586803840000000b0d007080000002c4a00e15

def row28 (index : ℕ) : List (List ℕ) :=
  if index < 109 then
    let packedCell := Nat.shiftRight row28PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row29PackedData : ℕ := 0x51b1428038600014565050070d455512d40a00e228aaa25a81401c4a2d689b9fe803894000146c50a00e1800051d943401c3000147b50e8038600028f6a1d0070e8f5a3ae85a00e25000052b1468038652a949651d007114a5526d46a00e2294aa4da8d401c4a51692ba3280389400014d452a00e194ca52d949401c453154bb52680388a62a976a4d00712995a5ee92a00e25000000014e8038400014f65350070d4f553ad4ca00e229eaa75a99401c4a7969cba62803894000000054a00e1000054594f401c3000151b53e803860002a36a7d0070ea35a8ae9fa00e25000055515280386000154a54d0070c000551553a00e18000aa2aa7401c3aa56a7ba96803894000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15000000015680384000000055500708000000154a00e100000002a9401c20000000ab2803854000000055a00e10000000155401c20000000552803840000000aa5007080000002aca00e15

def row29 (index : ℕ) : List (List ℕ) :=
  if index < 108 then
    let packedCell := Nat.shiftRight row29PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row30PackedData : ℕ := 0x146c50a00e18000515943401c3515544b50e80388a2aa896a1d007128b5a26e85a00e25000000014680384000000051d0070800051ed46a00e18000a3da8d401c3a3d68eba32803894000000052a00e10000000149401c20000000526803840000000a4d00708000a51692a00e1d000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15000000014a80384000000052500708000000149a00e10000000293401c20000000a56803854000000052a00e10000000149401c20000000526803840000000a4d00708000000295a00e15

def row30 (index : ℕ) : List (List ℕ) :=
  if index < 107 then
    let packedCell := Nat.shiftRight row30PackedData (index * 298)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem1 => (Nat.land packedItem1 16383)) 14 (Nat.land packedItem0 7) (Nat.shiftRight packedItem0 3))) 59 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

def lookup : ℕ → ℕ → List (List ℕ)
  | 1 => row1
  | 2 => row2
  | 3 => row3
  | 4 => row4
  | 5 => row5
  | 6 => row6
  | 7 => row7
  | 8 => row8
  | 9 => row9
  | 10 => row10
  | 11 => row11
  | 12 => row12
  | 13 => row13
  | 14 => row14
  | 15 => row15
  | 16 => row16
  | 17 => row17
  | 18 => row18
  | 19 => row19
  | 20 => row20
  | 21 => row21
  | 22 => row22
  | 23 => row23
  | 24 => row24
  | 25 => row25
  | 26 => row26
  | 27 => row27
  | 28 => row28
  | 29 => row29
  | 30 => row30
  | _ => fun _ => []

def runsFor (r v j : ℕ) : List Run :=
  ((lookup r v).getD j []).map (fun n => ⟨n/16,n%16⟩)

open Lower80791.PhaseChecks Lower80791.PhaseRows Lower80791.PhaseData
open Lower80791.ThresholdFast
def HybridAt (r v : ℕ) : Prop :=
  ∀ j ∈ List.range 6,
    Sufficient (phaseSource j) r v (thresholdAt (rowContext r v).threshold j) (runsFor r v j) ∨
      FastSourceThresholdSufficient (phaseSource j) r v (thresholdAt (rowContext r v).threshold j)
instance (r v : ℕ) : Decidable (HybridAt r v) := by unfold HybridAt; infer_instance

theorem hybrid_sound (r v : ℕ) (h : HybridAt r v) : ThresholdAt r v := by
  intro j hj
  rcases h j hj with hs | hs
  · exact sufficient_sound _ _ _ _ _ hs
  · exact hs
end ProximityPrize.SubmissionLower.Lower80791.CompressedData

end Compact_CompressedData80791

section Compact_PrefixChecked80791
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.PrefixChecked
open Lower80791.PhaseRows Lower80791.PhaseData
open Lower80791.ThresholdFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open Lower80791.PhaseChecks

private theorem r1part0 : ∀ i ∈ List.range 8, PrefixAt 1 (0+i) := by decide +kernel

private theorem r1part8 : ∀ i ∈ List.range 8, PrefixAt 1 (8+i) := by decide +kernel

private theorem r1part16 : ∀ i ∈ List.range 8, PrefixAt 1 (16+i) := by decide +kernel

private theorem r1part24 : ∀ i ∈ List.range 8, PrefixAt 1 (24+i) := by decide +kernel

private theorem r1part32 : ∀ i ∈ List.range 8, PrefixAt 1 (32+i) := by decide +kernel

private theorem r1part40 : ∀ i ∈ List.range 8, PrefixAt 1 (40+i) := by decide +kernel

private theorem r1part48 : ∀ i ∈ List.range 8, PrefixAt 1 (48+i) := by decide +kernel

private theorem r1part56 : ∀ i ∈ List.range 8, PrefixAt 1 (56+i) := by decide +kernel

private theorem r1part64 : ∀ i ∈ List.range 8, PrefixAt 1 (64+i) := by decide +kernel

private theorem r1part72 : ∀ i ∈ List.range 8, PrefixAt 1 (72+i) := by decide +kernel

private theorem r1part80 : ∀ i ∈ List.range 8, PrefixAt 1 (80+i) := by decide +kernel

private theorem r1part88 : ∀ i ∈ List.range 8, PrefixAt 1 (88+i) := by decide +kernel

private theorem r1part96 : ∀ i ∈ List.range 8, PrefixAt 1 (96+i) := by decide +kernel

private theorem r1part104 : ∀ i ∈ List.range 8, PrefixAt 1 (104+i) := by decide +kernel

private theorem r1part112 : ∀ i ∈ List.range 8, PrefixAt 1 (112+i) := by decide +kernel

private theorem r1part120 : ∀ i ∈ List.range 8, PrefixAt 1 (120+i) := by decide +kernel

private theorem r1part128 : ∀ i ∈ List.range 8, PrefixAt 1 (128+i) := by decide +kernel

theorem checkedR1 : ∀ V ∈ List.range 136, PrefixAt 1 V := by
  intro V hV
  have hlt : V < 136 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r1part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r1part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r1part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r1part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r1part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r1part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r1part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r1part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r1part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r1part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r1part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r1part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r1part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r1part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r1part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r1part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r1part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r2part0 : ∀ i ∈ List.range 8, PrefixAt 2 (0+i) := by decide +kernel

private theorem r2part8 : ∀ i ∈ List.range 8, PrefixAt 2 (8+i) := by decide +kernel

private theorem r2part16 : ∀ i ∈ List.range 8, PrefixAt 2 (16+i) := by decide +kernel

private theorem r2part24 : ∀ i ∈ List.range 8, PrefixAt 2 (24+i) := by decide +kernel

private theorem r2part32 : ∀ i ∈ List.range 8, PrefixAt 2 (32+i) := by decide +kernel

private theorem r2part40 : ∀ i ∈ List.range 8, PrefixAt 2 (40+i) := by decide +kernel

private theorem r2part48 : ∀ i ∈ List.range 8, PrefixAt 2 (48+i) := by decide +kernel

private theorem r2part56 : ∀ i ∈ List.range 8, PrefixAt 2 (56+i) := by decide +kernel

private theorem r2part64 : ∀ i ∈ List.range 8, PrefixAt 2 (64+i) := by decide +kernel

private theorem r2part72 : ∀ i ∈ List.range 8, PrefixAt 2 (72+i) := by decide +kernel

private theorem r2part80 : ∀ i ∈ List.range 8, PrefixAt 2 (80+i) := by decide +kernel

private theorem r2part88 : ∀ i ∈ List.range 8, PrefixAt 2 (88+i) := by decide +kernel

private theorem r2part96 : ∀ i ∈ List.range 8, PrefixAt 2 (96+i) := by decide +kernel

private theorem r2part104 : ∀ i ∈ List.range 8, PrefixAt 2 (104+i) := by decide +kernel

private theorem r2part112 : ∀ i ∈ List.range 8, PrefixAt 2 (112+i) := by decide +kernel

private theorem r2part120 : ∀ i ∈ List.range 8, PrefixAt 2 (120+i) := by decide +kernel

private theorem r2part128 : ∀ i ∈ List.range 7, PrefixAt 2 (128+i) := by decide +kernel

theorem checkedR2 : ∀ V ∈ List.range 135, PrefixAt 2 V := by
  intro V hV
  have hlt : V < 135 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r2part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r2part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r2part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r2part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r2part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r2part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r2part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r2part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r2part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r2part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r2part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r2part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r2part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r2part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r2part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r2part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r2part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r3part0 : ∀ i ∈ List.range 8, PrefixAt 3 (0+i) := by decide +kernel

private theorem r3part8 : ∀ i ∈ List.range 8, PrefixAt 3 (8+i) := by decide +kernel

private theorem r3part16 : ∀ i ∈ List.range 8, PrefixAt 3 (16+i) := by decide +kernel

private theorem r3part24 : ∀ i ∈ List.range 8, PrefixAt 3 (24+i) := by decide +kernel

private theorem r3part32 : ∀ i ∈ List.range 8, PrefixAt 3 (32+i) := by decide +kernel

private theorem r3part40 : ∀ i ∈ List.range 8, PrefixAt 3 (40+i) := by decide +kernel

private theorem r3part48 : ∀ i ∈ List.range 8, PrefixAt 3 (48+i) := by decide +kernel

private theorem r3part56 : ∀ i ∈ List.range 8, PrefixAt 3 (56+i) := by decide +kernel

private theorem r3part64 : ∀ i ∈ List.range 8, PrefixAt 3 (64+i) := by decide +kernel

private theorem r3part72 : ∀ i ∈ List.range 8, PrefixAt 3 (72+i) := by decide +kernel

private theorem r3part80 : ∀ i ∈ List.range 8, PrefixAt 3 (80+i) := by decide +kernel

private theorem r3part88 : ∀ i ∈ List.range 8, PrefixAt 3 (88+i) := by decide +kernel

private theorem r3part96 : ∀ i ∈ List.range 8, PrefixAt 3 (96+i) := by decide +kernel

private theorem r3part104 : ∀ i ∈ List.range 8, PrefixAt 3 (104+i) := by decide +kernel

private theorem r3part112 : ∀ i ∈ List.range 8, PrefixAt 3 (112+i) := by decide +kernel

private theorem r3part120 : ∀ i ∈ List.range 8, PrefixAt 3 (120+i) := by decide +kernel

private theorem r3part128 : ∀ i ∈ List.range 6, PrefixAt 3 (128+i) := by decide +kernel

theorem checkedR3 : ∀ V ∈ List.range 134, PrefixAt 3 V := by
  intro V hV
  have hlt : V < 134 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r3part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r3part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r3part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r3part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r3part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r3part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r3part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r3part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r3part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r3part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r3part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r3part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r3part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r3part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r3part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r3part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r3part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r4part0 : ∀ i ∈ List.range 8, PrefixAt 4 (0+i) := by decide +kernel

private theorem r4part8 : ∀ i ∈ List.range 8, PrefixAt 4 (8+i) := by decide +kernel

private theorem r4part16 : ∀ i ∈ List.range 8, PrefixAt 4 (16+i) := by decide +kernel

private theorem r4part24 : ∀ i ∈ List.range 8, PrefixAt 4 (24+i) := by decide +kernel

private theorem r4part32 : ∀ i ∈ List.range 8, PrefixAt 4 (32+i) := by decide +kernel

private theorem r4part40 : ∀ i ∈ List.range 8, PrefixAt 4 (40+i) := by decide +kernel

private theorem r4part48 : ∀ i ∈ List.range 8, PrefixAt 4 (48+i) := by decide +kernel

private theorem r4part56 : ∀ i ∈ List.range 8, PrefixAt 4 (56+i) := by decide +kernel

private theorem r4part64 : ∀ i ∈ List.range 8, PrefixAt 4 (64+i) := by decide +kernel

private theorem r4part72 : ∀ i ∈ List.range 8, PrefixAt 4 (72+i) := by decide +kernel

private theorem r4part80 : ∀ i ∈ List.range 8, PrefixAt 4 (80+i) := by decide +kernel

private theorem r4part88 : ∀ i ∈ List.range 8, PrefixAt 4 (88+i) := by decide +kernel

private theorem r4part96 : ∀ i ∈ List.range 8, PrefixAt 4 (96+i) := by decide +kernel

private theorem r4part104 : ∀ i ∈ List.range 8, PrefixAt 4 (104+i) := by decide +kernel

private theorem r4part112 : ∀ i ∈ List.range 8, PrefixAt 4 (112+i) := by decide +kernel

private theorem r4part120 : ∀ i ∈ List.range 8, PrefixAt 4 (120+i) := by decide +kernel

private theorem r4part128 : ∀ i ∈ List.range 5, PrefixAt 4 (128+i) := by decide +kernel

theorem checkedR4 : ∀ V ∈ List.range 133, PrefixAt 4 V := by
  intro V hV
  have hlt : V < 133 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r4part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r4part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r4part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r4part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r4part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r4part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r4part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r4part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r4part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r4part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r4part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r4part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r4part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r4part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r4part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r4part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r4part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r5part0 : ∀ i ∈ List.range 8, PrefixAt 5 (0+i) := by decide +kernel

private theorem r5part8 : ∀ i ∈ List.range 8, PrefixAt 5 (8+i) := by decide +kernel

private theorem r5part16 : ∀ i ∈ List.range 8, PrefixAt 5 (16+i) := by decide +kernel

private theorem r5part24 : ∀ i ∈ List.range 8, PrefixAt 5 (24+i) := by decide +kernel

private theorem r5part32 : ∀ i ∈ List.range 8, PrefixAt 5 (32+i) := by decide +kernel

private theorem r5part40 : ∀ i ∈ List.range 8, PrefixAt 5 (40+i) := by decide +kernel

private theorem r5part48 : ∀ i ∈ List.range 8, PrefixAt 5 (48+i) := by decide +kernel

private theorem r5part56 : ∀ i ∈ List.range 8, PrefixAt 5 (56+i) := by decide +kernel

private theorem r5part64 : ∀ i ∈ List.range 8, PrefixAt 5 (64+i) := by decide +kernel

private theorem r5part72 : ∀ i ∈ List.range 8, PrefixAt 5 (72+i) := by decide +kernel

private theorem r5part80 : ∀ i ∈ List.range 8, PrefixAt 5 (80+i) := by decide +kernel

private theorem r5part88 : ∀ i ∈ List.range 8, PrefixAt 5 (88+i) := by decide +kernel

private theorem r5part96 : ∀ i ∈ List.range 8, PrefixAt 5 (96+i) := by decide +kernel

private theorem r5part104 : ∀ i ∈ List.range 8, PrefixAt 5 (104+i) := by decide +kernel

private theorem r5part112 : ∀ i ∈ List.range 8, PrefixAt 5 (112+i) := by decide +kernel

private theorem r5part120 : ∀ i ∈ List.range 8, PrefixAt 5 (120+i) := by decide +kernel

private theorem r5part128 : ∀ i ∈ List.range 4, PrefixAt 5 (128+i) := by decide +kernel

theorem checkedR5 : ∀ V ∈ List.range 132, PrefixAt 5 V := by
  intro V hV
  have hlt : V < 132 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r5part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r5part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r5part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r5part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r5part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r5part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r5part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r5part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r5part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r5part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r5part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r5part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r5part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r5part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r5part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r5part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r5part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r6part0 : ∀ i ∈ List.range 8, PrefixAt 6 (0+i) := by decide +kernel

private theorem r6part8 : ∀ i ∈ List.range 8, PrefixAt 6 (8+i) := by decide +kernel

private theorem r6part16 : ∀ i ∈ List.range 8, PrefixAt 6 (16+i) := by decide +kernel

private theorem r6part24 : ∀ i ∈ List.range 8, PrefixAt 6 (24+i) := by decide +kernel

private theorem r6part32 : ∀ i ∈ List.range 8, PrefixAt 6 (32+i) := by decide +kernel

private theorem r6part40 : ∀ i ∈ List.range 8, PrefixAt 6 (40+i) := by decide +kernel

private theorem r6part48 : ∀ i ∈ List.range 8, PrefixAt 6 (48+i) := by decide +kernel

private theorem r6part56 : ∀ i ∈ List.range 8, PrefixAt 6 (56+i) := by decide +kernel

private theorem r6part64 : ∀ i ∈ List.range 8, PrefixAt 6 (64+i) := by decide +kernel

private theorem r6part72 : ∀ i ∈ List.range 8, PrefixAt 6 (72+i) := by decide +kernel

private theorem r6part80 : ∀ i ∈ List.range 8, PrefixAt 6 (80+i) := by decide +kernel

private theorem r6part88 : ∀ i ∈ List.range 8, PrefixAt 6 (88+i) := by decide +kernel

private theorem r6part96 : ∀ i ∈ List.range 8, PrefixAt 6 (96+i) := by decide +kernel

private theorem r6part104 : ∀ i ∈ List.range 8, PrefixAt 6 (104+i) := by decide +kernel

private theorem r6part112 : ∀ i ∈ List.range 8, PrefixAt 6 (112+i) := by decide +kernel

private theorem r6part120 : ∀ i ∈ List.range 8, PrefixAt 6 (120+i) := by decide +kernel

private theorem r6part128 : ∀ i ∈ List.range 3, PrefixAt 6 (128+i) := by decide +kernel

theorem checkedR6 : ∀ V ∈ List.range 131, PrefixAt 6 V := by
  intro V hV
  have hlt : V < 131 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r6part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r6part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r6part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r6part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r6part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r6part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r6part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r6part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r6part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r6part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r6part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r6part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r6part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r6part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r6part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r6part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r6part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r7part0 : ∀ i ∈ List.range 8, PrefixAt 7 (0+i) := by decide +kernel

private theorem r7part8 : ∀ i ∈ List.range 8, PrefixAt 7 (8+i) := by decide +kernel

private theorem r7part16 : ∀ i ∈ List.range 8, PrefixAt 7 (16+i) := by decide +kernel

private theorem r7part24 : ∀ i ∈ List.range 8, PrefixAt 7 (24+i) := by decide +kernel

private theorem r7part32 : ∀ i ∈ List.range 8, PrefixAt 7 (32+i) := by decide +kernel

private theorem r7part40 : ∀ i ∈ List.range 8, PrefixAt 7 (40+i) := by decide +kernel

private theorem r7part48 : ∀ i ∈ List.range 8, PrefixAt 7 (48+i) := by decide +kernel

private theorem r7part56 : ∀ i ∈ List.range 8, PrefixAt 7 (56+i) := by decide +kernel

private theorem r7part64 : ∀ i ∈ List.range 8, PrefixAt 7 (64+i) := by decide +kernel

private theorem r7part72 : ∀ i ∈ List.range 8, PrefixAt 7 (72+i) := by decide +kernel

private theorem r7part80 : ∀ i ∈ List.range 8, PrefixAt 7 (80+i) := by decide +kernel

private theorem r7part88 : ∀ i ∈ List.range 8, PrefixAt 7 (88+i) := by decide +kernel

private theorem r7part96 : ∀ i ∈ List.range 8, PrefixAt 7 (96+i) := by decide +kernel

private theorem r7part104 : ∀ i ∈ List.range 8, PrefixAt 7 (104+i) := by decide +kernel

private theorem r7part112 : ∀ i ∈ List.range 8, PrefixAt 7 (112+i) := by decide +kernel

private theorem r7part120 : ∀ i ∈ List.range 8, PrefixAt 7 (120+i) := by decide +kernel

private theorem r7part128 : ∀ i ∈ List.range 2, PrefixAt 7 (128+i) := by decide +kernel

theorem checkedR7 : ∀ V ∈ List.range 130, PrefixAt 7 V := by
  intro V hV
  have hlt : V < 130 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r7part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r7part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r7part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r7part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r7part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r7part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r7part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r7part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r7part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r7part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r7part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r7part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r7part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r7part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r7part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r7part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r7part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r8part0 : ∀ i ∈ List.range 8, PrefixAt 8 (0+i) := by decide +kernel

private theorem r8part8 : ∀ i ∈ List.range 8, PrefixAt 8 (8+i) := by decide +kernel

private theorem r8part16 : ∀ i ∈ List.range 8, PrefixAt 8 (16+i) := by decide +kernel

private theorem r8part24 : ∀ i ∈ List.range 8, PrefixAt 8 (24+i) := by decide +kernel

private theorem r8part32 : ∀ i ∈ List.range 8, PrefixAt 8 (32+i) := by decide +kernel

private theorem r8part40 : ∀ i ∈ List.range 8, PrefixAt 8 (40+i) := by decide +kernel

private theorem r8part48 : ∀ i ∈ List.range 8, PrefixAt 8 (48+i) := by decide +kernel

private theorem r8part56 : ∀ i ∈ List.range 8, PrefixAt 8 (56+i) := by decide +kernel

private theorem r8part64 : ∀ i ∈ List.range 8, PrefixAt 8 (64+i) := by decide +kernel

private theorem r8part72 : ∀ i ∈ List.range 8, PrefixAt 8 (72+i) := by decide +kernel

private theorem r8part80 : ∀ i ∈ List.range 8, PrefixAt 8 (80+i) := by decide +kernel

private theorem r8part88 : ∀ i ∈ List.range 8, PrefixAt 8 (88+i) := by decide +kernel

private theorem r8part96 : ∀ i ∈ List.range 8, PrefixAt 8 (96+i) := by decide +kernel

private theorem r8part104 : ∀ i ∈ List.range 8, PrefixAt 8 (104+i) := by decide +kernel

private theorem r8part112 : ∀ i ∈ List.range 8, PrefixAt 8 (112+i) := by decide +kernel

private theorem r8part120 : ∀ i ∈ List.range 8, PrefixAt 8 (120+i) := by decide +kernel

private theorem r8part128 : ∀ i ∈ List.range 1, PrefixAt 8 (128+i) := by decide +kernel

theorem checkedR8 : ∀ V ∈ List.range 129, PrefixAt 8 V := by
  intro V hV
  have hlt : V < 129 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r8part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r8part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r8part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r8part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r8part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r8part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r8part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r8part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r8part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r8part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r8part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r8part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r8part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r8part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r8part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r8part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r8part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r9part0 : ∀ i ∈ List.range 8, PrefixAt 9 (0+i) := by decide +kernel

private theorem r9part8 : ∀ i ∈ List.range 8, PrefixAt 9 (8+i) := by decide +kernel

private theorem r9part16 : ∀ i ∈ List.range 8, PrefixAt 9 (16+i) := by decide +kernel

private theorem r9part24 : ∀ i ∈ List.range 8, PrefixAt 9 (24+i) := by decide +kernel

private theorem r9part32 : ∀ i ∈ List.range 8, PrefixAt 9 (32+i) := by decide +kernel

private theorem r9part40 : ∀ i ∈ List.range 8, PrefixAt 9 (40+i) := by decide +kernel

private theorem r9part48 : ∀ i ∈ List.range 8, PrefixAt 9 (48+i) := by decide +kernel

private theorem r9part56 : ∀ i ∈ List.range 8, PrefixAt 9 (56+i) := by decide +kernel

private theorem r9part64 : ∀ i ∈ List.range 8, PrefixAt 9 (64+i) := by decide +kernel

private theorem r9part72 : ∀ i ∈ List.range 8, PrefixAt 9 (72+i) := by decide +kernel

private theorem r9part80 : ∀ i ∈ List.range 8, PrefixAt 9 (80+i) := by decide +kernel

private theorem r9part88 : ∀ i ∈ List.range 8, PrefixAt 9 (88+i) := by decide +kernel

private theorem r9part96 : ∀ i ∈ List.range 8, PrefixAt 9 (96+i) := by decide +kernel

private theorem r9part104 : ∀ i ∈ List.range 8, PrefixAt 9 (104+i) := by decide +kernel

private theorem r9part112 : ∀ i ∈ List.range 8, PrefixAt 9 (112+i) := by decide +kernel

private theorem r9part120 : ∀ i ∈ List.range 8, PrefixAt 9 (120+i) := by decide +kernel

theorem checkedR9 : ∀ V ∈ List.range 128, PrefixAt 9 V := by
  intro V hV
  have hlt : V < 128 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r9part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r9part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r9part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r9part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r9part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r9part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r9part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r9part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r9part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r9part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r9part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r9part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r9part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r9part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r9part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r9part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r10part0 : ∀ i ∈ List.range 8, PrefixAt 10 (0+i) := by decide +kernel

private theorem r10part8 : ∀ i ∈ List.range 8, PrefixAt 10 (8+i) := by decide +kernel

private theorem r10part16 : ∀ i ∈ List.range 8, PrefixAt 10 (16+i) := by decide +kernel

private theorem r10part24 : ∀ i ∈ List.range 8, PrefixAt 10 (24+i) := by decide +kernel

private theorem r10part32 : ∀ i ∈ List.range 8, PrefixAt 10 (32+i) := by decide +kernel

private theorem r10part40 : ∀ i ∈ List.range 8, PrefixAt 10 (40+i) := by decide +kernel

private theorem r10part48 : ∀ i ∈ List.range 8, PrefixAt 10 (48+i) := by decide +kernel

private theorem r10part56 : ∀ i ∈ List.range 8, PrefixAt 10 (56+i) := by decide +kernel

private theorem r10part64 : ∀ i ∈ List.range 8, PrefixAt 10 (64+i) := by decide +kernel

private theorem r10part72 : ∀ i ∈ List.range 8, PrefixAt 10 (72+i) := by decide +kernel

private theorem r10part80 : ∀ i ∈ List.range 8, PrefixAt 10 (80+i) := by decide +kernel

private theorem r10part88 : ∀ i ∈ List.range 8, PrefixAt 10 (88+i) := by decide +kernel

private theorem r10part96 : ∀ i ∈ List.range 8, PrefixAt 10 (96+i) := by decide +kernel

private theorem r10part104 : ∀ i ∈ List.range 8, PrefixAt 10 (104+i) := by decide +kernel

private theorem r10part112 : ∀ i ∈ List.range 8, PrefixAt 10 (112+i) := by decide +kernel

private theorem r10part120 : ∀ i ∈ List.range 7, PrefixAt 10 (120+i) := by decide +kernel

theorem checkedR10 : ∀ V ∈ List.range 127, PrefixAt 10 V := by
  intro V hV
  have hlt : V < 127 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r10part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r10part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r10part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r10part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r10part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r10part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r10part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r10part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r10part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r10part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r10part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r10part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r10part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r10part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r10part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r10part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r11part0 : ∀ i ∈ List.range 8, PrefixAt 11 (0+i) := by decide +kernel

private theorem r11part8 : ∀ i ∈ List.range 8, PrefixAt 11 (8+i) := by decide +kernel

private theorem r11part16 : ∀ i ∈ List.range 8, PrefixAt 11 (16+i) := by decide +kernel

private theorem r11part24 : ∀ i ∈ List.range 8, PrefixAt 11 (24+i) := by decide +kernel

private theorem r11part32 : ∀ i ∈ List.range 8, PrefixAt 11 (32+i) := by decide +kernel

private theorem r11part40 : ∀ i ∈ List.range 8, PrefixAt 11 (40+i) := by decide +kernel

private theorem r11part48 : ∀ i ∈ List.range 8, PrefixAt 11 (48+i) := by decide +kernel

private theorem r11part56 : ∀ i ∈ List.range 8, PrefixAt 11 (56+i) := by decide +kernel

private theorem r11part64 : ∀ i ∈ List.range 8, PrefixAt 11 (64+i) := by decide +kernel

private theorem r11part72 : ∀ i ∈ List.range 8, PrefixAt 11 (72+i) := by decide +kernel

private theorem r11part80 : ∀ i ∈ List.range 8, PrefixAt 11 (80+i) := by decide +kernel

private theorem r11part88 : ∀ i ∈ List.range 8, PrefixAt 11 (88+i) := by decide +kernel

private theorem r11part96 : ∀ i ∈ List.range 8, PrefixAt 11 (96+i) := by decide +kernel

private theorem r11part104 : ∀ i ∈ List.range 8, PrefixAt 11 (104+i) := by decide +kernel

private theorem r11part112 : ∀ i ∈ List.range 8, PrefixAt 11 (112+i) := by decide +kernel

private theorem r11part120 : ∀ i ∈ List.range 6, PrefixAt 11 (120+i) := by decide +kernel

theorem checkedR11 : ∀ V ∈ List.range 126, PrefixAt 11 V := by
  intro V hV
  have hlt : V < 126 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r11part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r11part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r11part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r11part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r11part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r11part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r11part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r11part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r11part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r11part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r11part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r11part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r11part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r11part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r11part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r11part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r12part0 : ∀ i ∈ List.range 8, PrefixAt 12 (0+i) := by decide +kernel

private theorem r12part8 : ∀ i ∈ List.range 8, PrefixAt 12 (8+i) := by decide +kernel

private theorem r12part16 : ∀ i ∈ List.range 8, PrefixAt 12 (16+i) := by decide +kernel

private theorem r12part24 : ∀ i ∈ List.range 8, PrefixAt 12 (24+i) := by decide +kernel

private theorem r12part32 : ∀ i ∈ List.range 8, PrefixAt 12 (32+i) := by decide +kernel

private theorem r12part40 : ∀ i ∈ List.range 8, PrefixAt 12 (40+i) := by decide +kernel

private theorem r12part48 : ∀ i ∈ List.range 8, PrefixAt 12 (48+i) := by decide +kernel

private theorem r12part56 : ∀ i ∈ List.range 8, PrefixAt 12 (56+i) := by decide +kernel

private theorem r12part64 : ∀ i ∈ List.range 8, PrefixAt 12 (64+i) := by decide +kernel

private theorem r12part72 : ∀ i ∈ List.range 8, PrefixAt 12 (72+i) := by decide +kernel

private theorem r12part80 : ∀ i ∈ List.range 8, PrefixAt 12 (80+i) := by decide +kernel

private theorem r12part88 : ∀ i ∈ List.range 8, PrefixAt 12 (88+i) := by decide +kernel

private theorem r12part96 : ∀ i ∈ List.range 8, PrefixAt 12 (96+i) := by decide +kernel

private theorem r12part104 : ∀ i ∈ List.range 8, PrefixAt 12 (104+i) := by decide +kernel

private theorem r12part112 : ∀ i ∈ List.range 8, PrefixAt 12 (112+i) := by decide +kernel

private theorem r12part120 : ∀ i ∈ List.range 5, PrefixAt 12 (120+i) := by decide +kernel

theorem checkedR12 : ∀ V ∈ List.range 125, PrefixAt 12 V := by
  intro V hV
  have hlt : V < 125 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r12part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r12part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r12part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r12part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r12part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r12part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r12part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r12part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r12part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r12part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r12part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r12part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r12part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r12part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r12part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r12part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r13part0 : ∀ i ∈ List.range 8, PrefixAt 13 (0+i) := by decide +kernel

private theorem r13part8 : ∀ i ∈ List.range 8, PrefixAt 13 (8+i) := by decide +kernel

private theorem r13part16 : ∀ i ∈ List.range 8, PrefixAt 13 (16+i) := by decide +kernel

private theorem r13part24 : ∀ i ∈ List.range 8, PrefixAt 13 (24+i) := by decide +kernel

private theorem r13part32 : ∀ i ∈ List.range 8, PrefixAt 13 (32+i) := by decide +kernel

private theorem r13part40 : ∀ i ∈ List.range 8, PrefixAt 13 (40+i) := by decide +kernel

private theorem r13part48 : ∀ i ∈ List.range 8, PrefixAt 13 (48+i) := by decide +kernel

private theorem r13part56 : ∀ i ∈ List.range 8, PrefixAt 13 (56+i) := by decide +kernel

private theorem r13part64 : ∀ i ∈ List.range 8, PrefixAt 13 (64+i) := by decide +kernel

private theorem r13part72 : ∀ i ∈ List.range 8, PrefixAt 13 (72+i) := by decide +kernel

private theorem r13part80 : ∀ i ∈ List.range 8, PrefixAt 13 (80+i) := by decide +kernel

private theorem r13part88 : ∀ i ∈ List.range 8, PrefixAt 13 (88+i) := by decide +kernel

private theorem r13part96 : ∀ i ∈ List.range 8, PrefixAt 13 (96+i) := by decide +kernel

private theorem r13part104 : ∀ i ∈ List.range 8, PrefixAt 13 (104+i) := by decide +kernel

private theorem r13part112 : ∀ i ∈ List.range 8, PrefixAt 13 (112+i) := by decide +kernel

private theorem r13part120 : ∀ i ∈ List.range 4, PrefixAt 13 (120+i) := by decide +kernel

theorem checkedR13 : ∀ V ∈ List.range 124, PrefixAt 13 V := by
  intro V hV
  have hlt : V < 124 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r13part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r13part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r13part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r13part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r13part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r13part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r13part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r13part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r13part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r13part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r13part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r13part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r13part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r13part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r13part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r13part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r14part0 : ∀ i ∈ List.range 8, PrefixAt 14 (0+i) := by decide +kernel

private theorem r14part8 : ∀ i ∈ List.range 8, PrefixAt 14 (8+i) := by decide +kernel

private theorem r14part16 : ∀ i ∈ List.range 8, PrefixAt 14 (16+i) := by decide +kernel

private theorem r14part24 : ∀ i ∈ List.range 8, PrefixAt 14 (24+i) := by decide +kernel

private theorem r14part32 : ∀ i ∈ List.range 8, PrefixAt 14 (32+i) := by decide +kernel

private theorem r14part40 : ∀ i ∈ List.range 8, PrefixAt 14 (40+i) := by decide +kernel

private theorem r14part48 : ∀ i ∈ List.range 8, PrefixAt 14 (48+i) := by decide +kernel

private theorem r14part56 : ∀ i ∈ List.range 8, PrefixAt 14 (56+i) := by decide +kernel

private theorem r14part64 : ∀ i ∈ List.range 8, PrefixAt 14 (64+i) := by decide +kernel

private theorem r14part72 : ∀ i ∈ List.range 8, PrefixAt 14 (72+i) := by decide +kernel

private theorem r14part80 : ∀ i ∈ List.range 8, PrefixAt 14 (80+i) := by decide +kernel

private theorem r14part88 : ∀ i ∈ List.range 8, PrefixAt 14 (88+i) := by decide +kernel

private theorem r14part96 : ∀ i ∈ List.range 8, PrefixAt 14 (96+i) := by decide +kernel

private theorem r14part104 : ∀ i ∈ List.range 8, PrefixAt 14 (104+i) := by decide +kernel

private theorem r14part112 : ∀ i ∈ List.range 8, PrefixAt 14 (112+i) := by decide +kernel

private theorem r14part120 : ∀ i ∈ List.range 3, PrefixAt 14 (120+i) := by decide +kernel

theorem checkedR14 : ∀ V ∈ List.range 123, PrefixAt 14 V := by
  intro V hV
  have hlt : V < 123 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r14part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r14part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r14part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r14part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r14part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r14part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r14part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r14part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r14part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r14part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r14part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r14part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r14part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r14part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r14part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r14part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r15part0 : ∀ i ∈ List.range 8, PrefixAt 15 (0+i) := by decide +kernel

private theorem r15part8 : ∀ i ∈ List.range 8, PrefixAt 15 (8+i) := by decide +kernel

private theorem r15part16 : ∀ i ∈ List.range 8, PrefixAt 15 (16+i) := by decide +kernel

private theorem r15part24 : ∀ i ∈ List.range 8, PrefixAt 15 (24+i) := by decide +kernel

private theorem r15part32 : ∀ i ∈ List.range 8, PrefixAt 15 (32+i) := by decide +kernel

private theorem r15part40 : ∀ i ∈ List.range 8, PrefixAt 15 (40+i) := by decide +kernel

private theorem r15part48 : ∀ i ∈ List.range 8, PrefixAt 15 (48+i) := by decide +kernel

private theorem r15part56 : ∀ i ∈ List.range 8, PrefixAt 15 (56+i) := by decide +kernel

private theorem r15part64 : ∀ i ∈ List.range 8, PrefixAt 15 (64+i) := by decide +kernel

private theorem r15part72 : ∀ i ∈ List.range 8, PrefixAt 15 (72+i) := by decide +kernel

private theorem r15part80 : ∀ i ∈ List.range 8, PrefixAt 15 (80+i) := by decide +kernel

private theorem r15part88 : ∀ i ∈ List.range 8, PrefixAt 15 (88+i) := by decide +kernel

private theorem r15part96 : ∀ i ∈ List.range 8, PrefixAt 15 (96+i) := by decide +kernel

private theorem r15part104 : ∀ i ∈ List.range 8, PrefixAt 15 (104+i) := by decide +kernel

private theorem r15part112 : ∀ i ∈ List.range 8, PrefixAt 15 (112+i) := by decide +kernel

private theorem r15part120 : ∀ i ∈ List.range 2, PrefixAt 15 (120+i) := by decide +kernel

theorem checkedR15 : ∀ V ∈ List.range 122, PrefixAt 15 V := by
  intro V hV
  have hlt : V < 122 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r15part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r15part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r15part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r15part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r15part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r15part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r15part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r15part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r15part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r15part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r15part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r15part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r15part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r15part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r15part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r15part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r16part0 : ∀ i ∈ List.range 8, PrefixAt 16 (0+i) := by decide +kernel

private theorem r16part8 : ∀ i ∈ List.range 8, PrefixAt 16 (8+i) := by decide +kernel

private theorem r16part16 : ∀ i ∈ List.range 8, PrefixAt 16 (16+i) := by decide +kernel

private theorem r16part24 : ∀ i ∈ List.range 8, PrefixAt 16 (24+i) := by decide +kernel

private theorem r16part32 : ∀ i ∈ List.range 8, PrefixAt 16 (32+i) := by decide +kernel

private theorem r16part40 : ∀ i ∈ List.range 8, PrefixAt 16 (40+i) := by decide +kernel

private theorem r16part48 : ∀ i ∈ List.range 8, PrefixAt 16 (48+i) := by decide +kernel

private theorem r16part56 : ∀ i ∈ List.range 8, PrefixAt 16 (56+i) := by decide +kernel

private theorem r16part64 : ∀ i ∈ List.range 8, PrefixAt 16 (64+i) := by decide +kernel

private theorem r16part72 : ∀ i ∈ List.range 8, PrefixAt 16 (72+i) := by decide +kernel

private theorem r16part80 : ∀ i ∈ List.range 8, PrefixAt 16 (80+i) := by decide +kernel

private theorem r16part88 : ∀ i ∈ List.range 8, PrefixAt 16 (88+i) := by decide +kernel

private theorem r16part96 : ∀ i ∈ List.range 8, PrefixAt 16 (96+i) := by decide +kernel

private theorem r16part104 : ∀ i ∈ List.range 8, PrefixAt 16 (104+i) := by decide +kernel

private theorem r16part112 : ∀ i ∈ List.range 8, PrefixAt 16 (112+i) := by decide +kernel

private theorem r16part120 : ∀ i ∈ List.range 1, PrefixAt 16 (120+i) := by decide +kernel

theorem checkedR16 : ∀ V ∈ List.range 121, PrefixAt 16 V := by
  intro V hV
  have hlt : V < 121 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r16part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r16part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r16part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r16part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r16part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r16part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r16part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r16part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r16part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r16part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r16part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r16part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r16part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r16part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r16part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r16part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r17part0 : ∀ i ∈ List.range 8, PrefixAt 17 (0+i) := by decide +kernel

private theorem r17part8 : ∀ i ∈ List.range 8, PrefixAt 17 (8+i) := by decide +kernel

private theorem r17part16 : ∀ i ∈ List.range 8, PrefixAt 17 (16+i) := by decide +kernel

private theorem r17part24 : ∀ i ∈ List.range 8, PrefixAt 17 (24+i) := by decide +kernel

private theorem r17part32 : ∀ i ∈ List.range 8, PrefixAt 17 (32+i) := by decide +kernel

private theorem r17part40 : ∀ i ∈ List.range 8, PrefixAt 17 (40+i) := by decide +kernel

private theorem r17part48 : ∀ i ∈ List.range 8, PrefixAt 17 (48+i) := by decide +kernel

private theorem r17part56 : ∀ i ∈ List.range 8, PrefixAt 17 (56+i) := by decide +kernel

private theorem r17part64 : ∀ i ∈ List.range 8, PrefixAt 17 (64+i) := by decide +kernel

private theorem r17part72 : ∀ i ∈ List.range 8, PrefixAt 17 (72+i) := by decide +kernel

private theorem r17part80 : ∀ i ∈ List.range 8, PrefixAt 17 (80+i) := by decide +kernel

private theorem r17part88 : ∀ i ∈ List.range 8, PrefixAt 17 (88+i) := by decide +kernel

private theorem r17part96 : ∀ i ∈ List.range 8, PrefixAt 17 (96+i) := by decide +kernel

private theorem r17part104 : ∀ i ∈ List.range 8, PrefixAt 17 (104+i) := by decide +kernel

private theorem r17part112 : ∀ i ∈ List.range 8, PrefixAt 17 (112+i) := by decide +kernel

theorem checkedR17 : ∀ V ∈ List.range 120, PrefixAt 17 V := by
  intro V hV
  have hlt : V < 120 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r17part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r17part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r17part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r17part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r17part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r17part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r17part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r17part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r17part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r17part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r17part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r17part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r17part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r17part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r17part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r18part0 : ∀ i ∈ List.range 8, PrefixAt 18 (0+i) := by decide +kernel

private theorem r18part8 : ∀ i ∈ List.range 8, PrefixAt 18 (8+i) := by decide +kernel

private theorem r18part16 : ∀ i ∈ List.range 8, PrefixAt 18 (16+i) := by decide +kernel

private theorem r18part24 : ∀ i ∈ List.range 8, PrefixAt 18 (24+i) := by decide +kernel

private theorem r18part32 : ∀ i ∈ List.range 8, PrefixAt 18 (32+i) := by decide +kernel

private theorem r18part40 : ∀ i ∈ List.range 8, PrefixAt 18 (40+i) := by decide +kernel

private theorem r18part48 : ∀ i ∈ List.range 8, PrefixAt 18 (48+i) := by decide +kernel

private theorem r18part56 : ∀ i ∈ List.range 8, PrefixAt 18 (56+i) := by decide +kernel

private theorem r18part64 : ∀ i ∈ List.range 8, PrefixAt 18 (64+i) := by decide +kernel

private theorem r18part72 : ∀ i ∈ List.range 8, PrefixAt 18 (72+i) := by decide +kernel

private theorem r18part80 : ∀ i ∈ List.range 8, PrefixAt 18 (80+i) := by decide +kernel

private theorem r18part88 : ∀ i ∈ List.range 8, PrefixAt 18 (88+i) := by decide +kernel

private theorem r18part96 : ∀ i ∈ List.range 8, PrefixAt 18 (96+i) := by decide +kernel

private theorem r18part104 : ∀ i ∈ List.range 8, PrefixAt 18 (104+i) := by decide +kernel

private theorem r18part112 : ∀ i ∈ List.range 7, PrefixAt 18 (112+i) := by decide +kernel

theorem checkedR18 : ∀ V ∈ List.range 119, PrefixAt 18 V := by
  intro V hV
  have hlt : V < 119 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r18part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r18part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r18part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r18part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r18part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r18part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r18part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r18part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r18part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r18part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r18part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r18part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r18part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r18part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r18part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r19part0 : ∀ i ∈ List.range 8, PrefixAt 19 (0+i) := by decide +kernel

private theorem r19part8 : ∀ i ∈ List.range 8, PrefixAt 19 (8+i) := by decide +kernel

private theorem r19part16 : ∀ i ∈ List.range 8, PrefixAt 19 (16+i) := by decide +kernel

private theorem r19part24 : ∀ i ∈ List.range 8, PrefixAt 19 (24+i) := by decide +kernel

private theorem r19part32 : ∀ i ∈ List.range 8, PrefixAt 19 (32+i) := by decide +kernel

private theorem r19part40 : ∀ i ∈ List.range 8, PrefixAt 19 (40+i) := by decide +kernel

private theorem r19part48 : ∀ i ∈ List.range 8, PrefixAt 19 (48+i) := by decide +kernel

private theorem r19part56 : ∀ i ∈ List.range 8, PrefixAt 19 (56+i) := by decide +kernel

private theorem r19part64 : ∀ i ∈ List.range 8, PrefixAt 19 (64+i) := by decide +kernel

private theorem r19part72 : ∀ i ∈ List.range 8, PrefixAt 19 (72+i) := by decide +kernel

private theorem r19part80 : ∀ i ∈ List.range 8, PrefixAt 19 (80+i) := by decide +kernel

private theorem r19part88 : ∀ i ∈ List.range 8, PrefixAt 19 (88+i) := by decide +kernel

private theorem r19part96 : ∀ i ∈ List.range 8, PrefixAt 19 (96+i) := by decide +kernel

private theorem r19part104 : ∀ i ∈ List.range 8, PrefixAt 19 (104+i) := by decide +kernel

private theorem r19part112 : ∀ i ∈ List.range 6, PrefixAt 19 (112+i) := by decide +kernel

theorem checkedR19 : ∀ V ∈ List.range 118, PrefixAt 19 V := by
  intro V hV
  have hlt : V < 118 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r19part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r19part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r19part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r19part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r19part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r19part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r19part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r19part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r19part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r19part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r19part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r19part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r19part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r19part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r19part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r20part0 : ∀ i ∈ List.range 8, PrefixAt 20 (0+i) := by decide +kernel

private theorem r20part8 : ∀ i ∈ List.range 8, PrefixAt 20 (8+i) := by decide +kernel

private theorem r20part16 : ∀ i ∈ List.range 8, PrefixAt 20 (16+i) := by decide +kernel

private theorem r20part24 : ∀ i ∈ List.range 8, PrefixAt 20 (24+i) := by decide +kernel

private theorem r20part32 : ∀ i ∈ List.range 8, PrefixAt 20 (32+i) := by decide +kernel

private theorem r20part40 : ∀ i ∈ List.range 8, PrefixAt 20 (40+i) := by decide +kernel

private theorem r20part48 : ∀ i ∈ List.range 8, PrefixAt 20 (48+i) := by decide +kernel

private theorem r20part56 : ∀ i ∈ List.range 8, PrefixAt 20 (56+i) := by decide +kernel

private theorem r20part64 : ∀ i ∈ List.range 8, PrefixAt 20 (64+i) := by decide +kernel

private theorem r20part72 : ∀ i ∈ List.range 8, PrefixAt 20 (72+i) := by decide +kernel

private theorem r20part80 : ∀ i ∈ List.range 8, PrefixAt 20 (80+i) := by decide +kernel

private theorem r20part88 : ∀ i ∈ List.range 8, PrefixAt 20 (88+i) := by decide +kernel

private theorem r20part96 : ∀ i ∈ List.range 8, PrefixAt 20 (96+i) := by decide +kernel

private theorem r20part104 : ∀ i ∈ List.range 8, PrefixAt 20 (104+i) := by decide +kernel

private theorem r20part112 : ∀ i ∈ List.range 5, PrefixAt 20 (112+i) := by decide +kernel

theorem checkedR20 : ∀ V ∈ List.range 117, PrefixAt 20 V := by
  intro V hV
  have hlt : V < 117 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r20part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r20part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r20part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r20part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r20part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r20part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r20part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r20part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r20part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r20part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r20part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r20part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r20part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r20part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r20part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r21part0 : ∀ i ∈ List.range 8, PrefixAt 21 (0+i) := by decide +kernel

private theorem r21part8 : ∀ i ∈ List.range 8, PrefixAt 21 (8+i) := by decide +kernel

private theorem r21part16 : ∀ i ∈ List.range 8, PrefixAt 21 (16+i) := by decide +kernel

private theorem r21part24 : ∀ i ∈ List.range 8, PrefixAt 21 (24+i) := by decide +kernel

private theorem r21part32 : ∀ i ∈ List.range 8, PrefixAt 21 (32+i) := by decide +kernel

private theorem r21part40 : ∀ i ∈ List.range 8, PrefixAt 21 (40+i) := by decide +kernel

private theorem r21part48 : ∀ i ∈ List.range 8, PrefixAt 21 (48+i) := by decide +kernel

private theorem r21part56 : ∀ i ∈ List.range 8, PrefixAt 21 (56+i) := by decide +kernel

private theorem r21part64 : ∀ i ∈ List.range 8, PrefixAt 21 (64+i) := by decide +kernel

private theorem r21part72 : ∀ i ∈ List.range 8, PrefixAt 21 (72+i) := by decide +kernel

private theorem r21part80 : ∀ i ∈ List.range 8, PrefixAt 21 (80+i) := by decide +kernel

private theorem r21part88 : ∀ i ∈ List.range 8, PrefixAt 21 (88+i) := by decide +kernel

private theorem r21part96 : ∀ i ∈ List.range 8, PrefixAt 21 (96+i) := by decide +kernel

private theorem r21part104 : ∀ i ∈ List.range 8, PrefixAt 21 (104+i) := by decide +kernel

private theorem r21part112 : ∀ i ∈ List.range 4, PrefixAt 21 (112+i) := by decide +kernel

theorem checkedR21 : ∀ V ∈ List.range 116, PrefixAt 21 V := by
  intro V hV
  have hlt : V < 116 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r21part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r21part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r21part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r21part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r21part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r21part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r21part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r21part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r21part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r21part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r21part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r21part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r21part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r21part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r21part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r22part0 : ∀ i ∈ List.range 8, PrefixAt 22 (0+i) := by decide +kernel

private theorem r22part8 : ∀ i ∈ List.range 8, PrefixAt 22 (8+i) := by decide +kernel

private theorem r22part16 : ∀ i ∈ List.range 8, PrefixAt 22 (16+i) := by decide +kernel

private theorem r22part24 : ∀ i ∈ List.range 8, PrefixAt 22 (24+i) := by decide +kernel

private theorem r22part32 : ∀ i ∈ List.range 8, PrefixAt 22 (32+i) := by decide +kernel

private theorem r22part40 : ∀ i ∈ List.range 8, PrefixAt 22 (40+i) := by decide +kernel

private theorem r22part48 : ∀ i ∈ List.range 8, PrefixAt 22 (48+i) := by decide +kernel

private theorem r22part56 : ∀ i ∈ List.range 8, PrefixAt 22 (56+i) := by decide +kernel

private theorem r22part64 : ∀ i ∈ List.range 8, PrefixAt 22 (64+i) := by decide +kernel

private theorem r22part72 : ∀ i ∈ List.range 8, PrefixAt 22 (72+i) := by decide +kernel

private theorem r22part80 : ∀ i ∈ List.range 8, PrefixAt 22 (80+i) := by decide +kernel

private theorem r22part88 : ∀ i ∈ List.range 8, PrefixAt 22 (88+i) := by decide +kernel

private theorem r22part96 : ∀ i ∈ List.range 8, PrefixAt 22 (96+i) := by decide +kernel

private theorem r22part104 : ∀ i ∈ List.range 8, PrefixAt 22 (104+i) := by decide +kernel

private theorem r22part112 : ∀ i ∈ List.range 3, PrefixAt 22 (112+i) := by decide +kernel

theorem checkedR22 : ∀ V ∈ List.range 115, PrefixAt 22 V := by
  intro V hV
  have hlt : V < 115 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r22part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r22part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r22part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r22part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r22part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r22part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r22part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r22part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r22part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r22part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r22part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r22part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r22part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r22part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r22part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r23part0 : ∀ i ∈ List.range 8, PrefixAt 23 (0+i) := by decide +kernel

private theorem r23part8 : ∀ i ∈ List.range 8, PrefixAt 23 (8+i) := by decide +kernel

private theorem r23part16 : ∀ i ∈ List.range 8, PrefixAt 23 (16+i) := by decide +kernel

private theorem r23part24 : ∀ i ∈ List.range 8, PrefixAt 23 (24+i) := by decide +kernel

private theorem r23part32 : ∀ i ∈ List.range 8, PrefixAt 23 (32+i) := by decide +kernel

private theorem r23part40 : ∀ i ∈ List.range 8, PrefixAt 23 (40+i) := by decide +kernel

private theorem r23part48 : ∀ i ∈ List.range 8, PrefixAt 23 (48+i) := by decide +kernel

private theorem r23part56 : ∀ i ∈ List.range 8, PrefixAt 23 (56+i) := by decide +kernel

private theorem r23part64 : ∀ i ∈ List.range 8, PrefixAt 23 (64+i) := by decide +kernel

private theorem r23part72 : ∀ i ∈ List.range 8, PrefixAt 23 (72+i) := by decide +kernel

private theorem r23part80 : ∀ i ∈ List.range 8, PrefixAt 23 (80+i) := by decide +kernel

private theorem r23part88 : ∀ i ∈ List.range 8, PrefixAt 23 (88+i) := by decide +kernel

private theorem r23part96 : ∀ i ∈ List.range 8, PrefixAt 23 (96+i) := by decide +kernel

private theorem r23part104 : ∀ i ∈ List.range 8, PrefixAt 23 (104+i) := by decide +kernel

private theorem r23part112 : ∀ i ∈ List.range 2, PrefixAt 23 (112+i) := by decide +kernel

theorem checkedR23 : ∀ V ∈ List.range 114, PrefixAt 23 V := by
  intro V hV
  have hlt : V < 114 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r23part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r23part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r23part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r23part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r23part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r23part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r23part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r23part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r23part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r23part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r23part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r23part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r23part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r23part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r23part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r24part0 : ∀ i ∈ List.range 8, PrefixAt 24 (0+i) := by decide +kernel

private theorem r24part8 : ∀ i ∈ List.range 8, PrefixAt 24 (8+i) := by decide +kernel

private theorem r24part16 : ∀ i ∈ List.range 8, PrefixAt 24 (16+i) := by decide +kernel

private theorem r24part24 : ∀ i ∈ List.range 8, PrefixAt 24 (24+i) := by decide +kernel

private theorem r24part32 : ∀ i ∈ List.range 8, PrefixAt 24 (32+i) := by decide +kernel

private theorem r24part40 : ∀ i ∈ List.range 8, PrefixAt 24 (40+i) := by decide +kernel

private theorem r24part48 : ∀ i ∈ List.range 8, PrefixAt 24 (48+i) := by decide +kernel

private theorem r24part56 : ∀ i ∈ List.range 8, PrefixAt 24 (56+i) := by decide +kernel

private theorem r24part64 : ∀ i ∈ List.range 8, PrefixAt 24 (64+i) := by decide +kernel

private theorem r24part72 : ∀ i ∈ List.range 8, PrefixAt 24 (72+i) := by decide +kernel

private theorem r24part80 : ∀ i ∈ List.range 8, PrefixAt 24 (80+i) := by decide +kernel

private theorem r24part88 : ∀ i ∈ List.range 8, PrefixAt 24 (88+i) := by decide +kernel

private theorem r24part96 : ∀ i ∈ List.range 8, PrefixAt 24 (96+i) := by decide +kernel

private theorem r24part104 : ∀ i ∈ List.range 8, PrefixAt 24 (104+i) := by decide +kernel

private theorem r24part112 : ∀ i ∈ List.range 1, PrefixAt 24 (112+i) := by decide +kernel

theorem checkedR24 : ∀ V ∈ List.range 113, PrefixAt 24 V := by
  intro V hV
  have hlt : V < 113 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r24part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r24part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r24part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r24part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r24part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r24part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r24part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r24part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r24part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r24part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r24part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r24part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r24part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r24part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r24part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r25part0 : ∀ i ∈ List.range 8, PrefixAt 25 (0+i) := by decide +kernel

private theorem r25part8 : ∀ i ∈ List.range 8, PrefixAt 25 (8+i) := by decide +kernel

private theorem r25part16 : ∀ i ∈ List.range 8, PrefixAt 25 (16+i) := by decide +kernel

private theorem r25part24 : ∀ i ∈ List.range 8, PrefixAt 25 (24+i) := by decide +kernel

private theorem r25part32 : ∀ i ∈ List.range 8, PrefixAt 25 (32+i) := by decide +kernel

private theorem r25part40 : ∀ i ∈ List.range 8, PrefixAt 25 (40+i) := by decide +kernel

private theorem r25part48 : ∀ i ∈ List.range 8, PrefixAt 25 (48+i) := by decide +kernel

private theorem r25part56 : ∀ i ∈ List.range 8, PrefixAt 25 (56+i) := by decide +kernel

private theorem r25part64 : ∀ i ∈ List.range 8, PrefixAt 25 (64+i) := by decide +kernel

private theorem r25part72 : ∀ i ∈ List.range 8, PrefixAt 25 (72+i) := by decide +kernel

private theorem r25part80 : ∀ i ∈ List.range 8, PrefixAt 25 (80+i) := by decide +kernel

private theorem r25part88 : ∀ i ∈ List.range 8, PrefixAt 25 (88+i) := by decide +kernel

private theorem r25part96 : ∀ i ∈ List.range 8, PrefixAt 25 (96+i) := by decide +kernel

private theorem r25part104 : ∀ i ∈ List.range 8, PrefixAt 25 (104+i) := by decide +kernel

theorem checkedR25 : ∀ V ∈ List.range 112, PrefixAt 25 V := by
  intro V hV
  have hlt : V < 112 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r25part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r25part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r25part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r25part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r25part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r25part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r25part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r25part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r25part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r25part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r25part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r25part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r25part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r25part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

private theorem r26part0 : ∀ i ∈ List.range 8, PrefixAt 26 (0+i) := by decide +kernel

private theorem r26part8 : ∀ i ∈ List.range 8, PrefixAt 26 (8+i) := by decide +kernel

private theorem r26part16 : ∀ i ∈ List.range 8, PrefixAt 26 (16+i) := by decide +kernel

private theorem r26part24 : ∀ i ∈ List.range 8, PrefixAt 26 (24+i) := by decide +kernel

private theorem r26part32 : ∀ i ∈ List.range 8, PrefixAt 26 (32+i) := by decide +kernel

private theorem r26part40 : ∀ i ∈ List.range 8, PrefixAt 26 (40+i) := by decide +kernel

private theorem r26part48 : ∀ i ∈ List.range 8, PrefixAt 26 (48+i) := by decide +kernel

private theorem r26part56 : ∀ i ∈ List.range 8, PrefixAt 26 (56+i) := by decide +kernel

private theorem r26part64 : ∀ i ∈ List.range 8, PrefixAt 26 (64+i) := by decide +kernel

private theorem r26part72 : ∀ i ∈ List.range 8, PrefixAt 26 (72+i) := by decide +kernel

private theorem r26part80 : ∀ i ∈ List.range 8, PrefixAt 26 (80+i) := by decide +kernel

private theorem r26part88 : ∀ i ∈ List.range 8, PrefixAt 26 (88+i) := by decide +kernel

private theorem r26part96 : ∀ i ∈ List.range 8, PrefixAt 26 (96+i) := by decide +kernel

private theorem r26part104 : ∀ i ∈ List.range 7, PrefixAt 26 (104+i) := by decide +kernel

theorem checkedR26 : ∀ V ∈ List.range 111, PrefixAt 26 V := by
  intro V hV
  have hlt : V < 111 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r26part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r26part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r26part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r26part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r26part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r26part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r26part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r26part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r26part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r26part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r26part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r26part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r26part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r26part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

private theorem r27part0 : ∀ i ∈ List.range 8, PrefixAt 27 (0+i) := by decide +kernel

private theorem r27part8 : ∀ i ∈ List.range 8, PrefixAt 27 (8+i) := by decide +kernel

private theorem r27part16 : ∀ i ∈ List.range 8, PrefixAt 27 (16+i) := by decide +kernel

private theorem r27part24 : ∀ i ∈ List.range 8, PrefixAt 27 (24+i) := by decide +kernel

private theorem r27part32 : ∀ i ∈ List.range 8, PrefixAt 27 (32+i) := by decide +kernel

private theorem r27part40 : ∀ i ∈ List.range 8, PrefixAt 27 (40+i) := by decide +kernel

private theorem r27part48 : ∀ i ∈ List.range 8, PrefixAt 27 (48+i) := by decide +kernel

private theorem r27part56 : ∀ i ∈ List.range 8, PrefixAt 27 (56+i) := by decide +kernel

private theorem r27part64 : ∀ i ∈ List.range 8, PrefixAt 27 (64+i) := by decide +kernel

private theorem r27part72 : ∀ i ∈ List.range 8, PrefixAt 27 (72+i) := by decide +kernel

private theorem r27part80 : ∀ i ∈ List.range 8, PrefixAt 27 (80+i) := by decide +kernel

private theorem r27part88 : ∀ i ∈ List.range 8, PrefixAt 27 (88+i) := by decide +kernel

private theorem r27part96 : ∀ i ∈ List.range 8, PrefixAt 27 (96+i) := by decide +kernel

private theorem r27part104 : ∀ i ∈ List.range 6, PrefixAt 27 (104+i) := by decide +kernel

theorem checkedR27 : ∀ V ∈ List.range 110, PrefixAt 27 V := by
  intro V hV
  have hlt : V < 110 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r27part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r27part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r27part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r27part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r27part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r27part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r27part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r27part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r27part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r27part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r27part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r27part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r27part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r27part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

private theorem r28part0 : ∀ i ∈ List.range 8, PrefixAt 28 (0+i) := by decide +kernel

private theorem r28part8 : ∀ i ∈ List.range 8, PrefixAt 28 (8+i) := by decide +kernel

private theorem r28part16 : ∀ i ∈ List.range 8, PrefixAt 28 (16+i) := by decide +kernel

private theorem r28part24 : ∀ i ∈ List.range 8, PrefixAt 28 (24+i) := by decide +kernel

private theorem r28part32 : ∀ i ∈ List.range 8, PrefixAt 28 (32+i) := by decide +kernel

private theorem r28part40 : ∀ i ∈ List.range 8, PrefixAt 28 (40+i) := by decide +kernel

private theorem r28part48 : ∀ i ∈ List.range 8, PrefixAt 28 (48+i) := by decide +kernel

private theorem r28part56 : ∀ i ∈ List.range 8, PrefixAt 28 (56+i) := by decide +kernel

private theorem r28part64 : ∀ i ∈ List.range 8, PrefixAt 28 (64+i) := by decide +kernel

private theorem r28part72 : ∀ i ∈ List.range 8, PrefixAt 28 (72+i) := by decide +kernel

private theorem r28part80 : ∀ i ∈ List.range 8, PrefixAt 28 (80+i) := by decide +kernel

private theorem r28part88 : ∀ i ∈ List.range 8, PrefixAt 28 (88+i) := by decide +kernel

private theorem r28part96 : ∀ i ∈ List.range 8, PrefixAt 28 (96+i) := by decide +kernel

private theorem r28part104 : ∀ i ∈ List.range 5, PrefixAt 28 (104+i) := by decide +kernel

theorem checkedR28 : ∀ V ∈ List.range 109, PrefixAt 28 V := by
  intro V hV
  have hlt : V < 109 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r28part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r28part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r28part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r28part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r28part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r28part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r28part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r28part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r28part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r28part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r28part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r28part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r28part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r28part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

private theorem r29part0 : ∀ i ∈ List.range 8, PrefixAt 29 (0+i) := by decide +kernel

private theorem r29part8 : ∀ i ∈ List.range 8, PrefixAt 29 (8+i) := by decide +kernel

private theorem r29part16 : ∀ i ∈ List.range 8, PrefixAt 29 (16+i) := by decide +kernel

private theorem r29part24 : ∀ i ∈ List.range 8, PrefixAt 29 (24+i) := by decide +kernel

private theorem r29part32 : ∀ i ∈ List.range 8, PrefixAt 29 (32+i) := by decide +kernel

private theorem r29part40 : ∀ i ∈ List.range 8, PrefixAt 29 (40+i) := by decide +kernel

private theorem r29part48 : ∀ i ∈ List.range 8, PrefixAt 29 (48+i) := by decide +kernel

private theorem r29part56 : ∀ i ∈ List.range 8, PrefixAt 29 (56+i) := by decide +kernel

private theorem r29part64 : ∀ i ∈ List.range 8, PrefixAt 29 (64+i) := by decide +kernel

private theorem r29part72 : ∀ i ∈ List.range 8, PrefixAt 29 (72+i) := by decide +kernel

private theorem r29part80 : ∀ i ∈ List.range 8, PrefixAt 29 (80+i) := by decide +kernel

private theorem r29part88 : ∀ i ∈ List.range 8, PrefixAt 29 (88+i) := by decide +kernel

private theorem r29part96 : ∀ i ∈ List.range 8, PrefixAt 29 (96+i) := by decide +kernel

private theorem r29part104 : ∀ i ∈ List.range 4, PrefixAt 29 (104+i) := by decide +kernel

theorem checkedR29 : ∀ V ∈ List.range 108, PrefixAt 29 V := by
  intro V hV
  have hlt : V < 108 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r29part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r29part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r29part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r29part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r29part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r29part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r29part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r29part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r29part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r29part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r29part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r29part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r29part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r29part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

private theorem r30part0 : ∀ i ∈ List.range 8, PrefixAt 30 (0+i) := by decide +kernel

private theorem r30part8 : ∀ i ∈ List.range 8, PrefixAt 30 (8+i) := by decide +kernel

private theorem r30part16 : ∀ i ∈ List.range 8, PrefixAt 30 (16+i) := by decide +kernel

private theorem r30part24 : ∀ i ∈ List.range 8, PrefixAt 30 (24+i) := by decide +kernel

private theorem r30part32 : ∀ i ∈ List.range 8, PrefixAt 30 (32+i) := by decide +kernel

private theorem r30part40 : ∀ i ∈ List.range 8, PrefixAt 30 (40+i) := by decide +kernel

private theorem r30part48 : ∀ i ∈ List.range 8, PrefixAt 30 (48+i) := by decide +kernel

private theorem r30part56 : ∀ i ∈ List.range 8, PrefixAt 30 (56+i) := by decide +kernel

private theorem r30part64 : ∀ i ∈ List.range 8, PrefixAt 30 (64+i) := by decide +kernel

private theorem r30part72 : ∀ i ∈ List.range 8, PrefixAt 30 (72+i) := by decide +kernel

private theorem r30part80 : ∀ i ∈ List.range 8, PrefixAt 30 (80+i) := by decide +kernel

private theorem r30part88 : ∀ i ∈ List.range 8, PrefixAt 30 (88+i) := by decide +kernel

private theorem r30part96 : ∀ i ∈ List.range 8, PrefixAt 30 (96+i) := by decide +kernel

private theorem r30part104 : ∀ i ∈ List.range 3, PrefixAt 30 (104+i) := by decide +kernel

theorem checkedR30 : ∀ V ∈ List.range 107, PrefixAt 30 V := by
  intro V hV
  have hlt : V < 107 := List.mem_range.mp hV
  by_cases h8 : V < 8
  · have hp := r30part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r30part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r30part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r30part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r30part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r30part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r30part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r30part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r30part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r30part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r30part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r30part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r30part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r30part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

theorem checked : ∀ r ∈ List.range 31, 1 ≤ r →
    ∀ v ∈ List.range (137-r), PrefixAt r v := by
  intro r hr hpos
  have hlt : r < 31 := List.mem_range.mp hr
  interval_cases r <;> first
    | exact checkedR1
    | exact checkedR2
    | exact checkedR3
    | exact checkedR4
    | exact checkedR5
    | exact checkedR6
    | exact checkedR7
    | exact checkedR8
    | exact checkedR9
    | exact checkedR10
    | exact checkedR11
    | exact checkedR12
    | exact checkedR13
    | exact checkedR14
    | exact checkedR15
    | exact checkedR16
    | exact checkedR17
    | exact checkedR18
    | exact checkedR19
    | exact checkedR20
    | exact checkedR21
    | exact checkedR22
    | exact checkedR23
    | exact checkedR24
    | exact checkedR25
    | exact checkedR26
    | exact checkedR27
    | exact checkedR28
    | exact checkedR29
    | exact checkedR30

end ProximityPrize.SubmissionLower.Lower80791.PrefixChecked

end Compact_PrefixChecked80791

section Compact_RunsChecked80791
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.RunsChecked
open Lower80791.PhaseRows Lower80791.PhaseData
open Lower80791.ThresholdFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open Lower80791.PhaseChecks

private theorem r1part0 : ∀ i ∈ List.range 4, RunsAt 1 (0+i) := by decide +kernel

private theorem r1part4 : ∀ i ∈ List.range 4, RunsAt 1 (4+i) := by decide +kernel

private theorem r1part8 : ∀ i ∈ List.range 4, RunsAt 1 (8+i) := by decide +kernel

private theorem r1part12 : ∀ i ∈ List.range 4, RunsAt 1 (12+i) := by decide +kernel

private theorem r1part16 : ∀ i ∈ List.range 4, RunsAt 1 (16+i) := by decide +kernel

private theorem r1part20 : ∀ i ∈ List.range 4, RunsAt 1 (20+i) := by decide +kernel

private theorem r1part24 : ∀ i ∈ List.range 4, RunsAt 1 (24+i) := by decide +kernel

private theorem r1part28 : ∀ i ∈ List.range 4, RunsAt 1 (28+i) := by decide +kernel

private theorem r1part32 : ∀ i ∈ List.range 4, RunsAt 1 (32+i) := by decide +kernel

private theorem r1part36 : ∀ i ∈ List.range 4, RunsAt 1 (36+i) := by decide +kernel

private theorem r1part40 : ∀ i ∈ List.range 4, RunsAt 1 (40+i) := by decide +kernel

private theorem r1part44 : ∀ i ∈ List.range 4, RunsAt 1 (44+i) := by decide +kernel

private theorem r1part48 : ∀ i ∈ List.range 4, RunsAt 1 (48+i) := by decide +kernel

private theorem r1part52 : ∀ i ∈ List.range 4, RunsAt 1 (52+i) := by decide +kernel

private theorem r1part56 : ∀ i ∈ List.range 4, RunsAt 1 (56+i) := by decide +kernel

private theorem r1part60 : ∀ i ∈ List.range 4, RunsAt 1 (60+i) := by decide +kernel

private theorem r1part64 : ∀ i ∈ List.range 4, RunsAt 1 (64+i) := by decide +kernel

private theorem r1part68 : ∀ i ∈ List.range 4, RunsAt 1 (68+i) := by decide +kernel

private theorem r1part72 : ∀ i ∈ List.range 4, RunsAt 1 (72+i) := by decide +kernel

private theorem r1part76 : ∀ i ∈ List.range 4, RunsAt 1 (76+i) := by decide +kernel

private theorem r1part80 : ∀ i ∈ List.range 4, RunsAt 1 (80+i) := by decide +kernel

private theorem r1part84 : ∀ i ∈ List.range 4, RunsAt 1 (84+i) := by decide +kernel

private theorem r1part88 : ∀ i ∈ List.range 4, RunsAt 1 (88+i) := by decide +kernel

private theorem r1part92 : ∀ i ∈ List.range 4, RunsAt 1 (92+i) := by decide +kernel

private theorem r1part96 : ∀ i ∈ List.range 4, RunsAt 1 (96+i) := by decide +kernel

private theorem r1part100 : ∀ i ∈ List.range 4, RunsAt 1 (100+i) := by decide +kernel

private theorem r1part104 : ∀ i ∈ List.range 4, RunsAt 1 (104+i) := by decide +kernel

private theorem r1part108 : ∀ i ∈ List.range 4, RunsAt 1 (108+i) := by decide +kernel

private theorem r1part112 : ∀ i ∈ List.range 4, RunsAt 1 (112+i) := by decide +kernel

private theorem r1part116 : ∀ i ∈ List.range 4, RunsAt 1 (116+i) := by decide +kernel

private theorem r1part120 : ∀ i ∈ List.range 4, RunsAt 1 (120+i) := by decide +kernel

private theorem r1part124 : ∀ i ∈ List.range 4, RunsAt 1 (124+i) := by decide +kernel

private theorem r1part128 : ∀ i ∈ List.range 4, RunsAt 1 (128+i) := by decide +kernel

private theorem r1part132 : ∀ i ∈ List.range 4, RunsAt 1 (132+i) := by decide +kernel

theorem checkedR1 : ∀ V ∈ List.range 136, RunsAt 1 V := by
  intro V hV
  have hlt : V < 136 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r1part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r1part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r1part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r1part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r1part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r1part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r1part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r1part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r1part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r1part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r1part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r1part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r1part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r1part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r1part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r1part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r1part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r1part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r1part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r1part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r1part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r1part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r1part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r1part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r1part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r1part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r1part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r1part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r1part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r1part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r1part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r1part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  by_cases h132 : V < 132
  · have hp := r1part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r1part132 (V-132) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hp

private theorem r2part0 : ∀ i ∈ List.range 4, RunsAt 2 (0+i) := by decide +kernel

private theorem r2part4 : ∀ i ∈ List.range 4, RunsAt 2 (4+i) := by decide +kernel

private theorem r2part8 : ∀ i ∈ List.range 4, RunsAt 2 (8+i) := by decide +kernel

private theorem r2part12 : ∀ i ∈ List.range 4, RunsAt 2 (12+i) := by decide +kernel

private theorem r2part16 : ∀ i ∈ List.range 4, RunsAt 2 (16+i) := by decide +kernel

private theorem r2part20 : ∀ i ∈ List.range 4, RunsAt 2 (20+i) := by decide +kernel

private theorem r2part24 : ∀ i ∈ List.range 4, RunsAt 2 (24+i) := by decide +kernel

private theorem r2part28 : ∀ i ∈ List.range 4, RunsAt 2 (28+i) := by decide +kernel

private theorem r2part32 : ∀ i ∈ List.range 4, RunsAt 2 (32+i) := by decide +kernel

private theorem r2part36 : ∀ i ∈ List.range 4, RunsAt 2 (36+i) := by decide +kernel

private theorem r2part40 : ∀ i ∈ List.range 4, RunsAt 2 (40+i) := by decide +kernel

private theorem r2part44 : ∀ i ∈ List.range 4, RunsAt 2 (44+i) := by decide +kernel

private theorem r2part48 : ∀ i ∈ List.range 4, RunsAt 2 (48+i) := by decide +kernel

private theorem r2part52 : ∀ i ∈ List.range 4, RunsAt 2 (52+i) := by decide +kernel

private theorem r2part56 : ∀ i ∈ List.range 4, RunsAt 2 (56+i) := by decide +kernel

private theorem r2part60 : ∀ i ∈ List.range 4, RunsAt 2 (60+i) := by decide +kernel

private theorem r2part64 : ∀ i ∈ List.range 4, RunsAt 2 (64+i) := by decide +kernel

private theorem r2part68 : ∀ i ∈ List.range 4, RunsAt 2 (68+i) := by decide +kernel

private theorem r2part72 : ∀ i ∈ List.range 4, RunsAt 2 (72+i) := by decide +kernel

private theorem r2part76 : ∀ i ∈ List.range 4, RunsAt 2 (76+i) := by decide +kernel

private theorem r2part80 : ∀ i ∈ List.range 4, RunsAt 2 (80+i) := by decide +kernel

private theorem r2part84 : ∀ i ∈ List.range 4, RunsAt 2 (84+i) := by decide +kernel

private theorem r2part88 : ∀ i ∈ List.range 4, RunsAt 2 (88+i) := by decide +kernel

private theorem r2part92 : ∀ i ∈ List.range 4, RunsAt 2 (92+i) := by decide +kernel

private theorem r2part96 : ∀ i ∈ List.range 4, RunsAt 2 (96+i) := by decide +kernel

private theorem r2part100 : ∀ i ∈ List.range 4, RunsAt 2 (100+i) := by decide +kernel

private theorem r2part104 : ∀ i ∈ List.range 4, RunsAt 2 (104+i) := by decide +kernel

private theorem r2part108 : ∀ i ∈ List.range 4, RunsAt 2 (108+i) := by decide +kernel

private theorem r2part112 : ∀ i ∈ List.range 4, RunsAt 2 (112+i) := by decide +kernel

private theorem r2part116 : ∀ i ∈ List.range 4, RunsAt 2 (116+i) := by decide +kernel

private theorem r2part120 : ∀ i ∈ List.range 4, RunsAt 2 (120+i) := by decide +kernel

private theorem r2part124 : ∀ i ∈ List.range 4, RunsAt 2 (124+i) := by decide +kernel

private theorem r2part128 : ∀ i ∈ List.range 4, RunsAt 2 (128+i) := by decide +kernel

private theorem r2part132 : ∀ i ∈ List.range 3, RunsAt 2 (132+i) := by decide +kernel

theorem checkedR2 : ∀ V ∈ List.range 135, RunsAt 2 V := by
  intro V hV
  have hlt : V < 135 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r2part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r2part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r2part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r2part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r2part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r2part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r2part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r2part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r2part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r2part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r2part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r2part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r2part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r2part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r2part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r2part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r2part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r2part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r2part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r2part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r2part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r2part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r2part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r2part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r2part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r2part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r2part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r2part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r2part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r2part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r2part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r2part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  by_cases h132 : V < 132
  · have hp := r2part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r2part132 (V-132) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hp

private theorem r3part0 : ∀ i ∈ List.range 4, RunsAt 3 (0+i) := by decide +kernel

private theorem r3part4 : ∀ i ∈ List.range 4, RunsAt 3 (4+i) := by decide +kernel

private theorem r3part8 : ∀ i ∈ List.range 4, RunsAt 3 (8+i) := by decide +kernel

private theorem r3part12 : ∀ i ∈ List.range 4, RunsAt 3 (12+i) := by decide +kernel

private theorem r3part16 : ∀ i ∈ List.range 4, RunsAt 3 (16+i) := by decide +kernel

private theorem r3part20 : ∀ i ∈ List.range 4, RunsAt 3 (20+i) := by decide +kernel

private theorem r3part24 : ∀ i ∈ List.range 4, RunsAt 3 (24+i) := by decide +kernel

private theorem r3part28 : ∀ i ∈ List.range 4, RunsAt 3 (28+i) := by decide +kernel

private theorem r3part32 : ∀ i ∈ List.range 4, RunsAt 3 (32+i) := by decide +kernel

private theorem r3part36 : ∀ i ∈ List.range 4, RunsAt 3 (36+i) := by decide +kernel

private theorem r3part40 : ∀ i ∈ List.range 4, RunsAt 3 (40+i) := by decide +kernel

private theorem r3part44 : ∀ i ∈ List.range 4, RunsAt 3 (44+i) := by decide +kernel

private theorem r3part48 : ∀ i ∈ List.range 4, RunsAt 3 (48+i) := by decide +kernel

private theorem r3part52 : ∀ i ∈ List.range 4, RunsAt 3 (52+i) := by decide +kernel

private theorem r3part56 : ∀ i ∈ List.range 4, RunsAt 3 (56+i) := by decide +kernel

private theorem r3part60 : ∀ i ∈ List.range 4, RunsAt 3 (60+i) := by decide +kernel

private theorem r3part64 : ∀ i ∈ List.range 4, RunsAt 3 (64+i) := by decide +kernel

private theorem r3part68 : ∀ i ∈ List.range 4, RunsAt 3 (68+i) := by decide +kernel

private theorem r3part72 : ∀ i ∈ List.range 4, RunsAt 3 (72+i) := by decide +kernel

private theorem r3part76 : ∀ i ∈ List.range 4, RunsAt 3 (76+i) := by decide +kernel

private theorem r3part80 : ∀ i ∈ List.range 4, RunsAt 3 (80+i) := by decide +kernel

private theorem r3part84 : ∀ i ∈ List.range 4, RunsAt 3 (84+i) := by decide +kernel

private theorem r3part88 : ∀ i ∈ List.range 4, RunsAt 3 (88+i) := by decide +kernel

private theorem r3part92 : ∀ i ∈ List.range 4, RunsAt 3 (92+i) := by decide +kernel

private theorem r3part96 : ∀ i ∈ List.range 4, RunsAt 3 (96+i) := by decide +kernel

private theorem r3part100 : ∀ i ∈ List.range 4, RunsAt 3 (100+i) := by decide +kernel

private theorem r3part104 : ∀ i ∈ List.range 4, RunsAt 3 (104+i) := by decide +kernel

private theorem r3part108 : ∀ i ∈ List.range 4, RunsAt 3 (108+i) := by decide +kernel

private theorem r3part112 : ∀ i ∈ List.range 4, RunsAt 3 (112+i) := by decide +kernel

private theorem r3part116 : ∀ i ∈ List.range 4, RunsAt 3 (116+i) := by decide +kernel

private theorem r3part120 : ∀ i ∈ List.range 4, RunsAt 3 (120+i) := by decide +kernel

private theorem r3part124 : ∀ i ∈ List.range 4, RunsAt 3 (124+i) := by decide +kernel

private theorem r3part128 : ∀ i ∈ List.range 4, RunsAt 3 (128+i) := by decide +kernel

private theorem r3part132 : ∀ i ∈ List.range 2, RunsAt 3 (132+i) := by decide +kernel

theorem checkedR3 : ∀ V ∈ List.range 134, RunsAt 3 V := by
  intro V hV
  have hlt : V < 134 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r3part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r3part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r3part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r3part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r3part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r3part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r3part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r3part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r3part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r3part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r3part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r3part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r3part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r3part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r3part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r3part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r3part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r3part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r3part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r3part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r3part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r3part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r3part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r3part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r3part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r3part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r3part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r3part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r3part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r3part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r3part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r3part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  by_cases h132 : V < 132
  · have hp := r3part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r3part132 (V-132) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hp

private theorem r4part0 : ∀ i ∈ List.range 4, RunsAt 4 (0+i) := by decide +kernel

private theorem r4part4 : ∀ i ∈ List.range 4, RunsAt 4 (4+i) := by decide +kernel

private theorem r4part8 : ∀ i ∈ List.range 4, RunsAt 4 (8+i) := by decide +kernel

private theorem r4part12 : ∀ i ∈ List.range 4, RunsAt 4 (12+i) := by decide +kernel

private theorem r4part16 : ∀ i ∈ List.range 4, RunsAt 4 (16+i) := by decide +kernel

private theorem r4part20 : ∀ i ∈ List.range 4, RunsAt 4 (20+i) := by decide +kernel

private theorem r4part24 : ∀ i ∈ List.range 4, RunsAt 4 (24+i) := by decide +kernel

private theorem r4part28 : ∀ i ∈ List.range 4, RunsAt 4 (28+i) := by decide +kernel

private theorem r4part32 : ∀ i ∈ List.range 4, RunsAt 4 (32+i) := by decide +kernel

private theorem r4part36 : ∀ i ∈ List.range 4, RunsAt 4 (36+i) := by decide +kernel

private theorem r4part40 : ∀ i ∈ List.range 4, RunsAt 4 (40+i) := by decide +kernel

private theorem r4part44 : ∀ i ∈ List.range 4, RunsAt 4 (44+i) := by decide +kernel

private theorem r4part48 : ∀ i ∈ List.range 4, RunsAt 4 (48+i) := by decide +kernel

private theorem r4part52 : ∀ i ∈ List.range 4, RunsAt 4 (52+i) := by decide +kernel

private theorem r4part56 : ∀ i ∈ List.range 4, RunsAt 4 (56+i) := by decide +kernel

private theorem r4part60 : ∀ i ∈ List.range 4, RunsAt 4 (60+i) := by decide +kernel

private theorem r4part64 : ∀ i ∈ List.range 4, RunsAt 4 (64+i) := by decide +kernel

private theorem r4part68 : ∀ i ∈ List.range 4, RunsAt 4 (68+i) := by decide +kernel

private theorem r4part72 : ∀ i ∈ List.range 4, RunsAt 4 (72+i) := by decide +kernel

private theorem r4part76 : ∀ i ∈ List.range 4, RunsAt 4 (76+i) := by decide +kernel

private theorem r4part80 : ∀ i ∈ List.range 4, RunsAt 4 (80+i) := by decide +kernel

private theorem r4part84 : ∀ i ∈ List.range 4, RunsAt 4 (84+i) := by decide +kernel

private theorem r4part88 : ∀ i ∈ List.range 4, RunsAt 4 (88+i) := by decide +kernel

private theorem r4part92 : ∀ i ∈ List.range 4, RunsAt 4 (92+i) := by decide +kernel

private theorem r4part96 : ∀ i ∈ List.range 4, RunsAt 4 (96+i) := by decide +kernel

private theorem r4part100 : ∀ i ∈ List.range 4, RunsAt 4 (100+i) := by decide +kernel

private theorem r4part104 : ∀ i ∈ List.range 4, RunsAt 4 (104+i) := by decide +kernel

private theorem r4part108 : ∀ i ∈ List.range 4, RunsAt 4 (108+i) := by decide +kernel

private theorem r4part112 : ∀ i ∈ List.range 4, RunsAt 4 (112+i) := by decide +kernel

private theorem r4part116 : ∀ i ∈ List.range 4, RunsAt 4 (116+i) := by decide +kernel

private theorem r4part120 : ∀ i ∈ List.range 4, RunsAt 4 (120+i) := by decide +kernel

private theorem r4part124 : ∀ i ∈ List.range 4, RunsAt 4 (124+i) := by decide +kernel

private theorem r4part128 : ∀ i ∈ List.range 4, RunsAt 4 (128+i) := by decide +kernel

private theorem r4part132 : ∀ i ∈ List.range 1, RunsAt 4 (132+i) := by decide +kernel

theorem checkedR4 : ∀ V ∈ List.range 133, RunsAt 4 V := by
  intro V hV
  have hlt : V < 133 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r4part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r4part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r4part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r4part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r4part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r4part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r4part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r4part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r4part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r4part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r4part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r4part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r4part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r4part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r4part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r4part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r4part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r4part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r4part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r4part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r4part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r4part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r4part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r4part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r4part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r4part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r4part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r4part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r4part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r4part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r4part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r4part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  by_cases h132 : V < 132
  · have hp := r4part128 (V-128) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
  have hp := r4part132 (V-132) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using hp

private theorem r5part0 : ∀ i ∈ List.range 4, RunsAt 5 (0+i) := by decide +kernel

private theorem r5part4 : ∀ i ∈ List.range 4, RunsAt 5 (4+i) := by decide +kernel

private theorem r5part8 : ∀ i ∈ List.range 4, RunsAt 5 (8+i) := by decide +kernel

private theorem r5part12 : ∀ i ∈ List.range 4, RunsAt 5 (12+i) := by decide +kernel

private theorem r5part16 : ∀ i ∈ List.range 4, RunsAt 5 (16+i) := by decide +kernel

private theorem r5part20 : ∀ i ∈ List.range 4, RunsAt 5 (20+i) := by decide +kernel

private theorem r5part24 : ∀ i ∈ List.range 4, RunsAt 5 (24+i) := by decide +kernel

private theorem r5part28 : ∀ i ∈ List.range 4, RunsAt 5 (28+i) := by decide +kernel

private theorem r5part32 : ∀ i ∈ List.range 4, RunsAt 5 (32+i) := by decide +kernel

private theorem r5part36 : ∀ i ∈ List.range 4, RunsAt 5 (36+i) := by decide +kernel

private theorem r5part40 : ∀ i ∈ List.range 4, RunsAt 5 (40+i) := by decide +kernel

private theorem r5part44 : ∀ i ∈ List.range 4, RunsAt 5 (44+i) := by decide +kernel

private theorem r5part48 : ∀ i ∈ List.range 4, RunsAt 5 (48+i) := by decide +kernel

private theorem r5part52 : ∀ i ∈ List.range 4, RunsAt 5 (52+i) := by decide +kernel

private theorem r5part56 : ∀ i ∈ List.range 4, RunsAt 5 (56+i) := by decide +kernel

private theorem r5part60 : ∀ i ∈ List.range 4, RunsAt 5 (60+i) := by decide +kernel

private theorem r5part64 : ∀ i ∈ List.range 4, RunsAt 5 (64+i) := by decide +kernel

private theorem r5part68 : ∀ i ∈ List.range 4, RunsAt 5 (68+i) := by decide +kernel

private theorem r5part72 : ∀ i ∈ List.range 4, RunsAt 5 (72+i) := by decide +kernel

private theorem r5part76 : ∀ i ∈ List.range 4, RunsAt 5 (76+i) := by decide +kernel

private theorem r5part80 : ∀ i ∈ List.range 4, RunsAt 5 (80+i) := by decide +kernel

private theorem r5part84 : ∀ i ∈ List.range 4, RunsAt 5 (84+i) := by decide +kernel

private theorem r5part88 : ∀ i ∈ List.range 4, RunsAt 5 (88+i) := by decide +kernel

private theorem r5part92 : ∀ i ∈ List.range 4, RunsAt 5 (92+i) := by decide +kernel

private theorem r5part96 : ∀ i ∈ List.range 4, RunsAt 5 (96+i) := by decide +kernel

private theorem r5part100 : ∀ i ∈ List.range 4, RunsAt 5 (100+i) := by decide +kernel

private theorem r5part104 : ∀ i ∈ List.range 4, RunsAt 5 (104+i) := by decide +kernel

private theorem r5part108 : ∀ i ∈ List.range 4, RunsAt 5 (108+i) := by decide +kernel

private theorem r5part112 : ∀ i ∈ List.range 4, RunsAt 5 (112+i) := by decide +kernel

private theorem r5part116 : ∀ i ∈ List.range 4, RunsAt 5 (116+i) := by decide +kernel

private theorem r5part120 : ∀ i ∈ List.range 4, RunsAt 5 (120+i) := by decide +kernel

private theorem r5part124 : ∀ i ∈ List.range 4, RunsAt 5 (124+i) := by decide +kernel

private theorem r5part128 : ∀ i ∈ List.range 4, RunsAt 5 (128+i) := by decide +kernel

theorem checkedR5 : ∀ V ∈ List.range 132, RunsAt 5 V := by
  intro V hV
  have hlt : V < 132 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r5part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r5part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r5part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r5part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r5part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r5part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r5part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r5part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r5part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r5part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r5part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r5part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r5part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r5part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r5part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r5part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r5part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r5part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r5part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r5part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r5part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r5part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r5part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r5part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r5part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r5part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r5part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r5part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r5part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r5part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r5part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r5part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  have hp := r5part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r6part0 : ∀ i ∈ List.range 4, RunsAt 6 (0+i) := by decide +kernel

private theorem r6part4 : ∀ i ∈ List.range 4, RunsAt 6 (4+i) := by decide +kernel

private theorem r6part8 : ∀ i ∈ List.range 4, RunsAt 6 (8+i) := by decide +kernel

private theorem r6part12 : ∀ i ∈ List.range 4, RunsAt 6 (12+i) := by decide +kernel

private theorem r6part16 : ∀ i ∈ List.range 4, RunsAt 6 (16+i) := by decide +kernel

private theorem r6part20 : ∀ i ∈ List.range 4, RunsAt 6 (20+i) := by decide +kernel

private theorem r6part24 : ∀ i ∈ List.range 4, RunsAt 6 (24+i) := by decide +kernel

private theorem r6part28 : ∀ i ∈ List.range 4, RunsAt 6 (28+i) := by decide +kernel

private theorem r6part32 : ∀ i ∈ List.range 4, RunsAt 6 (32+i) := by decide +kernel

private theorem r6part36 : ∀ i ∈ List.range 4, RunsAt 6 (36+i) := by decide +kernel

private theorem r6part40 : ∀ i ∈ List.range 4, RunsAt 6 (40+i) := by decide +kernel

private theorem r6part44 : ∀ i ∈ List.range 4, RunsAt 6 (44+i) := by decide +kernel

private theorem r6part48 : ∀ i ∈ List.range 4, RunsAt 6 (48+i) := by decide +kernel

private theorem r6part52 : ∀ i ∈ List.range 4, RunsAt 6 (52+i) := by decide +kernel

private theorem r6part56 : ∀ i ∈ List.range 4, RunsAt 6 (56+i) := by decide +kernel

private theorem r6part60 : ∀ i ∈ List.range 4, RunsAt 6 (60+i) := by decide +kernel

private theorem r6part64 : ∀ i ∈ List.range 4, RunsAt 6 (64+i) := by decide +kernel

private theorem r6part68 : ∀ i ∈ List.range 4, RunsAt 6 (68+i) := by decide +kernel

private theorem r6part72 : ∀ i ∈ List.range 4, RunsAt 6 (72+i) := by decide +kernel

private theorem r6part76 : ∀ i ∈ List.range 4, RunsAt 6 (76+i) := by decide +kernel

private theorem r6part80 : ∀ i ∈ List.range 4, RunsAt 6 (80+i) := by decide +kernel

private theorem r6part84 : ∀ i ∈ List.range 4, RunsAt 6 (84+i) := by decide +kernel

private theorem r6part88 : ∀ i ∈ List.range 4, RunsAt 6 (88+i) := by decide +kernel

private theorem r6part92 : ∀ i ∈ List.range 4, RunsAt 6 (92+i) := by decide +kernel

private theorem r6part96 : ∀ i ∈ List.range 4, RunsAt 6 (96+i) := by decide +kernel

private theorem r6part100 : ∀ i ∈ List.range 4, RunsAt 6 (100+i) := by decide +kernel

private theorem r6part104 : ∀ i ∈ List.range 4, RunsAt 6 (104+i) := by decide +kernel

private theorem r6part108 : ∀ i ∈ List.range 4, RunsAt 6 (108+i) := by decide +kernel

private theorem r6part112 : ∀ i ∈ List.range 4, RunsAt 6 (112+i) := by decide +kernel

private theorem r6part116 : ∀ i ∈ List.range 4, RunsAt 6 (116+i) := by decide +kernel

private theorem r6part120 : ∀ i ∈ List.range 4, RunsAt 6 (120+i) := by decide +kernel

private theorem r6part124 : ∀ i ∈ List.range 4, RunsAt 6 (124+i) := by decide +kernel

private theorem r6part128 : ∀ i ∈ List.range 3, RunsAt 6 (128+i) := by decide +kernel

theorem checkedR6 : ∀ V ∈ List.range 131, RunsAt 6 V := by
  intro V hV
  have hlt : V < 131 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r6part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r6part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r6part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r6part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r6part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r6part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r6part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r6part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r6part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r6part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r6part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r6part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r6part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r6part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r6part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r6part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r6part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r6part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r6part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r6part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r6part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r6part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r6part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r6part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r6part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r6part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r6part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r6part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r6part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r6part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r6part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r6part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  have hp := r6part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r7part0 : ∀ i ∈ List.range 4, RunsAt 7 (0+i) := by decide +kernel

private theorem r7part4 : ∀ i ∈ List.range 4, RunsAt 7 (4+i) := by decide +kernel

private theorem r7part8 : ∀ i ∈ List.range 4, RunsAt 7 (8+i) := by decide +kernel

private theorem r7part12 : ∀ i ∈ List.range 4, RunsAt 7 (12+i) := by decide +kernel

private theorem r7part16 : ∀ i ∈ List.range 4, RunsAt 7 (16+i) := by decide +kernel

private theorem r7part20 : ∀ i ∈ List.range 4, RunsAt 7 (20+i) := by decide +kernel

private theorem r7part24 : ∀ i ∈ List.range 4, RunsAt 7 (24+i) := by decide +kernel

private theorem r7part28 : ∀ i ∈ List.range 4, RunsAt 7 (28+i) := by decide +kernel

private theorem r7part32 : ∀ i ∈ List.range 4, RunsAt 7 (32+i) := by decide +kernel

private theorem r7part36 : ∀ i ∈ List.range 4, RunsAt 7 (36+i) := by decide +kernel

private theorem r7part40 : ∀ i ∈ List.range 4, RunsAt 7 (40+i) := by decide +kernel

private theorem r7part44 : ∀ i ∈ List.range 4, RunsAt 7 (44+i) := by decide +kernel

private theorem r7part48 : ∀ i ∈ List.range 4, RunsAt 7 (48+i) := by decide +kernel

private theorem r7part52 : ∀ i ∈ List.range 4, RunsAt 7 (52+i) := by decide +kernel

private theorem r7part56 : ∀ i ∈ List.range 4, RunsAt 7 (56+i) := by decide +kernel

private theorem r7part60 : ∀ i ∈ List.range 4, RunsAt 7 (60+i) := by decide +kernel

private theorem r7part64 : ∀ i ∈ List.range 4, RunsAt 7 (64+i) := by decide +kernel

private theorem r7part68 : ∀ i ∈ List.range 4, RunsAt 7 (68+i) := by decide +kernel

private theorem r7part72 : ∀ i ∈ List.range 4, RunsAt 7 (72+i) := by decide +kernel

private theorem r7part76 : ∀ i ∈ List.range 4, RunsAt 7 (76+i) := by decide +kernel

private theorem r7part80 : ∀ i ∈ List.range 4, RunsAt 7 (80+i) := by decide +kernel

private theorem r7part84 : ∀ i ∈ List.range 4, RunsAt 7 (84+i) := by decide +kernel

private theorem r7part88 : ∀ i ∈ List.range 4, RunsAt 7 (88+i) := by decide +kernel

private theorem r7part92 : ∀ i ∈ List.range 4, RunsAt 7 (92+i) := by decide +kernel

private theorem r7part96 : ∀ i ∈ List.range 4, RunsAt 7 (96+i) := by decide +kernel

private theorem r7part100 : ∀ i ∈ List.range 4, RunsAt 7 (100+i) := by decide +kernel

private theorem r7part104 : ∀ i ∈ List.range 4, RunsAt 7 (104+i) := by decide +kernel

private theorem r7part108 : ∀ i ∈ List.range 4, RunsAt 7 (108+i) := by decide +kernel

private theorem r7part112 : ∀ i ∈ List.range 4, RunsAt 7 (112+i) := by decide +kernel

private theorem r7part116 : ∀ i ∈ List.range 4, RunsAt 7 (116+i) := by decide +kernel

private theorem r7part120 : ∀ i ∈ List.range 4, RunsAt 7 (120+i) := by decide +kernel

private theorem r7part124 : ∀ i ∈ List.range 4, RunsAt 7 (124+i) := by decide +kernel

private theorem r7part128 : ∀ i ∈ List.range 2, RunsAt 7 (128+i) := by decide +kernel

theorem checkedR7 : ∀ V ∈ List.range 130, RunsAt 7 V := by
  intro V hV
  have hlt : V < 130 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r7part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r7part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r7part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r7part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r7part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r7part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r7part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r7part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r7part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r7part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r7part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r7part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r7part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r7part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r7part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r7part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r7part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r7part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r7part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r7part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r7part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r7part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r7part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r7part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r7part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r7part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r7part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r7part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r7part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r7part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r7part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r7part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  have hp := r7part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r8part0 : ∀ i ∈ List.range 4, RunsAt 8 (0+i) := by decide +kernel

private theorem r8part4 : ∀ i ∈ List.range 4, RunsAt 8 (4+i) := by decide +kernel

private theorem r8part8 : ∀ i ∈ List.range 4, RunsAt 8 (8+i) := by decide +kernel

private theorem r8part12 : ∀ i ∈ List.range 4, RunsAt 8 (12+i) := by decide +kernel

private theorem r8part16 : ∀ i ∈ List.range 4, RunsAt 8 (16+i) := by decide +kernel

private theorem r8part20 : ∀ i ∈ List.range 4, RunsAt 8 (20+i) := by decide +kernel

private theorem r8part24 : ∀ i ∈ List.range 4, RunsAt 8 (24+i) := by decide +kernel

private theorem r8part28 : ∀ i ∈ List.range 4, RunsAt 8 (28+i) := by decide +kernel

private theorem r8part32 : ∀ i ∈ List.range 4, RunsAt 8 (32+i) := by decide +kernel

private theorem r8part36 : ∀ i ∈ List.range 4, RunsAt 8 (36+i) := by decide +kernel

private theorem r8part40 : ∀ i ∈ List.range 4, RunsAt 8 (40+i) := by decide +kernel

private theorem r8part44 : ∀ i ∈ List.range 4, RunsAt 8 (44+i) := by decide +kernel

private theorem r8part48 : ∀ i ∈ List.range 4, RunsAt 8 (48+i) := by decide +kernel

private theorem r8part52 : ∀ i ∈ List.range 4, RunsAt 8 (52+i) := by decide +kernel

private theorem r8part56 : ∀ i ∈ List.range 4, RunsAt 8 (56+i) := by decide +kernel

private theorem r8part60 : ∀ i ∈ List.range 4, RunsAt 8 (60+i) := by decide +kernel

private theorem r8part64 : ∀ i ∈ List.range 4, RunsAt 8 (64+i) := by decide +kernel

private theorem r8part68 : ∀ i ∈ List.range 4, RunsAt 8 (68+i) := by decide +kernel

private theorem r8part72 : ∀ i ∈ List.range 4, RunsAt 8 (72+i) := by decide +kernel

private theorem r8part76 : ∀ i ∈ List.range 4, RunsAt 8 (76+i) := by decide +kernel

private theorem r8part80 : ∀ i ∈ List.range 4, RunsAt 8 (80+i) := by decide +kernel

private theorem r8part84 : ∀ i ∈ List.range 4, RunsAt 8 (84+i) := by decide +kernel

private theorem r8part88 : ∀ i ∈ List.range 4, RunsAt 8 (88+i) := by decide +kernel

private theorem r8part92 : ∀ i ∈ List.range 4, RunsAt 8 (92+i) := by decide +kernel

private theorem r8part96 : ∀ i ∈ List.range 4, RunsAt 8 (96+i) := by decide +kernel

private theorem r8part100 : ∀ i ∈ List.range 4, RunsAt 8 (100+i) := by decide +kernel

private theorem r8part104 : ∀ i ∈ List.range 4, RunsAt 8 (104+i) := by decide +kernel

private theorem r8part108 : ∀ i ∈ List.range 4, RunsAt 8 (108+i) := by decide +kernel

private theorem r8part112 : ∀ i ∈ List.range 4, RunsAt 8 (112+i) := by decide +kernel

private theorem r8part116 : ∀ i ∈ List.range 4, RunsAt 8 (116+i) := by decide +kernel

private theorem r8part120 : ∀ i ∈ List.range 4, RunsAt 8 (120+i) := by decide +kernel

private theorem r8part124 : ∀ i ∈ List.range 4, RunsAt 8 (124+i) := by decide +kernel

private theorem r8part128 : ∀ i ∈ List.range 1, RunsAt 8 (128+i) := by decide +kernel

theorem checkedR8 : ∀ V ∈ List.range 129, RunsAt 8 V := by
  intro V hV
  have hlt : V < 129 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r8part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r8part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r8part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r8part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r8part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r8part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r8part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r8part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r8part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r8part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r8part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r8part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r8part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r8part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r8part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r8part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r8part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r8part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r8part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r8part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r8part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r8part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r8part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r8part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r8part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r8part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r8part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r8part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r8part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r8part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r8part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  by_cases h128 : V < 128
  · have hp := r8part124 (V-124) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp
  have hp := r8part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp

private theorem r9part0 : ∀ i ∈ List.range 4, RunsAt 9 (0+i) := by decide +kernel

private theorem r9part4 : ∀ i ∈ List.range 4, RunsAt 9 (4+i) := by decide +kernel

private theorem r9part8 : ∀ i ∈ List.range 4, RunsAt 9 (8+i) := by decide +kernel

private theorem r9part12 : ∀ i ∈ List.range 4, RunsAt 9 (12+i) := by decide +kernel

private theorem r9part16 : ∀ i ∈ List.range 4, RunsAt 9 (16+i) := by decide +kernel

private theorem r9part20 : ∀ i ∈ List.range 4, RunsAt 9 (20+i) := by decide +kernel

private theorem r9part24 : ∀ i ∈ List.range 4, RunsAt 9 (24+i) := by decide +kernel

private theorem r9part28 : ∀ i ∈ List.range 4, RunsAt 9 (28+i) := by decide +kernel

private theorem r9part32 : ∀ i ∈ List.range 4, RunsAt 9 (32+i) := by decide +kernel

private theorem r9part36 : ∀ i ∈ List.range 4, RunsAt 9 (36+i) := by decide +kernel

private theorem r9part40 : ∀ i ∈ List.range 4, RunsAt 9 (40+i) := by decide +kernel

private theorem r9part44 : ∀ i ∈ List.range 4, RunsAt 9 (44+i) := by decide +kernel

private theorem r9part48 : ∀ i ∈ List.range 4, RunsAt 9 (48+i) := by decide +kernel

private theorem r9part52 : ∀ i ∈ List.range 4, RunsAt 9 (52+i) := by decide +kernel

private theorem r9part56 : ∀ i ∈ List.range 4, RunsAt 9 (56+i) := by decide +kernel

private theorem r9part60 : ∀ i ∈ List.range 4, RunsAt 9 (60+i) := by decide +kernel

private theorem r9part64 : ∀ i ∈ List.range 4, RunsAt 9 (64+i) := by decide +kernel

private theorem r9part68 : ∀ i ∈ List.range 4, RunsAt 9 (68+i) := by decide +kernel

private theorem r9part72 : ∀ i ∈ List.range 4, RunsAt 9 (72+i) := by decide +kernel

private theorem r9part76 : ∀ i ∈ List.range 4, RunsAt 9 (76+i) := by decide +kernel

private theorem r9part80 : ∀ i ∈ List.range 4, RunsAt 9 (80+i) := by decide +kernel

private theorem r9part84 : ∀ i ∈ List.range 4, RunsAt 9 (84+i) := by decide +kernel

private theorem r9part88 : ∀ i ∈ List.range 4, RunsAt 9 (88+i) := by decide +kernel

private theorem r9part92 : ∀ i ∈ List.range 4, RunsAt 9 (92+i) := by decide +kernel

private theorem r9part96 : ∀ i ∈ List.range 4, RunsAt 9 (96+i) := by decide +kernel

private theorem r9part100 : ∀ i ∈ List.range 4, RunsAt 9 (100+i) := by decide +kernel

private theorem r9part104 : ∀ i ∈ List.range 4, RunsAt 9 (104+i) := by decide +kernel

private theorem r9part108 : ∀ i ∈ List.range 4, RunsAt 9 (108+i) := by decide +kernel

private theorem r9part112 : ∀ i ∈ List.range 4, RunsAt 9 (112+i) := by decide +kernel

private theorem r9part116 : ∀ i ∈ List.range 4, RunsAt 9 (116+i) := by decide +kernel

private theorem r9part120 : ∀ i ∈ List.range 4, RunsAt 9 (120+i) := by decide +kernel

private theorem r9part124 : ∀ i ∈ List.range 4, RunsAt 9 (124+i) := by decide +kernel

theorem checkedR9 : ∀ V ∈ List.range 128, RunsAt 9 V := by
  intro V hV
  have hlt : V < 128 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r9part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r9part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r9part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r9part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r9part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r9part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r9part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r9part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r9part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r9part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r9part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r9part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r9part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r9part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r9part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r9part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r9part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r9part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r9part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r9part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r9part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r9part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r9part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r9part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r9part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r9part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r9part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r9part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r9part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r9part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r9part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r9part124 (V-124) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp

private theorem r10part0 : ∀ i ∈ List.range 4, RunsAt 10 (0+i) := by decide +kernel

private theorem r10part4 : ∀ i ∈ List.range 4, RunsAt 10 (4+i) := by decide +kernel

private theorem r10part8 : ∀ i ∈ List.range 4, RunsAt 10 (8+i) := by decide +kernel

private theorem r10part12 : ∀ i ∈ List.range 4, RunsAt 10 (12+i) := by decide +kernel

private theorem r10part16 : ∀ i ∈ List.range 4, RunsAt 10 (16+i) := by decide +kernel

private theorem r10part20 : ∀ i ∈ List.range 4, RunsAt 10 (20+i) := by decide +kernel

private theorem r10part24 : ∀ i ∈ List.range 4, RunsAt 10 (24+i) := by decide +kernel

private theorem r10part28 : ∀ i ∈ List.range 4, RunsAt 10 (28+i) := by decide +kernel

private theorem r10part32 : ∀ i ∈ List.range 4, RunsAt 10 (32+i) := by decide +kernel

private theorem r10part36 : ∀ i ∈ List.range 4, RunsAt 10 (36+i) := by decide +kernel

private theorem r10part40 : ∀ i ∈ List.range 4, RunsAt 10 (40+i) := by decide +kernel

private theorem r10part44 : ∀ i ∈ List.range 4, RunsAt 10 (44+i) := by decide +kernel

private theorem r10part48 : ∀ i ∈ List.range 4, RunsAt 10 (48+i) := by decide +kernel

private theorem r10part52 : ∀ i ∈ List.range 4, RunsAt 10 (52+i) := by decide +kernel

private theorem r10part56 : ∀ i ∈ List.range 4, RunsAt 10 (56+i) := by decide +kernel

private theorem r10part60 : ∀ i ∈ List.range 4, RunsAt 10 (60+i) := by decide +kernel

private theorem r10part64 : ∀ i ∈ List.range 4, RunsAt 10 (64+i) := by decide +kernel

private theorem r10part68 : ∀ i ∈ List.range 4, RunsAt 10 (68+i) := by decide +kernel

private theorem r10part72 : ∀ i ∈ List.range 4, RunsAt 10 (72+i) := by decide +kernel

private theorem r10part76 : ∀ i ∈ List.range 4, RunsAt 10 (76+i) := by decide +kernel

private theorem r10part80 : ∀ i ∈ List.range 4, RunsAt 10 (80+i) := by decide +kernel

private theorem r10part84 : ∀ i ∈ List.range 4, RunsAt 10 (84+i) := by decide +kernel

private theorem r10part88 : ∀ i ∈ List.range 4, RunsAt 10 (88+i) := by decide +kernel

private theorem r10part92 : ∀ i ∈ List.range 4, RunsAt 10 (92+i) := by decide +kernel

private theorem r10part96 : ∀ i ∈ List.range 4, RunsAt 10 (96+i) := by decide +kernel

private theorem r10part100 : ∀ i ∈ List.range 4, RunsAt 10 (100+i) := by decide +kernel

private theorem r10part104 : ∀ i ∈ List.range 4, RunsAt 10 (104+i) := by decide +kernel

private theorem r10part108 : ∀ i ∈ List.range 4, RunsAt 10 (108+i) := by decide +kernel

private theorem r10part112 : ∀ i ∈ List.range 4, RunsAt 10 (112+i) := by decide +kernel

private theorem r10part116 : ∀ i ∈ List.range 4, RunsAt 10 (116+i) := by decide +kernel

private theorem r10part120 : ∀ i ∈ List.range 4, RunsAt 10 (120+i) := by decide +kernel

private theorem r10part124 : ∀ i ∈ List.range 3, RunsAt 10 (124+i) := by decide +kernel

theorem checkedR10 : ∀ V ∈ List.range 127, RunsAt 10 V := by
  intro V hV
  have hlt : V < 127 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r10part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r10part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r10part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r10part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r10part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r10part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r10part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r10part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r10part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r10part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r10part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r10part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r10part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r10part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r10part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r10part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r10part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r10part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r10part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r10part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r10part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r10part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r10part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r10part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r10part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r10part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r10part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r10part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r10part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r10part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r10part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r10part124 (V-124) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp

private theorem r11part0 : ∀ i ∈ List.range 4, RunsAt 11 (0+i) := by decide +kernel

private theorem r11part4 : ∀ i ∈ List.range 4, RunsAt 11 (4+i) := by decide +kernel

private theorem r11part8 : ∀ i ∈ List.range 4, RunsAt 11 (8+i) := by decide +kernel

private theorem r11part12 : ∀ i ∈ List.range 4, RunsAt 11 (12+i) := by decide +kernel

private theorem r11part16 : ∀ i ∈ List.range 4, RunsAt 11 (16+i) := by decide +kernel

private theorem r11part20 : ∀ i ∈ List.range 4, RunsAt 11 (20+i) := by decide +kernel

private theorem r11part24 : ∀ i ∈ List.range 4, RunsAt 11 (24+i) := by decide +kernel

private theorem r11part28 : ∀ i ∈ List.range 4, RunsAt 11 (28+i) := by decide +kernel

private theorem r11part32 : ∀ i ∈ List.range 4, RunsAt 11 (32+i) := by decide +kernel

private theorem r11part36 : ∀ i ∈ List.range 4, RunsAt 11 (36+i) := by decide +kernel

private theorem r11part40 : ∀ i ∈ List.range 4, RunsAt 11 (40+i) := by decide +kernel

private theorem r11part44 : ∀ i ∈ List.range 4, RunsAt 11 (44+i) := by decide +kernel

private theorem r11part48 : ∀ i ∈ List.range 4, RunsAt 11 (48+i) := by decide +kernel

private theorem r11part52 : ∀ i ∈ List.range 4, RunsAt 11 (52+i) := by decide +kernel

private theorem r11part56 : ∀ i ∈ List.range 4, RunsAt 11 (56+i) := by decide +kernel

private theorem r11part60 : ∀ i ∈ List.range 4, RunsAt 11 (60+i) := by decide +kernel

private theorem r11part64 : ∀ i ∈ List.range 4, RunsAt 11 (64+i) := by decide +kernel

private theorem r11part68 : ∀ i ∈ List.range 4, RunsAt 11 (68+i) := by decide +kernel

private theorem r11part72 : ∀ i ∈ List.range 4, RunsAt 11 (72+i) := by decide +kernel

private theorem r11part76 : ∀ i ∈ List.range 4, RunsAt 11 (76+i) := by decide +kernel

private theorem r11part80 : ∀ i ∈ List.range 4, RunsAt 11 (80+i) := by decide +kernel

private theorem r11part84 : ∀ i ∈ List.range 4, RunsAt 11 (84+i) := by decide +kernel

private theorem r11part88 : ∀ i ∈ List.range 4, RunsAt 11 (88+i) := by decide +kernel

private theorem r11part92 : ∀ i ∈ List.range 4, RunsAt 11 (92+i) := by decide +kernel

private theorem r11part96 : ∀ i ∈ List.range 4, RunsAt 11 (96+i) := by decide +kernel

private theorem r11part100 : ∀ i ∈ List.range 4, RunsAt 11 (100+i) := by decide +kernel

private theorem r11part104 : ∀ i ∈ List.range 4, RunsAt 11 (104+i) := by decide +kernel

private theorem r11part108 : ∀ i ∈ List.range 4, RunsAt 11 (108+i) := by decide +kernel

private theorem r11part112 : ∀ i ∈ List.range 4, RunsAt 11 (112+i) := by decide +kernel

private theorem r11part116 : ∀ i ∈ List.range 4, RunsAt 11 (116+i) := by decide +kernel

private theorem r11part120 : ∀ i ∈ List.range 4, RunsAt 11 (120+i) := by decide +kernel

private theorem r11part124 : ∀ i ∈ List.range 2, RunsAt 11 (124+i) := by decide +kernel

theorem checkedR11 : ∀ V ∈ List.range 126, RunsAt 11 V := by
  intro V hV
  have hlt : V < 126 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r11part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r11part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r11part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r11part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r11part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r11part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r11part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r11part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r11part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r11part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r11part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r11part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r11part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r11part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r11part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r11part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r11part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r11part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r11part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r11part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r11part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r11part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r11part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r11part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r11part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r11part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r11part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r11part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r11part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r11part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r11part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r11part124 (V-124) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp

private theorem r12part0 : ∀ i ∈ List.range 4, RunsAt 12 (0+i) := by decide +kernel

private theorem r12part4 : ∀ i ∈ List.range 4, RunsAt 12 (4+i) := by decide +kernel

private theorem r12part8 : ∀ i ∈ List.range 4, RunsAt 12 (8+i) := by decide +kernel

private theorem r12part12 : ∀ i ∈ List.range 4, RunsAt 12 (12+i) := by decide +kernel

private theorem r12part16 : ∀ i ∈ List.range 4, RunsAt 12 (16+i) := by decide +kernel

private theorem r12part20 : ∀ i ∈ List.range 4, RunsAt 12 (20+i) := by decide +kernel

private theorem r12part24 : ∀ i ∈ List.range 4, RunsAt 12 (24+i) := by decide +kernel

private theorem r12part28 : ∀ i ∈ List.range 4, RunsAt 12 (28+i) := by decide +kernel

private theorem r12part32 : ∀ i ∈ List.range 4, RunsAt 12 (32+i) := by decide +kernel

private theorem r12part36 : ∀ i ∈ List.range 4, RunsAt 12 (36+i) := by decide +kernel

private theorem r12part40 : ∀ i ∈ List.range 4, RunsAt 12 (40+i) := by decide +kernel

private theorem r12part44 : ∀ i ∈ List.range 4, RunsAt 12 (44+i) := by decide +kernel

private theorem r12part48 : ∀ i ∈ List.range 4, RunsAt 12 (48+i) := by decide +kernel

private theorem r12part52 : ∀ i ∈ List.range 4, RunsAt 12 (52+i) := by decide +kernel

private theorem r12part56 : ∀ i ∈ List.range 4, RunsAt 12 (56+i) := by decide +kernel

private theorem r12part60 : ∀ i ∈ List.range 4, RunsAt 12 (60+i) := by decide +kernel

private theorem r12part64 : ∀ i ∈ List.range 4, RunsAt 12 (64+i) := by decide +kernel

private theorem r12part68 : ∀ i ∈ List.range 4, RunsAt 12 (68+i) := by decide +kernel

private theorem r12part72 : ∀ i ∈ List.range 4, RunsAt 12 (72+i) := by decide +kernel

private theorem r12part76 : ∀ i ∈ List.range 4, RunsAt 12 (76+i) := by decide +kernel

private theorem r12part80 : ∀ i ∈ List.range 4, RunsAt 12 (80+i) := by decide +kernel

private theorem r12part84 : ∀ i ∈ List.range 4, RunsAt 12 (84+i) := by decide +kernel

private theorem r12part88 : ∀ i ∈ List.range 4, RunsAt 12 (88+i) := by decide +kernel

private theorem r12part92 : ∀ i ∈ List.range 4, RunsAt 12 (92+i) := by decide +kernel

private theorem r12part96 : ∀ i ∈ List.range 4, RunsAt 12 (96+i) := by decide +kernel

private theorem r12part100 : ∀ i ∈ List.range 4, RunsAt 12 (100+i) := by decide +kernel

private theorem r12part104 : ∀ i ∈ List.range 4, RunsAt 12 (104+i) := by decide +kernel

private theorem r12part108 : ∀ i ∈ List.range 4, RunsAt 12 (108+i) := by decide +kernel

private theorem r12part112 : ∀ i ∈ List.range 4, RunsAt 12 (112+i) := by decide +kernel

private theorem r12part116 : ∀ i ∈ List.range 4, RunsAt 12 (116+i) := by decide +kernel

private theorem r12part120 : ∀ i ∈ List.range 4, RunsAt 12 (120+i) := by decide +kernel

private theorem r12part124 : ∀ i ∈ List.range 1, RunsAt 12 (124+i) := by decide +kernel

theorem checkedR12 : ∀ V ∈ List.range 125, RunsAt 12 V := by
  intro V hV
  have hlt : V < 125 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r12part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r12part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r12part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r12part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r12part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r12part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r12part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r12part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r12part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r12part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r12part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r12part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r12part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r12part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r12part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r12part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r12part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r12part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r12part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r12part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r12part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r12part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r12part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r12part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r12part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r12part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r12part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r12part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r12part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r12part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  by_cases h124 : V < 124
  · have hp := r12part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r12part124 (V-124) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using hp

private theorem r13part0 : ∀ i ∈ List.range 4, RunsAt 13 (0+i) := by decide +kernel

private theorem r13part4 : ∀ i ∈ List.range 4, RunsAt 13 (4+i) := by decide +kernel

private theorem r13part8 : ∀ i ∈ List.range 4, RunsAt 13 (8+i) := by decide +kernel

private theorem r13part12 : ∀ i ∈ List.range 4, RunsAt 13 (12+i) := by decide +kernel

private theorem r13part16 : ∀ i ∈ List.range 4, RunsAt 13 (16+i) := by decide +kernel

private theorem r13part20 : ∀ i ∈ List.range 4, RunsAt 13 (20+i) := by decide +kernel

private theorem r13part24 : ∀ i ∈ List.range 4, RunsAt 13 (24+i) := by decide +kernel

private theorem r13part28 : ∀ i ∈ List.range 4, RunsAt 13 (28+i) := by decide +kernel

private theorem r13part32 : ∀ i ∈ List.range 4, RunsAt 13 (32+i) := by decide +kernel

private theorem r13part36 : ∀ i ∈ List.range 4, RunsAt 13 (36+i) := by decide +kernel

private theorem r13part40 : ∀ i ∈ List.range 4, RunsAt 13 (40+i) := by decide +kernel

private theorem r13part44 : ∀ i ∈ List.range 4, RunsAt 13 (44+i) := by decide +kernel

private theorem r13part48 : ∀ i ∈ List.range 4, RunsAt 13 (48+i) := by decide +kernel

private theorem r13part52 : ∀ i ∈ List.range 4, RunsAt 13 (52+i) := by decide +kernel

private theorem r13part56 : ∀ i ∈ List.range 4, RunsAt 13 (56+i) := by decide +kernel

private theorem r13part60 : ∀ i ∈ List.range 4, RunsAt 13 (60+i) := by decide +kernel

private theorem r13part64 : ∀ i ∈ List.range 4, RunsAt 13 (64+i) := by decide +kernel

private theorem r13part68 : ∀ i ∈ List.range 4, RunsAt 13 (68+i) := by decide +kernel

private theorem r13part72 : ∀ i ∈ List.range 4, RunsAt 13 (72+i) := by decide +kernel

private theorem r13part76 : ∀ i ∈ List.range 4, RunsAt 13 (76+i) := by decide +kernel

private theorem r13part80 : ∀ i ∈ List.range 4, RunsAt 13 (80+i) := by decide +kernel

private theorem r13part84 : ∀ i ∈ List.range 4, RunsAt 13 (84+i) := by decide +kernel

private theorem r13part88 : ∀ i ∈ List.range 4, RunsAt 13 (88+i) := by decide +kernel

private theorem r13part92 : ∀ i ∈ List.range 4, RunsAt 13 (92+i) := by decide +kernel

private theorem r13part96 : ∀ i ∈ List.range 4, RunsAt 13 (96+i) := by decide +kernel

private theorem r13part100 : ∀ i ∈ List.range 4, RunsAt 13 (100+i) := by decide +kernel

private theorem r13part104 : ∀ i ∈ List.range 4, RunsAt 13 (104+i) := by decide +kernel

private theorem r13part108 : ∀ i ∈ List.range 4, RunsAt 13 (108+i) := by decide +kernel

private theorem r13part112 : ∀ i ∈ List.range 4, RunsAt 13 (112+i) := by decide +kernel

private theorem r13part116 : ∀ i ∈ List.range 4, RunsAt 13 (116+i) := by decide +kernel

private theorem r13part120 : ∀ i ∈ List.range 4, RunsAt 13 (120+i) := by decide +kernel

theorem checkedR13 : ∀ V ∈ List.range 124, RunsAt 13 V := by
  intro V hV
  have hlt : V < 124 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r13part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r13part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r13part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r13part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r13part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r13part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r13part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r13part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r13part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r13part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r13part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r13part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r13part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r13part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r13part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r13part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r13part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r13part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r13part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r13part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r13part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r13part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r13part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r13part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r13part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r13part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r13part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r13part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r13part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r13part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  have hp := r13part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r14part0 : ∀ i ∈ List.range 4, RunsAt 14 (0+i) := by decide +kernel

private theorem r14part4 : ∀ i ∈ List.range 4, RunsAt 14 (4+i) := by decide +kernel

private theorem r14part8 : ∀ i ∈ List.range 4, RunsAt 14 (8+i) := by decide +kernel

private theorem r14part12 : ∀ i ∈ List.range 4, RunsAt 14 (12+i) := by decide +kernel

private theorem r14part16 : ∀ i ∈ List.range 4, RunsAt 14 (16+i) := by decide +kernel

private theorem r14part20 : ∀ i ∈ List.range 4, RunsAt 14 (20+i) := by decide +kernel

private theorem r14part24 : ∀ i ∈ List.range 4, RunsAt 14 (24+i) := by decide +kernel

private theorem r14part28 : ∀ i ∈ List.range 4, RunsAt 14 (28+i) := by decide +kernel

private theorem r14part32 : ∀ i ∈ List.range 4, RunsAt 14 (32+i) := by decide +kernel

private theorem r14part36 : ∀ i ∈ List.range 4, RunsAt 14 (36+i) := by decide +kernel

private theorem r14part40 : ∀ i ∈ List.range 4, RunsAt 14 (40+i) := by decide +kernel

private theorem r14part44 : ∀ i ∈ List.range 4, RunsAt 14 (44+i) := by decide +kernel

private theorem r14part48 : ∀ i ∈ List.range 4, RunsAt 14 (48+i) := by decide +kernel

private theorem r14part52 : ∀ i ∈ List.range 4, RunsAt 14 (52+i) := by decide +kernel

private theorem r14part56 : ∀ i ∈ List.range 4, RunsAt 14 (56+i) := by decide +kernel

private theorem r14part60 : ∀ i ∈ List.range 4, RunsAt 14 (60+i) := by decide +kernel

private theorem r14part64 : ∀ i ∈ List.range 4, RunsAt 14 (64+i) := by decide +kernel

private theorem r14part68 : ∀ i ∈ List.range 4, RunsAt 14 (68+i) := by decide +kernel

private theorem r14part72 : ∀ i ∈ List.range 4, RunsAt 14 (72+i) := by decide +kernel

private theorem r14part76 : ∀ i ∈ List.range 4, RunsAt 14 (76+i) := by decide +kernel

private theorem r14part80 : ∀ i ∈ List.range 4, RunsAt 14 (80+i) := by decide +kernel

private theorem r14part84 : ∀ i ∈ List.range 4, RunsAt 14 (84+i) := by decide +kernel

private theorem r14part88 : ∀ i ∈ List.range 4, RunsAt 14 (88+i) := by decide +kernel

private theorem r14part92 : ∀ i ∈ List.range 4, RunsAt 14 (92+i) := by decide +kernel

private theorem r14part96 : ∀ i ∈ List.range 4, RunsAt 14 (96+i) := by decide +kernel

private theorem r14part100 : ∀ i ∈ List.range 4, RunsAt 14 (100+i) := by decide +kernel

private theorem r14part104 : ∀ i ∈ List.range 4, RunsAt 14 (104+i) := by decide +kernel

private theorem r14part108 : ∀ i ∈ List.range 4, RunsAt 14 (108+i) := by decide +kernel

private theorem r14part112 : ∀ i ∈ List.range 4, RunsAt 14 (112+i) := by decide +kernel

private theorem r14part116 : ∀ i ∈ List.range 4, RunsAt 14 (116+i) := by decide +kernel

private theorem r14part120 : ∀ i ∈ List.range 3, RunsAt 14 (120+i) := by decide +kernel

theorem checkedR14 : ∀ V ∈ List.range 123, RunsAt 14 V := by
  intro V hV
  have hlt : V < 123 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r14part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r14part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r14part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r14part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r14part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r14part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r14part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r14part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r14part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r14part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r14part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r14part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r14part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r14part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r14part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r14part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r14part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r14part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r14part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r14part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r14part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r14part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r14part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r14part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r14part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r14part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r14part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r14part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r14part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r14part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  have hp := r14part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r15part0 : ∀ i ∈ List.range 4, RunsAt 15 (0+i) := by decide +kernel

private theorem r15part4 : ∀ i ∈ List.range 4, RunsAt 15 (4+i) := by decide +kernel

private theorem r15part8 : ∀ i ∈ List.range 4, RunsAt 15 (8+i) := by decide +kernel

private theorem r15part12 : ∀ i ∈ List.range 4, RunsAt 15 (12+i) := by decide +kernel

private theorem r15part16 : ∀ i ∈ List.range 4, RunsAt 15 (16+i) := by decide +kernel

private theorem r15part20 : ∀ i ∈ List.range 4, RunsAt 15 (20+i) := by decide +kernel

private theorem r15part24 : ∀ i ∈ List.range 4, RunsAt 15 (24+i) := by decide +kernel

private theorem r15part28 : ∀ i ∈ List.range 4, RunsAt 15 (28+i) := by decide +kernel

private theorem r15part32 : ∀ i ∈ List.range 4, RunsAt 15 (32+i) := by decide +kernel

private theorem r15part36 : ∀ i ∈ List.range 4, RunsAt 15 (36+i) := by decide +kernel

private theorem r15part40 : ∀ i ∈ List.range 4, RunsAt 15 (40+i) := by decide +kernel

private theorem r15part44 : ∀ i ∈ List.range 4, RunsAt 15 (44+i) := by decide +kernel

private theorem r15part48 : ∀ i ∈ List.range 4, RunsAt 15 (48+i) := by decide +kernel

private theorem r15part52 : ∀ i ∈ List.range 4, RunsAt 15 (52+i) := by decide +kernel

private theorem r15part56 : ∀ i ∈ List.range 4, RunsAt 15 (56+i) := by decide +kernel

private theorem r15part60 : ∀ i ∈ List.range 4, RunsAt 15 (60+i) := by decide +kernel

private theorem r15part64 : ∀ i ∈ List.range 4, RunsAt 15 (64+i) := by decide +kernel

private theorem r15part68 : ∀ i ∈ List.range 4, RunsAt 15 (68+i) := by decide +kernel

private theorem r15part72 : ∀ i ∈ List.range 4, RunsAt 15 (72+i) := by decide +kernel

private theorem r15part76 : ∀ i ∈ List.range 4, RunsAt 15 (76+i) := by decide +kernel

private theorem r15part80 : ∀ i ∈ List.range 4, RunsAt 15 (80+i) := by decide +kernel

private theorem r15part84 : ∀ i ∈ List.range 4, RunsAt 15 (84+i) := by decide +kernel

private theorem r15part88 : ∀ i ∈ List.range 4, RunsAt 15 (88+i) := by decide +kernel

private theorem r15part92 : ∀ i ∈ List.range 4, RunsAt 15 (92+i) := by decide +kernel

private theorem r15part96 : ∀ i ∈ List.range 4, RunsAt 15 (96+i) := by decide +kernel

private theorem r15part100 : ∀ i ∈ List.range 4, RunsAt 15 (100+i) := by decide +kernel

private theorem r15part104 : ∀ i ∈ List.range 4, RunsAt 15 (104+i) := by decide +kernel

private theorem r15part108 : ∀ i ∈ List.range 4, RunsAt 15 (108+i) := by decide +kernel

private theorem r15part112 : ∀ i ∈ List.range 4, RunsAt 15 (112+i) := by decide +kernel

private theorem r15part116 : ∀ i ∈ List.range 4, RunsAt 15 (116+i) := by decide +kernel

private theorem r15part120 : ∀ i ∈ List.range 2, RunsAt 15 (120+i) := by decide +kernel

theorem checkedR15 : ∀ V ∈ List.range 122, RunsAt 15 V := by
  intro V hV
  have hlt : V < 122 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r15part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r15part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r15part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r15part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r15part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r15part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r15part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r15part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r15part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r15part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r15part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r15part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r15part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r15part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r15part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r15part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r15part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r15part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r15part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r15part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r15part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r15part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r15part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r15part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r15part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r15part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r15part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r15part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r15part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r15part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  have hp := r15part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r16part0 : ∀ i ∈ List.range 4, RunsAt 16 (0+i) := by decide +kernel

private theorem r16part4 : ∀ i ∈ List.range 4, RunsAt 16 (4+i) := by decide +kernel

private theorem r16part8 : ∀ i ∈ List.range 4, RunsAt 16 (8+i) := by decide +kernel

private theorem r16part12 : ∀ i ∈ List.range 4, RunsAt 16 (12+i) := by decide +kernel

private theorem r16part16 : ∀ i ∈ List.range 4, RunsAt 16 (16+i) := by decide +kernel

private theorem r16part20 : ∀ i ∈ List.range 4, RunsAt 16 (20+i) := by decide +kernel

private theorem r16part24 : ∀ i ∈ List.range 4, RunsAt 16 (24+i) := by decide +kernel

private theorem r16part28 : ∀ i ∈ List.range 4, RunsAt 16 (28+i) := by decide +kernel

private theorem r16part32 : ∀ i ∈ List.range 4, RunsAt 16 (32+i) := by decide +kernel

private theorem r16part36 : ∀ i ∈ List.range 4, RunsAt 16 (36+i) := by decide +kernel

private theorem r16part40 : ∀ i ∈ List.range 4, RunsAt 16 (40+i) := by decide +kernel

private theorem r16part44 : ∀ i ∈ List.range 4, RunsAt 16 (44+i) := by decide +kernel

private theorem r16part48 : ∀ i ∈ List.range 4, RunsAt 16 (48+i) := by decide +kernel

private theorem r16part52 : ∀ i ∈ List.range 4, RunsAt 16 (52+i) := by decide +kernel

private theorem r16part56 : ∀ i ∈ List.range 4, RunsAt 16 (56+i) := by decide +kernel

private theorem r16part60 : ∀ i ∈ List.range 4, RunsAt 16 (60+i) := by decide +kernel

private theorem r16part64 : ∀ i ∈ List.range 4, RunsAt 16 (64+i) := by decide +kernel

private theorem r16part68 : ∀ i ∈ List.range 4, RunsAt 16 (68+i) := by decide +kernel

private theorem r16part72 : ∀ i ∈ List.range 4, RunsAt 16 (72+i) := by decide +kernel

private theorem r16part76 : ∀ i ∈ List.range 4, RunsAt 16 (76+i) := by decide +kernel

private theorem r16part80 : ∀ i ∈ List.range 4, RunsAt 16 (80+i) := by decide +kernel

private theorem r16part84 : ∀ i ∈ List.range 4, RunsAt 16 (84+i) := by decide +kernel

private theorem r16part88 : ∀ i ∈ List.range 4, RunsAt 16 (88+i) := by decide +kernel

private theorem r16part92 : ∀ i ∈ List.range 4, RunsAt 16 (92+i) := by decide +kernel

private theorem r16part96 : ∀ i ∈ List.range 4, RunsAt 16 (96+i) := by decide +kernel

private theorem r16part100 : ∀ i ∈ List.range 4, RunsAt 16 (100+i) := by decide +kernel

private theorem r16part104 : ∀ i ∈ List.range 4, RunsAt 16 (104+i) := by decide +kernel

private theorem r16part108 : ∀ i ∈ List.range 4, RunsAt 16 (108+i) := by decide +kernel

private theorem r16part112 : ∀ i ∈ List.range 4, RunsAt 16 (112+i) := by decide +kernel

private theorem r16part116 : ∀ i ∈ List.range 4, RunsAt 16 (116+i) := by decide +kernel

private theorem r16part120 : ∀ i ∈ List.range 1, RunsAt 16 (120+i) := by decide +kernel

theorem checkedR16 : ∀ V ∈ List.range 121, RunsAt 16 V := by
  intro V hV
  have hlt : V < 121 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r16part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r16part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r16part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r16part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r16part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r16part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r16part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r16part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r16part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r16part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r16part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r16part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r16part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r16part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r16part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r16part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r16part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r16part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r16part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r16part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r16part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r16part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r16part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r16part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r16part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r16part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r16part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r16part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r16part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 120
  · have hp := r16part116 (V-116) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp
  have hp := r16part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp

private theorem r17part0 : ∀ i ∈ List.range 4, RunsAt 17 (0+i) := by decide +kernel

private theorem r17part4 : ∀ i ∈ List.range 4, RunsAt 17 (4+i) := by decide +kernel

private theorem r17part8 : ∀ i ∈ List.range 4, RunsAt 17 (8+i) := by decide +kernel

private theorem r17part12 : ∀ i ∈ List.range 4, RunsAt 17 (12+i) := by decide +kernel

private theorem r17part16 : ∀ i ∈ List.range 4, RunsAt 17 (16+i) := by decide +kernel

private theorem r17part20 : ∀ i ∈ List.range 4, RunsAt 17 (20+i) := by decide +kernel

private theorem r17part24 : ∀ i ∈ List.range 4, RunsAt 17 (24+i) := by decide +kernel

private theorem r17part28 : ∀ i ∈ List.range 4, RunsAt 17 (28+i) := by decide +kernel

private theorem r17part32 : ∀ i ∈ List.range 4, RunsAt 17 (32+i) := by decide +kernel

private theorem r17part36 : ∀ i ∈ List.range 4, RunsAt 17 (36+i) := by decide +kernel

private theorem r17part40 : ∀ i ∈ List.range 4, RunsAt 17 (40+i) := by decide +kernel

private theorem r17part44 : ∀ i ∈ List.range 4, RunsAt 17 (44+i) := by decide +kernel

private theorem r17part48 : ∀ i ∈ List.range 4, RunsAt 17 (48+i) := by decide +kernel

private theorem r17part52 : ∀ i ∈ List.range 4, RunsAt 17 (52+i) := by decide +kernel

private theorem r17part56 : ∀ i ∈ List.range 4, RunsAt 17 (56+i) := by decide +kernel

private theorem r17part60 : ∀ i ∈ List.range 4, RunsAt 17 (60+i) := by decide +kernel

private theorem r17part64 : ∀ i ∈ List.range 4, RunsAt 17 (64+i) := by decide +kernel

private theorem r17part68 : ∀ i ∈ List.range 4, RunsAt 17 (68+i) := by decide +kernel

private theorem r17part72 : ∀ i ∈ List.range 4, RunsAt 17 (72+i) := by decide +kernel

private theorem r17part76 : ∀ i ∈ List.range 4, RunsAt 17 (76+i) := by decide +kernel

private theorem r17part80 : ∀ i ∈ List.range 4, RunsAt 17 (80+i) := by decide +kernel

private theorem r17part84 : ∀ i ∈ List.range 4, RunsAt 17 (84+i) := by decide +kernel

private theorem r17part88 : ∀ i ∈ List.range 4, RunsAt 17 (88+i) := by decide +kernel

private theorem r17part92 : ∀ i ∈ List.range 4, RunsAt 17 (92+i) := by decide +kernel

private theorem r17part96 : ∀ i ∈ List.range 4, RunsAt 17 (96+i) := by decide +kernel

private theorem r17part100 : ∀ i ∈ List.range 4, RunsAt 17 (100+i) := by decide +kernel

private theorem r17part104 : ∀ i ∈ List.range 4, RunsAt 17 (104+i) := by decide +kernel

private theorem r17part108 : ∀ i ∈ List.range 4, RunsAt 17 (108+i) := by decide +kernel

private theorem r17part112 : ∀ i ∈ List.range 4, RunsAt 17 (112+i) := by decide +kernel

private theorem r17part116 : ∀ i ∈ List.range 4, RunsAt 17 (116+i) := by decide +kernel

theorem checkedR17 : ∀ V ∈ List.range 120, RunsAt 17 V := by
  intro V hV
  have hlt : V < 120 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r17part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r17part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r17part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r17part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r17part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r17part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r17part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r17part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r17part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r17part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r17part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r17part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r17part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r17part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r17part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r17part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r17part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r17part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r17part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r17part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r17part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r17part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r17part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r17part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r17part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r17part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r17part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r17part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r17part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r17part116 (V-116) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp

private theorem r18part0 : ∀ i ∈ List.range 4, RunsAt 18 (0+i) := by decide +kernel

private theorem r18part4 : ∀ i ∈ List.range 4, RunsAt 18 (4+i) := by decide +kernel

private theorem r18part8 : ∀ i ∈ List.range 4, RunsAt 18 (8+i) := by decide +kernel

private theorem r18part12 : ∀ i ∈ List.range 4, RunsAt 18 (12+i) := by decide +kernel

private theorem r18part16 : ∀ i ∈ List.range 4, RunsAt 18 (16+i) := by decide +kernel

private theorem r18part20 : ∀ i ∈ List.range 4, RunsAt 18 (20+i) := by decide +kernel

private theorem r18part24 : ∀ i ∈ List.range 4, RunsAt 18 (24+i) := by decide +kernel

private theorem r18part28 : ∀ i ∈ List.range 4, RunsAt 18 (28+i) := by decide +kernel

private theorem r18part32 : ∀ i ∈ List.range 4, RunsAt 18 (32+i) := by decide +kernel

private theorem r18part36 : ∀ i ∈ List.range 4, RunsAt 18 (36+i) := by decide +kernel

private theorem r18part40 : ∀ i ∈ List.range 4, RunsAt 18 (40+i) := by decide +kernel

private theorem r18part44 : ∀ i ∈ List.range 4, RunsAt 18 (44+i) := by decide +kernel

private theorem r18part48 : ∀ i ∈ List.range 4, RunsAt 18 (48+i) := by decide +kernel

private theorem r18part52 : ∀ i ∈ List.range 4, RunsAt 18 (52+i) := by decide +kernel

private theorem r18part56 : ∀ i ∈ List.range 4, RunsAt 18 (56+i) := by decide +kernel

private theorem r18part60 : ∀ i ∈ List.range 4, RunsAt 18 (60+i) := by decide +kernel

private theorem r18part64 : ∀ i ∈ List.range 4, RunsAt 18 (64+i) := by decide +kernel

private theorem r18part68 : ∀ i ∈ List.range 4, RunsAt 18 (68+i) := by decide +kernel

private theorem r18part72 : ∀ i ∈ List.range 4, RunsAt 18 (72+i) := by decide +kernel

private theorem r18part76 : ∀ i ∈ List.range 4, RunsAt 18 (76+i) := by decide +kernel

private theorem r18part80 : ∀ i ∈ List.range 4, RunsAt 18 (80+i) := by decide +kernel

private theorem r18part84 : ∀ i ∈ List.range 4, RunsAt 18 (84+i) := by decide +kernel

private theorem r18part88 : ∀ i ∈ List.range 4, RunsAt 18 (88+i) := by decide +kernel

private theorem r18part92 : ∀ i ∈ List.range 4, RunsAt 18 (92+i) := by decide +kernel

private theorem r18part96 : ∀ i ∈ List.range 4, RunsAt 18 (96+i) := by decide +kernel

private theorem r18part100 : ∀ i ∈ List.range 4, RunsAt 18 (100+i) := by decide +kernel

private theorem r18part104 : ∀ i ∈ List.range 4, RunsAt 18 (104+i) := by decide +kernel

private theorem r18part108 : ∀ i ∈ List.range 4, RunsAt 18 (108+i) := by decide +kernel

private theorem r18part112 : ∀ i ∈ List.range 4, RunsAt 18 (112+i) := by decide +kernel

private theorem r18part116 : ∀ i ∈ List.range 3, RunsAt 18 (116+i) := by decide +kernel

theorem checkedR18 : ∀ V ∈ List.range 119, RunsAt 18 V := by
  intro V hV
  have hlt : V < 119 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r18part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r18part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r18part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r18part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r18part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r18part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r18part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r18part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r18part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r18part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r18part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r18part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r18part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r18part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r18part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r18part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r18part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r18part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r18part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r18part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r18part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r18part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r18part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r18part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r18part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r18part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r18part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r18part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r18part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r18part116 (V-116) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp

private theorem r19part0 : ∀ i ∈ List.range 4, RunsAt 19 (0+i) := by decide +kernel

private theorem r19part4 : ∀ i ∈ List.range 4, RunsAt 19 (4+i) := by decide +kernel

private theorem r19part8 : ∀ i ∈ List.range 4, RunsAt 19 (8+i) := by decide +kernel

private theorem r19part12 : ∀ i ∈ List.range 4, RunsAt 19 (12+i) := by decide +kernel

private theorem r19part16 : ∀ i ∈ List.range 4, RunsAt 19 (16+i) := by decide +kernel

private theorem r19part20 : ∀ i ∈ List.range 4, RunsAt 19 (20+i) := by decide +kernel

private theorem r19part24 : ∀ i ∈ List.range 4, RunsAt 19 (24+i) := by decide +kernel

private theorem r19part28 : ∀ i ∈ List.range 4, RunsAt 19 (28+i) := by decide +kernel

private theorem r19part32 : ∀ i ∈ List.range 4, RunsAt 19 (32+i) := by decide +kernel

private theorem r19part36 : ∀ i ∈ List.range 4, RunsAt 19 (36+i) := by decide +kernel

private theorem r19part40 : ∀ i ∈ List.range 4, RunsAt 19 (40+i) := by decide +kernel

private theorem r19part44 : ∀ i ∈ List.range 4, RunsAt 19 (44+i) := by decide +kernel

private theorem r19part48 : ∀ i ∈ List.range 4, RunsAt 19 (48+i) := by decide +kernel

private theorem r19part52 : ∀ i ∈ List.range 4, RunsAt 19 (52+i) := by decide +kernel

private theorem r19part56 : ∀ i ∈ List.range 4, RunsAt 19 (56+i) := by decide +kernel

private theorem r19part60 : ∀ i ∈ List.range 4, RunsAt 19 (60+i) := by decide +kernel

private theorem r19part64 : ∀ i ∈ List.range 4, RunsAt 19 (64+i) := by decide +kernel

private theorem r19part68 : ∀ i ∈ List.range 4, RunsAt 19 (68+i) := by decide +kernel

private theorem r19part72 : ∀ i ∈ List.range 4, RunsAt 19 (72+i) := by decide +kernel

private theorem r19part76 : ∀ i ∈ List.range 4, RunsAt 19 (76+i) := by decide +kernel

private theorem r19part80 : ∀ i ∈ List.range 4, RunsAt 19 (80+i) := by decide +kernel

private theorem r19part84 : ∀ i ∈ List.range 4, RunsAt 19 (84+i) := by decide +kernel

private theorem r19part88 : ∀ i ∈ List.range 4, RunsAt 19 (88+i) := by decide +kernel

private theorem r19part92 : ∀ i ∈ List.range 4, RunsAt 19 (92+i) := by decide +kernel

private theorem r19part96 : ∀ i ∈ List.range 4, RunsAt 19 (96+i) := by decide +kernel

private theorem r19part100 : ∀ i ∈ List.range 4, RunsAt 19 (100+i) := by decide +kernel

private theorem r19part104 : ∀ i ∈ List.range 4, RunsAt 19 (104+i) := by decide +kernel

private theorem r19part108 : ∀ i ∈ List.range 4, RunsAt 19 (108+i) := by decide +kernel

private theorem r19part112 : ∀ i ∈ List.range 4, RunsAt 19 (112+i) := by decide +kernel

private theorem r19part116 : ∀ i ∈ List.range 2, RunsAt 19 (116+i) := by decide +kernel

theorem checkedR19 : ∀ V ∈ List.range 118, RunsAt 19 V := by
  intro V hV
  have hlt : V < 118 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r19part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r19part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r19part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r19part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r19part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r19part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r19part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r19part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r19part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r19part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r19part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r19part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r19part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r19part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r19part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r19part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r19part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r19part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r19part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r19part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r19part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r19part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r19part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r19part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r19part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r19part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r19part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r19part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r19part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r19part116 (V-116) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp

private theorem r20part0 : ∀ i ∈ List.range 4, RunsAt 20 (0+i) := by decide +kernel

private theorem r20part4 : ∀ i ∈ List.range 4, RunsAt 20 (4+i) := by decide +kernel

private theorem r20part8 : ∀ i ∈ List.range 4, RunsAt 20 (8+i) := by decide +kernel

private theorem r20part12 : ∀ i ∈ List.range 4, RunsAt 20 (12+i) := by decide +kernel

private theorem r20part16 : ∀ i ∈ List.range 4, RunsAt 20 (16+i) := by decide +kernel

private theorem r20part20 : ∀ i ∈ List.range 4, RunsAt 20 (20+i) := by decide +kernel

private theorem r20part24 : ∀ i ∈ List.range 4, RunsAt 20 (24+i) := by decide +kernel

private theorem r20part28 : ∀ i ∈ List.range 4, RunsAt 20 (28+i) := by decide +kernel

private theorem r20part32 : ∀ i ∈ List.range 4, RunsAt 20 (32+i) := by decide +kernel

private theorem r20part36 : ∀ i ∈ List.range 4, RunsAt 20 (36+i) := by decide +kernel

private theorem r20part40 : ∀ i ∈ List.range 4, RunsAt 20 (40+i) := by decide +kernel

private theorem r20part44 : ∀ i ∈ List.range 4, RunsAt 20 (44+i) := by decide +kernel

private theorem r20part48 : ∀ i ∈ List.range 4, RunsAt 20 (48+i) := by decide +kernel

private theorem r20part52 : ∀ i ∈ List.range 4, RunsAt 20 (52+i) := by decide +kernel

private theorem r20part56 : ∀ i ∈ List.range 4, RunsAt 20 (56+i) := by decide +kernel

private theorem r20part60 : ∀ i ∈ List.range 4, RunsAt 20 (60+i) := by decide +kernel

private theorem r20part64 : ∀ i ∈ List.range 4, RunsAt 20 (64+i) := by decide +kernel

private theorem r20part68 : ∀ i ∈ List.range 4, RunsAt 20 (68+i) := by decide +kernel

private theorem r20part72 : ∀ i ∈ List.range 4, RunsAt 20 (72+i) := by decide +kernel

private theorem r20part76 : ∀ i ∈ List.range 4, RunsAt 20 (76+i) := by decide +kernel

private theorem r20part80 : ∀ i ∈ List.range 4, RunsAt 20 (80+i) := by decide +kernel

private theorem r20part84 : ∀ i ∈ List.range 4, RunsAt 20 (84+i) := by decide +kernel

private theorem r20part88 : ∀ i ∈ List.range 4, RunsAt 20 (88+i) := by decide +kernel

private theorem r20part92 : ∀ i ∈ List.range 4, RunsAt 20 (92+i) := by decide +kernel

private theorem r20part96 : ∀ i ∈ List.range 4, RunsAt 20 (96+i) := by decide +kernel

private theorem r20part100 : ∀ i ∈ List.range 4, RunsAt 20 (100+i) := by decide +kernel

private theorem r20part104 : ∀ i ∈ List.range 4, RunsAt 20 (104+i) := by decide +kernel

private theorem r20part108 : ∀ i ∈ List.range 4, RunsAt 20 (108+i) := by decide +kernel

private theorem r20part112 : ∀ i ∈ List.range 4, RunsAt 20 (112+i) := by decide +kernel

private theorem r20part116 : ∀ i ∈ List.range 1, RunsAt 20 (116+i) := by decide +kernel

theorem checkedR20 : ∀ V ∈ List.range 117, RunsAt 20 V := by
  intro V hV
  have hlt : V < 117 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r20part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r20part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r20part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r20part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r20part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r20part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r20part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r20part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r20part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r20part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r20part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r20part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r20part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r20part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r20part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r20part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r20part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r20part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r20part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r20part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r20part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r20part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r20part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r20part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r20part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r20part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r20part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r20part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  by_cases h116 : V < 116
  · have hp := r20part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r20part116 (V-116) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using hp

private theorem r21part0 : ∀ i ∈ List.range 4, RunsAt 21 (0+i) := by decide +kernel

private theorem r21part4 : ∀ i ∈ List.range 4, RunsAt 21 (4+i) := by decide +kernel

private theorem r21part8 : ∀ i ∈ List.range 4, RunsAt 21 (8+i) := by decide +kernel

private theorem r21part12 : ∀ i ∈ List.range 4, RunsAt 21 (12+i) := by decide +kernel

private theorem r21part16 : ∀ i ∈ List.range 4, RunsAt 21 (16+i) := by decide +kernel

private theorem r21part20 : ∀ i ∈ List.range 4, RunsAt 21 (20+i) := by decide +kernel

private theorem r21part24 : ∀ i ∈ List.range 4, RunsAt 21 (24+i) := by decide +kernel

private theorem r21part28 : ∀ i ∈ List.range 4, RunsAt 21 (28+i) := by decide +kernel

private theorem r21part32 : ∀ i ∈ List.range 4, RunsAt 21 (32+i) := by decide +kernel

private theorem r21part36 : ∀ i ∈ List.range 4, RunsAt 21 (36+i) := by decide +kernel

private theorem r21part40 : ∀ i ∈ List.range 4, RunsAt 21 (40+i) := by decide +kernel

private theorem r21part44 : ∀ i ∈ List.range 4, RunsAt 21 (44+i) := by decide +kernel

private theorem r21part48 : ∀ i ∈ List.range 4, RunsAt 21 (48+i) := by decide +kernel

private theorem r21part52 : ∀ i ∈ List.range 4, RunsAt 21 (52+i) := by decide +kernel

private theorem r21part56 : ∀ i ∈ List.range 4, RunsAt 21 (56+i) := by decide +kernel

private theorem r21part60 : ∀ i ∈ List.range 4, RunsAt 21 (60+i) := by decide +kernel

private theorem r21part64 : ∀ i ∈ List.range 4, RunsAt 21 (64+i) := by decide +kernel

private theorem r21part68 : ∀ i ∈ List.range 4, RunsAt 21 (68+i) := by decide +kernel

private theorem r21part72 : ∀ i ∈ List.range 4, RunsAt 21 (72+i) := by decide +kernel

private theorem r21part76 : ∀ i ∈ List.range 4, RunsAt 21 (76+i) := by decide +kernel

private theorem r21part80 : ∀ i ∈ List.range 4, RunsAt 21 (80+i) := by decide +kernel

private theorem r21part84 : ∀ i ∈ List.range 4, RunsAt 21 (84+i) := by decide +kernel

private theorem r21part88 : ∀ i ∈ List.range 4, RunsAt 21 (88+i) := by decide +kernel

private theorem r21part92 : ∀ i ∈ List.range 4, RunsAt 21 (92+i) := by decide +kernel

private theorem r21part96 : ∀ i ∈ List.range 4, RunsAt 21 (96+i) := by decide +kernel

private theorem r21part100 : ∀ i ∈ List.range 4, RunsAt 21 (100+i) := by decide +kernel

private theorem r21part104 : ∀ i ∈ List.range 4, RunsAt 21 (104+i) := by decide +kernel

private theorem r21part108 : ∀ i ∈ List.range 4, RunsAt 21 (108+i) := by decide +kernel

private theorem r21part112 : ∀ i ∈ List.range 4, RunsAt 21 (112+i) := by decide +kernel

theorem checkedR21 : ∀ V ∈ List.range 116, RunsAt 21 V := by
  intro V hV
  have hlt : V < 116 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r21part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r21part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r21part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r21part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r21part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r21part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r21part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r21part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r21part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r21part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r21part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r21part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r21part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r21part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r21part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r21part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r21part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r21part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r21part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r21part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r21part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r21part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r21part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r21part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r21part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r21part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r21part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r21part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  have hp := r21part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r22part0 : ∀ i ∈ List.range 4, RunsAt 22 (0+i) := by decide +kernel

private theorem r22part4 : ∀ i ∈ List.range 4, RunsAt 22 (4+i) := by decide +kernel

private theorem r22part8 : ∀ i ∈ List.range 4, RunsAt 22 (8+i) := by decide +kernel

private theorem r22part12 : ∀ i ∈ List.range 4, RunsAt 22 (12+i) := by decide +kernel

private theorem r22part16 : ∀ i ∈ List.range 4, RunsAt 22 (16+i) := by decide +kernel

private theorem r22part20 : ∀ i ∈ List.range 4, RunsAt 22 (20+i) := by decide +kernel

private theorem r22part24 : ∀ i ∈ List.range 4, RunsAt 22 (24+i) := by decide +kernel

private theorem r22part28 : ∀ i ∈ List.range 4, RunsAt 22 (28+i) := by decide +kernel

private theorem r22part32 : ∀ i ∈ List.range 4, RunsAt 22 (32+i) := by decide +kernel

private theorem r22part36 : ∀ i ∈ List.range 4, RunsAt 22 (36+i) := by decide +kernel

private theorem r22part40 : ∀ i ∈ List.range 4, RunsAt 22 (40+i) := by decide +kernel

private theorem r22part44 : ∀ i ∈ List.range 4, RunsAt 22 (44+i) := by decide +kernel

private theorem r22part48 : ∀ i ∈ List.range 4, RunsAt 22 (48+i) := by decide +kernel

private theorem r22part52 : ∀ i ∈ List.range 4, RunsAt 22 (52+i) := by decide +kernel

private theorem r22part56 : ∀ i ∈ List.range 4, RunsAt 22 (56+i) := by decide +kernel

private theorem r22part60 : ∀ i ∈ List.range 4, RunsAt 22 (60+i) := by decide +kernel

private theorem r22part64 : ∀ i ∈ List.range 4, RunsAt 22 (64+i) := by decide +kernel

private theorem r22part68 : ∀ i ∈ List.range 4, RunsAt 22 (68+i) := by decide +kernel

private theorem r22part72 : ∀ i ∈ List.range 4, RunsAt 22 (72+i) := by decide +kernel

private theorem r22part76 : ∀ i ∈ List.range 4, RunsAt 22 (76+i) := by decide +kernel

private theorem r22part80 : ∀ i ∈ List.range 4, RunsAt 22 (80+i) := by decide +kernel

private theorem r22part84 : ∀ i ∈ List.range 4, RunsAt 22 (84+i) := by decide +kernel

private theorem r22part88 : ∀ i ∈ List.range 4, RunsAt 22 (88+i) := by decide +kernel

private theorem r22part92 : ∀ i ∈ List.range 4, RunsAt 22 (92+i) := by decide +kernel

private theorem r22part96 : ∀ i ∈ List.range 4, RunsAt 22 (96+i) := by decide +kernel

private theorem r22part100 : ∀ i ∈ List.range 4, RunsAt 22 (100+i) := by decide +kernel

private theorem r22part104 : ∀ i ∈ List.range 4, RunsAt 22 (104+i) := by decide +kernel

private theorem r22part108 : ∀ i ∈ List.range 4, RunsAt 22 (108+i) := by decide +kernel

private theorem r22part112 : ∀ i ∈ List.range 3, RunsAt 22 (112+i) := by decide +kernel

theorem checkedR22 : ∀ V ∈ List.range 115, RunsAt 22 V := by
  intro V hV
  have hlt : V < 115 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r22part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r22part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r22part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r22part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r22part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r22part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r22part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r22part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r22part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r22part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r22part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r22part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r22part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r22part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r22part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r22part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r22part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r22part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r22part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r22part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r22part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r22part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r22part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r22part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r22part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r22part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r22part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r22part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  have hp := r22part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r23part0 : ∀ i ∈ List.range 4, RunsAt 23 (0+i) := by decide +kernel

private theorem r23part4 : ∀ i ∈ List.range 4, RunsAt 23 (4+i) := by decide +kernel

private theorem r23part8 : ∀ i ∈ List.range 4, RunsAt 23 (8+i) := by decide +kernel

private theorem r23part12 : ∀ i ∈ List.range 4, RunsAt 23 (12+i) := by decide +kernel

private theorem r23part16 : ∀ i ∈ List.range 4, RunsAt 23 (16+i) := by decide +kernel

private theorem r23part20 : ∀ i ∈ List.range 4, RunsAt 23 (20+i) := by decide +kernel

private theorem r23part24 : ∀ i ∈ List.range 4, RunsAt 23 (24+i) := by decide +kernel

private theorem r23part28 : ∀ i ∈ List.range 4, RunsAt 23 (28+i) := by decide +kernel

private theorem r23part32 : ∀ i ∈ List.range 4, RunsAt 23 (32+i) := by decide +kernel

private theorem r23part36 : ∀ i ∈ List.range 4, RunsAt 23 (36+i) := by decide +kernel

private theorem r23part40 : ∀ i ∈ List.range 4, RunsAt 23 (40+i) := by decide +kernel

private theorem r23part44 : ∀ i ∈ List.range 4, RunsAt 23 (44+i) := by decide +kernel

private theorem r23part48 : ∀ i ∈ List.range 4, RunsAt 23 (48+i) := by decide +kernel

private theorem r23part52 : ∀ i ∈ List.range 4, RunsAt 23 (52+i) := by decide +kernel

private theorem r23part56 : ∀ i ∈ List.range 4, RunsAt 23 (56+i) := by decide +kernel

private theorem r23part60 : ∀ i ∈ List.range 4, RunsAt 23 (60+i) := by decide +kernel

private theorem r23part64 : ∀ i ∈ List.range 4, RunsAt 23 (64+i) := by decide +kernel

private theorem r23part68 : ∀ i ∈ List.range 4, RunsAt 23 (68+i) := by decide +kernel

private theorem r23part72 : ∀ i ∈ List.range 4, RunsAt 23 (72+i) := by decide +kernel

private theorem r23part76 : ∀ i ∈ List.range 4, RunsAt 23 (76+i) := by decide +kernel

private theorem r23part80 : ∀ i ∈ List.range 4, RunsAt 23 (80+i) := by decide +kernel

private theorem r23part84 : ∀ i ∈ List.range 4, RunsAt 23 (84+i) := by decide +kernel

private theorem r23part88 : ∀ i ∈ List.range 4, RunsAt 23 (88+i) := by decide +kernel

private theorem r23part92 : ∀ i ∈ List.range 4, RunsAt 23 (92+i) := by decide +kernel

private theorem r23part96 : ∀ i ∈ List.range 4, RunsAt 23 (96+i) := by decide +kernel

private theorem r23part100 : ∀ i ∈ List.range 4, RunsAt 23 (100+i) := by decide +kernel

private theorem r23part104 : ∀ i ∈ List.range 4, RunsAt 23 (104+i) := by decide +kernel

private theorem r23part108 : ∀ i ∈ List.range 4, RunsAt 23 (108+i) := by decide +kernel

private theorem r23part112 : ∀ i ∈ List.range 2, RunsAt 23 (112+i) := by decide +kernel

theorem checkedR23 : ∀ V ∈ List.range 114, RunsAt 23 V := by
  intro V hV
  have hlt : V < 114 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r23part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r23part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r23part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r23part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r23part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r23part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r23part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r23part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r23part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r23part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r23part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r23part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r23part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r23part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r23part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r23part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r23part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r23part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r23part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r23part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r23part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r23part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r23part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r23part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r23part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r23part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r23part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r23part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  have hp := r23part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r24part0 : ∀ i ∈ List.range 4, RunsAt 24 (0+i) := by decide +kernel

private theorem r24part4 : ∀ i ∈ List.range 4, RunsAt 24 (4+i) := by decide +kernel

private theorem r24part8 : ∀ i ∈ List.range 4, RunsAt 24 (8+i) := by decide +kernel

private theorem r24part12 : ∀ i ∈ List.range 4, RunsAt 24 (12+i) := by decide +kernel

private theorem r24part16 : ∀ i ∈ List.range 4, RunsAt 24 (16+i) := by decide +kernel

private theorem r24part20 : ∀ i ∈ List.range 4, RunsAt 24 (20+i) := by decide +kernel

private theorem r24part24 : ∀ i ∈ List.range 4, RunsAt 24 (24+i) := by decide +kernel

private theorem r24part28 : ∀ i ∈ List.range 4, RunsAt 24 (28+i) := by decide +kernel

private theorem r24part32 : ∀ i ∈ List.range 4, RunsAt 24 (32+i) := by decide +kernel

private theorem r24part36 : ∀ i ∈ List.range 4, RunsAt 24 (36+i) := by decide +kernel

private theorem r24part40 : ∀ i ∈ List.range 4, RunsAt 24 (40+i) := by decide +kernel

private theorem r24part44 : ∀ i ∈ List.range 4, RunsAt 24 (44+i) := by decide +kernel

private theorem r24part48 : ∀ i ∈ List.range 4, RunsAt 24 (48+i) := by decide +kernel

private theorem r24part52 : ∀ i ∈ List.range 4, RunsAt 24 (52+i) := by decide +kernel

private theorem r24part56 : ∀ i ∈ List.range 4, RunsAt 24 (56+i) := by decide +kernel

private theorem r24part60 : ∀ i ∈ List.range 4, RunsAt 24 (60+i) := by decide +kernel

private theorem r24part64 : ∀ i ∈ List.range 4, RunsAt 24 (64+i) := by decide +kernel

private theorem r24part68 : ∀ i ∈ List.range 4, RunsAt 24 (68+i) := by decide +kernel

private theorem r24part72 : ∀ i ∈ List.range 4, RunsAt 24 (72+i) := by decide +kernel

private theorem r24part76 : ∀ i ∈ List.range 4, RunsAt 24 (76+i) := by decide +kernel

private theorem r24part80 : ∀ i ∈ List.range 4, RunsAt 24 (80+i) := by decide +kernel

private theorem r24part84 : ∀ i ∈ List.range 4, RunsAt 24 (84+i) := by decide +kernel

private theorem r24part88 : ∀ i ∈ List.range 4, RunsAt 24 (88+i) := by decide +kernel

private theorem r24part92 : ∀ i ∈ List.range 4, RunsAt 24 (92+i) := by decide +kernel

private theorem r24part96 : ∀ i ∈ List.range 4, RunsAt 24 (96+i) := by decide +kernel

private theorem r24part100 : ∀ i ∈ List.range 4, RunsAt 24 (100+i) := by decide +kernel

private theorem r24part104 : ∀ i ∈ List.range 4, RunsAt 24 (104+i) := by decide +kernel

private theorem r24part108 : ∀ i ∈ List.range 4, RunsAt 24 (108+i) := by decide +kernel

private theorem r24part112 : ∀ i ∈ List.range 1, RunsAt 24 (112+i) := by decide +kernel

theorem checkedR24 : ∀ V ∈ List.range 113, RunsAt 24 V := by
  intro V hV
  have hlt : V < 113 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r24part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r24part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r24part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r24part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r24part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r24part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r24part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r24part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r24part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r24part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r24part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r24part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r24part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r24part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r24part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r24part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r24part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r24part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r24part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r24part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r24part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r24part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r24part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r24part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r24part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r24part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r24part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 112
  · have hp := r24part108 (V-108) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp
  have hp := r24part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp

private theorem r25part0 : ∀ i ∈ List.range 4, RunsAt 25 (0+i) := by decide +kernel

private theorem r25part4 : ∀ i ∈ List.range 4, RunsAt 25 (4+i) := by decide +kernel

private theorem r25part8 : ∀ i ∈ List.range 4, RunsAt 25 (8+i) := by decide +kernel

private theorem r25part12 : ∀ i ∈ List.range 4, RunsAt 25 (12+i) := by decide +kernel

private theorem r25part16 : ∀ i ∈ List.range 4, RunsAt 25 (16+i) := by decide +kernel

private theorem r25part20 : ∀ i ∈ List.range 4, RunsAt 25 (20+i) := by decide +kernel

private theorem r25part24 : ∀ i ∈ List.range 4, RunsAt 25 (24+i) := by decide +kernel

private theorem r25part28 : ∀ i ∈ List.range 4, RunsAt 25 (28+i) := by decide +kernel

private theorem r25part32 : ∀ i ∈ List.range 4, RunsAt 25 (32+i) := by decide +kernel

private theorem r25part36 : ∀ i ∈ List.range 4, RunsAt 25 (36+i) := by decide +kernel

private theorem r25part40 : ∀ i ∈ List.range 4, RunsAt 25 (40+i) := by decide +kernel

private theorem r25part44 : ∀ i ∈ List.range 4, RunsAt 25 (44+i) := by decide +kernel

private theorem r25part48 : ∀ i ∈ List.range 4, RunsAt 25 (48+i) := by decide +kernel

private theorem r25part52 : ∀ i ∈ List.range 4, RunsAt 25 (52+i) := by decide +kernel

private theorem r25part56 : ∀ i ∈ List.range 4, RunsAt 25 (56+i) := by decide +kernel

private theorem r25part60 : ∀ i ∈ List.range 4, RunsAt 25 (60+i) := by decide +kernel

private theorem r25part64 : ∀ i ∈ List.range 4, RunsAt 25 (64+i) := by decide +kernel

private theorem r25part68 : ∀ i ∈ List.range 4, RunsAt 25 (68+i) := by decide +kernel

private theorem r25part72 : ∀ i ∈ List.range 4, RunsAt 25 (72+i) := by decide +kernel

private theorem r25part76 : ∀ i ∈ List.range 4, RunsAt 25 (76+i) := by decide +kernel

private theorem r25part80 : ∀ i ∈ List.range 4, RunsAt 25 (80+i) := by decide +kernel

private theorem r25part84 : ∀ i ∈ List.range 4, RunsAt 25 (84+i) := by decide +kernel

private theorem r25part88 : ∀ i ∈ List.range 4, RunsAt 25 (88+i) := by decide +kernel

private theorem r25part92 : ∀ i ∈ List.range 4, RunsAt 25 (92+i) := by decide +kernel

private theorem r25part96 : ∀ i ∈ List.range 4, RunsAt 25 (96+i) := by decide +kernel

private theorem r25part100 : ∀ i ∈ List.range 4, RunsAt 25 (100+i) := by decide +kernel

private theorem r25part104 : ∀ i ∈ List.range 4, RunsAt 25 (104+i) := by decide +kernel

private theorem r25part108 : ∀ i ∈ List.range 4, RunsAt 25 (108+i) := by decide +kernel

theorem checkedR25 : ∀ V ∈ List.range 112, RunsAt 25 V := by
  intro V hV
  have hlt : V < 112 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r25part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r25part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r25part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r25part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r25part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r25part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r25part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r25part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r25part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r25part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r25part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r25part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r25part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r25part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r25part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r25part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r25part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r25part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r25part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r25part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r25part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r25part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r25part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r25part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r25part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r25part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r25part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r25part108 (V-108) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp

private theorem r26part0 : ∀ i ∈ List.range 4, RunsAt 26 (0+i) := by decide +kernel

private theorem r26part4 : ∀ i ∈ List.range 4, RunsAt 26 (4+i) := by decide +kernel

private theorem r26part8 : ∀ i ∈ List.range 4, RunsAt 26 (8+i) := by decide +kernel

private theorem r26part12 : ∀ i ∈ List.range 4, RunsAt 26 (12+i) := by decide +kernel

private theorem r26part16 : ∀ i ∈ List.range 4, RunsAt 26 (16+i) := by decide +kernel

private theorem r26part20 : ∀ i ∈ List.range 4, RunsAt 26 (20+i) := by decide +kernel

private theorem r26part24 : ∀ i ∈ List.range 4, RunsAt 26 (24+i) := by decide +kernel

private theorem r26part28 : ∀ i ∈ List.range 4, RunsAt 26 (28+i) := by decide +kernel

private theorem r26part32 : ∀ i ∈ List.range 4, RunsAt 26 (32+i) := by decide +kernel

private theorem r26part36 : ∀ i ∈ List.range 4, RunsAt 26 (36+i) := by decide +kernel

private theorem r26part40 : ∀ i ∈ List.range 4, RunsAt 26 (40+i) := by decide +kernel

private theorem r26part44 : ∀ i ∈ List.range 4, RunsAt 26 (44+i) := by decide +kernel

private theorem r26part48 : ∀ i ∈ List.range 4, RunsAt 26 (48+i) := by decide +kernel

private theorem r26part52 : ∀ i ∈ List.range 4, RunsAt 26 (52+i) := by decide +kernel

private theorem r26part56 : ∀ i ∈ List.range 4, RunsAt 26 (56+i) := by decide +kernel

private theorem r26part60 : ∀ i ∈ List.range 4, RunsAt 26 (60+i) := by decide +kernel

private theorem r26part64 : ∀ i ∈ List.range 4, RunsAt 26 (64+i) := by decide +kernel

private theorem r26part68 : ∀ i ∈ List.range 4, RunsAt 26 (68+i) := by decide +kernel

private theorem r26part72 : ∀ i ∈ List.range 4, RunsAt 26 (72+i) := by decide +kernel

private theorem r26part76 : ∀ i ∈ List.range 4, RunsAt 26 (76+i) := by decide +kernel

private theorem r26part80 : ∀ i ∈ List.range 4, RunsAt 26 (80+i) := by decide +kernel

private theorem r26part84 : ∀ i ∈ List.range 4, RunsAt 26 (84+i) := by decide +kernel

private theorem r26part88 : ∀ i ∈ List.range 4, RunsAt 26 (88+i) := by decide +kernel

private theorem r26part92 : ∀ i ∈ List.range 4, RunsAt 26 (92+i) := by decide +kernel

private theorem r26part96 : ∀ i ∈ List.range 4, RunsAt 26 (96+i) := by decide +kernel

private theorem r26part100 : ∀ i ∈ List.range 4, RunsAt 26 (100+i) := by decide +kernel

private theorem r26part104 : ∀ i ∈ List.range 4, RunsAt 26 (104+i) := by decide +kernel

private theorem r26part108 : ∀ i ∈ List.range 3, RunsAt 26 (108+i) := by decide +kernel

theorem checkedR26 : ∀ V ∈ List.range 111, RunsAt 26 V := by
  intro V hV
  have hlt : V < 111 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r26part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r26part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r26part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r26part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r26part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r26part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r26part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r26part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r26part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r26part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r26part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r26part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r26part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r26part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r26part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r26part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r26part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r26part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r26part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r26part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r26part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r26part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r26part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r26part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r26part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r26part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r26part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r26part108 (V-108) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp

private theorem r27part0 : ∀ i ∈ List.range 4, RunsAt 27 (0+i) := by decide +kernel

private theorem r27part4 : ∀ i ∈ List.range 4, RunsAt 27 (4+i) := by decide +kernel

private theorem r27part8 : ∀ i ∈ List.range 4, RunsAt 27 (8+i) := by decide +kernel

private theorem r27part12 : ∀ i ∈ List.range 4, RunsAt 27 (12+i) := by decide +kernel

private theorem r27part16 : ∀ i ∈ List.range 4, RunsAt 27 (16+i) := by decide +kernel

private theorem r27part20 : ∀ i ∈ List.range 4, RunsAt 27 (20+i) := by decide +kernel

private theorem r27part24 : ∀ i ∈ List.range 4, RunsAt 27 (24+i) := by decide +kernel

private theorem r27part28 : ∀ i ∈ List.range 4, RunsAt 27 (28+i) := by decide +kernel

private theorem r27part32 : ∀ i ∈ List.range 4, RunsAt 27 (32+i) := by decide +kernel

private theorem r27part36 : ∀ i ∈ List.range 4, RunsAt 27 (36+i) := by decide +kernel

private theorem r27part40 : ∀ i ∈ List.range 4, RunsAt 27 (40+i) := by decide +kernel

private theorem r27part44 : ∀ i ∈ List.range 4, RunsAt 27 (44+i) := by decide +kernel

private theorem r27part48 : ∀ i ∈ List.range 4, RunsAt 27 (48+i) := by decide +kernel

private theorem r27part52 : ∀ i ∈ List.range 4, RunsAt 27 (52+i) := by decide +kernel

private theorem r27part56 : ∀ i ∈ List.range 4, RunsAt 27 (56+i) := by decide +kernel

private theorem r27part60 : ∀ i ∈ List.range 4, RunsAt 27 (60+i) := by decide +kernel

private theorem r27part64 : ∀ i ∈ List.range 4, RunsAt 27 (64+i) := by decide +kernel

private theorem r27part68 : ∀ i ∈ List.range 4, RunsAt 27 (68+i) := by decide +kernel

private theorem r27part72 : ∀ i ∈ List.range 4, RunsAt 27 (72+i) := by decide +kernel

private theorem r27part76 : ∀ i ∈ List.range 4, RunsAt 27 (76+i) := by decide +kernel

private theorem r27part80 : ∀ i ∈ List.range 4, RunsAt 27 (80+i) := by decide +kernel

private theorem r27part84 : ∀ i ∈ List.range 4, RunsAt 27 (84+i) := by decide +kernel

private theorem r27part88 : ∀ i ∈ List.range 4, RunsAt 27 (88+i) := by decide +kernel

private theorem r27part92 : ∀ i ∈ List.range 4, RunsAt 27 (92+i) := by decide +kernel

private theorem r27part96 : ∀ i ∈ List.range 4, RunsAt 27 (96+i) := by decide +kernel

private theorem r27part100 : ∀ i ∈ List.range 4, RunsAt 27 (100+i) := by decide +kernel

private theorem r27part104 : ∀ i ∈ List.range 4, RunsAt 27 (104+i) := by decide +kernel

private theorem r27part108 : ∀ i ∈ List.range 2, RunsAt 27 (108+i) := by decide +kernel

theorem checkedR27 : ∀ V ∈ List.range 110, RunsAt 27 V := by
  intro V hV
  have hlt : V < 110 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r27part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r27part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r27part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r27part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r27part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r27part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r27part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r27part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r27part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r27part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r27part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r27part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r27part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r27part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r27part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r27part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r27part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r27part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r27part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r27part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r27part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r27part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r27part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r27part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r27part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r27part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r27part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r27part108 (V-108) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp

private theorem r28part0 : ∀ i ∈ List.range 4, RunsAt 28 (0+i) := by decide +kernel

private theorem r28part4 : ∀ i ∈ List.range 4, RunsAt 28 (4+i) := by decide +kernel

private theorem r28part8 : ∀ i ∈ List.range 4, RunsAt 28 (8+i) := by decide +kernel

private theorem r28part12 : ∀ i ∈ List.range 4, RunsAt 28 (12+i) := by decide +kernel

private theorem r28part16 : ∀ i ∈ List.range 4, RunsAt 28 (16+i) := by decide +kernel

private theorem r28part20 : ∀ i ∈ List.range 4, RunsAt 28 (20+i) := by decide +kernel

private theorem r28part24 : ∀ i ∈ List.range 4, RunsAt 28 (24+i) := by decide +kernel

private theorem r28part28 : ∀ i ∈ List.range 4, RunsAt 28 (28+i) := by decide +kernel

private theorem r28part32 : ∀ i ∈ List.range 4, RunsAt 28 (32+i) := by decide +kernel

private theorem r28part36 : ∀ i ∈ List.range 4, RunsAt 28 (36+i) := by decide +kernel

private theorem r28part40 : ∀ i ∈ List.range 4, RunsAt 28 (40+i) := by decide +kernel

private theorem r28part44 : ∀ i ∈ List.range 4, RunsAt 28 (44+i) := by decide +kernel

private theorem r28part48 : ∀ i ∈ List.range 4, RunsAt 28 (48+i) := by decide +kernel

private theorem r28part52 : ∀ i ∈ List.range 4, RunsAt 28 (52+i) := by decide +kernel

private theorem r28part56 : ∀ i ∈ List.range 4, RunsAt 28 (56+i) := by decide +kernel

private theorem r28part60 : ∀ i ∈ List.range 4, RunsAt 28 (60+i) := by decide +kernel

private theorem r28part64 : ∀ i ∈ List.range 4, RunsAt 28 (64+i) := by decide +kernel

private theorem r28part68 : ∀ i ∈ List.range 4, RunsAt 28 (68+i) := by decide +kernel

private theorem r28part72 : ∀ i ∈ List.range 4, RunsAt 28 (72+i) := by decide +kernel

private theorem r28part76 : ∀ i ∈ List.range 4, RunsAt 28 (76+i) := by decide +kernel

private theorem r28part80 : ∀ i ∈ List.range 4, RunsAt 28 (80+i) := by decide +kernel

private theorem r28part84 : ∀ i ∈ List.range 4, RunsAt 28 (84+i) := by decide +kernel

private theorem r28part88 : ∀ i ∈ List.range 4, RunsAt 28 (88+i) := by decide +kernel

private theorem r28part92 : ∀ i ∈ List.range 4, RunsAt 28 (92+i) := by decide +kernel

private theorem r28part96 : ∀ i ∈ List.range 4, RunsAt 28 (96+i) := by decide +kernel

private theorem r28part100 : ∀ i ∈ List.range 4, RunsAt 28 (100+i) := by decide +kernel

private theorem r28part104 : ∀ i ∈ List.range 4, RunsAt 28 (104+i) := by decide +kernel

private theorem r28part108 : ∀ i ∈ List.range 1, RunsAt 28 (108+i) := by decide +kernel

theorem checkedR28 : ∀ V ∈ List.range 109, RunsAt 28 V := by
  intro V hV
  have hlt : V < 109 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r28part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r28part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r28part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r28part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r28part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r28part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r28part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r28part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r28part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r28part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r28part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r28part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r28part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r28part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r28part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r28part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r28part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r28part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r28part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r28part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r28part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r28part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r28part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r28part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r28part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r28part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  by_cases h108 : V < 108
  · have hp := r28part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r28part108 (V-108) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using hp

private theorem r29part0 : ∀ i ∈ List.range 4, RunsAt 29 (0+i) := by decide +kernel

private theorem r29part4 : ∀ i ∈ List.range 4, RunsAt 29 (4+i) := by decide +kernel

private theorem r29part8 : ∀ i ∈ List.range 4, RunsAt 29 (8+i) := by decide +kernel

private theorem r29part12 : ∀ i ∈ List.range 4, RunsAt 29 (12+i) := by decide +kernel

private theorem r29part16 : ∀ i ∈ List.range 4, RunsAt 29 (16+i) := by decide +kernel

private theorem r29part20 : ∀ i ∈ List.range 4, RunsAt 29 (20+i) := by decide +kernel

private theorem r29part24 : ∀ i ∈ List.range 4, RunsAt 29 (24+i) := by decide +kernel

private theorem r29part28 : ∀ i ∈ List.range 4, RunsAt 29 (28+i) := by decide +kernel

private theorem r29part32 : ∀ i ∈ List.range 4, RunsAt 29 (32+i) := by decide +kernel

private theorem r29part36 : ∀ i ∈ List.range 4, RunsAt 29 (36+i) := by decide +kernel

private theorem r29part40 : ∀ i ∈ List.range 4, RunsAt 29 (40+i) := by decide +kernel

private theorem r29part44 : ∀ i ∈ List.range 4, RunsAt 29 (44+i) := by decide +kernel

private theorem r29part48 : ∀ i ∈ List.range 4, RunsAt 29 (48+i) := by decide +kernel

private theorem r29part52 : ∀ i ∈ List.range 4, RunsAt 29 (52+i) := by decide +kernel

private theorem r29part56 : ∀ i ∈ List.range 4, RunsAt 29 (56+i) := by decide +kernel

private theorem r29part60 : ∀ i ∈ List.range 4, RunsAt 29 (60+i) := by decide +kernel

private theorem r29part64 : ∀ i ∈ List.range 4, RunsAt 29 (64+i) := by decide +kernel

private theorem r29part68 : ∀ i ∈ List.range 4, RunsAt 29 (68+i) := by decide +kernel

private theorem r29part72 : ∀ i ∈ List.range 4, RunsAt 29 (72+i) := by decide +kernel

private theorem r29part76 : ∀ i ∈ List.range 4, RunsAt 29 (76+i) := by decide +kernel

private theorem r29part80 : ∀ i ∈ List.range 4, RunsAt 29 (80+i) := by decide +kernel

private theorem r29part84 : ∀ i ∈ List.range 4, RunsAt 29 (84+i) := by decide +kernel

private theorem r29part88 : ∀ i ∈ List.range 4, RunsAt 29 (88+i) := by decide +kernel

private theorem r29part92 : ∀ i ∈ List.range 4, RunsAt 29 (92+i) := by decide +kernel

private theorem r29part96 : ∀ i ∈ List.range 4, RunsAt 29 (96+i) := by decide +kernel

private theorem r29part100 : ∀ i ∈ List.range 4, RunsAt 29 (100+i) := by decide +kernel

private theorem r29part104 : ∀ i ∈ List.range 4, RunsAt 29 (104+i) := by decide +kernel

theorem checkedR29 : ∀ V ∈ List.range 108, RunsAt 29 V := by
  intro V hV
  have hlt : V < 108 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r29part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r29part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r29part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r29part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r29part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r29part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r29part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r29part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r29part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r29part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r29part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r29part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r29part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r29part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r29part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r29part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r29part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r29part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r29part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r29part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r29part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r29part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r29part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r29part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r29part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r29part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  have hp := r29part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

private theorem r30part0 : ∀ i ∈ List.range 4, RunsAt 30 (0+i) := by decide +kernel

private theorem r30part4 : ∀ i ∈ List.range 4, RunsAt 30 (4+i) := by decide +kernel

private theorem r30part8 : ∀ i ∈ List.range 4, RunsAt 30 (8+i) := by decide +kernel

private theorem r30part12 : ∀ i ∈ List.range 4, RunsAt 30 (12+i) := by decide +kernel

private theorem r30part16 : ∀ i ∈ List.range 4, RunsAt 30 (16+i) := by decide +kernel

private theorem r30part20 : ∀ i ∈ List.range 4, RunsAt 30 (20+i) := by decide +kernel

private theorem r30part24 : ∀ i ∈ List.range 4, RunsAt 30 (24+i) := by decide +kernel

private theorem r30part28 : ∀ i ∈ List.range 4, RunsAt 30 (28+i) := by decide +kernel

private theorem r30part32 : ∀ i ∈ List.range 4, RunsAt 30 (32+i) := by decide +kernel

private theorem r30part36 : ∀ i ∈ List.range 4, RunsAt 30 (36+i) := by decide +kernel

private theorem r30part40 : ∀ i ∈ List.range 4, RunsAt 30 (40+i) := by decide +kernel

private theorem r30part44 : ∀ i ∈ List.range 4, RunsAt 30 (44+i) := by decide +kernel

private theorem r30part48 : ∀ i ∈ List.range 4, RunsAt 30 (48+i) := by decide +kernel

private theorem r30part52 : ∀ i ∈ List.range 4, RunsAt 30 (52+i) := by decide +kernel

private theorem r30part56 : ∀ i ∈ List.range 4, RunsAt 30 (56+i) := by decide +kernel

private theorem r30part60 : ∀ i ∈ List.range 4, RunsAt 30 (60+i) := by decide +kernel

private theorem r30part64 : ∀ i ∈ List.range 4, RunsAt 30 (64+i) := by decide +kernel

private theorem r30part68 : ∀ i ∈ List.range 4, RunsAt 30 (68+i) := by decide +kernel

private theorem r30part72 : ∀ i ∈ List.range 4, RunsAt 30 (72+i) := by decide +kernel

private theorem r30part76 : ∀ i ∈ List.range 4, RunsAt 30 (76+i) := by decide +kernel

private theorem r30part80 : ∀ i ∈ List.range 4, RunsAt 30 (80+i) := by decide +kernel

private theorem r30part84 : ∀ i ∈ List.range 4, RunsAt 30 (84+i) := by decide +kernel

private theorem r30part88 : ∀ i ∈ List.range 4, RunsAt 30 (88+i) := by decide +kernel

private theorem r30part92 : ∀ i ∈ List.range 4, RunsAt 30 (92+i) := by decide +kernel

private theorem r30part96 : ∀ i ∈ List.range 4, RunsAt 30 (96+i) := by decide +kernel

private theorem r30part100 : ∀ i ∈ List.range 4, RunsAt 30 (100+i) := by decide +kernel

private theorem r30part104 : ∀ i ∈ List.range 3, RunsAt 30 (104+i) := by decide +kernel

theorem checkedR30 : ∀ V ∈ List.range 107, RunsAt 30 V := by
  intro V hV
  have hlt : V < 107 := List.mem_range.mp hV
  by_cases h4 : V < 4
  · have hp := r30part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 8
  · have hp := r30part4 (V-4) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using hp
  by_cases h12 : V < 12
  · have hp := r30part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 16
  · have hp := r30part12 (V-12) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using hp
  by_cases h20 : V < 20
  · have hp := r30part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 24
  · have hp := r30part20 (V-20) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using hp
  by_cases h28 : V < 28
  · have hp := r30part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 32
  · have hp := r30part28 (V-28) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using hp
  by_cases h36 : V < 36
  · have hp := r30part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 40
  · have hp := r30part36 (V-36) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using hp
  by_cases h44 : V < 44
  · have hp := r30part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 48
  · have hp := r30part44 (V-44) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using hp
  by_cases h52 : V < 52
  · have hp := r30part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 56
  · have hp := r30part52 (V-52) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using hp
  by_cases h60 : V < 60
  · have hp := r30part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 64
  · have hp := r30part60 (V-60) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using hp
  by_cases h68 : V < 68
  · have hp := r30part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 72
  · have hp := r30part68 (V-68) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using hp
  by_cases h76 : V < 76
  · have hp := r30part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 80
  · have hp := r30part76 (V-76) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using hp
  by_cases h84 : V < 84
  · have hp := r30part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 88
  · have hp := r30part84 (V-84) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using hp
  by_cases h92 : V < 92
  · have hp := r30part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 96
  · have hp := r30part92 (V-92) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using hp
  by_cases h100 : V < 100
  · have hp := r30part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 104
  · have hp := r30part100 (V-100) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using hp
  have hp := r30part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

theorem checked : ∀ r ∈ List.range 31, 1 ≤ r →
    ∀ v ∈ List.range (137-r), RunsAt r v := by
  intro r hr hpos
  have hlt : r < 31 := List.mem_range.mp hr
  interval_cases r <;> first
    | exact checkedR1
    | exact checkedR2
    | exact checkedR3
    | exact checkedR4
    | exact checkedR5
    | exact checkedR6
    | exact checkedR7
    | exact checkedR8
    | exact checkedR9
    | exact checkedR10
    | exact checkedR11
    | exact checkedR12
    | exact checkedR13
    | exact checkedR14
    | exact checkedR15
    | exact checkedR16
    | exact checkedR17
    | exact checkedR18
    | exact checkedR19
    | exact checkedR20
    | exact checkedR21
    | exact checkedR22
    | exact checkedR23
    | exact checkedR24
    | exact checkedR25
    | exact checkedR26
    | exact checkedR27
    | exact checkedR28
    | exact checkedR29
    | exact checkedR30

end ProximityPrize.SubmissionLower.Lower80791.RunsChecked

end Compact_RunsChecked80791

section Compact_ThresholdCompressed80791
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.ThresholdCompressed
open Lower80791.CompressedData Lower80791.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem r1part0 : ∀ i ∈ List.range 8, HybridAt 1 (0+i) := by decide +kernel

private theorem r1part8 : ∀ i ∈ List.range 8, HybridAt 1 (8+i) := by decide +kernel

private theorem r1part16 : ∀ i ∈ List.range 8, HybridAt 1 (16+i) := by decide +kernel

private theorem r1part24 : ∀ i ∈ List.range 8, HybridAt 1 (24+i) := by decide +kernel

private theorem r1part32 : ∀ i ∈ List.range 8, HybridAt 1 (32+i) := by decide +kernel

private theorem r1part40 : ∀ i ∈ List.range 8, HybridAt 1 (40+i) := by decide +kernel

private theorem r1part48 : ∀ i ∈ List.range 8, HybridAt 1 (48+i) := by decide +kernel

private theorem r1part56 : ∀ i ∈ List.range 8, HybridAt 1 (56+i) := by decide +kernel

private theorem r1part64 : ∀ i ∈ List.range 8, HybridAt 1 (64+i) := by decide +kernel

private theorem r1part72 : ∀ i ∈ List.range 8, HybridAt 1 (72+i) := by decide +kernel

private theorem r1part80 : ∀ i ∈ List.range 8, HybridAt 1 (80+i) := by decide +kernel

private theorem r1part88 : ∀ i ∈ List.range 8, HybridAt 1 (88+i) := by decide +kernel

private theorem r1part96 : ∀ i ∈ List.range 8, HybridAt 1 (96+i) := by decide +kernel

private theorem r1part104 : ∀ i ∈ List.range 8, HybridAt 1 (104+i) := by decide +kernel

private theorem r1part112 : ∀ i ∈ List.range 8, HybridAt 1 (112+i) := by decide +kernel

private theorem r1part120 : ∀ i ∈ List.range 8, HybridAt 1 (120+i) := by decide +kernel

private theorem r1part128 : ∀ i ∈ List.range 8, HybridAt 1 (128+i) := by decide +kernel

theorem checkedR1 : ∀ v ∈ List.range 136, HybridAt 1 v := by
  intro v hv
  have hlt : v < 136 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r1part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r1part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r1part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r1part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r1part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r1part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r1part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r1part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r1part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r1part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r1part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r1part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r1part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r1part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r1part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  by_cases h128 : v < 128
  · have hp := r1part120 (v-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp
  have hp := r1part128 (v-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ v by omega)] using hp

private theorem r2part0 : ∀ i ∈ List.range 8, HybridAt 2 (0+i) := by decide +kernel

private theorem r2part8 : ∀ i ∈ List.range 8, HybridAt 2 (8+i) := by decide +kernel

private theorem r2part16 : ∀ i ∈ List.range 8, HybridAt 2 (16+i) := by decide +kernel

private theorem r2part24 : ∀ i ∈ List.range 8, HybridAt 2 (24+i) := by decide +kernel

private theorem r2part32 : ∀ i ∈ List.range 8, HybridAt 2 (32+i) := by decide +kernel

private theorem r2part40 : ∀ i ∈ List.range 8, HybridAt 2 (40+i) := by decide +kernel

private theorem r2part48 : ∀ i ∈ List.range 8, HybridAt 2 (48+i) := by decide +kernel

private theorem r2part56 : ∀ i ∈ List.range 8, HybridAt 2 (56+i) := by decide +kernel

private theorem r2part64 : ∀ i ∈ List.range 8, HybridAt 2 (64+i) := by decide +kernel

private theorem r2part72 : ∀ i ∈ List.range 8, HybridAt 2 (72+i) := by decide +kernel

private theorem r2part80 : ∀ i ∈ List.range 8, HybridAt 2 (80+i) := by decide +kernel

private theorem r2part88 : ∀ i ∈ List.range 8, HybridAt 2 (88+i) := by decide +kernel

private theorem r2part96 : ∀ i ∈ List.range 8, HybridAt 2 (96+i) := by decide +kernel

private theorem r2part104 : ∀ i ∈ List.range 8, HybridAt 2 (104+i) := by decide +kernel

private theorem r2part112 : ∀ i ∈ List.range 8, HybridAt 2 (112+i) := by decide +kernel

private theorem r2part120 : ∀ i ∈ List.range 8, HybridAt 2 (120+i) := by decide +kernel

private theorem r2part128 : ∀ i ∈ List.range 7, HybridAt 2 (128+i) := by decide +kernel

theorem checkedR2 : ∀ v ∈ List.range 135, HybridAt 2 v := by
  intro v hv
  have hlt : v < 135 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r2part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r2part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r2part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r2part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r2part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r2part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r2part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r2part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r2part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r2part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r2part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r2part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r2part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r2part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r2part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  by_cases h128 : v < 128
  · have hp := r2part120 (v-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp
  have hp := r2part128 (v-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ v by omega)] using hp

private theorem r3part0 : ∀ i ∈ List.range 8, HybridAt 3 (0+i) := by decide +kernel

private theorem r3part8 : ∀ i ∈ List.range 8, HybridAt 3 (8+i) := by decide +kernel

private theorem r3part16 : ∀ i ∈ List.range 8, HybridAt 3 (16+i) := by decide +kernel

private theorem r3part24 : ∀ i ∈ List.range 8, HybridAt 3 (24+i) := by decide +kernel

private theorem r3part32 : ∀ i ∈ List.range 8, HybridAt 3 (32+i) := by decide +kernel

private theorem r3part40 : ∀ i ∈ List.range 8, HybridAt 3 (40+i) := by decide +kernel

private theorem r3part48 : ∀ i ∈ List.range 8, HybridAt 3 (48+i) := by decide +kernel

private theorem r3part56 : ∀ i ∈ List.range 8, HybridAt 3 (56+i) := by decide +kernel

private theorem r3part64 : ∀ i ∈ List.range 8, HybridAt 3 (64+i) := by decide +kernel

private theorem r3part72 : ∀ i ∈ List.range 8, HybridAt 3 (72+i) := by decide +kernel

private theorem r3part80 : ∀ i ∈ List.range 8, HybridAt 3 (80+i) := by decide +kernel

private theorem r3part88 : ∀ i ∈ List.range 8, HybridAt 3 (88+i) := by decide +kernel

private theorem r3part96 : ∀ i ∈ List.range 8, HybridAt 3 (96+i) := by decide +kernel

private theorem r3part104 : ∀ i ∈ List.range 8, HybridAt 3 (104+i) := by decide +kernel

private theorem r3part112 : ∀ i ∈ List.range 8, HybridAt 3 (112+i) := by decide +kernel

private theorem r3part120 : ∀ i ∈ List.range 8, HybridAt 3 (120+i) := by decide +kernel

private theorem r3part128 : ∀ i ∈ List.range 6, HybridAt 3 (128+i) := by decide +kernel

theorem checkedR3 : ∀ v ∈ List.range 134, HybridAt 3 v := by
  intro v hv
  have hlt : v < 134 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r3part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r3part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r3part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r3part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r3part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r3part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r3part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r3part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r3part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r3part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r3part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r3part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r3part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r3part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r3part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  by_cases h128 : v < 128
  · have hp := r3part120 (v-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp
  have hp := r3part128 (v-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ v by omega)] using hp

private theorem r4part0 : ∀ i ∈ List.range 8, HybridAt 4 (0+i) := by decide +kernel

private theorem r4part8 : ∀ i ∈ List.range 8, HybridAt 4 (8+i) := by decide +kernel

private theorem r4part16 : ∀ i ∈ List.range 8, HybridAt 4 (16+i) := by decide +kernel

private theorem r4part24 : ∀ i ∈ List.range 8, HybridAt 4 (24+i) := by decide +kernel

private theorem r4part32 : ∀ i ∈ List.range 8, HybridAt 4 (32+i) := by decide +kernel

private theorem r4part40 : ∀ i ∈ List.range 8, HybridAt 4 (40+i) := by decide +kernel

private theorem r4part48 : ∀ i ∈ List.range 8, HybridAt 4 (48+i) := by decide +kernel

private theorem r4part56 : ∀ i ∈ List.range 8, HybridAt 4 (56+i) := by decide +kernel

private theorem r4part64 : ∀ i ∈ List.range 8, HybridAt 4 (64+i) := by decide +kernel

private theorem r4part72 : ∀ i ∈ List.range 8, HybridAt 4 (72+i) := by decide +kernel

private theorem r4part80 : ∀ i ∈ List.range 8, HybridAt 4 (80+i) := by decide +kernel

private theorem r4part88 : ∀ i ∈ List.range 8, HybridAt 4 (88+i) := by decide +kernel

private theorem r4part96 : ∀ i ∈ List.range 8, HybridAt 4 (96+i) := by decide +kernel

private theorem r4part104 : ∀ i ∈ List.range 8, HybridAt 4 (104+i) := by decide +kernel

private theorem r4part112 : ∀ i ∈ List.range 8, HybridAt 4 (112+i) := by decide +kernel

private theorem r4part120 : ∀ i ∈ List.range 8, HybridAt 4 (120+i) := by decide +kernel

private theorem r4part128 : ∀ i ∈ List.range 5, HybridAt 4 (128+i) := by decide +kernel

theorem checkedR4 : ∀ v ∈ List.range 133, HybridAt 4 v := by
  intro v hv
  have hlt : v < 133 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r4part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r4part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r4part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r4part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r4part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r4part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r4part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r4part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r4part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r4part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r4part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r4part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r4part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r4part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r4part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  by_cases h128 : v < 128
  · have hp := r4part120 (v-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp
  have hp := r4part128 (v-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ v by omega)] using hp

private theorem r5part0 : ∀ i ∈ List.range 8, HybridAt 5 (0+i) := by decide +kernel

private theorem r5part8 : ∀ i ∈ List.range 8, HybridAt 5 (8+i) := by decide +kernel

private theorem r5part16 : ∀ i ∈ List.range 8, HybridAt 5 (16+i) := by decide +kernel

private theorem r5part24 : ∀ i ∈ List.range 8, HybridAt 5 (24+i) := by decide +kernel

private theorem r5part32 : ∀ i ∈ List.range 8, HybridAt 5 (32+i) := by decide +kernel

private theorem r5part40 : ∀ i ∈ List.range 8, HybridAt 5 (40+i) := by decide +kernel

private theorem r5part48 : ∀ i ∈ List.range 8, HybridAt 5 (48+i) := by decide +kernel

private theorem r5part56 : ∀ i ∈ List.range 8, HybridAt 5 (56+i) := by decide +kernel

private theorem r5part64 : ∀ i ∈ List.range 8, HybridAt 5 (64+i) := by decide +kernel

private theorem r5part72 : ∀ i ∈ List.range 8, HybridAt 5 (72+i) := by decide +kernel

private theorem r5part80 : ∀ i ∈ List.range 8, HybridAt 5 (80+i) := by decide +kernel

private theorem r5part88 : ∀ i ∈ List.range 8, HybridAt 5 (88+i) := by decide +kernel

private theorem r5part96 : ∀ i ∈ List.range 8, HybridAt 5 (96+i) := by decide +kernel

private theorem r5part104 : ∀ i ∈ List.range 8, HybridAt 5 (104+i) := by decide +kernel

private theorem r5part112 : ∀ i ∈ List.range 8, HybridAt 5 (112+i) := by decide +kernel

private theorem r5part120 : ∀ i ∈ List.range 8, HybridAt 5 (120+i) := by decide +kernel

private theorem r5part128 : ∀ i ∈ List.range 4, HybridAt 5 (128+i) := by decide +kernel

theorem checkedR5 : ∀ v ∈ List.range 132, HybridAt 5 v := by
  intro v hv
  have hlt : v < 132 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r5part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r5part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r5part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r5part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r5part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r5part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r5part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r5part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r5part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r5part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r5part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r5part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r5part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r5part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r5part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  by_cases h128 : v < 128
  · have hp := r5part120 (v-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp
  have hp := r5part128 (v-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ v by omega)] using hp

private theorem r6part0 : ∀ i ∈ List.range 8, HybridAt 6 (0+i) := by decide +kernel

private theorem r6part8 : ∀ i ∈ List.range 8, HybridAt 6 (8+i) := by decide +kernel

private theorem r6part16 : ∀ i ∈ List.range 8, HybridAt 6 (16+i) := by decide +kernel

private theorem r6part24 : ∀ i ∈ List.range 8, HybridAt 6 (24+i) := by decide +kernel

private theorem r6part32 : ∀ i ∈ List.range 8, HybridAt 6 (32+i) := by decide +kernel

private theorem r6part40 : ∀ i ∈ List.range 8, HybridAt 6 (40+i) := by decide +kernel

private theorem r6part48 : ∀ i ∈ List.range 8, HybridAt 6 (48+i) := by decide +kernel

private theorem r6part56 : ∀ i ∈ List.range 8, HybridAt 6 (56+i) := by decide +kernel

private theorem r6part64 : ∀ i ∈ List.range 8, HybridAt 6 (64+i) := by decide +kernel

private theorem r6part72 : ∀ i ∈ List.range 8, HybridAt 6 (72+i) := by decide +kernel

private theorem r6part80 : ∀ i ∈ List.range 8, HybridAt 6 (80+i) := by decide +kernel

private theorem r6part88 : ∀ i ∈ List.range 8, HybridAt 6 (88+i) := by decide +kernel

private theorem r6part96 : ∀ i ∈ List.range 8, HybridAt 6 (96+i) := by decide +kernel

private theorem r6part104 : ∀ i ∈ List.range 8, HybridAt 6 (104+i) := by decide +kernel

private theorem r6part112 : ∀ i ∈ List.range 8, HybridAt 6 (112+i) := by decide +kernel

private theorem r6part120 : ∀ i ∈ List.range 8, HybridAt 6 (120+i) := by decide +kernel

private theorem r6part128 : ∀ i ∈ List.range 3, HybridAt 6 (128+i) := by decide +kernel

theorem checkedR6 : ∀ v ∈ List.range 131, HybridAt 6 v := by
  intro v hv
  have hlt : v < 131 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r6part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r6part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r6part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r6part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r6part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r6part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r6part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r6part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r6part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r6part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r6part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r6part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r6part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r6part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r6part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  by_cases h128 : v < 128
  · have hp := r6part120 (v-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp
  have hp := r6part128 (v-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ v by omega)] using hp

private theorem r7part0 : ∀ i ∈ List.range 8, HybridAt 7 (0+i) := by decide +kernel

private theorem r7part8 : ∀ i ∈ List.range 8, HybridAt 7 (8+i) := by decide +kernel

private theorem r7part16 : ∀ i ∈ List.range 8, HybridAt 7 (16+i) := by decide +kernel

private theorem r7part24 : ∀ i ∈ List.range 8, HybridAt 7 (24+i) := by decide +kernel

private theorem r7part32 : ∀ i ∈ List.range 8, HybridAt 7 (32+i) := by decide +kernel

private theorem r7part40 : ∀ i ∈ List.range 8, HybridAt 7 (40+i) := by decide +kernel

private theorem r7part48 : ∀ i ∈ List.range 8, HybridAt 7 (48+i) := by decide +kernel

private theorem r7part56 : ∀ i ∈ List.range 8, HybridAt 7 (56+i) := by decide +kernel

private theorem r7part64 : ∀ i ∈ List.range 8, HybridAt 7 (64+i) := by decide +kernel

private theorem r7part72 : ∀ i ∈ List.range 8, HybridAt 7 (72+i) := by decide +kernel

private theorem r7part80 : ∀ i ∈ List.range 8, HybridAt 7 (80+i) := by decide +kernel

private theorem r7part88 : ∀ i ∈ List.range 8, HybridAt 7 (88+i) := by decide +kernel

private theorem r7part96 : ∀ i ∈ List.range 8, HybridAt 7 (96+i) := by decide +kernel

private theorem r7part104 : ∀ i ∈ List.range 8, HybridAt 7 (104+i) := by decide +kernel

private theorem r7part112 : ∀ i ∈ List.range 8, HybridAt 7 (112+i) := by decide +kernel

private theorem r7part120 : ∀ i ∈ List.range 8, HybridAt 7 (120+i) := by decide +kernel

private theorem r7part128 : ∀ i ∈ List.range 2, HybridAt 7 (128+i) := by decide +kernel

theorem checkedR7 : ∀ v ∈ List.range 130, HybridAt 7 v := by
  intro v hv
  have hlt : v < 130 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r7part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r7part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r7part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r7part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r7part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r7part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r7part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r7part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r7part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r7part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r7part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r7part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r7part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r7part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r7part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  by_cases h128 : v < 128
  · have hp := r7part120 (v-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp
  have hp := r7part128 (v-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ v by omega)] using hp

private theorem r8part0 : ∀ i ∈ List.range 8, HybridAt 8 (0+i) := by decide +kernel

private theorem r8part8 : ∀ i ∈ List.range 8, HybridAt 8 (8+i) := by decide +kernel

private theorem r8part16 : ∀ i ∈ List.range 8, HybridAt 8 (16+i) := by decide +kernel

private theorem r8part24 : ∀ i ∈ List.range 8, HybridAt 8 (24+i) := by decide +kernel

private theorem r8part32 : ∀ i ∈ List.range 8, HybridAt 8 (32+i) := by decide +kernel

private theorem r8part40 : ∀ i ∈ List.range 8, HybridAt 8 (40+i) := by decide +kernel

private theorem r8part48 : ∀ i ∈ List.range 8, HybridAt 8 (48+i) := by decide +kernel

private theorem r8part56 : ∀ i ∈ List.range 8, HybridAt 8 (56+i) := by decide +kernel

private theorem r8part64 : ∀ i ∈ List.range 8, HybridAt 8 (64+i) := by decide +kernel

private theorem r8part72 : ∀ i ∈ List.range 8, HybridAt 8 (72+i) := by decide +kernel

private theorem r8part80 : ∀ i ∈ List.range 8, HybridAt 8 (80+i) := by decide +kernel

private theorem r8part88 : ∀ i ∈ List.range 8, HybridAt 8 (88+i) := by decide +kernel

private theorem r8part96 : ∀ i ∈ List.range 8, HybridAt 8 (96+i) := by decide +kernel

private theorem r8part104 : ∀ i ∈ List.range 8, HybridAt 8 (104+i) := by decide +kernel

private theorem r8part112 : ∀ i ∈ List.range 8, HybridAt 8 (112+i) := by decide +kernel

private theorem r8part120 : ∀ i ∈ List.range 8, HybridAt 8 (120+i) := by decide +kernel

private theorem r8part128 : ∀ i ∈ List.range 1, HybridAt 8 (128+i) := by decide +kernel

theorem checkedR8 : ∀ v ∈ List.range 129, HybridAt 8 v := by
  intro v hv
  have hlt : v < 129 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r8part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r8part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r8part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r8part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r8part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r8part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r8part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r8part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r8part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r8part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r8part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r8part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r8part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r8part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r8part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  by_cases h128 : v < 128
  · have hp := r8part120 (v-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp
  have hp := r8part128 (v-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ v by omega)] using hp

private theorem r9part0 : ∀ i ∈ List.range 8, HybridAt 9 (0+i) := by decide +kernel

private theorem r9part8 : ∀ i ∈ List.range 8, HybridAt 9 (8+i) := by decide +kernel

private theorem r9part16 : ∀ i ∈ List.range 8, HybridAt 9 (16+i) := by decide +kernel

private theorem r9part24 : ∀ i ∈ List.range 8, HybridAt 9 (24+i) := by decide +kernel

private theorem r9part32 : ∀ i ∈ List.range 8, HybridAt 9 (32+i) := by decide +kernel

private theorem r9part40 : ∀ i ∈ List.range 8, HybridAt 9 (40+i) := by decide +kernel

private theorem r9part48 : ∀ i ∈ List.range 8, HybridAt 9 (48+i) := by decide +kernel

private theorem r9part56 : ∀ i ∈ List.range 8, HybridAt 9 (56+i) := by decide +kernel

private theorem r9part64 : ∀ i ∈ List.range 8, HybridAt 9 (64+i) := by decide +kernel

private theorem r9part72 : ∀ i ∈ List.range 8, HybridAt 9 (72+i) := by decide +kernel

private theorem r9part80 : ∀ i ∈ List.range 8, HybridAt 9 (80+i) := by decide +kernel

private theorem r9part88 : ∀ i ∈ List.range 8, HybridAt 9 (88+i) := by decide +kernel

private theorem r9part96 : ∀ i ∈ List.range 8, HybridAt 9 (96+i) := by decide +kernel

private theorem r9part104 : ∀ i ∈ List.range 8, HybridAt 9 (104+i) := by decide +kernel

private theorem r9part112 : ∀ i ∈ List.range 8, HybridAt 9 (112+i) := by decide +kernel

private theorem r9part120 : ∀ i ∈ List.range 8, HybridAt 9 (120+i) := by decide +kernel

theorem checkedR9 : ∀ v ∈ List.range 128, HybridAt 9 v := by
  intro v hv
  have hlt : v < 128 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r9part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r9part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r9part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r9part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r9part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r9part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r9part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r9part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r9part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r9part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r9part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r9part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r9part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r9part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r9part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  have hp := r9part120 (v-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp

private theorem r10part0 : ∀ i ∈ List.range 8, HybridAt 10 (0+i) := by decide +kernel

private theorem r10part8 : ∀ i ∈ List.range 8, HybridAt 10 (8+i) := by decide +kernel

private theorem r10part16 : ∀ i ∈ List.range 8, HybridAt 10 (16+i) := by decide +kernel

private theorem r10part24 : ∀ i ∈ List.range 8, HybridAt 10 (24+i) := by decide +kernel

private theorem r10part32 : ∀ i ∈ List.range 8, HybridAt 10 (32+i) := by decide +kernel

private theorem r10part40 : ∀ i ∈ List.range 8, HybridAt 10 (40+i) := by decide +kernel

private theorem r10part48 : ∀ i ∈ List.range 8, HybridAt 10 (48+i) := by decide +kernel

private theorem r10part56 : ∀ i ∈ List.range 8, HybridAt 10 (56+i) := by decide +kernel

private theorem r10part64 : ∀ i ∈ List.range 8, HybridAt 10 (64+i) := by decide +kernel

private theorem r10part72 : ∀ i ∈ List.range 8, HybridAt 10 (72+i) := by decide +kernel

private theorem r10part80 : ∀ i ∈ List.range 8, HybridAt 10 (80+i) := by decide +kernel

private theorem r10part88 : ∀ i ∈ List.range 8, HybridAt 10 (88+i) := by decide +kernel

private theorem r10part96 : ∀ i ∈ List.range 8, HybridAt 10 (96+i) := by decide +kernel

private theorem r10part104 : ∀ i ∈ List.range 8, HybridAt 10 (104+i) := by decide +kernel

private theorem r10part112 : ∀ i ∈ List.range 8, HybridAt 10 (112+i) := by decide +kernel

private theorem r10part120 : ∀ i ∈ List.range 7, HybridAt 10 (120+i) := by decide +kernel

theorem checkedR10 : ∀ v ∈ List.range 127, HybridAt 10 v := by
  intro v hv
  have hlt : v < 127 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r10part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r10part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r10part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r10part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r10part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r10part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r10part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r10part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r10part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r10part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r10part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r10part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r10part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r10part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r10part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  have hp := r10part120 (v-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp

private theorem r11part0 : ∀ i ∈ List.range 8, HybridAt 11 (0+i) := by decide +kernel

private theorem r11part8 : ∀ i ∈ List.range 8, HybridAt 11 (8+i) := by decide +kernel

private theorem r11part16 : ∀ i ∈ List.range 8, HybridAt 11 (16+i) := by decide +kernel

private theorem r11part24 : ∀ i ∈ List.range 8, HybridAt 11 (24+i) := by decide +kernel

private theorem r11part32 : ∀ i ∈ List.range 8, HybridAt 11 (32+i) := by decide +kernel

private theorem r11part40 : ∀ i ∈ List.range 8, HybridAt 11 (40+i) := by decide +kernel

private theorem r11part48 : ∀ i ∈ List.range 8, HybridAt 11 (48+i) := by decide +kernel

private theorem r11part56 : ∀ i ∈ List.range 8, HybridAt 11 (56+i) := by decide +kernel

private theorem r11part64 : ∀ i ∈ List.range 8, HybridAt 11 (64+i) := by decide +kernel

private theorem r11part72 : ∀ i ∈ List.range 8, HybridAt 11 (72+i) := by decide +kernel

private theorem r11part80 : ∀ i ∈ List.range 8, HybridAt 11 (80+i) := by decide +kernel

private theorem r11part88 : ∀ i ∈ List.range 8, HybridAt 11 (88+i) := by decide +kernel

private theorem r11part96 : ∀ i ∈ List.range 8, HybridAt 11 (96+i) := by decide +kernel

private theorem r11part104 : ∀ i ∈ List.range 8, HybridAt 11 (104+i) := by decide +kernel

private theorem r11part112 : ∀ i ∈ List.range 8, HybridAt 11 (112+i) := by decide +kernel

private theorem r11part120 : ∀ i ∈ List.range 6, HybridAt 11 (120+i) := by decide +kernel

theorem checkedR11 : ∀ v ∈ List.range 126, HybridAt 11 v := by
  intro v hv
  have hlt : v < 126 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r11part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r11part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r11part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r11part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r11part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r11part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r11part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r11part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r11part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r11part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r11part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r11part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r11part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r11part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r11part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  have hp := r11part120 (v-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp

private theorem r12part0 : ∀ i ∈ List.range 8, HybridAt 12 (0+i) := by decide +kernel

private theorem r12part8 : ∀ i ∈ List.range 8, HybridAt 12 (8+i) := by decide +kernel

private theorem r12part16 : ∀ i ∈ List.range 8, HybridAt 12 (16+i) := by decide +kernel

private theorem r12part24 : ∀ i ∈ List.range 8, HybridAt 12 (24+i) := by decide +kernel

private theorem r12part32 : ∀ i ∈ List.range 8, HybridAt 12 (32+i) := by decide +kernel

private theorem r12part40 : ∀ i ∈ List.range 8, HybridAt 12 (40+i) := by decide +kernel

private theorem r12part48 : ∀ i ∈ List.range 8, HybridAt 12 (48+i) := by decide +kernel

private theorem r12part56 : ∀ i ∈ List.range 8, HybridAt 12 (56+i) := by decide +kernel

private theorem r12part64 : ∀ i ∈ List.range 8, HybridAt 12 (64+i) := by decide +kernel

private theorem r12part72 : ∀ i ∈ List.range 8, HybridAt 12 (72+i) := by decide +kernel

private theorem r12part80 : ∀ i ∈ List.range 8, HybridAt 12 (80+i) := by decide +kernel

private theorem r12part88 : ∀ i ∈ List.range 8, HybridAt 12 (88+i) := by decide +kernel

private theorem r12part96 : ∀ i ∈ List.range 8, HybridAt 12 (96+i) := by decide +kernel

private theorem r12part104 : ∀ i ∈ List.range 8, HybridAt 12 (104+i) := by decide +kernel

private theorem r12part112 : ∀ i ∈ List.range 8, HybridAt 12 (112+i) := by decide +kernel

private theorem r12part120 : ∀ i ∈ List.range 5, HybridAt 12 (120+i) := by decide +kernel

theorem checkedR12 : ∀ v ∈ List.range 125, HybridAt 12 v := by
  intro v hv
  have hlt : v < 125 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r12part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r12part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r12part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r12part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r12part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r12part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r12part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r12part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r12part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r12part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r12part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r12part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r12part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r12part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r12part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  have hp := r12part120 (v-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp

private theorem r13part0 : ∀ i ∈ List.range 8, HybridAt 13 (0+i) := by decide +kernel

private theorem r13part8 : ∀ i ∈ List.range 8, HybridAt 13 (8+i) := by decide +kernel

private theorem r13part16 : ∀ i ∈ List.range 8, HybridAt 13 (16+i) := by decide +kernel

private theorem r13part24 : ∀ i ∈ List.range 8, HybridAt 13 (24+i) := by decide +kernel

private theorem r13part32 : ∀ i ∈ List.range 8, HybridAt 13 (32+i) := by decide +kernel

private theorem r13part40 : ∀ i ∈ List.range 8, HybridAt 13 (40+i) := by decide +kernel

private theorem r13part48 : ∀ i ∈ List.range 8, HybridAt 13 (48+i) := by decide +kernel

private theorem r13part56 : ∀ i ∈ List.range 8, HybridAt 13 (56+i) := by decide +kernel

private theorem r13part64 : ∀ i ∈ List.range 8, HybridAt 13 (64+i) := by decide +kernel

private theorem r13part72 : ∀ i ∈ List.range 8, HybridAt 13 (72+i) := by decide +kernel

private theorem r13part80 : ∀ i ∈ List.range 8, HybridAt 13 (80+i) := by decide +kernel

private theorem r13part88 : ∀ i ∈ List.range 8, HybridAt 13 (88+i) := by decide +kernel

private theorem r13part96 : ∀ i ∈ List.range 8, HybridAt 13 (96+i) := by decide +kernel

private theorem r13part104 : ∀ i ∈ List.range 8, HybridAt 13 (104+i) := by decide +kernel

private theorem r13part112 : ∀ i ∈ List.range 8, HybridAt 13 (112+i) := by decide +kernel

private theorem r13part120 : ∀ i ∈ List.range 4, HybridAt 13 (120+i) := by decide +kernel

theorem checkedR13 : ∀ v ∈ List.range 124, HybridAt 13 v := by
  intro v hv
  have hlt : v < 124 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r13part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r13part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r13part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r13part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r13part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r13part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r13part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r13part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r13part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r13part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r13part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r13part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r13part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r13part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r13part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  have hp := r13part120 (v-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp

private theorem r14part0 : ∀ i ∈ List.range 8, HybridAt 14 (0+i) := by decide +kernel

private theorem r14part8 : ∀ i ∈ List.range 8, HybridAt 14 (8+i) := by decide +kernel

private theorem r14part16 : ∀ i ∈ List.range 8, HybridAt 14 (16+i) := by decide +kernel

private theorem r14part24 : ∀ i ∈ List.range 8, HybridAt 14 (24+i) := by decide +kernel

private theorem r14part32 : ∀ i ∈ List.range 8, HybridAt 14 (32+i) := by decide +kernel

private theorem r14part40 : ∀ i ∈ List.range 8, HybridAt 14 (40+i) := by decide +kernel

private theorem r14part48 : ∀ i ∈ List.range 8, HybridAt 14 (48+i) := by decide +kernel

private theorem r14part56 : ∀ i ∈ List.range 8, HybridAt 14 (56+i) := by decide +kernel

private theorem r14part64 : ∀ i ∈ List.range 8, HybridAt 14 (64+i) := by decide +kernel

private theorem r14part72 : ∀ i ∈ List.range 8, HybridAt 14 (72+i) := by decide +kernel

private theorem r14part80 : ∀ i ∈ List.range 8, HybridAt 14 (80+i) := by decide +kernel

private theorem r14part88 : ∀ i ∈ List.range 8, HybridAt 14 (88+i) := by decide +kernel

private theorem r14part96 : ∀ i ∈ List.range 8, HybridAt 14 (96+i) := by decide +kernel

private theorem r14part104 : ∀ i ∈ List.range 8, HybridAt 14 (104+i) := by decide +kernel

private theorem r14part112 : ∀ i ∈ List.range 8, HybridAt 14 (112+i) := by decide +kernel

private theorem r14part120 : ∀ i ∈ List.range 3, HybridAt 14 (120+i) := by decide +kernel

theorem checkedR14 : ∀ v ∈ List.range 123, HybridAt 14 v := by
  intro v hv
  have hlt : v < 123 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r14part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r14part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r14part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r14part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r14part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r14part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r14part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r14part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r14part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r14part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r14part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r14part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r14part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r14part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r14part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  have hp := r14part120 (v-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp

private theorem r15part0 : ∀ i ∈ List.range 8, HybridAt 15 (0+i) := by decide +kernel

private theorem r15part8 : ∀ i ∈ List.range 8, HybridAt 15 (8+i) := by decide +kernel

private theorem r15part16 : ∀ i ∈ List.range 8, HybridAt 15 (16+i) := by decide +kernel

private theorem r15part24 : ∀ i ∈ List.range 8, HybridAt 15 (24+i) := by decide +kernel

private theorem r15part32 : ∀ i ∈ List.range 8, HybridAt 15 (32+i) := by decide +kernel

private theorem r15part40 : ∀ i ∈ List.range 8, HybridAt 15 (40+i) := by decide +kernel

private theorem r15part48 : ∀ i ∈ List.range 8, HybridAt 15 (48+i) := by decide +kernel

private theorem r15part56 : ∀ i ∈ List.range 8, HybridAt 15 (56+i) := by decide +kernel

private theorem r15part64 : ∀ i ∈ List.range 8, HybridAt 15 (64+i) := by decide +kernel

private theorem r15part72 : ∀ i ∈ List.range 8, HybridAt 15 (72+i) := by decide +kernel

private theorem r15part80 : ∀ i ∈ List.range 8, HybridAt 15 (80+i) := by decide +kernel

private theorem r15part88 : ∀ i ∈ List.range 8, HybridAt 15 (88+i) := by decide +kernel

private theorem r15part96 : ∀ i ∈ List.range 8, HybridAt 15 (96+i) := by decide +kernel

private theorem r15part104 : ∀ i ∈ List.range 8, HybridAt 15 (104+i) := by decide +kernel

private theorem r15part112 : ∀ i ∈ List.range 8, HybridAt 15 (112+i) := by decide +kernel

private theorem r15part120 : ∀ i ∈ List.range 2, HybridAt 15 (120+i) := by decide +kernel

theorem checkedR15 : ∀ v ∈ List.range 122, HybridAt 15 v := by
  intro v hv
  have hlt : v < 122 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r15part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r15part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r15part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r15part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r15part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r15part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r15part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r15part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r15part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r15part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r15part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r15part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r15part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r15part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r15part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  have hp := r15part120 (v-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp

private theorem r16part0 : ∀ i ∈ List.range 8, HybridAt 16 (0+i) := by decide +kernel

private theorem r16part8 : ∀ i ∈ List.range 8, HybridAt 16 (8+i) := by decide +kernel

private theorem r16part16 : ∀ i ∈ List.range 8, HybridAt 16 (16+i) := by decide +kernel

private theorem r16part24 : ∀ i ∈ List.range 8, HybridAt 16 (24+i) := by decide +kernel

private theorem r16part32 : ∀ i ∈ List.range 8, HybridAt 16 (32+i) := by decide +kernel

private theorem r16part40 : ∀ i ∈ List.range 8, HybridAt 16 (40+i) := by decide +kernel

private theorem r16part48 : ∀ i ∈ List.range 8, HybridAt 16 (48+i) := by decide +kernel

private theorem r16part56 : ∀ i ∈ List.range 8, HybridAt 16 (56+i) := by decide +kernel

private theorem r16part64 : ∀ i ∈ List.range 8, HybridAt 16 (64+i) := by decide +kernel

private theorem r16part72 : ∀ i ∈ List.range 8, HybridAt 16 (72+i) := by decide +kernel

private theorem r16part80 : ∀ i ∈ List.range 8, HybridAt 16 (80+i) := by decide +kernel

private theorem r16part88 : ∀ i ∈ List.range 8, HybridAt 16 (88+i) := by decide +kernel

private theorem r16part96 : ∀ i ∈ List.range 8, HybridAt 16 (96+i) := by decide +kernel

private theorem r16part104 : ∀ i ∈ List.range 8, HybridAt 16 (104+i) := by decide +kernel

private theorem r16part112 : ∀ i ∈ List.range 8, HybridAt 16 (112+i) := by decide +kernel

private theorem r16part120 : ∀ i ∈ List.range 1, HybridAt 16 (120+i) := by decide +kernel

theorem checkedR16 : ∀ v ∈ List.range 121, HybridAt 16 v := by
  intro v hv
  have hlt : v < 121 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r16part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r16part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r16part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r16part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r16part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r16part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r16part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r16part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r16part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r16part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r16part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r16part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r16part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r16part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  by_cases h120 : v < 120
  · have hp := r16part112 (v-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp
  have hp := r16part120 (v-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ v by omega)] using hp

private theorem r17part0 : ∀ i ∈ List.range 8, HybridAt 17 (0+i) := by decide +kernel

private theorem r17part8 : ∀ i ∈ List.range 8, HybridAt 17 (8+i) := by decide +kernel

private theorem r17part16 : ∀ i ∈ List.range 8, HybridAt 17 (16+i) := by decide +kernel

private theorem r17part24 : ∀ i ∈ List.range 8, HybridAt 17 (24+i) := by decide +kernel

private theorem r17part32 : ∀ i ∈ List.range 8, HybridAt 17 (32+i) := by decide +kernel

private theorem r17part40 : ∀ i ∈ List.range 8, HybridAt 17 (40+i) := by decide +kernel

private theorem r17part48 : ∀ i ∈ List.range 8, HybridAt 17 (48+i) := by decide +kernel

private theorem r17part56 : ∀ i ∈ List.range 8, HybridAt 17 (56+i) := by decide +kernel

private theorem r17part64 : ∀ i ∈ List.range 8, HybridAt 17 (64+i) := by decide +kernel

private theorem r17part72 : ∀ i ∈ List.range 8, HybridAt 17 (72+i) := by decide +kernel

private theorem r17part80 : ∀ i ∈ List.range 8, HybridAt 17 (80+i) := by decide +kernel

private theorem r17part88 : ∀ i ∈ List.range 8, HybridAt 17 (88+i) := by decide +kernel

private theorem r17part96 : ∀ i ∈ List.range 8, HybridAt 17 (96+i) := by decide +kernel

private theorem r17part104 : ∀ i ∈ List.range 8, HybridAt 17 (104+i) := by decide +kernel

private theorem r17part112 : ∀ i ∈ List.range 8, HybridAt 17 (112+i) := by decide +kernel

theorem checkedR17 : ∀ v ∈ List.range 120, HybridAt 17 v := by
  intro v hv
  have hlt : v < 120 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r17part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r17part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r17part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r17part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r17part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r17part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r17part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r17part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r17part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r17part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r17part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r17part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r17part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r17part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  have hp := r17part112 (v-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp

private theorem r18part0 : ∀ i ∈ List.range 8, HybridAt 18 (0+i) := by decide +kernel

private theorem r18part8 : ∀ i ∈ List.range 8, HybridAt 18 (8+i) := by decide +kernel

private theorem r18part16 : ∀ i ∈ List.range 8, HybridAt 18 (16+i) := by decide +kernel

private theorem r18part24 : ∀ i ∈ List.range 8, HybridAt 18 (24+i) := by decide +kernel

private theorem r18part32 : ∀ i ∈ List.range 8, HybridAt 18 (32+i) := by decide +kernel

private theorem r18part40 : ∀ i ∈ List.range 8, HybridAt 18 (40+i) := by decide +kernel

private theorem r18part48 : ∀ i ∈ List.range 8, HybridAt 18 (48+i) := by decide +kernel

private theorem r18part56 : ∀ i ∈ List.range 8, HybridAt 18 (56+i) := by decide +kernel

private theorem r18part64 : ∀ i ∈ List.range 8, HybridAt 18 (64+i) := by decide +kernel

private theorem r18part72 : ∀ i ∈ List.range 8, HybridAt 18 (72+i) := by decide +kernel

private theorem r18part80 : ∀ i ∈ List.range 8, HybridAt 18 (80+i) := by decide +kernel

private theorem r18part88 : ∀ i ∈ List.range 8, HybridAt 18 (88+i) := by decide +kernel

private theorem r18part96 : ∀ i ∈ List.range 8, HybridAt 18 (96+i) := by decide +kernel

private theorem r18part104 : ∀ i ∈ List.range 8, HybridAt 18 (104+i) := by decide +kernel

private theorem r18part112 : ∀ i ∈ List.range 7, HybridAt 18 (112+i) := by decide +kernel

theorem checkedR18 : ∀ v ∈ List.range 119, HybridAt 18 v := by
  intro v hv
  have hlt : v < 119 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r18part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r18part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r18part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r18part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r18part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r18part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r18part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r18part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r18part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r18part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r18part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r18part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r18part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r18part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  have hp := r18part112 (v-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp

private theorem r19part0 : ∀ i ∈ List.range 8, HybridAt 19 (0+i) := by decide +kernel

private theorem r19part8 : ∀ i ∈ List.range 8, HybridAt 19 (8+i) := by decide +kernel

private theorem r19part16 : ∀ i ∈ List.range 8, HybridAt 19 (16+i) := by decide +kernel

private theorem r19part24 : ∀ i ∈ List.range 8, HybridAt 19 (24+i) := by decide +kernel

private theorem r19part32 : ∀ i ∈ List.range 8, HybridAt 19 (32+i) := by decide +kernel

private theorem r19part40 : ∀ i ∈ List.range 8, HybridAt 19 (40+i) := by decide +kernel

private theorem r19part48 : ∀ i ∈ List.range 8, HybridAt 19 (48+i) := by decide +kernel

private theorem r19part56 : ∀ i ∈ List.range 8, HybridAt 19 (56+i) := by decide +kernel

private theorem r19part64 : ∀ i ∈ List.range 8, HybridAt 19 (64+i) := by decide +kernel

private theorem r19part72 : ∀ i ∈ List.range 8, HybridAt 19 (72+i) := by decide +kernel

private theorem r19part80 : ∀ i ∈ List.range 8, HybridAt 19 (80+i) := by decide +kernel

private theorem r19part88 : ∀ i ∈ List.range 8, HybridAt 19 (88+i) := by decide +kernel

private theorem r19part96 : ∀ i ∈ List.range 8, HybridAt 19 (96+i) := by decide +kernel

private theorem r19part104 : ∀ i ∈ List.range 8, HybridAt 19 (104+i) := by decide +kernel

private theorem r19part112 : ∀ i ∈ List.range 6, HybridAt 19 (112+i) := by decide +kernel

theorem checkedR19 : ∀ v ∈ List.range 118, HybridAt 19 v := by
  intro v hv
  have hlt : v < 118 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r19part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r19part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r19part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r19part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r19part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r19part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r19part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r19part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r19part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r19part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r19part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r19part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r19part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r19part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  have hp := r19part112 (v-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp

private theorem r20part0 : ∀ i ∈ List.range 8, HybridAt 20 (0+i) := by decide +kernel

private theorem r20part8 : ∀ i ∈ List.range 8, HybridAt 20 (8+i) := by decide +kernel

private theorem r20part16 : ∀ i ∈ List.range 8, HybridAt 20 (16+i) := by decide +kernel

private theorem r20part24 : ∀ i ∈ List.range 8, HybridAt 20 (24+i) := by decide +kernel

private theorem r20part32 : ∀ i ∈ List.range 8, HybridAt 20 (32+i) := by decide +kernel

private theorem r20part40 : ∀ i ∈ List.range 8, HybridAt 20 (40+i) := by decide +kernel

private theorem r20part48 : ∀ i ∈ List.range 8, HybridAt 20 (48+i) := by decide +kernel

private theorem r20part56 : ∀ i ∈ List.range 8, HybridAt 20 (56+i) := by decide +kernel

private theorem r20part64 : ∀ i ∈ List.range 8, HybridAt 20 (64+i) := by decide +kernel

private theorem r20part72 : ∀ i ∈ List.range 8, HybridAt 20 (72+i) := by decide +kernel

private theorem r20part80 : ∀ i ∈ List.range 8, HybridAt 20 (80+i) := by decide +kernel

private theorem r20part88 : ∀ i ∈ List.range 8, HybridAt 20 (88+i) := by decide +kernel

private theorem r20part96 : ∀ i ∈ List.range 8, HybridAt 20 (96+i) := by decide +kernel

private theorem r20part104 : ∀ i ∈ List.range 8, HybridAt 20 (104+i) := by decide +kernel

private theorem r20part112 : ∀ i ∈ List.range 5, HybridAt 20 (112+i) := by decide +kernel

theorem checkedR20 : ∀ v ∈ List.range 117, HybridAt 20 v := by
  intro v hv
  have hlt : v < 117 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r20part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r20part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r20part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r20part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r20part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r20part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r20part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r20part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r20part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r20part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r20part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r20part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r20part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r20part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  have hp := r20part112 (v-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp

private theorem r21part0 : ∀ i ∈ List.range 8, HybridAt 21 (0+i) := by decide +kernel

private theorem r21part8 : ∀ i ∈ List.range 8, HybridAt 21 (8+i) := by decide +kernel

private theorem r21part16 : ∀ i ∈ List.range 8, HybridAt 21 (16+i) := by decide +kernel

private theorem r21part24 : ∀ i ∈ List.range 8, HybridAt 21 (24+i) := by decide +kernel

private theorem r21part32 : ∀ i ∈ List.range 8, HybridAt 21 (32+i) := by decide +kernel

private theorem r21part40 : ∀ i ∈ List.range 8, HybridAt 21 (40+i) := by decide +kernel

private theorem r21part48 : ∀ i ∈ List.range 8, HybridAt 21 (48+i) := by decide +kernel

private theorem r21part56 : ∀ i ∈ List.range 8, HybridAt 21 (56+i) := by decide +kernel

private theorem r21part64 : ∀ i ∈ List.range 8, HybridAt 21 (64+i) := by decide +kernel

private theorem r21part72 : ∀ i ∈ List.range 8, HybridAt 21 (72+i) := by decide +kernel

private theorem r21part80 : ∀ i ∈ List.range 8, HybridAt 21 (80+i) := by decide +kernel

private theorem r21part88 : ∀ i ∈ List.range 8, HybridAt 21 (88+i) := by decide +kernel

private theorem r21part96 : ∀ i ∈ List.range 8, HybridAt 21 (96+i) := by decide +kernel

private theorem r21part104 : ∀ i ∈ List.range 8, HybridAt 21 (104+i) := by decide +kernel

private theorem r21part112 : ∀ i ∈ List.range 4, HybridAt 21 (112+i) := by decide +kernel

theorem checkedR21 : ∀ v ∈ List.range 116, HybridAt 21 v := by
  intro v hv
  have hlt : v < 116 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r21part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r21part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r21part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r21part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r21part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r21part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r21part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r21part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r21part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r21part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r21part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r21part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r21part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r21part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  have hp := r21part112 (v-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp

private theorem r22part0 : ∀ i ∈ List.range 8, HybridAt 22 (0+i) := by decide +kernel

private theorem r22part8 : ∀ i ∈ List.range 8, HybridAt 22 (8+i) := by decide +kernel

private theorem r22part16 : ∀ i ∈ List.range 8, HybridAt 22 (16+i) := by decide +kernel

private theorem r22part24 : ∀ i ∈ List.range 8, HybridAt 22 (24+i) := by decide +kernel

private theorem r22part32 : ∀ i ∈ List.range 8, HybridAt 22 (32+i) := by decide +kernel

private theorem r22part40 : ∀ i ∈ List.range 8, HybridAt 22 (40+i) := by decide +kernel

private theorem r22part48 : ∀ i ∈ List.range 8, HybridAt 22 (48+i) := by decide +kernel

private theorem r22part56 : ∀ i ∈ List.range 8, HybridAt 22 (56+i) := by decide +kernel

private theorem r22part64 : ∀ i ∈ List.range 8, HybridAt 22 (64+i) := by decide +kernel

private theorem r22part72 : ∀ i ∈ List.range 8, HybridAt 22 (72+i) := by decide +kernel

private theorem r22part80 : ∀ i ∈ List.range 8, HybridAt 22 (80+i) := by decide +kernel

private theorem r22part88 : ∀ i ∈ List.range 8, HybridAt 22 (88+i) := by decide +kernel

private theorem r22part96 : ∀ i ∈ List.range 8, HybridAt 22 (96+i) := by decide +kernel

private theorem r22part104 : ∀ i ∈ List.range 8, HybridAt 22 (104+i) := by decide +kernel

private theorem r22part112 : ∀ i ∈ List.range 3, HybridAt 22 (112+i) := by decide +kernel

theorem checkedR22 : ∀ v ∈ List.range 115, HybridAt 22 v := by
  intro v hv
  have hlt : v < 115 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r22part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r22part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r22part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r22part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r22part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r22part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r22part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r22part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r22part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r22part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r22part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r22part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r22part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r22part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  have hp := r22part112 (v-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp

private theorem r23part0 : ∀ i ∈ List.range 8, HybridAt 23 (0+i) := by decide +kernel

private theorem r23part8 : ∀ i ∈ List.range 8, HybridAt 23 (8+i) := by decide +kernel

private theorem r23part16 : ∀ i ∈ List.range 8, HybridAt 23 (16+i) := by decide +kernel

private theorem r23part24 : ∀ i ∈ List.range 8, HybridAt 23 (24+i) := by decide +kernel

private theorem r23part32 : ∀ i ∈ List.range 8, HybridAt 23 (32+i) := by decide +kernel

private theorem r23part40 : ∀ i ∈ List.range 8, HybridAt 23 (40+i) := by decide +kernel

private theorem r23part48 : ∀ i ∈ List.range 8, HybridAt 23 (48+i) := by decide +kernel

private theorem r23part56 : ∀ i ∈ List.range 8, HybridAt 23 (56+i) := by decide +kernel

private theorem r23part64 : ∀ i ∈ List.range 8, HybridAt 23 (64+i) := by decide +kernel

private theorem r23part72 : ∀ i ∈ List.range 8, HybridAt 23 (72+i) := by decide +kernel

private theorem r23part80 : ∀ i ∈ List.range 8, HybridAt 23 (80+i) := by decide +kernel

private theorem r23part88 : ∀ i ∈ List.range 8, HybridAt 23 (88+i) := by decide +kernel

private theorem r23part96 : ∀ i ∈ List.range 8, HybridAt 23 (96+i) := by decide +kernel

private theorem r23part104 : ∀ i ∈ List.range 8, HybridAt 23 (104+i) := by decide +kernel

private theorem r23part112 : ∀ i ∈ List.range 2, HybridAt 23 (112+i) := by decide +kernel

theorem checkedR23 : ∀ v ∈ List.range 114, HybridAt 23 v := by
  intro v hv
  have hlt : v < 114 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r23part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r23part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r23part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r23part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r23part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r23part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r23part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r23part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r23part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r23part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r23part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r23part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r23part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r23part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  have hp := r23part112 (v-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp

private theorem r24part0 : ∀ i ∈ List.range 8, HybridAt 24 (0+i) := by decide +kernel

private theorem r24part8 : ∀ i ∈ List.range 8, HybridAt 24 (8+i) := by decide +kernel

private theorem r24part16 : ∀ i ∈ List.range 8, HybridAt 24 (16+i) := by decide +kernel

private theorem r24part24 : ∀ i ∈ List.range 8, HybridAt 24 (24+i) := by decide +kernel

private theorem r24part32 : ∀ i ∈ List.range 8, HybridAt 24 (32+i) := by decide +kernel

private theorem r24part40 : ∀ i ∈ List.range 8, HybridAt 24 (40+i) := by decide +kernel

private theorem r24part48 : ∀ i ∈ List.range 8, HybridAt 24 (48+i) := by decide +kernel

private theorem r24part56 : ∀ i ∈ List.range 8, HybridAt 24 (56+i) := by decide +kernel

private theorem r24part64 : ∀ i ∈ List.range 8, HybridAt 24 (64+i) := by decide +kernel

private theorem r24part72 : ∀ i ∈ List.range 8, HybridAt 24 (72+i) := by decide +kernel

private theorem r24part80 : ∀ i ∈ List.range 8, HybridAt 24 (80+i) := by decide +kernel

private theorem r24part88 : ∀ i ∈ List.range 8, HybridAt 24 (88+i) := by decide +kernel

private theorem r24part96 : ∀ i ∈ List.range 8, HybridAt 24 (96+i) := by decide +kernel

private theorem r24part104 : ∀ i ∈ List.range 8, HybridAt 24 (104+i) := by decide +kernel

private theorem r24part112 : ∀ i ∈ List.range 1, HybridAt 24 (112+i) := by decide +kernel

theorem checkedR24 : ∀ v ∈ List.range 113, HybridAt 24 v := by
  intro v hv
  have hlt : v < 113 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r24part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r24part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r24part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r24part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r24part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r24part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r24part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r24part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r24part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r24part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r24part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r24part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r24part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  by_cases h112 : v < 112
  · have hp := r24part104 (v-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp
  have hp := r24part112 (v-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ v by omega)] using hp

private theorem r25part0 : ∀ i ∈ List.range 8, HybridAt 25 (0+i) := by decide +kernel

private theorem r25part8 : ∀ i ∈ List.range 8, HybridAt 25 (8+i) := by decide +kernel

private theorem r25part16 : ∀ i ∈ List.range 8, HybridAt 25 (16+i) := by decide +kernel

private theorem r25part24 : ∀ i ∈ List.range 8, HybridAt 25 (24+i) := by decide +kernel

private theorem r25part32 : ∀ i ∈ List.range 8, HybridAt 25 (32+i) := by decide +kernel

private theorem r25part40 : ∀ i ∈ List.range 8, HybridAt 25 (40+i) := by decide +kernel

private theorem r25part48 : ∀ i ∈ List.range 8, HybridAt 25 (48+i) := by decide +kernel

private theorem r25part56 : ∀ i ∈ List.range 8, HybridAt 25 (56+i) := by decide +kernel

private theorem r25part64 : ∀ i ∈ List.range 8, HybridAt 25 (64+i) := by decide +kernel

private theorem r25part72 : ∀ i ∈ List.range 8, HybridAt 25 (72+i) := by decide +kernel

private theorem r25part80 : ∀ i ∈ List.range 8, HybridAt 25 (80+i) := by decide +kernel

private theorem r25part88 : ∀ i ∈ List.range 8, HybridAt 25 (88+i) := by decide +kernel

private theorem r25part96 : ∀ i ∈ List.range 8, HybridAt 25 (96+i) := by decide +kernel

private theorem r25part104 : ∀ i ∈ List.range 8, HybridAt 25 (104+i) := by decide +kernel

theorem checkedR25 : ∀ v ∈ List.range 112, HybridAt 25 v := by
  intro v hv
  have hlt : v < 112 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r25part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r25part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r25part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r25part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r25part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r25part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r25part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r25part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r25part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r25part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r25part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r25part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r25part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  have hp := r25part104 (v-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp

private theorem r26part0 : ∀ i ∈ List.range 8, HybridAt 26 (0+i) := by decide +kernel

private theorem r26part8 : ∀ i ∈ List.range 8, HybridAt 26 (8+i) := by decide +kernel

private theorem r26part16 : ∀ i ∈ List.range 8, HybridAt 26 (16+i) := by decide +kernel

private theorem r26part24 : ∀ i ∈ List.range 8, HybridAt 26 (24+i) := by decide +kernel

private theorem r26part32 : ∀ i ∈ List.range 8, HybridAt 26 (32+i) := by decide +kernel

private theorem r26part40 : ∀ i ∈ List.range 8, HybridAt 26 (40+i) := by decide +kernel

private theorem r26part48 : ∀ i ∈ List.range 8, HybridAt 26 (48+i) := by decide +kernel

private theorem r26part56 : ∀ i ∈ List.range 8, HybridAt 26 (56+i) := by decide +kernel

private theorem r26part64 : ∀ i ∈ List.range 8, HybridAt 26 (64+i) := by decide +kernel

private theorem r26part72 : ∀ i ∈ List.range 8, HybridAt 26 (72+i) := by decide +kernel

private theorem r26part80 : ∀ i ∈ List.range 8, HybridAt 26 (80+i) := by decide +kernel

private theorem r26part88 : ∀ i ∈ List.range 8, HybridAt 26 (88+i) := by decide +kernel

private theorem r26part96 : ∀ i ∈ List.range 8, HybridAt 26 (96+i) := by decide +kernel

private theorem r26part104 : ∀ i ∈ List.range 7, HybridAt 26 (104+i) := by decide +kernel

theorem checkedR26 : ∀ v ∈ List.range 111, HybridAt 26 v := by
  intro v hv
  have hlt : v < 111 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r26part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r26part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r26part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r26part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r26part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r26part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r26part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r26part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r26part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r26part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r26part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r26part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r26part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  have hp := r26part104 (v-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp

private theorem r27part0 : ∀ i ∈ List.range 8, HybridAt 27 (0+i) := by decide +kernel

private theorem r27part8 : ∀ i ∈ List.range 8, HybridAt 27 (8+i) := by decide +kernel

private theorem r27part16 : ∀ i ∈ List.range 8, HybridAt 27 (16+i) := by decide +kernel

private theorem r27part24 : ∀ i ∈ List.range 8, HybridAt 27 (24+i) := by decide +kernel

private theorem r27part32 : ∀ i ∈ List.range 8, HybridAt 27 (32+i) := by decide +kernel

private theorem r27part40 : ∀ i ∈ List.range 8, HybridAt 27 (40+i) := by decide +kernel

private theorem r27part48 : ∀ i ∈ List.range 8, HybridAt 27 (48+i) := by decide +kernel

private theorem r27part56 : ∀ i ∈ List.range 8, HybridAt 27 (56+i) := by decide +kernel

private theorem r27part64 : ∀ i ∈ List.range 8, HybridAt 27 (64+i) := by decide +kernel

private theorem r27part72 : ∀ i ∈ List.range 8, HybridAt 27 (72+i) := by decide +kernel

private theorem r27part80 : ∀ i ∈ List.range 8, HybridAt 27 (80+i) := by decide +kernel

private theorem r27part88 : ∀ i ∈ List.range 8, HybridAt 27 (88+i) := by decide +kernel

private theorem r27part96 : ∀ i ∈ List.range 8, HybridAt 27 (96+i) := by decide +kernel

private theorem r27part104 : ∀ i ∈ List.range 6, HybridAt 27 (104+i) := by decide +kernel

theorem checkedR27 : ∀ v ∈ List.range 110, HybridAt 27 v := by
  intro v hv
  have hlt : v < 110 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r27part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r27part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r27part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r27part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r27part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r27part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r27part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r27part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r27part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r27part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r27part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r27part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r27part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  have hp := r27part104 (v-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp

private theorem r28part0 : ∀ i ∈ List.range 8, HybridAt 28 (0+i) := by decide +kernel

private theorem r28part8 : ∀ i ∈ List.range 8, HybridAt 28 (8+i) := by decide +kernel

private theorem r28part16 : ∀ i ∈ List.range 8, HybridAt 28 (16+i) := by decide +kernel

private theorem r28part24 : ∀ i ∈ List.range 8, HybridAt 28 (24+i) := by decide +kernel

private theorem r28part32 : ∀ i ∈ List.range 8, HybridAt 28 (32+i) := by decide +kernel

private theorem r28part40 : ∀ i ∈ List.range 8, HybridAt 28 (40+i) := by decide +kernel

private theorem r28part48 : ∀ i ∈ List.range 8, HybridAt 28 (48+i) := by decide +kernel

private theorem r28part56 : ∀ i ∈ List.range 8, HybridAt 28 (56+i) := by decide +kernel

private theorem r28part64 : ∀ i ∈ List.range 8, HybridAt 28 (64+i) := by decide +kernel

private theorem r28part72 : ∀ i ∈ List.range 8, HybridAt 28 (72+i) := by decide +kernel

private theorem r28part80 : ∀ i ∈ List.range 8, HybridAt 28 (80+i) := by decide +kernel

private theorem r28part88 : ∀ i ∈ List.range 8, HybridAt 28 (88+i) := by decide +kernel

private theorem r28part96 : ∀ i ∈ List.range 8, HybridAt 28 (96+i) := by decide +kernel

private theorem r28part104 : ∀ i ∈ List.range 5, HybridAt 28 (104+i) := by decide +kernel

theorem checkedR28 : ∀ v ∈ List.range 109, HybridAt 28 v := by
  intro v hv
  have hlt : v < 109 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r28part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r28part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r28part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r28part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r28part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r28part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r28part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r28part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r28part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r28part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r28part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r28part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r28part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  have hp := r28part104 (v-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp

private theorem r29part0 : ∀ i ∈ List.range 8, HybridAt 29 (0+i) := by decide +kernel

private theorem r29part8 : ∀ i ∈ List.range 8, HybridAt 29 (8+i) := by decide +kernel

private theorem r29part16 : ∀ i ∈ List.range 8, HybridAt 29 (16+i) := by decide +kernel

private theorem r29part24 : ∀ i ∈ List.range 8, HybridAt 29 (24+i) := by decide +kernel

private theorem r29part32 : ∀ i ∈ List.range 8, HybridAt 29 (32+i) := by decide +kernel

private theorem r29part40 : ∀ i ∈ List.range 8, HybridAt 29 (40+i) := by decide +kernel

private theorem r29part48 : ∀ i ∈ List.range 8, HybridAt 29 (48+i) := by decide +kernel

private theorem r29part56 : ∀ i ∈ List.range 8, HybridAt 29 (56+i) := by decide +kernel

private theorem r29part64 : ∀ i ∈ List.range 8, HybridAt 29 (64+i) := by decide +kernel

private theorem r29part72 : ∀ i ∈ List.range 8, HybridAt 29 (72+i) := by decide +kernel

private theorem r29part80 : ∀ i ∈ List.range 8, HybridAt 29 (80+i) := by decide +kernel

private theorem r29part88 : ∀ i ∈ List.range 8, HybridAt 29 (88+i) := by decide +kernel

private theorem r29part96 : ∀ i ∈ List.range 8, HybridAt 29 (96+i) := by decide +kernel

private theorem r29part104 : ∀ i ∈ List.range 4, HybridAt 29 (104+i) := by decide +kernel

theorem checkedR29 : ∀ v ∈ List.range 108, HybridAt 29 v := by
  intro v hv
  have hlt : v < 108 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r29part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r29part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r29part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r29part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r29part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r29part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r29part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r29part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r29part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r29part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r29part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r29part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r29part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  have hp := r29part104 (v-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp

private theorem r30part0 : ∀ i ∈ List.range 8, HybridAt 30 (0+i) := by decide +kernel

private theorem r30part8 : ∀ i ∈ List.range 8, HybridAt 30 (8+i) := by decide +kernel

private theorem r30part16 : ∀ i ∈ List.range 8, HybridAt 30 (16+i) := by decide +kernel

private theorem r30part24 : ∀ i ∈ List.range 8, HybridAt 30 (24+i) := by decide +kernel

private theorem r30part32 : ∀ i ∈ List.range 8, HybridAt 30 (32+i) := by decide +kernel

private theorem r30part40 : ∀ i ∈ List.range 8, HybridAt 30 (40+i) := by decide +kernel

private theorem r30part48 : ∀ i ∈ List.range 8, HybridAt 30 (48+i) := by decide +kernel

private theorem r30part56 : ∀ i ∈ List.range 8, HybridAt 30 (56+i) := by decide +kernel

private theorem r30part64 : ∀ i ∈ List.range 8, HybridAt 30 (64+i) := by decide +kernel

private theorem r30part72 : ∀ i ∈ List.range 8, HybridAt 30 (72+i) := by decide +kernel

private theorem r30part80 : ∀ i ∈ List.range 8, HybridAt 30 (80+i) := by decide +kernel

private theorem r30part88 : ∀ i ∈ List.range 8, HybridAt 30 (88+i) := by decide +kernel

private theorem r30part96 : ∀ i ∈ List.range 8, HybridAt 30 (96+i) := by decide +kernel

private theorem r30part104 : ∀ i ∈ List.range 3, HybridAt 30 (104+i) := by decide +kernel

theorem checkedR30 : ∀ v ∈ List.range 107, HybridAt 30 v := by
  intro v hv
  have hlt : v < 107 := List.mem_range.mp hv
  by_cases h8 : v < 8
  · have hp := r30part0 (v-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ v by omega)] using hp
  by_cases h16 : v < 16
  · have hp := r30part8 (v-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ v by omega)] using hp
  by_cases h24 : v < 24
  · have hp := r30part16 (v-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ v by omega)] using hp
  by_cases h32 : v < 32
  · have hp := r30part24 (v-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ v by omega)] using hp
  by_cases h40 : v < 40
  · have hp := r30part32 (v-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ v by omega)] using hp
  by_cases h48 : v < 48
  · have hp := r30part40 (v-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ v by omega)] using hp
  by_cases h56 : v < 56
  · have hp := r30part48 (v-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ v by omega)] using hp
  by_cases h64 : v < 64
  · have hp := r30part56 (v-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ v by omega)] using hp
  by_cases h72 : v < 72
  · have hp := r30part64 (v-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ v by omega)] using hp
  by_cases h80 : v < 80
  · have hp := r30part72 (v-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ v by omega)] using hp
  by_cases h88 : v < 88
  · have hp := r30part80 (v-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ v by omega)] using hp
  by_cases h96 : v < 96
  · have hp := r30part88 (v-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ v by omega)] using hp
  by_cases h104 : v < 104
  · have hp := r30part96 (v-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ v by omega)] using hp
  have hp := r30part104 (v-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ v by omega)] using hp

theorem hybridChecked : ∀ r ∈ List.range 31, 1 ≤ r →
    ∀ v ∈ List.range (137-r), HybridAt r v := by
  intro r hr hpos
  have hlt : r < 31 := List.mem_range.mp hr
  interval_cases r <;> first
    | exact checkedR1
    | exact checkedR2
    | exact checkedR3
    | exact checkedR4
    | exact checkedR5
    | exact checkedR6
    | exact checkedR7
    | exact checkedR8
    | exact checkedR9
    | exact checkedR10
    | exact checkedR11
    | exact checkedR12
    | exact checkedR13
    | exact checkedR14
    | exact checkedR15
    | exact checkedR16
    | exact checkedR17
    | exact checkedR18
    | exact checkedR19
    | exact checkedR20
    | exact checkedR21
    | exact checkedR22
    | exact checkedR23
    | exact checkedR24
    | exact checkedR25
    | exact checkedR26
    | exact checkedR27
    | exact checkedR28
    | exact checkedR29
    | exact checkedR30

theorem checked : ∀ r ∈ List.range 31, 1 ≤ r →
    ∀ v ∈ List.range (137-r), ThresholdAt r v := by
  intro r hr hpos v hv
  exact hybrid_sound r v (hybridChecked r hr hpos v hv)
end ProximityPrize.SubmissionLower.Lower80791.ThresholdCompressed

end Compact_ThresholdCompressed80791

section Compact_LedgerData80791
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.LedgerData
open Lower80791.LedgerAudit Lower80791.PhaseData
set_option maxRecDepth 100000

private def row1PackedData : ℕ := 0x3a7e20000000000074fe400000000000ea00800000000001d409000000000003a822000000000007506400000000000ea10800000000001d429000000000003a86200000000000750e400000000000ea20800000000001d449000000000003a8a2000000000007516400000000000ea30800000000001d469000000000003a8e200000000000751e400000000000ea40800000000001d489000000000003a922000000000007526400000000000ea50800000000001d4a9000000000003a96200000000000752e400000000000ea60800000000001d4c9000000000003a9a2000000000007536400000000000ea70800000000001d4e9000000000003a9e200000000000753e400000000000ea80800000000001d509000000000003aa22000000000007546400000000000ea90800000000001d529000000000003aa6200000000000754e400000000000eaa0800000000001d549000000000003aaa2000000000007556400000000000eab0800000000001d569000000000003aae200000000000755e400000000000eac0800000000002d589000000000005ab2200000000000b5664000000000016ad0800000000002d5a9000000000005ab6200000000000b56e4000000000016ae0800000000002d5c9000000000005aba200000000000b5764000000000016af09abd00060008000c357c000c001000186afc001800200030d600003000400061ac100060008000c3584000c001000186b0c001800200030d620003000400061ac500060008000c358c000c001000186b1c001800200030d640003000400061ac900060008000c3594000c001000186b2c001800200030d660003000400061acd00060008000c359c000c001000186b3c001800200030d680003000400061ad100060008000c35a4000c001000186b4c001800200030d6a0003000400061ad500060008000c35ac000c001000186b5c001800200030d6c0003000400061ad900060008000c35b4000c001000186b6c001800200030d6e0003000400061add00060008000c35bc000c001000186b7c001800200030d700003000400061ae100060008000c35c4000c001000186b8c001800200030d720003000400061ae500060008000c35cc000c001000186b9c001800200030d740003000400061ae900060008000c35d4000c001000186bac001800200030d760003000400061aed00060008000c35dc000c001000186bbc001800200030d780003000400061af100060008000c35e4000c001000186bcc001800200030d7a0003000400061af500060008000c35ec000c001000186bdc001800200030d7c0003000400061af900060008000c35f4000c001000186bec001800200030d7e0003000400061afd00060008000c35fc000c001000186bfc001800200030d800003000400061b0100060008000c3604000c001000186c0c001800200030d820003000400061b0500060008000c

def row1 (index : ℕ) : List LedgerRun :=
  if index < 136 then
    let packedCell := Nat.shiftRight row1PackedData (index * 63)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 3), 0⟩) 15 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row2PackedData : ℕ := 0x74fc400000000000e9fc800000000001d401000000000003a812000000000007504400000000000ea0c800000000001d421000000000003a85200000000000750c400000000000ea1c800000000001d441000000000003a892000000000007514400000000000ea2c800000000001d461000000000003a8d200000000000751c400000000000ea3c800000000001d481000000000003a912000000000007524400000000000ea4c800000000001d4a1000000000003a95200000000000752c400000000000ea5c800000000001d4c1000000000003a992000000000007534400000000000ea6c800000000001d4e1000000000003a9d200000000000753c400000000000ea7c800000000001d501000000000003aa12000000000007544400000000000ea8c800000000001d521000000000003aa5200000000000754c400000000000ea9c800000000001d541000000000003aa92000000000007554400000000000eaac800000000001d561000000000003aad200000000000755c400000000000eabc800000000001d581000000000003ab1200000000000b5644000000000016acc800000000002d5a1000000000005ab5200000000000b56c4000000000016adc800000000002d5c1000000000005ab9200000000000b5744000000000016aec800000000002d5e1000000000005abd26af8001800200030d5f8003000400061ac000060008000c3582000c001000186b08001800200030d618003000400061ac400060008000c358a000c001000186b18001800200030d638003000400061ac800060008000c3592000c001000186b28001800200030d658003000400061acc00060008000c359a000c001000186b38001800200030d678003000400061ad000060008000c35a2000c001000186b48001800200030d698003000400061ad400060008000c35aa000c001000186b58001800200030d6b8003000400061ad800060008000c35b2000c001000186b68001800200030d6d8003000400061adc00060008000c35ba000c001000186b78001800200030d6f8003000400061ae000060008000c35c2000c001000186b88001800200030d718003000400061ae400060008000c35ca000c001000186b98001800200030d738003000400061ae800060008000c35d2000c001000186ba8001800200030d758003000400061aec00060008000c35da000c001000186bb8001800200030d778003000400061af000060008000c35e2000c001000186bc8001800200030d798003000400061af400060008000c35ea000c001000186bd8001800200030d7b8003000400061af800060008000c35f2000c001000186be8001800200030d7d8003000400061afc00060008000c35fa000c001000186bf8001800200030d7f8003000400061b0000060008000c3602000c001000186c08001800200030d818003000400061b0400060008000c

def row2 (index : ℕ) : List LedgerRun :=
  if index < 135 then
    let packedCell := Nat.shiftRight row2PackedData (index * 63)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 3), 0⟩) 15 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row3PackedData : ℕ := 0xe9f880000000000000001d3f900000000000000003a8020000000000000000750240000000000000000ea0880000000000000001d41900000000000000003a8420000000000000000750a40000000000000000ea1880000000000000001d43900000000000000003a8820000000000000000751240000000000000000ea2880000000000000001d45900000000000000003a8c20000000000000000751a40000000000000000ea3880000000000000001d47900000000000000003a9020000000000000000752240000000000000000ea4880000000000000001d49900000000000000003a9420000000000000000752a40000000000000000ea5880000000000000001d4b900000000000000003a9820000000000000000753240000000000000000ea6880000000000000001d4d900000000000000003a9c20000000000000000753a40000000000000000ea7880000000000000001d4f900000000000000003aa020000000000000000754240000000000000000ea8880000000000000001d51900000000000000003aa420000000000000000754a40000000000000000ea9880000000000000001d53900000000000000003aa820000000000000000755240000000000000000eaa880000000000000001d55900000000000000003aac20000000000000000755a40000000000000000eab880000000000000001d57900000000000000003ab020000000000000000756240000000000000000eac880000000000000002d59900000000000000005ab420000000000000000b56a400000000000000016ad880000000000000002d5b900000000000000005ab820000000000000000b572400000000000000016ae880000000000000002d5d900000000000000005abc20000000000000000b57a400000000000000016af89d5f8a11800180010000d3ac0146f000300020001a7582297c0006000400034eb08543c000c000800069d618ab1800180010000d3ac415b9000300020001a758a2c240006000400034eb1859b8000c000800069d638b66000180010000d3ac8172e000300020001a75922f280006000400034eb285ff0000c000800069d658c34800180010000d3acc18d9000300020001a759a329c0006000400034eb38671c000c000800069d678d22000180010000d00009ad00003000200018000035a2000600040003000006b48000c0008000600000d69800180010000c00001ad40003000200018000035aa000600040003000006b58000c0008000600000d6b800180010000c00001ad80003000200018000035b2000600040003000006b68000c0008000600000d6d800180010000c00001adc0003000200018000035ba000600040003000006b78000c0008000600000d6f800180010000c00001ae00003000200018000035c2000600040003000006b88000c0008000600000d71800180010000c00001ae40003000200018000035ca000600040003000006b98000c0008000600000d73800180010000c00001ae80003000200018000035d2000600040003000006ba8000c0008000600000d75800180010000c00001aec0003000200018000035da000600040003000006bb8000c0008000600000d77800180010000c00001af00003000200018000035e2000600040003000006bc8000c0008000600000d79800180010000c00001af40003000200018000035ea000600040003000006bd8000c0008000600000d7b800180010000c00001af80003000200018000035f2000600040003000006be8000c0008000600000d7d800180010000c00001afc0003000200018000035fa000600040003000006bf8000c0008000600000d7f800180010000c00001b00000300020001800003602000600040003000006c08000c0008000600000d81800180010000c

def row3 (index : ℕ) : List LedgerRun :=
  if index < 134 then
    let packedCell := Nat.shiftRight row3PackedData (index * 83)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 3), (Nat.land (Nat.shiftRight packedItem0 15) 1)⟩) 16 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row4PackedData : ℕ := 0x1d3f100000000000000074fe4000000000000001d40100000000000000075024000000000000001d41100000000000000075064000000000000001d421000000000000000750a4000000000000001d431000000000000000750e4000000000000001d44100000000000000075124000000000000001d45100000000000000075164000000000000001d461000000000000000751a4000000000000001d471000000000000000751e4000000000000001d48100000000000000075224000000000000001d49100000000000000075264000000000000001d4a1000000000000000752a4000000000000001d4b1000000000000000752e4000000000000001d4c100000000000000075324000000000000001d4d100000000000000075364000000000000001d4e1000000000000000753a4000000000000001d4f1000000000000000753e4000000000000001d50100000000000000075424000000000000001d51100000000000000075464000000000000001d521000000000000000754a4000000000000001d531000000000000000754e4000000000000001d54100000000000000075524000000000000001d55100000000000000075564000000000000001d561000000000000000755a4000000000000001d571000000000000000755e4000000000000001d58100000000000000075624000000000000001d59100000000000000075664000000000000002d5a1000000000000000b56a4000000000000002d5b1000000000000000b56e4000000000000002d5c1000000000000000b5724000000000000002d5d1000000000000000b5764000000000000002d5e1000000000000000b57a4000000000000002d5f1000000000000000b57e5d600e9200060008000d75823b28001800200035d610f0500060008000d75863d04001800200035d620f7f00060008000d758a3efc001800200035d63100100060008000d758e4118001800200035d64108d00060008000d75924358001800200035d65112100060008000d759645c0001800200035d6611c100060008000d759a4854001800200035d67126c00060008000d759e4b1c001800200035d68132500060008000d75a24e18001800200035d6913ec00060008000d75a65158001800200035d6a14c500060008000d75aa54e0001800200035d6b15b000060008000d75ae58b8001800200035d6c16b100060008000d75b25cec001800200035d6d17cb00060008000d75b6618c001800200035d6e190200060008000d75ba66a8001800200035d6f1a5a00060008000d00006b7c0018002000300001ae000060008000c00006b840018002000300001ae200060008000c00006b8c0018002000300001ae400060008000c00006b940018002000300001ae600060008000c00006b9c0018002000300001ae800060008000c00006ba40018002000300001aea00060008000c00006bac0018002000300001aec00060008000c00006bb40018002000300001aee00060008000c00006bbc0018002000300001af000060008000c00006bc40018002000300001af200060008000c00006bcc0018002000300001af400060008000c00006bd40018002000300001af600060008000c00006bdc0018002000300001af800060008000c00006be40018002000300001afa00060008000c00006bec0018002000300001afc00060008000c00006bf40018002000300001afe00060008000c00006bfc0018002000300001b0000060008000c00006c040018002000300001b0200060008000c

def row4 (index : ℕ) : List LedgerRun :=
  if index < 133 then
    let packedCell := Nat.shiftRight row4PackedData (index * 78)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 3), 0⟩) 15 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row5PackedData : ℕ := 0x74fc4000000000000001d3f900000000000000075004000000000000001d40900000000000000075044000000000000001d41900000000000000075084000000000000001d429000000000000000750c4000000000000001d43900000000000000075104000000000000001d44900000000000000075144000000000000001d45900000000000000075184000000000000001d469000000000000000751c4000000000000001d47900000000000000075204000000000000001d48900000000000000075244000000000000001d49900000000000000075284000000000000001d4a9000000000000000752c4000000000000001d4b900000000000000075304000000000000001d4c900000000000000075344000000000000001d4d900000000000000075384000000000000001d4e9000000000000000753c4000000000000001d4f900000000000000075404000000000000001d50900000000000000075444000000000000001d51900000000000000075484000000000000001d529000000000000000754c4000000000000001d53900000000000000075504000000000000001d54900000000000000075544000000000000001d55900000000000000075584000000000000001d569000000000000000755c4000000000000001d57900000000000000075604000000000000001d58900000000000000075644000000000000001d59900000000000000075684000000000000002d5a9000000000000000b56c4000000000000002d5b9000000000000000b5704000000000000002d5c9000000000000000b5744000000000000002d5d9000000000000000b5784000000000000002d5e9000000000000000b57c4000000000000002d5f9000000000000000b5805d608b8600060008000d75842ed0001800200035d618be400060008000d75883054001800200035d628c4800060008000d758c31f0001800200035d638cb200060008000d759033a4001800200035d648d2300060008000d7594357c001800200035d658d9d00060008000d75983774001800200035d668e1f00060008000d759c3990001800200035d678eac00060008000d75a03bd8001800200035d688f4300060008000d75a43e50001800200035d698fe800060008000d75a840fc001800200035d6a909a00060008000d75ac43e8001800200035d6b915d00060008000d75b04714001800200035d6c923200060008000d75b44a94001800200035d6d931d00060008000d75b84e70001800200035d6e942100060008000d75bc52b4001800200035d6f954100060008000d75c05778001800200035d70968300060008000d75c45ccc001800200035d7197ee00060008000d75c862d4001800200035d72998a00060008000d75cc69b40018002000340001ae700060008000c00006ba00018002000300001ae900060008000c00006ba80018002000300001aeb00060008000c00006bb00018002000300001aed00060008000c00006bb80018002000300001aef00060008000c00006bc00018002000300001af100060008000c00006bc80018002000300001af300060008000c00006bd00018002000300001af500060008000c00006bd80018002000300001af700060008000c00006be00018002000300001af900060008000c00006be80018002000300001afb00060008000c00006bf00018002000300001afd00060008000c00006bf80018002000300001aff00060008000c00006c000018002000300001b0100060008000c

def row5 (index : ℕ) : List LedgerRun :=
  if index < 132 then
    let packedCell := Nat.shiftRight row5PackedData (index * 78)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 3), 0⟩) 15 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row6PackedData : ℕ := 0x74fc40000000000000000e9fc80000000000000001d40100000000000000003a8120000000000000000750440000000000000000ea0c80000000000000001d42100000000000000003a8520000000000000000750c40000000000000000ea1c80000000000000001d44100000000000000003a8920000000000000000751440000000000000000ea2c80000000000000001d46100000000000000003a8d20000000000000000751c40000000000000000ea3c80000000000000001d48100000000000000003a9120000000000000000752440000000000000000ea4c80000000000000001d4a100000000000000003a9520000000000000000752c40000000000000000ea5c80000000000000001d4c100000000000000003a9920000000000000000753440000000000000000ea6c80000000000000001d4e100000000000000003a9d20000000000000000753c40000000000000000ea7c80000000000000001d50100000000000000003aa120000000000000000754440000000000000000ea8c80000000000000001d52100000000000000003aa520000000000000000754c40000000000000000ea9c80000000000000001d54100000000000000003aa920000000000000000755440000000000000000eaac80000000000000001d56100000000000000003aad20000000000000000755c40000000000000000eabc80000000000000001d58100000000000000003ab120000000000000000756440000000000000000eacc80000000000000001d5a100000000000000003ab520000000000000000b56c400000000000000016adc80000000000000002d5c100000000000000005ab920000000000000000b574400000000000000016aec80000000000000002d5e100000000000000005abd20000000000000000b57c400000000000000016afc80000000000000002d60100000000000000005ac127584133a0006000400034eb0c2710000c000800069d6204f6800180010000d3ac50a17000300020001a758c14840006000400034eb1c29bc000c000800069d64054f000180010000d3ac90ace000300020001a759415fe0006000400034eb2c2ccc000c000800069d6605b4000180010000d3acd0b9f000300020001a759c17b20006000400034eb3c3054000c000800069d680629800180010000d3ad10c93000300020001a75a419ac0006000400034eb4c3470000c000800069d6a06b2800180010000d3ad50db1000300020001a75ac1c020006000400034eb5c3950000c000800069d6c0755800180010000d3ad90f06000300020001a75b41ecc0006000400034eb6c3f2c000c000800069d6e081a800180010000d3add10a4000300020001a75bc22340006000400034eb7c4658000c000800069d70090c800180010000d3ae112a5000300020001a75c426700006000400034eb8c4f58000c000800069d720a3e800180010000d3ae51530000300020001a75cc2be00006000400034eb9c5af8000c000800069d740bcd800180010000d3ae91889000300020001a75d433180006000400034ebae6ab0000c0008000680000d76000180010000c00001aed0003000200018000035dc000600040003000006bbc000c0008000600000d78000180010000c00001af10003000200018000035e4000600040003000006bcc000c0008000600000d7a000180010000c00001af50003000200018000035ec000600040003000006bdc000c0008000600000d7c000180010000c00001af90003000200018000035f4000600040003000006bec000c0008000600000d7e000180010000c00001afd000300020001835fc001e000600040003400006bfc000c0008000600000d80000180010000c

def row6 (index : ℕ) : List LedgerRun :=
  if index < 131 then
    let packedCell := Nat.shiftRight row6PackedData (index * 83)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 3), (Nat.land (Nat.shiftRight packedItem0 15) 1)⟩) 16 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row7PackedData : ℕ := 0xe9f880000000000000001d3f900000000000000003a8020000000000000000750240000000000000000ea0880000000000000001d41900000000000000003a8420000000000000000750a40000000000000000ea1880000000000000001d43900000000000000003a8820000000000000000751240000000000000000ea2880000000000000001d45900000000000000003a8c20000000000000000751a40000000000000000ea3880000000000000001d47900000000000000003a9020000000000000000752240000000000000000ea4880000000000000001d49900000000000000003a9420000000000000000752a40000000000000000ea5880000000000000001d4b900000000000000003a9820000000000000000753240000000000000000ea6880000000000000001d4d900000000000000003a9c20000000000000000753a40000000000000000ea7880000000000000001d4f900000000000000003aa020000000000000000754240000000000000000ea8880000000000000001d51900000000000000003aa420000000000000000754a40000000000000000ea9880000000000000001d53900000000000000003aa820000000000000000755240000000000000000eaa880000000000000001d55900000000000000003aac20000000000000000755a40000000000000000eab880000000000000001d57900000000000000003ab020000000000000000756240000000000000000eac880000000000000001d59900000000000000003ab420000000000000000756a40000000000000000ead880000000000000002d5b900000000000000005ab820000000000000000b572400000000000000016ae880000000000000002d5d900000000000000005abc20000000000000000b57a400000000000000016af880000000000000002d5f900000000000000005ac020000000000000000b582400000000000000016b0880000000000000002d6193ac40871000300020001a758a112a0006000400034eb1822e8000c000800069d638470800180010000d3ac80909000300020001a759212640006000400034eb282574000c000800069d6584c5000180010000d3acc09b8000300020001a759a13ce0006000400034eb382864000c000800069d678526000180010000d3ad00a82000300020001a75a215720006000400034eb482bcc000c000800069d698598000180010000d3ad40b6f000300020001a75aa17620006000400034eb582fd4000c000800069d6b861e800180010000d3ad80c89000300020001a75b219b00006000400034eb6834ac000c000800069d6d86c1000180010000d3adc0dde000300020001a75ba1c7e0006000400034eb783a94000c000800069d6f8788800180010000d3ae00f83000300020001a75c21ff80006000400034eb8841f4000c000800069d718883000180010000d3ae41199000300020001a75ca246a0006000400034eb984b74000c000800069d7389c8800180010000d3ae81453000300020001a75d22a480006000400034eba8581c000c000800069d758b7f000180010000d3aec180b000300020001a75da32640006000400034ebba69e0000c0008000680000d77800180010000c00001af00003000200018000035e2000600040003000006bc8000c0008000600000d79800180010000c00001af40003000200018000035ea000600040003000006bd8000c0008000600000d7b800180010000c00001af80003000200018000035f2000600040003000006be8000c0008000600000d7d800180010000c00001afc000300020001835fa000a000600040003400006bf8000c0008000600000d7f800180010000c

def row7 (index : ℕ) : List LedgerRun :=
  if index < 130 then
    let packedCell := Nat.shiftRight row7PackedData (index * 83)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 3), (Nat.land (Nat.shiftRight packedItem0 15) 1)⟩) 16 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row8PackedData : ℕ := 0x1d3f10000000000000000000e9fc8000000000000000000750040000000000000000003a8120000000000000000001d4110000000000000000000ea0c8000000000000000000750840000000000000000003a8520000000000000000001d4310000000000000000000ea1c8000000000000000000751040000000000000000003a8920000000000000000001d4510000000000000000000ea2c8000000000000000000751840000000000000000003a8d20000000000000000001d4710000000000000000000ea3c8000000000000000000752040000000000000000003a9120000000000000000001d4910000000000000000000ea4c8000000000000000000752840000000000000000003a9520000000000000000001d4b10000000000000000000ea5c8000000000000000000753040000000000000000003a9920000000000000000001d4d10000000000000000000ea6c8000000000000000000753840000000000000000003a9d20000000000000000001d4f10000000000000000000ea7c8000000000000000000754040000000000000000003aa120000000000000000001d5110000000000000000000ea8c8000000000000000000754840000000000000000003aa520000000000000000001d5310000000000000000000ea9c8000000000000000000755040000000000000000003aa920000000000000000001d5510000000000000000000eaac8000000000000000000755840000000000000000003aad20000000000000000001d5710000000000000000000eabc8000000000000000000756040000000000000000003ab120000000000000000001d5910000000000000000000eacc8000000000000000000756840000000000000000003ab520000000000000000001d5b10000000000000000000eadc8000000000000000000757040000000000000000005ab920000000000000000002d5d100000000000000000016aec8000000000000000000b57840000000000000000005abd20000000000000000002d5f100000000000000000016afc8000000000000000000b58040000000000000000005ac120000000000000000002d61100000000000000000016b0c8000000000000000000b58840003ac50ef6000c0010001a0001d63079c00060008000d0000eb1c3df000300040006800075901f880018002000340003ac9100c000c0010001a0001d65082c00060008000d0000eb2c4200003000400068000759821000018002000340003acd1082000c0010001a0001d67085e00060008000d00016b3c42f0003000400068000b5a021780018002000340005ad11174000c0010001aeb484d588ba00060008000e75a6277445d0003000400073ad4142222e8001800200039d6a8a47120e000c0010001c0001d6b09bd00060008000d0000eb5c54e000300040006800075b02bec0018002000340003ad91682000c0010001a0001d6d0b8b00060008000d0000eb6c5ec000300040006800075b830a80018002000340003add1900000c0010001a0001d6f0cdb00060008000d0000eb7c69d800300040006800075c036840018002000340003ae11c1a000c0010001a0001d710e8100060008000d0000eb8c77d800300040006800075c83df80018002000340003ae52014000c0010001a0001d7310a100060008000d0000eb9c8a1000300040006800075d047c40018002000340003ae9255a000c0010001a0001d75137a00060008000d0000ebaca2c800300040006800075d855340018002000340003aed2cb0000c0010001a0001d77177f00060008000d0000ebbcc63000300040006800075e068cc001800200034000000035e2000c0010001800000001af200060008000c00000000d79800300040006000000006bd0001800200030000000035ea000c0010001800000001af600060008000c00000000d7b800300040006000000006be0001800200030000000035f2000c0010001800000001afa00060008000c00000000d7d800300040006000000006bf0001800200030000000035fa000c0010001800000001afe00060008000c

def row8 (index : ℕ) : List LedgerRun :=
  if index < 129 then
    let packedCell := Nat.shiftRight row8PackedData (index * 93)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 3), 0⟩) 15 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row9PackedData : ℕ := 0x5a7e1000000000000000000000000005a7f1000000000000000000000000005a801000000000000000000000000005a811000000000000000000000000005a821000000000000000000000000005a831000000000000000000000000005a841000000000000000000000000005a851000000000000000000000000005a861000000000000000000000000005a871000000000000000000000000005a881000000000000000000000000005a891000000000000000000000000005a8a1000000000000000000000000005a8b1000000000000000000000000005a8c1000000000000000000000000005a8d1000000000000000000000000005a8e1000000000000000000000000005a8f1000000000000000000000000005a901000000000000000000000000005a911000000000000000000000000005a921000000000000000000000000005a931000000000000000000000000005a941000000000000000000000000005a951000000000000000000000000005a961000000000000000000000000005a971000000000000000000000000005a981000000000000000000000000005a991000000000000000000000000005a9a1000000000000000000000000005a9b1000000000000000000000000005a9c1000000000000000000000000005a9d1000000000000000000000000005a9e1000000000000000000000000005a9f1000000000000000000000000005aa01000000000000000000000000005aa11000000000000000000000000005aa21000000000000000000000000005aa31000000000000000000000000005aa41000000000000000000000000005aa51000000000000000000000000005aa61000000000000000000000000005aa71000000000000000000000000005aa81000000000000000000000000005aa91000000000000000000000000005aaa1000000000000000000000000005aab1000000000000000000000000005aac1000000000000000000000000005aad1000000000000000000000000005aae1000000000000000000000000005aaf1000000000000000000000000005ab01000000000000000000000000005ab11000000000000000000000000005ab21000000000000000000000000005ab31000000000000000000000000005ab41000000000000000000000000005ab51000000000000000000000000005ab61000000000000000000000000005ab71000000000000000000000000005ab81000000000000000000000000005ab91000000000000000000000000005aba1000000000000000000000000005abb1000000000000000000000000005abc1000000000000000000000000005abd1000000000000000000000000005abe1000000000000000000000000005abf1000000000000000000000000005ac01000000000000000000000000005ac11000000000000000000000000005ac21000000000000000000000000005ac31000000000000000000000000005ac41000000000000000000000000005ac51000000000000000000000000005ac61000000000005ac70dc2000c00100015000000000005ac80e02000c00100015000000000005ac90e42000c00100015000000000005aca0e86000c00100015000000000005acb0ece000c00100015000000000003acc0f16000c00100015000000000003acd0f62000c00100015000000000003ace0fb2000c00100015000000000003acf1004000c00100015000000000003ad01058000c00100015000000000005ad11080000c00100015000000000005ad21080000c001000150000eb4c45d085e1080000c0010001775a8248845d085e1080000c0010001875aa255045d085e1080000c001000180000eb584c388ba10bc000c001000170000eb5c4de88ba10bc000c001000170000eb604fa08ba10bc000c001000170000eb6451788ba1168000c0010001700000001d6d0a6b1174000c0010001600000001d6d8aab1174000c0010001600000001d6e0aed1292000c00100016000000000003add14d0000c00100015000000000003ade16fe000c00100015000000000003adf17ac000c00100015000000000003ae01866000c00100015000000000003ae1192c000c00100015000000000003ae219fc000c00100015000000000003ae31adc000c00100015000000000003ae41bcc000c00100015000000000003ae51ccc000c00100015000000000003ae61dde000c00100015000000000003ae71f06000c00100015000000000003ae82046000c00100015000000000003ae921a0000c00100015000000000003aea2318000c00100015000000000003aeb24b4000c00100015000000000003aec2676000c00100015000000000003aed2864000c00100015000000000003aee2a88000c00100015000000000003aef2ce8000c00100015000000000003af02f90000c00100015000000000003af1328e000c0010001500000000000000035e4000c0010001400000000000000035e6000c0010001400000000000000035e8000c0010001400000000000000035ea000c0010001400000000000000035ec000c0010001400000000000000035ee000c0010001400000000000000035f0000c0010001400000000000000035f2000c0010001400000000000000035f4000c0010001400000000000000035f6000c0010001400000000000000035f8000c0010001400000000000000035fa000c00100014

def row9 (index : ℕ) : List LedgerRun :=
  if index < 128 then
    let packedCell := Nat.shiftRight row9PackedData (index * 124)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 3), 0⟩) 15 (Nat.land packedCell 15) (Nat.shiftRight packedCell 4))
  else []

private def row10PackedData : ℕ := 0x9a7e1000000000000000000000000000000000000269fc40000000000000000000000000000000000009a80100000000000000000000000000000000000026a0440000000000000000000000000000000000009a82100000000000000000000000000000000000026a0c40000000000000000000000000000000000009a84100000000000000000000000000000000000026a1440000000000000000000000000000000000009a86100000000000000000000000000000000000026a1c40000000000000000000000000000000000009a88100000000000000000000000000000000000026a2440000000000000000000000000000000000009a8a100000000000000000000000000000000000026a2c40000000000000000000000000000000000009a8c100000000000000000000000000000000000026a3440000000000000000000000000000000000009a8e100000000000000000000000000000000000026a3c40000000000000000000000000000000000009a90100000000000000000000000000000000000026a4440000000000000000000000000000000000009a92100000000000000000000000000000000000026a4c40000000000000000000000000000000000009a94100000000000000000000000000000000000026a5440000000000000000000000000000000000009a96100000000000000000000000000000000000026a5c40000000000000000000000000000000000009a98100000000000000000000000000000000000026a6440000000000000000000000000000000000009a9a100000000000000000000000000000000000026a6c40000000000000000000000000000000000009a9c100000000000000000000000000000000000026a7440000000000000000000000000000000000009a9e100000000000000000000000000000000000026a7c40000000000000000000000000000000000009aa0100000000000000000000000000000000000026a8440000000000000000000000000000000000009aa2100000000000000000000000000000000000026a8c40000000000000000000000000000000000009aa4100000000000000000000000000000000000026a9440000000000000000000000000000000000009aa6100000000000000000000000000000000000026a9c40000000000000000000000000000000000009aa8100000000000000000000000000000000000026aa440000000000000000000000000000000000009aaa100000000000000000000000000000000000026aac40000000000000000000000000000000000009aac100000000000000000000000000000000000026ab440000000000000000000000000000000000009aae100000000000000000000000000000000000026abc40000000000000000000000000000000000009ab0100000000000000000000000000000000000026ac440000000000000000000000000000000000009ab2100000000000000000000000000000000000026acc40000000000000000000000000000000000009ab4100000000000000000000000000000000000026ad440000000000000000000000000000000000009ab6100000000000000000000000000000000000026adc40000000000000000000000000000000000009ab8100000000000000000000000000000000000026ae440000000000000000000000000000000000009aba100000000000000000000000000000000000026aec40000000000000000000000000000000000009abc100000000000000000000000000000000000026af440000000000000000000000000000000000009abe100000000000000000000000000000000000036afc4000000000000000000000000000000000000dac01000000000000000000000000000000009ac11d4cc8000000000000000000000000000000026b0875662000000000000000000000000000000009ac31d6648000000000000000000000000000000026b1075cc2000000000000000000000000000000009ac51d7fc8000000000000000000000000000000026b1876322000000000000000000000000000000009ac7158788000000000000000000000000000000026b205655200000000000000000026b24066d0000c00020000540000000000000000009aca01a300003000080001500000000000000000026b2c06ad0000c00020000540000000000000000009acc01b380003000080001500000000000000000026b3406f10000c00020000540000000000000000009ace01c540003000080001500000000000000000026b3c073a0000c00020000540000000000000000009ad001d8400030000800015000000000000009ad11e1a4078a0000c0002000058000000000000026b48789d01ed000030000800016000000000000009ad31e34407e00000c0002000058000000000000026b5079060203c0003000080001600000000000000000016b54083f0000c00020000540000000005ad6022a8085e021000003000080001716b5c349f023b808ba0217808400000c00020000645ad80db180922022e8085e021000003000080001916b6439530256008ba0217808400000c00020000640000000003ada0264408ba02178000300008000170000000000eb6c09cc022e8085e0000c000200005c0000000003adc0282808ba02178000300008000170000000000eb740a4a022e8085e0000c000200005c00000000000000eb780a8e022e800030000800016000000000000003adf02b5808ba0000c000200005800000000000000eb800b21026b0000300008000160000000000000000000eb840b500000c00020000540000000000000000003ae202f40000300008000150000000000000000000eb8c0c370000c00020000540000000000000000003ae403298000300008000150000000000000000000eb940d1c0000c00020000540000000000000000003ae603670000300008000150000000000000000000eb9c0e260000c00020000540000000000000000003ae803ae8000300008000150000000000000000000eba40f5c0000c00020000540000000000000000003aea04030000300008000150000000000000000000ebac10cc0000c00020000540000000000000000003aec0467c000300008000150000000000000000000ebb412870000c00020000540000000000000000003aee04e24000300008000150000000000000000000ebbc14a90000c00020000540000000000000000003af0057ac000300008000150000000000000000000ebc417570000c00020000540000000000000000003af2063d4000300008000150000000000000000000ebce1ae70000c0002000054000000000000000000000006bd000030000800014000000000000000000000001af50000c0002000050000000000000000000000006bd800030000800014000000000000000000000001af70000c0002000050000000000000000000000006be000030000800014000000000000000000000001af90000c0002000050000000000000000000000006be800030000800014000000000000000000000001afb0000c0002000050000000000000000000000006bf000030000800014

def row10 (index : ℕ) : List LedgerRun :=
  if index < 127 then
    let packedCell := Nat.shiftRight row10PackedData (index * 166)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), (Nat.land (Nat.shiftRight packedItem0 16) 3)⟩) 18 (Nat.land packedCell 15) (Nat.shiftRight packedCell 4))
  else []

private def row11PackedData : ℕ := 0xda7e10000000000000000000000000000da7f10000000000000000000000000000da8010000000000000000000000000000da8110000000000000000000000000000da8210000000000000000000000000000da8310000000000000000000000000000da8410000000000000000000000000000da8510000000000000000000000000000da8610000000000000000000000000000da8710000000000000000000000000000da8810000000000000000000000000000da8910000000000000000000000000000da8a10000000000000000000000000000da8b10000000000000000000000000000da8c10000000000000000000000000000da8d10000000000000000000000000000da8e10000000000000000000000000000da8f10000000000000000000000000000da9010000000000000000000000000000da9110000000000000000000000000000da9210000000000000000000000000000da9310000000000000000000000000000da9410000000000000000000000000000da9510000000000000000000000000000da9610000000000000000000000000000da9710000000000000000000000000000da9810000000000000000000000000000da9910000000000000000000000000000da9a10000000000000000000000000000da9b10000000000000000000000000000da9c10000000000000000000000000000da9d10000000000000000000000000000da9e10000000000000000000000000000da9f10000000000000000000000000000daa010000000000000000000000000000daa110000000000000000000000000000daa210000000000000000000000000000daa310000000000000000000000000000daa410000000000000000000000000000daa510000000000000000000000000000daa610000000000000000000000000000daa710000000000000000000000000000daa810000000000000000000000000000daa910000000000000000000000000000daaa10000000000000000000000000000daab10000000000000000000000000000daac10000000000000000000000000000daad10000000000000000000000000000daae10000000000000000000000000000daaf10000000000000000000000000000dab010000000000000000000000000000dab110000000000000000000000000000dab210000000000000000000000000000dab310000000000000000000000000000dab410000000000000000000000000000dab510000000000000000000000000000dab610000000000000000000000000000dab710000000000000000000000000000dab810000000000000000000000000000dab910000000000000000000000000000daba10000000000000000000000000000dabb10000000000000000000000000000dabc10000000000000000000000000000dabd10000000000000000000000000000dabe10000000000000000000000000000dabf10000000000000000000000000000dac010000000000000000000000000000dac110000000000000000000000000000dac21000000000000000000000000dac366ff2000000000000000000000000dac4672f2000000000000000000000000dac567602000000000000000000000000dac667902000000000000000000000000dac767c12000000000000000000000000dac867f12000000000000000000000000dac947db2000000000000000000000000daca480f2000000000000dacb06170003000200015000000000000dacc06350003000200015000000000000dacd0656000300020001500000000daceb6fe0677000300020001600000000dacfb70d0699000300020001600000000dad0b71c06be000300020001600000000dad18dc906e3000300020001600000000dad28de7070a000300020001600000000dad36a0c0733000300020001600000000dad46a3d075e000300020001600000000dad56a6f078b000300020001600000000dad66aa007ba000300020001600000000bad76d4907eb0003000200016000000009ad870e9081e000300020001600009ad9551b085e084000030002000179ada5a4908ba085e084000030002000189adb091208ba085e084000030002000189adc094c08ba085e0840000300020001800009add098908ba085e000300020001700003ade09c908ba085e000300020001700003adf0a0c08ba085e000300020001700003ae00a5308ba08950003000200017000000003ae10a9d08ba0003000200016000000003ae20aeb095300030002000160000000000003ae30b2800030002000150000000000003ae40ba500030002000150000000000003ae50c1500030002000150000000000003ae60c8c00030002000150000000000003ae70d0e00030002000150000000000003ae80d9a00030002000150000000000003ae90e3200030002000150000000000003aea0ed900030002000150000000000003aeb0f8f00030002000150000000000003aec105700030002000150000000000003aed113400030002000150000000000003aee122a00030002000150000000000003aef133d00030002000150000000000003af0147300030002000150000000000003af115d100030002000150000000000003af2176200030002000150000000000003af31931000300020001500000000000000001af4000300020001400000000000000001af5000300020001400000000000000001af6000300020001400000000000000001af7000300020001400000000000000001af8000300020001400000000000000001af9000300020001400000000000000001afa000300020001400000000000000001afb0003000200014

def row11 (index : ℕ) : List LedgerRun :=
  if index < 126 then
    let packedCell := Nat.shiftRight row11PackedData (index * 132)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 15) (Nat.shiftRight packedCell 4))
  else []

private def row12PackedData : ℕ := 0x6d3f1000000000000000000000000da7f2000000000000000000000001b50040000000000000000000000036a048000000000000000000000006d411000000000000000000000000da832000000000000000000000001b50840000000000000000000000036a148000000000000000000000006d431000000000000000000000000da872000000000000000000000001b51040000000000000000000000036a248000000000000000000000006d451000000000000000000000000da8b2000000000000000000000001b51840000000000000000000000036a348000000000000000000000006d471000000000000000000000000da8f2000000000000000000000001b52040000000000000000000000036a448000000000000000000000006d491000000000000000000000000da932000000000000000000000001b52840000000000000000000000036a548000000000000000000000006d4b1000000000000000000000000da972000000000000000000000001b53040000000000000000000000036a648000000000000000000000006d4d1000000000000000000000000da9b2000000000000000000000001b53840000000000000000000000036a748000000000000000000000006d4f1000000000000000000000000da9f2000000000000000000000001b54040000000000000000000000036a848000000000000000000000006d511000000000000000000000000daa32000000000000000000000001b54840000000000000000000000036a948000000000000000000000006d531000000000000000000000000daa72000000000000000000000001b55040000000000000000000000036aa48000000000000000000000006d551000000000000000000000000daab2000000000000000000000001b55840000000000000000000000036ab48000000000000000000000006d571000000000000000000000000daaf2000000000000000000000001b56040000000000000000000000036ac48000000000000000000000006d591000000000000000000000000dab32000000000000000000000001b56840000000000000000000000036ad48000000000000000000000006d5b1000000000000000000000000dab72000000000000000000000001b57040000000000000000000000036ae48000000000000000000000006d5d1000000000000000000000000dabb2000000000000000000000001b57840000000000000000000000036af48000000000000000000000006d5f1000000000000000000000000dabf2000000000000000000000001b58040000000000000000000000036b048000000000000000000000006d611000000000000000000000000dac32000000000000000000000001b5884000000000000000000036b159ab9000000000000000000006d63336fa00000000000000000000dac76710400000000000000000001b590ce848000000000000000000036b259dcd000000000000000000006d6533d2200000000000000000000dacb4785400000000000000000001b5988f748000000036b341758000c00080006800000006d6702fa800180010000d00000000dacf0615000300020001a0001b5a16b5e0c6e000600040003800036b46d7041968000c0008000700006d695ae9033f800180010000e0000dad3b5e406a5000300020001c0001b5a96bec0d9a000600040003800036b5635e41bdc000c0008000700005d6b35a00391000180010000e0000bad76b720750000300020001c000175b0d7480f0200060004000380002eb65af5c1ecc000c0008000700005d6d375e03f4800180010000e00009adb73c90821000300020001c000135b8f29010800006000400038000000016b742100000c00080006ad6f045d042f0420000180010000f3adf096208ba085e000300020001e75c01348117410bc000600040003ceb8427ac22e82178000c0008000780001d71051a845d000180010000e00003ae30a8408ba000300020001c0000000075c814b6000600040003400000000eb942cf4000c00080006800000001d7305d7800180010000d000000003ae70c2a000300020001a0000000075d0195e000600040003400000000eba43500000c00080006800000001d7506ef800180010000d000000003aeb0e8d000300020001a0000000075d81e9c000600040003400000000ebb44088000c00080006800000001d770888000180010000d000000003aef121a000300020001a0000000075e0268c000600040003400000000ebc45270000c00080006800000001d790b12000180010000d000000003af317ec000300020001a0000000075e8340600060004000340000000000006bd4000c000800060000000000000d7b000180010000c000000001af7002e000300020001a00000000000035f000060004000300000000000006be4000c000800060000000000000d7d000180010000c

def row12 (index : ℕ) : List LedgerRun :=
  if index < 125 then
    let packedCell := Nat.shiftRight row12PackedData (index * 115)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row13PackedData : ℕ := 0xda7e20000000000000001b4fe400000000000000036a0080000000000000006d4090000000000000000da8220000000000000001b506400000000000000036a1080000000000000006d4290000000000000000da8620000000000000001b50e400000000000000036a2080000000000000006d4490000000000000000da8a20000000000000001b516400000000000000036a3080000000000000006d4690000000000000000da8e20000000000000001b51e400000000000000036a4080000000000000006d4890000000000000000da9220000000000000001b526400000000000000036a5080000000000000006d4a90000000000000000da9620000000000000001b52e400000000000000036a6080000000000000006d4c90000000000000000da9a20000000000000001b536400000000000000036a7080000000000000006d4e90000000000000000da9e20000000000000001b53e400000000000000036a8080000000000000006d5090000000000000000daa220000000000000001b546400000000000000036a9080000000000000006d5290000000000000000daa620000000000000001b54e400000000000000036aa080000000000000006d5490000000000000000daaa20000000000000001b556400000000000000036ab080000000000000006d5690000000000000000daae20000000000000001b55e400000000000000036ac080000000000000006d5890000000000000000dab220000000000000001b566400000000000000036ad080000000000000006d5a90000000000000000dab620000000000000001b56e400000000000000036ae080000000000000006d5c90000000000000000daba20000000000000001b576400000000000000036af080000000000000006d5e90000000000000000dabe20000000000000001b57e400000000000000036b0080000000000000006d6090000000000000000dac220000000000000001b586400000000000000036b1080000000000000006d6290000000000000000dac620000000000000001b58e40000000000036b219a3d0000000000006d64b360a000000000000daca66f34000000000001b596ce4a80000000000036b319d5d0000000000006d66b3c4a000000000000dace47654000000000001b59e8f3680000000000036b411f456d6882f3800180010000ddad2060a000300020001bb5a60c5c00060004000376b50194c000c00080006dd6a833d800180010000dbad606a4000300020001b75ae0d9e0006000400036eb601bf4000c00080006dd6c8396800180010000d9ada0760000300020001b35b60f2a00060004000356b701f34000c00080006ad6e8404800180010000d5ade0840000300020001ab5be10800006000400034eb802178000c00080006ad70842f000180010000d5ae2085e000300020001ab5c6115a00060004000356b9022e8000c000800069d728545000180010000d3ae60af7000300020001a75ce16da0006000400034eba02fb4000c000800069d74863c000180010000d3aea0d11000300020001a75d61b740006000400034ebb039d0000c000800069d7687a1000180010000d3aee1029000300020001a75de225a0006000400034ebc0494c000c000800069d7889d2000180010000d3af21528000300020001a75e62ddc0006000400034ebd06414000c0008000680000d7a800180010000c1af60012000300020001a35ee0076000600040003400006be0000c0008000600000d7c800180010000c

def row13 (index : ℕ) : List LedgerRun :=
  if index < 124 then
    let packedCell := Nat.shiftRight row13PackedData (index * 83)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row14PackedData : ℕ := 0x1b4fc40000000000000000000000369fc800000000000000000000006d40100000000000000000000000da81200000000000000000000001b5044000000000000000000000036a0c800000000000000000000006d42100000000000000000000000da85200000000000000000000001b50c4000000000000000000000036a1c800000000000000000000006d44100000000000000000000000da89200000000000000000000001b5144000000000000000000000036a2c800000000000000000000006d46100000000000000000000000da8d200000000000000000000001b51c4000000000000000000000036a3c800000000000000000000006d48100000000000000000000000da91200000000000000000000001b5244000000000000000000000036a4c800000000000000000000006d4a100000000000000000000000da95200000000000000000000001b52c4000000000000000000000036a5c800000000000000000000006d4c100000000000000000000000da99200000000000000000000001b5344000000000000000000000036a6c800000000000000000000006d4e100000000000000000000000da9d200000000000000000000001b53c4000000000000000000000036a7c800000000000000000000006d50100000000000000000000000daa1200000000000000000000001b5444000000000000000000000036a8c800000000000000000000006d52100000000000000000000000daa5200000000000000000000001b54c4000000000000000000000036a9c800000000000000000000006d54100000000000000000000000daa9200000000000000000000001b5544000000000000000000000036aac800000000000000000000006d56100000000000000000000000daad200000000000000000000001b55c4000000000000000000000036abc800000000000000000000006d58100000000000000000000000dab1200000000000000000000001b5644000000000000000000000036acc800000000000000000000006d5a100000000000000000000000dab5200000000000000000000001b56c4000000000000000000000036adc800000000000000000000006d5c100000000000000000000000dab9200000000000000000000001b5744000000000000000000000036aec800000000000000000000006d5e100000000000000000000000dabd200000000000000000000001b57c4000000000000000000000036afc800000000000000000000006d60100000000000000000000000dac1200000000000000000000001b5844000000000000000000000036b0c800000000000000000000006d62100000000000000000000000dac5200000000000000000000001b58c4000000000000000000000036b1c800000000000000000000006d64100000000000000000000000dac9200000000000000000000001b5944000000000000000000dacb199c90000000000000000001b5983352a00000000000000000036b3466d840000000000000000006d670ce148000000000000000000dacf19cf50000000000000000001b5a033b8200000000000000000036b4467a340000000000000000006d690cfac8000000000000000000dad311ed1000000000000000000175a82499a0000000000000000002eb54496a40000175ac031c80006000100003400002eb5c06620000c000200006800005d6c00d1c0001800040000d000009ad901aec0003000080001a0000135b40375800060001000034000016b6c071e0000c000200006800002d6e00ea80001800040000d000005add01e340003000080001a00000b5bc03e4800060001000034000016b7c08090000c000200006800001d70010800001800040000d000003ae1021780003000080001a0000075c4042f00006000100003400000eb8c085e0000c000200006800001d72011740001800040000d000003ae5024cc0003000080001a0000075cc052e00006000100003400000eb9c0ace0000c000200006800001d74016940001800040000d000003ae902f440003000080001a0000075d4063300006000100003400000ebac0d0a0000c000200006800001d7601b7e0001800040000d000003aed03a240003000080001a0000075dc07b600006000100003400000ebbc106c0000c000200006800001d780231e0001800040000d000003af104b740003000080001a0000075e40a3080006000100003400000ebcc16280000c000200006800001d7a0308e0001800040000d0ebd61af20002c0003000080001c0000035ec000900006000100003400000ebdc192c0000c000200006800001d7c034960001800040000d

def row14 (index : ℕ) : List LedgerRun :=
  if index < 123 then
    let packedCell := Nat.shiftRight row14PackedData (index * 111)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), (Nat.land (Nat.shiftRight packedItem0 16) 3)⟩) 18 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row15PackedData : ℕ := 0x369f8800000000000000000006d3f900000000000000000000da80200000000000000000001b5024000000000000000000036a08800000000000000000006d41900000000000000000000da84200000000000000000001b50a4000000000000000000036a18800000000000000000006d43900000000000000000000da88200000000000000000001b5124000000000000000000036a28800000000000000000006d45900000000000000000000da8c200000000000000000001b51a4000000000000000000036a38800000000000000000006d47900000000000000000000da90200000000000000000001b5224000000000000000000036a48800000000000000000006d49900000000000000000000da94200000000000000000001b52a4000000000000000000036a58800000000000000000006d4b900000000000000000000da98200000000000000000001b5324000000000000000000036a68800000000000000000006d4d900000000000000000000da9c200000000000000000001b53a4000000000000000000036a78800000000000000000006d4f900000000000000000000daa0200000000000000000001b5424000000000000000000036a88800000000000000000006d51900000000000000000000daa4200000000000000000001b54a4000000000000000000036a98800000000000000000006d53900000000000000000000daa8200000000000000000001b5524000000000000000000036aa8800000000000000000006d55900000000000000000000daac200000000000000000001b55a4000000000000000000036ab8800000000000000000006d57900000000000000000000dab0200000000000000000001b5624000000000000000000036ac8800000000000000000006d59900000000000000000000dab4200000000000000000001b56a4000000000000000000036ad8800000000000000000006d5b900000000000000000000dab8200000000000000000001b5724000000000000000000036ae8800000000000000000006d5d900000000000000000000dabc200000000000000000001b57a4000000000000000000036af8800000000000000000006d5f900000000000000000000dac0200000000000000000001b5824000000000000000000036b08800000000000000000006d61900000000000000000000dac4200000000000000000001b58a4000000000000000000036b18800000000000000000006d63900000000000000000000dac8200000000000000000001b5924000000000000000000036b28800000000000000000006d65900000000000000000000dacc200000000000000000001b59a4000000000000000000036b3880000000000000006d67b344a0000000000000000dad066bd40000000000000001b5a2cde0800000000000000036b499c9100000000000000005d69b44ba0000000000000000bad468cb4000000000000000175aad1fc80000000000000002eb59a4c900000000000000005d6bb605200000000000000009ad850a04000000000000000135b2abf68000000000000000000016b688000000000002d6d80010000b00005adc06ec000300020001a0000b5ba0e46000600040003400016b781d74000c0008000680001d6f83cd000180010000d00003ae007dc000300020001a000075c2104600060004000340000eb882178000c0008000680001d71842f000180010000d00003ae4085e000300020001a000075ca117400060004000340000eb982764000c0008000680001d738524000180010000d00003ae80ac1000300020001a000075d2168a00060004000340000eba82f58000c0008000680001d75863b000180010000d00003aec0d28000300020001a000075da1be000060004000340000ebb83b40000c0008000680001d7787e6800180010000d00003af010f0000300020001a000075e2247c00060004000340000ebc84f14000c0008000680001d798ac9800180010000d3af417bd0007000300020001c75ea3260001400060004000380000ebd857f0000c0008000680001d7b8b73800180010000d

def row15 (index : ℕ) : List LedgerRun :=
  if index < 122 then
    let packedCell := Nat.shiftRight row15PackedData (index * 99)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row16PackedData : ℕ := 0x6d3f100000000000000000000da7f200000000000000000001b5004000000000000000000036a04800000000000000000006d41100000000000000000000da83200000000000000000001b5084000000000000000000036a14800000000000000000006d43100000000000000000000da87200000000000000000001b5104000000000000000000036a24800000000000000000006d45100000000000000000000da8b200000000000000000001b5184000000000000000000036a34800000000000000000006d47100000000000000000000da8f200000000000000000001b5204000000000000000000036a44800000000000000000006d49100000000000000000000da93200000000000000000001b5284000000000000000000036a54800000000000000000006d4b100000000000000000000da97200000000000000000001b5304000000000000000000036a64800000000000000000006d4d100000000000000000000da9b200000000000000000001b5384000000000000000000036a74800000000000000000006d4f100000000000000000000da9f200000000000000000001b5404000000000000000000036a84800000000000000000006d51100000000000000000000daa3200000000000000000001b5484000000000000000000036a94800000000000000000006d53100000000000000000000daa7200000000000000000001b5504000000000000000000036aa4800000000000000000006d55100000000000000000000daab200000000000000000001b5584000000000000000000036ab4800000000000000000006d57100000000000000000000daaf200000000000000000001b5604000000000000000000036ac4800000000000000000006d59100000000000000000000dab3200000000000000000001b5684000000000000000000036ad4800000000000000000006d5b100000000000000000000dab7200000000000000000001b5704000000000000000000036ae4800000000000000000006d5d100000000000000000000dabb200000000000000000001b5784000000000000000000036af4800000000000000000006d5f100000000000000000000dabf200000000000000000001b5804000000000000000000036b04800000000000000000006d61100000000000000000000dac3200000000000000000001b5884000000000000000000036b14800000000000000000006d63100000000000000000000dac7200000000000000000001b5904000000000000000000036b24800000000000000000006d65100000000000000000000dacb200000000000000000001b5984000000000000000000036b34800000000000000000006d67100000000000000000000dacf200000000000000000001b5a04000000000000000000036b44800000000000000000006d69100000000000000000000dad3200000000000000000001b5a840000000000000002eb55a12500000000000000005d6b358ea00000000000000009ad76ffc4000000000000000135b0ea968000000000000000000016b64800000000000000000002d6d1000000000000000000005adb200000000000000000000b5b84000000000000000000016b74800000000000000000002d6f1000000000000000000005adf200000000000000000000b5c04000000000000000000016b84800000000000000000002d71100003ae30856000300020001a000075c810bc00060004000340000eb9422e8000c0008000680001d7304b5000180010000d00003ae709d6000300020001a000075d0149800060004000340000eba42b34000c0008000680001d7505ae000180010000d00003aeb0bfa000300020001a000075d8195400060004000340000ebb435c0000c0008000680001d770727800180010000d00003aef0f4c000300020001a000075e020e000060004000340000ebc44704000c0008000680001d7909a7000180010000d3af315260005000300020001c75e82c00000c00060004000380000ebd44d78000c0008000680001d7b0a10800180010000d

def row16 (index : ℕ) : List LedgerRun :=
  if index < 121 then
    let packedCell := Nat.shiftRight row16PackedData (index * 99)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row17PackedData : ℕ := 0xda7e200000000000000000001b4fe4000000000000000000036a00800000000000000000006d40900000000000000000000da82200000000000000000001b5064000000000000000000036a10800000000000000000006d42900000000000000000000da86200000000000000000001b50e4000000000000000000036a20800000000000000000006d44900000000000000000000da8a200000000000000000001b5164000000000000000000036a30800000000000000000006d46900000000000000000000da8e200000000000000000001b51e4000000000000000000036a40800000000000000000006d48900000000000000000000da92200000000000000000001b5264000000000000000000036a50800000000000000000006d4a900000000000000000000da96200000000000000000001b52e4000000000000000000036a60800000000000000000006d4c900000000000000000000da9a200000000000000000001b5364000000000000000000036a70800000000000000000006d4e900000000000000000000da9e200000000000000000001b53e4000000000000000000036a80800000000000000000006d50900000000000000000000daa2200000000000000000001b5464000000000000000000036a90800000000000000000006d52900000000000000000000daa6200000000000000000001b54e4000000000000000000036aa0800000000000000000006d54900000000000000000000daaa200000000000000000001b5564000000000000000000036ab0800000000000000000006d56900000000000000000000daae200000000000000000001b55e4000000000000000000036ac0800000000000000000006d58900000000000000000000dab2200000000000000000001b5664000000000000000000036ad0800000000000000000006d5a900000000000000000000dab6200000000000000000001b56e4000000000000000000036ae0800000000000000000006d5c900000000000000000000daba200000000000000000001b5764000000000000000000036af0800000000000000000006d5e900000000000000000000dabe200000000000000000001b57e4000000000000000000036b00800000000000000000006d60900000000000000000000dac2200000000000000000001b5864000000000000000000036b10800000000000000000006d62900000000000000000000dac6200000000000000000001b58e4000000000000000000036b20800000000000000000006d64900000000000000000000daca200000000000000000001b5964000000000000000000036b30800000000000000000006d66900000000000000000000dace200000000000000000001b59e4000000000000000000036b40800000000000000000005d68900000000000000000000bad220000000000000000000175a6400000000000000000002eb50800000000000000000005d6a9000000000000000000009ad620000000000000000000135ae4000000000000000000036b60800000000000000000002d6c9000000000000000000005ada200000000000000000000b5b64000000000000000000016b70800000000000000000002d6e9000000000000000000005ade200000000000000000000b5be4000000000000000000016b80800000000000000000002d709000000000000000000005ae2200000000000000000000b5c64000000000000000000016b90800000000000000000002d729000000000000000000005ae6200000000000000000000b5ce4000000000000000000016ba0800000000000000000002d749000000000000000000005aea2000075d6172200060004000340000ebb03100000c0008000680001d768682800180010000d00003aee0de5000300020001a000075de1dc800060004000340000ebc04028000c0008000680001d7888b0800180010000d00003af212f7000300020001a75e626c4000800060004000380000ebd044c8000c0008000680001d7a88ea800180010000d

def row17 (index : ℕ) : List LedgerRun :=
  if index < 120 then
    let packedCell := Nat.shiftRight row17PackedData (index * 99)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 7) (Nat.shiftRight packedCell 3))
  else []

private def row18PackedData : ℕ := 0x6d3f769ffb501da81ed4176a0fb509da85ed4376a1fb511da89ed4576a2fb519da8ded4776a3fb521da91ed4976a4fb529da95ed4b76a5fb531da99ed4d76a6fb539da9ded4f76a7fb541daa1ed5176a8fb549daa5ed5376a9fb551daa9ed5576aafb559daaded5776abfb561dab1ed5976acfb569dab5ed5b76adfb571dab9ed5d76aefb579dabded5f76affb581dac1ed6176b0fb589dac5ed6376b1fb591dac9ed6576b2fb599dacded6776b3fb5a1dad1dd696eb4f75a99ad5cd6b66b5eb5b15ad9ad6d56b6eb5b95addad6f56b7eb5c15ae1ad7156b8eb5c95ae5ad7356b9eb5d15ae9ad7556baeb5d95aedad7756bbeb5e15af1ad7956bceb5e9

def row18 (index : ℕ) : List LedgerRun :=
  if index < 119 then
    let packedCell := Nat.shiftRight row18PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row19PackedData : ℕ := 0x369fbb4ffda80ed40f6a0bb507da84ed42f6a1bb50fda88ed44f6a2bb517da8ced46f6a3bb51fda90ed48f6a4bb527da94ed4af6a5bb52fda98ed4cf6a6bb537da9ced4ef6a7bb53fdaa0ed50f6a8bb547daa4ed52f6a9bb54fdaa8ed54f6aabb557daaced56f6abbb55fdab0ed58f6acbb567dab4ed5af6adbb56fdab8ed5cf6aebb577dabced5ef6afbb57fdac0ed60f6b0bb587dac4ed62f6b1bb58fdac8ed64f6b2bb597dacced66f6b3bb59fdad0ed68f6b4b75a79ad4cd6ae6b5ab5af5ad8ad6cd6b6ab5b73adc9d6eceb7a75bf5ae0ad70d6b8ab5c75ae4ad72d6b9ab5cf5ae8ad74d6baab5d75aecad76d6bbab5df5af0ad78d6bcab5e7

def row19 (index : ℕ) : List LedgerRun :=
  if index < 118 then
    let packedCell := Nat.shiftRight row19PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row20PackedData : ℕ := 0x1b4fdda7fed4076a07b505da83ed4276a17b50dda87ed4476a27b515da8bed4676a37b51dda8fed4876a47b525da93ed4a76a57b52dda97ed4c76a67b535da9bed4e76a77b53dda9fed5076a87b545daa3ed5276a97b54ddaa7ed5476aa7b555daabed5676ab7b55ddaafed5876ac7b565dab3ed5a76ad7b56ddab7ed5c76ae7b575dabbed5e76af7b57ddabfed6076b07b585dac3ed6276b17b58ddac7ed6476b27b595dacbed6676b37b59ddacfed6876b4775a59ad3cd6a66b56b5ad5ad7ad6c56b66b5b53adb9d6e4eb7675bd3adf9d704eb8675c53ae39d724eb9675cd3ae79d7456ba6b5d55aebad7656bb6b5dd5aefad7856bc6b5e5

def row20 (index : ℕ) : List LedgerRun :=
  if index < 117 then
    let packedCell := Nat.shiftRight row20PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row21PackedData : ℕ := 0xda7eed3ff6a03b503da82ed41f6a13b50bda86ed43f6a23b513da8aed45f6a33b51bda8eed47f6a43b523da92ed49f6a53b52bda96ed4bf6a63b533da9aed4df6a73b53bda9eed4ff6a83b543daa2ed51f6a93b54bdaa6ed53f6aa3b553daaaed55f6ab3b55bdaaeed57f6ac3b563dab2ed59f6ad3b56bdab6ed5bf6ae3b573dabaed5df6af3b57bdabeed5ff6b03b583dac2ed61f6b13b58bdac6ed63f6b23b593dacaed65f6b33b59bdaceed67f6b4375a3bad2cd69e6b52b5ab5ad6ad6bd6b62b5b33ada9d6dceb7275bb3ade9d6fceb8275c33ae29d71ceb9275cb3ae69d73ceba275d33aea9d75cebb275db3aee9d77cebc275e3

def row21 (index : ℕ) : List LedgerRun :=
  if index < 116 then
    let packedCell := Nat.shiftRight row21PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row22PackedData : ℕ := 0x6d3f769ffb501da81ed4176a0fb509da85ed4376a1fb511da89ed4576a2fb519da8ded4776a3fb521da91ed4976a4fb529da95ed4b76a5fb531da99ed4d76a6fb539da9ded4f76a7fb541daa1ed5176a8fb549daa5ed5376a9fb551daa9ed5576aafb559daaded5776abfb561dab1ed5976acfb569dab5ed5b76adfb571dab9ed5d76aefb579dabded5f76affb581dac1ed6176b0fb589dac5ed6376b1fb591dac9ed6576b2fb599dacded6776b3f75a1bad1cd6966b4ef5a95ad5ad6b56b5eb5b15ad99d6d4eb6e75b93add9d6f4eb7e75c13ae19d714eb8e75c93ae59d734eb9e75d13ae99d754ebae75d93aed9d774ebbe75e1

def row22 (index : ℕ) : List LedgerRun :=
  if index < 115 then
    let packedCell := Nat.shiftRight row22PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row23PackedData : ℕ := 0x369fbb4ffda80ed40f6a0bb507da84ed42f6a1bb50fda88ed44f6a2bb517da8ced46f6a3bb51fda90ed48f6a4bb527da94ed4af6a5bb52fda98ed4cf6a6bb537da9ced4ef6a7bb53fdaa0ed50f6a8bb547daa4ed52f6a9bb54fdaa8ed54f6aabb557daaced56f6abbb55fdab0ed58f6acbb567dab4ed5af6adbb56fdab8ed5cf6aebb577dabced5ef6afbb57fdac0ed60f6b0bb587dac4ed62f6b1bb58fdac8ed64f6b2bb597dacced66f6b3b759fbad0cd68e6b4b35a75ad4ad6ad6b5ab5af5ad89d6cceb6a75b73adc9d6eceb7a75bf3ae09d70ceb8a75c73ae49d72ceb9a75cf3ae89d74cebaa75d73aec9d76cebba75df

def row23 (index : ℕ) : List LedgerRun :=
  if index < 114 then
    let packedCell := Nat.shiftRight row23PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row24PackedData : ℕ := 0x1b4fdda7fed4076a07b505da83ed4276a17b50dda87ed4476a27b515da8bed4676a37b51dda8fed4876a47b525da93ed4a76a57b52dda97ed4c76a67b535da9bed4e76a77b53dda9fed5076a87b545daa3ed5276a97b54ddaa7ed5476aa7b555daabed5676ab7b55ddaafed5876ac7b565dab3ed5a76ad7b56ddab7ed5c76ae7b575dabbed5e76af7b57ddabfed6076b07b585dac3ed6276b17b58ddac7ed6476b27b595dacbed6676b37759dbacfcd6866b4735a55ad3ad6a56b56b5ad5ad79d6c4eb6675b53adb9d6e4eb7675bd3adf9d704eb8675c53ae39d724eb9675cd3ae79d744eba675d53aeb9d764ebb675dd

def row24 (index : ℕ) : List LedgerRun :=
  if index < 113 then
    let packedCell := Nat.shiftRight row24PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row25PackedData : ℕ := 0xda7eed3ff6a03b503da82ed41f6a13b50bda86ed43f6a23b513da8aed45f6a33b51bda8eed47f6a43b523da92ed49f6a53b52bda96ed4bf6a63b533da9aed4df6a73b53bda9eed4ff6a83b543daa2ed51f6a93b54bdaa6ed53f6aa3b553daaaed55f6ab3b55bdaaeed57f6ac3b563dab2ed59f6ad3b56bdab6ed5bf6ae3b573dabaed5df6af3b57bdabeed5ff6b03b583dac2ed61f6b13b58bdac6ed63f6b23b593dacaed65f6b33759bbacecd67e6b4335a35ad2ad69d6b52b5ab5ad69d6bceb6275b33ada9d6dceb7275bb3ade9d6fceb8275c33ae29d71ceb9275cb3ae69d73ceba275d33aea9d75cebb275db

def row25 (index : ℕ) : List LedgerRun :=
  if index < 112 then
    let packedCell := Nat.shiftRight row25PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row26PackedData : ℕ := 0x6d3f769ffb501da81ed4176a0fb509da85ed4376a1fb511da89ed4576a2fb519da8ded4776a3fb521da91ed4976a4fb529da95ed4b76a5fb531da99ed4d76a6fb539da9ded4f76a7fb541daa1ed5176a8fb549daa5ed5376a9fb551daa9ed5576aafb559daaded5776abfb561dab1ed5976acfb569dab5ed5b76adfb571dab9ed5d76aefb579dabded5f76affb581dac1ed6176b0fb589dac5ed6376b1fb591dac9ed6576b2f7599bacdcd6766b3f35a17ad1bd6956b4eb5a95ad59d6b4eb5e75b13ad99d6d4eb6e75b93add9d6f4eb7e75c13ae19d714eb8e75c93ae59d734eb9e75d13ae99d754ebae75d9

def row26 (index : ℕ) : List LedgerRun :=
  if index < 111 then
    let packedCell := Nat.shiftRight row26PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row27PackedData : ℕ := 0x369fbb4ffda80ed40f6a0bb507da84ed42f6a1bb50fda88ed44f6a2bb517da8ced46f6a3bb51fda90ed48f6a4bb527da94ed4af6a5bb52fda98ed4cf6a6bb537da9ced4ef6a7bb53fdaa0ed50f6a8bb547daa4ed52f6a9bb54fdaa8ed54f6aabb557daaced56f6abbb55fdab0ed58f6acbb567dab4ed5af6adbb56fdab8ed5cf6aebb577dabced5ef6afbb57fdac0ed60f6b0bb587dac4ed62f6b1bb58fdac8ed64f6b2b7597bacccd66e6b3b359f9ad0cd68d6b4ab5a75ad49d6aceb5a75af3ad89d6cceb6a75b73adc9d6eceb7a75bf3ae09d70ceb8a75c73ae49d72ceb9a75cf3ae89d74cebaa75d7

def row27 (index : ℕ) : List LedgerRun :=
  if index < 110 then
    let packedCell := Nat.shiftRight row27PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row28PackedData : ℕ := 0x1b4fdda7fed4076a07b505da83ed4276a17b50dda87ed4476a27b515da8bed4676a37b51dda8fed4876a47b525da93ed4a76a57b52dda97ed4c76a67b535da9bed4e76a77b53dda9fed5076a87b545daa3ed5276a97b54ddaa7ed5476aa7b555daabed5676ab7b55ddaafed5876ac7b565dab3ed5a76ad7b56ddab7ed5c76ae7b575dabbed5e76af7b57ddabfed6076b07b585dac3ed6276b17b58ddac7ed6476b277595bacbcd6666b37359d9acfcd6856b46b5a55ad3ad6a4eb5675ad3ad79d6c4eb6675b53adb9d6e4eb7675bd3adf9d704eb8675c53ae39d724eb9675cd3ae79d744eba675d5

def row28 (index : ℕ) : List LedgerRun :=
  if index < 109 then
    let packedCell := Nat.shiftRight row28PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row29PackedData : ℕ := 0xda7eed3ff6a03b503da82ed41f6a13b50bda86ed43f6a23b513da8aed45f6a33b51bda8eed47f6a43b523da92ed49f6a53b52bda96ed4bf6a63b533da9aed4df6a73b53bda9eed4ff6a83b543daa2ed51f6a93b54bdaa6ed53f6aa3b553daaaed55f6ab3b55bdaaeed57f6ac3b563dab2ed59f6ad3b56bdab6ed5bf6ae3b573dabaed5df6af3b57bdabeed5ff6b03b583dac2ed61f6b13b58bdac6ed63f6b237593bacacd65e6b33359b9acecd67d6b42b5a35ad2ad69ceb5275ab3ad69d6bceb6275b33ada9d6dceb7275bb3ade9d6fceb8275c33ae29d71ceb9275cb3ae69d73ceba275d3

def row29 (index : ℕ) : List LedgerRun :=
  if index < 108 then
    let packedCell := Nat.shiftRight row29PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

private def row30PackedData : ℕ := 0x6d3f769ffb501da81ed4176a0fb509da85ed4376a1fb511da89ed4576a2fb519da8ded4776a3fb521da91ed4976a4fb529da95ed4b76a5fb531da99ed4d76a6fb539da9ded4f76a7fb541daa1ed5176a8fb549daa5ed5376a9fb551daa9ed5576aafb559daaded5776abfb561dab1ed5976acfb569dab5ed5b76adfb571dab9ed5d76aefb579dabded5f76affb581dac1ed6176b0fb589dac5ed6376b1fb591bac9cd6566b2f35999acdcd6756b3eb5a15ad1ad694eb4e75a93ad59d6b4eb5e75b13ad99d6d4eb6e75b93add9d6f4eb7e75c13ae19d714eb8e75c93ae59d734eb9e75d1

def row30 (index : ℕ) : List LedgerRun :=
  if index < 107 then
    let packedCell := Nat.shiftRight row30PackedData (index * 17)
    (ProximityPrize.SubmissionLower.BitPackedData80791.decodeList (fun packedItem0 => ⟨(Nat.land packedItem0 8191), (Nat.land (Nat.shiftRight packedItem0 13) 7), 0⟩) 16 (Nat.land packedCell 1) (Nat.shiftRight packedCell 1))
  else []

def lookup : ℕ → ℕ → List LedgerRun
  | 1, v => row1 v
  | 2, v => row2 v
  | 3, v => row3 v
  | 4, v => row4 v
  | 5, v => row5 v
  | 6, v => row6 v
  | 7, v => row7 v
  | 8, v => row8 v
  | 9, v => row9 v
  | 10, v => row10 v
  | 11, v => row11 v
  | 12, v => row12 v
  | 13, v => row13 v
  | 14, v => row14 v
  | 15, v => row15 v
  | 16, v => row16 v
  | 17, v => row17 v
  | 18, v => row18 v
  | 19, v => row19 v
  | 20, v => row20 v
  | 21, v => row21 v
  | 22, v => row22 v
  | 23, v => row23 v
  | 24, v => row24 v
  | 25, v => row25 v
  | 26, v => row26 v
  | 27, v => row27 v
  | 28, v => row28 v
  | 29, v => row29 v
  | 30, v => row30 v
  | _, _ => []

end ProximityPrize.SubmissionLower.Lower80791.LedgerData

end Compact_LedgerData80791

section Compact_LedgerChecked80791
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.LedgerChecked
open Lower80791.LedgerData Lower80791.LedgerAudit Lower80791.PhaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem r1part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (0+k)) 0 (lookup 1 (0+k)) := by decide +kernel
theorem r1part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (8+k)) 0 (lookup 1 (8+k)) := by decide +kernel
theorem r1part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (16+k)) 0 (lookup 1 (16+k)) := by decide +kernel
theorem r1part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (24+k)) 0 (lookup 1 (24+k)) := by decide +kernel
theorem r1part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (32+k)) 0 (lookup 1 (32+k)) := by decide +kernel
theorem r1part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (40+k)) 0 (lookup 1 (40+k)) := by decide +kernel
theorem r1part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (48+k)) 0 (lookup 1 (48+k)) := by decide +kernel
theorem r1part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (56+k)) 0 (lookup 1 (56+k)) := by decide +kernel
theorem r1part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (64+k)) 0 (lookup 1 (64+k)) := by decide +kernel
theorem r1part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (72+k)) 0 (lookup 1 (72+k)) := by decide +kernel
theorem r1part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (80+k)) 0 (lookup 1 (80+k)) := by decide +kernel
theorem r1part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (88+k)) 0 (lookup 1 (88+k)) := by decide +kernel
theorem r1part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (96+k)) 0 (lookup 1 (96+k)) := by decide +kernel
theorem r1part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (104+k)) 0 (lookup 1 (104+k)) := by decide +kernel
theorem r1part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (112+k)) 0 (lookup 1 (112+k)) := by decide +kernel
theorem r1part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (120+k)) 0 (lookup 1 (120+k)) := by decide +kernel
theorem r1part128 : ∀ k ∈ List.range 8, RunsValid (rowContext 1 (128+k)) 0 (lookup 1 (128+k)) := by decide +kernel

theorem checkedR1 (V : ℕ) (hV : V ∈ List.range 136) : RunsValid (rowContext 1 V) 0 (lookup 1 V) := by
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r1part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r1part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r1part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r1part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r1part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r1part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r1part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r1part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r1part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r1part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r1part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r1part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r1part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r1part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r1part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r1part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r1part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
theorem r2part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (0+k)) 0 (lookup 2 (0+k)) := by decide +kernel
theorem r2part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (8+k)) 0 (lookup 2 (8+k)) := by decide +kernel
theorem r2part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (16+k)) 0 (lookup 2 (16+k)) := by decide +kernel
theorem r2part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (24+k)) 0 (lookup 2 (24+k)) := by decide +kernel
theorem r2part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (32+k)) 0 (lookup 2 (32+k)) := by decide +kernel
theorem r2part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (40+k)) 0 (lookup 2 (40+k)) := by decide +kernel
theorem r2part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (48+k)) 0 (lookup 2 (48+k)) := by decide +kernel
theorem r2part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (56+k)) 0 (lookup 2 (56+k)) := by decide +kernel
theorem r2part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (64+k)) 0 (lookup 2 (64+k)) := by decide +kernel
theorem r2part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (72+k)) 0 (lookup 2 (72+k)) := by decide +kernel
theorem r2part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (80+k)) 0 (lookup 2 (80+k)) := by decide +kernel
theorem r2part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (88+k)) 0 (lookup 2 (88+k)) := by decide +kernel
theorem r2part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (96+k)) 0 (lookup 2 (96+k)) := by decide +kernel
theorem r2part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (104+k)) 0 (lookup 2 (104+k)) := by decide +kernel
theorem r2part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (112+k)) 0 (lookup 2 (112+k)) := by decide +kernel
theorem r2part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 2 (120+k)) 0 (lookup 2 (120+k)) := by decide +kernel
theorem r2part128 : ∀ k ∈ List.range 7, RunsValid (rowContext 2 (128+k)) 0 (lookup 2 (128+k)) := by decide +kernel

theorem checkedR2 (V : ℕ) (hV : V ∈ List.range 135) : RunsValid (rowContext 2 V) 0 (lookup 2 V) := by
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r2part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r2part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r2part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r2part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r2part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r2part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r2part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r2part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r2part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r2part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r2part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r2part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r2part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r2part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r2part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r2part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r2part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
theorem r3part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (0+k)) 0 (lookup 3 (0+k)) := by decide +kernel
theorem r3part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (8+k)) 0 (lookup 3 (8+k)) := by decide +kernel
theorem r3part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (16+k)) 0 (lookup 3 (16+k)) := by decide +kernel
theorem r3part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (24+k)) 0 (lookup 3 (24+k)) := by decide +kernel
theorem r3part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (32+k)) 0 (lookup 3 (32+k)) := by decide +kernel
theorem r3part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (40+k)) 0 (lookup 3 (40+k)) := by decide +kernel
theorem r3part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (48+k)) 0 (lookup 3 (48+k)) := by decide +kernel
theorem r3part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (56+k)) 0 (lookup 3 (56+k)) := by decide +kernel
theorem r3part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (64+k)) 0 (lookup 3 (64+k)) := by decide +kernel
theorem r3part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (72+k)) 0 (lookup 3 (72+k)) := by decide +kernel
theorem r3part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (80+k)) 0 (lookup 3 (80+k)) := by decide +kernel
theorem r3part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (88+k)) 0 (lookup 3 (88+k)) := by decide +kernel
theorem r3part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (96+k)) 0 (lookup 3 (96+k)) := by decide +kernel
theorem r3part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (104+k)) 0 (lookup 3 (104+k)) := by decide +kernel
theorem r3part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (112+k)) 0 (lookup 3 (112+k)) := by decide +kernel
theorem r3part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 3 (120+k)) 0 (lookup 3 (120+k)) := by decide +kernel
theorem r3part128 : ∀ k ∈ List.range 6, RunsValid (rowContext 3 (128+k)) 0 (lookup 3 (128+k)) := by decide +kernel

theorem checkedR3 (V : ℕ) (hV : V ∈ List.range 134) : RunsValid (rowContext 3 V) 0 (lookup 3 V) := by
  have hv : V < 134 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r3part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r3part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r3part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r3part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r3part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r3part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r3part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r3part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r3part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r3part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r3part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r3part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r3part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r3part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r3part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r3part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r3part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
theorem r4part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (0+k)) 0 (lookup 4 (0+k)) := by decide +kernel
theorem r4part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (8+k)) 0 (lookup 4 (8+k)) := by decide +kernel
theorem r4part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (16+k)) 0 (lookup 4 (16+k)) := by decide +kernel
theorem r4part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (24+k)) 0 (lookup 4 (24+k)) := by decide +kernel
theorem r4part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (32+k)) 0 (lookup 4 (32+k)) := by decide +kernel
theorem r4part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (40+k)) 0 (lookup 4 (40+k)) := by decide +kernel
theorem r4part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (48+k)) 0 (lookup 4 (48+k)) := by decide +kernel
theorem r4part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (56+k)) 0 (lookup 4 (56+k)) := by decide +kernel
theorem r4part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (64+k)) 0 (lookup 4 (64+k)) := by decide +kernel
theorem r4part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (72+k)) 0 (lookup 4 (72+k)) := by decide +kernel
theorem r4part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (80+k)) 0 (lookup 4 (80+k)) := by decide +kernel
theorem r4part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (88+k)) 0 (lookup 4 (88+k)) := by decide +kernel
theorem r4part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (96+k)) 0 (lookup 4 (96+k)) := by decide +kernel
theorem r4part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (104+k)) 0 (lookup 4 (104+k)) := by decide +kernel
theorem r4part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (112+k)) 0 (lookup 4 (112+k)) := by decide +kernel
theorem r4part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 4 (120+k)) 0 (lookup 4 (120+k)) := by decide +kernel
theorem r4part128 : ∀ k ∈ List.range 5, RunsValid (rowContext 4 (128+k)) 0 (lookup 4 (128+k)) := by decide +kernel

theorem checkedR4 (V : ℕ) (hV : V ∈ List.range 133) : RunsValid (rowContext 4 V) 0 (lookup 4 V) := by
  have hv : V < 133 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r4part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r4part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r4part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r4part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r4part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r4part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r4part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r4part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r4part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r4part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r4part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r4part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r4part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r4part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r4part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r4part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r4part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
theorem r5part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (0+k)) 0 (lookup 5 (0+k)) := by decide +kernel
theorem r5part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (8+k)) 0 (lookup 5 (8+k)) := by decide +kernel
theorem r5part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (16+k)) 0 (lookup 5 (16+k)) := by decide +kernel
theorem r5part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (24+k)) 0 (lookup 5 (24+k)) := by decide +kernel
theorem r5part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (32+k)) 0 (lookup 5 (32+k)) := by decide +kernel
theorem r5part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (40+k)) 0 (lookup 5 (40+k)) := by decide +kernel
theorem r5part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (48+k)) 0 (lookup 5 (48+k)) := by decide +kernel
theorem r5part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (56+k)) 0 (lookup 5 (56+k)) := by decide +kernel
theorem r5part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (64+k)) 0 (lookup 5 (64+k)) := by decide +kernel
theorem r5part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (72+k)) 0 (lookup 5 (72+k)) := by decide +kernel
theorem r5part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (80+k)) 0 (lookup 5 (80+k)) := by decide +kernel
theorem r5part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (88+k)) 0 (lookup 5 (88+k)) := by decide +kernel
theorem r5part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (96+k)) 0 (lookup 5 (96+k)) := by decide +kernel
theorem r5part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (104+k)) 0 (lookup 5 (104+k)) := by decide +kernel
theorem r5part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (112+k)) 0 (lookup 5 (112+k)) := by decide +kernel
theorem r5part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 5 (120+k)) 0 (lookup 5 (120+k)) := by decide +kernel
theorem r5part128 : ∀ k ∈ List.range 4, RunsValid (rowContext 5 (128+k)) 0 (lookup 5 (128+k)) := by decide +kernel

theorem checkedR5 (V : ℕ) (hV : V ∈ List.range 132) : RunsValid (rowContext 5 V) 0 (lookup 5 V) := by
  have hv : V < 132 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r5part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r5part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r5part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r5part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r5part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r5part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r5part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r5part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r5part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r5part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r5part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r5part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r5part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r5part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r5part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r5part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r5part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
theorem r6part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (0+k)) 0 (lookup 6 (0+k)) := by decide +kernel
theorem r6part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (8+k)) 0 (lookup 6 (8+k)) := by decide +kernel
theorem r6part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (16+k)) 0 (lookup 6 (16+k)) := by decide +kernel
theorem r6part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (24+k)) 0 (lookup 6 (24+k)) := by decide +kernel
theorem r6part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (32+k)) 0 (lookup 6 (32+k)) := by decide +kernel
theorem r6part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (40+k)) 0 (lookup 6 (40+k)) := by decide +kernel
theorem r6part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (48+k)) 0 (lookup 6 (48+k)) := by decide +kernel
theorem r6part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (56+k)) 0 (lookup 6 (56+k)) := by decide +kernel
theorem r6part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (64+k)) 0 (lookup 6 (64+k)) := by decide +kernel
theorem r6part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (72+k)) 0 (lookup 6 (72+k)) := by decide +kernel
theorem r6part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (80+k)) 0 (lookup 6 (80+k)) := by decide +kernel
theorem r6part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (88+k)) 0 (lookup 6 (88+k)) := by decide +kernel
theorem r6part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (96+k)) 0 (lookup 6 (96+k)) := by decide +kernel
theorem r6part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (104+k)) 0 (lookup 6 (104+k)) := by decide +kernel
theorem r6part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (112+k)) 0 (lookup 6 (112+k)) := by decide +kernel
theorem r6part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 6 (120+k)) 0 (lookup 6 (120+k)) := by decide +kernel
theorem r6part128 : ∀ k ∈ List.range 3, RunsValid (rowContext 6 (128+k)) 0 (lookup 6 (128+k)) := by decide +kernel

theorem checkedR6 (V : ℕ) (hV : V ∈ List.range 131) : RunsValid (rowContext 6 V) 0 (lookup 6 V) := by
  have hv : V < 131 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r6part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r6part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r6part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r6part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r6part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r6part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r6part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r6part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r6part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r6part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r6part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r6part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r6part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r6part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r6part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r6part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r6part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
theorem r7part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (0+k)) 0 (lookup 7 (0+k)) := by decide +kernel
theorem r7part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (8+k)) 0 (lookup 7 (8+k)) := by decide +kernel
theorem r7part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (16+k)) 0 (lookup 7 (16+k)) := by decide +kernel
theorem r7part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (24+k)) 0 (lookup 7 (24+k)) := by decide +kernel
theorem r7part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (32+k)) 0 (lookup 7 (32+k)) := by decide +kernel
theorem r7part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (40+k)) 0 (lookup 7 (40+k)) := by decide +kernel
theorem r7part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (48+k)) 0 (lookup 7 (48+k)) := by decide +kernel
theorem r7part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (56+k)) 0 (lookup 7 (56+k)) := by decide +kernel
theorem r7part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (64+k)) 0 (lookup 7 (64+k)) := by decide +kernel
theorem r7part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (72+k)) 0 (lookup 7 (72+k)) := by decide +kernel
theorem r7part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (80+k)) 0 (lookup 7 (80+k)) := by decide +kernel
theorem r7part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (88+k)) 0 (lookup 7 (88+k)) := by decide +kernel
theorem r7part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (96+k)) 0 (lookup 7 (96+k)) := by decide +kernel
theorem r7part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (104+k)) 0 (lookup 7 (104+k)) := by decide +kernel
theorem r7part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (112+k)) 0 (lookup 7 (112+k)) := by decide +kernel
theorem r7part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 7 (120+k)) 0 (lookup 7 (120+k)) := by decide +kernel
theorem r7part128 : ∀ k ∈ List.range 2, RunsValid (rowContext 7 (128+k)) 0 (lookup 7 (128+k)) := by decide +kernel

theorem checkedR7 (V : ℕ) (hV : V ∈ List.range 130) : RunsValid (rowContext 7 V) 0 (lookup 7 V) := by
  have hv : V < 130 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r7part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r7part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r7part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r7part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r7part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r7part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r7part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r7part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r7part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r7part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r7part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r7part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r7part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r7part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r7part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r7part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r7part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
theorem r8part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (0+k)) 0 (lookup 8 (0+k)) := by decide +kernel
theorem r8part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (8+k)) 0 (lookup 8 (8+k)) := by decide +kernel
theorem r8part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (16+k)) 0 (lookup 8 (16+k)) := by decide +kernel
theorem r8part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (24+k)) 0 (lookup 8 (24+k)) := by decide +kernel
theorem r8part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (32+k)) 0 (lookup 8 (32+k)) := by decide +kernel
theorem r8part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (40+k)) 0 (lookup 8 (40+k)) := by decide +kernel
theorem r8part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (48+k)) 0 (lookup 8 (48+k)) := by decide +kernel
theorem r8part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (56+k)) 0 (lookup 8 (56+k)) := by decide +kernel
theorem r8part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (64+k)) 0 (lookup 8 (64+k)) := by decide +kernel
theorem r8part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (72+k)) 0 (lookup 8 (72+k)) := by decide +kernel
theorem r8part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (80+k)) 0 (lookup 8 (80+k)) := by decide +kernel
theorem r8part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (88+k)) 0 (lookup 8 (88+k)) := by decide +kernel
theorem r8part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (96+k)) 0 (lookup 8 (96+k)) := by decide +kernel
theorem r8part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (104+k)) 0 (lookup 8 (104+k)) := by decide +kernel
theorem r8part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (112+k)) 0 (lookup 8 (112+k)) := by decide +kernel
theorem r8part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 8 (120+k)) 0 (lookup 8 (120+k)) := by decide +kernel
theorem r8part128 : ∀ k ∈ List.range 1, RunsValid (rowContext 8 (128+k)) 0 (lookup 8 (128+k)) := by decide +kernel

theorem checkedR8 (V : ℕ) (hV : V ∈ List.range 129) : RunsValid (rowContext 8 V) 0 (lookup 8 V) := by
  have hv : V < 129 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r8part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r8part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r8part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r8part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r8part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r8part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r8part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r8part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r8part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r8part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r8part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r8part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r8part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r8part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r8part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  by_cases h120 : V < 128
  · have hp := r8part120 (V-120) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
  have hp := r8part128 (V-128) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using hp
theorem r9part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (0+k)) 0 (lookup 9 (0+k)) := by decide +kernel
theorem r9part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (8+k)) 0 (lookup 9 (8+k)) := by decide +kernel
theorem r9part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (16+k)) 0 (lookup 9 (16+k)) := by decide +kernel
theorem r9part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (24+k)) 0 (lookup 9 (24+k)) := by decide +kernel
theorem r9part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (32+k)) 0 (lookup 9 (32+k)) := by decide +kernel
theorem r9part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (40+k)) 0 (lookup 9 (40+k)) := by decide +kernel
theorem r9part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (48+k)) 0 (lookup 9 (48+k)) := by decide +kernel
theorem r9part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (56+k)) 0 (lookup 9 (56+k)) := by decide +kernel
theorem r9part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (64+k)) 0 (lookup 9 (64+k)) := by decide +kernel
theorem r9part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (72+k)) 0 (lookup 9 (72+k)) := by decide +kernel
theorem r9part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (80+k)) 0 (lookup 9 (80+k)) := by decide +kernel
theorem r9part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (88+k)) 0 (lookup 9 (88+k)) := by decide +kernel
theorem r9part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (96+k)) 0 (lookup 9 (96+k)) := by decide +kernel
theorem r9part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (104+k)) 0 (lookup 9 (104+k)) := by decide +kernel
theorem r9part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (112+k)) 0 (lookup 9 (112+k)) := by decide +kernel
theorem r9part120 : ∀ k ∈ List.range 8, RunsValid (rowContext 9 (120+k)) 0 (lookup 9 (120+k)) := by decide +kernel

theorem checkedR9 (V : ℕ) (hV : V ∈ List.range 128) : RunsValid (rowContext 9 V) 0 (lookup 9 V) := by
  have hv : V < 128 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r9part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r9part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r9part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r9part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r9part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r9part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r9part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r9part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r9part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r9part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r9part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r9part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r9part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r9part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r9part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r9part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
theorem r10part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (0+k)) 0 (lookup 10 (0+k)) := by decide +kernel
theorem r10part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (8+k)) 0 (lookup 10 (8+k)) := by decide +kernel
theorem r10part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (16+k)) 0 (lookup 10 (16+k)) := by decide +kernel
theorem r10part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (24+k)) 0 (lookup 10 (24+k)) := by decide +kernel
theorem r10part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (32+k)) 0 (lookup 10 (32+k)) := by decide +kernel
theorem r10part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (40+k)) 0 (lookup 10 (40+k)) := by decide +kernel
theorem r10part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (48+k)) 0 (lookup 10 (48+k)) := by decide +kernel
theorem r10part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (56+k)) 0 (lookup 10 (56+k)) := by decide +kernel
theorem r10part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (64+k)) 0 (lookup 10 (64+k)) := by decide +kernel
theorem r10part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (72+k)) 0 (lookup 10 (72+k)) := by decide +kernel
theorem r10part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (80+k)) 0 (lookup 10 (80+k)) := by decide +kernel
theorem r10part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (88+k)) 0 (lookup 10 (88+k)) := by decide +kernel
theorem r10part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (96+k)) 0 (lookup 10 (96+k)) := by decide +kernel
theorem r10part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (104+k)) 0 (lookup 10 (104+k)) := by decide +kernel
theorem r10part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 10 (112+k)) 0 (lookup 10 (112+k)) := by decide +kernel
theorem r10part120 : ∀ k ∈ List.range 7, RunsValid (rowContext 10 (120+k)) 0 (lookup 10 (120+k)) := by decide +kernel

theorem checkedR10 (V : ℕ) (hV : V ∈ List.range 127) : RunsValid (rowContext 10 V) 0 (lookup 10 V) := by
  have hv : V < 127 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r10part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r10part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r10part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r10part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r10part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r10part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r10part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r10part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r10part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r10part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r10part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r10part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r10part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r10part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r10part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r10part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
theorem r11part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (0+k)) 0 (lookup 11 (0+k)) := by decide +kernel
theorem r11part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (8+k)) 0 (lookup 11 (8+k)) := by decide +kernel
theorem r11part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (16+k)) 0 (lookup 11 (16+k)) := by decide +kernel
theorem r11part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (24+k)) 0 (lookup 11 (24+k)) := by decide +kernel
theorem r11part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (32+k)) 0 (lookup 11 (32+k)) := by decide +kernel
theorem r11part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (40+k)) 0 (lookup 11 (40+k)) := by decide +kernel
theorem r11part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (48+k)) 0 (lookup 11 (48+k)) := by decide +kernel
theorem r11part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (56+k)) 0 (lookup 11 (56+k)) := by decide +kernel
theorem r11part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (64+k)) 0 (lookup 11 (64+k)) := by decide +kernel
theorem r11part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (72+k)) 0 (lookup 11 (72+k)) := by decide +kernel
theorem r11part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (80+k)) 0 (lookup 11 (80+k)) := by decide +kernel
theorem r11part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (88+k)) 0 (lookup 11 (88+k)) := by decide +kernel
theorem r11part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (96+k)) 0 (lookup 11 (96+k)) := by decide +kernel
theorem r11part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (104+k)) 0 (lookup 11 (104+k)) := by decide +kernel
theorem r11part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 11 (112+k)) 0 (lookup 11 (112+k)) := by decide +kernel
theorem r11part120 : ∀ k ∈ List.range 6, RunsValid (rowContext 11 (120+k)) 0 (lookup 11 (120+k)) := by decide +kernel

theorem checkedR11 (V : ℕ) (hV : V ∈ List.range 126) : RunsValid (rowContext 11 V) 0 (lookup 11 V) := by
  have hv : V < 126 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r11part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r11part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r11part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r11part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r11part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r11part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r11part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r11part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r11part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r11part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r11part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r11part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r11part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r11part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r11part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r11part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
theorem r12part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (0+k)) 0 (lookup 12 (0+k)) := by decide +kernel
theorem r12part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (8+k)) 0 (lookup 12 (8+k)) := by decide +kernel
theorem r12part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (16+k)) 0 (lookup 12 (16+k)) := by decide +kernel
theorem r12part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (24+k)) 0 (lookup 12 (24+k)) := by decide +kernel
theorem r12part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (32+k)) 0 (lookup 12 (32+k)) := by decide +kernel
theorem r12part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (40+k)) 0 (lookup 12 (40+k)) := by decide +kernel
theorem r12part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (48+k)) 0 (lookup 12 (48+k)) := by decide +kernel
theorem r12part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (56+k)) 0 (lookup 12 (56+k)) := by decide +kernel
theorem r12part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (64+k)) 0 (lookup 12 (64+k)) := by decide +kernel
theorem r12part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (72+k)) 0 (lookup 12 (72+k)) := by decide +kernel
theorem r12part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (80+k)) 0 (lookup 12 (80+k)) := by decide +kernel
theorem r12part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (88+k)) 0 (lookup 12 (88+k)) := by decide +kernel
theorem r12part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (96+k)) 0 (lookup 12 (96+k)) := by decide +kernel
theorem r12part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (104+k)) 0 (lookup 12 (104+k)) := by decide +kernel
theorem r12part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 12 (112+k)) 0 (lookup 12 (112+k)) := by decide +kernel
theorem r12part120 : ∀ k ∈ List.range 5, RunsValid (rowContext 12 (120+k)) 0 (lookup 12 (120+k)) := by decide +kernel

theorem checkedR12 (V : ℕ) (hV : V ∈ List.range 125) : RunsValid (rowContext 12 V) 0 (lookup 12 V) := by
  have hv : V < 125 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r12part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r12part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r12part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r12part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r12part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r12part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r12part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r12part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r12part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r12part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r12part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r12part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r12part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r12part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r12part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r12part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
theorem r13part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (0+k)) 0 (lookup 13 (0+k)) := by decide +kernel
theorem r13part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (8+k)) 0 (lookup 13 (8+k)) := by decide +kernel
theorem r13part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (16+k)) 0 (lookup 13 (16+k)) := by decide +kernel
theorem r13part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (24+k)) 0 (lookup 13 (24+k)) := by decide +kernel
theorem r13part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (32+k)) 0 (lookup 13 (32+k)) := by decide +kernel
theorem r13part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (40+k)) 0 (lookup 13 (40+k)) := by decide +kernel
theorem r13part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (48+k)) 0 (lookup 13 (48+k)) := by decide +kernel
theorem r13part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (56+k)) 0 (lookup 13 (56+k)) := by decide +kernel
theorem r13part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (64+k)) 0 (lookup 13 (64+k)) := by decide +kernel
theorem r13part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (72+k)) 0 (lookup 13 (72+k)) := by decide +kernel
theorem r13part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (80+k)) 0 (lookup 13 (80+k)) := by decide +kernel
theorem r13part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (88+k)) 0 (lookup 13 (88+k)) := by decide +kernel
theorem r13part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (96+k)) 0 (lookup 13 (96+k)) := by decide +kernel
theorem r13part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (104+k)) 0 (lookup 13 (104+k)) := by decide +kernel
theorem r13part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 13 (112+k)) 0 (lookup 13 (112+k)) := by decide +kernel
theorem r13part120 : ∀ k ∈ List.range 4, RunsValid (rowContext 13 (120+k)) 0 (lookup 13 (120+k)) := by decide +kernel

theorem checkedR13 (V : ℕ) (hV : V ∈ List.range 124) : RunsValid (rowContext 13 V) 0 (lookup 13 V) := by
  have hv : V < 124 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r13part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r13part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r13part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r13part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r13part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r13part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r13part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r13part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r13part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r13part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r13part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r13part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r13part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r13part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r13part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r13part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
theorem r14part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (0+k)) 0 (lookup 14 (0+k)) := by decide +kernel
theorem r14part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (8+k)) 0 (lookup 14 (8+k)) := by decide +kernel
theorem r14part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (16+k)) 0 (lookup 14 (16+k)) := by decide +kernel
theorem r14part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (24+k)) 0 (lookup 14 (24+k)) := by decide +kernel
theorem r14part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (32+k)) 0 (lookup 14 (32+k)) := by decide +kernel
theorem r14part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (40+k)) 0 (lookup 14 (40+k)) := by decide +kernel
theorem r14part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (48+k)) 0 (lookup 14 (48+k)) := by decide +kernel
theorem r14part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (56+k)) 0 (lookup 14 (56+k)) := by decide +kernel
theorem r14part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (64+k)) 0 (lookup 14 (64+k)) := by decide +kernel
theorem r14part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (72+k)) 0 (lookup 14 (72+k)) := by decide +kernel
theorem r14part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (80+k)) 0 (lookup 14 (80+k)) := by decide +kernel
theorem r14part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (88+k)) 0 (lookup 14 (88+k)) := by decide +kernel
theorem r14part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (96+k)) 0 (lookup 14 (96+k)) := by decide +kernel
theorem r14part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (104+k)) 0 (lookup 14 (104+k)) := by decide +kernel
theorem r14part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 14 (112+k)) 0 (lookup 14 (112+k)) := by decide +kernel
theorem r14part120 : ∀ k ∈ List.range 3, RunsValid (rowContext 14 (120+k)) 0 (lookup 14 (120+k)) := by decide +kernel

theorem checkedR14 (V : ℕ) (hV : V ∈ List.range 123) : RunsValid (rowContext 14 V) 0 (lookup 14 V) := by
  have hv : V < 123 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r14part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r14part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r14part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r14part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r14part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r14part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r14part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r14part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r14part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r14part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r14part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r14part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r14part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r14part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r14part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r14part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
theorem r15part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (0+k)) 0 (lookup 15 (0+k)) := by decide +kernel
theorem r15part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (8+k)) 0 (lookup 15 (8+k)) := by decide +kernel
theorem r15part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (16+k)) 0 (lookup 15 (16+k)) := by decide +kernel
theorem r15part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (24+k)) 0 (lookup 15 (24+k)) := by decide +kernel
theorem r15part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (32+k)) 0 (lookup 15 (32+k)) := by decide +kernel
theorem r15part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (40+k)) 0 (lookup 15 (40+k)) := by decide +kernel
theorem r15part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (48+k)) 0 (lookup 15 (48+k)) := by decide +kernel
theorem r15part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (56+k)) 0 (lookup 15 (56+k)) := by decide +kernel
theorem r15part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (64+k)) 0 (lookup 15 (64+k)) := by decide +kernel
theorem r15part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (72+k)) 0 (lookup 15 (72+k)) := by decide +kernel
theorem r15part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (80+k)) 0 (lookup 15 (80+k)) := by decide +kernel
theorem r15part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (88+k)) 0 (lookup 15 (88+k)) := by decide +kernel
theorem r15part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (96+k)) 0 (lookup 15 (96+k)) := by decide +kernel
theorem r15part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (104+k)) 0 (lookup 15 (104+k)) := by decide +kernel
theorem r15part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 15 (112+k)) 0 (lookup 15 (112+k)) := by decide +kernel
theorem r15part120 : ∀ k ∈ List.range 2, RunsValid (rowContext 15 (120+k)) 0 (lookup 15 (120+k)) := by decide +kernel

theorem checkedR15 (V : ℕ) (hV : V ∈ List.range 122) : RunsValid (rowContext 15 V) 0 (lookup 15 V) := by
  have hv : V < 122 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r15part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r15part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r15part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r15part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r15part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r15part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r15part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r15part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r15part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r15part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r15part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r15part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r15part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r15part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r15part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r15part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
theorem r16part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (0+k)) 0 (lookup 16 (0+k)) := by decide +kernel
theorem r16part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (8+k)) 0 (lookup 16 (8+k)) := by decide +kernel
theorem r16part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (16+k)) 0 (lookup 16 (16+k)) := by decide +kernel
theorem r16part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (24+k)) 0 (lookup 16 (24+k)) := by decide +kernel
theorem r16part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (32+k)) 0 (lookup 16 (32+k)) := by decide +kernel
theorem r16part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (40+k)) 0 (lookup 16 (40+k)) := by decide +kernel
theorem r16part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (48+k)) 0 (lookup 16 (48+k)) := by decide +kernel
theorem r16part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (56+k)) 0 (lookup 16 (56+k)) := by decide +kernel
theorem r16part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (64+k)) 0 (lookup 16 (64+k)) := by decide +kernel
theorem r16part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (72+k)) 0 (lookup 16 (72+k)) := by decide +kernel
theorem r16part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (80+k)) 0 (lookup 16 (80+k)) := by decide +kernel
theorem r16part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (88+k)) 0 (lookup 16 (88+k)) := by decide +kernel
theorem r16part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (96+k)) 0 (lookup 16 (96+k)) := by decide +kernel
theorem r16part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (104+k)) 0 (lookup 16 (104+k)) := by decide +kernel
theorem r16part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 16 (112+k)) 0 (lookup 16 (112+k)) := by decide +kernel
theorem r16part120 : ∀ k ∈ List.range 1, RunsValid (rowContext 16 (120+k)) 0 (lookup 16 (120+k)) := by decide +kernel

theorem checkedR16 (V : ℕ) (hV : V ∈ List.range 121) : RunsValid (rowContext 16 V) 0 (lookup 16 V) := by
  have hv : V < 121 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r16part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r16part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r16part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r16part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r16part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r16part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r16part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r16part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r16part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r16part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r16part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r16part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r16part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r16part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  by_cases h112 : V < 120
  · have hp := r16part112 (V-112) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
  have hp := r16part120 (V-120) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using hp
theorem r17part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (0+k)) 0 (lookup 17 (0+k)) := by decide +kernel
theorem r17part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (8+k)) 0 (lookup 17 (8+k)) := by decide +kernel
theorem r17part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (16+k)) 0 (lookup 17 (16+k)) := by decide +kernel
theorem r17part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (24+k)) 0 (lookup 17 (24+k)) := by decide +kernel
theorem r17part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (32+k)) 0 (lookup 17 (32+k)) := by decide +kernel
theorem r17part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (40+k)) 0 (lookup 17 (40+k)) := by decide +kernel
theorem r17part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (48+k)) 0 (lookup 17 (48+k)) := by decide +kernel
theorem r17part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (56+k)) 0 (lookup 17 (56+k)) := by decide +kernel
theorem r17part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (64+k)) 0 (lookup 17 (64+k)) := by decide +kernel
theorem r17part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (72+k)) 0 (lookup 17 (72+k)) := by decide +kernel
theorem r17part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (80+k)) 0 (lookup 17 (80+k)) := by decide +kernel
theorem r17part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (88+k)) 0 (lookup 17 (88+k)) := by decide +kernel
theorem r17part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (96+k)) 0 (lookup 17 (96+k)) := by decide +kernel
theorem r17part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (104+k)) 0 (lookup 17 (104+k)) := by decide +kernel
theorem r17part112 : ∀ k ∈ List.range 8, RunsValid (rowContext 17 (112+k)) 0 (lookup 17 (112+k)) := by decide +kernel

theorem checkedR17 (V : ℕ) (hV : V ∈ List.range 120) : RunsValid (rowContext 17 V) 0 (lookup 17 V) := by
  have hv : V < 120 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r17part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r17part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r17part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r17part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r17part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r17part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r17part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r17part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r17part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r17part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r17part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r17part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r17part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r17part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r17part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
theorem r18part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (0+k)) 0 (lookup 18 (0+k)) := by decide +kernel
theorem r18part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (8+k)) 0 (lookup 18 (8+k)) := by decide +kernel
theorem r18part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (16+k)) 0 (lookup 18 (16+k)) := by decide +kernel
theorem r18part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (24+k)) 0 (lookup 18 (24+k)) := by decide +kernel
theorem r18part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (32+k)) 0 (lookup 18 (32+k)) := by decide +kernel
theorem r18part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (40+k)) 0 (lookup 18 (40+k)) := by decide +kernel
theorem r18part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (48+k)) 0 (lookup 18 (48+k)) := by decide +kernel
theorem r18part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (56+k)) 0 (lookup 18 (56+k)) := by decide +kernel
theorem r18part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (64+k)) 0 (lookup 18 (64+k)) := by decide +kernel
theorem r18part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (72+k)) 0 (lookup 18 (72+k)) := by decide +kernel
theorem r18part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (80+k)) 0 (lookup 18 (80+k)) := by decide +kernel
theorem r18part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (88+k)) 0 (lookup 18 (88+k)) := by decide +kernel
theorem r18part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (96+k)) 0 (lookup 18 (96+k)) := by decide +kernel
theorem r18part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 18 (104+k)) 0 (lookup 18 (104+k)) := by decide +kernel
theorem r18part112 : ∀ k ∈ List.range 7, RunsValid (rowContext 18 (112+k)) 0 (lookup 18 (112+k)) := by decide +kernel

theorem checkedR18 (V : ℕ) (hV : V ∈ List.range 119) : RunsValid (rowContext 18 V) 0 (lookup 18 V) := by
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r18part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r18part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r18part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r18part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r18part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r18part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r18part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r18part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r18part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r18part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r18part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r18part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r18part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r18part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r18part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
theorem r19part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (0+k)) 0 (lookup 19 (0+k)) := by decide +kernel
theorem r19part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (8+k)) 0 (lookup 19 (8+k)) := by decide +kernel
theorem r19part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (16+k)) 0 (lookup 19 (16+k)) := by decide +kernel
theorem r19part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (24+k)) 0 (lookup 19 (24+k)) := by decide +kernel
theorem r19part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (32+k)) 0 (lookup 19 (32+k)) := by decide +kernel
theorem r19part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (40+k)) 0 (lookup 19 (40+k)) := by decide +kernel
theorem r19part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (48+k)) 0 (lookup 19 (48+k)) := by decide +kernel
theorem r19part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (56+k)) 0 (lookup 19 (56+k)) := by decide +kernel
theorem r19part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (64+k)) 0 (lookup 19 (64+k)) := by decide +kernel
theorem r19part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (72+k)) 0 (lookup 19 (72+k)) := by decide +kernel
theorem r19part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (80+k)) 0 (lookup 19 (80+k)) := by decide +kernel
theorem r19part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (88+k)) 0 (lookup 19 (88+k)) := by decide +kernel
theorem r19part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (96+k)) 0 (lookup 19 (96+k)) := by decide +kernel
theorem r19part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 19 (104+k)) 0 (lookup 19 (104+k)) := by decide +kernel
theorem r19part112 : ∀ k ∈ List.range 6, RunsValid (rowContext 19 (112+k)) 0 (lookup 19 (112+k)) := by decide +kernel

theorem checkedR19 (V : ℕ) (hV : V ∈ List.range 118) : RunsValid (rowContext 19 V) 0 (lookup 19 V) := by
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r19part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r19part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r19part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r19part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r19part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r19part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r19part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r19part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r19part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r19part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r19part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r19part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r19part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r19part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r19part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
theorem r20part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (0+k)) 0 (lookup 20 (0+k)) := by decide +kernel
theorem r20part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (8+k)) 0 (lookup 20 (8+k)) := by decide +kernel
theorem r20part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (16+k)) 0 (lookup 20 (16+k)) := by decide +kernel
theorem r20part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (24+k)) 0 (lookup 20 (24+k)) := by decide +kernel
theorem r20part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (32+k)) 0 (lookup 20 (32+k)) := by decide +kernel
theorem r20part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (40+k)) 0 (lookup 20 (40+k)) := by decide +kernel
theorem r20part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (48+k)) 0 (lookup 20 (48+k)) := by decide +kernel
theorem r20part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (56+k)) 0 (lookup 20 (56+k)) := by decide +kernel
theorem r20part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (64+k)) 0 (lookup 20 (64+k)) := by decide +kernel
theorem r20part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (72+k)) 0 (lookup 20 (72+k)) := by decide +kernel
theorem r20part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (80+k)) 0 (lookup 20 (80+k)) := by decide +kernel
theorem r20part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (88+k)) 0 (lookup 20 (88+k)) := by decide +kernel
theorem r20part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (96+k)) 0 (lookup 20 (96+k)) := by decide +kernel
theorem r20part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 20 (104+k)) 0 (lookup 20 (104+k)) := by decide +kernel
theorem r20part112 : ∀ k ∈ List.range 5, RunsValid (rowContext 20 (112+k)) 0 (lookup 20 (112+k)) := by decide +kernel

theorem checkedR20 (V : ℕ) (hV : V ∈ List.range 117) : RunsValid (rowContext 20 V) 0 (lookup 20 V) := by
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r20part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r20part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r20part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r20part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r20part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r20part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r20part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r20part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r20part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r20part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r20part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r20part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r20part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r20part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r20part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
theorem r21part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (0+k)) 0 (lookup 21 (0+k)) := by decide +kernel
theorem r21part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (8+k)) 0 (lookup 21 (8+k)) := by decide +kernel
theorem r21part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (16+k)) 0 (lookup 21 (16+k)) := by decide +kernel
theorem r21part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (24+k)) 0 (lookup 21 (24+k)) := by decide +kernel
theorem r21part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (32+k)) 0 (lookup 21 (32+k)) := by decide +kernel
theorem r21part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (40+k)) 0 (lookup 21 (40+k)) := by decide +kernel
theorem r21part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (48+k)) 0 (lookup 21 (48+k)) := by decide +kernel
theorem r21part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (56+k)) 0 (lookup 21 (56+k)) := by decide +kernel
theorem r21part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (64+k)) 0 (lookup 21 (64+k)) := by decide +kernel
theorem r21part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (72+k)) 0 (lookup 21 (72+k)) := by decide +kernel
theorem r21part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (80+k)) 0 (lookup 21 (80+k)) := by decide +kernel
theorem r21part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (88+k)) 0 (lookup 21 (88+k)) := by decide +kernel
theorem r21part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (96+k)) 0 (lookup 21 (96+k)) := by decide +kernel
theorem r21part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 21 (104+k)) 0 (lookup 21 (104+k)) := by decide +kernel
theorem r21part112 : ∀ k ∈ List.range 4, RunsValid (rowContext 21 (112+k)) 0 (lookup 21 (112+k)) := by decide +kernel

theorem checkedR21 (V : ℕ) (hV : V ∈ List.range 116) : RunsValid (rowContext 21 V) 0 (lookup 21 V) := by
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r21part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r21part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r21part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r21part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r21part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r21part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r21part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r21part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r21part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r21part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r21part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r21part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r21part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r21part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r21part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
theorem r22part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (0+k)) 0 (lookup 22 (0+k)) := by decide +kernel
theorem r22part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (8+k)) 0 (lookup 22 (8+k)) := by decide +kernel
theorem r22part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (16+k)) 0 (lookup 22 (16+k)) := by decide +kernel
theorem r22part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (24+k)) 0 (lookup 22 (24+k)) := by decide +kernel
theorem r22part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (32+k)) 0 (lookup 22 (32+k)) := by decide +kernel
theorem r22part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (40+k)) 0 (lookup 22 (40+k)) := by decide +kernel
theorem r22part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (48+k)) 0 (lookup 22 (48+k)) := by decide +kernel
theorem r22part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (56+k)) 0 (lookup 22 (56+k)) := by decide +kernel
theorem r22part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (64+k)) 0 (lookup 22 (64+k)) := by decide +kernel
theorem r22part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (72+k)) 0 (lookup 22 (72+k)) := by decide +kernel
theorem r22part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (80+k)) 0 (lookup 22 (80+k)) := by decide +kernel
theorem r22part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (88+k)) 0 (lookup 22 (88+k)) := by decide +kernel
theorem r22part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (96+k)) 0 (lookup 22 (96+k)) := by decide +kernel
theorem r22part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 22 (104+k)) 0 (lookup 22 (104+k)) := by decide +kernel
theorem r22part112 : ∀ k ∈ List.range 3, RunsValid (rowContext 22 (112+k)) 0 (lookup 22 (112+k)) := by decide +kernel

theorem checkedR22 (V : ℕ) (hV : V ∈ List.range 115) : RunsValid (rowContext 22 V) 0 (lookup 22 V) := by
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r22part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r22part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r22part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r22part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r22part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r22part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r22part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r22part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r22part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r22part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r22part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r22part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r22part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r22part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r22part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
theorem r23part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (0+k)) 0 (lookup 23 (0+k)) := by decide +kernel
theorem r23part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (8+k)) 0 (lookup 23 (8+k)) := by decide +kernel
theorem r23part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (16+k)) 0 (lookup 23 (16+k)) := by decide +kernel
theorem r23part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (24+k)) 0 (lookup 23 (24+k)) := by decide +kernel
theorem r23part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (32+k)) 0 (lookup 23 (32+k)) := by decide +kernel
theorem r23part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (40+k)) 0 (lookup 23 (40+k)) := by decide +kernel
theorem r23part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (48+k)) 0 (lookup 23 (48+k)) := by decide +kernel
theorem r23part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (56+k)) 0 (lookup 23 (56+k)) := by decide +kernel
theorem r23part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (64+k)) 0 (lookup 23 (64+k)) := by decide +kernel
theorem r23part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (72+k)) 0 (lookup 23 (72+k)) := by decide +kernel
theorem r23part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (80+k)) 0 (lookup 23 (80+k)) := by decide +kernel
theorem r23part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (88+k)) 0 (lookup 23 (88+k)) := by decide +kernel
theorem r23part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (96+k)) 0 (lookup 23 (96+k)) := by decide +kernel
theorem r23part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 23 (104+k)) 0 (lookup 23 (104+k)) := by decide +kernel
theorem r23part112 : ∀ k ∈ List.range 2, RunsValid (rowContext 23 (112+k)) 0 (lookup 23 (112+k)) := by decide +kernel

theorem checkedR23 (V : ℕ) (hV : V ∈ List.range 114) : RunsValid (rowContext 23 V) 0 (lookup 23 V) := by
  have hv : V < 114 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r23part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r23part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r23part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r23part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r23part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r23part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r23part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r23part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r23part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r23part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r23part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r23part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r23part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r23part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r23part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
theorem r24part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (0+k)) 0 (lookup 24 (0+k)) := by decide +kernel
theorem r24part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (8+k)) 0 (lookup 24 (8+k)) := by decide +kernel
theorem r24part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (16+k)) 0 (lookup 24 (16+k)) := by decide +kernel
theorem r24part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (24+k)) 0 (lookup 24 (24+k)) := by decide +kernel
theorem r24part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (32+k)) 0 (lookup 24 (32+k)) := by decide +kernel
theorem r24part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (40+k)) 0 (lookup 24 (40+k)) := by decide +kernel
theorem r24part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (48+k)) 0 (lookup 24 (48+k)) := by decide +kernel
theorem r24part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (56+k)) 0 (lookup 24 (56+k)) := by decide +kernel
theorem r24part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (64+k)) 0 (lookup 24 (64+k)) := by decide +kernel
theorem r24part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (72+k)) 0 (lookup 24 (72+k)) := by decide +kernel
theorem r24part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (80+k)) 0 (lookup 24 (80+k)) := by decide +kernel
theorem r24part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (88+k)) 0 (lookup 24 (88+k)) := by decide +kernel
theorem r24part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (96+k)) 0 (lookup 24 (96+k)) := by decide +kernel
theorem r24part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 24 (104+k)) 0 (lookup 24 (104+k)) := by decide +kernel
theorem r24part112 : ∀ k ∈ List.range 1, RunsValid (rowContext 24 (112+k)) 0 (lookup 24 (112+k)) := by decide +kernel

theorem checkedR24 (V : ℕ) (hV : V ∈ List.range 113) : RunsValid (rowContext 24 V) 0 (lookup 24 V) := by
  have hv : V < 113 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r24part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r24part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r24part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r24part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r24part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r24part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r24part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r24part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r24part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r24part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r24part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r24part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r24part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  by_cases h104 : V < 112
  · have hp := r24part104 (V-104) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
  have hp := r24part112 (V-112) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using hp
theorem r25part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (0+k)) 0 (lookup 25 (0+k)) := by decide +kernel
theorem r25part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (8+k)) 0 (lookup 25 (8+k)) := by decide +kernel
theorem r25part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (16+k)) 0 (lookup 25 (16+k)) := by decide +kernel
theorem r25part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (24+k)) 0 (lookup 25 (24+k)) := by decide +kernel
theorem r25part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (32+k)) 0 (lookup 25 (32+k)) := by decide +kernel
theorem r25part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (40+k)) 0 (lookup 25 (40+k)) := by decide +kernel
theorem r25part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (48+k)) 0 (lookup 25 (48+k)) := by decide +kernel
theorem r25part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (56+k)) 0 (lookup 25 (56+k)) := by decide +kernel
theorem r25part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (64+k)) 0 (lookup 25 (64+k)) := by decide +kernel
theorem r25part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (72+k)) 0 (lookup 25 (72+k)) := by decide +kernel
theorem r25part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (80+k)) 0 (lookup 25 (80+k)) := by decide +kernel
theorem r25part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (88+k)) 0 (lookup 25 (88+k)) := by decide +kernel
theorem r25part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (96+k)) 0 (lookup 25 (96+k)) := by decide +kernel
theorem r25part104 : ∀ k ∈ List.range 8, RunsValid (rowContext 25 (104+k)) 0 (lookup 25 (104+k)) := by decide +kernel

theorem checkedR25 (V : ℕ) (hV : V ∈ List.range 112) : RunsValid (rowContext 25 V) 0 (lookup 25 V) := by
  have hv : V < 112 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r25part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r25part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r25part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r25part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r25part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r25part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r25part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r25part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r25part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r25part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r25part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r25part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r25part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r25part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
theorem r26part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (0+k)) 0 (lookup 26 (0+k)) := by decide +kernel
theorem r26part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (8+k)) 0 (lookup 26 (8+k)) := by decide +kernel
theorem r26part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (16+k)) 0 (lookup 26 (16+k)) := by decide +kernel
theorem r26part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (24+k)) 0 (lookup 26 (24+k)) := by decide +kernel
theorem r26part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (32+k)) 0 (lookup 26 (32+k)) := by decide +kernel
theorem r26part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (40+k)) 0 (lookup 26 (40+k)) := by decide +kernel
theorem r26part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (48+k)) 0 (lookup 26 (48+k)) := by decide +kernel
theorem r26part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (56+k)) 0 (lookup 26 (56+k)) := by decide +kernel
theorem r26part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (64+k)) 0 (lookup 26 (64+k)) := by decide +kernel
theorem r26part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (72+k)) 0 (lookup 26 (72+k)) := by decide +kernel
theorem r26part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (80+k)) 0 (lookup 26 (80+k)) := by decide +kernel
theorem r26part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (88+k)) 0 (lookup 26 (88+k)) := by decide +kernel
theorem r26part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 26 (96+k)) 0 (lookup 26 (96+k)) := by decide +kernel
theorem r26part104 : ∀ k ∈ List.range 7, RunsValid (rowContext 26 (104+k)) 0 (lookup 26 (104+k)) := by decide +kernel

theorem checkedR26 (V : ℕ) (hV : V ∈ List.range 111) : RunsValid (rowContext 26 V) 0 (lookup 26 V) := by
  have hv : V < 111 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r26part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r26part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r26part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r26part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r26part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r26part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r26part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r26part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r26part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r26part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r26part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r26part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r26part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r26part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
theorem r27part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (0+k)) 0 (lookup 27 (0+k)) := by decide +kernel
theorem r27part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (8+k)) 0 (lookup 27 (8+k)) := by decide +kernel
theorem r27part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (16+k)) 0 (lookup 27 (16+k)) := by decide +kernel
theorem r27part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (24+k)) 0 (lookup 27 (24+k)) := by decide +kernel
theorem r27part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (32+k)) 0 (lookup 27 (32+k)) := by decide +kernel
theorem r27part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (40+k)) 0 (lookup 27 (40+k)) := by decide +kernel
theorem r27part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (48+k)) 0 (lookup 27 (48+k)) := by decide +kernel
theorem r27part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (56+k)) 0 (lookup 27 (56+k)) := by decide +kernel
theorem r27part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (64+k)) 0 (lookup 27 (64+k)) := by decide +kernel
theorem r27part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (72+k)) 0 (lookup 27 (72+k)) := by decide +kernel
theorem r27part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (80+k)) 0 (lookup 27 (80+k)) := by decide +kernel
theorem r27part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (88+k)) 0 (lookup 27 (88+k)) := by decide +kernel
theorem r27part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 27 (96+k)) 0 (lookup 27 (96+k)) := by decide +kernel
theorem r27part104 : ∀ k ∈ List.range 6, RunsValid (rowContext 27 (104+k)) 0 (lookup 27 (104+k)) := by decide +kernel

theorem checkedR27 (V : ℕ) (hV : V ∈ List.range 110) : RunsValid (rowContext 27 V) 0 (lookup 27 V) := by
  have hv : V < 110 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r27part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r27part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r27part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r27part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r27part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r27part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r27part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r27part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r27part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r27part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r27part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r27part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r27part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r27part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
theorem r28part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (0+k)) 0 (lookup 28 (0+k)) := by decide +kernel
theorem r28part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (8+k)) 0 (lookup 28 (8+k)) := by decide +kernel
theorem r28part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (16+k)) 0 (lookup 28 (16+k)) := by decide +kernel
theorem r28part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (24+k)) 0 (lookup 28 (24+k)) := by decide +kernel
theorem r28part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (32+k)) 0 (lookup 28 (32+k)) := by decide +kernel
theorem r28part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (40+k)) 0 (lookup 28 (40+k)) := by decide +kernel
theorem r28part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (48+k)) 0 (lookup 28 (48+k)) := by decide +kernel
theorem r28part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (56+k)) 0 (lookup 28 (56+k)) := by decide +kernel
theorem r28part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (64+k)) 0 (lookup 28 (64+k)) := by decide +kernel
theorem r28part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (72+k)) 0 (lookup 28 (72+k)) := by decide +kernel
theorem r28part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (80+k)) 0 (lookup 28 (80+k)) := by decide +kernel
theorem r28part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (88+k)) 0 (lookup 28 (88+k)) := by decide +kernel
theorem r28part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 28 (96+k)) 0 (lookup 28 (96+k)) := by decide +kernel
theorem r28part104 : ∀ k ∈ List.range 5, RunsValid (rowContext 28 (104+k)) 0 (lookup 28 (104+k)) := by decide +kernel

theorem checkedR28 (V : ℕ) (hV : V ∈ List.range 109) : RunsValid (rowContext 28 V) 0 (lookup 28 V) := by
  have hv : V < 109 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r28part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r28part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r28part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r28part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r28part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r28part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r28part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r28part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r28part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r28part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r28part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r28part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r28part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r28part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
theorem r29part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (0+k)) 0 (lookup 29 (0+k)) := by decide +kernel
theorem r29part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (8+k)) 0 (lookup 29 (8+k)) := by decide +kernel
theorem r29part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (16+k)) 0 (lookup 29 (16+k)) := by decide +kernel
theorem r29part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (24+k)) 0 (lookup 29 (24+k)) := by decide +kernel
theorem r29part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (32+k)) 0 (lookup 29 (32+k)) := by decide +kernel
theorem r29part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (40+k)) 0 (lookup 29 (40+k)) := by decide +kernel
theorem r29part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (48+k)) 0 (lookup 29 (48+k)) := by decide +kernel
theorem r29part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (56+k)) 0 (lookup 29 (56+k)) := by decide +kernel
theorem r29part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (64+k)) 0 (lookup 29 (64+k)) := by decide +kernel
theorem r29part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (72+k)) 0 (lookup 29 (72+k)) := by decide +kernel
theorem r29part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (80+k)) 0 (lookup 29 (80+k)) := by decide +kernel
theorem r29part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (88+k)) 0 (lookup 29 (88+k)) := by decide +kernel
theorem r29part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 29 (96+k)) 0 (lookup 29 (96+k)) := by decide +kernel
theorem r29part104 : ∀ k ∈ List.range 4, RunsValid (rowContext 29 (104+k)) 0 (lookup 29 (104+k)) := by decide +kernel

theorem checkedR29 (V : ℕ) (hV : V ∈ List.range 108) : RunsValid (rowContext 29 V) 0 (lookup 29 V) := by
  have hv : V < 108 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r29part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r29part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r29part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r29part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r29part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r29part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r29part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r29part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r29part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r29part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r29part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r29part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r29part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r29part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp
theorem r30part0 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (0+k)) 0 (lookup 30 (0+k)) := by decide +kernel
theorem r30part8 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (8+k)) 0 (lookup 30 (8+k)) := by decide +kernel
theorem r30part16 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (16+k)) 0 (lookup 30 (16+k)) := by decide +kernel
theorem r30part24 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (24+k)) 0 (lookup 30 (24+k)) := by decide +kernel
theorem r30part32 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (32+k)) 0 (lookup 30 (32+k)) := by decide +kernel
theorem r30part40 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (40+k)) 0 (lookup 30 (40+k)) := by decide +kernel
theorem r30part48 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (48+k)) 0 (lookup 30 (48+k)) := by decide +kernel
theorem r30part56 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (56+k)) 0 (lookup 30 (56+k)) := by decide +kernel
theorem r30part64 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (64+k)) 0 (lookup 30 (64+k)) := by decide +kernel
theorem r30part72 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (72+k)) 0 (lookup 30 (72+k)) := by decide +kernel
theorem r30part80 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (80+k)) 0 (lookup 30 (80+k)) := by decide +kernel
theorem r30part88 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (88+k)) 0 (lookup 30 (88+k)) := by decide +kernel
theorem r30part96 : ∀ k ∈ List.range 8, RunsValid (rowContext 30 (96+k)) 0 (lookup 30 (96+k)) := by decide +kernel
theorem r30part104 : ∀ k ∈ List.range 3, RunsValid (rowContext 30 (104+k)) 0 (lookup 30 (104+k)) := by decide +kernel

theorem checkedR30 (V : ℕ) (hV : V ∈ List.range 107) : RunsValid (rowContext 30 V) 0 (lookup 30 V) := by
  have hv : V < 107 := List.mem_range.mp hV
  by_cases h0 : V < 8
  · have hp := r30part0 (V-0) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using hp
  by_cases h8 : V < 16
  · have hp := r30part8 (V-8) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using hp
  by_cases h16 : V < 24
  · have hp := r30part16 (V-16) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using hp
  by_cases h24 : V < 32
  · have hp := r30part24 (V-24) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using hp
  by_cases h32 : V < 40
  · have hp := r30part32 (V-32) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using hp
  by_cases h40 : V < 48
  · have hp := r30part40 (V-40) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using hp
  by_cases h48 : V < 56
  · have hp := r30part48 (V-48) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using hp
  by_cases h56 : V < 64
  · have hp := r30part56 (V-56) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using hp
  by_cases h64 : V < 72
  · have hp := r30part64 (V-64) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using hp
  by_cases h72 : V < 80
  · have hp := r30part72 (V-72) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using hp
  by_cases h80 : V < 88
  · have hp := r30part80 (V-80) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using hp
  by_cases h88 : V < 96
  · have hp := r30part88 (V-88) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using hp
  by_cases h96 : V < 104
  · have hp := r30part96 (V-96) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using hp
  have hp := r30part104 (V-104) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using hp

theorem checked (r v z : ℕ) (hr : 1 ≤ r) (hr30 : r ≤ 30) (hy : r+v ≤ 136)
    (ht : r+v+z ≤ 6917) : ledger (rowContext r v) z ≤ bound := by
  have hv : v ∈ List.range (137-r) := List.mem_range.mpr (by omega)
  have hc : RunsValid (rowContext r v) 0 (lookup r v) := by
    interval_cases r <;> first
      | exact checkedR1 v hv
      | exact checkedR2 v hv
      | exact checkedR3 v hv
      | exact checkedR4 v hv
      | exact checkedR5 v hv
      | exact checkedR6 v hv
      | exact checkedR7 v hv
      | exact checkedR8 v hv
      | exact checkedR9 v hv
      | exact checkedR10 v hv
      | exact checkedR11 v hv
      | exact checkedR12 v hv
      | exact checkedR13 v hv
      | exact checkedR14 v hv
      | exact checkedR15 v hv
      | exact checkedR16 v hv
      | exact checkedR17 v hv
      | exact checkedR18 v hv
      | exact checkedR19 v hv
      | exact checkedR20 v hv
      | exact checkedR21 v hv
      | exact checkedR22 v hv
      | exact checkedR23 v hv
      | exact checkedR24 v hv
      | exact checkedR25 v hv
      | exact checkedR26 v hv
      | exact checkedR27 v hv
      | exact checkedR28 v hv
      | exact checkedR29 v hv
      | exact checkedR30 v hv
  exact RunsValid.sound _ _ 0 z hc (Nat.zero_le _) (by dsimp [rowContext]; omega)
end ProximityPrize.SubmissionLower.Lower80791.LedgerChecked

end Compact_LedgerChecked80791

section Compact_ClaimCompressed80791
/-! Unconditional exact-radius lower-bound certificate at error 80791. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.CompressedClaim
open ProximityPrize.Benchmark
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem prefixReceipt : PhaseSemantics.PrefixReceiptSound := by
  intro r v hr hR hY
  exact PrefixChecked.checked r (List.mem_range.mpr (by omega)) hr
    v (List.mem_range.mpr (by omega))

theorem thresholdReceipt : PhaseSemantics.ThresholdReceiptSound := by
  intro r v hr hR hY
  exact ThresholdCompressed.checked r (List.mem_range.mpr (by omega)) hr
    v (List.mem_range.mpr (by omega))

theorem runReceipt : PhaseSemantics.RunReceiptSound := by
  intro r v hr hR hY
  exact RunsChecked.checked r (List.mem_range.mpr (by omega)) hr
    v (List.mem_range.mpr (by omega))

theorem ledgerReceipt : Assembly.LedgerReceiptSound := LedgerChecked.checked

theorem protocolClaim : ProtocolClaim 6804 10341375 33554432 :=
  Closure.protocolClaim6804 prefixReceipt thresholdReceipt runReceipt ledgerReceipt

end ProximityPrize.SubmissionLower.Lower80791.CompressedClaim

end Compact_ClaimCompressed80791
