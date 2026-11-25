import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin
open K1_13 (Shape shape)
open Low6960SharedPrice (additiveBase nonsharedFee)

/-- the `i`-th chunk of 200 shapes of a gate list, checked as a gate row -/
def chunkOf (l : List (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) := (l.drop (200 * i)).take 200

theorem all_of_chunks (f : ℕ × ℕ → Bool) (l : List (ℕ × ℕ)) (N : ℕ) (hN : l.length ≤ 200 * N)
    (h : ∀ i, i < N → (chunkOf l i).all f = true) : l.all f = true := by
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
  have hi : k / 200 < N := by omega
  have := List.all_eq_true.mp (h (k / 200) hi) p ?_
  · exact this
  · unfold chunkOf
    rw [← hkp]
    have hmem : l[k] ∈ (l.drop (200 * (k / 200))).take 200 := by
      rw [List.mem_iff_getElem]
      refine ⟨k - 200 * (k / 200), ?_, ?_⟩
      · simp [List.length_take, List.length_drop]; omega
      · simp [List.getElem_take, List.getElem_drop]; congr 1; omega
    exact hmem

def oneF (_id t : ℕ) (p : ℕ × ℕ) : Bool := !(valid ⟨p.1, p.2, t⟩) || shapeOK ⟨p.1, p.2, t⟩

def gtF (id t : ℕ) (p : ℕ × ℕ) : Bool :=
  let x : Shape := ⟨p.1, p.2, t⟩
  let k : Low6960Allocation.Band := ⟨id % 44, Nat.mod_lt _ (by decide)⟩
  let l := Low6960Allocation.order (Low6960Allocation.bandOrders k) x
  Nat.blt 0 l && Nat.ble (Low6960Gate.gatePrice Gfun x l)
    (Low6960Allocation.allowance k ((Low6960Allocation.start k).t + t) p.1 p.2 t)

theorem one_of_chunks (id t N : ℕ) (hN : (Low6960Gate.gateList id t).length ≤ 200 * N)
    (h : ∀ i, i < N → (chunkOf (Low6960Gate.gateList id t) i).all (oneF id t) = true) : one id t = true :=
  all_of_chunks (oneF id t) _ N hN h

theorem gtOne_of_chunks (id t N : ℕ) (hN : (Low6960Gate.gateList id t).length ≤ 200 * N)
    (h : ∀ i, i < N → (chunkOf (Low6960Gate.gateList id t) i).all (gtF id t) = true) : gtOne id t = true :=
  all_of_chunks (gtF id t) _ N hN h
def hiTab : ℕ → List (List ℤ)
  | 1 => [[0, 33844005144642240, 160827326397120000], [33844005144642240, 119325748562307360, 790368146505147840], [160827326397120000, 790368146505147840, 2489695061441830080]]
  | 2 => [[0, 42920342402941440, 160827326397120000], [42920342402941440, 164169014124836160, 808520821021746240], [160827326397120000, 808520821021746240, 2489695061441830080]]
  | 3 => [[0, 49227627147364800, 160827326397120000], [49227627147364800, 206704735925801760, 821135390510592960], [160827326397120000, 821135390510592960, 2489695061441830080]]
  | 4 => [[0, 38578736338512960, 123137435991361920], [38578736338512960, 188355488212305120, 718295851618222080], [123137435991361920, 718295851618222080, 2169690008806312320]]
  | 5 => [[0, 47432871400765440, 160827326397120000], [47432871400765440, 153571386182027520, 639506018414705280], [160827326397120000, 639506018414705280, 1955575479633763200]]
  | 6 => [[0, 39741058093631040, 144059171220140160], [39741058093631040, 162579371970180960, 767523457501238400], [144059171220140160, 767523457501238400, 2352242366382209280]]
  | 7 => [[0, 6973941290981760, 144059171220140160], [6973941290981760, 22511470254842880, 701989223895939840], [144059171220140160, 701989223895939840, 2352242366382209280]]
  | 8 => [[0, 17434807111992000, 160827326397120000], [17434807111992000, 55945215294281760, 757549750439847360], [160827326397120000, 757549750439847360, 2489695061441830080]]
  | 9 => [[0, 45330443152624320, 160827326397120000], [45330443152624320, 178603981809776160, 813341022521112000], [160827326397120000, 813341022521112000, 2489695061441830080]]
  | 10 => [[0, 506081004816576, 1518243014449728], [506081004816576, 3966610802890224, 11899832954529232], [1518243014449728, 11899832954529232, 35699498863587696]]
  | 11 => [[0, 562681527261440, 1689184189274880], [562681527261440, 4091904505817616, 12565743623800368], [1689184189274880, 12565743623800368, 37699510086382224]]
  | 12 => [[0, 653850152126816, 1962690063871008], [653850152126816, 4426949120852544, 13568598253924032], [1962690063871008, 13568598253924032, 40708073976753216]]
  | 13 => [[0, 990034464324320, 3261842910556320], [990034464324320, 1883914330992736, 7055739421348128], [3261842910556320, 7055739421348128, 21750697299211104]]
  | _ => []

def rayK (c : ℕ) (x : Shape) : Fin 3 → Fin 3 → ℤ := if isT c then rayT x else rayO x

/-- the gate's top ray as literals (checked equal to `rayK c (hiS (Gk c))` for 1 <= c <= 9) -/
def hiL (c : ℕ) : Fin 3 → Fin 3 → ℤ := fun i k =>
  if c = 0 ∨ 14 ≤ c then rayK c (hiS (Gk c)) i k else ((hiTab c).getD i.1 []).getD k.1 0

theorem hiTab_ok : ∀ c, c < 14 → 1 ≤ c → ∀ i k : Fin 3,
    ((hiTab c).getD i.1 []).getD k.1 0 = rayK c (hiS (Gk c)) i k := by decide +kernel

theorem hiL_eq (c : ℕ) : hiL c = rayK c (hiS (Gk c)) := by
  funext i k
  unfold hiL
  by_cases h : c = 0 ∨ 14 ≤ c
  · simp only [h, ite_true]
  · rw [if_neg h]
    exact hiTab_ok c (by omega) (by omega) i k

theorem numK_eq (c : ℕ) (x : Shape) : numK c x = thNum (rayK c x) (hiL c) := by
  rw [hiL_eq]
  unfold numK rayK
  by_cases h : isT c = true
  · simp only [h, ite_true]; rfl
  · simp only [h, ite_false]; rfl

/-- shape check from the shared numerator -/
def sN (c : ℕ) (x : Shape) (n : ℕ) : Bool :=
  if c = 0 then false else Nat.ble c 13 && okK c x && decide (∀ i k : Fin 3, (DEN : ℤ) * rayK c x i k ≤ (n : ℤ) * hiL c i k)

theorem thK_eq (c : ℕ) (x : Shape) : thK c x =
    (if isT c = true then thOK (rayT x) (rayT (hiS (Gk c))) else thOK (rayO x) (rayO (hiS (Gk c)))) := rfl
theorem thOK_eq (rx rh : Fin 3 → Fin 3 → ℤ) : thOK rx rh =
    decide (∀ i k : Fin 3, (DEN : ℤ) * rx i k ≤ (thNum rx rh : ℤ) * rh i k) := rfl
theorem shapeOK_c (c : ℕ) (x : Shape) :
    (if c = 0 then false else Nat.ble c 13 && okK c x && thK c x) = sN c x (thNum (rayK c x) (hiL c)) := by
  unfold sN
  by_cases h : c = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rw [thK_eq, hiL_eq]
    by_cases h2 : isT c = true
    · rw [if_pos h2, thOK_eq]
      simp only [rayK, h2, ite_true]
    · rw [if_neg h2, thOK_eq]
      simp only [rayK, h2, Bool.false_eq_true, ite_false]

theorem shapeOK_eq (x : Shape) : shapeOK x = sN (cls x) x (thNum (rayK (cls x) x) (hiL (cls x))) :=
  shapeOK_c (cls x) x

def gtG (id t : ℕ) (p : ℕ × ℕ) (G : ℕ) : Bool :=
  let x : Shape := ⟨p.1, p.2, t⟩
  let k : Low6960Allocation.Band := ⟨id % 44, Nat.mod_lt _ (by decide)⟩
  let l := Low6960Allocation.order (Low6960Allocation.bandOrders k) x
  Nat.blt 0 l && Nat.ble (additiveBase x l + nonsharedFee x l + G)
    (Low6960Allocation.allowance k ((Low6960Allocation.start k).t + t) p.1 p.2 t)

/-- fused shape + price check: the ray numerator is computed once -/
def fF (id t : ℕ) (p : ℕ × ℕ) : Bool :=
  let x : Shape := ⟨p.1, p.2, t⟩
  let c := cls x
  let n := thNum (rayK c x) (hiL c)
  (!(valid x) || sN c x n) && gtG id t p (if c = 0 then 0 else Ax n (Gk c).A)

theorem gtF_eq (id t : ℕ) (p : ℕ × ℕ) :
    gtF id t p = gtG id t p (Gfun ⟨p.1, p.2, t⟩) := rfl

theorem Gfun_eq (x : Shape) : Gfun x = (if cls x = 0 then 0 else Ax (thNum (rayK (cls x) x) (hiL (cls x))) (Gk (cls x)).A) := by
  unfold Gfun
  generalize cls x = c
  by_cases h : c = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, numK_eq]

theorem fF_eq (id t : ℕ) (p : ℕ × ℕ) : fF id t p = (oneF id t p && gtF id t p) := by
  rw [gtF_eq, Gfun_eq]
  unfold oneF
  rw [shapeOK_eq]
  rfl

theorem both_of_chunks (id t N : ℕ) (hN : (Low6960Gate.gateList id t).length ≤ 200 * N)
    (h : ∀ i, i < N → (chunkOf (Low6960Gate.gateList id t) i).all (fF id t) = true) :
    one id t = true ∧ gtOne id t = true := by
  have h1 : ∀ i, i < N → (chunkOf (Low6960Gate.gateList id t) i).all (oneF id t) = true := by
    intro i hi
    have := h i hi
    simp only [fF_eq, List.all_eq_true, Bool.and_eq_true] at this ⊢
    exact fun p hp => (this p hp).1
  have h2 : ∀ i, i < N → (chunkOf (Low6960Gate.gateList id t) i).all (gtF id t) = true := by
    intro i hi
    have := h i hi
    simp only [fF_eq, List.all_eq_true, Bool.and_eq_true] at this ⊢
    exact fun p hp => (this p hp).2
  exact ⟨one_of_chunks id t N hN h1, gtOne_of_chunks id t N hN h2⟩

end Gate61Fin
